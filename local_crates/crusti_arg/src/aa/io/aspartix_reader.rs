// crusti_arg
// Copyright (C) 2020  Artois University and CNRS
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
// Contributors:
//   *   CRIL - initial API and implementation

use crate::{utils::warning_result::WarningResult, AAFramework, ArgumentSet};
use anyhow::{anyhow, Context, Result};
use lazy_static::lazy_static;
use regex::{Captures, Regex};
use std::{
    cell::RefCell,
    io::{BufRead, BufReader, Read},
    rc::Rc,
};

const ARG_AND_SPACE_PATTERN: &str = r"\s*[_[:alpha:]][_[:alpha:]\d]*\s*";

lazy_static! { // kcov-ignore
    static ref ARG_LINE_PATTERN: Regex = Regex::new(r"^\s*arg\([^)]+\).\s*$").unwrap();
    static ref ARG_LINE_ARG_NAME_PATTERN: Regex =
        Regex::new(&format!(r"^\s*arg\(({})\).\s*$", ARG_AND_SPACE_PATTERN)).unwrap();
    static ref ATT_LINE_PATTERN: Regex = Regex::new(r"^\s*att\([^,]+,[^)]+\).\s*$").unwrap();
    static ref ATT_LINE_ARG_NAMES_PATTERN: Regex = Regex::new(&format!(
        r"^\s*att\(({}),({})\).\s*$",
        ARG_AND_SPACE_PATTERN, ARG_AND_SPACE_PATTERN,
    ))
    .unwrap();
}

const DEFAULT_ARG_LABELS_CAP: usize = 1 << 10;

fn captured_arg(c: &Captures, i: usize) -> WarningResult<String, String> {
    let str_arg = c.get(i).unwrap().as_str();
    let trimmed_str_arg = str_arg.trim().to_string();
    if trimmed_str_arg.len() == str_arg.len() {
        WarningResult::Ok(trimmed_str_arg)
    } else {
        WarningResult::Warned(
            trimmed_str_arg,
            vec!["argument names beginning or ending by spaces may be ambiguous".to_string()],
        ) // kcov-ignore
    }
}

fn try_read_arg_line<T>(l: T) -> Result<Option<WarningResult<String, String>>>
where
    T: AsRef<str>,
{
    if ARG_LINE_PATTERN.is_match(l.as_ref()) {
        let captures = ARG_LINE_ARG_NAME_PATTERN.captures(l.as_ref());
        match captures {
            Some(c) => Ok(Some(captured_arg(&c, 1))),
            None => Err(anyhow!("invalid argument name in {}", l.as_ref().trim())),
        }
    } else {
        Ok(None)
    }
}

fn try_read_att_line<T>(l: T) -> Result<Option<WarningResult<(String, String), String>>>
where
    T: AsRef<str>,
{
    if ATT_LINE_PATTERN.is_match(l.as_ref()) {
        let captures = ATT_LINE_ARG_NAMES_PATTERN.captures(l.as_ref());
        match captures {
            Some(c) => Ok(Some(captured_arg(&c, 1).zip(captured_arg(&c, 2)))),
            None => Err(anyhow!("invalid argument names in {}", l.as_ref().trim())),
        }
    } else {
        Ok(None)
    }
}

/// A reader for the Aspartix format.
///
/// This object is used to read an [`AAFramework`] encoded using the Aspartix input format, as defined on [the Aspartix website](https://www.dbai.tuwien.ac.at/research/argumentation/aspartix/dung.html).
/// The [`LabelType`] of the returned argument frameworks is `String`.
///
/// # Example
///
/// ```
/// # use crusti_arg::{AAFramework, AspartixReader};
/// fn read_af_from_str(s: &str) -> AAFramework<String> {
///     let reader = AspartixReader::default();
///     reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
/// }
/// # read_af_from_str("arg(a).");
/// ```
///
/// [`AAFramework`]: struct.AAFramework.html
/// [`LabelType`]: trait.LabelType.html
#[derive(Default)]
pub struct AspartixReader<'a> {
    warning_handlers: Vec<Rc<RefCell<&'a mut dyn FnMut(usize, String)>>>,
}

impl<'a> AspartixReader<'a> {
    /// Reads an [`AAFramework`] encoded using the Aspartix input format.
    /// The [`LabelType`] of the returned AFs is `String`.
    ///
    /// In case warnings are raised, the callback functions registered by [`add_warning_handler`] are triggered.
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{AAFramework, AspartixReader};
    /// fn read_af_from_str(s: &str) -> AAFramework<String> {
    ///     let reader = AspartixReader::default();
    ///     reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
    /// }
    /// # read_af_from_str("arg(a).");
    /// ```
    ///
    /// [`AAFramework`]: struct.AAFramework.html
    /// [`LabelType`]: trait.LabelType.html
    /// [`add_warning_handler`]: struct.AspartixReader.html#method.add_warning_handler
    pub fn read(&self, reader: &mut dyn Read) -> Result<AAFramework<String>> {
        let mut arg_labels = Some(Vec::with_capacity(DEFAULT_ARG_LABELS_CAP));
        let mut af = None;
        let br = BufReader::new(reader);
        let mut line_index_plus_one = 0;
        for line in br.lines() {
            line_index_plus_one += 1;
            let context = || format!("while reading line {}", line_index_plus_one - 1);
            let warning_consumer = |warnings: Vec<String>| {
                for w in warnings.iter() {
                    self.warning_handlers
                        .iter()
                        .for_each(|h| (*h.borrow_mut())(line_index_plus_one - 1, w.to_string()));
                }
            };
            let l = &line.with_context(context)?;
            if l.trim().is_empty() {
                continue;
            }
            if let Some(a) = try_read_arg_line(l).with_context(context)? {
                if af.is_some() {
                    return Err(anyhow!("found an argument declaration after an attack"))
                        .with_context(context);
                }
                arg_labels
                    .as_mut()
                    .unwrap()
                    .push(a.consume_warnings(warning_consumer));
                continue;
            }
            if let Some(result) = try_read_att_line(l).with_context(context)? {
                let (a, b) = result.consume_warnings(warning_consumer);
                if af.is_none() {
                    af = Some(AAFramework::new(ArgumentSet::new(
                        arg_labels.as_ref().unwrap_or(&vec![]),
                    )?));
                }
                af.as_mut()
                    .unwrap()
                    .new_attack(&a, &b)
                    .with_context(context)?;
                continue;
            }
            return Err(anyhow!("syntax error in line \"{}\"", l)).with_context(context);
        }
        if af.is_none() {
            af = Some(AAFramework::new(ArgumentSet::new(
                arg_labels.as_ref().unwrap_or(&vec![]),
            )?));
        }
        Ok(af.unwrap())
    }

    /// Adds a callback function to call when warnings are raised while parsing an AF.
    pub fn add_warning_handler(&mut self, h: &'a mut dyn FnMut(usize, String)) {
        self.warning_handlers.push(Rc::new(RefCell::new(h)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arg_line_pattern_ok() {
        assert!(ARG_LINE_PATTERN.is_match("arg(a)."));
        assert!(ARG_LINE_PATTERN.is_match("    arg(a).   "));
        assert!(ARG_LINE_PATTERN.is_match("arg(1a. )."));
    }

    const WRONG_ARG_LINES: [&'static str; 6] = [
        "rg(a).",
        "arg(a)",
        "arg().",
        "arga).",
        "arg(a.",
        "arg(a).arg(b).",
    ];

    #[test]
    fn test_arg_line_pattern_not_ok() {
        WRONG_ARG_LINES
            .iter()
            .for_each(|p| assert!(!ARG_LINE_PATTERN.is_match(p)))
    }

    #[test]
    fn test_try_read_arg_line_ok() {
        let assert_arg_name = |expected: &str, actual| {
            let result = try_read_arg_line(actual);
            if let Ok(opt_result) = result {
                if let Some(result) = opt_result {
                    assert_eq!(expected.to_string(), result.consume_warnings(|_| {}));
                    return;
                }
            } // kcov-ignore
            panic!("error for line \"{}\"", actual); // kcov-ignore
        };
        assert_arg_name("a", "arg(a).");
        assert_arg_name("a", "arg( a).");
        assert_arg_name("a", "arg(a ).");
        assert_arg_name("a", "arg( a ).");
        assert_arg_name("a", "    arg(a).   ");
        assert_arg_name("_a", "arg(_a).");
        assert_arg_name("a1_", "arg(a1_).");
    }

    #[test]
    fn test_try_read_arg_line_wrong_name() {
        ["arg(a.).", "arg(1a)."].iter().for_each(|l| {
            assert!(try_read_arg_line(l).is_err());
        });
    }

    #[test]
    fn test_try_read_arg_line_wrong_line_pattern() {
        WRONG_ARG_LINES.iter().for_each(|p| {
            assert!(try_read_arg_line(p).is_ok());
            assert!(try_read_arg_line(p).unwrap().is_none());
        });
    }

    #[test]
    fn test_att_line_pattern_ok() {
        assert!(ATT_LINE_PATTERN.is_match("att(a,b)."));
        assert!(ATT_LINE_PATTERN.is_match("    att(a,b).   "));
        assert!(ATT_LINE_PATTERN.is_match("att(1a. ,b)."));
        assert!(ATT_LINE_PATTERN.is_match("att(b,1a. )."));
        assert!(ATT_LINE_PATTERN.is_match("att(1a. ,2b.)."));
    }

    const WRONG_ATT_LINES: [&'static str; 8] = [
        "tt(a,b).",
        "att(a,b)",
        "att().",
        "att(a,).",
        "att(,b).",
        "atta,b).",
        "att(a,b.",
        "att(a,b).att(c,d).",
    ];

    #[test]
    fn test_att_line_pattern_not_ok() {
        WRONG_ATT_LINES
            .iter()
            .for_each(|p| assert!(!ATT_LINE_PATTERN.is_match(p)))
    }

    #[test]
    fn test_try_read_att_line_ok() {
        let assert_att_names = |expected0: &str, expected1: &str, actual| {
            let result = try_read_att_line(actual);
            if let Ok(opt_result) = result {
                if let Some(result) = opt_result {
                    // kcov-ignore-start
                    assert_eq!(
                        (expected0.to_string(), expected1.to_string()),
                        result.consume_warnings(|_| {})
                    );
                    // kcov-ignore-end
                    return;
                }
                panic!("line \"{}\": argument names seen as invalid", actual); // kcov-ignore
            }
            panic!("line \"{}\": not seen as an attack line", actual); // kcov-ignore
        };
        assert_att_names("a", "b", "att(a,b).");
        assert_att_names("a", "b", "att( a,b).");
        assert_att_names("a", "b", "att(a ,b).");
        assert_att_names("a", "b", "att( a ,b).");
        assert_att_names("a", "b", "att(a, b).");
        assert_att_names("a", "b", "att(a,b ).");
        assert_att_names("a", "b", "att(a, b ).");
        assert_att_names("a", "b", "    att(a,b).   ");
        assert_att_names("_a", "b", "att(_a,b).");
        assert_att_names("a1_", "b", "att(a1_,b).");
    }

    #[test]
    fn test_try_read_att_line_wrong_name() {
        ["att(a.,b).", "att(a,b.).", "att(1a,b).", "att(a,1b)."]
            .iter()
            .for_each(|l| {
                assert!(try_read_att_line(l).is_err());
            });
    }

    #[test]
    fn test_try_read_att_line_wrong_line_pattern() {
        WRONG_ATT_LINES.iter().for_each(|p| {
            assert!(try_read_att_line(p).is_ok());
            assert!(try_read_att_line(p).unwrap().is_none());
        });
    }

    fn str_args(af: &AAFramework<String>) -> Vec<String> {
        af.argument_set().iter().map(|s| format!("{}", s)).collect()
    }

    fn str_attacks(af: &AAFramework<String>) -> Vec<String> {
        af.iter_attacks()
            .map(|a| format!("({},{})", a.attacker(), a.attacked()))
            .collect()
    }

    #[test]
    fn test_read_ok() {
        let instance = "arg(a).\narg(b).\natt(a,b).\n";
        let af = AspartixReader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        let args = str_args(&af);
        assert_eq!(vec!["a".to_string(), "b".to_string()], args);
        let attacks = str_attacks(&af);
        assert_eq!(vec!["(a,b)".to_string()], attacks);
    }

    #[test]
    fn test_read_empty() {
        let instance = "\n";
        let af = AspartixReader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        let args = str_args(&af);
        assert_eq!(vec![] as Vec<String>, args);
        let attacks = str_attacks(&af);
        assert_eq!(vec![] as Vec<String>, attacks);
    }

    #[test]
    fn test_read_arg_after_att() {
        let instance = "arg(a).\narg(b).\natt(a,b).\narg(c).\n";
        assert!(AspartixReader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_read_syntax_error() {
        let instance = "argument(a).\narg(b).\natt(a,b).\n";
        assert!(AspartixReader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_read_unknown_arg_in_att() {
        let instance = "arg(a).\narg(b).\natt(a,c).\n";
        assert!(AspartixReader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_read_warn_arg_left_space() {
        let instance = "arg( a).\narg(b).\natt(a,b).\n";
        let mut warnings = vec![];
        let mut closure = |i, w| warnings.push((i, w));
        let mut reader = AspartixReader::default();
        reader.add_warning_handler(&mut closure);
        reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(
            warnings,
            vec![(
                0,
                "argument names beginning or ending by spaces may be ambiguous".to_string()
            )]
        );
    }

    #[test]
    fn test_read_only_args() {
        let instance = "arg(a).\narg(b).\n";
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(2, af.argument_set().len());
        assert_eq!(0, af.n_attacks());
    }
}
