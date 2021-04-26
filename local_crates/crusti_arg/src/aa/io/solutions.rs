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

//! A module used to read argumentation solvers output.
use anyhow::{anyhow, Context, Result};
use lazy_static::lazy_static;
use regex::Regex;
use std::io::{BufRead, Write};

use crate::{ArgumentSet, LabelType};

const APX_ARG_AND_SPACE_PATTERN: &str = r"\s*[_[:alpha:]][_[:alpha:]\d]*\s*";
const TGF_ARG_AND_SPACE_PATTERN: &str = r"\s*\d+\s*";

lazy_static! {
    static ref ACCEPTANCE_STATUS_LINE_PATTERN: Regex = Regex::new(r"^\s*([^\s]+)\s*$").unwrap();
    static ref EXTENSION_COUNT_LINE_PATTERN: Regex = Regex::new(r"^\s*(\d+)\s*$").unwrap();
    static ref APX_EXTENSION_LINE_PATTERN: Regex = Regex::new(&format!(
        r"^\s*\[\s*({}(,\s*{})*)?\]\s*$",
        APX_ARG_AND_SPACE_PATTERN, APX_ARG_AND_SPACE_PATTERN
    ))
    .unwrap();
    static ref TGF_EXTENSION_LINE_PATTERN: Regex = Regex::new(&format!(
        r"^\s*\[\s*({}(,\s*{})*)?\]\s*$",
        TGF_ARG_AND_SPACE_PATTERN, TGF_ARG_AND_SPACE_PATTERN
    ))
    .unwrap();
    static ref EMPTY_EXTENSION_SET_LINE_PATTERN: Regex = Regex::new(r"^\s*\[\s*\]\s*$").unwrap();
    static ref EXTENSION_SET_BEGIN_LINE_PATTERN: Regex = Regex::new(r"^\s*\[\s*$").unwrap();
    static ref EXTENSION_SET_END_LINE_PATTERN: Regex = Regex::new(r"^\s*\]\s*$").unwrap();
}

/// A trait to be implemented by objects intended to read argumentation solver solutions.
pub trait SolutionReader<T>
where
    T: LabelType,
{
    /// Reads an extension from a single line of text.
    fn read_extension_line_from_str(&self, line: &str) -> Result<ArgumentSet<T>>;

    /// Reads a result of a `DC` (credulous acceptance) or `DS` (skeptical acceptance) query.
    ///
    /// Such result must be a single line containing the string "YES" or "NO", depending on the acceptance status.
    ///
    /// If the result does not match these words, an error is returned.
    ///
    /// # Arguments
    /// * `reader` - the reader in which the result must be read
    fn read_acceptance_status(&self, reader: &mut dyn BufRead) -> Result<bool> {
        let mut line = String::new();
        let wrong_acceptance_status =
            |s| Err(anyhow!(r#"expected an acceptance status, found "{}""#, s));
        match reader
            .read_line(&mut line)
            .context("while parsing an acceptance status")?
        {
            0 => Err(anyhow!("read EOF while parsing an acceptance status")),
            _ => match ACCEPTANCE_STATUS_LINE_PATTERN.captures(line.as_str()) {
                Some(c) => match c.get(1).unwrap().as_str() {
                    "YES" => Ok(true),
                    "NO" => Ok(false),
                    _ => wrong_acceptance_status(c.get(1).unwrap().as_str()),
                },
                None => wrong_acceptance_status(line.as_str()),
            }, // kcov-ignore
        }
    }

    /// Reads an extension count (`CE`) query.
    ///
    /// Such result must be a single line containing a positive number.
    ///
    /// If the result does not match a positive number, an error is returned.
    ///
    /// # Arguments
    /// * `reader` - the reader in which the result must be read
    fn read_extension_count(&self, reader: &mut dyn BufRead) -> Result<usize> {
        let mut line = String::new();
        match reader
            .read_line(&mut line)
            .context("while parsing an extension count")?
        {
            0 => Err(anyhow!("read EOF while parsing an acceptance status")),
            _ => match EXTENSION_COUNT_LINE_PATTERN.captures(line.as_str()) {
                Some(c) => c
                    .get(1)
                    .unwrap()
                    .as_str()
                    .parse::<usize>()
                    .context("while parsing an extension count"),
                None => Err(anyhow!(
                    r#"expected an extension count, found "{}""#,
                    line.as_str()
                )),
            },
        }
    }

    /// Reads an extension.
    ///
    /// The extension must be given on a single line, surrounded between square brackets.
    /// The arguments composing the extension must be split be commas.
    ///
    /// If the content does not match these requirements, an error is returned.
    ///
    /// # Arguments
    /// * `reader` - the reader in which the content must be read
    fn read_extension(&self, reader: &mut dyn BufRead) -> Result<ArgumentSet<T>> {
        let mut line = String::new();
        match reader
            .read_line(&mut line)
            .context("while parsing an extension line")?
        {
            0 => Err(anyhow!("read EOF while parsing an extension line")),
            _ => self.read_extension_line_from_str(line.as_str()),
        }
    }

    /// Reads a set of extensions.
    ///
    /// A non-empty set of `n` extensions must be given by `n+2` lines:
    /// * a line containing a single opening bracket, indicating the beginning of the set;
    /// * the following `n` lines give the extensions (see [`read_extension`](crate::solution_reader::read_extension) for the extension formatting);
    /// * a line containing a single closing bracket, indicating the end of the set.
    ///
    /// In case the set of extensions is empty, it may be given using two lines (as described above, but without any extension)
    /// or by a single line containing the two brackets.
    ///
    /// If the content does not match these requirements, an error is returned.
    ///
    /// # Arguments
    /// * `reader` - the reader in which the content must be read
    fn read_extension_set(&self, reader: &mut dyn BufRead) -> Result<Vec<ArgumentSet<T>>> {
        let mut extensions = None;
        let mut line_count = 0;
        for line in reader.lines() {
            line_count += 1;
            let l = line
                .with_context(|| format!("while reading an extension set (line {})", line_count))?;
            if EMPTY_EXTENSION_SET_LINE_PATTERN.is_match(&l) && extensions.is_none() {
                return Ok(vec![]);
            } else if EXTENSION_SET_BEGIN_LINE_PATTERN.is_match(&l) {
                if extensions.is_some() {
                    return Err(anyhow!(
                        "unexpected second extension beginning pattern (line {})",
                        line_count
                    ));
                }
                extensions = Some(vec![]);
            } else {
                if extensions.is_none() {
                    return Err(anyhow!(
                        "expected an extension beginning pattern (line {})",
                        line_count
                    ));
                }
                if EXTENSION_SET_END_LINE_PATTERN.is_match(&l) {
                    return Ok(extensions.unwrap());
                }
                extensions
                    .as_mut()
                    .unwrap()
                    .push(self.read_extension_line_from_str(&l)?);
            }
        }
        Err(anyhow!("unterminated extension set"))
    }
}

/// A structure used to read solutions returned by APX solvers.
pub struct AspartixSolutionReader;

impl AspartixSolutionReader {
    /// Builds a new reader for APX solutions.
    pub fn new() -> Self {
        AspartixSolutionReader
    }
}

impl SolutionReader<String> for AspartixSolutionReader {
    fn read_extension_line_from_str(&self, line: &str) -> Result<ArgumentSet<String>> {
        match APX_EXTENSION_LINE_PATTERN.captures(line) {
            Some(c) if c.get(1).is_none() => ArgumentSet::new(&[]),
            Some(c) => ArgumentSet::new(
                &c[1]
                    .split(',')
                    .map(|a| a.trim().to_string())
                    .collect::<Vec<String>>(),
            ),
            None => Err(anyhow!(r#"expected an extension line, found "{}""#, line)),
        }
    }
}

/// A structure used to read solutions returned by TGF solvers.
pub struct TGFSolutionReader;

impl TGFSolutionReader {
    /// Builds a new reader for TGF solutions.
    pub fn new() -> Self {
        TGFSolutionReader
    }
}

impl SolutionReader<usize> for TGFSolutionReader {
    fn read_extension_line_from_str(&self, line: &str) -> Result<ArgumentSet<usize>> {
        match TGF_EXTENSION_LINE_PATTERN.captures(line) {
            Some(c) if c.get(1).is_none() => ArgumentSet::new(&[]),
            Some(c) => ArgumentSet::new(
                &c[1]
                    .split(',')
                    .map(|a| str::parse(a.trim()).context("while parsing argument"))
                    .collect::<Result<Vec<usize>>>()?,
            ),
            None => Err(anyhow!(r#"expected an extension line, found "{}""#, line)),
        }
    }
}

/// A trait to be implemented by objects intended to write argumentation solver solutions.
pub trait SolutionWriter {
    /// Writes an extension into the provided writer.
    ///
    /// # Arguments
    /// * `writer` - the writer in which the status must be written
    /// * `extension` - the extension
    fn write_extension<T>(&self, writer: &mut dyn Write, extension: &ArgumentSet<T>) -> Result<()>
    where
        T: LabelType;

    /// Writes an acceptance status into the provided writer.
    ///
    /// # Arguments
    /// * `writer` - the writer in which the status must be written
    /// * `status` - the acceptance status
    fn write_acceptance_status(&self, writer: &mut dyn Write, status: bool) -> Result<()> {
        writeln!(writer, "{}", if status { "YES" } else { "NO" })
            .context("while writing an acceptance status")
    }

    /// Writes an extension count into the provided writer.
    ///
    /// # Arguments
    /// * `writer` - the writer in which the status must be written
    /// * `count` - the extension count
    fn write_extension_count(&self, writer: &mut dyn Write, count: usize) -> Result<()> {
        writeln!(writer, "{}", count).context("while writing an extension count")
    }

    /// Writes an extension set into the provided writer.
    ///
    /// # Arguments
    /// * `writer` - the writer in which the status must be written
    /// * `extension_set` - the extension set
    fn write_extension_set<T>(
        &self,
        writer: &mut dyn Write,
        extension_set: &[&ArgumentSet<T>],
    ) -> Result<()>
    where
        T: LabelType,
    {
        let context: &str = "while writing an extension set";
        writeln!(writer, "[").context(context)?;
        for ext in extension_set {
            self.write_extension(writer, ext).context(context)?;
        }
        writeln!(writer, "]").context(context)
    }
}

/// A structure used to writes solutions like APX solvers.
pub struct AspartixSolutionWriter;

impl AspartixSolutionWriter {
    /// Builds a new writer for APX solver solutions.
    pub fn new() -> Self {
        AspartixSolutionWriter
    }
}

impl SolutionWriter for AspartixSolutionWriter {
    fn write_extension<T>(&self, writer: &mut dyn Write, extension: &ArgumentSet<T>) -> Result<()>
    where
        T: LabelType,
    {
        writeln!(
            writer,
            "[{}]",
            extension
                .iter()
                .map(|a| format!("{}", a))
                .fold(String::new(), |acc, s| if acc.is_empty() {
                    s
                } else {
                    format!("{}, {}", acc, s)
                })
        )
        .context("while writing an extension")
    }
}

/// A structure used to writes solutions like TGF solvers.
pub struct TGFSolutionWriter;

impl TGFSolutionWriter {
    /// Builds a new writer for TGF solver solutions.
    pub fn new() -> Self {
        TGFSolutionWriter
    }
}

impl SolutionWriter for TGFSolutionWriter {
    fn write_extension<T>(&self, writer: &mut dyn Write, extension: &ArgumentSet<T>) -> Result<()>
    where
        T: LabelType,
    {
        writeln!(
            writer,
            "[{}]",
            extension
                .iter()
                .map(|a| format!("{}", a.id()))
                .fold(String::new(), |acc, s| if acc.is_empty() {
                    s
                } else {
                    format!("{}, {}", acc, s)
                })
        )
        .context("while writing an extension")
    }
}

// kcov-ignore-start

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read, Seek, SeekFrom};

    use super::*;

    #[test]
    fn test_acceptance_status_yes() {
        let answer = "YES\n";
        assert_eq!(
            true,
            AspartixSolutionReader::new()
                .read_acceptance_status(&mut answer.as_bytes())
                .unwrap()
        );
    }

    #[test]
    fn test_acceptance_status_no() {
        let answer = "NO\n";
        assert_eq!(
            false,
            AspartixSolutionReader::new()
                .read_acceptance_status(&mut answer.as_bytes())
                .unwrap()
        );
    }

    #[test]
    fn test_acceptance_status_crlf() {
        let answer = "YES\r\n";
        assert_eq!(
            true,
            AspartixSolutionReader::new()
                .read_acceptance_status(&mut answer.as_bytes())
                .unwrap()
        );
    }

    #[test]
    fn test_wrong_acceptance_status() {
        let answer = "MAYBE\n";
        assert_eq!(
            "expected an acceptance status, found \"MAYBE\"",
            AspartixSolutionReader::new()
                .read_acceptance_status(&mut answer.as_bytes())
                .unwrap_err()
                .to_string()
        );
    }

    #[test]
    fn test_empty_acceptance_status() {
        let answer = "";
        assert_eq!(
            "read EOF while parsing an acceptance status",
            AspartixSolutionReader::new()
                .read_acceptance_status(&mut answer.as_bytes())
                .unwrap_err()
                .to_string()
        );
    }

    #[test]
    fn test_acceptance_status_no_newline() {
        let answer = "YES or NO";
        assert_eq!(
            "expected an acceptance status, found \"YES or NO\"",
            AspartixSolutionReader::new()
                .read_acceptance_status(&mut answer.as_bytes())
                .unwrap_err()
                .to_string()
        );
    }

    #[test]
    fn test_extension_line_empty() {
        let answer = "[]";
        let extension = AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(0, extension.len());
    }

    #[test]
    fn test_extension_line_single_arg() {
        let answer = "[a0]";
        let extension = AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(
            ["a0"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            extension
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_extension_line_two_args() {
        let answer = "[a0, a1]";
        let extension = AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(
            ["a0", "a1"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            extension
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_extension_line_two_args_no_spaces() {
        let answer = "[a0,a1]";
        let extension = AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(
            ["a0", "a1"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            extension
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_extension_line_with_spaces() {
        let answer = " [ a0 , a1 ] ";
        let extension = AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(
            ["a0", "a1"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            extension
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_extension_line_no_brackets() {
        let answer = "a0, a1";
        assert!(AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_line_no_comma() {
        let answer = "[a0 a1]";
        assert!(AspartixSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_empty_single_line() {
        let answer = "[]";
        assert_eq!(
            0,
            AspartixSolutionReader::new()
                .read_extension_set(&mut answer.as_bytes())
                .unwrap()
                .len()
        );
    }

    #[test]
    fn test_extension_set_empty_two_lines() {
        let answer = "[\n]";
        assert_eq!(
            0,
            AspartixSolutionReader::new()
                .read_extension_set(&mut answer.as_bytes())
                .unwrap()
                .len()
        );
    }

    #[test]
    fn test_extension_set_containing_one() {
        let answer = "[\n[a0, a1]\n]";
        let ext_set = AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(1, ext_set.len());
        assert_eq!(
            ["a0", "a1"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            ext_set[0]
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_extension_set_containing_two() {
        let answer = "[\n[a0, a1]\n[a0, a2]\n]";
        let ext_set = AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(2, ext_set.len());
        assert_eq!(
            ["a0", "a1"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            ext_set[0]
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
        assert_eq!(
            ["a0", "a2"]
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>(),
            ext_set[1]
                .iter()
                .map(|a| a.label().to_string())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_extension_set_containing_empty_extension() {
        let answer = "[\n[]\n]";
        let ext_set = AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(1, ext_set.len());
        assert_eq!(0, ext_set[0].len());
    }

    #[test]
    fn test_extension_set_empty_single_line_err() {
        let answer = "[] a";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_empty_two_lines_err_on_first() {
        let answer = "[a\n]";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_empty_two_lines_err_on_second() {
        let answer = "[\n]a";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_two_lines_err_on_arg() {
        let answer = "[\na0\n]";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_two_opening() {
        let answer = "[\n[\n]";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_empty_no_closing() {
        let answer = "[\n";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_set_eof() {
        let answer = "";
        assert!(AspartixSolutionReader::new()
            .read_extension_set(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_count() {
        let answer = "1";
        let ext_count = AspartixSolutionReader::new()
            .read_extension_count(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(1, ext_count);
    }

    #[test]
    fn test_extension_count_negative() {
        let answer = "-1";
        assert!(AspartixSolutionReader::new()
            .read_extension_count(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_extension_count_nan() {
        let answer = "a";
        assert!(AspartixSolutionReader::new()
            .read_extension_count(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_write_acceptance_status_yes() {
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_acceptance_status(&mut cursor, true)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("YES\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_acceptance_status_no() {
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_acceptance_status(&mut cursor, false)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("NO\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_extension_count() {
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_extension_count(&mut cursor, 1)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("1\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_extension_no_args() {
        let extension = ArgumentSet::new(&[] as &[String]).unwrap();
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_extension(&mut cursor, &extension)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[]\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_extension_one_arg() {
        let extension = ArgumentSet::new(&["a"]).unwrap();
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_extension(&mut cursor, &extension)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[a]\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_extension_two_args() {
        let extension = ArgumentSet::new(&["a", "b"]).unwrap();
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_extension(&mut cursor, &extension)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[a, b]\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_extension_set() {
        let extension_set = vec![
            ArgumentSet::new(&[]).unwrap(),
            ArgumentSet::new(&["a"]).unwrap(),
            ArgumentSet::new(&["a", "b"]).unwrap(),
        ];
        let mut cursor = Cursor::new(vec![]);
        AspartixSolutionWriter::new()
            .write_extension_set(
                &mut cursor,
                &extension_set.iter().collect::<Vec<&ArgumentSet<&str>>>(),
            )
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[\n[]\n[a]\n[a, b]\n]\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_tgf_extension_line_empty() {
        let answer = "[]";
        let extension = TGFSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(0, extension.len());
    }

    #[test]
    fn test_tgf_extension_line_single_arg() {
        let answer = "[0]";
        let extension = TGFSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(
            vec![0],
            extension.iter().map(|a| a.id()).collect::<Vec<usize>>()
        );
    }

    #[test]
    fn test_tgf_extension_line_two_args() {
        let answer = "[0, 1]";
        let extension = TGFSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .unwrap();
        assert_eq!(
            vec![0, 1],
            extension.iter().map(|a| a.id()).collect::<Vec<usize>>()
        );
    }

    #[test]
    fn test_tgf_extension_line_no_brackets() {
        let answer = "0, 1";
        assert!(TGFSolutionReader::new()
            .read_extension(&mut answer.as_bytes())
            .is_err());
    }

    #[test]
    fn test_write_tgf_extension_no_args() {
        let extension = ArgumentSet::new(&[] as &[String]).unwrap();
        let mut cursor = Cursor::new(vec![]);
        TGFSolutionWriter::new()
            .write_extension(&mut cursor, &extension)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[]\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_tgf_extension_one_arg() {
        let extension = ArgumentSet::new(&["a"]).unwrap();
        let mut cursor = Cursor::new(vec![]);
        TGFSolutionWriter::new()
            .write_extension(&mut cursor, &extension)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[0]\n", String::from_utf8(out).unwrap());
    }

    #[test]
    fn test_write_tgf_two_args() {
        let extension = ArgumentSet::new(&["a", "b"]).unwrap();
        let mut cursor = Cursor::new(vec![]);
        TGFSolutionWriter::new()
            .write_extension(&mut cursor, &extension)
            .unwrap();
        cursor.seek(SeekFrom::Start(0)).unwrap();
        let mut out = Vec::new();
        cursor.read_to_end(&mut out).unwrap();
        assert_eq!("[0, 1]\n", String::from_utf8(out).unwrap());
    }
}

// kcov-ignore-end
