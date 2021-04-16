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

use crate::aa::aa_framework::AAFramework;
use crate::aa::arguments::LabelType;
use anyhow::Result;
use std::io::Write;

/// A writer for the TGF format.
///
/// This object is used to write an [`AAFramework`] using the Aspartix input format.
/// See [Wikipedia](https://en.wikipedia.org/wiki/Trivial_Graph_Format) for more information on the format.
///
/// # Example
///
/// The following example retrieves an AF and writes it to the standard output using the Aspartix format.
///
/// ```
/// # use crusti_arg::AAFramework;
/// # use crusti_arg::ArgumentSet;
/// # use crusti_arg::TGFWriter;
/// # use crusti_arg::LabelType;
/// # use anyhow::Result;
/// fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
///     let writer = TGFWriter::new();
///     writer.write(&af, &mut std::io::stdout())
/// }
/// # write_af_to_stdout(&AAFramework::new(ArgumentSet::new(&[] as &[String]).unwrap()));
/// ```
///
/// [`AAFramework`]: struct.AAFramework.html
pub struct TGFWriter {
    arg_labels: bool,
}

impl TGFWriter {
    /// Creates a new `TGFWriter` with default parameters.
    ///
    /// By default, the argument labels are not shown.
    /// To change this setting, call the function [`display_arg_labels`](`Self::display_arg_labels`).
    pub fn new() -> Self {
        TGFWriter { arg_labels: false }
    }

    /// Enables/disables the display of the argument labels.
    ///
    /// Setting `true` enables the display, see `false` disables it.
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::AAFramework;
    /// # use crusti_arg::ArgumentSet;
    /// # use crusti_arg::TGFWriter;
    /// # use crusti_arg::LabelType;
    /// # use anyhow::Result;
    /// fn write_af_to_stdout_with_labels<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
    ///     let mut writer = TGFWriter::new();
    ///     writer.display_arg_labels(true);
    ///     writer.write(&af, &mut std::io::stdout())
    /// }
    /// # write_af_to_stdout_with_labels(&AAFramework::new(ArgumentSet::new(&[] as &[String]).unwrap()));
    /// ```
    pub fn display_arg_labels(&mut self, display: bool) {
        self.arg_labels = display
    }

    /// Writes a framework using the TGF format to the provided writer.
    ///
    /// # Arguments
    ///
    /// * `framework` - the framework
    /// * `writer` - the writer
    ///
    /// # Example
    ///
    /// The following example retrieves an AF and writes it to the standard output using the TGF format.
    ///
    /// ```
    /// # use crusti_arg::AAFramework;
    /// # use crusti_arg::ArgumentSet;
    /// # use crusti_arg::TGFWriter;
    /// # use crusti_arg::LabelType;
    /// # use anyhow::Result;
    /// fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
    ///     let writer = TGFWriter::new();
    ///     writer.write(&af, &mut std::io::stdout())
    /// }
    /// # write_af_to_stdout(&AAFramework::new(ArgumentSet::new(&[] as &[String]).unwrap()));
    /// ```
    ///
    /// [`AAFramework`]: struct.AAFramework.html
    pub fn write<T: LabelType>(
        &self,
        framework: &AAFramework<T>,
        writer: &mut dyn Write,
    ) -> Result<()> {
        let args = framework.argument_set();
        for arg in args.iter() {
            if self.arg_labels {
                writeln!(writer, "{} {}", arg.id(), arg.label())?;
            } else {
                writeln!(writer, "{}", arg.id())?;
            }
        }
        writeln!(writer, "#")?;
        for attack in framework.iter_attacks() {
            writeln!(
                writer,
                "{} {}",
                attack.attacker().id(),
                attack.attacked().id(),
            )?;
        }
        writer.flush()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aa::arguments::ArgumentSet;
    use crate::utils::writable_string::WritableString;

    #[test]
    fn test_write() {
        let arg_names = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_names).unwrap();
        let mut framework = AAFramework::new(args);
        framework.new_attack(&arg_names[0], &arg_names[0]).unwrap();
        framework.new_attack(&arg_names[1], &arg_names[2]).unwrap();
        let mut result = WritableString::default();
        let writer = TGFWriter::new();
        writer.write(&framework, &mut result).unwrap();
        assert_eq!("0\n1\n2\n#\n0 0\n1 2\n", result.to_string())
    }

    #[test]
    fn test_write_with_labels() {
        let arg_names = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_names).unwrap();
        let mut framework = AAFramework::new(args);
        framework.new_attack(&arg_names[0], &arg_names[0]).unwrap();
        framework.new_attack(&arg_names[1], &arg_names[2]).unwrap();
        let mut result = WritableString::default();
        let mut writer = TGFWriter::new();
        writer.display_arg_labels(true);
        writer.write(&framework, &mut result).unwrap();
        assert_eq!("0 a\n1 b\n2 c\n#\n0 0\n1 2\n", result.to_string())
    }
}
