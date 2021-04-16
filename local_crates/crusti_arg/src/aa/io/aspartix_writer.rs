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

/// A writer for the Aspartix format.
///
/// This object is used to write an [`AAFramework`] using the Aspartix input format, as defined on [the Aspartix website](https://www.dbai.tuwien.ac.at/research/argumentation/aspartix/dung.html).
///
/// # Example
///
/// The following example retrieves an AF and writes it to the standard output using the Aspartix format.
///
/// ```
/// # use crusti_arg::AAFramework;
/// # use crusti_arg::ArgumentSet;
/// # use crusti_arg::AspartixWriter;
/// # use crusti_arg::LabelType;
/// # use anyhow::Result;
/// fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
///     let writer = AspartixWriter::default();
///     writer.write(&af, &mut std::io::stdout())
/// }
/// # write_af_to_stdout(&AAFramework::new(ArgumentSet::new(&[] as &[String]).unwrap()));
/// ```
///
/// [`AAFramework`]: struct.AAFramework.html
#[derive(Default)]
pub struct AspartixWriter {}

impl AspartixWriter {
    /// Writes a framework using the Aspartix format to the provided writer.
    ///
    /// # Arguments
    ///
    /// * `framework` - the framework
    /// * `writer` - the writer
    ///
    /// # Example
    ///
    /// The following example retrieves an AF and writes it to the standard output using the Aspartix format.
    ///
    /// ```
    /// # use crusti_arg::AAFramework;
    /// # use crusti_arg::ArgumentSet;
    /// # use crusti_arg::AspartixWriter;
    /// # use crusti_arg::LabelType;
    /// # use anyhow::Result;
    /// fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
    ///     let writer = AspartixWriter::default();
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
            writeln!(writer, "arg({}).", arg.to_string())?;
        }
        for attack in framework.iter_attacks() {
            writeln!(
                writer,
                "att({},{}).",
                attack.attacker().to_string(),
                attack.attacked().to_string(),
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
        let writer = AspartixWriter::default();
        writer.write(&framework, &mut result).unwrap();
        assert_eq!(
            "arg(a).\narg(b).\narg(c).\natt(a,a).\natt(b,c).\n",
            result.to_string()
        )
    }
}
