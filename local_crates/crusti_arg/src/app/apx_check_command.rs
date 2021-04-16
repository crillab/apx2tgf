// crusti_arg
// Copyright (C) 2021  Artois University and CNRS
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

use anyhow::{Context, Result};
use crusti_app_helper::{info, warn, App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_arg::AspartixReader;
use std::{fs::File, path::PathBuf};

const CMD_NAME: &str = "apx_check";

#[derive(Default)]
pub(crate) struct ApxCheckCommand();

impl<'a> Command<'a> for ApxCheckCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("check an Aspartix file")
            .global_setting(AppSettings::DisableVersion)
            .global_setting(AppSettings::VersionlessSubcommands)
            .arg(
                Arg::with_name("INPUT_FILE")
                    .help("Sets the input file to check")
                    .required(true),
            )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let str_path = arg_matches.value_of("INPUT_FILE").unwrap();
        self.execute_internal(str_path)
    }
}

impl ApxCheckCommand {
    fn execute_internal(&self, str_path: &str) -> Result<()> {
        info!("executing APX checker");
        info!("input file is {}", str_path);
        let path = PathBuf::from(str_path);
        let mut file_reader =
            File::open(&path).with_context(|| format!("while opening file {}", &path.display()))?;
        let mut apx_reader = AspartixReader::default();
        let mut warning_counter = 0;
        let mut warning_handler = |line, reason| {
            warn!("line {}: {}", line, reason);
            warning_counter += 1;
        };
        apx_reader.add_warning_handler(&mut warning_handler);
        let af = apx_reader.read(&mut file_reader)?;
        info!("instance was read without errors");
        match warning_counter {
            0 => info!("no warnings were found"),
            n => info!("got {} warning(s)", n),
        }
        info!(
            "instance contains {} argument(s) and {} attack(s)",
            af.argument_set().len(),
            af.n_attacks()
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Error;
    use crusti_app_helper::Level;
    use logtest::Logger;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn logtest() {
        let mut logger = Logger::start();
        logtest_execute_ok(&mut logger);
        logtest_execute_warning_spaces_next_to_arg_name(&mut logger);
        logtest_execute_error_syntax_error(&mut logger);
        logtest_execute_error_multiple_def_of_arg(&mut logger);
        logtest_execute_error_no_such_arg_in_attack(&mut logger);
        assert!(logger.pop().is_none());
    }

    fn assert_log_message<T>(logger: &mut Logger, level: Level, message: T)
    where
        T: AsRef<str>,
    {
        let log_message = logger.pop().unwrap();
        assert_eq!(
            level,
            log_message.level(),
            "expected log level {}, got log level {} and message \"{}\"",
            level,
            log_message.level(),
            log_message.args()
        );
        assert_eq!(
            message.as_ref(),
            log_message.args(),
            "expected message \"{}\", got log level {} and message \"{}\"",
            message.as_ref(),
            log_message.level(),
            log_message.args()
        );
    }

    fn assert_err_message(expected_chain: Vec<&'static str>, actual: Error) {
        let error_chain: Vec<String> = actual.chain().map(|e| format!("{}", e)).collect();
        assert_eq!(expected_chain, error_chain);
    }

    fn logtest_execute_ok(mut logger: &mut Logger) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all("arg(a0).\narg(a1).\natt(a0,a1).\n\n".as_bytes())
            .unwrap();
        let apx = ApxCheckCommand::default();
        let file_path = format!("{}", file.path().display());
        apx.execute_internal(&format!("{}", file_path)).unwrap();
        assert_log_message(&mut logger, Level::Info, "executing APX checker");
        assert_log_message(
            &mut logger,
            Level::Info,
            format!("input file is {}", file_path),
        );
        assert_log_message(&mut logger, Level::Info, "instance was read without errors");
        assert_log_message(&mut logger, Level::Info, "no warnings were found");
        assert_log_message(
            &mut logger,
            Level::Info,
            "instance contains 2 argument(s) and 1 attack(s)",
        );
        assert!(logger.pop().is_none());
    }

    fn logtest_execute_warning_spaces_next_to_arg_name(mut logger: &mut Logger) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all("arg( a0).\narg(a1).\natt(a0,a1).\n\n".as_bytes())
            .unwrap();
        let apx = ApxCheckCommand::default();
        let file_path = format!("{}", file.path().display());
        apx.execute_internal(&format!("{}", file_path)).unwrap();
        assert_log_message(&mut logger, Level::Info, "executing APX checker");
        assert_log_message(
            &mut logger,
            Level::Info,
            format!("input file is {}", file_path),
        );
        assert_log_message(
            &mut logger,
            Level::Warn,
            "line 0: argument names beginning or ending by spaces may be ambiguous",
        );
        assert_log_message(&mut logger, Level::Info, "instance was read without errors");
        assert_log_message(&mut logger, Level::Info, "got 1 warning(s)");
        assert_log_message(
            &mut logger,
            Level::Info,
            "instance contains 2 argument(s) and 1 attack(s)",
        );
        assert!(logger.pop().is_none());
    }

    fn logtest_execute_error(
        mut logger: &mut Logger,
        instance: &'static str,
        expected_error_chain: Vec<&'static str>,
    ) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(instance.as_bytes()).unwrap();
        let apx = ApxCheckCommand::default();
        let file_path = format!("{}", file.path().display());
        let error = apx.execute_internal(&format!("{}", file_path)).unwrap_err();
        assert_err_message(expected_error_chain, error);
        assert_log_message(&mut logger, Level::Info, "executing APX checker");
        assert_log_message(
            &mut logger,
            Level::Info,
            format!("input file is {}", file_path),
        );
        assert!(logger.pop().is_none());
    }

    fn logtest_execute_error_syntax_error(logger: &mut Logger) {
        logtest_execute_error(
            logger,
            "arg(a0)\narg(a1).\natt(a0,a1).\n\n",
            vec!["while reading line 0", "syntax error in line \"arg(a0)\""],
        );
    }

    fn logtest_execute_error_multiple_def_of_arg(logger: &mut Logger) {
        logtest_execute_error(
            logger,
            "arg(a0).\narg(a0).\natt(a0,a0).\n\n",
            vec!["multiple definitions of argument a0"],
        );
    }

    fn logtest_execute_error_no_such_arg_in_attack(logger: &mut Logger) {
        logtest_execute_error(
            logger,
            "arg(a0).\narg(a1).\natt(a0,a2).\n\n",
            vec![
                "while reading line 2",
                "cannot add an attack from \"a0\" to \"a2\"",
                "no such argument: a2",
            ],
        );
    }
}
