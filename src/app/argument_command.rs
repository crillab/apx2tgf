// fm2apx
// Copyright (C) 2021  Univ. Artois & CNRS
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

use anyhow::{anyhow, Result};
use crusti_app_helper::{App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_arg::AspartixReader;

pub(crate) struct ArgumentCommand;

const CMD_NAME: &str = "argument";

const ARG_ARGUMENT: &str = "ARGUMENT";

impl ArgumentCommand {
    pub fn new() -> Self {
        ArgumentCommand
    }
}

impl<'a> Command<'a> for ArgumentCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Translates an argument name into its TGF index.")
            .setting(AppSettings::DisableVersion)
            .arg(super::arg_input())
            .arg(super::arg_output())
            .arg(
                Arg::with_name(ARG_ARGUMENT)
                    .long("argument")
                    .short("a")
                    .takes_value(true)
                    .help("sets the APX argument")
                    .required(true),
            )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let reader = AspartixReader::default();
        let af = reader.read(&mut super::create_input(arg_matches)?)?;

        let str_arg = arg_matches.value_of(ARG_ARGUMENT).unwrap();
        match af.argument_set().iter().find(|a| a.label() == str_arg) {
            Some(a) => {
                writeln!(super::create_output(arg_matches)?.as_mut(), "{}", a.id())?;
            }
            None => return Err(anyhow!("no such argument in APX file")),
        }
        Ok(())
    }
}
