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

use anyhow::Result;
use crusti_app_helper::{App, AppSettings, ArgMatches, Command, SubCommand};
use crusti_arg::{AspartixReader, TGFWriter};

pub(crate) struct FrameworkCommand;

const CMD_NAME: &str = "framework";

impl FrameworkCommand {
    pub fn new() -> Self {
        FrameworkCommand
    }
}

impl<'a> Command<'a> for FrameworkCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Translates an APX-encoded Argumentation Framework into the TGF format.")
            .setting(AppSettings::DisableVersion)
            .arg(super::arg_input())
            .arg(super::arg_output())
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let reader = AspartixReader::default();
        let af = reader.read(&mut super::create_input(arg_matches)?)?;
        let writer = TGFWriter::new();
        writer.write(&af, super::create_output(arg_matches)?.as_mut())
    }
}
