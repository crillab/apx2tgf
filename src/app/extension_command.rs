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

use anyhow::{Context, Result};
use crusti_app_helper::{App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_arg::{
    ArgumentSet, AspartixReader, AspartixSolutionWriter, SolutionReader, SolutionWriter,
    TGFSolutionReader,
};
use std::fs;
use std::io::BufReader;

pub(crate) struct ExtensionCommand;

const CMD_NAME: &str = "extension";

const ARG_EXT: &str = "EXTENSION";

impl ExtensionCommand {
    pub fn new() -> Self {
        ExtensionCommand
    }
}

impl<'a> Command<'a> for ExtensionCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Translates a TGF extension obtained from a translated APX framework.")
            .setting(AppSettings::DisableVersion)
            .arg(super::arg_input())
            .arg(super::arg_output())
            .arg(
                Arg::with_name(ARG_EXT)
                    .long("extension")
                    .short("e")
                    .takes_value(true)
                    .help("sets the file containing the TGF extension")
                    .required(true),
            )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let reader = AspartixReader::default();
        let af = reader.read(&mut super::create_input(arg_matches)?)?;
        let content = fs::read_to_string(arg_matches.value_of(ARG_EXT).unwrap())?;
        let tgf_solution_reader = TGFSolutionReader::new();
        let tgf_extension = tgf_solution_reader
            .read_extension(&mut BufReader::new(content.trim().as_bytes()))
            .context("while reading the extension")?;
        let apx_solution_writer = AspartixSolutionWriter::new();
        let apx_labels = tgf_extension
            .iter()
            .map(|a| af.argument_set().get_argument_by_id(*a.label()).label().clone())
            .collect::<Vec<String>>();
        let apx_extension = ArgumentSet::new(&apx_labels)?;
        apx_solution_writer
            .write_extension(super::create_output(arg_matches)?.as_mut(), &apx_extension)
    }
}
