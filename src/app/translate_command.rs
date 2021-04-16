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
use crusti_app_helper::{info, App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_arg::{AspartixReader, TGFWriter};
use std::{
    fs::{self, File},
    path::PathBuf,
};

pub(crate) struct TranslateCommand;

const CMD_NAME: &str = "translate";

const ARG_INPUT: &str = "INPUT";

impl TranslateCommand {
    pub fn new() -> Self {
        TranslateCommand
    }
}

impl<'a> Command<'a> for TranslateCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Translates an APX-encoded Argumentation Framework into the TGF format.")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name(ARG_INPUT)
                    .long("input")
                    .short("i")
                    .takes_value(true)
                    .help("sets the APX input file")
                    .required(true),
            )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let file_path = arg_matches.value_of(ARG_INPUT).unwrap();
        info!(
            "reading input file {}",
            fs::canonicalize(&PathBuf::from(file_path))
                .unwrap()
                .display()
        );
        let mut file = File::open(file_path)
            .with_context(|| format!(r#"while opening file "{}""#, file_path))?;
        let reader = AspartixReader::default();
        let af = reader.read(&mut file)?;
        let writer = TGFWriter::new();
        writer.write(&af, &mut std::io::stdout())
    }
}
