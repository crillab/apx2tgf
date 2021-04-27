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

mod argument_command;
pub(crate) use argument_command::ArgumentCommand;

mod extension_command;
pub(crate) use extension_command::ExtensionCommand;

mod framework_command;
pub(crate) use framework_command::FrameworkCommand;

use anyhow::{Context, Result};
use crusti_app_helper::{info, Arg, ArgMatches};
use fs::File;
use std::path::PathBuf;
use std::{fs, io::Write};

const ARG_INPUT: &str = "INPUT";
const ARG_OUTPUT: &str = "OUTPUT";

pub(crate) fn arg_input<'a>() -> Arg<'a, 'a> {
    Arg::with_name(ARG_INPUT)
        .long("input")
        .short("i")
        .takes_value(true)
        .help("sets the APX input file")
        .required(true)
}

pub(crate) fn create_input(arg_matches: &ArgMatches<'_>) -> Result<File> {
    let file_path = arg_matches.value_of(ARG_INPUT).unwrap();
    info!("reading input file {}", canonicalize(file_path));
    File::open(file_path).with_context(|| format!(r#"while opening file "{}""#, file_path))
}

pub(crate) fn arg_output<'a>() -> Arg<'a, 'a> {
    Arg::with_name(ARG_OUTPUT)
        .long("output")
        .short("o")
        .takes_value(true)
        .help("sets the TGF output file")
}

pub(crate) fn create_output(arg_matches: &ArgMatches<'_>) -> Result<Box<dyn Write>> {
    Ok(match arg_matches.value_of(ARG_OUTPUT) {
        Some(o) => {
            let r = Box::new(File::create(o)?);
            info!("setting output file to {}", canonicalize(o));
            r
        }
        None => {
            info!("setting output to STDOUT");
            Box::new(std::io::stdout())
        }
    })
}

pub(crate) fn canonicalize(file_path: &str) -> String {
    format!(
        "{}",
        fs::canonicalize(&PathBuf::from(file_path))
            .unwrap()
            .display()
    )
}
