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

//! Crusti_arg is a library and an app used to handle Argumentation Frameworks.
//!
//! # Abstract Argument Frameworks
//!
//! This library allows to handle Abstract Argumentation Frameworks through the [`AAFramework`] struct.
//!
//! In order to create an AAF, you must provide its argument set, which is itself built upon the labels of the set of arguments.
//! Any type following the [`LabelType`] trait may be used to build an argument set.
//! When the AAF is built, you can then add attacks to it.
//!
//! ```
//! # use crusti_arg::{ArgumentSet, AAFramework};
//! let labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
//! let arguments = ArgumentSet::new(&labels).unwrap();
//! let mut framework = AAFramework::new(arguments);
//! assert_eq!(3, framework.argument_set().len());
//! assert_eq!(0, framework.iter_attacks().count());
//! framework.new_attack(&labels[0], &labels[1]);
//! assert_eq!(1, framework.iter_attacks().count());
//! ```
//!
//! # Reading and writing AAF
//!
//! The library provides structures to read and write AAFs, taking advantage of [the Aspartix format](https://www.dbai.tuwien.ac.at/research/argumentation/aspartix/dung.html).
//!
//! Use the [`AspartixReader`] to read an AAF from a reader (the label type will be `String`).
//!
//! ```
//! # use crusti_arg::{AAFramework, AspartixReader};
//! fn read_af_from_str(s: &str) -> AAFramework<String> {
//!     let reader = AspartixReader::default();
//!     reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
//! }
//! # read_af_from_str("arg(a).");
//! ```
//!
//! Use the [`AspartixWriter`] to write an AAF using the provided writer.
//!
//! ```
//! # use crusti_arg::AAFramework;
//! # use crusti_arg::ArgumentSet;
//! # use crusti_arg::AspartixWriter;
//! # use crusti_arg::LabelType;
//! # use anyhow::Result;
//! fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
//!     let writer = AspartixWriter::default();
//!     writer.write(&af, &mut std::io::stdout())
//! }
//! # write_af_to_stdout(&AAFramework::new(ArgumentSet::new(&[] as &[String]).unwrap()));
//! ```
//!
//! # License
//!
//! Crusti_binnet is developed at CRIL (Centre de Recherche en Informatique de Lens).
//! It is made available under the terms of the GNU GPLv3 license.
//!
//! [`AAFramework`]: struct.AAFramework.html
//! [`AspartixReader`]: struct.AspartixReader.html
//! [`AspartixWriter`]: struct.AspartixWriter.html
//! [`LabelType`]: trait.LabelType.html

#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

mod aa;

pub use crate::aa::aa_framework::{AAFramework, Attack};
pub use crate::aa::arguments::{Argument, ArgumentSet, LabelType};

pub use crate::aa::io::AspartixReader;
pub use crate::aa::io::AspartixSolutionReader;
pub use crate::aa::io::AspartixSolutionWriter;
pub use crate::aa::io::AspartixWriter;
pub use crate::aa::io::SolutionReader;
pub use crate::aa::io::SolutionWriter;
pub use crate::aa::io::TGFSolutionReader;
pub use crate::aa::io::TGFSolutionWriter;
pub use crate::aa::io::TGFWriter;

mod utils;

