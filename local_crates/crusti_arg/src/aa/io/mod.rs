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

mod aspartix_reader;
pub use aspartix_reader::AspartixReader;

mod aspartix_writer;
pub use aspartix_writer::AspartixWriter;

mod solutions;
pub use solutions::AspartixSolutionReader;
pub use solutions::AspartixSolutionWriter;
pub use solutions::SolutionReader;
pub use solutions::SolutionWriter;
pub use solutions::TGFSolutionReader;
pub use solutions::TGFSolutionWriter;

mod tgf_writer;
pub use tgf_writer::TGFWriter;
