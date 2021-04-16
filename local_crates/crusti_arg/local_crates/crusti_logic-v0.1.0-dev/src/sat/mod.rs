// crusti_logic
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

mod cadical_sat_solver;
pub use cadical_sat_solver::CadicalSatSolver;

pub mod equivalence;

mod sat_solver;
pub use sat_solver::default_sat_solver;
pub use sat_solver::ConsistencyCheckResult;
pub use sat_solver::SatSolver;
pub use sat_solver::MAYBE_TIMEOUT_MSG;

mod tseitin_encoder;
pub use tseitin_encoder::TseitinEncoder;

mod var_mapper_solver;
pub(crate) use var_mapper_solver::VarMapperSolver;
