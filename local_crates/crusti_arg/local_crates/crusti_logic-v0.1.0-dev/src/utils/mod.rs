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

mod maybe_trivial;
pub use maybe_trivial::MaybeTrivial;

mod rc_mut;
#[cfg(not(feature = "mt"))]
pub use rc_mut::RcMut;

mod rc_mut_mt;
#[cfg(feature = "mt")]
pub use rc_mut_mt::RcMut;
