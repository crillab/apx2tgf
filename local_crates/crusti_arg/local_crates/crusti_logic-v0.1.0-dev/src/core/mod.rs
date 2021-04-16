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

mod formula;
pub use formula::Formula;

mod formula_node;
pub use formula_node::FormulaNode;
pub use formula_node::FormulaNodeKind;
pub(crate) use formula_node::FormulaNodeMarker;

mod literal;
pub use literal::Literal;
pub(crate) use literal::LiteralVec;
pub use literal::VarId;
