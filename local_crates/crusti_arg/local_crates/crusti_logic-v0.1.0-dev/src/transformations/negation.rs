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

use crate::{core::FormulaNodeMarker, Formula, NnfFormula};

/// A [`Formula`] that can be negated into another [`Formula`].
///
/// The source and target languages may be different;
/// the target languages is given by the type `T`.
/// For example, the negation of a [`Clause`](crate::Clause) is a [`Term`](crate::Term).
pub trait Negation<T> {
    /// Negates the current formula, consuming it to produce a new one of type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Clause, Negation, Term};
    ///
    /// let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
    /// let t = Term::new(vec![(0, true), (1, false)].into()).unwrap();
    /// assert_eq!(t, c.negate());
    /// ```
    fn negate(self) -> T;
}

pub(crate) fn simple_negate<T>(source: T) -> NnfFormula
where
    T: Formula,
{
    let root = source.root();
    let mut marker = FormulaNodeMarker::new();
    root.borrow_mut().negate(&mut marker);
    root.borrow_mut().unmark_recursive(&mut marker);
    NnfFormula::from_data(root, source.n_vars())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        languages::{Clause, Term},
        utils::MaybeTrivial,
    };

    #[test]
    fn test_simple_negate() {
        let clause = MaybeTrivial::<Clause>::from(vec![(0, false), (1, false)]).unwrap();
        let term = MaybeTrivial::<Term>::from(vec![(0, true), (1, true)]).unwrap();
        assert_eq!(
            term.root().borrow().node_kind(),
            simple_negate(clause.clone()).root().borrow().node_kind()
        );
        assert_eq!(
            clause.root().borrow().node_kind(),
            simple_negate(term).root().borrow().node_kind()
        );
    }
}
