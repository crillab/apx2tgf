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

use crate::{
    Formula, FormulaNode, FormulaNodeKind, Literal, LiteralSetFormula, MaybeTrivial, NnfFormula,
    RcMut, Term,
};

/// A trait for formula languages that can be conditioned by literals.
pub trait Conditioning<T> {
    /// Returns a copy of this formula conditioned by a single literal.
    ///
    /// The conditioning process may return a trivial formula.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Clause, Conditioning, Formula, Literal};
    ///
    /// let c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
    /// let c2 = c.conditioning((2, true).into()).unwrap();
    /// assert_eq!("or(-0, -1)", format!("{}", c2.root().borrow().default_display()));
    /// ```
    fn conditioning(self, l: Literal) -> MaybeTrivial<T>;

    /// Returns a copy of this formula conditioned by a multiple literals grouped in a term.
    ///
    /// The conditioning process may return a trivial formula.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Clause, Conditioning, Formula, Literal, Term};
    ///
    /// let c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
    /// let t = Term::new(vec![(1, true), (2, true)].into()).unwrap();
    /// let c2 = c.conditioning_by_term(&t).unwrap();
    /// assert_eq!("-0", format!("{}", c2.root().borrow().default_display()));
    /// ```
    fn conditioning_by_term(self, t: &Term) -> MaybeTrivial<T>;
}

pub(crate) fn simple_conditioning_by_term<T>(source: T, t: &Term) -> MaybeTrivial<NnfFormula>
where
    T: Formula,
{
    let source_n_vars = source.n_vars();
    let mut conditioning = vec![None; usize::max(t.n_vars(), source_n_vars)];
    t.as_literals()
        .iter()
        .for_each(|l| conditioning[usize::from(l.var_id())] = Some(l.polarity()));
    simple_node_conditioning_by_term(source.root(), &conditioning)
        .map(|r| NnfFormula::from_data(r, source_n_vars))
}

fn simple_node_conditioning_by_term(
    n: RcMut<FormulaNode>,
    conditioning: &[Option<bool>],
) -> MaybeTrivial<RcMut<FormulaNode>> {
    match n.borrow().node_kind() {
        FormulaNodeKind::And(children) => {
            let mut new_children = Vec::with_capacity(children.len());
            for c in children.into_iter() {
                match simple_node_conditioning_by_term(c, conditioning) {
                    MaybeTrivial::NotTrivial(new_c) => new_children.push(new_c),
                    MaybeTrivial::True => {}
                    MaybeTrivial::False => return MaybeTrivial::False,
                }
            }
            FormulaNode::new_and(new_children).map(|n| RcMut::new(n))
        }
        FormulaNodeKind::Or(children) => {
            let mut new_children = Vec::with_capacity(children.len());
            for c in children.into_iter() {
                match simple_node_conditioning_by_term(c, conditioning) {
                    MaybeTrivial::NotTrivial(new_c) => new_children.push(new_c),
                    MaybeTrivial::True => return MaybeTrivial::True,
                    MaybeTrivial::False => {}
                }
            }
            FormulaNode::new_or(new_children).map(|n| RcMut::new(n))
        }
        FormulaNodeKind::Lit(l) => match conditioning[usize::from(l.var_id())] {
            Some(b) => MaybeTrivial::from(b == l.polarity()),
            None => MaybeTrivial::NotTrivial(RcMut::clone(&n)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Clause;

    #[test]
    fn test_conditioning_clause() {
        let c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        let t = Term::new(vec![(1, true), (2, true)].into()).unwrap();
        let c2 = c.conditioning_by_term(&t).unwrap();
        assert_eq!("-0", format!("{}", c2.root().borrow().default_display()));
    }

    #[test]
    fn test_conditioning_clause_becomes_false() {
        let c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        let t = Term::new(vec![(1, true), (2, true), (0, true)].into()).unwrap();
        assert!(c.conditioning_by_term(&t).is_false());
    }

    #[test]
    fn test_conditioning_clause_becomes_true() {
        let c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        let t = Term::new(vec![(1, false)].into()).unwrap();
        assert!(c.conditioning_by_term(&t).is_true());
    }

    #[test]
    fn test_conditioning_term() {
        let c = Term::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        let t = Term::new(vec![(1, false), (2, false)].into()).unwrap();
        let c2 = c.conditioning_by_term(&t).unwrap();
        assert_eq!("-0", format!("{}", c2.root().borrow().default_display()));
    }

    #[test]
    fn test_conditioning_term_becomes_false() {
        let c = Term::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        let t = Term::new(vec![(1, true)].into()).unwrap();
        assert!(c.conditioning_by_term(&t).is_false());
    }

    #[test]
    fn test_conditioning_term_becomes_true() {
        let c = Term::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        let t = Term::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
        assert!(c.conditioning_by_term(&t).is_true());
    }
}
