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
    core::VarId, Formula, FormulaNode, FormulaNodeKind, Literal, MaybeTrivial, NnfFormula, RcMut,
};

/// A trait for formulas able to replace the occurrences of a variable by another variable.
///
/// The source and target languages may be different;
/// the target languages is given by the type `T`.
pub trait VarReplacement<T> {
    /// Replaces the occurrences of a variable by another variable (the polarities are kept).
    /// The formula is consumed.
    ///
    /// The process may return a trivial formula in case the "new" variable already appears in the formula.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Clause, VarId, VarReplacement};
    ///
    /// let mut c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
    /// c = c.replace_var(VarId::from(1), VarId::from(0)).unwrap();
    /// c = c.replace_var(VarId::from(2), VarId::from(3)).unwrap();
    /// assert_eq!(Clause::new(vec![(0, false), (3, false)].into()).unwrap(), c);
    /// ```
    fn replace_var(self, before: VarId, after: VarId) -> MaybeTrivial<T>;

    /// Replaces the occurrences of a literal by another variable (the same applies for the opposite literals).
    /// The formula is consumed.
    ///
    /// The process may return a trivial formula in case the "new" variable already appears in the formula.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Clause, Literal, VarId, VarReplacement};
    ///
    /// let mut c = Clause::new(vec![(0, false), (1, false), (2, false)].into()).unwrap();
    /// c = c.replace_lit(
    ///     Literal::new(VarId::from(1), true),
    ///     Literal::new(VarId::from(3), false)
    /// ).unwrap();
    /// assert_eq!(Clause::new(vec![(0, false), (2, false), (3, true)].into()).unwrap(), c);
    /// ```
    fn replace_lit(self, before: Literal, after: Literal) -> MaybeTrivial<T>;
}

pub(crate) fn simple_var_replacement<T>(
    source: T,
    before: VarId,
    after: VarId,
) -> MaybeTrivial<NnfFormula>
where
    T: Formula,
{
    simple_lit_replacement_from_node(
        source.root(),
        Literal::new(before, true),
        Literal::new(after, true),
    )
    .map(|r| NnfFormula::from_data(r, source.n_vars()))
}

pub(crate) fn simple_lit_replacement<T>(
    source: T,
    before: Literal,
    after: Literal,
) -> MaybeTrivial<NnfFormula>
where
    T: Formula,
{
    simple_lit_replacement_from_node(source.root(), before, after)
        .map(|r| NnfFormula::from_data(r, source.n_vars()))
}

fn simple_lit_replacement_from_node(
    n: RcMut<FormulaNode>,
    before: Literal,
    after: Literal,
) -> MaybeTrivial<RcMut<FormulaNode>> {
    match n.borrow().node_kind() {
        FormulaNodeKind::And(children) => {
            let mut new_children = Vec::with_capacity(children.len());
            for c in children.into_iter() {
                match simple_lit_replacement_from_node(c, before, after) {
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
                match simple_lit_replacement_from_node(c, before, after) {
                    MaybeTrivial::NotTrivial(new_c) => new_children.push(new_c),
                    MaybeTrivial::True => return MaybeTrivial::True,
                    MaybeTrivial::False => {}
                }
            }
            FormulaNode::new_or(new_children).map(|n| RcMut::new(n))
        }
        FormulaNodeKind::Lit(l) if l.var_id() == before.var_id() => {
            MaybeTrivial::NotTrivial(RcMut::new(FormulaNode::new_literal(Literal::new(
                after.var_id(),
                after.polarity() ^ (l.polarity() ^ before.polarity()),
            ))))
        }
        FormulaNodeKind::Lit(_) => MaybeTrivial::NotTrivial(RcMut::clone(&n)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Clause, Term};

    #[test]
    fn test_var_clause() {
        let mut c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        c = c.replace_var(1.into(), 2.into()).unwrap();
        assert_eq!(
            "or(-0, 2)",
            format!("{}", c.root().borrow().default_display())
        );
    }

    #[test]
    fn test_var_clause_becomes_true() {
        let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        assert!(c.replace_var(1.into(), 0.into()).is_true());
    }

    #[test]
    fn test_var_term() {
        let mut t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        t = t.replace_var(1.into(), 2.into()).unwrap();
        assert_eq!(
            "and(-0, 2)",
            format!("{}", t.root().borrow().default_display())
        );
    }

    #[test]
    fn test_var_term_becomes_false() {
        let t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        assert!(t.replace_var(1.into(), 0.into()).is_false());
    }

    #[test]
    fn test_var_propagate_false() {
        let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        let t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        let f = NnfFormula::new_and(&mut [c.into(), t.into()]).unwrap();
        assert!(f.replace_var(1.into(), 0.into()).is_false());
    }

    #[test]
    fn test_var_propagate_true() {
        let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        let t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        let f = NnfFormula::new_or(&mut [c.into(), t.into()]).unwrap();
        assert!(f.replace_var(1.into(), 0.into()).is_true());
    }

    #[test]
    fn test_lit_clause() {
        let mut c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        c = c
            .replace_lit(
                Literal::new(VarId::from(1), true),
                Literal::new(VarId::from(2), true),
            )
            .unwrap();
        assert_eq!(
            "or(-0, 2)",
            format!("{}", c.root().borrow().default_display())
        );
    }

    #[test]
    fn test_lit_clause_becomes_true() {
        let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        assert!(c
            .replace_lit(
                Literal::new(VarId::from(1), true),
                Literal::new(VarId::from(0), true)
            )
            .is_true());
    }

    #[test]
    fn test_lit_term() {
        let mut t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        t = t
            .replace_lit(
                Literal::new(VarId::from(1), true),
                Literal::new(VarId::from(2), true),
            )
            .unwrap();
        assert_eq!(
            "and(-0, 2)",
            format!("{}", t.root().borrow().default_display())
        );
    }

    #[test]
    fn test_lit_term_becomes_false() {
        let t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        assert!(t
            .replace_lit(
                Literal::new(VarId::from(1), true),
                Literal::new(VarId::from(0), true)
            )
            .is_false());
    }

    #[test]
    fn test_lit_propagate_false() {
        let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        let t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        let f = NnfFormula::new_and(&mut [c.into(), t.into()]).unwrap();
        assert!(f
            .replace_lit(
                Literal::new(VarId::from(1), true),
                Literal::new(VarId::from(0), true)
            )
            .is_false());
    }

    #[test]
    fn test_lit_propagate_true() {
        let c = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        let t = Term::new(vec![(0, false), (1, true)].into()).unwrap();
        let f = NnfFormula::new_or(&mut [c.into(), t.into()]).unwrap();
        assert!(f
            .replace_lit(
                Literal::new(VarId::from(1), true),
                Literal::new(VarId::from(0), true)
            )
            .is_true());
    }
}
