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
    core::LiteralVec, transformations, Conditioning, Formula, FormulaNode, FormulaNodeKind,
    Literal, MaybeTrivial, Negation, NnfFormula, RcMut, Subsumable, VarId, VarReplacement,
};

/// A trait for formulas built on top of a single vector of literals.
pub trait LiteralSetFormula {
    /// Returns an iterator to the literals of this formula.
    fn as_literals(&self) -> &[Literal];
}

macro_rules! default_lit_set_formula_impl {
    ($doc:meta, $t:ident, $lit_combiner:path, $empty_set_eval:expr) => {
        #[$doc]
        #[derive(Debug, Clone)]
        pub struct $t {
            literals: Vec<Literal>,
            is_child: bool,
            n_vars: usize,
        }

        impl $t {
            /// Builds a new instance of this formula given its set of literals.
            ///
            /// The set of literals is reduced if it contains multiple literals referring to the same variable.
            /// If this reduction leads to a trivial formula, the corresponding value of [`MaybeTrivial`](MaybeTrivial) is returned.
            pub fn new(literals: LiteralVec) -> MaybeTrivial<$t> {
                match literals.clean() {
                    None => MaybeTrivial::from(!$empty_set_eval),
                    Some(v) if v.as_slice().is_empty() => MaybeTrivial::from($empty_set_eval),
                    Some(v) => {
                        let n_vars = v.n_vars();
                        MaybeTrivial::NotTrivial($t {
                            literals: v.to_vec(),
                            is_child: false,
                            n_vars: n_vars,
                        })
                    }
                }
            }

            pub(crate) fn from_data_unchecked(
                literals: Vec<Literal>,
                is_child: bool,
                n_vars: usize,
            ) -> Self {
                $t {
                    literals,
                    is_child,
                    n_vars,
                }
            }

            fn from_nnf_unchecked(nnf: NnfFormula) -> MaybeTrivial<$t> {
                match nnf.root().borrow().node_kind() {
                    FormulaNodeKind::And(children) | FormulaNodeKind::Or(children) => {
                        let child_lits = children
                            .iter()
                            .map(|c| {
                                if let FormulaNodeKind::Lit(l) = c.borrow().node_kind() {
                                    l
                                } else {
                                    unreachable!() // kcov-ignore
                                }
                            })
                            .collect::<Vec<Literal>>();
                        $t::new(child_lits.into())
                    }
                    FormulaNodeKind::Lit(l) => $t::new(vec![l].into()),
                }
            }
        }

        impl LiteralSetFormula for $t {
            fn as_literals(&self) -> &[Literal] {
                self.literals.as_slice()
            }
        }

        impl Formula for $t {
            fn root(&self) -> RcMut<FormulaNode> {
                $lit_combiner(
                    self.literals
                        .iter()
                        .map(|l| crate::languages::nnf_formula::NnfFormula::new_literal(*l))
                        .collect::<Vec<crate::languages::nnf_formula::NnfFormula>>()
                        .as_mut_slice(),
                )
                .unwrap()
                .root()
            }

            fn n_vars(&self) -> usize {
                self.n_vars
            }
        }

        impl<T> From<T> for MaybeTrivial<$t>
        where
            T: Into<LiteralVec>,
        {
            fn from(v: T) -> Self {
                $t::new(v.into())
            }
        }

        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                self.literals.eq(&other.as_literals())
            }
        }

        impl Eq for $t {}

        impl PartialOrd for $t {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.as_literals().partial_cmp(&other.as_literals())
            }
        }

        impl Ord for $t {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.as_literals().cmp(&other.as_literals())
            }
        }

        impl Conditioning<$t> for $t {
            fn conditioning(self, l: Literal) -> MaybeTrivial<$t> {
                self.conditioning_by_term(&Term::new(vec![l].into()).unwrap())
            }

            fn conditioning_by_term(self, t: &Term) -> MaybeTrivial<$t> {
                transformations::simple_conditioning_by_term(self, t)
                    .and_then($t::from_nnf_unchecked)
            }
        }

        impl VarReplacement<$t> for $t {
            fn replace_var(self, before: VarId, after: VarId) -> MaybeTrivial<$t> {
                transformations::simple_var_replacement(self, before, after)
                    .and_then($t::from_nnf_unchecked)
            }

            fn replace_lit(self, before: Literal, after: Literal) -> MaybeTrivial<$t> {
                transformations::simple_lit_replacement(self, before, after)
                    .and_then($t::from_nnf_unchecked)
            }
        }
    };
}

fn is_lit_vec_included(first: &[Literal], other: &[Literal]) -> bool {
    if first.len() > other.len() {
        false
    } else {
        let mut j = 0;
        for l in first.iter() {
            while j < other.len() && other[j].var_id() < l.var_id() {
                j += 1;
            }
            if j == other.len() || &other[j] != l {
                return false;
            }
        }
        true
    }
}

default_lit_set_formula_impl!(
    doc = "A [`Formula`](crate::Formula) which is a disjunction of [`Literal`](crate::Literal)s.",
    Clause,
    NnfFormula::new_or,
    false
);

impl Subsumable<Clause> for Clause {
    fn subsums(&self, other: &Clause) -> bool {
        is_lit_vec_included(self.as_literals(), other.as_literals())
    }
}

impl Negation<Term> for Clause {
    fn negate(self) -> Term {
        Term::from_data_unchecked(
            self.literals.iter().map(|l| l.negate()).collect(),
            self.is_child,
            self.n_vars,
        )
    }
}

default_lit_set_formula_impl!(
    doc = "A [`Formula`](crate::Formula) which is a conjunction of [`Literal`](crate::Literal)s.",
    Term,
    NnfFormula::new_and,
    true
);

impl Subsumable<Term> for Term {
    fn subsums(&self, other: &Term) -> bool {
        is_lit_vec_included(other.as_literals(), self.as_literals())
    }
}

impl Negation<Clause> for Term {
    fn negate(self) -> Clause {
        Clause::from_data_unchecked(
            self.literals.iter().map(|l| l.negate()).collect(),
            self.is_child,
            self.n_vars,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::{Literal, LiteralVec},
        utils::MaybeTrivial,
    };

    #[test]
    fn test_clause_new() {
        let clause =
            Clause::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        assert_eq!(2, clause.as_literals().to_vec().len());
    }

    #[test]
    fn test_clause_new_copied_lit() {
        let clause = Clause::new(
            vec![
                Literal::new(0.into(), false),
                Literal::new(1.into(), false),
                Literal::new(1.into(), false),
            ]
            .into(),
        )
        .unwrap();
        assert_eq!(2, clause.as_literals().to_vec().len());
    }

    #[test]
    fn test_clause_new_copied_lit_result_in_single_lit() {
        let clause =
            Clause::new(vec![Literal::new(1.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        assert_eq!(1, clause.as_literals().to_vec().len());
    }

    #[test]
    fn test_clause_new_trivial_true() {
        assert_eq!(
            MaybeTrivial::True,
            Clause::new(vec![Literal::new(0.into(), false), Literal::new(0.into(), true)].into())
        );
    }

    #[test]
    fn test_clause_new_trivial_false() {
        assert_eq!(
            MaybeTrivial::False,
            Clause::new(LiteralVec::from(vec![] as Vec<Literal>))
        );
    }

    #[test]
    fn test_clause_subsums() {
        let cl1 =
            Clause::new(vec![Literal::new(1.into(), false), Literal::new(3.into(), false)].into())
                .unwrap();
        let cl2 = Clause::new(
            vec![
                Literal::new(0.into(), false),
                Literal::new(1.into(), false),
                Literal::new(2.into(), false),
                Literal::new(3.into(), false),
                Literal::new(4.into(), false),
            ]
            .into(),
        )
        .unwrap();
        assert!(cl1.subsums(&cl2));
        assert!(!cl2.subsums(&cl1));
    }

    #[test]
    fn test_clause_subsums_same_len() {
        let cl1 = Clause::new(vec![Literal::new(0.into(), false)].into()).unwrap();
        let cl2 = Clause::new(vec![Literal::new(1.into(), false)].into()).unwrap();
        assert!(cl1.subsums(&cl1));
        assert!(!cl1.subsums(&cl2));
        assert!(!cl2.subsums(&cl1));
    }

    #[test]
    fn test_clause_eq() {
        let cl1 =
            Clause::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        let cl2 =
            Clause::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        let cl3 =
            Clause::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), true)].into())
                .unwrap();
        assert_eq!(cl1, cl2);
        assert_ne!(cl1, cl3);
    }

    #[test]
    fn test_term_new() {
        let term =
            Term::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        assert_eq!(2, term.as_literals().to_vec().len());
    }

    #[test]
    fn test_term_new_copied_lit() {
        let term = Term::new(
            vec![
                Literal::new(0.into(), false),
                Literal::new(1.into(), false),
                Literal::new(1.into(), false),
            ]
            .into(),
        )
        .unwrap();
        assert_eq!(2, term.as_literals().to_vec().len());
    }

    #[test]
    fn test_term_new_copied_lit_result_in_single_lit() {
        let term =
            Term::new(vec![Literal::new(1.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        assert_eq!(1, term.as_literals().to_vec().len());
    }

    #[test]
    fn test_term_new_trivial_false() {
        assert_eq!(
            MaybeTrivial::False,
            Term::new(vec![Literal::new(0.into(), false), Literal::new(0.into(), true)].into())
        );
    }

    #[test]
    fn test_term_new_trivial_true() {
        assert_eq!(
            MaybeTrivial::True,
            Term::new(LiteralVec::from(vec![] as Vec<Literal>))
        );
    }

    #[test]
    fn test_term_subsums() {
        let t1 =
            Term::new(vec![Literal::new(1.into(), false), Literal::new(3.into(), false)].into())
                .unwrap();
        let t2 = Term::new(
            vec![
                Literal::new(0.into(), false),
                Literal::new(1.into(), false),
                Literal::new(2.into(), false),
                Literal::new(3.into(), false),
                Literal::new(4.into(), false),
            ]
            .into(),
        )
        .unwrap();
        assert!(!t1.subsums(&t2));
        assert!(t2.subsums(&t1));
    }

    #[test]
    fn test_term_subsums_same_len() {
        let t1 = Term::new(vec![Literal::new(0.into(), false)].into()).unwrap();
        let t2 = Term::new(vec![Literal::new(1.into(), false)].into()).unwrap();
        assert!(t1.subsums(&t1));
        assert!(!t1.subsums(&t2));
        assert!(!t2.subsums(&t1));
    }

    #[test]
    fn test_term_eq() {
        let t1 =
            Term::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        let t2 =
            Term::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), false)].into())
                .unwrap();
        let t3 =
            Term::new(vec![Literal::new(0.into(), false), Literal::new(1.into(), true)].into())
                .unwrap();
        assert_eq!(t1, t2);
        assert_ne!(t1, t3);
    }
}
