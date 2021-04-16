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
    Clause, Conditioning, Formula, FormulaNode, Literal, MaybeTrivial, Negation, NnfFormula, RcMut,
    Term, VarId, VarReplacement,
};

macro_rules! default_flat_formula_impl {
    ($doc:meta, $t:ident, $sub_t:ident, $lit_set_combiner:path, $contrary_t:ident, $contrary_sub_t:ident) => {
        #[$doc]
        #[derive(Debug)]
        pub struct $t {
            sub_formulas: Vec<$sub_t>,
            is_child: bool,
            n_vars: usize,
        }

        impl $t {
            fn new_aux(lit_set_formulas: &mut [$sub_t]) -> MaybeTrivial<Self> {
                lit_set_formulas.sort_unstable();
                let n_vars = lit_set_formulas
                    .iter()
                    .map(|l| (l as &dyn Formula).n_vars())
                    .max()
                    .unwrap_or(0);
                MaybeTrivial::NotTrivial($t {
                    sub_formulas: lit_set_formulas.to_vec(),
                    is_child: false,
                    n_vars,
                })
            }

            fn add_sub_formula(&mut self, sub_f: $sub_t) {
                self.n_vars = usize::max(self.n_vars, (&sub_f as &dyn Formula).n_vars());
                self.sub_formulas.push(sub_f);
            }

            /// Consumes this `CnfFormula`, returning its clauses.
            fn into_sub_formulas(self) -> Vec<$sub_t> {
                self.sub_formulas
            }
        }

        impl Formula for $t {
            fn root(&self) -> RcMut<FormulaNode> {
                $lit_set_combiner(
                    self.sub_formulas
                        .iter()
                        .map(|s| crate::languages::NnfFormula::from_data(s.root(), s.n_vars()))
                        .collect::<Vec<crate::languages::NnfFormula>>()
                        .as_mut_slice(),
                )
                .unwrap()
                .root()
            }

            fn n_vars(&self) -> usize {
                self.n_vars
            }
        }

        impl Conditioning<$t> for $t {
            fn conditioning(self, l: Literal) -> MaybeTrivial<$t> {
                self.conditioning_by_term(&Term::new(vec![l].into()).unwrap())
            }

            fn conditioning_by_term(self, t: &Term) -> MaybeTrivial<$t> {
                let new_sub_formulas = self
                    .into_sub_formulas()
                    .into_iter()
                    .map(|f| f.conditioning_by_term(t))
                    .collect::<Vec<MaybeTrivial<$sub_t>>>();
                MaybeTrivial::<$t>::from(new_sub_formulas)
            }
        }

        impl VarReplacement<$t> for $t {
            fn replace_var(self, before: VarId, after: VarId) -> MaybeTrivial<$t> {
                let new_sub_formulas = self
                    .into_sub_formulas()
                    .into_iter()
                    .map(|f| f.replace_var(before, after))
                    .collect::<Vec<MaybeTrivial<$sub_t>>>();
                MaybeTrivial::<$t>::from(new_sub_formulas)
            }

            fn replace_lit(self, before: Literal, after: Literal) -> MaybeTrivial<$t> {
                let new_sub_formulas = self
                    .into_sub_formulas()
                    .into_iter()
                    .map(|f| f.replace_lit(before, after))
                    .collect::<Vec<MaybeTrivial<$sub_t>>>();
                MaybeTrivial::<$t>::from(new_sub_formulas)
            }
        }

        impl Negation<$contrary_t> for $t {
            fn negate(self) -> $contrary_t {
                let mut new_sub_formulas = self
                    .into_sub_formulas()
                    .into_iter()
                    .map(|f| f.negate())
                    .collect::<Vec<$contrary_sub_t>>();
                $contrary_t::new(&mut new_sub_formulas).unwrap()
            }
        }
    };
}

default_flat_formula_impl!(
    doc = "A [`Formula`](crate::Formula) which is a conjunction of [`Clause`](crate::Clause)s.",
    CnfFormula,
    Clause,
    NnfFormula::new_and,
    DnfFormula,
    Term
);

impl CnfFormula {
    /// Builds a new instance of `CnfFormula` given its [`Clause`]s.
    ///
    /// The set of clauses is reduced if it contains multiple literals referring to the same variable.
    /// If this reduction leads to a trivial formula, the corresponding value of [`MaybeTrivial`](MaybeTrivial) is returned.
    pub fn new(clauses: &mut [Clause]) -> MaybeTrivial<Self> {
        CnfFormula::new_aux(clauses)
    }

    /// Adds a new clause to this `CnfFormula`.
    pub fn add_clause(&mut self, cl: Clause) {
        self.add_sub_formula(cl)
    }

    /// Returns an iterator to the clauses of this `CnfFormula`.
    pub fn as_clauses(&self) -> &[Clause] {
        self.sub_formulas.as_slice()
    }

    /// Consumes this `CnfFormula`, returning its clauses.
    pub fn into_clauses(self) -> Vec<Clause> {
        self.into_sub_formulas()
    }

    /// Returns the number of clauses this `CnfFormula` contains.
    pub fn n_clauses(&self) -> usize {
        self.sub_formulas.len()
    }
}

impl<T> From<Vec<T>> for MaybeTrivial<CnfFormula>
where
    T: Into<MaybeTrivial<Clause>>,
{
    fn from(init_lit_sets: Vec<T>) -> Self {
        let mut lit_sets = Vec::with_capacity(init_lit_sets.len());
        for s in init_lit_sets {
            match s.into() {
                MaybeTrivial::NotTrivial(f) => lit_sets.push(f),
                MaybeTrivial::True => {}
                MaybeTrivial::False => return MaybeTrivial::False,
            }
        }
        if lit_sets.is_empty() {
            return MaybeTrivial::True;
        }
        CnfFormula::new(&mut lit_sets)
    }
}

default_flat_formula_impl!(
    doc = "A [`Formula`](crate::Formula) which is a disjunction of [`Term`](crate::Term)s.",
    DnfFormula,
    Term,
    NnfFormula::new_or,
    CnfFormula,
    Clause
);

impl DnfFormula {
    /// Builds a new instance of `DnfFormula` given its [`Term`]s.
    ///
    /// The set of terms is reduced if it contains multiple literals referring to the same variable.
    /// If this reduction leads to a trivial formula, the corresponding value of [`MaybeTrivial`](MaybeTrivial) is returned.
    pub fn new(clauses: &mut [Term]) -> MaybeTrivial<Self> {
        DnfFormula::new_aux(clauses)
    }

    /// Adds a new term to this `DnfFormula`.
    pub fn add_clause(&mut self, t: Term) {
        self.add_sub_formula(t)
    }

    /// Returns an iterator to the terms of this `DnfFormula`.
    pub fn as_terms(&self) -> &[Term] {
        self.sub_formulas.as_slice()
    }

    /// Consumes this `DnfFormula`, returning its terms.
    pub fn into_terms(self) -> Vec<Term> {
        self.into_sub_formulas()
    }

    /// Returns the number of terms this `DnfFormula` contains.
    pub fn n_terms(&self) -> usize {
        self.sub_formulas.len()
    }
}

impl<T> From<Vec<T>> for MaybeTrivial<DnfFormula>
where
    T: Into<MaybeTrivial<Term>>,
{
    fn from(init_lit_sets: Vec<T>) -> Self {
        let mut lit_sets = Vec::with_capacity(init_lit_sets.len());
        for s in init_lit_sets {
            match s.into() {
                MaybeTrivial::NotTrivial(f) => lit_sets.push(f),
                MaybeTrivial::False => {}
                MaybeTrivial::True => return MaybeTrivial::True,
            }
        }
        if lit_sets.is_empty() {
            return MaybeTrivial::False;
        }
        DnfFormula::new(&mut lit_sets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{core::LiteralVec, FormulaNode, FormulaNodeKind, Literal, LiteralSetFormula, Term};
    use MaybeTrivial;

    fn evaluate_node(node: &FormulaNode, literals: &[Literal]) -> Option<bool> {
        match node.node_kind() {
            FormulaNodeKind::And(children) => {
                let mut has_undefined_child = false;
                for child in children {
                    match evaluate_node(&child.borrow(), literals) {
                        Some(true) => {}
                        Some(false) => return Some(false),
                        None => has_undefined_child = true,
                    }
                }
                if has_undefined_child {
                    None
                } else {
                    Some(true)
                }
            }
            FormulaNodeKind::Or(children) => {
                let mut has_undefined_child = false;
                for child in children {
                    match evaluate_node(&child.borrow(), literals) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => has_undefined_child = true,
                    }
                }
                if has_undefined_child {
                    None
                } else {
                    Some(false)
                }
            }
            FormulaNodeKind::Lit(lit) => {
                if literals.contains(&lit) {
                    Some(true)
                } else if literals.contains(&lit.negate()) {
                    Some(false)
                } else {
                    None
                }
            }
        }
    }

    #[test]
    fn test_cnf_evaluate() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![
                (200, false),
                (688, false),
                (2752, false),
                (4531, false),
                (4850, false),
            ],
            vec![(1246, false), (1402, false), (1405, false), (1478, false)],
            vec![(1816, false), (1817, false), (1863, false)],
            vec![(1872, false), (5535, false)],
        ])
        .unwrap();
        assert_eq!(
            Some(true),
            evaluate_node(
                &cnf.root().borrow(),
                &MaybeTrivial::<Term>::from(vec![
                    (200, false),
                    (1246, false),
                    (1816, false),
                    (1872, false)
                ])
                .unwrap()
                .as_literals()
                .to_vec()
            )
        );
        assert_eq!(
            None,
            evaluate_node(
                &cnf.root().borrow(),
                &MaybeTrivial::<Term>::from(vec![(200, true)])
                    .unwrap()
                    .as_literals()
                    .to_vec()
            )
        );
        assert_eq!(
            Some(false),
            evaluate_node(
                &cnf.root().borrow(),
                &MaybeTrivial::<Term>::from(vec![(1872, true), (5535, true)])
                    .unwrap()
                    .as_literals()
                    .to_vec()
            )
        );
    }

    #[test]
    fn test_cnf_from_is_trivial_true() {
        match MaybeTrivial::<CnfFormula>::from(vec![
            vec![Literal::new(0.into(), false), Literal::new(0.into(), true)],
            vec![Literal::new(1.into(), false), Literal::new(1.into(), true)],
        ]) {
            MaybeTrivial::True => {}
            _ => panic!(), // kcov-ignore
        }
    }

    #[test]
    fn test_cnf_from_is_trivial_false() {
        match MaybeTrivial::<CnfFormula>::from(
            vec![(vec![] as Vec<Literal>).into()] as Vec<LiteralVec>
        ) {
            MaybeTrivial::False => {}
            _ => panic!(), // kcov-ignore
        }
    }

    #[test]
    fn test_cnf_negate() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![Literal::new(0.into(), false), Literal::new(1.into(), true)],
            vec![Literal::new(0.into(), true), Literal::new(2.into(), true)],
        ])
        .unwrap();
        let dnf = MaybeTrivial::<DnfFormula>::from(vec![
            vec![Literal::new(0.into(), false), Literal::new(2.into(), false)],
            vec![Literal::new(0.into(), true), Literal::new(1.into(), false)],
        ])
        .unwrap();
        let mut neg = cnf.negate();
        neg.sub_formulas.sort_unstable();
        assert_eq!(
            dnf.root().borrow().node_kind(),
            neg.root().borrow().node_kind()
        );
    }

    #[test]
    fn test_dnf_evaluate() {
        let dnf = MaybeTrivial::<DnfFormula>::from(vec![
            vec![
                (200, true),
                (688, true),
                (2752, true),
                (4531, true),
                (4850, true),
            ],
            vec![(1246, true), (1402, true), (1405, true), (1478, true)],
            vec![(1816, true), (1817, true), (1863, true)],
            vec![(1872, true), (5535, true)],
        ])
        .unwrap();
        assert_eq!(
            Some(false),
            evaluate_node(
                &dnf.root().borrow(),
                &MaybeTrivial::<Term>::from(vec![
                    (200, false),
                    (1246, false),
                    (1816, false),
                    (1872, false)
                ])
                .unwrap()
                .as_literals()
                .to_vec()
            )
        );
        assert_eq!(
            None,
            evaluate_node(
                &dnf.root().borrow(),
                &MaybeTrivial::<Term>::from(vec![(200, true)])
                    .unwrap()
                    .as_literals()
                    .to_vec()
            )
        );
        assert_eq!(
            Some(true),
            evaluate_node(
                &dnf.root().borrow(),
                &MaybeTrivial::<Term>::from(vec![(1872, true), (5535, true)])
                    .unwrap()
                    .as_literals()
                    .to_vec()
            )
        );
    }

    #[test]
    fn test_dnf_from_is_trivial_false() {
        match MaybeTrivial::<DnfFormula>::from(vec![
            vec![Literal::new(0.into(), false), Literal::new(0.into(), true)],
            vec![Literal::new(1.into(), false), Literal::new(1.into(), true)],
        ]) {
            MaybeTrivial::False => {}
            MaybeTrivial::NotTrivial(_) => {}
            MaybeTrivial::True => {}
        }
    }

    #[test]
    fn test_dnf_from_is_trivial_true() {
        match MaybeTrivial::<DnfFormula>::from(
            vec![(vec![] as Vec<Literal>).into()] as Vec<LiteralVec>
        ) {
            MaybeTrivial::True => {}
            _ => panic!(), // kcov-ignore
        }
    }

    #[test]
    fn test_dnf_negate() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![Literal::new(0.into(), false), Literal::new(1.into(), true)],
            vec![Literal::new(0.into(), true), Literal::new(2.into(), true)],
        ])
        .unwrap();
        let dnf = MaybeTrivial::<DnfFormula>::from(vec![
            vec![Literal::new(0.into(), false), Literal::new(2.into(), false)],
            vec![Literal::new(0.into(), true), Literal::new(1.into(), false)],
        ])
        .unwrap();
        let mut neg = dnf.negate();
        neg.sub_formulas.sort_unstable();
        assert_eq!(
            cnf.root().borrow().node_kind(),
            neg.root().borrow().node_kind()
        );
    }
}
