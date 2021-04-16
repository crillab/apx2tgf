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
    core::{Formula, FormulaNode, Literal, VarId},
    languages::Term,
    transformations,
    transformations::{Conditioning, Negation},
    utils::MaybeTrivial,
    utils::RcMut,
};
use transformations::VarReplacement;

/// A [`Formula`] in the Negation Normal Form.
///
/// This structure handles both the syntactic tree of the formula and its number of variables.
/// By default, the number of variables is assumed to be the highest [`VarId`] involved in the formula plus `1`.
/// In order to consider more variables, one can take advantage of the [`from_data`](NnfFormula::from_data) function.
#[derive(Debug)]
pub struct NnfFormula {
    formula_node: RcMut<FormulaNode>,
    n_vars: usize,
}

impl NnfFormula {
    /// Builds a `NnfFormula` composed by a single literal.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Formula, Literal, NnfFormula, VarId};
    ///
    /// let l = NnfFormula::new_literal(Literal::new(VarId::from(0), false));
    /// assert_eq!("-0", format!("{}", l.root().borrow().default_display()));
    /// ```
    pub fn new_literal(lit: Literal) -> Self {
        NnfFormula {
            formula_node: RcMut::new(FormulaNode::new_literal(lit)),
            n_vars: 1 + usize::from(lit.var_id()),
        } // kcov-ignore
    }

    /// Builds a `NnfFormula` which is a conjunction of other `NnfFormula`s.
    ///
    /// If this operation leads to a trivial case, it may be returned by the right [`MaybeTrivial`] constant.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Formula, Literal, NnfFormula, VarId};
    ///
    /// let mut l0 = NnfFormula::new_literal(Literal::new(VarId::from(0), false));
    /// let mut l1 = NnfFormula::new_literal(Literal::new(VarId::from(1), true));
    /// let and = NnfFormula::new_and(&mut [l0, l1]).unwrap();
    /// assert_eq!("and(-0, 1)", format!("{}", and.root().borrow().default_display()));
    /// ```
    pub fn new_and(children: &mut [NnfFormula]) -> MaybeTrivial<Self> {
        Self::new_operator(children, FormulaNode::new_and)
    }

    /// Builds a `NnfFormula` which is a disjunction of other `NnfFormula`s.
    ///
    /// If this operation leads to a trivial case, it may be returned by the right [`MaybeTrivial`] constant.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Formula, Literal, NnfFormula, VarId};
    ///
    /// let mut l0 = NnfFormula::new_literal(Literal::new(VarId::from(0), false));
    /// let mut l1 = NnfFormula::new_literal(Literal::new(VarId::from(1), true));
    /// let or = NnfFormula::new_or(&mut [l0, l1]).unwrap();
    /// assert_eq!("or(-0, 1)", format!("{}", or.root().borrow().default_display()));
    /// ```
    pub fn new_or(children: &mut [NnfFormula]) -> MaybeTrivial<Self> {
        Self::new_operator(children, FormulaNode::new_or)
    }

    fn new_operator<F>(children: &mut [NnfFormula], node_combiner: F) -> MaybeTrivial<Self>
    where
        F: FnOnce(Vec<RcMut<FormulaNode>>) -> MaybeTrivial<FormulaNode>,
    {
        let mut children_nodes = Vec::with_capacity(children.len());
        let mut n_vars = 0;
        for child in children {
            children_nodes.push(RcMut::clone(&child.formula_node));
            if child.n_vars() > n_vars {
                n_vars = child.n_vars()
            }
        }
        node_combiner(children_nodes).map(|f| NnfFormula {
            formula_node: RcMut::new(f),
            n_vars,
        })
    }

    /// Builds a new `NnfFormula` given its syntactic tree and the number of variables to consider.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{Formula, NnfFormula};
    ///
    /// // adds a new free variable to the formula
    /// fn add_new_var(nnf: NnfFormula) -> NnfFormula {
    ///     NnfFormula::from_data(nnf.root(), 1 + nnf.n_vars())
    /// }
    /// # add_new_var(NnfFormula::new_literal((0, false).into()));
    /// ```
    pub fn from_data(formula_node: RcMut<FormulaNode>, n_vars: usize) -> NnfFormula {
        NnfFormula {
            formula_node,
            n_vars,
        }
    }
}

impl Formula for NnfFormula {
    fn root(&self) -> RcMut<FormulaNode> {
        RcMut::clone(&self.formula_node)
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }
}

impl Clone for NnfFormula {
    fn clone(&self) -> Self {
        NnfFormula {
            formula_node: RcMut::new(self.formula_node.borrow().clone()),
            n_vars: self.n_vars,
        }
    }
}

impl Negation<NnfFormula> for NnfFormula {
    fn negate(self) -> NnfFormula {
        transformations::simple_negate(self)
    }
}

impl Conditioning<NnfFormula> for NnfFormula {
    fn conditioning(self, l: Literal) -> MaybeTrivial<NnfFormula> {
        self.conditioning_by_term(&Term::new(vec![l].into()).unwrap())
    }

    fn conditioning_by_term(self, t: &Term) -> MaybeTrivial<NnfFormula> {
        transformations::simple_conditioning_by_term(self, t)
    }
}

impl VarReplacement<NnfFormula> for NnfFormula {
    fn replace_var(self, before: VarId, after: VarId) -> MaybeTrivial<NnfFormula> {
        transformations::simple_var_replacement(self, before, after)
    }

    fn replace_lit(self, before: Literal, after: Literal) -> MaybeTrivial<NnfFormula> {
        transformations::simple_lit_replacement(self, before, after)
    }
}

macro_rules! add_from_for_language {
    ($t:ty) => {
        add_from_for_language_ref!($t);
        add_from_for_language_ref!(&$t);
        add_from_for_language_ref!(&mut $t);
    };
}

macro_rules! add_from_for_language_ref {
    ($t:ty) => {
        impl From<$t> for NnfFormula {
            fn from(f: $t) -> Self {
                NnfFormula {
                    formula_node: f.root(),
                    n_vars: f.n_vars(),
                } // kcov-ignore
            }
        }
    };
}

add_from_for_language!(super::Clause);
add_from_for_language!(super::CnfFormula);
add_from_for_language!(super::Term);
add_from_for_language!(super::DnfFormula);
