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
    Clause, CnfFormula, Formula, FormulaNode, FormulaNodeKind, Literal, MaybeTrivial, RcMut, VarId,
};

/// A structure used to efficiently translate [`Formula`]s into [`CnfFormula`]s by adding auxiliary variables.
pub struct TseitinEncoder {
    cnf_formula: MaybeTrivial<CnfFormula>,
}

impl TseitinEncoder {
    /// Creates a Tseitin encoder by encoding a formula.
    pub fn encode(init_formula: &dyn Formula) -> Self {
        let cnf_formula = encode(init_formula, init_formula.n_vars());
        TseitinEncoder { cnf_formula }
    }

    /// Returns a reference to the underlying [`CnfFormula`].
    pub fn cnf_formula(&self) -> &MaybeTrivial<CnfFormula> {
        &self.cnf_formula
    }

    /// Consumes the encoder, returning the underlying [`CnfFormula`].
    pub fn take_cnf_formula(self) -> MaybeTrivial<CnfFormula> {
        self.cnf_formula
    }
}

fn encode(formula: &dyn Formula, n_vars: usize) -> MaybeTrivial<CnfFormula> {
    let mut builder = TseitinCnfFormulaBuilder::new(n_vars);
    let root_lits = encode_root(&mut builder, formula.root());
    root_lits
        .into_iter()
        .for_each(|l| builder.add_clause(MaybeTrivial::<Clause>::from(vec![l])));
    builder.into_cnf()
}

fn encode_root(builder: &mut TseitinCnfFormulaBuilder, node: RcMut<FormulaNode>) -> Vec<Literal> {
    match RcMut::clone(&node).borrow().node_kind() {
        FormulaNodeKind::And(children) => children
            .iter()
            .map(|c| encode_root(builder, RcMut::clone(c)))
            .fold(Vec::new(), |mut acc, mut v| {
                acc.append(&mut v);
                acc
            }),
        FormulaNodeKind::Or(children)
            if children
                .iter()
                .all(|c| matches!(c.borrow().node_kind(), FormulaNodeKind::Lit(_))) =>
        {
            let cl = Clause::new(
                children
                    .iter()
                    .map(|c| encode_node(builder, RcMut::clone(c)))
                    .collect::<Vec<Literal>>()
                    .into(),
            );
            builder.add_clause(cl);
            vec![]
        }
        _ => vec![encode_node(builder, node)],
    }
}

fn encode_node(builder: &mut TseitinCnfFormulaBuilder, node: RcMut<FormulaNode>) -> Literal {
    fn setup_combination(
        builder: &mut TseitinCnfFormulaBuilder,
        children: Vec<RcMut<FormulaNode>>,
    ) -> (Literal, Literal, Vec<Literal>) {
        let mut children_lits = Vec::with_capacity(children.len());
        for c in children {
            children_lits.push(encode_node(builder, c));
        }
        let v = builder.new_var();
        (Literal::new(v, true), Literal::new(v, false), children_lits)
    }
    match node.borrow().node_kind() {
        FormulaNodeKind::And(children) => {
            let (pos_lit, neg_lit, children_lits) = setup_combination(builder, children);
            children_lits
                .iter()
                .for_each(|c| builder.add_clause(MaybeTrivial::<Clause>::from(vec![neg_lit, *c])));
            builder.add_clause(Clause::new(
                std::iter::once(pos_lit)
                    .chain(children_lits.iter().map(Literal::negate))
                    .collect::<Vec<Literal>>()
                    .into(),
            ));
            pos_lit
        }
        FormulaNodeKind::Or(children) => {
            let (pos_lit, neg_lit, children_lits) = setup_combination(builder, children);
            children_lits.iter().for_each(|c| {
                builder.add_clause(MaybeTrivial::<Clause>::from(vec![pos_lit, c.negate()]))
            });
            builder.add_clause(Clause::new(
                std::iter::once(neg_lit)
                    .chain(children_lits.into_iter())
                    .collect::<Vec<Literal>>()
                    .into(),
            ));
            pos_lit
        }
        FormulaNodeKind::Lit(l) => l,
    }
}

struct TseitinCnfFormulaBuilder {
    clauses: Vec<Clause>,
    n_vars: usize,
}

impl TseitinCnfFormulaBuilder {
    fn new(n_vars: usize) -> Self {
        TseitinCnfFormulaBuilder {
            clauses: vec![],
            n_vars,
        } // kcov-ignore
    }

    fn new_var(&mut self) -> VarId {
        self.n_vars += 1;
        VarId::from(self.n_vars - 1)
    }

    fn add_clause(&mut self, clause: MaybeTrivial<Clause>) {
        self.clauses.push(clause.unwrap());
    }

    fn into_cnf(mut self) -> MaybeTrivial<CnfFormula> {
        CnfFormula::new(&mut self.clauses)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::DnfFormula;

    #[test]
    fn test_dnf() {
        let dnf = MaybeTrivial::<DnfFormula>::from(vec![
            vec![(0, false), (1, true)],
            vec![(0, true), (2, true)],
        ])
        .unwrap();
        let encoder = TseitinEncoder::encode(&dnf);
        assert_eq!(
            "and(or(-0, -2, 4), or(-0, -3), or(0, -1, 3), or(0, -4), or(1, -3), or(2, -4), or(-3, 5), or(3, 4, -5), or(-4, 5), 5)",
            format!("{}", encoder.cnf_formula.unwrap().root().borrow().default_display())
        )
    }

    #[test]
    fn test_cnf() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![(0, false), (1, true)],
            vec![(0, true), (2, true)],
        ])
        .unwrap();
        let encoder = TseitinEncoder::encode(&cnf);
        assert_eq!(
            "and(or(-0, 1), or(0, 2))",
            format!(
                "{}",
                encoder
                    .cnf_formula
                    .unwrap()
                    .root()
                    .borrow()
                    .default_display()
            )
        )
    }

    #[test]
    fn test_clause() {
        let cl = Clause::new(vec![(0, false), (1, true)].into()).unwrap();
        let encoder = TseitinEncoder::encode(&cl);
        assert_eq!(
            "or(-0, 1)",
            format!(
                "{}",
                encoder
                    .cnf_formula
                    .unwrap()
                    .root()
                    .borrow()
                    .default_display()
            )
        )
    }
}
