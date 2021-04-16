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
    core::LiteralVec, languages::Clause, ConsistencyCheckResult, Literal, LiteralSetFormula,
    SatSolver, VarId,
};
use anyhow::{Context, Result};

pub struct VarMapperSolver {
    solver: Box<dyn SatSolver>,
    literal_mapper: LiteralMapper,
}

impl VarMapperSolver {
    pub fn new(solver: Box<dyn SatSolver>, max_init_var_id: VarId, real_n_vars: usize) -> Self {
        VarMapperSolver {
            solver,
            literal_mapper: LiteralMapper::with_capacity(max_init_var_id, real_n_vars),
        } // kcov-ignore
    }
}

impl SatSolver for VarMapperSolver {
    fn add_clause(&mut self, clause: Clause) {
        self.solver.add_clause(
            Clause::new(
                self.literal_mapper
                    .map_literal_vec(clause.as_literals())
                    .into(),
            )
            .unwrap(),
        )
    }

    fn n_vars(&self) -> usize {
        self.solver.n_vars()
    }

    fn check_consistency_with(
        &mut self,
        assumptions: &[Literal],
    ) -> Result<ConsistencyCheckResult> {
        match self
            .solver
            .check_consistency_with(self.literal_mapper.map_literal_vec(assumptions))
            .context("in the VarMapperSolver")?
        {
            ConsistencyCheckResult::Sat(m) => Ok(ConsistencyCheckResult::Sat(
                self.literal_mapper.unmap_literal_vec(m),
            )),
            ConsistencyCheckResult::Unsat => Ok(ConsistencyCheckResult::Unsat),
        }
    }
}

pub struct LiteralMapper {
    init_to_mapped: Vec<Option<VarId>>,
    mapped_to_init: Vec<VarId>,
    current_mapping: Vec<Literal>,
}

impl LiteralMapper {
    pub fn with_capacity(max_init_var_id: VarId, real_n_vars: usize) -> Self {
        LiteralMapper {
            init_to_mapped: vec![None; 1 + usize::from(max_init_var_id)],
            mapped_to_init: Vec::with_capacity(real_n_vars),
            current_mapping: Vec::with_capacity(real_n_vars),
        } // kcov-ignore
    }

    pub fn map_literal(&mut self, l: Literal) -> Literal {
        let init_var_id = l.var_id();
        let id = if let Some(v) = self.init_to_mapped[usize::from(init_var_id)] {
            v
        } else {
            let v = VarId::from(self.mapped_to_init.len());
            self.init_to_mapped[usize::from(init_var_id)] = Some(v);
            self.mapped_to_init.push(init_var_id);
            v
        };
        Literal::new(id, l.polarity())
    }

    pub fn map_literal_vec(&mut self, v: &[Literal]) -> &[Literal] {
        self.current_mapping.clear();
        for l in v {
            let mapped = self.map_literal(*l);
            self.current_mapping.push(mapped);
        }
        &self.current_mapping
    }

    pub fn unmap_literal(&self, l: Literal) -> Literal {
        Literal::new(self.mapped_to_init[usize::from(l.var_id())], l.polarity())
    }

    pub fn unmap_literal_vec(&self, v: LiteralVec) -> LiteralVec {
        LiteralVec::new(
            v.to_vec()
                .into_iter()
                .map(|l| self.unmap_literal(l))
                .collect::<Vec<Literal>>(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{default_sat_solver, MaybeTrivial};

    #[test]
    fn test_new_vars() {
        let mut m = LiteralMapper::with_capacity(1001.into(), 2);
        let m1 = m.map_literal(Literal::new(1001.into(), false));
        assert_eq!(0, usize::from(m1.var_id()));
        assert!(!m1.polarity());
        let u1 = m.unmap_literal(m1);
        assert_eq!(1001, usize::from(u1.var_id()));
        assert!(!u1.polarity());
        let m2 = m.map_literal(Literal::new(1000.into(), true));
        assert_eq!(1, usize::from(m2.var_id()));
        assert!(m2.polarity());
        let u2 = m.unmap_literal(m2);
        assert_eq!(1000, usize::from(u2.var_id()));
        assert!(u2.polarity());
    }

    #[test]
    fn test_sat() {
        let decorated = default_sat_solver();
        let mut decorator = VarMapperSolver::new(decorated, 12.into(), 2);
        decorator.add_clause(
            MaybeTrivial::<Clause>::from(vec![
                Literal::new(11.into(), false),
                Literal::new(12.into(), false),
            ])
            .unwrap(),
        );
        decorator.add_clause(
            MaybeTrivial::<Clause>::from(vec![
                Literal::new(11.into(), true),
                Literal::new(12.into(), false),
            ])
            .unwrap(),
        );
        assert_eq!(2, decorator.n_vars());
        if let ConsistencyCheckResult::Sat(m) = decorator.check_consistency().unwrap() {
            assert!(m.as_slice().contains(&Literal::new(12.into(), false)));
        } else {
            panic!(); // kcov-ignore
        }
    }

    #[test]
    fn test_unsat() {
        let decorated = default_sat_solver();
        let mut decorator = VarMapperSolver::new(decorated, 12.into(), 2);
        decorator.add_clause(
            MaybeTrivial::<Clause>::from(vec![
                Literal::new(11.into(), false),
                Literal::new(12.into(), false),
            ])
            .unwrap(),
        );
        decorator.add_clause(
            MaybeTrivial::<Clause>::from(vec![
                Literal::new(11.into(), true),
                Literal::new(12.into(), false),
            ])
            .unwrap(),
        );
        decorator.add_clause(
            MaybeTrivial::<Clause>::from(vec![
                Literal::new(11.into(), false),
                Literal::new(12.into(), true),
            ])
            .unwrap(),
        );
        decorator.add_clause(
            MaybeTrivial::<Clause>::from(vec![
                Literal::new(11.into(), true),
                Literal::new(12.into(), true),
            ])
            .unwrap(),
        );
        assert_eq!(2, decorator.n_vars());
        // kcov-ignore-start
        assert!(matches!(
            decorator.check_consistency().unwrap(),
            ConsistencyCheckResult::Unsat
        ));
        // kcov-ignore-end
    }
}
