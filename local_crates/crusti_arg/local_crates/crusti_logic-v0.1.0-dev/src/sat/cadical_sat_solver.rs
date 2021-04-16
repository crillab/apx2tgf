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

use super::sat_solver::MAYBE_TIMEOUT_MSG;
use crate::{
    core::LiteralVec, Clause, ConsistencyCheckResult, Literal, LiteralSetFormula, SatSolver,
};
use anyhow::{anyhow, Context, Result};
use cadical::{Callbacks, Solver};

struct CadicalCallbacks;

impl Callbacks for CadicalCallbacks {}

/// The CaDiCaL SAT solver.
///
/// CaDiCaL is an efficient SAT solver written in C++.
/// It won first place in the SAT track of the SAT Race 2019 and second overall place.
pub struct CadicalSatSolver {
    solver: Solver<CadicalCallbacks>,
}

impl CadicalSatSolver {
    /// Builds a new instance of the CaDiCaL SAT solver.
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
        }
    }
}

impl SatSolver for CadicalSatSolver {
    fn add_clause(&mut self, clause: Clause) {
        self.solver
            .add_clause(clause.as_literals().iter().map(internal_to_cadical))
    }

    fn n_vars(&self) -> usize {
        self.solver.max_variable() as usize
    }

    fn check_consistency_with(
        &mut self,
        assumptions: &[Literal],
    ) -> Result<ConsistencyCheckResult> {
        let cadical_assumptions = assumptions.iter().map(internal_to_cadical);
        match self.solver.solve_with(cadical_assumptions) {
            Some(true) => Ok(ConsistencyCheckResult::Sat(LiteralVec::new(build_model(
                &self.solver,
            )))),
            Some(false) => Ok(ConsistencyCheckResult::Unsat),
            // kcov-ignore-start
            None => Err(anyhow!(MAYBE_TIMEOUT_MSG))
                .context("while checking consistency with the CaDiCaL SAT solver"),
            // kcov-ignore-end
        }
    }
}

#[inline(always)]
fn internal_to_cadical(lit: &Literal) -> i32 {
    if lit.polarity() {
        usize::from(lit.var_id()) as i32 + 1
    } else {
        -(usize::from(lit.var_id()) as i32) - 1
    }
}

#[inline(always)]
fn cadical_to_internal(lit: i32) -> Literal {
    if lit < 0 {
        Literal::new((-lit as usize - 1).into(), false)
    } else {
        Literal::new((lit as usize - 1).into(), true)
    }
}

fn build_model<T>(solver: &Solver<T>) -> Vec<Literal>
where
    T: Callbacks,
{
    (1..=solver.max_variable())
        .map(|i| match solver.value(i) {
            Some(true) => cadical_to_internal(i),
            Some(false) | None => cadical_to_internal(-i),
        })
        .collect::<Vec<Literal>>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::CnfFormula;
    use crate::utils::MaybeTrivial;

    #[test]
    fn test_cadical_sat() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![(0, false), (1, true)],
            vec![(0, true), (2, true)],
        ])
        .unwrap();
        let mut solver = CadicalSatSolver::new();
        cnf.as_clauses()
            .into_iter()
            .for_each(|c| solver.add_clause(c.clone()));
        match solver.check_consistency().unwrap() {
            ConsistencyCheckResult::Sat(model) => {
                model
                    .as_slice()
                    .iter()
                    .find(|l| l == &&Literal::new(1.into(), true))
                    .or(model
                        .as_slice()
                        .iter()
                        .find(|l| l == &&Literal::new(2.into(), true)))
                    .unwrap();
                model
                    .as_slice()
                    .iter()
                    .find(|l| usize::from(l.var_id()) == 0)
                    .unwrap();
            }
            _ => panic!(), // kcov-ignore
        }
    }

    #[test]
    fn test_sat_unit_prop() {
        let cnf =
            MaybeTrivial::<CnfFormula>::from(vec![vec![(0, false)], vec![(0, true), (1, false)]])
                .unwrap();
        let mut solver = CadicalSatSolver::new();
        cnf.as_clauses()
            .into_iter()
            .for_each(|c| solver.add_clause(c.clone()));
        match solver.check_consistency().unwrap() {
            ConsistencyCheckResult::Sat(model) => {
                assert_eq!(
                    LiteralVec::new(vec![(0, false).into(), (1, false).into()].into()),
                    model
                )
            }
            _ => panic!(), // kcov-ignore
        }
    }

    #[test]
    fn test_cadical_unsat() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![(0, false), (1, true)],
            vec![(0, true), (1, false)],
            vec![(0, false), (1, false)],
            vec![(0, true), (1, true)],
        ])
        .unwrap();
        let mut solver = CadicalSatSolver::new();
        cnf.as_clauses()
            .into_iter()
            .for_each(|c| solver.add_clause(c.clone()));
        // kcov-ignore-start
        assert!(matches!(
            solver.check_consistency().unwrap(),
            ConsistencyCheckResult::Unsat
        ))
        // kcov-ignore-end
    }

    #[test]
    fn test_multiple_calls() {
        let mut solver = CadicalSatSolver::new();
        solver.add_clause(Clause::new(vec![(0, false), (1, false)].into()).unwrap());
        solver.add_clause(Clause::new(vec![(0, true), (1, true)].into()).unwrap());
        // kcov-ignore-start
        assert!(matches!(
            solver.check_consistency_with(&[(0, true).into()]).unwrap(),
            ConsistencyCheckResult::Sat(_)
        ));
        assert!(matches!(
            solver
                .check_consistency_with(&[(0, true).into(), (1, true).into()])
                .unwrap(),
            ConsistencyCheckResult::Unsat
        ));
        // kcov-ignore-end
    }
}
