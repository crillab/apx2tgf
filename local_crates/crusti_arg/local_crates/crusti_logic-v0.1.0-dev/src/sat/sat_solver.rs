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

use crate::{core::LiteralVec, CadicalSatSolver, Clause, Literal};
use anyhow::Result;

/// The error message included in errors thrown because of a SAT solver invocation resulting in an error.
pub const MAYBE_TIMEOUT_MSG: &str = "the SAT solver did not reply (maybe a timeout was reached ?)";

/// An enum used to handle the return of a consistency check algorithm.
#[derive(Debug, Eq, PartialEq)]
pub enum ConsistencyCheckResult {
    /// A model was found
    Sat(LiteralVec),
    /// Unsatisfiability was proved
    Unsat,
}

/// A `SatSolver` is used to look for models in `CNF` formulas.
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, Clause, ConsistencyCheckResult, SatSolver};
///
/// let mut solver = default_sat_solver();
/// solver.add_clause(Clause::new(vec![(0, false), (1, true)].into()).unwrap());
/// solver.add_clause(Clause::new(vec![(0, true), (1, false)].into()).unwrap());
/// match solver.check_consistency().unwrap() {
///     ConsistencyCheckResult::Sat(model) => println!("{:?} is a model", model),
///     ConsistencyCheckResult::Unsat => println!("no model"),
/// }
/// ```
pub trait SatSolver {
    /// Adds a [`Clause`] to the `CNF` formula considered by the solver.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{default_sat_solver, Clause, SatSolver};
    ///
    /// let mut solver = default_sat_solver();
    /// solver.add_clause(Clause::new(vec![(0, false), (1, true)].into()).unwrap());
    /// ```
    fn add_clause(&mut self, clause: Clause);

    /// Returns the number of variables taken into consideration by the solver.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{default_sat_solver, Clause, SatSolver};
    ///
    /// let mut solver = default_sat_solver();
    /// assert_eq!(0, solver.n_vars());
    /// solver.add_clause(Clause::new(vec![(0, false), (1, true)].into()).unwrap());
    /// assert_eq!(2, solver.n_vars());
    /// ```
    fn n_vars(&self) -> usize;

    /// Checks if the underlying `CNF` has a model.
    ///
    /// If a model is found, it is returned through the [`ConsistencyCheckResult`] object.
    /// A SAT solver may not manage to decide the satisfiability of the formula (e.g. if a timeout is reached);
    /// in this case, an error is returned, and its message is [`MAYBE_TIMEOUT_MSG`].
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{default_sat_solver, Clause, ConsistencyCheckResult, SatSolver};
    ///
    /// let mut solver = default_sat_solver();
    /// solver.add_clause(Clause::new(vec![(0, false), (1, true)].into()).unwrap());
    /// solver.add_clause(Clause::new(vec![(0, true), (1, false)].into()).unwrap());
    /// match solver.check_consistency().unwrap() {
    ///     ConsistencyCheckResult::Sat(model) => println!("{:?} is a model", model),
    ///     ConsistencyCheckResult::Unsat => println!("no model"),
    /// }
    /// ```
    fn check_consistency(&mut self) -> Result<ConsistencyCheckResult> {
        self.check_consistency_with(&[])
    }

    /// Checks if the underlying `CNF`, conditioned by a set of literals, has a model.
    ///
    /// The `CNF` itself is not altered by this function.
    ///
    /// If a model is found, it is returned through the [`ConsistencyCheckResult`] object.
    /// A SAT solver may not manage to decide the satisfiability of the formula (e.g. if a timeout is reached);
    /// in this case, an error is returned, and its message is [`MAYBE_TIMEOUT_MSG`].
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{default_sat_solver, Clause, ConsistencyCheckResult, SatSolver};
    ///
    /// let mut solver = default_sat_solver();
    /// solver.add_clause(Clause::new(vec![(0, false), (1, false)].into()).unwrap());
    /// solver.add_clause(Clause::new(vec![(0, true), (1, true)].into()).unwrap());
    /// assert!(matches!(
    ///     solver.check_consistency_with(&[(0, true).into()]).unwrap(),
    ///     ConsistencyCheckResult::Sat(_)
    /// ));
    /// assert!(matches!(
    ///     solver.check_consistency_with(&[(0, true).into(), (1, true).into()]).unwrap(),
    ///     ConsistencyCheckResult::Unsat
    /// ));
    /// ```
    fn check_consistency_with(&mut self, assumptions: &[Literal])
        -> Result<ConsistencyCheckResult>;
}

/// Returns the default SAT solver.
///
/// The default SAT solver is currently the [`CadicalSatSolver`].
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, Clause, ConsistencyCheckResult, SatSolver};
///
/// let mut solver = default_sat_solver();
/// solver.add_clause(Clause::new(vec![(0, false), (1, true)].into()).unwrap());
/// solver.add_clause(Clause::new(vec![(0, true), (1, false)].into()).unwrap());
/// match solver.check_consistency().unwrap() {
///     ConsistencyCheckResult::Sat(model) => println!("{:?} is a model", model),
///     ConsistencyCheckResult::Unsat => println!("no model"),
/// }
/// ```
pub fn default_sat_solver() -> Box<dyn SatSolver> {
    Box::new(CadicalSatSolver::new())
}
