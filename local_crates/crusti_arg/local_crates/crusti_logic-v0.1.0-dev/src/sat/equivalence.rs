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

//! This module provides functions used to compute equivalency relations between variables, using a SAT solver.

use crate::{core::LiteralVec, ConsistencyCheckResult, Literal, SatSolver, VarId};
use anyhow::{anyhow, Context, Result};
use std::cell::RefCell;

/// The error message included in errors thrown because of an unexpected inconsistent formula.
pub const UNEXPECTED_UNSAT_FORMULA_MSG: &str = "cannot call this method on an inconsistent formula";

/// Compute the equivalency class of a variable.
///
/// The formula encoded in the SAT solver must be satisfiable.
///
/// The equivalency class is the set of variables such that, for every model of the formula,
/// their truth value is the same. In case there is no such variable, a vector containing the input variable as its single element is returned.
///
/// This function requires a minimal and a maximal variable identifier to consider.
/// The variable for which the equivalency class computation is required must have an identifier within these bounds.
/// The computed equivalency class will be restricted to the set of variables bounded by these minimal and maximal values.
///
/// In case the SAT solver returns an error (which can occurs e.g. when a timeout is reached),
/// this error is returned. An error is also returned if the formula is inconsistent.
///
/// The returned class is sorted in increasing order of variable identifiers.
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, equivalence, Clause, Literal, SatSolver, VarId};
///
/// let mut s = default_sat_solver();
/// let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
/// let pos_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, true))
///     .collect::<Vec<Literal>>();
/// let neg_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, false))
///     .collect::<Vec<Literal>>();
/// s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
/// assert_eq!(
///     vec![vars[0], vars[1]],
///     equivalence::compute_class_of_variable(s.as_mut(), vars[0], vars[0], vars[4]).unwrap()
/// );
/// ```
pub fn compute_class_of_variable(
    sat_solver: &mut dyn SatSolver,
    var: VarId,
    min_var_id: VarId,
    max_var_id: VarId,
) -> Result<Vec<VarId>> {
    let pos_lit = Literal::new(var, true);
    let neg_lit = Literal::new(var, false);
    let mut eq_class = vec![var];
    let n_vars = usize::from(max_var_id) - usize::from(min_var_id) + 1;
    let not_candidate_anymore = RefCell::new(vec![false; n_vars]);
    not_candidate_anymore.borrow_mut()[usize::from(pos_lit.var_id()) - usize::from(min_var_id)] =
        true;
    let mut reduce = |lit, other_lit, unexpected_polarity| {
        reduce_lit_equiv_candidates(
            sat_solver,
            lit,
            other_lit,
            unexpected_polarity,
            min_var_id,
            max_var_id,
            &mut not_candidate_anymore.borrow_mut(),
        )
    };
    let context_message = || format!("while computing the class of variable {}", var);
    if !reduce(neg_lit, None, true).with_context(context_message)?
        && !reduce(pos_lit, None, false).with_context(context_message)?
    {
        return Err(anyhow!(UNEXPECTED_UNSAT_FORMULA_MSG));
    }
    for i in 0..n_vars {
        if not_candidate_anymore.borrow()[i] {
            continue;
        }
        let other_var = VarId::from(usize::from(min_var_id) + i);
        if !reduce(neg_lit, Some(Literal::new(other_var, true)), true)
            .with_context(context_message)?
            && !reduce(pos_lit, Some(Literal::new(other_var, false)), false)
                .with_context(context_message)?
        {
            eq_class.push(other_var);
        }
    }
    Ok(eq_class)
}

fn reduce_lit_equiv_candidates(
    sat_solver: &mut dyn SatSolver,
    lit: Literal,
    other_lit: Option<Literal>,
    unexpected_polarity: bool,
    min_var_id: VarId,
    max_var_id: VarId,
    not_candidate_anymore: &mut [bool],
) -> Result<bool> {
    let assumptions = if let Some(l) = other_lit {
        vec![lit, l]
    } else {
        vec![lit]
    };
    match sat_solver.check_consistency_with(&assumptions)? {
        ConsistencyCheckResult::Sat(m) => {
            for_each_lit_in_model(m, min_var_id, max_var_id, Some(unexpected_polarity), |l| {
                not_candidate_anymore[usize::from(l.var_id()) - usize::from(min_var_id)] = true
            });
            Ok(true)
        }
        ConsistencyCheckResult::Unsat => Ok(false),
    }
}

/// Compute the equivalency classes of a set of variables.
///
/// The formula encoded in the SAT solver must be satisfiable.
///
/// The equivalency class of a variable is the set of variables such that, for every model of the formula,
/// their truth value is the same.
///
/// This function requires a minimal and a maximal variable identifier to consider.
/// The computation will be done for each variable in this interval.
/// The computed equivalency classes will be restricted to the set of variables bounded by these minimal and maximal values.
///
/// This function returns a vector of classes, such that each variable under consideration appears in exactly one class.
/// The elements inside a class are sorted by increasing order.
/// The classes order follows the (increasing) order of their first elements.
///
/// In case the SAT solver returns an error (which can occurs e.g. when a timeout is reached),
/// this error is returned. An error is also returned if the formula is inconsistent.
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, equivalence, Clause, Literal, SatSolver, VarId};
///
/// let mut s = default_sat_solver();
/// let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
/// let pos_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, true))
///     .collect::<Vec<Literal>>();
/// let neg_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, false))
///     .collect::<Vec<Literal>>();
/// s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
/// assert_eq!(
///     vec![
///         vec![vars[0], vars[1]],
///         vec![vars[2]],
///         vec![vars[3], vars[4]]
///     ],
///     equivalence::compute_all_variable_classes(s.as_mut(), vars[0], vars[4]).unwrap()
/// );
/// ```
pub fn compute_all_variable_classes(
    sat_solver: &mut dyn SatSolver,
    min_var_id: VarId,
    max_var_id: VarId,
) -> Result<Vec<Vec<VarId>>> {
    let n_vars = usize::from(max_var_id) - usize::from(min_var_id) + 1;
    let mut classes = Vec::with_capacity(n_vars);
    let mut in_classes = vec![false; n_vars];
    for i in 0..n_vars {
        if in_classes[i] {
            continue;
        }
        let var = VarId::from(usize::from(min_var_id) + i);
        let var_class = compute_class_of_variable(sat_solver, var, var, max_var_id)
            .context("while computing the variable equivalence classes")?;
        var_class
            .iter()
            .for_each(|v| in_classes[usize::from(*v) - usize::from(min_var_id)] = true);
        classes.push(var_class);
    }
    classes.shrink_to_fit();
    Ok(classes)
}

/// Compute the equivalency class of a literal.
///
/// The formula encoded in the SAT solver must be satisfiable.
///
/// The equivalency class is the set of literals such that, for every model of the formula,
/// their truth value is the same. In case there is no such literal, a vector containing the input literal as its single element is returned.
///
/// This function requires a minimal and a maximal variable identifier to consider.
/// The literal for which the equivalency class computation is required must have a variable identifier within these bounds.
/// The computed equivalency class will be restricted to the set of literals which variable identifiers are bounded by these minimal and maximal values.
///
/// In case the SAT solver returns an error (which can occurs e.g. when a timeout is reached),
/// this error is returned. An error is also returned if the formula is inconsistent.
///
/// The returned class is sorted in increasing order of literals. See [`Literal`] for more information on the order.
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, equivalence, Clause, Literal, SatSolver, VarId};
///
/// let mut s = default_sat_solver();
/// let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
/// let pos_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, true))
///     .collect::<Vec<Literal>>();
/// let neg_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, false))
///     .collect::<Vec<Literal>>();
/// s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
/// s.add_clause(Clause::new(vec![neg_lits[1], neg_lits[0]].into()).unwrap());
/// assert_eq!(
///     vec![pos_lits[0], neg_lits[1]],
///     equivalence::compute_class_of_literal(s.as_mut(), pos_lits[0], vars[0], vars[1]).unwrap()
/// );
/// ```
pub fn compute_class_of_literal(
    sat_solver: &mut dyn SatSolver,
    lit: Literal,
    min_var_id: VarId,
    max_var_id: VarId,
) -> Result<Vec<Literal>> {
    let context_message = || format!("while computing the class of literal {:?}", lit);
    let var_class = compute_class_of_variable(sat_solver, lit.var_id(), min_var_id, max_var_id)
        .with_context(context_message)?;
    let n_vars = usize::from(max_var_id) - usize::from(min_var_id) + 1;
    let no_more_xor_candidate = RefCell::new(vec![false; n_vars]);
    var_class.iter().for_each(|v| {
        no_more_xor_candidate.borrow_mut()[usize::from(*v) - usize::from(min_var_id)] = true
    });
    let mut xor_var = None;
    let mut reduce = |lit, other_lit| {
        reduce_lit_equiv_candidates(
            sat_solver,
            lit,
            Some(other_lit),
            lit.polarity(),
            min_var_id,
            max_var_id,
            &mut no_more_xor_candidate.borrow_mut(),
        )
    };
    for i in 0..n_vars {
        if no_more_xor_candidate.borrow()[i] {
            continue;
        }
        let other_var = VarId::from(usize::from(min_var_id) + i);
        if !reduce(lit, Literal::new(other_var, lit.polarity())).with_context(context_message)?
            && !reduce(lit.negate(), Literal::new(other_var, !lit.polarity()))
                .with_context(context_message)?
        {
            xor_var = Some(other_var);
            break;
        }
    }
    let mut lit_class = var_class
        .into_iter()
        .map(|v| Literal::new(v, lit.polarity()))
        .collect::<Vec<Literal>>();
    if let Some(x) = xor_var {
        let xor_class = compute_class_of_variable(sat_solver, x, min_var_id, max_var_id)
            .with_context(context_message)?;
        lit_class.reserve(xor_class.len());
        xor_class
            .into_iter()
            .map(|v| Literal::new(v, !lit.polarity()))
            .for_each(|l| lit_class.push(l));
    }
    lit_class.sort_unstable();
    Ok(lit_class)
}

/// Compute the equivalency classes of a set of literals given by a set of variables.
///
/// The formula encoded in the SAT solver must be satisfiable.
///
/// The set of literals under consideration is the one composed by the two literals of each variable.
///
/// The equivalency class is the set of literals such that, for every model of the formula,
/// their truth value is the same.
///
/// This function requires a minimal and a maximal variable identifier to consider.
/// The computed equivalency class will be restricted to the set of literals which variable identifiers are bounded by these minimal and maximal values.
///
/// This function returns a vector of couples of classes, such that each literal under consideration appears in exactly one class.
/// The two classes in a couple are of the ones that consider the same set of variables, but with opposite literals.
/// The elements inside a class are sorted by increasing order.
/// The couples and the classes order follows the (increasing) order of their first elements.
///
/// In case the SAT solver returns an error (which can occurs e.g. when a timeout is reached),
/// this error is returned. An error is also returned if the formula is inconsistent.
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, equivalence, Clause, Literal, SatSolver, VarId};
///
/// let mut s = default_sat_solver();
/// let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
/// let pos_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, true))
///     .collect::<Vec<Literal>>();
/// let neg_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, false))
///     .collect::<Vec<Literal>>();
/// s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
/// assert_eq!(
///     vec![
///         (vec![neg_lits[0], neg_lits[1]], vec![pos_lits[0], pos_lits[1]]),
///         (vec![neg_lits[2]], vec![pos_lits[2]]),
///         (vec![neg_lits[3], neg_lits[4]], vec![pos_lits[3], pos_lits[4]]),
///     ],
///     equivalence::compute_all_literal_classes(s.as_mut(), vars[0], vars[4]).unwrap()
/// );
/// ```
pub fn compute_all_literal_classes(
    sat_solver: &mut dyn SatSolver,
    min_var_id: VarId,
    max_var_id: VarId,
) -> Result<Vec<(Vec<Literal>, Vec<Literal>)>> {
    let n_vars = usize::from(max_var_id) - usize::from(min_var_id) + 1;
    let mut classes = Vec::with_capacity(n_vars << 1);
    let mut var_in_classes = vec![false; n_vars];
    for i in 0..n_vars {
        let var = VarId::from(usize::from(min_var_id) + i);
        if !var_in_classes[i] {
            let pos_lit = Literal::new(var, true);
            let lit_class = compute_class_of_literal(sat_solver, pos_lit, var, max_var_id)
                .context("while computing the literal equivalence classes")?;
            lit_class.iter().for_each(|l| {
                let vec_index = usize::from(l.var_id()) - usize::from(min_var_id);
                var_in_classes[vec_index] = true;
            });
            let neg_lit_class = lit_class
                .iter()
                .map(Literal::negate)
                .collect::<Vec<Literal>>();
            classes.push((neg_lit_class, lit_class));
        }
    }
    classes.shrink_to_fit();
    classes.sort_unstable();
    Ok(classes)
}

/// Compute the backbone of a formula.
///
/// The formula encoded in the SAT solver must be satisfiable.
///
/// The backbone is the set of literals that appear in all the models of a consistent formula.
///
/// This function requires a minimal and a maximal variable identifier to consider.
/// The backbone search will be restricted to the variables within these bounds.
///
/// In case the SAT solver returns an error (which can occurs e.g. when a timeout is reached),
/// this error is returned. An error is also returned if the formula is inconsistent.
///
/// The returned set of literals is sorted according to the order defined for the [`Literal`]s.
///
/// # Examples
///
/// ```
/// use crusti_logic::{default_sat_solver, equivalence, Clause, Literal, SatSolver, VarId};
///
/// let mut s = default_sat_solver();
/// let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
/// let pos_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, true))
///     .collect::<Vec<Literal>>();
/// let neg_lits = vars
///     .iter()
///     .map(|v| Literal::new(*v, false))
///     .collect::<Vec<Literal>>();
/// s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
/// s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
/// assert_eq!(
///     vec![vars[0], vars[1]],
///     equivalence::compute_class_of_variable(s.as_mut(), vars[0], vars[0], vars[4]).unwrap()
/// );
/// ```
pub fn compute_backbone(
    sat_solver: &mut dyn SatSolver,
    min_var_id: VarId,
    max_var_id: VarId,
) -> Result<Vec<Literal>> {
    let n_vars = usize::from(max_var_id) - usize::from(min_var_id) + 1;
    let mut candidates = vec![None; n_vars];
    let context_message = "while computing the backbone of the formula";
    match sat_solver.check_consistency().context(context_message)? {
        ConsistencyCheckResult::Sat(m) => {
            for_each_lit_in_model(m, min_var_id, max_var_id, None, |l| {
                candidates[usize::from(l.var_id()) - usize::from(min_var_id)] = Some(l.polarity())
            })
        }
        ConsistencyCheckResult::Unsat => return Err(anyhow!(UNEXPECTED_UNSAT_FORMULA_MSG)),
    } // kcov-ignore
    let mut backbone = Vec::with_capacity(n_vars);
    for i in 0..candidates.len() {
        let polarity = match candidates[i] {
            Some(p) => p,
            None => continue,
        };
        let var_id = VarId::from(usize::from(min_var_id) + i);
        let lit = Literal::new(var_id, polarity);
        match sat_solver
            .check_consistency_with(&[lit.negate()])
            .context(context_message)?
        {
            ConsistencyCheckResult::Sat(m) => {
                for_each_lit_in_model(m, min_var_id, max_var_id, None, |l| {
                    let vec_index = usize::from(l.var_id()) - usize::from(min_var_id);
                    if let Some(p) = candidates[vec_index] {
                        if p != l.polarity() {
                            candidates[vec_index] = None;
                        }
                    }
                })
            }
            ConsistencyCheckResult::Unsat => backbone.push(lit),
        }
    } // kcov-ignore
    backbone.shrink_to_fit();
    Ok(backbone)
}

fn for_each_lit_in_model<F>(
    model: LiteralVec,
    min_var_id: VarId,
    max_var_id: VarId,
    polarity: Option<bool>,
    f: F,
) where
    F: FnMut(&Literal),
{
    model
        .as_slice()
        .iter()
        .filter(|l| {
            l.var_id() >= min_var_id
                && l.var_id() <= max_var_id
                && if let Some(p) = polarity {
                    l.polarity() == p
                } else {
                    true
                }
        })
        .for_each(f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{default_sat_solver, Clause};

    #[test]
    fn test_single_var_class() {
        let mut s = default_sat_solver();
        let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
        assert_eq!(
            vec![vars[0], vars[1]],
            compute_class_of_variable(s.as_mut(), vars[0], vars[0], vars[4]).unwrap()
        );
        assert_eq!(
            vec![vars[1]],
            compute_class_of_variable(s.as_mut(), vars[1], vars[1], vars[4]).unwrap()
        );
        assert_eq!(
            vec![vars[3], vars[4]],
            compute_class_of_variable(s.as_mut(), vars[3], vars[1], vars[4]).unwrap()
        );
        assert_eq!(
            vec![vars[3]],
            compute_class_of_variable(s.as_mut(), vars[3], vars[1], vars[3]).unwrap()
        );
    }

    #[test]
    fn test_all_var_classes() {
        let mut s = default_sat_solver();
        let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
        assert_eq!(
            vec![
                vec![vars[0], vars[1]],
                vec![vars[2]],
                vec![vars[3], vars[4]]
            ],
            compute_all_variable_classes(s.as_mut(), vars[0], vars[4]).unwrap()
        );
        assert_eq!(
            vec![vec![vars[0], vars[1]], vec![vars[2]], vec![vars[3]]],
            compute_all_variable_classes(s.as_mut(), vars[0], vars[3]).unwrap()
        );
        assert_eq!(
            vec![vec![vars[1]], vec![vars[2]], vec![vars[3], vars[4]]],
            compute_all_variable_classes(s.as_mut(), vars[1], vars[4]).unwrap()
        );
    }

    fn sort_expected_class_of_literals(mut v: Vec<Literal>) -> Vec<Literal> {
        v.sort_unstable();
        v
    }

    #[test]
    fn test_single_lit_class() {
        let mut s = default_sat_solver();
        let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
        assert_eq!(
            sort_expected_class_of_literals(vec![pos_lits[0], pos_lits[1]]),
            compute_class_of_literal(s.as_mut(), pos_lits[0], vars[0], vars[4]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![pos_lits[1]]),
            compute_class_of_literal(s.as_mut(), pos_lits[1], vars[1], vars[4]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![pos_lits[3], pos_lits[4]]),
            compute_class_of_literal(s.as_mut(), pos_lits[3], vars[1], vars[4]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![pos_lits[3]]),
            compute_class_of_literal(s.as_mut(), pos_lits[3], vars[1], vars[3]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![neg_lits[0], neg_lits[1]]),
            compute_class_of_literal(s.as_mut(), neg_lits[0], vars[0], vars[4]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![neg_lits[1]]),
            compute_class_of_literal(s.as_mut(), neg_lits[1], vars[1], vars[4]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![neg_lits[3], neg_lits[4]]),
            compute_class_of_literal(s.as_mut(), neg_lits[3], vars[1], vars[4]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![neg_lits[3]]),
            compute_class_of_literal(s.as_mut(), neg_lits[3], vars[1], vars[3]).unwrap()
        );
    }

    #[test]
    fn test_single_lit_xor() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[1], neg_lits[0]].into()).unwrap());
        assert_eq!(
            sort_expected_class_of_literals(vec![pos_lits[0], neg_lits[1]]),
            compute_class_of_literal(s.as_mut(), pos_lits[0], vars[0], vars[1]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![pos_lits[0], neg_lits[1]]),
            compute_class_of_literal(s.as_mut(), neg_lits[1], vars[0], vars[1]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![neg_lits[0], pos_lits[1]]),
            compute_class_of_literal(s.as_mut(), neg_lits[0], vars[0], vars[1]).unwrap()
        );
        assert_eq!(
            sort_expected_class_of_literals(vec![neg_lits[0], pos_lits[1]]),
            compute_class_of_literal(s.as_mut(), pos_lits[1], vars[0], vars[1]).unwrap()
        );
    }

    fn sort_expected_classes_of_literals(mut v: Vec<Vec<Literal>>) -> Vec<Vec<Literal>> {
        v.iter_mut().for_each(|c| c.sort_unstable());
        v.sort_unstable();
        v
    }

    fn flatten_literal_classes(classes: Vec<(Vec<Literal>, Vec<Literal>)>) -> Vec<Vec<Literal>> {
        sort_expected_classes_of_literals(
            classes
                .into_iter()
                .map(|(v0, v1)| std::iter::once(v0).chain(std::iter::once(v1)))
                .flatten()
                .map(|v| v.clone())
                .collect(),
        )
    }

    #[test]
    fn test_all_lit_classes() {
        let mut s = default_sat_solver();
        let vars = (0..5).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[1], neg_lits[0]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1], pos_lits[2]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[3], neg_lits[4]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[4], neg_lits[3]].into()).unwrap());
        assert_eq!(
            sort_expected_classes_of_literals(vec![
                vec![pos_lits[0], pos_lits[1]],
                vec![neg_lits[0], neg_lits[1]],
                vec![pos_lits[2]],
                vec![neg_lits[2]],
                vec![pos_lits[3], pos_lits[4]],
                vec![neg_lits[3], neg_lits[4]],
            ]),
            flatten_literal_classes(
                compute_all_literal_classes(s.as_mut(), vars[0], vars[4]).unwrap()
            )
        );
        assert_eq!(
            sort_expected_classes_of_literals(vec![
                vec![pos_lits[0], pos_lits[1]],
                vec![neg_lits[0], neg_lits[1]],
                vec![pos_lits[2]],
                vec![neg_lits[2]],
                vec![pos_lits[3]],
                vec![neg_lits[3]]
            ]),
            flatten_literal_classes(
                compute_all_literal_classes(s.as_mut(), vars[0], vars[3]).unwrap()
            )
        );
        assert_eq!(
            sort_expected_classes_of_literals(vec![
                vec![pos_lits[1]],
                vec![neg_lits[1]],
                vec![pos_lits[2]],
                vec![neg_lits[2]],
                vec![pos_lits[3], pos_lits[4]],
                vec![neg_lits[3], neg_lits[4]],
            ]),
            flatten_literal_classes(
                compute_all_literal_classes(s.as_mut(), vars[1], vars[4]).unwrap()
            )
        );
    }

    #[test]
    fn test_all_lit_classes_xor() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[1], neg_lits[0]].into()).unwrap());
        assert_eq!(
            sort_expected_classes_of_literals(vec![
                vec![pos_lits[0], neg_lits[1]],
                vec![neg_lits[0], pos_lits[1]],
            ]),
            flatten_literal_classes(
                compute_all_literal_classes(s.as_mut(), vars[0], vars[1]).unwrap()
            )
        );
    }

    #[test]
    fn test_backbone() {
        let mut s = default_sat_solver();
        let vars = (0..4).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[2]].into()).unwrap());
        assert_eq!(
            vec![pos_lits[1], neg_lits[2]],
            compute_backbone(s.as_mut(), vars[0], vars[3]).unwrap()
        );
    }

    #[test]
    fn test_var_class_unsat() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], neg_lits[1]].into()).unwrap());
        assert!(compute_class_of_variable(s.as_mut(), vars[0], vars[0], vars[1]).is_err());
    }

    #[test]
    fn test_all_var_classes_unsat() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], neg_lits[1]].into()).unwrap());
        assert!(compute_all_variable_classes(s.as_mut(), vars[0], vars[1]).is_err());
    }

    #[test]
    fn test_lit_class_unsat() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], neg_lits[1]].into()).unwrap());
        assert!(compute_class_of_literal(s.as_mut(), pos_lits[0], vars[0], vars[1]).is_err());
    }

    #[test]
    fn test_all_lit_classes_unsat() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], neg_lits[1]].into()).unwrap());
        assert!(compute_all_literal_classes(s.as_mut(), vars[0], vars[1]).is_err());
    }

    #[test]
    fn test_backbone_unsat() {
        let mut s = default_sat_solver();
        let vars = (0..2).map(VarId::from).collect::<Vec<VarId>>();
        let pos_lits = vars
            .iter()
            .map(|v| Literal::new(*v, true))
            .collect::<Vec<Literal>>();
        let neg_lits = vars
            .iter()
            .map(|v| Literal::new(*v, false))
            .collect::<Vec<Literal>>();
        s.add_clause(Clause::new(vec![pos_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![pos_lits[0], neg_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], pos_lits[1]].into()).unwrap());
        s.add_clause(Clause::new(vec![neg_lits[0], neg_lits[1]].into()).unwrap());
        assert!(compute_backbone(s.as_mut(), vars[0], vars[1]).is_err());
    }
}
