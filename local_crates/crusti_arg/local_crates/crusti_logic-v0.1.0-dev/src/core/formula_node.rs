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

use crate::{Literal, MaybeTrivial, RcMut, VarId};
use std::fmt::Display;

/// An enum for the three kinds of propositional formula nodes considered in this library.
///
/// See [`FormulaNode`] for more information.
#[derive(Clone, Debug)]
pub enum FormulaNodeKind {
    /// A conjunction node
    And(Vec<RcMut<FormulaNode>>),
    /// A disjunction node
    Or(Vec<RcMut<FormulaNode>>),
    /// A literal node
    Lit(Literal),
}

impl PartialEq for FormulaNodeKind {
    fn eq(&self, other: &Self) -> bool {
        fn vec_eq(first: &[RcMut<FormulaNode>], second: &[RcMut<FormulaNode>]) -> bool {
            if first.len() != second.len() {
                false
            } else {
                (0..first.len()).all(|i| first[i].borrow().eq(&second[i].borrow()))
            }
        }
        match self {
            FormulaNodeKind::And(children) => {
                if let FormulaNodeKind::And(other_children) = other {
                    vec_eq(children, other_children)
                } else {
                    false
                }
            }
            FormulaNodeKind::Or(children) => {
                if let FormulaNodeKind::Or(other_children) = other {
                    vec_eq(children, other_children)
                } else {
                    false
                }
            }
            FormulaNodeKind::Lit(lit) => {
                if let FormulaNodeKind::Lit(other_lit) = other {
                    lit.eq(other_lit)
                } else {
                    false
                }
            }
        }
    }
}

impl Eq for FormulaNodeKind {}

impl PartialOrd for FormulaNodeKind {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FormulaNodeKind {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn vec_cmp(
            first: &[RcMut<FormulaNode>],
            second: &[RcMut<FormulaNode>],
        ) -> std::cmp::Ordering {
            let l1 = first.len();
            let l2 = second.len();
            let min_l = if l1 < l2 { l1 } else { l2 };
            for i in 0..min_l {
                let local_cmp = first[i].borrow().cmp(&second[i].borrow());
                match local_cmp {
                    std::cmp::Ordering::Less | std::cmp::Ordering::Greater => return local_cmp,
                    std::cmp::Ordering::Equal => {}
                }
            }
            l1.cmp(&l2)
        }
        match self {
            FormulaNodeKind::And(children) => match other {
                FormulaNodeKind::And(other_children) => vec_cmp(children, other_children),
                FormulaNodeKind::Or(_) | FormulaNodeKind::Lit(_) => std::cmp::Ordering::Less,
            },
            FormulaNodeKind::Or(children) => match other {
                FormulaNodeKind::And(_) => std::cmp::Ordering::Greater,
                FormulaNodeKind::Or(other_children) => vec_cmp(children, other_children),
                FormulaNodeKind::Lit(_) => std::cmp::Ordering::Less,
            },
            FormulaNodeKind::Lit(lit) => match other {
                FormulaNodeKind::And(_) | FormulaNodeKind::Or(_) => std::cmp::Ordering::Greater,
                FormulaNodeKind::Lit(other_lit) => lit.cmp(other_lit),
            },
        }
    }
}

/// A formula node.
///
/// This type is a wrapper around the [`FormulaNodeKind`] enum.
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct FormulaNode {
    node_kind: FormulaNodeKind,
    marked: bool,
}

impl FormulaNode {
    /// Builds a new literal node, given the [`Literal`] instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{FormulaNode, Literal, RcMut};
    ///
    /// let l1 = FormulaNode::new_literal(Literal::new(1.into(), false));
    /// ```
    pub fn new_literal(lit: Literal) -> Self {
        FormulaNode {
            node_kind: FormulaNodeKind::Lit(lit),
            marked: false,
        }
    }

    /// Builds a new conjunction node, given the its children.
    ///
    /// The set of children is reduced if it contains literals of the same variable.
    ///
    /// If two opposite literals are found, [`MaybeTrivial::False`] is returned;
    /// else, an instance of [`MaybeTrivial::NotTrivial`] is returned.
    /// If multiple occurrences of the same literal are found, only one is kept.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{FormulaNode, Literal, RcMut};
    ///
    /// let l1 = FormulaNode::new_literal(Literal::new(1.into(), false));
    /// let l1_rc = RcMut::new(l1);
    /// let l2 = FormulaNode::new_literal(Literal::new(2.into(), true));
    /// let l2_rc = RcMut::new(l2);
    /// let not_l2 = FormulaNode::new_literal(Literal::new(2.into(), false));
    /// let not_l2_rc = RcMut::new(not_l2);
    /// assert_eq!(
    ///     FormulaNode::new_and(vec![RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)]).unwrap(),
    ///     FormulaNode::new_and(
    ///         vec![RcMut::clone(&l1_rc), RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)
    ///     ]).unwrap()
    /// );
    /// assert!(FormulaNode::new_and(vec![RcMut::clone(&l2_rc), RcMut::clone(&not_l2_rc)]).is_false())
    /// ```
    pub fn new_and(children: Vec<RcMut<FormulaNode>>) -> MaybeTrivial<Self> {
        let mut new_children = Vec::with_capacity(children.len());
        let mut new_literals: Vec<Literal> = Vec::with_capacity(children.len());
        for child in children {
            match RcMut::clone(&child).borrow().node_kind {
                FormulaNodeKind::And(_) | FormulaNodeKind::Or(_) => new_children.push(child),
                FormulaNodeKind::Lit(lit) => {
                    let mut ignore = false;
                    for new_lit in new_literals.iter() {
                        if lit.var_id() == new_lit.var_id() {
                            if lit.polarity() != new_lit.polarity() {
                                return MaybeTrivial::False;
                            } else {
                                ignore = true;
                                break;
                            }
                        }
                    }
                    if !ignore {
                        new_literals.push(lit);
                        new_children.push(RcMut::clone(&child))
                    }
                }
            }
        }
        let node_kind = match new_children.len() {
            0 => return MaybeTrivial::True,
            1 => new_children[0].borrow().node_kind.clone(),
            _ => FormulaNodeKind::And(new_children),
        };
        MaybeTrivial::NotTrivial(FormulaNode {
            node_kind,
            marked: false,
        })
    }

    /// Builds a new disjunction node, given the its children.
    ///
    /// The set of children is reduced if it contains literals of the same variable.
    ///
    /// If two opposite literals are found, [`MaybeTrivial::True`] is returned;
    /// else, an instance of [`MaybeTrivial::NotTrivial`] is returned.
    /// If multiple occurrences of the same literal are found, only one is kept.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{FormulaNode, Literal, RcMut};
    ///
    /// let l1 = FormulaNode::new_literal(Literal::new(1.into(), false));
    /// let l1_rc = RcMut::new(l1);
    /// let l2 = FormulaNode::new_literal(Literal::new(2.into(), true));
    /// let l2_rc = RcMut::new(l2);
    /// let not_l2 = FormulaNode::new_literal(Literal::new(2.into(), false));
    /// let not_l2_rc = RcMut::new(not_l2);
    /// assert_eq!(
    ///     FormulaNode::new_or(vec![RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)]).unwrap(),
    ///     FormulaNode::new_or(
    ///         vec![RcMut::clone(&l1_rc), RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)
    ///     ]).unwrap()
    /// );
    /// assert!(FormulaNode::new_or(vec![RcMut::clone(&l2_rc), RcMut::clone(&not_l2_rc)]).is_true())
    /// ```
    pub fn new_or(children: Vec<RcMut<FormulaNode>>) -> MaybeTrivial<Self> {
        let mut new_children = Vec::with_capacity(children.len());
        let mut new_literals: Vec<Literal> = Vec::with_capacity(children.len());
        for child in children {
            match RcMut::clone(&child).borrow().node_kind {
                FormulaNodeKind::And(_) | FormulaNodeKind::Or(_) => new_children.push(child),
                FormulaNodeKind::Lit(lit) => {
                    let mut ignore = false;
                    for new_lit in new_literals.iter() {
                        if lit.var_id() == new_lit.var_id() {
                            if lit.polarity() != new_lit.polarity() {
                                return MaybeTrivial::True;
                            } else {
                                ignore = true;
                                break;
                            }
                        }
                    }
                    if !ignore {
                        new_literals.push(lit);
                        new_children.push(RcMut::clone(&child))
                    }
                }
            }
        }
        let node_kind = match new_children.len() {
            0 => return MaybeTrivial::False,
            1 => new_children[0].borrow().node_kind.clone(),
            _ => FormulaNodeKind::Or(new_children),
        };
        MaybeTrivial::NotTrivial(FormulaNode {
            node_kind,
            marked: false,
        })
    }

    /// Returns the node kind associated with this node.
    pub fn node_kind(&self) -> FormulaNodeKind {
        self.node_kind.clone()
    }

    pub(crate) fn negate(&mut self, marker: &mut FormulaNodeMarker) {
        if self.marked {
            return;
        }
        let new_kind = match &self.node_kind {
            FormulaNodeKind::And(children) => {
                children.iter().for_each(|c| c.borrow_mut().negate(marker));
                FormulaNodeKind::Or(children.clone())
            }
            FormulaNodeKind::Or(children) => {
                children.iter().for_each(|c| c.borrow_mut().negate(marker));
                FormulaNodeKind::And(children.clone())
            }
            FormulaNodeKind::Lit(lit) => FormulaNodeKind::Lit(lit.negate()),
        };
        self.node_kind = new_kind;
        marker.mark(self);
    }

    pub(crate) fn unmark_recursive(&mut self, marker: &mut FormulaNodeMarker) {
        marker.unmark(self);
        match &self.node_kind {
            FormulaNodeKind::And(children) | FormulaNodeKind::Or(children) => children
                .iter()
                .for_each(|c| c.borrow_mut().unmark_recursive(marker)),
            _ => {}
        }
    }

    /// Returns the variables that appear in the formula rooted by this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{FormulaNode, Literal, RcMut};
    ///
    /// let l1 = FormulaNode::new_literal(Literal::new(1.into(), false));
    /// let l1_rc = RcMut::new(l1);
    /// let l2 = FormulaNode::new_literal(Literal::new(2.into(), true));
    /// let l2_rc = RcMut::new(l2);
    /// let l3 = FormulaNode::new_literal(Literal::new(3.into(), true));
    /// let l3_rc = RcMut::new(l3);
    /// let not_l2 = FormulaNode::new_literal(Literal::new(2.into(), false));
    /// let not_l2_rc = RcMut::new(not_l2);
    /// let or = FormulaNode::new_or(vec![RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)]).unwrap();
    /// let or_rc = RcMut::new(or);
    /// let and = FormulaNode::new_and(vec![RcMut::clone(&or_rc), RcMut::clone(&l3_rc)]).unwrap();
    /// assert_eq!(3, and.vars().len());
    /// ```
    pub fn vars(&self) -> Vec<VarId> {
        let mut with_dups = self.vars_with_dups();
        with_dups.sort_unstable();
        with_dups.dedup();
        with_dups
    }

    fn vars_with_dups(&self) -> Vec<VarId> {
        match &self.node_kind {
            FormulaNodeKind::And(children) | FormulaNodeKind::Or(children) => {
                let mut result = Vec::new();
                for c in children {
                    result.append(&mut c.borrow().vars_with_dups());
                }
                result
            } // kcov-ignore
            FormulaNodeKind::Lit(l) => vec![l.var_id()],
        }
    }

    /// Returns an object dedicated to the display of this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{FormulaNode, Literal, RcMut};
    ///
    /// let l1 = FormulaNode::new_literal(Literal::new(1.into(), false));
    /// let l1_rc = RcMut::new(l1);
    /// let l2 = FormulaNode::new_literal(Literal::new(2.into(), true));
    /// let l2_rc = RcMut::new(l2);
    /// let and = FormulaNode::new_and(vec![RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)]).unwrap();
    /// let or = FormulaNode::new_or(vec![RcMut::clone(&l1_rc), RcMut::clone(&l2_rc)]).unwrap();
    /// assert_eq!("-1", format!("{}", l1_rc.borrow().default_display()));
    /// assert_eq!("2", format!("{}", l2_rc.borrow().default_display()));
    /// assert_eq!("and(-1, 2)", format!("{}", and.default_display()));
    /// assert_eq!("or(-1, 2)", format!("{}", or.default_display()));
    /// ```
    pub fn default_display<'a>(&'a self) -> DefaultDisplay<'a> {
        DefaultDisplay::new(self)
    }
}

pub struct DefaultDisplay<'a> {
    n: &'a FormulaNode,
}

impl<'a> DefaultDisplay<'a> {
    fn new(n: &'a FormulaNode) -> Self {
        DefaultDisplay { n }
    }
}

impl Display for DefaultDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn write_children(
            f: &mut std::fmt::Formatter<'_>,
            children: &Vec<RcMut<FormulaNode>>,
        ) -> std::fmt::Result {
            write!(f, "{}", children[0].borrow().default_display())?;
            for i in 1..children.len() {
                write!(f, ", {}", children[i].borrow().default_display())?;
            }
            Ok(())
        }
        match &self.n.node_kind {
            FormulaNodeKind::And(children) => {
                write!(f, "and(")?;
                write_children(f, children)?;
                write!(f, ")")?;
            }
            FormulaNodeKind::Or(children) => {
                write!(f, "or(")?;
                write_children(f, children)?;
                write!(f, ")")?;
            }
            FormulaNodeKind::Lit(l) => {
                write!(f, "{}{}", if l.polarity() { "" } else { "-" }, l.var_id())?
            }
        }
        Ok(())
    }
}

pub struct FormulaNodeMarker {
    n_marked: usize,
}

impl FormulaNodeMarker {
    pub fn new() -> Self {
        FormulaNodeMarker { n_marked: 0 }
    }

    pub fn mark(&mut self, node: &mut FormulaNode) {
        if !node.marked {
            node.marked = true;
            self.n_marked += 1;
        }
    }

    pub fn unmark(&mut self, node: &mut FormulaNode) {
        if node.marked {
            node.marked = false;
            self.n_marked -= 1;
        }
    }
}

impl Drop for FormulaNodeMarker {
    fn drop(&mut self) {
        if self.n_marked != 0 {
            panic!("some nodes are still marked")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfFormula, Formula};

    #[test]
    fn test_node_marker_ok() {
        let mut node = FormulaNode::new_literal(Literal::new(0.into(), false));
        let mut marker = FormulaNodeMarker::new();
        marker.mark(&mut node);
        marker.mark(&mut node);
        marker.unmark(&mut node);
        marker.unmark(&mut node);
    }

    #[test]
    #[should_panic(expected = "some nodes are still marked")]
    fn test_node_marker_error() {
        let mut node = FormulaNode::new_literal(Literal::new(0.into(), false));
        let mut marker = FormulaNodeMarker::new();
        marker.mark(&mut node);
    }

    #[test]
    fn test_negation() {
        let cnf = MaybeTrivial::<CnfFormula>::from(vec![
            vec![(0, false), (1, true)],
            vec![(0, true), (2, true)],
        ])
        .unwrap();
        let root = cnf.root();
        let mut marker = FormulaNodeMarker::new();
        root.borrow_mut().negate(&mut marker);
        root.borrow_mut().unmark_recursive(&mut marker);
        assert_eq!(
            "or(and(0, -1), and(-0, -2))",
            format!("{}", root.borrow().default_display())
        )
    }

    #[test]
    fn test_node_kind_eq() {
        let l0_false = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), false)));
        let l0_true = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), true)));
        let l1 = RcMut::new(FormulaNode::new_literal(Literal::new(1.into(), false)));
        let l2 = RcMut::new(FormulaNode::new_literal(Literal::new(2.into(), false)));
        let nodes = vec![
            RcMut::clone(&l0_false),
            RcMut::clone(&l0_true),
            RcMut::new(
                FormulaNode::new_and(vec![RcMut::clone(&l0_false), RcMut::clone(&l1)]).unwrap(),
            ),
            RcMut::new(
                FormulaNode::new_and(vec![RcMut::clone(&l0_true), RcMut::clone(&l1)]).unwrap(),
            ),
            RcMut::new(
                FormulaNode::new_and(vec![
                    RcMut::clone(&l0_true),
                    RcMut::clone(&l1),
                    RcMut::clone(&l2),
                ])
                .unwrap(),
            ),
            RcMut::new(
                FormulaNode::new_or(vec![RcMut::clone(&l0_false), RcMut::clone(&l1)]).unwrap(),
            ),
            RcMut::new(
                FormulaNode::new_or(vec![RcMut::clone(&l0_true), RcMut::clone(&l1)]).unwrap(),
            ),
        ];
        for i in 0..nodes.len() {
            for j in 0..nodes.len() {
                if i == j {
                    assert_eq!(nodes[i].borrow().node_kind(), nodes[j].borrow().node_kind())
                } else {
                    assert_ne!(nodes[i].borrow().node_kind(), nodes[j].borrow().node_kind())
                }
            }
        }
    }

    #[test]
    fn test_op_reductions() {
        let l0_false = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), false)));
        let l0_true = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), true)));
        let l1 = RcMut::new(FormulaNode::new_literal(Literal::new(1.into(), false)));
        assert_eq!(
            MaybeTrivial::False,
            FormulaNode::new_and(vec![RcMut::clone(&l0_false), RcMut::clone(&l0_true)])
        );
        assert_eq!(
            MaybeTrivial::True,
            FormulaNode::new_or(vec![RcMut::clone(&l0_false), RcMut::clone(&l0_true)])
        );
        assert_eq!(
            FormulaNode::new_literal(Literal::new(0.into(), false)),
            FormulaNode::new_and(vec![RcMut::clone(&l0_false)]).unwrap()
        );
        assert_eq!(
            FormulaNode::new_literal(Literal::new(0.into(), false)),
            FormulaNode::new_or(vec![RcMut::clone(&l0_false)]).unwrap()
        );
        assert_eq!(
            FormulaNode::new_and(vec![RcMut::clone(&l0_false), RcMut::clone(&l1)]),
            FormulaNode::new_and(vec![
                RcMut::clone(&l0_false),
                RcMut::clone(&l0_false),
                RcMut::clone(&l1)
            ])
        );
        assert_eq!(
            FormulaNode::new_or(vec![RcMut::clone(&l0_false), RcMut::clone(&l1)]),
            FormulaNode::new_or(vec![
                RcMut::clone(&l0_false),
                RcMut::clone(&l0_false),
                RcMut::clone(&l1)
            ])
        );
    }

    #[test]
    fn test_vars() {
        let l0_false = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), false)));
        let l0_true = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), true)));
        let l1 = RcMut::new(FormulaNode::new_literal(Literal::new(1.into(), false)));
        let l2 = RcMut::new(FormulaNode::new_literal(Literal::new(2.into(), false)));
        let and1 = RcMut::new(FormulaNode::new_and(vec![l0_false, l1]).unwrap());
        let and2 = RcMut::new(FormulaNode::new_and(vec![l0_true, l2]).unwrap());
        let or = FormulaNode::new_or(vec![and1, and2]).unwrap();
        assert_eq!(
            vec![VarId::from(0), VarId::from(1), VarId::from(2)] as Vec<VarId>,
            or.vars()
        )
    }

    #[test]
    fn test_default_display() {
        let l0_false = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), false)));
        let l0_true = RcMut::new(FormulaNode::new_literal(Literal::new(0.into(), true)));
        let l1 = RcMut::new(FormulaNode::new_literal(Literal::new(1.into(), false)));
        let l2 = RcMut::new(FormulaNode::new_literal(Literal::new(2.into(), false)));
        let and1 = RcMut::new(FormulaNode::new_and(vec![l0_false, l1]).unwrap());
        let and2 = RcMut::new(FormulaNode::new_and(vec![l0_true, l2]).unwrap());
        let or = FormulaNode::new_or(vec![and1, and2]).unwrap();
        assert_eq!(
            "or(and(-0, -1), and(0, -2))",
            format!("{}", or.default_display())
        )
    }
}
