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

/// A variable identifier.
///
/// It can be obtained from and converted into `usize`.
///
/// # Examples
///
/// ```
/// use crusti_logic::VarId;
///
/// assert_eq!(0, usize::from(VarId::from(0)))
/// ```
#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct VarId(usize);

impl From<usize> for VarId {
    fn from(u: usize) -> Self {
        VarId(u)
    }
}

impl From<VarId> for usize {
    fn from(v: VarId) -> Self {
        v.0
    }
}

impl std::fmt::Display for VarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

/// A literal, composed by a [`VarId`] and a `bool` (its polarity).
///
/// # Order
///
/// A total order is imposed on literals:
/// * if variable identifiers are not equal, the same order applies to the literals;
/// * if variable identifiers are equal and polarity are different, the polarity (`bool`) order applies;
/// * if variable identifiers and polarity are equals, the two literals are equal.
///
/// # Examples
///
/// ```
/// use crusti_logic::{VarId, Literal};
///
/// let v = VarId::from(0);
/// let l = Literal::new(v, true);
/// let not_l = Literal::new(v, false);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Literal(VarId, bool);

impl Literal {
    /// Builds a new literal, given its [`VarId`] and its polarity as a `bool`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{VarId, Literal};
    ///
    /// let v = VarId::from(0);
    /// let l = Literal::new(v, true);
    /// let not_l = Literal::new(v, false);
    /// ```
    pub fn new(var_id: VarId, polarity: bool) -> Self {
        Literal(var_id, polarity)
    }

    /// Returns the negation of the literal, as a new `Literal`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{VarId, Literal};
    ///
    /// let v = VarId::from(0);
    /// let l = Literal::new(v, true);
    /// let not_l = l.negate();
    /// assert_eq!(Literal::new(v, false), not_l)
    /// ```
    pub fn negate(&self) -> Self {
        Literal(self.0, !self.1)
    }

    /// Checks if a literal is the negation of this literal.
    fn is_negation_of(&self, other: &Literal) -> bool {
        self.0 == other.0 && self.1 != other.1
    }

    /// Returns the [`VarId`] of this literal.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{VarId, Literal};
    ///
    /// let v = VarId::from(0);
    /// let l = Literal::new(v, true);
    /// assert_eq!(v, l.var_id());
    /// ```
    pub fn var_id(&self) -> VarId {
        self.0
    }

    /// Returns the polarity of this literal.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::{VarId, Literal};
    ///
    /// let v = VarId::from(0);
    /// let l = Literal::new(v, true);
    /// assert!(l.polarity());
    /// ```
    pub fn polarity(&self) -> bool {
        self.1
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let id_cmp = self.0.partial_cmp(&other.0);
        if let Some(std::cmp::Ordering::Equal) = id_cmp {
            self.1.partial_cmp(&other.1)
        } else {
            id_cmp
        }
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl From<(usize, bool)> for Literal {
    fn from(couple: (usize, bool)) -> Self {
        Literal::new(VarId::from(couple.0), couple.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiteralVec(Vec<Literal>);

impl LiteralVec {
    pub fn new(mut literals: Vec<Literal>) -> Self {
        literals.sort_unstable();
        LiteralVec(literals)
    }

    pub fn clean(self) -> Option<LiteralVec> {
        let literals = &self.0;
        if literals.is_empty() {
            return Some(LiteralVec(vec![]));
        }
        let mut new_vec: Vec<Literal> = Vec::with_capacity(literals.len());
        for i in 0..literals.len() - 1 {
            let lit_i = &literals[i];
            let mut ignore_lit = false;
            for j in i + 1..literals.len() {
                let lit_j = &literals[j];
                if lit_i.is_negation_of(lit_j) {
                    return None;
                }
                if lit_i == lit_j {
                    ignore_lit = true;
                    break;
                }
            }
            if !ignore_lit {
                new_vec.push(*lit_i);
            }
        }
        new_vec.push(literals[literals.len() - 1]);
        Some(LiteralVec(new_vec))
    }

    pub fn as_slice(&self) -> &[Literal] {
        &self.0
    }

    pub fn to_vec(self) -> Vec<Literal> {
        self.0
    }

    pub fn n_vars(&self) -> usize {
        1 + self
            .0
            .iter()
            .map(|l| l.var_id().into())
            .fold(0, |acc, v| if acc > v { acc } else { v })
    }
}

impl<T> From<Vec<T>> for LiteralVec
where
    T: Into<Literal>,
{
    fn from(v: Vec<T>) -> Self {
        LiteralVec::new(v.into_iter().map(|l| l.into()).collect())
    }
}

impl<T> From<&[T]> for LiteralVec
where
    T: Copy + Into<Literal>,
{
    fn from(v: &[T]) -> Self {
        LiteralVec::new(v.into_iter().map(|l| (*l).into()).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_negate() {
        let lit = Literal::new(0.into(), false);
        let neg = lit.negate();
        assert!(neg.1);
    }

    #[test]
    fn test_eq() {
        let lit0 = Literal::new(0.into(), false);
        let lit1 = Literal::new(0.into(), false);
        let lit2 = Literal::new(0.into(), true);
        assert_eq!(lit0, lit1);
        assert_ne!(lit0, lit2);
    }

    #[test]
    fn test_sort() {
        let v = LiteralVec::new(vec![
            Literal::new(1.into(), true),
            Literal::new(1.into(), false),
            Literal::new(0.into(), false),
            Literal::new(0.into(), true),
        ]);
        assert_eq!(
            vec![
                Literal::new(0.into(), false),
                Literal::new(0.into(), true),
                Literal::new(1.into(), false),
                Literal::new(1.into(), true)
            ],
            v.to_vec()
        );
    }
}
