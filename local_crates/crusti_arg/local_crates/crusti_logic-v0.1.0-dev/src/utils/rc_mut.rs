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

use std::{cell::RefCell, fmt::Debug, ops::Deref, rc::Rc};

/// A reference-counted cell bringing interior mutability in a mono-thread context.
///
/// This structure is equivalent to an [`Rc<RefCell<T>>`].
///
/// # Examples
///
/// ```
/// use crusti_logic::RcMut;
///
/// let a  = 5;
/// let rc = RcMut::new(a);
/// assert_eq!(5, *rc.borrow());
/// *rc.borrow_mut() = 6;
/// let rc_bis = RcMut::clone(&rc);
/// assert_eq!(6, *rc.borrow());
/// assert_eq!(6, *rc_bis.borrow());
/// ```
pub struct RcMut<T>(Rc<RefCell<T>>);

impl<T> RcMut<T> {
    /// Constructs a new `RcMut<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::RcMut;
    ///
    /// let a  = 5;
    /// let rc = RcMut::new(a);
    /// ```
    pub fn new(t: T) -> Self {
        RcMut(Rc::new(RefCell::new(t)))
    }

    /// Consumes the `RcMut`, returning the wrapped value.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::RcMut;
    ///
    /// let a  = 5;
    /// let rc = RcMut::new(a);
    /// assert_eq!(5, RcMut::into_inner(rc));
    /// ```
    pub fn into_inner(this: RcMut<T>) -> T {
        match Rc::try_unwrap(this.0) {
            Ok(r) => r.into_inner(),
            Err(_) => panic!(),
        }
    }

    /// Returns `true` if the two `RcMut`s point to the same allocation (in a vein similar to [`ptr::eq`]).
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::RcMut;
    ///
    /// let a  = 5;
    /// let rc = RcMut::new(a);
    /// let rc_bis = RcMut::clone(&rc);
    /// assert!(RcMut::ptr_eq(&rc, &rc_bis));
    /// assert!(!RcMut::ptr_eq(&rc, &RcMut::new(a)));
    /// ```
    ///
    /// [`ptr::eq`]: core::ptr::eq
    pub fn ptr_eq(a: &RcMut<T>, b: &RcMut<T>) -> bool {
        Rc::ptr_eq(&a.0, &b.0)
    }

    /// Makes a clone of the `RcMut` pointer.
    ///
    /// This creates another pointer to the same allocation, increasing the
    /// strong reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use crusti_logic::RcMut;
    ///
    /// let a  = 5;
    /// let rc = RcMut::new(a);
    /// let rc_bis = RcMut::clone(&rc);
    /// assert!(RcMut::ptr_eq(&rc, &rc_bis));
    /// ```
    pub fn clone(a: &RcMut<T>) -> Self {
        RcMut(a.0.clone())
    }
}

impl<T> Clone for RcMut<T>
where
    T: Debug,
{
    fn clone(&self) -> Self {
        RcMut::clone(&self)
    }
}

impl<T> Deref for RcMut<T> {
    type Target = RefCell<T>;

    #[inline(always)]
    fn deref(&self) -> &RefCell<T> {
        &self.0
    }
}

impl<T> Debug for RcMut<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.borrow())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_debug() {
        assert_eq!("0", format!("{:?}", RcMut::new(0)))
    }
}
