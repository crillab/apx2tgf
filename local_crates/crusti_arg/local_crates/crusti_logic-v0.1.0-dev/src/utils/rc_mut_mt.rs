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

use std::{
    borrow::{Borrow, BorrowMut},
    fmt::{Debug, Display},
    ops::{Deref, DerefMut},
    sync::{Arc, LockResult, RwLock, RwLockReadGuard, RwLockWriteGuard},
};

/// A reference-counted cell bringing interior mutability in a multi-thread context.
///
/// This structure is equivalent to an [`Arc<RwLock<T>>`].
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
pub struct RcMut<T>(Arc<RwLock<T>>);

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
        RcMut(Arc::new(RwLock::new(t)))
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
        match Arc::try_unwrap(this.0) {
            Ok(r) => r.into_inner().unwrap(),
            Err(_) => panic!(),
        }
    }

    /// Immutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `LocalBorrow` exits scope.
    /// Multiple immutable borrows can be taken out at the same time.
    ///
    /// #Panics
    ///
    /// Panics if the value is currently mutably borrowed.
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
    /// assert_eq!(6, *rc.borrow());
    /// ```
    pub fn borrow(&self) -> LocalBorrow<T> {
        LocalBorrow { r: self.0.read() }
    }

    /// Mutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `LocalMutBorrow` exits scope.
    /// The value cannot be borrowed while this borrow is active.
    ///
    /// #Panics
    ///
    /// Panics if the value is currently borrowed. For a non-panicking variant, use try_borrow_mut.
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
    /// assert_eq!(6, *rc.borrow());
    /// ```
    pub fn borrow_mut(&self) -> LocalMutBorrow<T> {
        LocalMutBorrow { r: self.0.write() }
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
        Arc::ptr_eq(&a.0, &b.0)
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

    /// Consumes the `RcMut`, returning its `Arc<RwLock<T>>`.
    pub fn unwrap(a: RcMut<T>) -> Arc<RwLock<T>> {
        a.0
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
    type Target = RwLock<T>;

    #[inline(always)]
    fn deref(&self) -> &RwLock<T> {
        &self.0
    }
}

pub struct LocalBorrow<'a, T> {
    r: LockResult<RwLockReadGuard<'a, T>>,
}

impl<T> Borrow<T> for LocalBorrow<'_, T> {
    fn borrow(&self) -> &T {
        self.r.as_ref().unwrap()
    }
}

impl<T> Deref for LocalBorrow<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.r.as_ref().unwrap()
    }
}

impl<T> Debug for LocalBorrow<'_, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.borrow() as &T)
    }
}

impl<T> Display for LocalBorrow<'_, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.borrow() as &T)
    }
}

pub struct LocalMutBorrow<'a, T> {
    r: LockResult<RwLockWriteGuard<'a, T>>,
}

impl<T> Borrow<T> for LocalMutBorrow<'_, T> {
    fn borrow(&self) -> &T {
        self.r.as_ref().unwrap()
    }
}

impl<T> BorrowMut<T> for LocalMutBorrow<'_, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self.r.as_mut().unwrap()
    }
}

impl<T> Display for LocalMutBorrow<'_, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.borrow() as &T)
    }
}

impl<T> Deref for LocalMutBorrow<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.r.as_ref().unwrap()
    }
}

impl<T> DerefMut for LocalMutBorrow<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.r.as_mut().unwrap()
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
