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

use std::{fmt::Debug, mem};

/// A logical content that may be trivial.
///
/// This enum mainly acts like an [`Option`],
/// where [`Some`] is replaced by [`NotTrivial`]
/// and [`None`] can be [`True`] or [`False`].
///
/// [`Option`]: std::option::Option
/// [`Some`]: std::option::Option::Some
/// [`None`]: std::option::Option::None
/// [`NotTrivial`]: MaybeTrivial::NotTrivial
/// [`True`]: MaybeTrivial::True
/// [`False`]: MaybeTrivial::False
#[derive(Debug)] // kcov-ignore
pub enum MaybeTrivial<T> {
    /// A value which is not trivial
    NotTrivial(T), // kcov-ignore
    /// A trivially `true` value (a tautology)
    True,
    /// A trivially `false` value (a contradiction)
    False,
}

impl<F> MaybeTrivial<F> {
    /// Returns the contained [`MaybeTrivial::NotTrivial`] value, consuming the self value.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `True` or `False`.
    pub fn unwrap(self) -> F {
        // kcov-ignore-start
        match self {
            // kcov-ignore-end
            MaybeTrivial::NotTrivial(f) => f,
            MaybeTrivial::True => panic!("cannot unwrap MaybeTrivial for True"),
            MaybeTrivial::False => panic!("cannot unwrap MaybeTrivial for False"),
        }
    }

    /// Returns the contained [`MaybeTrivial::NotTrivial`] value, consuming the self value.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `True` or `False` with a custom panic message provided by `msg`.
    pub fn expect(self, msg: &str) -> F {
        match self {
            MaybeTrivial::NotTrivial(f) => f,
            _ => panic!("{}", msg),
        }
    }

    /// Returns `true` if the `MaybeTrivial` is a [`False`] value.
    ///
    /// [`False`]: MaybeTrivial::False
    pub fn is_false(&self) -> bool {
        matches!(self, MaybeTrivial::False)
    }

    /// Returns `true` if the `MaybeTrivial` is a [`True`] value.
    ///
    /// [`True`]: MaybeTrivial::True
    pub fn is_true(&self) -> bool {
        matches!(self, MaybeTrivial::True)
    }

    /// Converts from `&MaybeTrivial<T>` to `MaybeTrivial<&T>`.
    pub fn as_ref(&self) -> MaybeTrivial<&F> {
        match self {
            MaybeTrivial::NotTrivial(ref f) => MaybeTrivial::NotTrivial(f),
            MaybeTrivial::True => MaybeTrivial::True,
            MaybeTrivial::False => MaybeTrivial::False,
        }
    }

    /// Replaces the actual value in the `MaybeTrivial` by the value given in parameter, returning the old value.
    pub fn replace(&mut self, value: MaybeTrivial<F>) -> MaybeTrivial<F> {
        mem::replace(self, value)
    }

    /// Maps a `MaybeTrivial<T>` to `MaybeTrivial<U>` by applying a function to a non-trivial value.
    pub fn map<M, U>(self, mapper: M) -> MaybeTrivial<U>
    where
        M: FnOnce(F) -> U,
    {
        match self {
            MaybeTrivial::NotTrivial(f) => MaybeTrivial::NotTrivial(mapper(f)),
            MaybeTrivial::True => MaybeTrivial::True,
            MaybeTrivial::False => MaybeTrivial::False,
        }
    }

    /// Returns [`True`] (resp. [`False`]) if the `MaybeTrivial` is [`True`] (resp. [`False`]),
    /// otherwise calls `mapper` with the non-trivial value and returns the result.
    ///
    /// [`True`]: MaybeTrivial::True
    /// [`False`]: MaybeTrivial::False
    pub fn and_then<U, M>(self, mapper: M) -> MaybeTrivial<U>
    where
        M: FnOnce(F) -> MaybeTrivial<U>,
    {
        match self {
            MaybeTrivial::NotTrivial(f) => mapper(f),
            MaybeTrivial::True => MaybeTrivial::True,
            MaybeTrivial::False => MaybeTrivial::False,
        }
    }
}

impl<F> PartialEq for MaybeTrivial<F>
where
    F: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match self {
            MaybeTrivial::NotTrivial(f) => match other {
                MaybeTrivial::NotTrivial(f2) => f.eq(f2),
                _ => false,
            },
            MaybeTrivial::True => match other {
                MaybeTrivial::True => true,
                _ => false,
            },
            MaybeTrivial::False => match other {
                MaybeTrivial::False => true,
                _ => false,
            },
        }
    }
}

impl<T> From<bool> for MaybeTrivial<T> {
    fn from(v: bool) -> Self {
        if v {
            MaybeTrivial::True
        } else {
            MaybeTrivial::False
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unwrap_ok() {
        assert_eq!(0, MaybeTrivial::NotTrivial(0).unwrap());
    }

    #[test]
    #[should_panic(expected = "cannot unwrap MaybeTrivial for False")]
    fn test_unwrap_on_false() {
        MaybeTrivial::False.unwrap()
    } // kcov-ignore

    #[test]
    #[should_panic(expected = "cannot unwrap MaybeTrivial for True")]
    fn test_unwrap_on_true() {
        MaybeTrivial::True.unwrap()
    } // kcov-ignore

    #[test]
    fn test_as_ref() {
        assert_eq!(&0, MaybeTrivial::NotTrivial(0).as_ref().unwrap());
        assert_eq!(MaybeTrivial::False, MaybeTrivial::<usize>::False.as_ref());
        assert_eq!(MaybeTrivial::True, MaybeTrivial::<usize>::True.as_ref());
    }

    #[test]
    fn test_map() {
        let mapper = |i| i + 1;
        assert_eq!(1, MaybeTrivial::NotTrivial(0).map(mapper).unwrap());
        assert_eq!(
            MaybeTrivial::False,
            MaybeTrivial::<usize>::False.map(mapper)
        );
        assert_eq!(MaybeTrivial::True, MaybeTrivial::<usize>::True.map(mapper));
    }

    #[test]
    fn test_and_then() {
        let mapper = |i| match i {
            0 => MaybeTrivial::False,
            1 => MaybeTrivial::True,
            n => MaybeTrivial::NotTrivial(n),
        };
        assert_eq!(
            MaybeTrivial::False,
            MaybeTrivial::NotTrivial(0).and_then(mapper)
        );
        assert_eq!(
            MaybeTrivial::True,
            MaybeTrivial::NotTrivial(1).and_then(mapper)
        );
        assert_eq!(2, MaybeTrivial::NotTrivial(2).and_then(mapper).unwrap());
        assert_eq!(
            MaybeTrivial::False,
            MaybeTrivial::<usize>::False.and_then(mapper)
        );
        assert_eq!(
            MaybeTrivial::True,
            MaybeTrivial::<usize>::True.and_then(mapper)
        );
    }

    #[test]
    fn test_eq() {
        let t = vec![
            MaybeTrivial::NotTrivial(0),
            MaybeTrivial::NotTrivial(1),
            MaybeTrivial::False,
            MaybeTrivial::True,
        ];
        for i in 0..t.len() {
            for j in 0..t.len() {
                if i == j {
                    assert_eq!(t[i], t[j])
                } else {
                    assert_ne!(t[i], t[j])
                }
            }
        }
    }

    #[test]
    fn test_is_true() {
        assert!(MaybeTrivial::<usize>::True.is_true());
        assert!(!MaybeTrivial::<usize>::False.is_true());
        assert!(!MaybeTrivial::<usize>::NotTrivial(1).is_true());
    }

    #[test]
    fn test_is_false() {
        assert!(!MaybeTrivial::<usize>::True.is_false());
        assert!(MaybeTrivial::<usize>::False.is_false());
        assert!(!MaybeTrivial::<usize>::NotTrivial(1).is_false());
    }

    #[test]
    fn test_replace() {
        let mut t = MaybeTrivial::<usize>::True;
        assert_eq!(
            MaybeTrivial::<usize>::True,
            t.replace(MaybeTrivial::<usize>::False)
        );
        assert_eq!(MaybeTrivial::<usize>::False, t);
    }

    #[test]
    #[should_panic(expected = "err")]
    fn test_except_msg() {
        MaybeTrivial::<usize>::True.expect("err");
    }
}
