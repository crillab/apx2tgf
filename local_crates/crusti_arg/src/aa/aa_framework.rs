// crusti_arg
// Copyright (C) 2020  Artois University and CNRS
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
//
// Contributors:
//   *   CRIL - initial API and implementation

use crate::aa::arguments::Argument;
use crate::aa::arguments::ArgumentSet;
use crate::aa::arguments::LabelType;
use anyhow::{anyhow, Context, Result};
use std::fmt::Display;

/// An Abstract Argumentation framework as defined in Dung semantics.
pub struct AAFramework<T>
where
    T: LabelType,
{
    arguments: ArgumentSet<T>,
    attacks: Vec<(usize, usize)>,
}

/// An attack, represented as a couple of two arguments.
///
/// Attacks are built by [`AAFramework`] objects.
///
/// [`AAFramework`]: struct.AAFramework.html
pub struct Attack<'a, T>(&'a Argument<T>, &'a Argument<T>)
where
    T: LabelType;

impl<'a, T> Attack<'a, T>
where
    T: LabelType,
{
    /// Returns the attacker.
    ///
    /// Example
    ///
    /// ```
    /// # use crusti_arg::{Attack, LabelType};
    /// fn describe_attack<T: LabelType>(attack: &Attack<T>) {
    ///     println!("{} attacks {}", attack.attacker(), attack.attacked());
    /// }
    /// ```
    pub fn attacker(&self) -> &'a Argument<T> {
        self.0
    }

    /// Returns the attacked argument.
    ///
    /// Example
    ///
    /// ```
    /// # use crusti_arg::{Attack, LabelType};
    /// fn describe_attack<T: LabelType>(attack: &Attack<T>) {
    ///     println!("{} attacks {}", attack.attacker(), attack.attacked());
    /// }
    /// ```
    pub fn attacked(&self) -> &'a Argument<T> {
        self.1
    }
}

impl<'a, T> Display for Attack<'a, T>
where
    T: LabelType,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format_attack(self.0, self.1))
    }
}

pub(crate) fn format_attack<T>(attacker: &T, attacked: &T) -> String
where
    T: Display,
{
    format!("{} → {}", attacker, attacked)
}

impl<T> AAFramework<T>
where
    T: LabelType,
{
    /// Builds an AA framework.
    ///
    /// The set of arguments used in the framework must be provided.
    ///
    /// # Arguments
    ///
    /// * `arguments` - the set of arguments
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{ArgumentSet, AAFramework};
    /// let arguments = ArgumentSet::new(&["a", "b", "c"]).unwrap();
    /// let framework = AAFramework::new(arguments);
    /// assert_eq!(3, framework.argument_set().len());
    /// assert_eq!(0, framework.iter_attacks().count());
    /// ```
    pub fn new(arguments: ArgumentSet<T>) -> Self {
        AAFramework {
            arguments,
            attacks: vec![],
        } // kcov-ignore
    }

    /// Adds a new attack given the labels of the source and destination arguments.
    ///
    /// If the provided arguments are undefined, an error is returned.
    /// Else, the attack is added.
    ///
    /// If the attack already exists, it is added another time (no checks are made for existence).
    ///
    /// # Arguments
    ///
    /// * `from` - the label of the source arguments (attacker)
    /// * `to` - the label of the destination argument (attacked)
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels).unwrap();
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack(&labels[0], &labels[1]);
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        let context = || format!("cannot add an attack from {:?} to {:?}", from, to,);
        self.attacks.push((
            self.arguments
                .get_argument_index(from)
                .with_context(context)?,
            self.arguments
                .get_argument_index(to)
                .with_context(context)?,
        )); // kcov-ignore
        Ok(())
    }

    /// Adds a new attack given the IDs of the source and destination arguments.
    ///
    /// If the provided arguments are undefined, an error is returned.
    /// Else, the attack is added.
    ///
    /// If the attack already exists, it is added another time (no checks are made for existence).
    ///
    /// # Arguments
    ///
    /// * `from` - the id of the source arguments (attacker)
    /// * `to` - the id of the destination argument (attacked)
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels).unwrap();
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn new_attack_by_ids(&mut self, from: usize, to: usize) -> Result<()> {
        let n_arguments = self.arguments.len();
        if from >= n_arguments || to >= n_arguments {
            return Err(anyhow!(
                "cannot add an attack from identifiers {:?} to {:?}; max id is {}",
                from,
                to,
                n_arguments - 1
            ));
        }
        self.attacks.push((from, to));
        Ok(())
    }

    /// Returns the argument set of the framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels).unwrap();
    /// let framework = AAFramework::new(arguments);
    /// assert_eq!(3, framework.argument_set().len());
    /// ```
    pub fn argument_set(&self) -> &ArgumentSet<T> {
        &self.arguments
    }

    /// Provides an iterator to the attacks.
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels).unwrap();
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn iter_attacks<'a>(&'a self) -> Box<dyn Iterator<Item = Attack<'a, T>> + 'a> {
        Box::new(self.attacks.iter().map(move |att| {
            Attack(
                self.arguments.get_argument_by_id(att.0),
                self.arguments.get_argument_by_id(att.1),
            )
        }))
    }

    /// returns the number of attacks in this framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crusti_arg::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels).unwrap();
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.n_attacks());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.n_attacks());
    /// ```
    pub fn n_attacks<'a>(&'a self) -> usize {
        self.attacks.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_attack_ok() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels).unwrap();
        let mut attacks = AAFramework::new(args);
        assert_eq!(0, attacks.attacks.len());
        attacks.new_attack(&arg_labels[0], &arg_labels[0]).unwrap();
        assert_eq!(1, attacks.attacks.len());
        assert_eq!((0, 0), attacks.attacks[0]);
    }

    #[test]
    fn test_new_attack_unknown_label_1() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels).unwrap();
        let mut attacks = AAFramework::new(args);
        attacks
            .new_attack(&"d".to_string(), &arg_labels[0])
            .unwrap_err();
    }

    #[test]
    fn test_new_attack_unknown_label_2() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels).unwrap();
        let mut attacks = AAFramework::new(args);
        attacks
            .new_attack(&arg_labels[0], &"d".to_string())
            .unwrap_err();
    }

    #[test]
    fn test_new_attack_by_ids_ok() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels).unwrap();
        let mut attacks = AAFramework::new(args);
        assert_eq!(0, attacks.attacks.len());
        attacks.new_attack_by_ids(0, 0).unwrap();
        assert_eq!(1, attacks.attacks.len());
        assert_eq!((0, 0), attacks.attacks[0]);
    }

    #[test]
    fn test_new_attack_by_ids_unknown_id_1() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels).unwrap();
        let mut attacks = AAFramework::new(args);
        attacks.new_attack_by_ids(3, 0).unwrap_err();
    }

    #[test]
    fn test_new_attack_by_ids_unknown_id_2() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels).unwrap();
        let mut attacks = AAFramework::new(args);
        attacks.new_attack_by_ids(0, 3).unwrap_err();
    }
}
