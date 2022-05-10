use crate::output::diagnostic;
use crate::parse::extensions::simple::type_expressions::metavalues;
use crate::parse::extensions::simple::type_expressions::metavars;
use std::cell::RefCell;
use std::rc::Rc;

/// A data block for a metavariable. This holds the set of constraints imposed
/// on the variable, and caches the possible values that the variable may still
/// have.
#[derive(Clone, Debug)]
pub struct Data {
    /// Weak references to all aliases that refer to this data block. For
    /// example, in fn(T) -> T, the return type, the first parameter, and
    /// generic T all refer to the same data block.
    aliases: Vec<metavars::alias::Weak>,

    /// The possible values remaining for this metavariable.
    values: metavalues::set::Set,

    /// Set when it shouldn't be possible for this value to be further
    /// constrained. If this is set, merge_with() will always panic, and
    /// constrain() will panic if a constraint is added that isn't already
    /// in the list. This flag is necessary to determine when solving is
    /// complete, and for determining when covers() can start returning a
    /// value.
    complete: bool,
}

impl Default for Data {
    /// Returns a new, empty data block that has not yet been constrained.
    fn default() -> Self {
        Self {
            aliases: vec![],
            values: metavalues::set::Set::full(),
            complete: false
        }
    }
}

impl Data {
    /// Adds an alias to this data block.
    pub fn push_alias(&mut self, alias: &metavars::alias::Reference) {
        self.aliases.push(Rc::downgrade(alias));
    }

    /// Returns a suitable Err for when a constraint is added to a complete
    /// variable.
    fn check_can_be_constrained(&self) -> diagnostic::Result<()> {
        if self.complete {
            Err(cause!(
                InternalError,
                "attempting to further constrain metavar after it was marked as complete"
            ))
        } else {
            Ok(())
        }
    }

    /// Adds an equality constraint between this metavariable and the other
    /// metavariable. This essentially just merges their data blocks: other
    /// is merged into this, and references to other are redirected. Returns
    /// whether the any possible values are removed from the perspective of
    /// either reference.
    pub fn merge_with(&mut self, other: &Reference) -> diagnostic::Result<bool> {
        self.check_can_be_constrained()?;
        let mut other_data = other.try_borrow_mut().map_err(|_| {
            cause!(
                InternalError,
                "merge_with() failed to borrow sacrificial data block"
            )
        })?;
        other_data.check_can_be_constrained()?;

        // Remap aliases to block b to block a instead, dropping expired weak
        // references while we're at it.
        self.aliases
            .extend(other_data.aliases.drain(..).filter(|x| {
                x.upgrade()
                    .map(|x| x.borrow_mut().data = other.clone())
                    .is_some()
            }));

        // Constrain the value of a by the possible values of b, such that
        // the resulting possibilities in a' are the intersection of a and b.
        self.constrain(&other_data.values)
    }

    /// Further constrains the possible values of this variable. Returns
    /// whether the new constraint reduced the number of possible values.
    pub fn constrain(&mut self, constraint: &metavalues::set::Set) -> diagnostic::Result<bool> {
        self.check_can_be_constrained()?;
        self.values.constrain(&constraint)
    }

    /// If the set of possible values for this metavariable has been reduced to
    /// only one possibility, return it. Otherwise returns None.
    pub fn value(&self) -> diagnostic::Result<Option<metavalues::value::Value>> {
        self.values.value()
    }

    /// Returns whether this metavalue still has the given value as a
    /// possibility.
    pub fn matches(&self, value: &metavalues::value::Value) -> diagnostic::Result<bool> {
        self.values.contains(value)
    }

    /// Returns whether the value of this metavariable can be proven to either
    /// cover or not cover the value of the other metavariable, where
    /// "a covers b" means that all possible values of b are also possible
    /// values of a. If this cannot yet be proven, None is returned. This
    /// happens when:
    ///
    ///  - self currently covers other, but new constraints may still be added
    ///    to self; or
    ///  - self currently does not cover other, but they do have at least one
    ///    possible value in common, and new constraints may still be added to
    ///    remove possibile values from other.
    pub fn covers(&self, other: &Data) -> diagnostic::Result<Option<bool>> {
        Ok(match self.values.superset_of(&other.values)? {
            Some(true) => {
                if self.complete {
                    Some(true)
                } else {
                    None
                }
            }
            Some(false) => {
                if other.complete || !self.values.intersects_with(&other.values)? {
                    Some(false)
                } else {
                    None
                }
            }
            None => None,
        })
    }

    /// Returns whether this value could equal the other value.
    pub fn intersects_with(&self, other: &Data) -> diagnostic::Result<bool> {
        self.values.intersects_with(&other.values)
    }

    /// Marks this variable as being fully constrained, i.e. no further
    /// constraints will be imposed. Any covers() function evaluation that
    /// relies on this fact may start returning a value.
    pub fn mark_complete(&mut self) {
        self.complete = true;
    }

    /// Returns whether this value has been completely constrained.
    pub fn is_complete(&self) -> bool {
        self.complete
    }
}

/// Reference to the data block for a metavariable, holding its constraints
/// and remaining possible values.
pub type Reference = Rc<RefCell<Data>>;
