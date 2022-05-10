use crate::output::diagnostic;
use crate::parse::extensions::simple::type_expressions::context;
use crate::parse::extensions::simple::type_expressions::metavalues;
use crate::parse::extensions::simple::type_expressions::metavars;
use std::rc::Rc;
use std::cell::RefCell;

/// A reference to a metavariable.
#[derive(Clone, Debug)]
pub struct Reference {
    /// The method through which the metavariable is referenced.
    key: metavars::key::Key,

    /// The raw parsed string that the user used to refer to the metavariable,
    /// if any. Used to keep track of the case/syntax convention that the user
    /// used, in order to produce better diagnostic messages. bind() moves this
    /// into the alias block.
    description: Option<Rc<String>>,

    /// Reference to the alias block for this metavariable. Initialized via
    /// bind().
    alias: RefCell<Option<metavars::alias::Reference>>,
}

impl std::fmt::Display for Reference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Try to print the description from the alias block.
        if let Ok(alias) = self.alias.try_borrow() {
            if let Some(alias) = alias.as_ref() {
                if let Ok(alias) = alias.try_borrow() {
                    return write!(f, "{alias}");
                }
            }
        }

        // If we aren't bound to an alias block yet, or if we can't borrow
        // to access the description, see if we have a description of our own.
        if let Some(s) = &self.description {
            return write!(f, "{s}");
        }

        // Fall back to the generated description of the key.
        self.key.fmt(f)
    }
}

impl PartialEq for Reference {
    /// Checks whether two references are functionally the same. Two references
    /// that alias the same value are NOT considered to be equal.
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Reference {
    /// Creates an (unbound) named reference to a metavariable.
    pub fn new_generic<S: ToString>(name: S) -> Self {
        let name = name.to_string();
        let key = name.to_ascii_lowercase();
        Reference {
            key: metavars::key::Key::Generic(key),
            description: Some(Rc::new(name)),
            alias: RefCell::default(),
        }
    }

    /// Creates a reference to a new, unique metavariable. The reference can be
    /// copied to refer to the same metavariable multiple times.
    pub fn new_inferred<S: ToString>(description: Option<S>) -> Self {
        Reference {
            key: metavars::key::Key::Inferred(metavars::key::Unique::default()),
            description: description.map(|x| Rc::new(x.to_string())),
            alias: RefCell::default(),
        }
    }

    /// Creates a reference to the type of the index'th parameter of the
    /// function being solved for.
    pub fn new_function_parameter_type(index: usize) -> Self {
        Reference {
            key: metavars::key::Key::FunctionParameterType(index),
            description: None,
            alias: RefCell::default(),
        }
    }

    /// Creates a reference to the return type of the function being solved
    /// for.
    pub fn new_function_return_type() -> Self {
        Reference {
            key: metavars::key::Key::FunctionReturnType,
            description: None,
            alias: RefCell::default(),
        }
    }

    /// Bind this metavariable reference to the given context.
    pub fn bind(&self, context: &mut context::solver::Solver) -> diagnostic::Result<()> {
        // Construct alias and data blocks if they don't already exist in the
        // context, and save the correct reference in self.alias.
        let mut binding = self.alias.try_borrow_mut().map_err(|_| cause!(InternalError, "concurrency error"))?;
        if binding.replace(context.resolve(&self.key, || self.to_string())).is_some() {
            Err(cause!(
                InternalError,
                "attempt to dereference unbound reference to {} in function constraint solver",
                self.key
            ))
        } else {
            Ok(())
        }
    }

    /// Returns a reference to the binding.
    pub fn binding(&self) -> diagnostic::Result<std::cell::Ref<Option<metavars::alias::Reference>>> {
        self.alias.try_borrow().map_err(|_| cause!(InternalError, "concurrency error"))
    }

    /// Given a reference to the binding, returns the pointer to the alias
    /// block.
    fn alias_ptr<'a, 'b>(&'a self, binding: &'b std::cell::Ref<Option<metavars::alias::Reference>>) -> diagnostic::Result<&'b metavars::alias::Reference> {
        binding.as_ref().ok_or_else(|| {
            cause!(
                InternalError,
                "attempt to dereference unbound reference to {} in function constraint solver",
                self.key
            )
        })
    }

    /// Given a pointer to an alias block, returns a (mutable) reference to
    /// it.
    fn alias_ref<'a, 'b>(
        &'a self,
        alias_ptr: &'b metavars::alias::Reference,
    ) -> diagnostic::Result<std::cell::RefMut<'b, metavars::alias::Alias>> {
        alias_ptr.try_borrow_mut().map_err(|_| {
            cause!(
                FunctionRecursiveTypeExpression,
                "while dereferencing {}",
                self.key
            )
        })
    }

    /// Given a reference to the binding, returns a (mutable) reference to the
    /// alias block.
    pub fn alias<'a, 'b>(&'a self, binding: &'b std::cell::Ref<Option<metavars::alias::Reference>>) -> diagnostic::Result<std::cell::RefMut<'b, metavars::alias::Alias>> {
        self.alias_ref(self.alias_ptr(binding)?)
    }

    /// Given a reference to the alias block, returns a (mutable) reference
    /// to the data block.
    pub fn data(
        alias: &metavars::alias::Alias,
    ) -> diagnostic::Result<std::cell::RefMut<metavars::data::Data>> {
        alias.data.try_borrow_mut().map_err(|_| {
            cause!(
                FunctionRecursiveTypeExpression,
                "while dereferencing {}",
                alias.description
            )
        })
    }

    /// Adds an equality constraint between this metavariable and the other
    /// metavariable. This essentially just merges their data blocks. Both
    /// references must have been bound. Returns whether the any possible
    /// values are removed from the perspective of either reference. If no
    /// more values are possible, an error is returned.
    pub fn merge_with(&self, other: &Reference) -> diagnostic::Result<bool> {
        let a_binding = self.binding()?;
        let b_binding = other.binding()?;
        let a_alias = self.alias_ptr(&a_binding)?;
        let b_alias = other.alias_ptr(&b_binding)?;

        // If the references are equivalent, their values are already equal by
        // definition.
        if Rc::ptr_eq(&a_alias, &b_alias) {
            return Ok(false);
        }

        // Borrow the alias blocks.
        let a_alias = self.alias_ref(a_alias)?;
        let b_alias = other.alias_ref(b_alias)?;

        // If the references refer to the same data block already, their
        // values are already equal by definition.
        if Rc::ptr_eq(&a_alias.data, &b_alias.data) {
            return Ok(false);
        }

        // Borrow the data blocks mutably. We first clone the Rc so we can drop
        // the alias borrows; we need to do this, because we're about to borrow
        // them mutably to re-alias them to the combined data block.
        let a_data_ref = a_alias.data.clone();
        let b_data_ref = b_alias.data.clone();
        let mut a_data = a_data_ref.try_borrow_mut().map_err(|_| {
            cause!(
                FunctionRecursiveTypeExpression,
                "while dereferencing {}",
                a_alias.description
            )
        })?;

        // Ensure that we can borrow the data block for b without causing a
        // recursion error before calling merge_with(); it doesn't have the
        // information it needs to make a proper error message.
        drop(b_data_ref.try_borrow_mut().map_err(|_| {
            cause!(
                FunctionRecursiveTypeExpression,
                "while dereferencing {}",
                b_alias.description
            )
        })?);

        // Drop the borrows to the alias blocks before we do the merge.
        drop(a_alias);
        drop(b_alias);

        // Merge data block b into a.
        a_data.merge_with(&b_data_ref)
    }

    /// Constrains the value of the referred variable. Returns whether the new
    /// constraint reduced the number of possible values. If no more values are
    /// possible, an error is returned.
    pub fn constrain(&self, constraint: &metavalues::set::Set) -> diagnostic::Result<bool> {
        let binding = self.binding()?;
        let alias = self.alias(&binding)?;
        let mut data = Self::data(&alias)?;
        data.constrain(constraint)
    }

    /// If the set of possible values for this metavariable has been reduced to
    /// only one possibility, return it. Otherwise returns None.
    pub fn value(&self) -> diagnostic::Result<Option<metavalues::value::Value>> {
        let binding = self.binding()?;
        let alias = self.alias(&binding)?;
        let data = Self::data(&alias)?;
        data.value()
    }

    /// Returns whether this metavalue still has the given value as a
    /// possibility.
    pub fn matches(&self, value: &metavalues::value::Value) -> diagnostic::Result<bool> {
        let binding = self.binding()?;
        if let Some(alias) = binding.as_ref() {
            let alias = self.alias_ref(alias)?;
            let data = Self::data(&alias)?;
            data.matches(value)
        } else {
            Ok(true)
        }
    }

    /// Returns true when both references refer to the same data block due to
    /// an equality constraint or due to being the same reference.
    pub fn aliases(&self, other: &Reference) -> diagnostic::Result<bool> {
        let a_binding = self.binding()?;
        let b_binding = other.binding()?;
        let a_alias = self.alias_ptr(&a_binding)?;
        let b_alias = other.alias_ptr(&b_binding)?;
        if Rc::ptr_eq(&a_alias, &b_alias) {
            return Ok(true);
        }
        if Rc::ptr_eq(
            &self.alias_ref(a_alias)?.data,
            &other.alias_ref(b_alias)?.data,
        ) {
            return Ok(true);
        }
        Ok(false)
    }

    /// Returns whether this metavariable can be proven to have the same value
    /// as the other metavariable. This is true if both references alias the
    /// same variable, or if the values for both variables were resolved and
    /// these values are equal.
    pub fn value_equals(&self, other: &Reference) -> diagnostic::Result<bool> {
        if self.aliases(other)? {
            return Ok(true);
        }
        if let Some(self_value) = self.value()? {
            if let Some(other_value) = other.value()? {
                return Ok(self_value == other_value);
            }
        }
        Ok(false)
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
    pub fn covers(&self, other: &Reference) -> diagnostic::Result<Option<bool>> {
        // A value always covers itself, so if both references alias the same
        // value, covers will always return true, no matter which constraints
        // are added.
        if self.aliases(other)? {
            return Ok(Some(true));
        }

        let a_binding = self.binding()?;
        let b_binding = other.binding()?;
        let a_alias = self.alias(&a_binding)?;
        let b_alias = other.alias(&b_binding)?;
        let a_data = a_alias.data.borrow();
        let b_data = b_alias.data.borrow();
        a_data.covers(&b_data)
    }

    /// Returns whether the value of this metavariable could have the same
    /// value as the other metavariable.
    pub fn intersects_with(&self, other: &Reference) -> diagnostic::Result<bool> {
        // A value always intersects with itself.
        if self.aliases(other)? {
            return Ok(true);
        }

        let a_binding = self.binding()?;
        let b_binding = other.binding()?;
        let a_alias = self.alias(&a_binding)?;
        let b_alias = other.alias(&b_binding)?;
        let a_data = a_alias.data.borrow();
        let b_data = b_alias.data.borrow();
        a_data.intersects_with(&b_data)
    }
}
