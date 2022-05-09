// SPDX-License-Identifier: Apache-2.0

//! Module providing string parsing and management of type expressions.
//!
//! A note on nomenclature to avoid confusion with runtime values and data
//! types:
//!  - (concrete) data type: the type of a piece of runtime data. Fully
//!    specified a.k.a. concrete. Represented by [data_type::DataType].
//!  - data value: a value that a data type can have at runtime.
//!  - parameterized data type: a data type that may or may not be completely
//!    specified. This is an extension of (concrete) data types: in addition
//!    to concrete types like STRUCT<i32, i64> and STRUCT<>, this also supports
//!    data types like STRUCT and STRUCT<T>, and doesn't necessarily specify
//!    nullability. Represented by [ParameterizedDataType].
//!  - metatype: the type of a piece of data during constraint solving,
//!    including data types. Represented by [MetaType].
//!  - metavalue: a value that a metatype can have during constraint solving.
//!    Represented by [MetaValue].
//!  - generic: a named, unknown metavalue, for which the value must be solved
//!    via contextual information and constraints. Represented using strings
//!    within a [Context].
//!  - parameter type: the type of a function parameter. May or may not be
//!    concrete in the function specification, but will always be concrete once
//!    solving starts. Represented using integer argument indices within a
//!    [Context].
//!  - return type: the return type of a function. Not concrete when solving
//!    starts; it is the desired result of the solving process.
//!  - metavariable: something that is constrained to a certain set of
//!    metavalues, such as generics, parameter types, and return types.
//!    Represented by [MetaVariable] and referred to using
//!    [MetaVariableReference] within some [Context].
//!  - constraint: something that constrains a metavariable to a (smaller set
//!    of) value(s). Represented using [Constraint].
//!
//! We can now say, for example: the type of a data type is a metavalue of the
//! metatype "data type". Make sure you understand this sentence before trying
//! to make sense of this module; it doesn't get any easier :)

use crate::output::data_type;
use crate::output::data_type::ParameterInfo;
use crate::output::diagnostic;
use crate::string_util;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

/// A pattern that matches some set of data types.
///
/// Types are printed/parsed in the following order:
///
///  - class;
///  - nullability;
///  - variation;
///  - parameter pack.
///
/// Intentionally convoluted example: `struct?x[?]<>` matches any variation of
/// an empty struct with nullability `x`.
///
/// When a data type pattern is successfully matched against a concrete type,
/// this may impose constraints on metavariables referenced in the pattern.
#[derive(Clone, Debug)]
pub struct DataTypePattern {
    /// Type class (simple, compound, or user-defined).
    pub class: data_type::Class,

    /// Nullability. Must map to a boolean metavariable.
    ///  - generic -> printed/parsed as `class?generic`.
    ///  - anonymous -> printed/parsed as `class?_123`.
    ///  - resolved to true -> printed/parsed as `class?`.
    ///  - resolved to false -> printed/parsed as `class`.
    pub nullable: MetaVariableReference,

    /// Type variation, if specified. Note that data_type::Variation is itself
    /// an option:
    ///  - None -> variation is unspecified; this parameterized type matches
    ///    any variation. Printed/parsed as `class[?]`.
    ///  - Some(None) -> this parameterized type is the base variation of
    ///    class. Printed as `class`, parsed as `class` or `class[]`.
    ///  - Some(Some(variation)) -> this parameterized type is the specified
    ///    variation of class. Printed/parsed as `class[variation]`.
    pub variation: Option<data_type::Variation>,

    /// Parameters for parameterized types. Must be set to Some([]) for
    /// non-parameterizable types.
    ///  - None -> parameters are unspecified. Any number of parameters can be
    ///    matched, within the constraints of class. Printed/parsed as `class`,
    ///    even if class requires parameters.
    ///  - Some([]) -> parameters are specified to be an empty list.
    ///    Printed/parsed as `class<>`
    ///  - Some([a, b, c]) -> printed/parsed as `class<a, b, c>`.
    pub parameters: Option<Vec<DataTypeParameter>>,
}

impl std::fmt::Display for DataTypePattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Class description.
        write!(f, "{}", self.class)?;

        // Nullable flag.
        match self.nullable.value().as_ref().and_then(MetaValue::as_bool) {
            Some(true) => write!(f, "?")?,
            Some(false) => (),
            None => write!(f, "?{}", self.nullable)?,
        }

        // Variation.
        match &self.variation {
            Some(Some(variation)) => write!(f, "[{}]", variation)?,
            Some(None) => (),
            None => write!(f, "[?]")?,
        }

        // Parameter pack.
        if self.class.has_parameters() {
            if let Some(parameters) = &self.parameters {
                write!(f, "<")?;
                let mut first = true;
                for parameter in parameters.iter() {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{parameter}")?;
                }
                write!(f, ">")?;
            }
        }

        Ok(())
    }
}

impl DataTypePattern {
    /// Bind all metavariable references in this pattern to the given context.
    pub fn bind(&mut self, context: &mut Context) {
        self.nullable.bind(context);
        if let Some(parameters) = &mut self.parameters {
            for parameter in parameters.iter_mut() {
                parameter.value.bind(context);
            }
        }
    }

    /// Add constraints to all referenced metavariables based on the pattern:
    ///  - the metavariable used to specify nullability must be a boolean;
    ///  - metavariables used in the parameter pack must satisfy the
    ///    constraints imposed by the class;
    ///  - if the parameter pack has the wrong number of parameters for the
    ///    class, Err is returned;
    ///  - if a parameter has a name and the class does not support this or
    ///    vice versa, Err is returned.
    pub fn apply_static_constraints(&self) -> diagnostic::Result<()> {
        todo!();
    }

    /// Returns whether the given concrete type matches this pattern. Parameter
    /// names are ignored in the comparison.
    pub fn matches(&self, concrete: &Arc<data_type::DataType>) -> bool {
        // Check class.
        if &self.class != concrete.class() {
            return false;
        }

        // Check nullability.
        if let Some(nullable) = self.nullable.value().as_ref().and_then(MetaValue::as_bool) {
            if nullable != concrete.nullable() {
                return false;
            }
        }

        // Check variation.
        if let Some(variation) = &self.variation {
            if variation != concrete.variation() {
                return false;
            }
        }

        // Check parameter pack.
        if let Some(parameters) = &self.parameters {
            let concrete_parameters = concrete.parameters();
            if parameters.len() != concrete_parameters.len() {
                return false;
            }
            if parameters
                .iter()
                .zip(concrete_parameters.iter())
                .any(|(x, y)| !x.matches(y))
            {
                return false;
            }
        }

        return true;
    }

    /// Add constraints to all referenced parameters based on the given
    /// concrete type (effectively forcing the values of the metavariables)
    /// and copy the variation from the pattern.
    pub fn apply_match_constraints(
        &mut self,
        concrete: &Arc<data_type::DataType>,
    ) -> diagnostic::Result<()> {
        todo!();
    }

    /// Checks whether this pattern covers another, i.e. all types that
    /// match other also match this.
    pub fn covers(&self, other: &DataTypePattern) -> bool {
        todo!()
    }

    /// Returns the concrete type associated with this pattern, if it is a
    /// concrete type. An error is contained in the option if this is a
    /// concrete type but the type could not be constructed because it is
    /// invalid.
    pub fn make_concrete(&self) -> Option<diagnostic::Result<Arc<data_type::DataType>>> {
        todo!();
    }
}

/// A parameter within a data type parameter pack.
///
/// Printed/parsed as:
///
///  - `name: value` for named parameters;
///  - `value` for non-named parameters.
#[derive(Clone, Debug)]
pub struct DataTypeParameter {
    /// Name of this parameter, if applicable (currently used only for
    /// NSTRUCT).
    pub name: Option<String>,

    /// The metavariable representing the value of this parameter.
    pub value: MetaVariableReference,
}

impl std::fmt::Display for DataTypeParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{}: ", string_util::as_ident_or_string(name))?;
        }
        write!(f, "{}", self.value)
    }
}

impl DataTypeParameter {
    /// Returns whether the given parameter value matches one of the remaining
    /// possible values for value. The parameter name is not checked.
    pub fn matches(&self, parameter: &data_type::Parameter) -> bool {
        match parameter {
            data_type::Parameter::Type(_) => todo!(),
            data_type::Parameter::NamedType(_, _) => todo!(),
            data_type::Parameter::Unsigned(_) => todo!(),
        }
    }
}

/// Hashable type that, when constructed via Default, guarantees that no other
/// value of this type in the program is equal to the new value. Can however
/// be copied after constructions, to make multiple aliases to the same unique
/// value.
#[derive(Clone, Debug, Eq)]
pub struct Unique(Rc<()>);

impl Default for Unique {
    fn default() -> Self {
        Self(Rc::new(()))
    }
}

impl PartialEq for Unique {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl std::hash::Hash for Unique {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

/// An unresolved reference to a metavariable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum MetaVariableReferenceKey {
    /// A generic metavariable, case-insensitively identified by a string in
    /// type expressions. The string is stored in lowercase here.
    Generic(String),

    /// A reference to an inferred metavariable.
    Inferred(Unique),

    /// The type of the parameter with the given zero-based index.
    FunctionParameterType(usize),

    /// The return type.
    FunctionReturnType,
}

impl std::fmt::Display for MetaVariableReferenceKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MetaVariableReferenceKey::Generic(s) => write!(f, "{s}"),
            MetaVariableReferenceKey::Inferred(_) => write!(f, "_"),
            MetaVariableReferenceKey::FunctionParameterType(i) => write!(
                f,
                "type of {} parameter",
                string_util::describe_nth(*i as u32)
            ),
            MetaVariableReferenceKey::FunctionReturnType => write!(f, "return type"),
        }
    }
}

/// A reference to a metavariable.
#[derive(Clone, Debug)]
pub struct MetaVariableReference {
    /// The method through which the metavariable is referenced.
    key: MetaVariableReferenceKey,

    /// The raw parsed string that the user used to refer to the metavariable,
    /// if any. Used to keep track of the case/syntax convention that the user
    /// used, in order to produce better diagnostic messages. bind() moves this
    /// into the alias block.
    description: Option<Rc<String>>,

    /// Reference to the alias block for this metavariable. Initialized via
    /// bind().
    alias: Option<MetaVariableAliasReference>,
}

impl std::fmt::Display for MetaVariableReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Try to print the description from the alias block.
        if let Some(alias) = &self.alias {
            if let Ok(alias) = alias.try_borrow() {
                return write!(f, "{alias}");
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

impl MetaVariableReference {
    /// Creates an (unbound) named reference to a metavariable.
    pub fn new_generic<S: ToString>(name: S) -> Self {
        let name = name.to_string();
        let key = name.to_ascii_lowercase();
        MetaVariableReference {
            key: MetaVariableReferenceKey::Generic(key),
            description: Some(Rc::new(name)),
            alias: None,
        }
    }

    /// Creates a reference to a new, unique metavariable. The reference can be
    /// copied to refer to the same metavariable multiple times.
    pub fn new_inferred<S: ToString>(description: Option<S>) -> Self {
        MetaVariableReference {
            key: MetaVariableReferenceKey::Inferred(Unique::default()),
            description: description.map(|x| Rc::new(x.to_string())),
            alias: None,
        }
    }

    /// Creates a reference to the type of the index'th parameter of the
    /// function being solved for.
    pub fn new_function_parameter_type(index: usize) -> Self {
        MetaVariableReference {
            key: MetaVariableReferenceKey::FunctionParameterType(index),
            description: None,
            alias: None,
        }
    }

    /// Creates a reference to the return type of the function being solved
    /// for.
    pub fn new_function_return_type() -> Self {
        MetaVariableReference {
            key: MetaVariableReferenceKey::FunctionReturnType,
            description: None,
            alias: None,
        }
    }

    /// Bind this metavariable reference to the given context.
    pub fn bind(&mut self, context: &mut Context) {
        todo!()
    }

    /// Adds an equality constraint between this metavariable and the other
    /// metavariable. This essentially just merges their data blocks. Both
    /// references must have been bound.
    pub fn constrain_equal(&self, other: &MetaVariableReference) {
        let a_alias = self
            .alias
            .as_ref()
            .expect("attempt to constrain unbound metavariable reference");
        let b_alias = other
            .alias
            .as_ref()
            .expect("attempt to constrain unbound metavariable reference");

        // If the references are equivalent, their values are already equal by
        // definition.
        if Rc::ptr_eq(&a_alias, &b_alias) {
            return;
        }

        // Borrow the alias blocks.
        let a_alias = a_alias.borrow();
        let b_alias = b_alias.borrow();

        // If the references refer to the same data block already, their
        // values are already equal by definition.
        if Rc::ptr_eq(&a_alias.data, &b_alias.data) {
            return;
        }

        // Borrow the data blocks mutably. We first clone the Rc so we can drop
        // the alias borrows; we need to do this, because we're about to borrow
        // them mutably to re-alias them to the combined data block.
        let a_data_ref = a_alias.data.clone();
        let b_data_ref = b_alias.data.clone();
        let mut a_data = a_data_ref.borrow_mut();
        let mut b_data = b_data_ref.borrow_mut();

        // Drop the borrows to the alias blocks.
        drop(a_alias);
        drop(b_alias);

        // Copy stuff from the data block for b to the data block for a, such
        // that a becomes the combined data block for both. Remap aliases to
        // block b to block a instead, dropping expired weak references while
        // we're at it.
        a_data.aliases.extend(b_data.aliases.drain(..).filter(|x| {
            x.upgrade()
                .map(|x| x.borrow_mut().data = a_data_ref.clone())
                .is_some()
        }));
        a_data.constraints.extend(b_data.constraints.drain(..));

        // Reset the possible values for a. This ensures that when the
        // combined data block is updated later, the update call indicates that
        // solving progress was made.
        a_data.reset();
    }

    /// Constrains the value of the referred variable. The constraint is only
    /// added if no equivalent constraint exists yet.
    pub fn constrain(&self, constraint: Constraint) {
        let alias = self
            .alias
            .as_ref()
            .expect("attempt to constrain unbound metavariable reference")
            .borrow();
        let mut data = alias.data.borrow_mut();
        if !data.constraints.iter().any(|x| x == &constraint) {
            data.constraints.push(constraint);
        }
    }

    /// If the set of possible values for this metavariable has been reduced to
    /// only one possibility, return it. Otherwise returns None.
    pub fn value(&self) -> Option<MetaValue> {
        self.alias.as_ref().and_then(|alias| {
            let alias = alias.borrow();
            let data = alias.data.borrow();
            data.values.value()
        })
    }

    /// Returns whether this metavalue still has the given value as a
    /// possibility.
    pub fn matches(&self, value: &MetaValue) -> bool {
        if let Some(alias) = &self.alias {
            let alias = alias.borrow();
            let data = alias.data.borrow();
            data.values.contains(value)
        } else {
            true
        }
    }
}

/// Reference to a metavariable alias block.
type MetaVariableAliasReference = Rc<RefCell<MetaVariableAlias>>;

/// Weak reference to a metavariable alias block.
type MetaVariableAliasWeakReference = std::rc::Weak<RefCell<MetaVariableAlias>>;

/// An alias block for a metavariable. A (MetaVariableReferenceKey, Context)
/// pair map to exactly one alias instance.
#[derive(Clone, Debug)]
struct MetaVariableAlias {
    /// The best description we have for referring to this metavariable in
    /// diagnostics.
    description: String,

    /// Reference to the data block that holds the state of this variable.
    /// Different references may be aliases to the same data block.
    data: MetaVariableDataBlockReference,
}

impl std::fmt::Display for MetaVariableAlias {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description)
    }
}

impl MetaVariableAlias {}

/// Reference to the data block for a metavariable, holding its constraints
/// and remaining possible values.
type MetaVariableDataBlockReference = Rc<RefCell<MetaVariableDataBlock>>;

/// A data block for a metavariable. This holds the set of constraints imposed
/// on the variable, and caches the possible values that the variable may still
/// have.
#[derive(Clone, Debug)]
struct MetaVariableDataBlock {
    /// Weak references to all aliases that refer to this data block. For
    /// example, in fn(T) -> T, the return type, the first parameter, and
    /// generic T all refer to the same data block.
    aliases: Vec<MetaVariableAliasWeakReference>,

    /// The constraints on the value of this metavariable.
    constraints: Vec<Constraint>,

    /// The possible values remaining for this metavariable. Updated using
    /// update().
    values: MetaValueSet,
}

impl MetaVariableDataBlock {
    /// Resets the cached set of possible values remaining for this
    /// metavariable.
    pub fn reset(&mut self) {
        todo!();
    }

    /// Updates values based on constraints. Returns whether progress was made
    /// by excluding options that were previously allowed. Throws an error if
    /// the value is overconstrained (i.e. no options remain).
    pub fn update(&mut self) -> diagnostic::Result<bool> {
        todo!();
    }
}

/// Reference to a context.
pub type ContextReference = Rc<RefCell<Context>>;

#[derive(Clone, Debug)]
pub struct Context {
    // TODO
}

impl Context {
    // TODO
}

#[derive(Clone, Debug, PartialEq)]
pub struct Constraint {
    // TODO
}

#[derive(Clone, Debug)]
pub struct MetaValueSet {
    // TODO
}

impl MetaValueSet {
    /// If this set contains exactly one value, return it.
    pub fn value(&self) -> Option<MetaValue> {
        todo!()
    }

    /// Returns whether the set contains the given value.
    pub fn contains(&self, value: &MetaValue) -> bool {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct MetaValue {
    // TODO
}

impl MetaValue {
    /// If this is a boolean metavalue, return the value.
    pub fn as_bool(&self) -> Option<bool> {
        todo!()
    }

    /// If this is an integer metavalue, return the value.
    pub fn as_integer(&self) -> Option<i64> {
        todo!()
    }

    /// If this is a data type pattern metavalue, return the data type pattern.
    pub fn as_data_type_pattern(&self) -> Option<&DataTypePattern> {
        todo!()
    }

    /// If this is a data type pattern metavalue that maps to a single,
    /// concrete data type, return it.
    pub fn as_concrete_data_type(&self) -> Option<diagnostic::Result<Arc<data_type::DataType>>> {
        self.as_data_type_pattern().and_then(|x| x.make_concrete())
    }
}
