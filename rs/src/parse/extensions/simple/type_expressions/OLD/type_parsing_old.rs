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
use crate::output::diagnostic;
use crate::string_util;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

/// A metatype, i.e. the type of a value that a generic can assume during the
/// constraint-solving process.
#[derive(Clone, Copy, Debug)]
pub enum MetaType {
    /// A data type.
    DataType,

    /// An integer.
    Integer,

    /// A boolean.
    Boolean,
}

/// A metavalue, i.e. a fully-specified value of a metatype.
#[derive(Clone, Debug)]
pub enum MetaValue {
    /// A data type.
    DataType(data_type::DataType),

    /// An integer.
    Integer(i64),

    /// A boolean.
    Boolean(bool),
}

impl MetaValue {
    /// Returns the metatype of this metavalue.
    pub fn metatype(&self) -> MetaType {
        match self {
            MetaValue::DataType(_) => MetaType::DataType,
            MetaValue::Integer(_) => MetaType::Integer,
            MetaValue::Boolean(_) => MetaType::Boolean,
        }
    }
}

/// A reference to a metavariable. The context maps this to a description, a
/// set of constraints, and a set of (additional) aliases for that
/// metavariable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum MetaVariableReferenceKey {
    /// A generic metavariable, case-insensitively identified by a string in
    /// type expressions. The string is stored in lowercase here.
    Generic(String),

    /// The type of the parameter with the given zero-based index.
    ParameterType(usize),

    /// The return type.
    ReturnType,

    /// A inferred reference to a metavariable. Used for the (intermediate)
    /// results of expressions and literals. The usize is used to guarantee
    /// uniqueness, while the string is used as a human-readable description
    /// of the reference.
    Anonymous(usize),
}

impl std::fmt::Display for MetaVariableReferenceKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MetaVariableReferenceKey::Generic(s) => write!(f, "{}", s),
            MetaVariableReferenceKey::ParameterType(i) => write!(
                f,
                "type of {} parameter",
                string_util::describe_nth(*i as u32)
            ),
            MetaVariableReferenceKey::ReturnType => write!(f, "return type"),
            MetaVariableReferenceKey::Anonymous(_) => write!(f, "(anonymous)"),
        }
    }
}

/// An opaque reference to a metavariable returned by the context.
#[derive(Clone, Debug)]
pub struct MetaVariableReference {
    /// The key used to internally refer to the variable within the context.
    key: MetaVariableReferenceKey,

    /// Description, if a better one than just the string representation of the
    /// key was known by the context.
    description: Option<Rc<String>>,
}

impl PartialEq for MetaVariableReference {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl std::fmt::Display for MetaVariableReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(description) = &self.description {
            write!(f, "{}", description)
        } else {
            write!(f, "{}", self.key)
        }
    }
}

/// A data type, which may or may not be concrete/completely specified.
#[derive(Clone, Debug)]
struct ParameterizedDataType {
    /// Type class (simple, compound, or user-defined).
    pub class: data_type::Class,

    /// Nullability, if specified.
    pub nullable: Option<Rc<MetaVariableReferenceKey>>,

    /// Type variation, if specified.
    pub variation: Option<data_type::Variation>,

    /// Type parameters for non-simple types. None is used to signify that both
    /// the types and the number of parameters are unbound.
    pub parameters: Option<Vec<MetaVariableReferenceKey>>,
}

impl ParameterizedDataType {
    /// Returns whether this type "covers" the other type. This is true when
    /// all possible options for the other type are also possible options for
    /// this type.
    pub fn covers(&self, other: &ParameterizedDataType, context: &Context) -> bool {
        /*
        // Check class.
        // FIXME: should for example i16 cover i8? Currently it doesn't.
        if self.class != other.class {
            return false;
        }

        // Check variation.
        // FIXME: should the base variation cover derived types with transparent
        // function behavior? Currently it doesn't.
        match (self.variation, other.variation) {
            (None, _) => (),
            (Some(_), None) => return false,
            (Some(self_variation), Some(other_variation)) => {
                if self_variation != other_variation {more
        let self_nullable = self.nullable.and_then(context.possible_values_for).unwrap_or(&all_booleans);
        let other_nullable = other.nullable.and_then(context.possible_values_for).unwrap_or(&all_booleans);
        if !self_nullable.contains_all(other_nullable) {
            return false;
        }
        match (self.parameters, other.parameters) {
            (None, _) => (),
            (Some(_), None) => return false,
            (Some(self_parameters), Some(other_parameters)) => {
                if self_parameters.len() != other_parameters.len() {
                    return false;
                }
                for (self_parameter, other_parameter) in self_parameters.iter().zip(other_parameters.iter()) {
                    //let all_values = self.class.;
                    let self_parameter = context.possible_values_for(self_parameter).unwrap_or(&all_values);
                    let other_parameter = context.possible_values_for(other_parameter).unwrap_or(&all_values);
                    if !self_parameter.contains_all(other_parameter) {
                        return false;
                    }
                }
            }
        }*/
        return true;
    }
}

/// A (builtin) function used to resolve type expressions.
#[derive(Clone, Debug)]
pub enum MetaFunction {
    /// Error marker for unknown functions.
    Unresolved(String),

    /// Boolean inversion: !bool | not(bool) -> bool
    Not,

    /// Boolean and: bool and bool | and(bool, bool) -> bool
    And,

    /// Boolean or: bool or bool | or(bool, bool) -> bool
    Or,

    /// Integer negation: -int | negate(int) -> int
    Neg,

    /// Integer multiplication: int * int | multiply(int, int) -> int
    Mul,

    /// Integer division: int / int | divide(int, int) -> int
    Div,

    /// Integer addition: int + int | add(int, int) -> int
    Add,

    /// Integer subtraction: int - int | subtract(int, int) -> int
    Sub,

    /// Integer minimum: min(int, int) -> int
    Min,

    /// Integer maximum: max(int, int) -> int
    Max,

    /// Integer equality: int = int | equal(int, int) -> int
    Eq,

    /// Integer inequality: int != int -> bool
    Ne,

    /// Integer less than or equal: int <= int -> bool
    Le,

    /// Integer greater than or equal: int >= int -> bool
    Ge,

    /// Integer less than: int < int | less_than(int, int) -> bool
    Lt,

    /// Integer greater than: int > int | greater_than(int, int) -> bool
    Gt,

    /// Ternary: if bool then any1 else any1 | bool ? any1 : any1 -> any1
    Ternary,

    /// Type comparison (lhs is an ancestor of or is equal to rhs):
    /// covers(type, type) -> bool
    Covers,

    /// Takes no arguments. Resolves to true if any of the function arguments
    /// passed to the function call being solved for is nullable, or to false
    /// otherwise.
    AnyParametersNullable,
}

/// A set of integers described by inclusive ranges.
#[derive(Clone, Debug, Default)]
pub struct IntegerSet<V: Ord + Clone + num_traits::bounds::Bounded> {
    /// The values for which set containment flips. For example, the flips
    /// [1, 4, 5, 6, 7] represent the ranges [1, 4), [5, 6), [7, MAX]. All
    /// values must be unique and must be stored in ascending order.
    flips: Vec<V>,
}

impl<V> IntegerSet<V>
where
    V: Ord
        + Clone
        + num_traits::bounds::Bounded
        + std::ops::Add<Output = V>
        + num_traits::identities::One,
{
    /// Returns an integer set containing only the given value.
    pub fn new_single(value: V) -> Self {
        IntegerSet {
            flips: if value != V::max_value() {
                vec![value.clone(), value + V::one()]
            } else {
                vec![value]
            },
        }
    }
}

impl<V> IntegerSet<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded,
{
    /// Returns an empty integer set.
    pub fn new() -> Self {
        IntegerSet { flips: vec![] }
    }

    /// Returns whether the given value is contained in the set.
    pub fn contains(&self, value: &V) -> bool {
        // Find the index of the value or, if the value is not contained in the
        // list of flips, the index of the flip before it. The parity of that
        // index indicates whether the value is contained in the set.
        let index = match self.flips.binary_search(value) {
            Ok(x) => x,
            Err(x) => x - 1,
        };
        index & 1 == 1
    }

    /// Returns whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.flips.is_empty()
    }

    /// Performs an arbitrary set operation by combining the given sets into a
    /// single set using the given operation. Whether a value v is in the
    /// resulting set is functionally determined as follows (though the
    /// implementation is more efficient):
    ///  - each input set is assigned a weight (the i32 associated with it);
    ///  - for each value v, the weights if the input sets it is contained in
    /// is summed;
    ///  - v is in the resulting set iff operation(sum_of_weights) yields true.
    pub fn arbitrary<F: Fn(i32) -> bool>(
        sets: &[(&IntegerSet<V>, i32)],
        operation: F,
    ) -> IntegerSet<V> {
        let sets = sets
            .iter()
            .map(|(s, w)| (&s.flips[..], *w))
            .collect::<Vec<_>>();
        let flips = set_operation(&sets, operation);
        IntegerSet { flips }
    }

    /// Computes the union of this set and the given other set.
    pub fn union(&self, other: &IntegerSet<V>) -> IntegerSet<V> {
        Self::arbitrary(&[(self, 1), (other, 1)], |x| x > 0)
    }

    /// Computes the difference between this set and the given other set.
    pub fn difference(&self, other: &IntegerSet<V>) -> IntegerSet<V> {
        Self::arbitrary(&[(self, 1), (other, -1)], |x| x > 0)
    }

    /// Computes the intersection between this set and the given other set.
    pub fn intersection(&self, other: &IntegerSet<V>) -> IntegerSet<V> {
        Self::arbitrary(&[(self, 1), (other, 1)], |x| x > 1)
    }
}

impl<V> From<std::ops::Range<V>> for IntegerSet<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded,
{
    fn from(range: std::ops::Range<V>) -> Self {
        IntegerSet {
            flips: if range.end > range.start {
                vec![range.start, range.end]
            } else {
                vec![]
            },
        }
    }
}

impl<V> From<std::ops::RangeInclusive<V>> for IntegerSet<V>
where
    V: Ord
        + Clone
        + num_traits::bounds::Bounded
        + std::ops::Add<Output = V>
        + num_traits::identities::One,
{
    fn from(range: std::ops::RangeInclusive<V>) -> Self {
        IntegerSet {
            flips: if range.end() != &V::max_value() && range.end() >= range.start() {
                vec![range.start().clone(), range.end().clone() + V::one()]
            } else {
                vec![range.start().clone()]
            },
        }
    }
}

impl<V> From<std::ops::RangeFrom<V>> for IntegerSet<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded,
{
    fn from(range: std::ops::RangeFrom<V>) -> Self {
        IntegerSet {
            flips: vec![range.start],
        }
    }
}

impl<V> From<std::ops::RangeTo<V>> for IntegerSet<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded,
{
    fn from(range: std::ops::RangeTo<V>) -> Self {
        IntegerSet {
            flips: if range.end > V::min_value() {
                vec![V::min_value(), range.end]
            } else {
                vec![]
            },
        }
    }
}

impl<V> From<std::ops::RangeToInclusive<V>> for IntegerSet<V>
where
    V: Ord
        + Clone
        + num_traits::bounds::Bounded
        + std::ops::Add<Output = V>
        + num_traits::identities::One,
{
    fn from(range: std::ops::RangeToInclusive<V>) -> Self {
        IntegerSet {
            flips: if range.end != V::max_value() {
                vec![V::min_value(), range.end + V::one()]
            } else {
                vec![V::min_value()]
            },
        }
    }
}

impl<V> From<std::ops::RangeFull> for IntegerSet<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded,
{
    fn from(range: std::ops::RangeFull) -> Self {
        IntegerSet {
            flips: vec![V::min_value()],
        }
    }
}

/// Combines the given sets of ranges of V into a single set of ranges of V
/// using the given operation. Whether a value v is in the resulting set is
/// functionally determined as follows (though the implementation is more
/// efficient):
///  - each input set is assigned a weight (the i32 associated with it);
///  - for each value v, the weights if the input sets it is contained in is
///    summed;
///  - v is in the resulting set iff operation(sum_of_weights).
///
/// The sets are represented as sorted unique integers representing the values
/// where set containment flips. For example, [1, 4, 5, 6, 7] represents
/// [1, 4), [5, 6), [7, MAX]. All values must be unique and must be stored in
/// ascending order.
///
/// Examples:
///  - union/or: set_operation(&[(a, 1), (b, 1)], |w| w > 0)
///  - difference: set_operation(&[(a, 1), (b, -1)], |w| w > 0)
///  - intersection/and: set_operation(&[(a, 1), (b, 1)], |w| w > 1)
///  - xor: set_operation(&[(a, 1), (b, 1)], |w| w & 1 == 1)
///  - invert/not: set_operation(&[(a, 1)], |w| w == 0)
///  - empty set: set_operation(&[], |w| w != 0)
///  - complete set: set_operation(&[], |w| w == 0)
fn set_operation<V, F>(sets: &[(&[V], i32)], operation: F) -> Vec<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded,
    F: Fn(i32) -> bool,
{
    // Make an iterator for each input set that yields
    // (value, weight_delta) pairs. This allows us to merge the iterators
    // together while accumulating the weights we encounter to get
    // (value, weight) pairs.
    let mut sets = sets
        .into_iter()
        .map(|(set, weight)| {
            let weight = *weight;
            set.iter()
                .enumerate()
                .map(move |(i, v)| (v.clone(), if i & 1 == 1 { weight } else { -weight }))
                .peekable()
        })
        .collect::<Vec<_>>();

    // The resulting set.
    let mut result = vec![];

    // Whether the latest entry we pushed into result opens or closes a
    // range.
    let mut in_set = false;

    // Weight accumulator.
    let mut weight = 0;

    // Iterating over the merged input set iterators will only yield values
    // where the weight (may) change. If none of the input sets include the
    // minimum value of V and we would only iterate over them, that means
    // we'd never have a change to include V::MIN, even if operation(0)
    // yields true. This option is used to always check V::MIN as well.
    let mut first = Some(V::min_value());

    // Find the next value that we need to compute the weight for.
    while let Some(value) = first.take().or_else(|| {
        sets.iter_mut()
            .filter_map(|s| s.peek().map(|(v, _)| v))
            .min()
            .cloned()
    }) {
        // Take from all iterators that will return exactly value, and
        // accumulate the weights associated with them.
        weight += sets
            .iter_mut()
            .filter_map(|s| s.next_if(|(v2, _)| v2 == &value).map(|(_, w)| w))
            .sum::<i32>();

        // Determine whether the new weight corresponds to values that
        // should be contained in the resulting set.
        let new_in_set = operation(weight);

        // If the set containment flips, push the value in the resulting
        // set.
        if new_in_set != in_set {
            in_set = new_in_set;
            result.push(value);
        }
    }
    result
}

/// A set of data types.
#[derive(Clone, Debug)]
enum DataTypeSet {
    /// Empty set.
    None,

    /// The specified data types are in the set.
    Some(Vec<ParameterizedDataType>),

    /// All possible data types are in the set.
    All,
}

impl DataTypeSet {}

/// A set of metavalues, stored efficiently.
#[derive(Clone, Debug)]
pub struct MetaValueSet {
    /// The set of contained data types.
    data_types: DataTypeSet,

    /// The set of contained integers.
    integers: IntegerSet<i64>,

    /// Whether boolean true is in the set.
    bool_true: bool,

    /// Whether boolean false is in the set.
    bool_false: bool,
}

/// The types of constraints that can be imposed on metavariables.
#[derive(Clone, Debug)]
pub enum ConstraintType {
    /// The value must be contained in this set.
    Within(MetaValueSet),

    /// The value must equal the return value of the given function.
    Function(MetaFunction, Vec<Rc<MetaVariableReferenceKey>>),
}

/// A constraint on a metavariable.
#[derive(Clone, Debug)]
pub struct Constraint {
    /// The data for the constraint.
    pub data: ConstraintType,

    /// A human-readable reason for the existence of the constraint, used for
    /// error messages when there are conflicting constraints.
    pub reason: String,
}

/// A metavariable and its constraints.
#[derive(Clone, Debug)]
struct MetaVariable {
    /// The aliases for this metavariable. For example, in fn(T) -> T, the
    /// return type, the first parameter, and generic T all refer to the same
    /// MetaVariable.
    pub aliases: Vec<MetaVariableReferenceKey>,

    /// The constraints on the value of this metavariable.
    pub constraints: Vec<Constraint>,

    /// The possible values remaining for this metavariable.
    pub values: MetaValueSet,
}

impl MetaVariable {
    /// Returns Some(value) if and only if this metavariable maps to a single
    /// value.
    pub fn get_value(&self) -> Option<&MetaValue> {
        if self.constraints.len() == 1 {
            if let ConstraintType::Exactly(value) = &self.constraints[0].data {
                return Some(value);
            }
        }
        None
    }
}

/// Metavariable constraint solver context.
#[derive(Clone, Debug)]
pub struct Context {
    /// The variables that we're solving for.
    variables: HashMap<usize, MetaVariable>,

    /// Maps references to indices in the variables HashMap.
    reference_map: HashMap<MetaVariableReferenceKey, usize>,

    /// Maps references to human-readable descriptions, insofar that a better
    /// description than just the generated string representation of the
    /// reference key is available.
    descriptions: HashMap<MetaVariableReferenceKey, Rc<String>>,

    /// Counter for generating unique variable indices.
    variable_counter: usize,

    /// Counter for generating unique anonymous reference indices.
    anonymous_reference_counter: usize,
}

impl Context {
    /// Makes a reference to a new, unique metavariable.
    pub fn anonymous<S: ToString>(&mut self, description: S) -> MetaVariableReference {
        let index = self.anonymous_reference_counter;
        self.anonymous_reference_counter += 1;
        let key = MetaVariableReferenceKey::Anonymous(index);
        let description = Rc::new(description.to_string());
        self.descriptions.insert(key.clone(), description.clone());
        MetaVariableReference {
            key,
            description: Some(description),
        }
    }

    /// Makes a reference to the given generic.
    pub fn generic<S: ToString>(&mut self, identifier: S) -> MetaVariableReference {
        let identifier = identifier.to_string();

        // Parameters are matched case-insensitively, so we use the identifier
        // in lowercase for the key. However, we use the user's case convention
        // for the description. If the user is inconsistent in their case, the
        // case of the first instance is used.
        let identifier_lower = identifier.to_ascii_lowercase();
        let key = MetaVariableReferenceKey::Generic(identifier_lower);

        let description = self
            .descriptions
            .entry(key.clone())
            .or_insert_with(|| Rc::new(identifier))
            .clone();
        MetaVariableReference {
            key,
            description: Some(description),
        }
    }

    /// Makes a reference to the type of the parameter with the given index.
    pub fn parameter_type(&self, index: usize) -> MetaVariableReference {
        self.key_to_reference(&MetaVariableReferenceKey::ParameterType(index))
    }

    /// Makes a reference to the return type of the function.
    pub fn return_type(&self) -> MetaVariableReference {
        self.key_to_reference(&MetaVariableReferenceKey::ReturnType)
    }

    /// Resolves the description of the given reference key to form a complete
    /// reference.
    fn key_to_reference(&self, key: &MetaVariableReferenceKey) -> MetaVariableReference {
        let description = self.descriptions.get(key).cloned();
        MetaVariableReference {
            key: key.clone(),
            description,
        }
    }

    /// Sets the description of the parameter types based on the parameter names.
    pub fn set_parameter_names<S: std::fmt::Display>(&mut self, names: &[S]) {
        for (index, name) in names.iter().enumerate() {
            self.descriptions.insert(
                MetaVariableReferenceKey::ParameterType(index),
                Rc::new(format!("type of {}", name)),
            );
        }
    }

    /// Resolves a reference to its constraints.
    pub fn resolve_reference(&mut self, reference: &MetaVariableReference) -> &[Constraint] {
        &self.resolve_reference_key(&reference.key)[..]
    }

    /// Resolves a reference to its constraints.
    fn resolve_reference_key(
        &mut self,
        reference: &MetaVariableReferenceKey,
    ) -> &mut Vec<Constraint> {
        match self.reference_map.get(reference) {
            Some(x) => {
                &mut self
                    .variables
                    .get_mut(x)
                    .expect("missing variable, inconsistent context")
                    .constraints
            }
            None => {
                let index = self.variable_counter;
                self.variable_counter += 1;
                self.reference_map.insert(reference.clone(), index);
                &mut self
                    .variables
                    .entry(index)
                    .or_insert_with(|| MetaVariable {
                        aliases: vec![reference.clone()],
                        constraints: vec![],
                    })
                    .constraints
            }
        }
    }

    /// Impose the given constraint on the given variable. If the variable
    /// doesn't exist yet, it is created.
    pub fn constrain(&mut self, reference: &MetaVariableReference, constraint: Constraint) {
        self.constrain_key(&reference.key, constraint);
    }

    /// Impose the given constraint on the given variable. If the variable
    /// doesn't exist yet, it is created.
    fn constrain_key(&mut self, reference: &MetaVariableReferenceKey, constraint: Constraint) {
        self.resolve_reference_key(reference).push(constraint);
    }

    /// Assert that the given two metavariables must have the same value.
    pub fn equate(&mut self, a: &MetaVariableReference, b: &MetaVariableReference) {
        self.equate_key(&a.key, &b.key);
    }

    /// Assert that the given two metavariables must have the same value.
    fn equate_key(&mut self, a: &MetaVariableReferenceKey, b: &MetaVariableReferenceKey) {
        // This constraint is always met if the references are equal.
        if a == b {
            return;
        }
        match (
            self.reference_map.get(a).cloned(),
            self.reference_map.get(b).cloned(),
        ) {
            (Some(av), Some(bv)) => {
                // The constraint is always met if both references already
                // refer to the same variable.
                if av == bv {
                    return;
                }

                // Remove b from the variable list. It will be merged into a.
                let source = self
                    .variables
                    .remove(&bv)
                    .expect("missing variable, inconsistent context");

                // Re-alias all aliases for b to a.
                for alias in source.aliases.iter() {
                    self.reference_map.insert(alias.clone(), av);
                }

                // Constrain a by whatever the constraints on b were.
                self.variables
                    .get_mut(&av)
                    .expect("missing variable, inconsistent context")
                    .constraints
                    .extend(source.constraints);
            }
            (Some(av), None) => {
                // No variable exist for b yet, so we just have to alias b to a.
                self.variables
                    .get_mut(&av)
                    .expect("missing variable, inconsistent context")
                    .aliases
                    .push(b.clone());
                self.reference_map.insert(b.clone(), av);
            }
            (None, Some(bv)) => {
                // No variable exist for a yet, so we just have to alias a to b.
                self.variables
                    .get_mut(&bv)
                    .expect("missing variable, inconsistent context")
                    .aliases
                    .push(a.clone());
                self.reference_map.insert(a.clone(), bv);
            }
            (None, None) => {
                // No variable exist for either yet, so we need to make one.
                let v = self.variable_counter;
                self.variable_counter += 1;
                self.variables.insert(
                    v,
                    MetaVariable {
                        aliases: vec![a.clone(), b.clone()],
                        constraints: vec![],
                    },
                );
                self.reference_map.insert(a.clone(), v);
                self.reference_map.insert(b.clone(), v);
            }
        }
    }

    /// Copy the constraints on source to dest, without asserting that source
    /// and dest are exactly equal.
    pub fn copy_constraints(
        &mut self,
        source: &MetaVariableReference,
        dest: &MetaVariableReference,
    ) {
        self.copy_constraints_key(&source.key, &dest.key);
    }

    /// Copy the constraints on source to dest, without asserting that source
    /// and dest are exactly equal.
    fn copy_constraints_key(
        &mut self,
        source: &MetaVariableReferenceKey,
        dest: &MetaVariableReferenceKey,
    ) {
        let constraints = self.resolve_reference_key(source).clone();
        self.resolve_reference_key(dest).extend(constraints);
    }

    /// Attempts to reduce the given set of constraints. Returns Err if the
    /// given set of constraints is overconstrained, Ok(None) if no reduction
    /// could be performed, or Ok(Some(constraints)) if the constraint set
    /// was successfully reduced.
    fn reduce(
        &mut self,
        constraints: Vec<Constraint>,
    ) -> diagnostic::Result<Option<Vec<Constraint>>> {
        /*let mut new_constraints_a;
        let mut new_constraints_b;
        let mut reduced = false;
        for new in constraints {
            let mut new = Some(new);
            for old in new_constraints_a.drain(..) {
                match (old, new) {

                }
            }
        }

        Ok(if reduced {
            Some(new_constraints)
        } else {
            None
        })*/
        todo!()
    }

    /// Solve constraints until all metavariables are resolved to a single
    /// value.
    pub fn solve(&mut self, allow_underconstrained: bool) -> diagnostic::Result<()> {
        /*
        // Add constraints to variables based on how they are used. First of
        // all, function parameter and return types must be data types.
        for variable in self.variables.values_mut() {
            if variable.aliases.iter().any(|x| matches!(x, MetaVariableReferenceKey::ParameterType(_) | MetaVariableReferenceKey::ReturnType)) {
                variable.constraints.push(Constraint {
                    data: ConstraintType::MetaTypeSet(vec![MetaType::DataType]),
                    reason: String::from("function parameter/return types must be data types"),
                })
            }
        }


        // Attempt to solve the constraints iteratively.
        loop {

            // For each iteration, loop over all variables and reduce their
            // constraints one by one. Terminate if we stop making progress,
            // or once all constraints were reduced to a single Exactly.
            // Note that we need to make a copy of the indices because
            // variables could be added or removed by the solving process.
            let mut made_progress = false;
            let indices = self.variables.keys().collect::<Vec<_>>();
            for index in indices.into_iter() {
                if let Some(constraints) = self.variables.get(index).map(|x| x.constraints.clone()) {
                    if let Some(constraints) = self.reduce(constraints)? {
                        made_progress = true;
                        self.variables.get_mut(index).expect("variable removed while reducing").constraints = constraints;
                    }
                }
            }

            // Terminate if we failed to reduce the set of possible metavalues
            // for any metavariable.
            if !made_progress {
                break;
            }
        }

        // Return an underconstrained error if the constraints for any variable
        // were not reduced to a single Exactly, unless allow_underconstrained
        // was passed.
        if !allow_underconstrained {
            for variable in self.variables.values() {
                if variable.get_value().is_none() {
                    // TODO: better error message here... Describe the variable
                    // that failed to solve and its remaining options.
                    return Err(cause!(TypeUnderconstrained, "failed to solve"));
                }
            }
        }
        Ok(())
        */
        todo!()
    }
}

/// The types of function parameters.
#[derive(Clone, Debug)]
pub enum FunctionParameterType {
    /// Used for value arguments. The type of said value argument is
    /// constrained using a metavariable.
    Value,

    /// Used for type arguments. The type is constrained using a
    /// metavariable.
    Type,

    /// Used for required enumerations.
    RequiredEnum(Vec<String>),

    /// Used for optional enumerations.
    OptionalEnum(Vec<String>),
}

/// A function parameter.
#[derive(Clone, Debug)]
pub struct FunctionParameter {
    /// The user-specified name of the argument.
    name: String,

    /// The type of the argument.
    argument_type: FunctionParameterType,
}

/// The variadic behavior of the last argument of a function.
#[derive(Clone, Copy, Debug)]
pub enum FunctionVariadicity {
    /// The last argument in the prototype can match up to this many
    /// *additional* value arguments of the exact same type. Effectively, the
    /// metavariables representing the types of the additional arguments are
    /// treated as aliases for the type of the argument specified in the
    /// prototype. This variant is also used for functions that aren't
    /// varadic.
    Consistent,

    /// The last argument in the prototype can match up to this many
    /// *additional* value arguments, that need not be the exact same type.
    /// Effectively, the metavariables representing the types of the additional
    /// arguments are cloned (along with their constraints, if any) from the
    /// argument specified in the prototype.
    Inconsistent,
}

/// The prototype of a function.
#[derive(Clone, Debug)]
pub struct FunctionPrototype {
    /// The initial context that the solvers for particular usages of this
    /// function are derived from. This includes all the constraints specified
    /// in the prototype, but is free from constraints imposed by any usage of
    /// the function.
    pub context: Context,

    /// The number of specified arguments and their argument types.
    pub parameters: FunctionParameter,

    /// Maximum number of additional arguments that may be passed, derived from
    /// the last parameter by means of variadicity. This is simply set to zero
    /// for functions that are not variadic, or to usize::MAX for functions
    /// with no limit on the number of arguments.
    pub max_additional_arguments: usize,

    /// How the contraints on the additional arguments are derived.
    pub variadicity: FunctionVariadicity,
}
