use crate::output::data_type;
use crate::output::diagnostic;
use crate::parse::extensions::simple::type_expressions::context;
use crate::parse::extensions::simple::type_expressions::metavalues;
use crate::util;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

/// A set of boolean metavalues.
#[derive(Clone, Debug, PartialEq)]
pub enum Booleans {
    /// The set contains both true and false.
    All,

    /// The set contains only the given value.
    Some(bool),

    /// The set is empty.
    None,
}

impl Booleans {
    /// Returns the set containing all possible values.
    pub fn full() -> Self {
        Booleans::All
    }

    /// Returns the empty set.
    pub fn empty() -> Self {
        Booleans::None
    }

    /// Remove all values in the set that do not satisfy the given constraint.
    pub fn constrain(&mut self, constraint: &Booleans) -> bool {
        match (self.clone(), constraint) {
            (_, Booleans::All) => false,
            (Booleans::All, _) => {
                *self = constraint.clone();
                true
            }
            (Booleans::None, _) => false,
            (_, Booleans::None) => {
                *self = Booleans::None;
                true
            }
            (Booleans::Some(x), Booleans::Some(y)) => {
                if x != *y {
                    *self = Booleans::None;
                    true
                } else {
                    false
                }
            }
        }
    }

    /// Returns whether the set contains the given value.
    pub fn contains(&self, value: bool) -> bool {
        match self {
            Booleans::All => true,
            Booleans::Some(x) => x == &value,
            Booleans::None => false,
        }
    }

    /// Returns whether this is a superset of other.
    pub fn superset_of(&self, other: &Booleans) -> bool {
        match (self, other) {
            (Booleans::All, _) => true,
            (_, Booleans::All) => false,
            (_, Booleans::None) => true,
            (Booleans::None, _) => false,
            (Booleans::Some(x), Booleans::Some(y)) => x == y,
        }
    }

    /// Returns whether this set intersects with the other.
    pub fn intersects_with(&self, other: &Booleans) -> bool {
        match (self, other) {
            (Booleans::None, _) => false,
            (_, Booleans::None) => false,
            (Booleans::All, _) => true,
            (_, Booleans::All) => true,
            (Booleans::Some(x), Booleans::Some(y)) => x == y,
        }
    }

    /// Returns whether this is the empty set.
    pub fn is_empty(&self) -> bool {
        matches!(self, Booleans::None)
    }

    /// If this set contains exactly one value, return it.
    pub fn value(&self) -> Option<bool> {
        if let Booleans::Some(x) = self {
            Some(*x)
        } else {
            None
        }
    }
}

/// A set of integer metavalues.
#[derive(Clone, Debug, PartialEq)]
pub struct Integers(util::integer_set::IntegerSet<i64>);

impl Integers {
    /// Returns the set containing all possible values.
    pub fn full() -> Self {
        Self(util::integer_set::IntegerSet::new_full())
    }

    /// Returns the empty set.
    pub fn empty() -> Self {
        Self(util::integer_set::IntegerSet::default())
    }

    /// Remove all values in the set that do not satisfy the given constraint.
    pub fn constrain(&mut self, constraint: &Integers) -> bool {
        let new_set = self.0.intersect(&constraint.0);
        if new_set != self.0 {
            self.0 = new_set;
            true
        } else {
            false
        }
    }

    /// Returns whether the set contains the given value.
    pub fn contains(&self, value: i64) -> bool {
        self.0.contains(&value)
    }

    /// Returns whether this is a superset of other.
    pub fn superset_of(&self, other: &Integers) -> bool {
        other.0.subtract(&self.0).is_empty()
    }

    /// Returns whether this set intersects with the other.
    pub fn intersects_with(&self, other: &Integers) -> bool {
        !self.0.intersect(&other.0).is_empty()
    }

    /// Returns whether this is the empty set.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// If this set contains exactly one value, return it.
    pub fn value(&self) -> Option<i64> {
        self.0.value()
    }
}

/// Wraps a type pattern to provide equality and hash methods that also report
/// two patterns as equal when they only differ by referenced metavariables.
/// This is used to ensure that a set of data types cannot contain two patterns
/// like that, because that would make it extremely difficult to perform set
/// operations. For example, the set [Struct<T>, Struct<S>] cannot be
/// represented; it would need to be pessimistically expanded to Struct<_>.
/// Struct<[T, S]> would work, though, because it reduces to Struct<_> and
/// _ in [T, S]
#[derive(Clone, Debug)]
pub struct DistinctPattern(metavalues::data_type::Pattern);

impl std::ops::Deref for DistinctPattern {
    type Target = metavalues::data_type::Pattern;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialEq for DistinctPattern {
    fn eq(&self, other: &Self) -> bool {
        if self.class != other.class {
            return false;
        }
        if self.nullable.is_some() != other.nullable.is_some() {
            return false;
        }
        if self.variation != other.variation {
            return false;
        }
        if self.parameters.as_ref().map(|x| x.len()) != other.parameters.as_ref().map(|x| x.len()) {
            return false;
        }
        true
    }
}

impl Eq for DistinctPattern {}

impl std::hash::Hash for DistinctPattern {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.class.hash(state);
        self.nullable.is_some().hash(state);
        self.variation.hash(state);
        self.parameters.as_ref().map(|x| x.len()).hash(state);
    }
}

/// A set of data type metavalues.
#[derive(Clone, Debug, PartialEq)]
pub enum DataTypes {
    /// The set contains all data types.
    All,

    /// The set consists of all data types matched by at least one of these
    /// patterns. The patterns must be chosen such that any pair of patterns
    /// is distinghuished by at least one of the following features:
    ///  - class;
    ///  - variation;
    ///  - number of parameters.
    /// The hash and equality of DistinctPattern is chosen such that any two
    /// patterns that intersect while one does not cover the other have the
    /// same hash and are considered equal (because this can only happen via
    /// metavar references). Furthermore, patterns are indexed by their class;
    /// patterns with differing class can never intersect because the class
    /// portion of a type is mandatory, allowing most set operations to be
    /// optimized a bit.
    Some(HashMap<data_type::Class, HashSet<DistinctPattern>>),
}

impl DataTypes {
    /// Returns the set containing all possible values.
    pub fn full() -> Self {
        DataTypes::All
    }

    /// Returns the empty set.
    pub fn empty() -> Self {
        DataTypes::Some(HashMap::default())
    }

    /// Bind all metavariable references in this set to the given context.
    pub fn bind(&self, context: &mut context::solver::Solver) -> diagnostic::Result<()> {
        if let DataTypes::Some(patterns) = self {
            for patterns in patterns.values() {
                for pattern in patterns.iter() {
                    pattern.bind(context)?;
                }
            }
        }
        Ok(())
    }

    /// Adds the given pattern to the set. If the resulting set is not
    /// representable, a best-effort superset thereof is produced instead.
    pub fn add_pattern(
        &mut self,
        pattern: &metavalues::data_type::Pattern,
    ) -> diagnostic::Result<()> {
        if let DataTypes::Some(patterns) = self {
            let patterns = patterns.entry(pattern.class.clone()).or_default();

            // We must insert the incoming pattern into the set of patterns,
            // in such a way that there is no overlap between the patterns,
            // to satisfy the invariants related to the pattern list. So,
            // we need to loop over the existing patterns and check for
            // intersections. Whenever we find an intersection, we compute
            // the union of it and the incoming pattern, treat that as the
            // new incoming pattern, and remove the existing pattern that
            // intersected with it. The union operation isn't perfect,
            // however; it may return a bigger set than the true union.
            let mut carry = pattern.clone();
            loop {
                let mut remove = vec![];
                for existing in patterns.iter() {
                    if existing.intersects_with(&carry)? {
                        if let Some(new_carry) = existing.union(&carry)? {
                            carry = new_carry;
                            remove.push(existing.clone());
                        } else {
                            // This implies that the patterns involved have
                            // different type classes, which should never
                            // happen due to the class to patterns map. If it
                            // *could* happen, this would be the correct logic:
                            //
                            //   *self = DataTypes::All;
                            //   return Ok(());
                            return Err(cause!(
                                InternalError,
                                "invalid internal state of data type pattern set"
                            ));
                        }
                    }
                }
                if remove.is_empty() {
                    break;
                } else {
                    for pattern in remove.iter() {
                        assert!(patterns.remove(pattern));
                    }
                }
            }
            assert!(patterns.insert(DistinctPattern(carry)));
        }
        Ok(())
    }

    /// Remove all values in the set that do not satisfy the given constraint,
    /// and propagate constraints to the nullability and generic variables if
    /// applicable. If the resulting set is not representable, a best-effort
    /// superset thereof is produced instead; this superset should always be
    /// a subset or equal to both inputs, though. Returns whether the number
    /// of possibilities were reduced.
    pub fn constrain(&mut self, constraint: &DataTypes) -> diagnostic::Result<bool> {
        // Note: can't use a match(self, constraint) here because then we can't
        // do the *self = constraint.clone().
        if matches!(constraint, DataTypes::All) {
            Ok(false)
        } else if matches!(self, DataTypes::All) {
            *self = constraint.clone();
            Ok(true)
        } else if let (DataTypes::Some(target), DataTypes::Some(constraint)) = (self, constraint) {
            // intersect(union(X0, X1, ..., Xx), union(Y0, Y1, ..., Yy))
            // = union(intersect(X0, Y0), ... intersect(Xx, Yy)) for all pairs
            let mut result = DataTypes::empty();
            for (class, x) in target.iter() {
                if let Some(y) = constraint.get(class) {
                    for y in y.iter() {
                        for x in x.iter() {
                            if let Some(xy) = x.intersect(y)? {
                                result.add_pattern(&xy);
                            }
                        }
                    }
                }
            }
            if let DataTypes::Some(result) = result {
                if target != &result {
                    *target = result;
                    return Ok(true);
                }
            }
            Ok(false)
        } else {
            unreachable!();
        }
    }

    /// Returns whether the set contains the given value.
    pub fn contains(&self, value: &Arc<data_type::DataType>) -> diagnostic::Result<bool> {
        match self {
            DataTypes::All => Ok(true),
            DataTypes::Some(patterns) => {
                if let Some(patterns) = patterns.get(value.class()) {
                    for pattern in patterns.iter() {
                        if pattern.matches(&value)? {
                            return Ok(true);
                        }
                    }
                }
                Ok(false)
            }
        }
    }

    /// Returns whether this is a superset of other, taking the possible values
    /// of metavariables referred to by the patterns into consideration. If
    /// further constraints imposed on any metavariables might change the
    /// current result, or if the computation is too complex, Ok(None) is
    /// returned.
    pub fn superset_of(&self, other: &DataTypes) -> diagnostic::Result<Option<bool>> {
        match (self, other) {
            (DataTypes::All, _) => Ok(Some(true)),
            (_, DataTypes::All) => Ok(Some(false)),
            (DataTypes::Some(x), DataTypes::Some(y)) => {
                if y.is_empty() {
                    return Ok(Some(true));
                }
                if x.is_empty() {
                    return Ok(Some(false));
                }

                // All patterns in y must be covered by the union of patterns
                // in x. This is very difficult if x is not a single pattern!
                // For example, union(x) may "look like"
                // .-------.
                // |1 2 3 4|
                // |   .---'
                // |5 6|
                // '---'
                // as constructed from
                // .-------.
                // |1 2 3 4|
                // '-------'
                // and
                // .---.
                // |5 6|
                // '---'
                // for which it's difficult to prove that this covers
                // .---.
                // |1 2|
                // |   |
                // |5 6|
                // '---'
                // without having a way to construct all possible sets (rather
                // than just "rectangles"; where one dimension might be the
                // number of template parameters and the other might be the
                // variation) in one go. However, we can detect these cases by
                // also doing intersection checks, which are comparatively
                // easy; if any y intersects with more than one x the pattern
                // is too complicated and we return None. If solving the system
                // relies on this, this will simply yield a "failed to solve
                // system" diagnostic.
                let mut too_complex = false;
                for (class, y) in y.iter() {
                    if y.is_empty() {
                        continue;
                    }
                    if let Some(x) = x.get(class) {
                        for y in y.iter() {
                            let mut covered = false;
                            let mut num_intersections = 0;
                            for x in x.iter() {
                                if x.intersects_with(y)? {
                                    num_intersections += 1;
                                    match x.covers(y)? {
                                        Some(true) => {
                                            covered = true;
                                            break;
                                        }
                                        Some(false) => {
                                            continue;
                                        }
                                        None => {
                                            return Ok(None);
                                        }
                                    }
                                }
                            }
                            if !covered {
                                return Ok(Some(false));
                            }
                            if num_intersections > 1 {
                                too_complex = true;
                            }
                        }
                    } else {
                        return Ok(Some(false));
                    }
                }
                if too_complex {
                    Ok(None)
                } else {
                    Ok(Some(true))
                }
            }
        }
    }

    /// Returns whether this set intersects with the other. Note that further
    /// constraints imposed on either set can only ever flip this outcome from
    /// true to false.
    pub fn intersects_with(&self, other: &DataTypes) -> diagnostic::Result<bool> {
        match (self, other) {
            (DataTypes::All, _) => Ok(!other.is_empty()),
            (_, DataTypes::All) => Ok(!other.is_empty()),
            (DataTypes::Some(x), DataTypes::Some(y)) => {
                for (class, x) in x.iter() {
                    if let Some(y) = y.get(class) {
                        for x in x.iter() {
                            for y in y.iter() {
                                if x.intersects_with(y)? {
                                    return Ok(true);
                                }
                            }
                        }
                    }
                }
                Ok(false)
            }
        }
    }

    /// Returns whether this is the empty set.
    pub fn is_empty(&self) -> bool {
        match self {
            DataTypes::All => false,
            DataTypes::Some(x) => x.is_empty(),
        }
    }

    /// If this set contains exactly one value, return it.
    pub fn value(&self) -> diagnostic::Result<Option<Arc<data_type::DataType>>> {
        if let DataTypes::Some(patterns) = self {
            if patterns.len() == 1 {
                let patterns = patterns.values().next().unwrap();
                if patterns.len() == 1 {
                    return patterns.iter().next().unwrap().make_concrete();
                }
            }
        }
        Ok(None)
    }
}

/// A set of metavalues of any supported metatype.
#[derive(Clone, Debug, PartialEq)]
pub struct Set {
    /// The booleans contained in the set.
    booleans: Booleans,

    /// The integers contained in the set.
    integers: Integers,

    /// The data types contained in the set.
    data_types: DataTypes,
}

impl Set {
    /// Returns the set containing all possible values.
    pub fn full() -> Self {
        Self {
            booleans: Booleans::full(),
            integers: Integers::full(),
            data_types: DataTypes::full(),
        }
    }

    /// Returns the empty set.
    pub fn empty() -> Self {
        Self {
            booleans: Booleans::empty(),
            integers: Integers::empty(),
            data_types: DataTypes::empty(),
        }
    }

    /// Bind all metavariable references in this set to the given context.
    pub fn bind(&self, context: &mut context::solver::Solver) -> diagnostic::Result<()> {
        self.data_types.bind(context)
    }

    /// Remove all values in the set that do not satisfy the given constraint.
    pub fn constrain(&mut self, constraint: &Set) -> diagnostic::Result<bool> {
        // NOTE: we want the side effects of all three of these, even if they
        // return true. So don't use || directly!
        let mut modified = false;
        if self.booleans.constrain(&constraint.booleans) {
            modified = true;
        }
        if self.integers.constrain(&constraint.integers) {
            modified = true;
        }
        if self.data_types.constrain(&constraint.data_types)? {
            modified = true;
        }
        Ok(modified)
    }

    /// Returns whether the set contains the given value.
    pub fn contains(&self, value: &metavalues::value::Value) -> diagnostic::Result<bool> {
        match value {
            metavalues::value::Value::Boolean(b) => Ok(self.booleans.contains(*b)),
            metavalues::value::Value::Integer(i) => Ok(self.integers.contains(*i)),
            metavalues::value::Value::DataType(d) => self.data_types.contains(d),
        }
    }

    /// Returns whether this is a superset of other, if further constraints
    /// imposed on any metavariables referred to by any data type patterns
    /// can't be futher constrained to change the outcome.
    pub fn superset_of(&self, other: &Set) -> diagnostic::Result<Option<bool>> {
        let result = self.data_types.superset_of(&other.data_types);
        if result != Ok(Some(true)) {
            return result;
        }
        if !self.booleans.superset_of(&other.booleans) {
            return Ok(Some(false));
        }
        if !self.integers.superset_of(&other.integers) {
            return Ok(Some(false));
        }
        Ok(Some(true))
    }

    /// Returns whether this set intersects with the other. Note that further
    /// constraints imposed on either set can only ever flip this outcome from
    /// true to false.
    pub fn intersects_with(&self, other: &Set) -> diagnostic::Result<bool> {
        if self.booleans.intersects_with(&other.booleans) {
            return Ok(true);
        }
        if self.integers.intersects_with(&other.integers) {
            return Ok(true);
        }
        if self.data_types.intersects_with(&other.data_types)? {
            return Ok(true);
        }
        Ok(false)
    }

    /// Returns whether this is the empty set.
    pub fn is_empty(&self) -> bool {
        self.booleans.is_empty() && self.integers.is_empty() && self.data_types.is_empty()
    }

    /// If this set contains exactly one value, return it.
    pub fn value(&self) -> diagnostic::Result<Option<metavalues::value::Value>> {
        match (
            self.booleans.is_empty(),
            self.integers.is_empty(),
            self.data_types.is_empty(),
        ) {
            (false, true, true) => Ok(self.booleans.value().map(|x| x.into())),
            (true, false, true) => Ok(self.integers.value().map(|x| x.into())),
            (true, true, false) => self.data_types.value().map(|x| x.map(|x| x.into())),
            _ => Ok(None),
        }
    }
}

impl From<Booleans> for Set {
    fn from(x: Booleans) -> Self {
        Self {
            booleans: x,
            integers: Integers::empty(),
            data_types: DataTypes::empty(),
        }
    }
}

impl From<Integers> for Set {
    fn from(x: Integers) -> Self {
        Self {
            booleans: Booleans::empty(),
            integers: x,
            data_types: DataTypes::empty(),
        }
    }
}

impl From<DataTypes> for Set {
    fn from(x: DataTypes) -> Self {
        Self {
            booleans: Booleans::empty(),
            integers: Integers::empty(),
            data_types: x,
        }
    }
}
