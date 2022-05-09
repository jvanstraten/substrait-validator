// SPDX-License-Identifier: Apache-2.0

//! Module for representing sets of countable inner types using ranges.

/// A set of values from a countable type represented using ranges.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct IntegerSet<V: Ord + Clone + num_traits::bounds::Bounded> {
    /// The values for which set containment flips. For example, the flips
    /// [1, 4, 5, 6, 7] represent the ranges [1, 4), [5, 6), [7, MAX]. All
    /// values must be unique and must be stored in ascending order.
    flips: Vec<V>,
}

impl<V> std::fmt::Display for IntegerSet<V>
where
    V: Ord + Clone + num_traits::bounds::Bounded + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        let mut contained = false;
        for flip in self.flips.iter() {
            if first {
                if flip != &V::min_value() {
                    flip.fmt(f)?;
                }
                first = false;
            } else {
                if !contained {
                    write!(f, ", ");
                }
                flip.fmt(f)?;
            }
            contained = !contained;
            if contained {
                write!(f, "..");
            }
        }
        Ok(())
    }
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

    /// If this set contains a single value, this returns it.
    pub fn value(&self) -> Option<V> {
        if (self.flips.len() == 1 && self.flips[0] == V::max_value())
            || (self.flips.len() == 2 && self.flips[1] == self.flips[0].clone() + V::one())
        {
            Some(self.flips[0].clone())
        } else {
            None
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

    /// Returns a full integer set.
    pub fn new_full() -> Self {
        IntegerSet {
            flips: vec![V::min_value()],
        }
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
    pub fn subtract(&self, other: &IntegerSet<V>) -> IntegerSet<V> {
        Self::arbitrary(&[(self, 1), (other, -1)], |x| x > 0)
    }

    /// Computes the intersection between this set and the given other set.
    pub fn intersect(&self, other: &IntegerSet<V>) -> IntegerSet<V> {
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
