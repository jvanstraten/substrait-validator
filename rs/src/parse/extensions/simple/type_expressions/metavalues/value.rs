use crate::output::data_type;
use std::sync::Arc;

/// A metatype, i.e. the type of a value that a generic can assume during the
/// constraint-solving process.
#[derive(Clone, Copy, Debug)]
pub enum Type {
    /// A boolean.
    Boolean,

    /// An integer.
    Integer,

    /// A concrete data type.
    DataType,
}

/// A metavalue, i.e. a fully-specified value of a metatype.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// A boolean.
    Boolean(bool),

    /// An integer.
    Integer(i64),

    /// A concrete data type.
    DataType(Arc<data_type::DataType>),
}

impl Value {
    /// Returns the metatype of this metavalue.
    pub fn metatype(&self) -> Type {
        match self {
            Value::Boolean(_) => Type::Boolean,
            Value::Integer(_) => Type::Integer,
            Value::DataType(_) => Type::DataType,
        }
    }

    /// If this is a boolean metavalue, return the value.
    pub fn as_boolean(&self) -> Option<bool> {
        if let Value::Boolean(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    /// If this is an integer metavalue, return the value.
    pub fn as_integer(&self) -> Option<i64> {
        if let Value::Integer(i) = self {
            Some(*i)
        } else {
            None
        }
    }

    /// If this is a data type metavalue, return the value.
    pub fn as_data_type_pattern(&self) -> Option<&Arc<data_type::DataType>> {
        if let Value::DataType(d) = self {
            Some(d)
        } else {
            None
        }
    }
}

impl From<bool> for Value {
    fn from(x: bool) -> Self {
        Value::Boolean(x)
    }
}

impl From<i64> for Value {
    fn from(x: i64) -> Self {
        Value::Integer(x)
    }
}

impl From<Arc<data_type::DataType>> for Value {
    fn from(x: Arc<data_type::DataType>) -> Self {
        Value::DataType(x)
    }
}
