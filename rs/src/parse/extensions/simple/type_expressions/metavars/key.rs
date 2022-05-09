use crate::util;
use std::rc::Rc;

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
pub enum Key {
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

impl std::fmt::Display for Key {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Key::Generic(s) => write!(f, "{s}"),
            Key::Inferred(_) => write!(f, "_"),
            Key::FunctionParameterType(i) => write!(
                f,
                "type of {} parameter",
                util::string::describe_nth(*i as u32)
            ),
            Key::FunctionReturnType => write!(f, "return type"),
        }
    }
}
