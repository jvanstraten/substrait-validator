use crate::parse::extensions::simple::type_expressions::metavars;
use std::cell::RefCell;
use std::rc::Rc;

/// An alias block for a metavariable. A (MetaVariableReferenceKey, Context)
/// pair map to exactly one alias instance.
#[derive(Clone, Debug)]
pub struct Alias {
    /// The best description we have for referring to this metavariable in
    /// diagnostics.
    pub description: String,

    /// Reference to the data block that holds the state of this variable.
    /// Different references may be aliases to the same data block.
    pub data: metavars::data::Reference,
}

impl std::fmt::Display for Alias {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description)
    }
}

/// Reference to a metavariable alias block.
pub type Reference = Rc<RefCell<Alias>>;

/// Weak reference to a metavariable alias block.
pub type Weak = std::rc::Weak<RefCell<Alias>>;
