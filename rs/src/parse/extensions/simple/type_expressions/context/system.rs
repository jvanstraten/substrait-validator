use crate::parse::extensions::simple::type_expressions::constraints;

/// A system of constraints.
#[derive(Debug, Clone, Default)]
pub struct System {
    pub constraints: Vec<constraints::constraint::Constraint>,
}
