use crate::output::diagnostic;
use crate::parse::extensions::simple::type_expressions::constraints;
use crate::parse::extensions::simple::type_expressions::context;
use crate::parse::extensions::simple::type_expressions::metavars;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Constraint solver context.
pub struct Solver {
    /// The set of constraints in the system.
    constraints: Vec<constraints::constraint::Constraint>,

    /// Map from metavariable key to the respective alias block within this
    /// context, used by the various bind() functions.
    alias_map: HashMap<metavars::key::Key, metavars::alias::Reference>,
}

impl Solver {
    /// Turns a system of constraints into a constraint solver to solve the
    /// system. This is the entry point for the binding logic.
    pub fn new(system: context::system::System) -> diagnostic::Result<Self> {
        let mut solver = Self {
            constraints: vec![],
            alias_map: HashMap::new(),
        };
        let mut constraints = system.constraints;
        for constraint in constraints.iter_mut() {
            constraint.bind(&mut solver)?;
        }
        solver.constraints = constraints;
        Ok(solver)
    }

    /// Resolves a reference to its alias block, and indirectly to its data
    /// block. If no alias or data block exists yet, one is created,
    /// initialized without any constrants placed upon it.
    pub fn resolve<F: FnOnce() -> String>(
        &mut self,
        key: &metavars::key::Key,
        describer: F,
    ) -> metavars::alias::Reference {
        self.alias_map
            .entry(key.clone())
            .or_insert_with(|| {
                let alias = Rc::new(RefCell::new(metavars::alias::Alias {
                    description: describer(),
                    data: Rc::default(),
                }));
                alias.borrow().data.borrow_mut().push_alias(&alias);
                alias
            })
            .clone()
    }
}
