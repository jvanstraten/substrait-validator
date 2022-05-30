use crate::output::diagnostic;
use crate::parse::extensions::simple::type_expressions::constraints;
use crate::parse::extensions::simple::type_expressions::context;
use crate::parse::extensions::simple::type_expressions::metavalues;
use crate::parse::extensions::simple::type_expressions::metavars;

/// The types of constraints that can be imposed on metavariables.
#[derive(Clone, Debug, PartialEq)]
pub enum ConstraintType {
    /// The value must be contained in this set. Among other things, this is
    /// used to add boolean/integer literals and data type patterns specified
    /// on the input to the system; each literal gets an anonymous metavar that
    /// is constrained to only a single value by means of one of these.
    /// However, user-specified bounds are represented using a OneOf
    /// constraint, as a single Set is not expressive enough to represent all
    /// combinations of data type patterns.
    Within(metavalues::set::Set),

    /// The value must equal the return value of the given function. A function
    /// constraint does the following things:
    ///  - once the overload is known, metatype constraints are imposed on the
    ///    argument variables and return variable;
    ///  - once all argument variables are resolved to a single value or (in
    ///    case of covers()) are marked complete, the return variable is
    ///    constrained to the result of the function.
    Function(
        constraints::function::Function,
        Vec<metavars::reference::Reference>,
    ),

    /// The value must equal the values of one of the given variables. This is
    /// also used for describing equality constraints, in which case the vector
    /// only has one entry. A oneof constraint can be applied in three
    /// different ways:
    ///  - if the vector only has one entry, an alias-based equality constraint
    ///    is imposed between the variables;
    ///  - if the options for the target variable no longer intersect with any
    ///    of the options for any of the oneof entries, the target variable is
    ///    marked as overconstrained;
    ///  - when all the oneof entries are marked as complete, the target
    ///    variable is constrained by the smallest representable superset of
    ///    all possible values of the oneof entries.
    OneOf(Vec<metavars::reference::Reference>),
}

/// A constraint on a metavariable.
#[derive(Clone, Debug, PartialEq)]
pub struct Constraint {
    /// The data for the constraint.
    pub data: ConstraintType,

    /// A human-readable reason for the existence of the constraint, used for
    /// error messages when there are conflicting constraints.
    pub reason: String,
}

impl Constraint {
    /// Bind all metavariable references in this constraint to the given
    /// context.
    pub fn bind(&mut self, context: &mut context::solver::Solver) -> diagnostic::Result<()> {
        match &mut self.data {
            ConstraintType::Within(x) => x.bind(context)?,
            ConstraintType::Function(_, x) => {
                for x in x.iter_mut() {
                    x.bind(context)?;
                }
            }
            ConstraintType::OneOf(x) => {
                for x in x.iter_mut() {
                    x.bind(context)?;
                }
            }
        }
        Ok(())
    }
}
