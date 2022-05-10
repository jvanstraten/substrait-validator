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

    /// The value must equal the return value of the given function. Functions
    /// are only evaluated once all their arguments have been reduced to a
    /// single value, but metatype constraints can be placed on the arguments
    /// and the result/constrained metavar and the applicable overload(s).
    Function(
        constraints::function::Function,
        Vec<metavars::reference::Reference>,
    ),

    /// The value must equal the values of one of the given variables. This is
    /// also used for describing equality constraints, in which case the vector
    /// only has one entry.
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
    pub fn bind(&self, context: &mut context::solver::Solver) -> diagnostic::Result<()> {
        match &self.data {
            ConstraintType::Within(x) => x.bind(context)?,
            ConstraintType::Function(_, x) => {
                for x in x.iter() {
                    x.bind(context)?;
                }
            }
            ConstraintType::OneOf(x) => {
                for x in x.iter() {
                    x.bind(context)?;
                }
            }
        }
        Ok(())
    }
}
