use crate::output::data_type;
use crate::output::data_type::ParameterInfo;
use crate::output::diagnostic;
use crate::parse::extensions::simple::type_expressions::context;
use crate::parse::extensions::simple::type_expressions::metavalues;
use crate::parse::extensions::simple::type_expressions::metavars;
use crate::util;
use std::sync::Arc;

/// A pattern that matches some set of data types.
///
/// Types are printed/parsed in the following order:
///
///  - class;
///  - nullability;
///  - variation;
///  - parameter pack.
///
/// Intentionally convoluted example: `struct?x[?]<>` matches any variation of
/// an empty struct with nullability `x`.
///
/// When a data type pattern is successfully matched against a concrete type,
/// this may impose constraints on metavariables referenced in the pattern.
#[derive(Clone, Debug, PartialEq)]
pub struct Pattern {
    /// Type class (simple, compound, or user-defined).
    pub class: data_type::Class,

    /// Nullability. Must map to a boolean metavariable.
    ///  - None -> printed/parsed as `class??`.
    ///  - Some(metavar) -> printed/parsed as `class?metavar`.
    ///  - Some(resolved to true) -> printed/parsed as `class?`.
    ///  - Some(resolved to false) -> printed/parsed as `class`.
    pub nullable: Option<metavars::reference::Reference>,

    /// Type variation, if specified. Note that data_type::Variation is itself
    /// an option:
    ///  - None -> variation is unspecified; this parameterized type matches
    ///    any variation. Printed/parsed as `class[?]`.
    ///  - Some(None) -> this parameterized type is the base variation of
    ///    class. Printed as `class`, parsed as `class` or `class[]`.
    ///  - Some(Some(variation)) -> this parameterized type is the specified
    ///    variation of class. Printed/parsed as `class[variation]`.
    pub variation: Option<data_type::Variation>,

    /// Parameters for parameterized types. Must be set to Some([]) for
    /// non-parameterizable types.
    ///  - None -> parameters are unspecified. Any number of parameters can be
    ///    matched, within the constraints of class. Printed/parsed as `class`,
    ///    even if class requires parameters.
    ///  - Some([]) -> parameters are specified to be an empty list.
    ///    Printed/parsed as `class<>`
    ///  - Some([Some(a), Some(b), Some(c)]) -> printed/parsed as
    ///    `class<a, b, c>`.
    ///  - Some([Some(a), None]) -> printed as `class<a, ?>`.
    pub parameters: Option<Vec<Option<Parameter>>>,
}

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Class description.
        write!(f, "{}", self.class)?;

        // Nullable flag.
        if let Some(nullable) = &self.nullable {
            match nullable.value() {
                Ok(value) => {
                    match value
                        .as_ref()
                        .and_then(metavalues::value::Value::as_boolean)
                    {
                        Some(true) => write!(f, "?")?,
                        Some(false) => (),
                        None => write!(f, "?{}", nullable)?,
                    }
                }
                Err(_) => write!(f, "!")?,
            }
        } else {
            write!(f, "??")?;
        }

        // Variation.
        match &self.variation {
            Some(Some(variation)) => write!(f, "[{}]", variation)?,
            Some(None) => (),
            None => write!(f, "[?]")?,
        }

        // Parameter pack.
        if self.class.has_parameters() {
            if let Some(parameters) = &self.parameters {
                write!(f, "<")?;
                let mut first = true;
                for parameter in parameters.iter() {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    if let Some(parameter) = parameter {
                        write!(f, "{parameter}")?;
                    } else {
                        write!(f, "?")?;
                    }
                }
                write!(f, ">")?;
            }
        }

        Ok(())
    }
}

impl Pattern {
    /// Bind all metavariable references in this pattern to the given context.
    pub fn bind(&self, context: &mut context::solver::Solver) -> diagnostic::Result<()> {
        if let Some(nullable) = &self.nullable {
            nullable.bind(context)?;
        }
        if let Some(parameters) = &self.parameters {
            for parameter in parameters.iter() {
                if let Some(parameter) = parameter {
                    parameter.value.bind(context)?;
                }
            }
        }
        Ok(())
    }

    /// Returns whether the given concrete type matches this pattern. Parameter
    /// names are ignored in the comparison.
    pub fn matches(&self, concrete: &Arc<data_type::DataType>) -> diagnostic::Result<bool> {
        // Check class.
        if &self.class != concrete.class() {
            return Ok(false);
        }

        // Check nullability.
        if let Some(nullable) = &self.nullable {
            if let Some(nullable) = nullable
                .value()?
                .as_ref()
                .and_then(metavalues::value::Value::as_boolean)
            {
                if nullable != concrete.nullable() {
                    return Ok(false);
                }
            }
        }

        // Check variation.
        if let Some(variation) = &self.variation {
            if variation != concrete.variation() {
                return Ok(false);
            }
        }

        // Check parameter pack.
        if let Some(parameters) = &self.parameters {
            let concrete_parameters = concrete.parameters();
            if parameters.len() != concrete_parameters.len() {
                return Ok(false);
            }
            for (x, y) in parameters.iter().zip(concrete_parameters.iter()) {
                if let Some(x) = x {
                    if !x.matches(y) {
                        return Ok(false);
                    }
                }
            }
        }

        Ok(true)
    }

    /// Checks whether this pattern covers another, i.e. all types that
    /// match other also match this. This will only yield a result if all
    /// metavariables involved are sufficiently constrained; i.e., further
    /// constraining the possible values of metavariables will not affect
    /// the output once Some(_) is returned.
    pub fn covers(&self, other: &Pattern) -> diagnostic::Result<Option<bool>> {
        // Check class.
        if self.class != other.class {
            return Ok(Some(false));
        }

        // Check nullability.
        if let Some(self_nullable) = &self.nullable {
            if let Some(other_nullable) = &other.nullable {
                let covers = self_nullable.covers(other_nullable);
                if covers != Ok(Some(true)) {
                    return covers;
                }
            } else {
                return Ok(Some(false));
            }
        }

        // Check variation.
        if let Some(self_variation) = &self.variation {
            if let Some(other_variation) = &other.variation {
                if self_variation != other_variation {
                    return Ok(Some(false));
                }
            } else {
                return Ok(Some(false));
            }
        }

        // Check parameter pack.
        if let Some(self_parameters) = &self.parameters {
            if let Some(other_parameters) = &other.parameters {
                if self_parameters.len() != other_parameters.len() {
                    return Ok(Some(false));
                }
                for (self_parameter, other_parameter) in
                    self_parameters.iter().zip(other_parameters.iter())
                {
                    if let Some(self_parameter) = self_parameter {
                        if let Some(other_parameter) = other_parameter {
                            let covers = self_parameter.value.covers(&other_parameter.value);
                            if covers != Ok(Some(true)) {
                                return covers;
                            }
                        } else {
                            return Ok(Some(false));
                        }
                    }
                }
            } else {
                return Ok(Some(false));
            }
        }

        Ok(Some(true))
    }

    /// Checks whether this pattern has at least one concrete type in common
    /// with the other pattern.
    pub fn intersects_with(&self, other: &Pattern) -> diagnostic::Result<bool> {
        // Check class.
        if self.class != other.class {
            return Ok(false);
        }

        // Check nullability.
        if let Some(self_nullable) = &self.nullable {
            if let Some(other_nullable) = &other.nullable {
                if !self_nullable.intersects_with(other_nullable)? {
                    return Ok(false);
                }
            }
        }

        // Check variation.
        if let Some(self_variation) = &self.variation {
            if let Some(other_variation) = &other.variation {
                if self_variation != other_variation {
                    return Ok(false);
                }
            }
        }

        // Check parameter pack.
        if let Some(self_parameters) = &self.parameters {
            if let Some(other_parameters) = &other.parameters {
                if self_parameters.len() != other_parameters.len() {
                    return Ok(false);
                }
                for (a, b) in self_parameters.iter().zip(other_parameters.iter()) {
                    if let Some(a) = a {
                        if let Some(b) = b {
                            if !a.value.intersects_with(&b.value)? {
                                return Ok(false);
                            }
                        }
                    }
                }
            }
        }

        Ok(true)
    }

    /// Computes the intersection between this pattern and the other pattern.
    /// If this intersection cannot be represented with one pattern without
    /// creating a new metavariable, a superset is returned by leaving the
    /// position of that metavariable black. If there is no intersection, None
    /// is returned.
    pub fn intersect(&self, other: &Pattern) -> diagnostic::Result<Option<Pattern>> {
        // Check class.
        if self.class != other.class {
            return Ok(None);
        }
        let class = self.class.clone();

        // Check nullability.
        let nullable = match (&self.nullable, &other.nullable) {
            (None, None) => None,
            (None, Some(x)) => Some(x.clone()),
            (Some(x), None) => Some(x.clone()),
            (Some(x), Some(y)) => {
                if x.value_equals(y)? {
                    Some(x.clone())
                } else if x.intersects_with(y)? {
                    // Intersects, but cannot be represented!
                    None
                } else {
                    return Ok(None);
                }
            }
        };

        // Check variation.
        let variation = match (&self.variation, &other.variation) {
            (None, None) => None,
            (None, Some(x)) => Some(x.clone()),
            (Some(x), None) => Some(x.clone()),
            (Some(x), Some(y)) => {
                if x == y {
                    Some(x.clone())
                } else {
                    return Ok(None);
                }
            }
        };

        // Check parameter pack.
        let parameters = match (&self.parameters, &other.parameters) {
            (None, None) => None,
            (None, Some(x)) => Some(x.clone()),
            (Some(x), None) => Some(x.clone()),
            (Some(x), Some(y)) => {
                if x.len() == y.len() {
                    let mut parameters = Vec::with_capacity(x.len());
                    for (a, b) in x.iter().zip(y.iter()) {
                        parameters.push(match (a, b) {
                            (None, None) => None,
                            (None, Some(x)) => Some(x.clone()),
                            (Some(x), None) => Some(x.clone()),
                            (Some(x), Some(y)) => {
                                if x.value.value_equals(&y.value)? {
                                    Some(x.clone())
                                } else if x.value.intersects_with(&y.value)? {
                                    // Intersects, but cannot be represented!
                                    None
                                } else {
                                    return Ok(None);
                                }
                            }
                        });
                    }
                    Some(parameters)
                } else {
                    return Ok(None);
                }
            }
        };

        Ok(Some(Pattern {
            class,
            nullable,
            variation,
            parameters,
        }))
    }

    /// Computes the union of this pattern and the other pattern. If this union
    /// cannot be represented with a single pattern, a superset is returned.
    /// None is used to represent the set of all types.
    pub fn union(&self, other: &Pattern) -> diagnostic::Result<Option<Pattern>> {
        // Check class.
        if self.class != other.class {
            // The class is required in a pattern, so expand to all types.
            return Ok(None);
        }
        let class = self.class.clone();

        // Check nullability.
        let nullable = match (&self.nullable, &other.nullable) {
            (Some(x), Some(y)) => {
                if x.value_equals(y)? {
                    Some(x.clone())
                } else {
                    // Multiple values possible, expand to accept all values.
                    None
                }
            }
            (_, _) => None,
        };

        // Check variation.
        let variation = match (&self.variation, &other.variation) {
            (Some(x), Some(y)) => {
                if x == y {
                    Some(x.clone())
                } else {
                    // Multiple variations possible, expand to accept all
                    // variations.
                    None
                }
            }
            (_, _) => None,
        };

        // Check parameter pack.
        let parameters = match (&self.parameters, &other.parameters) {
            (Some(x), Some(y)) => {
                if x.len() == y.len() {
                    let mut parameters = Vec::with_capacity(x.len());
                    for (a, b) in x.iter().zip(y.iter()) {
                        parameters.push(match (a, b) {
                            (Some(x), Some(y)) => {
                                if x.value.value_equals(&y.value)? {
                                    Some(x.clone())
                                } else {
                                    // Multiple values possible, expand to
                                    // accept all values.
                                    None
                                }
                            }
                            (_, _) => None,
                        });
                    }
                    Some(parameters)
                } else {
                    // Multiple parameter counts possible, expand to accept all
                    // parameter packs.
                    None
                }
            }
            (_, _) => None,
        };

        Ok(Some(Pattern {
            class,
            nullable,
            variation,
            parameters,
        }))
    }

    /// Returns the concrete type associated with this pattern, if it is a
    /// concrete type.
    pub fn make_concrete(&self) -> diagnostic::Result<Option<Arc<data_type::DataType>>> {
        todo!();
    }
}

/// A parameter within a data type parameter pack.
///
/// Printed/parsed as:
///
///  - `name: value` for named parameters;
///  - `value` for non-named parameters.
#[derive(Clone, Debug)]
pub struct Parameter {
    /// Name of this parameter, if applicable (currently used only for
    /// NSTRUCT).
    pub name: Option<String>,

    /// The metavariable representing the value of this parameter.
    pub value: metavars::reference::Reference,
}

impl PartialEq for Parameter {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl std::fmt::Display for Parameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{}: ", util::string::as_ident_or_string(name))?;
        }
        write!(f, "{}", self.value)
    }
}

impl Parameter {
    /// Returns whether the given parameter value matches one of the remaining
    /// possible values for value. The parameter name is not checked.
    pub fn matches(&self, parameter: &data_type::Parameter) -> bool {
        match parameter {
            data_type::Parameter::Type(_) => todo!(),
            data_type::Parameter::NamedType(_, _) => todo!(),
            data_type::Parameter::Unsigned(_) => todo!(),
        }
    }
}
