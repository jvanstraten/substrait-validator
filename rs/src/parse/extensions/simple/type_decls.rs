// SPDX-License-Identifier: Apache-2.0

//! Module providing parse/validation functions for parsing YAML type
//! declarations.

use crate::input::yaml;
use crate::output::data_type;
use crate::output::diagnostic::Result;
use crate::parse::context;

/// Resolves a component of a type definition.
pub fn resolve_component(x: &str, y: &mut context::Context) -> Result<data_type::Class> {
    // Try to resolve as a user-defined type from the current file first.
    todo!()
}

/// Parse a type declaration.
pub fn parse_type(x: &yaml::Value, y: &mut context::Context) -> Result<()> {
    // Parse fields.
    let name = yaml_required_field!(x, y, "name", yaml_prim!(str))?.1;
    let structure = yaml_repeated_field!(x, y, "structure", yaml_prim!(str, resolve_component))?.1;

    // Describe node.
    if let Some(name) = &name {
        describe!(y, Misc, "Declares type {name}");
    } else {
        describe!(y, Misc, "Invalid type declaration");
    }
    Ok(())
}
