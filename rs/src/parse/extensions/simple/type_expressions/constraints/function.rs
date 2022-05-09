/// A (builtin) function used to resolve type expressions.
#[derive(Clone, Debug, PartialEq)]
pub enum Function {
    /// Error marker for unknown functions.
    Unresolved(String),

    /// Boolean inversion: !bool | not(bool) -> bool
    Not,

    /// Boolean and: bool and bool | and(bool, bool) -> bool
    And,

    /// Boolean or: bool or bool | or(bool, bool) -> bool
    Or,

    /// Integer negation: -int | negate(int) -> int
    Neg,

    /// Integer multiplication: int * int | multiply(int, int) -> int
    Mul,

    /// Integer division: int / int | divide(int, int) -> int
    Div,

    /// Integer addition: int + int | add(int, int) -> int
    Add,

    /// Integer subtraction: int - int | subtract(int, int) -> int
    Sub,

    /// Integer minimum: min(int, int) -> int
    Min,

    /// Integer maximum: max(int, int) -> int
    Max,

    /// Integer equality: int = int | equal(int, int) -> int
    Eq,

    /// Integer inequality: int != int -> bool
    Ne,

    /// Integer less than or equal: int <= int -> bool
    Le,

    /// Integer greater than or equal: int >= int -> bool
    Ge,

    /// Integer less than: int < int | less_than(int, int) -> bool
    Lt,

    /// Integer greater than: int > int | greater_than(int, int) -> bool
    Gt,

    /// Ternary: if bool then any1 else any1 | bool ? any1 : any1 -> any1
    Ternary,

    /// Type comparison (lhs is an ancestor of or is equal to rhs):
    /// covers(type, type) -> bool
    Covers,

    /// Takes no arguments. Resolves to true if any of the function arguments
    /// passed to the function call being solved for is nullable, or to false
    /// otherwise.
    AnyParametersNullable,
}
