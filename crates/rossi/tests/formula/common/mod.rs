//! Shared builders for the formula behavior suite.
//!
//! Thin wrappers over the factory that default the span to `None`, so
//! tests read as formulas rather than plumbing.

use rossi::ast::Span;
use rossi::formula::tag::{QuantPredOp, RelationalOp};
use rossi::formula::{BoundIdentDecl, Expression, FormulaFactory, Predicate, Type};

/// The core-language factory every test builds with.
pub fn ff() -> FormulaFactory {
    FormulaFactory::default_factory()
}

/// A span for span-insensitivity tests.
pub fn span(start: usize, end: usize) -> Span {
    Span { start, end }
}

/// An untyped free identifier.
pub fn fid(name: &str) -> Expression {
    ff().free_identifier(name, None, None)
}

/// A typed free identifier.
pub fn fid_ty(name: &str, ty: Type) -> Expression {
    ff().free_identifier(name, None, Some(ty))
}

/// An untyped bound identifier.
pub fn bid(index: u32) -> Expression {
    ff().bound_identifier(index, None, None)
}

/// An integer literal.
pub fn int(value: i64) -> Expression {
    ff().integer_literal(value, None)
}

/// An untyped, unannotated declaration.
pub fn decl(name: &str) -> BoundIdentDecl {
    ff().bound_ident_decl(name, None, None, None)
}

/// A declaration with a solved type.
pub fn decl_ty(name: &str, ty: Type) -> BoundIdentDecl {
    ff().bound_ident_decl(name, None, None, Some(ty))
}

/// `left = right`.
pub fn eq_pred(left: Expression, right: Expression) -> Predicate {
    ff().relational_predicate(RelationalOp::Equal, left, right, None)
}

/// `∀ decls · pred`.
pub fn forall(decls: Vec<BoundIdentDecl>, pred: Predicate) -> Predicate {
    ff().quantified_predicate(QuantPredOp::Forall, decls, pred, None)
}
