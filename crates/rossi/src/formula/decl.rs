//! Bound-identifier declarations.

use std::sync::Arc;

use crate::ast::Span;

use super::expression::Expression;
use super::factory::FormulaFactory;
use super::hashing;
use super::types::Type;

/// The declaration of one bound identifier, attached to a quantifier
/// (or to the primed-identifier list of a such-that assignment).
///
/// The name is a printing hint and fresh-name seed: occurrences in the
/// quantifier's body refer to the declaration by de Bruijn index, never
/// by name. Consequently, two quantified formulas that differ only in
/// declaration names are equal (alpha-equivalence); the name does
/// participate in *standalone* declaration equality.
///
/// A declaration may carry a source type annotation (`x ⦂ T`, kept
/// verbatim for printing) and, once type-checked, its solved [`Type`].
#[derive(Debug, Clone)]
pub struct BoundIdentDecl(pub(super) Arc<DeclData>);

#[derive(Debug)]
pub(super) struct DeclData {
    pub(super) name: String,
    pub(super) annotation: Option<Expression>,
    pub(super) ty: Option<Type>,
    pub(super) span: Option<Span>,
    pub(super) hash: u64,
    pub(super) free_idents: Box<[String]>,
    pub(super) dangling: Box<[u32]>,
    pub(super) factory: FormulaFactory,
}

impl BoundIdentDecl {
    /// The declared name (a printing hint).
    pub fn name(&self) -> &str {
        &self.0.name
    }

    /// The source type annotation, if the declaration was written
    /// `name ⦂ T`.
    pub fn annotation(&self) -> Option<&Expression> {
        self.0.annotation.as_ref()
    }

    /// The solved type, once type-checked.
    pub fn ty(&self) -> Option<&Type> {
        self.0.ty.as_ref()
    }

    /// The source span, if the declaration came from source text.
    pub fn span(&self) -> Option<Span> {
        self.0.span
    }

    /// Whether the declaration carries a solved type.
    pub fn is_type_checked(&self) -> bool {
        self.0.ty.is_some()
    }

    /// The factory this declaration was built with.
    pub fn factory(&self) -> &FormulaFactory {
        &self.0.factory
    }

    /// Free-identifier names referenced by the declaration (through its
    /// annotation and the given sets of its solved type), sorted and
    /// deduplicated.
    pub fn free_identifiers(&self) -> &[String] {
        &self.0.free_idents
    }

    /// De Bruijn indices that escape this declaration (through its
    /// annotation, which is scoped to the *enclosing* binder context),
    /// sorted ascending.
    pub fn dangling_bound_indices(&self) -> &[u32] {
        &self.0.dangling
    }

    /// Equality up to renaming: compares solved types only. This is the
    /// comparison quantifiers use for their declaration lists, which is
    /// what makes alpha-equivalent formulas equal.
    pub(super) fn alpha_eq(&self, other: &BoundIdentDecl) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.ty == other.0.ty
    }
}

/// Standalone declaration equality: name and solved type; the
/// annotation and span are presentation details and do not participate.
impl PartialEq for BoundIdentDecl {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        self.0.name == other.0.name && self.0.ty == other.0.ty
    }
}

impl Eq for BoundIdentDecl {}

impl std::hash::Hash for BoundIdentDecl {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash);
    }
}

/// The cached structural hash of a declaration: its name.
pub(super) fn decl_hash(name: &str) -> u64 {
    hashing::hash_one(name)
}
