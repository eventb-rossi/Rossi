//! Context AST nodes
//!
//! Contexts define the static properties of Event-B models including
//! sets, constants, and axioms.

use super::{ClauseRegion, FileMetadata, LabeledPredicate, NamedElement, Span};

/// An Event-B Context component
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context {
    /// Name of the context
    pub name: String,

    /// Contexts that this context extends
    pub extends: Vec<String>,

    /// Carrier sets declared in this context
    pub sets: Vec<NamedElement>,

    /// Constants declared in this context
    pub constants: Vec<NamedElement>,

    /// Axioms (properties that must hold).
    /// Theorems are stored here with `is_theorem = true`.
    pub axioms: Vec<LabeledPredicate>,

    /// Source location of the entire context (CONTEXT name ... END)
    pub span: Option<Span>,

    /// Source location of the context name
    pub name_span: Option<Span>,

    /// Source regions of the context's clause sections (textual parse only),
    /// used by structural LSP features such as folding.
    pub clauses: Vec<ClauseRegion>,

    /// Comment from Rodin XML
    pub comment: Option<String>,

    /// File-level metadata from Rodin XML
    pub metadata: Option<FileMetadata>,
}

impl Context {
    /// Create a new context with the given name
    pub fn new(name: String) -> Self {
        Self {
            name,
            extends: Vec::new(),
            sets: Vec::new(),
            constants: Vec::new(),
            axioms: Vec::new(),
            span: None,
            name_span: None,
            clauses: Vec::new(),
            comment: None,
            metadata: None,
        }
    }
}
