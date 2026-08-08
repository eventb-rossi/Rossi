//! Construction-time computation of the per-node identifier caches.
//!
//! Every node caches the free-identifier names and the dangling de
//! Bruijn indices of its subtree, merged bottom-up from its children.
//! A child scoped under `n` local declarations contributes its dangling
//! indices renumbered by `-n` (indices below `n` are bound locally and
//! dropped). Declarations contribute their own caches unrenumbered:
//! their annotations are scoped to the *enclosing* binder context.

use super::decl::BoundIdentDecl;
use super::expression::Expression;
use super::predicate::Predicate;

#[derive(Default)]
pub(super) struct CacheBuilder {
    free: Vec<String>,
    dangling: Vec<u32>,
}

impl CacheBuilder {
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// Adds one free-identifier name (leaf constructors).
    pub(super) fn add_free_name(&mut self, name: String) {
        self.free.push(name);
    }

    /// Adds one dangling de Bruijn index (leaf constructors).
    pub(super) fn add_dangling_index(&mut self, index: u32) {
        self.dangling.push(index);
    }

    pub(super) fn add_expr(&mut self, expr: &Expression) {
        self.free.extend_from_slice(&expr.0.free_idents);
        self.dangling.extend_from_slice(&expr.0.dangling);
    }

    pub(super) fn add_pred(&mut self, pred: &Predicate) {
        self.free.extend_from_slice(&pred.0.free_idents);
        self.dangling.extend_from_slice(&pred.0.dangling);
    }

    pub(super) fn add_decl(&mut self, decl: &BoundIdentDecl) {
        self.free.extend_from_slice(&decl.0.free_idents);
        self.dangling.extend_from_slice(&decl.0.dangling);
    }

    /// Adds a child scoped under `n_decls` local declarations: indices
    /// below `n_decls` are bound locally, the rest escape renumbered.
    pub(super) fn add_scoped_expr(&mut self, expr: &Expression, n_decls: usize) {
        self.free.extend_from_slice(&expr.0.free_idents);
        self.add_scoped_indices(&expr.0.dangling, n_decls);
    }

    /// Scoped variant of [`Self::add_pred`].
    pub(super) fn add_scoped_pred(&mut self, pred: &Predicate, n_decls: usize) {
        self.free.extend_from_slice(&pred.0.free_idents);
        self.add_scoped_indices(&pred.0.dangling, n_decls);
    }

    fn add_scoped_indices(&mut self, dangling: &[u32], n_decls: usize) {
        let n = n_decls as u32;
        self.dangling
            .extend(dangling.iter().filter(|i| **i >= n).map(|i| i - n));
    }

    pub(super) fn finish(mut self) -> (Box<[String]>, Box<[u32]>) {
        self.free.sort_unstable();
        self.free.dedup();
        self.dangling.sort_unstable();
        self.dangling.dedup();
        (self.free.into(), self.dangling.into())
    }
}
