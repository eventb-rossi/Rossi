//! Substitutions: rewriters that respect binding depth.
//!
//! Every substitution here is an ordinary [`FormulaRewriter`] driven by
//! the shared post-order driver. Each tracks the current binding depth
//! through the quantifier hooks; indices below the depth are locally
//! bound and untouched, indices at or above it are the substitution's
//! to renumber or replace. Replacement expressions carrying dangling
//! indices are shifted by the insertion depth (memoized per depth).

use std::collections::HashMap;

use super::decl::BoundIdentDecl;
use super::expression::{Expression, ExpressionKind};
use super::predicate::{Predicate, PredicateKind};
use super::rewrite::{FormulaRewriter, rewrite_pred};

impl Expression {
    /// Renumbers every dangling index by `offset`. Panics if a shifted
    /// index would fall below zero.
    pub fn shift_bound_identifiers(&self, offset: i32) -> Expression {
        if offset == 0 || self.dangling_bound_indices().is_empty() {
            return self.clone();
        }
        self.rewrite(&mut Shifter { offset, depth: 0 })
    }

    /// Replaces free identifiers by expressions. Replacements carrying
    /// dangling indices are shifted to their insertion depth.
    pub fn substitute_free_idents(&self, map: &HashMap<String, Expression>) -> Expression {
        self.rewrite(&mut FreeSubst::new(map))
    }

    /// Turns the named free identifiers into bound identifiers, ready
    /// to be put under a binder declaring them in the given order: the
    /// last name gets index 0. Existing dangling indices are shifted by
    /// the number of names.
    pub fn bind_idents(&self, names: &[&str]) -> Expression {
        self.rewrite(&mut Binder::new(names))
    }
}

impl Predicate {
    /// See [`Expression::shift_bound_identifiers`].
    pub fn shift_bound_identifiers(&self, offset: i32) -> Predicate {
        if offset == 0 || self.dangling_bound_indices().is_empty() {
            return self.clone();
        }
        self.rewrite(&mut Shifter { offset, depth: 0 })
    }

    /// See [`Expression::substitute_free_idents`].
    pub fn substitute_free_idents(&self, map: &HashMap<String, Expression>) -> Predicate {
        self.rewrite(&mut FreeSubst::new(map))
    }

    /// See [`Expression::bind_idents`].
    pub fn bind_idents(&self, names: &[&str]) -> Predicate {
        self.rewrite(&mut Binder::new(names))
    }

    /// Instantiates declarations of this quantified predicate:
    /// `replacements[i]` replaces the i-th declaration, `None` keeps
    /// it. Kept declarations are renumbered; if none remain, the
    /// quantifier disappears. Panics if this is not a quantified
    /// predicate or the lengths differ.
    #[track_caller]
    pub fn instantiate(&self, replacements: &[Option<Expression>]) -> Predicate {
        let PredicateKind::Quantified { op, decls, pred } = self.kind() else {
            panic!("instantiate applies to a quantified predicate");
        };
        assert_eq!(
            decls.len(),
            replacements.len(),
            "one replacement slot per declaration"
        );
        let n = decls.len();
        // Declaration position i corresponds to root index n-1-i.
        let keep: Vec<bool> = replacements.iter().map(Option::is_none).collect();
        let kept: Vec<BoundIdentDecl> = decls
            .iter()
            .zip(&keep)
            .filter(|(_, keep)| **keep)
            .map(|(d, _)| d.clone())
            .collect();
        let mapping = kept_index_mapping(&keep);
        let mut subst = DeclSubst {
            n: n as u32,
            kept_count: kept.len() as u32,
            mapping,
            replacements: replacements
                .iter()
                .rev()
                .map(|r| r.clone().map(Substituted::new))
                .collect(),
            depth: 0,
        };
        let body = rewrite_pred(pred, &mut subst);
        if kept.is_empty() {
            body
        } else {
            self.factory()
                .clone()
                .quantified_predicate(*op, kept, body, self.span())
        }
    }
}

/// Root-index → new-index mapping for the kept declarations.
/// `keep[i]` speaks about declaration position i; root index r maps to
/// position n-1-r. Kept roots are numbered ascending from 0.
fn kept_index_mapping(keep: &[bool]) -> Vec<Option<u32>> {
    let n = keep.len();
    let mut next = 0;
    (0..n)
        .map(|root| {
            keep[n - 1 - root].then(|| {
                let index = next;
                next += 1;
                index
            })
        })
        .collect()
}

/// Drops the declarations the body no longer references, renumbering
/// the survivors. `None` if every declaration is used.
pub(super) fn remove_unused_decls(
    decls: &[BoundIdentDecl],
    body: &Predicate,
) -> Option<(Vec<BoundIdentDecl>, Predicate)> {
    let n = decls.len();
    let mut keep = vec![false; n];
    for index in body.dangling_bound_indices() {
        if (*index as usize) < n {
            keep[n - 1 - *index as usize] = true;
        }
    }
    if keep.iter().all(|k| *k) {
        return None;
    }
    let kept: Vec<BoundIdentDecl> = decls
        .iter()
        .zip(&keep)
        .filter(|(_, keep)| **keep)
        .map(|(d, _)| d.clone())
        .collect();
    let mut subst = DeclSubst {
        n: n as u32,
        kept_count: kept.len() as u32,
        mapping: kept_index_mapping(&keep),
        replacements: vec![None; n],
        depth: 0,
    };
    let body = rewrite_pred(body, &mut subst);
    Some((kept, body))
}

/// Renumbers dangling indices by a constant offset.
struct Shifter {
    offset: i32,
    depth: u32,
}

impl FormulaRewriter for Shifter {
    fn entering_quantifier(&mut self, n_decls: usize) {
        self.depth += n_decls as u32;
    }

    fn leaving_quantifier(&mut self, n_decls: usize) {
        self.depth -= n_decls as u32;
    }

    fn rewrite_expression(&mut self, expr: &Expression) -> Expression {
        let ExpressionKind::BoundIdentifier(index) = expr.kind() else {
            return expr.clone();
        };
        if *index < self.depth {
            return expr.clone();
        }
        let shifted = i64::from(*index) + i64::from(self.offset);
        assert!(
            shifted >= i64::from(self.depth),
            "shift would capture a dangling identifier"
        );
        expr.factory()
            .clone()
            .bound_identifier(shifted as u32, expr.span(), expr.ty().cloned())
    }
}

/// A replacement expression with its per-depth shifted variants
/// memoized.
#[derive(Clone)]
struct Substituted {
    base: Expression,
    by_depth: Vec<Option<Expression>>,
}

impl Substituted {
    fn new(base: Expression) -> Self {
        Substituted {
            base,
            by_depth: Vec::new(),
        }
    }

    fn at_depth(&mut self, depth: u32) -> Expression {
        if depth == 0 || self.base.dangling_bound_indices().is_empty() {
            return self.base.clone();
        }
        let slot = depth as usize;
        if self.by_depth.len() <= slot {
            self.by_depth.resize(slot + 1, None);
        }
        self.by_depth[slot]
            .get_or_insert_with(|| self.base.shift_bound_identifiers(depth as i32))
            .clone()
    }
}

/// Free-identifier substitution.
struct FreeSubst {
    map: HashMap<String, Substituted>,
    depth: u32,
}

impl FreeSubst {
    fn new(map: &HashMap<String, Expression>) -> Self {
        FreeSubst {
            map: map
                .iter()
                .map(|(name, expr)| (name.clone(), Substituted::new(expr.clone())))
                .collect(),
            depth: 0,
        }
    }
}

impl FormulaRewriter for FreeSubst {
    fn entering_quantifier(&mut self, n_decls: usize) {
        self.depth += n_decls as u32;
    }

    fn leaving_quantifier(&mut self, n_decls: usize) {
        self.depth -= n_decls as u32;
    }

    fn rewrite_expression(&mut self, expr: &Expression) -> Expression {
        let ExpressionKind::FreeIdentifier(name) = expr.kind() else {
            return expr.clone();
        };
        let depth = self.depth;
        match self.map.get_mut(name) {
            Some(substituted) => substituted.at_depth(depth),
            None => expr.clone(),
        }
    }
}

/// Binds named free identifiers as de Bruijn indices.
struct Binder<'a> {
    /// Name → declaration position (0-based, in declaration order).
    positions: HashMap<&'a str, u32>,
    count: u32,
    depth: u32,
}

impl<'a> Binder<'a> {
    fn new(names: &[&'a str]) -> Self {
        let positions: HashMap<&str, u32> = names
            .iter()
            .enumerate()
            .map(|(j, name)| (*name, j as u32))
            .collect();
        assert_eq!(
            positions.len(),
            names.len(),
            "names to bind must be distinct"
        );
        Binder {
            count: names.len() as u32,
            positions,
            depth: 0,
        }
    }
}

impl FormulaRewriter for Binder<'_> {
    fn entering_quantifier(&mut self, n_decls: usize) {
        self.depth += n_decls as u32;
    }

    fn leaving_quantifier(&mut self, n_decls: usize) {
        self.depth -= n_decls as u32;
    }

    fn rewrite_expression(&mut self, expr: &Expression) -> Expression {
        match expr.kind() {
            ExpressionKind::FreeIdentifier(name) => {
                let Some(position) = self.positions.get(name.as_str()) else {
                    return expr.clone();
                };
                expr.factory().clone().bound_identifier(
                    self.depth + (self.count - 1 - position),
                    expr.span(),
                    expr.ty().cloned(),
                )
            }
            ExpressionKind::BoundIdentifier(index) if *index >= self.depth => expr
                .factory()
                .clone()
                .bound_identifier(index + self.count, expr.span(), expr.ty().cloned()),
            _ => expr.clone(),
        }
    }
}

/// Declaration-list substitution: replaces or renumbers root indices.
/// Shared by instantiation and unused-declaration removal.
/// `replacements` and `mapping` are indexed by root index.
struct DeclSubst {
    n: u32,
    kept_count: u32,
    mapping: Vec<Option<u32>>,
    replacements: Vec<Option<Substituted>>,
    depth: u32,
}

impl FormulaRewriter for DeclSubst {
    fn entering_quantifier(&mut self, n_decls: usize) {
        self.depth += n_decls as u32;
    }

    fn leaving_quantifier(&mut self, n_decls: usize) {
        self.depth -= n_decls as u32;
    }

    fn rewrite_expression(&mut self, expr: &Expression) -> Expression {
        let ExpressionKind::BoundIdentifier(index) = expr.kind() else {
            return expr.clone();
        };
        if *index < self.depth {
            return expr.clone();
        }
        let root = index - self.depth;
        if root < self.n {
            let root = root as usize;
            if let Some(substituted) = &mut self.replacements[root] {
                // The replacement lands under this substitution's kept
                // declarations plus the local binders.
                return substituted.at_depth(self.depth + self.kept_count);
            }
            let new_index = self.mapping[root].expect("an unreplaced declaration must be kept");
            return expr.factory().clone().bound_identifier(
                new_index + self.depth,
                expr.span(),
                expr.ty().cloned(),
            );
        }
        // Externally bound: renumbered by the net declaration loss.
        let new_index = index - self.n + self.kept_count;
        if new_index == *index {
            return expr.clone();
        }
        expr.factory()
            .clone()
            .bound_identifier(new_index, expr.span(), expr.ty().cloned())
    }
}
