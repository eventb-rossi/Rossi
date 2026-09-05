//! Scope-aware identifier traversal over formula-model trees.
//!
//! One walker threads a declaration stack through expressions,
//! predicates and assignments and reports every identifier occurrence —
//! reads, binder declarations, assignment targets, and predicate
//! application names — with its span, its role, and its exact
//! resolution: a bound occurrence carries the index of the declaration
//! it refers to, so consumers never re-derive scoping by name.
//!
//! Identifiers in a declaration's annotation are reported in the
//! *enclosing* scope, before the declaration's frame is pushed. The
//! primed declarations of a such-that assignment bind like quantifier
//! declarations, so `x'` reads inside the condition resolve to them.

use std::ops::ControlFlow;

use crate::ast::Span;

use super::assignment::{Assignment, AssignmentKind};
use super::decl::BoundIdentDecl;
use super::expression::{Expression, ExpressionKind};
use super::predicate::{Predicate, PredicateKind};

/// One declaration in scope, innermost last.
#[derive(Debug, Clone)]
pub struct DeclRef {
    /// The declared name (a printing hint; occurrences resolve by
    /// index, not by this name).
    pub name: String,
    /// Source span of the declaration's name token, if known.
    pub span: Option<Span>,
}

impl DeclRef {
    fn of(decl: &BoundIdentDecl) -> DeclRef {
        DeclRef {
            name: decl.name().to_string(),
            span: decl.span(),
        }
    }
}

/// The syntactic role of a reported occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// A read of an identifier.
    Usage,
    /// A binder declaration.
    Binder,
    /// An assignment target.
    WriteTarget,
    /// The name of a user predicate application.
    PredicateCall,
}

/// How an occurrence resolves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolution {
    /// A free identifier (including primed after-state reads outside
    /// their binding assignment).
    Free,
    /// A bound identifier: the declaration is `scope[len - 1 - index]`.
    Bound {
        /// The de Bruijn index at this occurrence.
        index: u32,
    },
}

/// One identifier occurrence.
pub struct Occurrence<'a> {
    /// The identifier text: the verbatim lexeme for free identifiers,
    /// the declaration's hint for bound ones.
    pub name: &'a str,
    /// Source span of this occurrence, if known.
    pub span: Option<Span>,
    /// What this occurrence is.
    pub role: Role,
    /// How it resolves.
    pub resolution: Resolution,
    /// The declarations in scope here, innermost last. A declaration is
    /// not in its own snapshot.
    pub scope: &'a [DeclRef],
}

impl Occurrence<'_> {
    /// The declaration a bound occurrence refers to.
    pub fn bound_decl(&self) -> Option<&DeclRef> {
        match self.resolution {
            Resolution::Bound { index } => self
                .scope
                .len()
                .checked_sub(1 + index as usize)
                .map(|i| &self.scope[i]),
            Resolution::Free => None,
        }
    }

    /// Whether this is an after-state read: a bound occurrence of a
    /// becomes-such-that primed declaration (`x'`), which reads the
    /// post-value of the assigned variable `x` rather than a local
    /// binder. The primed-name spelling is the model's representation
    /// of those declarations; this is its one decoding site.
    pub fn is_after_state_read(&self) -> bool {
        matches!(self.resolution, Resolution::Bound { .. })
            && crate::names::is_primed_identifier(self.name)
    }

    /// The unprimed variable an after-state read refers to (`x` for
    /// `x'`); `None` when this is not an after-state read.
    pub fn after_state_base(&self) -> Option<&str> {
        if self.is_after_state_read() {
            self.name.strip_suffix('\'')
        } else {
            None
        }
    }
}

/// Invoked for every occurrence. Returning [`ControlFlow::Break`]
/// aborts the traversal.
pub trait OccurrenceVisitor {
    /// Visit one occurrence.
    fn visit(&mut self, occurrence: Occurrence<'_>) -> ControlFlow<()>;

    /// Invoked once per binding construct when the walker enters its
    /// body, with the frame it introduces and the span the frame covers
    /// (the body, excluding declarations and their annotations).
    fn enter_scope(&mut self, _frame: &[DeclRef], _scope_span: Option<Span>) -> ControlFlow<()> {
        ControlFlow::Continue(())
    }
}

fn union_span(a: Option<Span>, b: Option<Span>) -> Option<Span> {
    match (a, b) {
        (Some(a), Some(b)) => Some(Span {
            start: a.start.min(b.start),
            end: a.end.max(b.end),
        }),
        (a, None) => a,
        (None, b) => b,
    }
}

fn emit<V: OccurrenceVisitor>(
    v: &mut V,
    name: &str,
    span: Option<Span>,
    role: Role,
    resolution: Resolution,
    scope: &[DeclRef],
) -> ControlFlow<()> {
    v.visit(Occurrence {
        name,
        span,
        role,
        resolution,
        scope,
    })
}

/// Reports the declarations of a binding construct (and their
/// annotations) in the enclosing scope.
fn decl_intros<V: OccurrenceVisitor>(
    decls: &[BoundIdentDecl],
    scope: &mut Vec<DeclRef>,
    v: &mut V,
) -> ControlFlow<()> {
    for decl in decls {
        emit(
            v,
            decl.name(),
            decl.span(),
            Role::Binder,
            Resolution::Free,
            scope,
        )?;
        if let Some(annotation) = decl.annotation() {
            walk_expression(annotation, scope, v)?;
        }
    }
    ControlFlow::Continue(())
}

/// Runs `body` with the declarations pushed, always popping them.
fn with_frame<V: OccurrenceVisitor>(
    decls: &[BoundIdentDecl],
    scope_span: Option<Span>,
    scope: &mut Vec<DeclRef>,
    v: &mut V,
    body: impl FnOnce(&mut Vec<DeclRef>, &mut V) -> ControlFlow<()>,
) -> ControlFlow<()> {
    let frame: Vec<DeclRef> = decls.iter().map(DeclRef::of).collect();
    v.enter_scope(&frame, scope_span)?;
    let depth = scope.len();
    scope.extend(frame);
    let flow = body(scope, v);
    scope.truncate(depth);
    flow
}

/// Walk an expression; `scope` is the stack of enclosing declarations
/// (seed it to resolve indices bound outside the formula).
pub fn walk_expression<V: OccurrenceVisitor>(
    e: &Expression,
    scope: &mut Vec<DeclRef>,
    v: &mut V,
) -> ControlFlow<()> {
    match e.kind() {
        ExpressionKind::FreeIdentifier(name) => {
            emit(v, name, e.span(), Role::Usage, Resolution::Free, scope)
        }
        ExpressionKind::BoundIdentifier(index) => {
            match scope.len().checked_sub(1 + *index as usize) {
                Some(i) => emit(
                    v,
                    &scope[i].name,
                    e.span(),
                    Role::Usage,
                    Resolution::Bound { index: *index },
                    scope,
                ),
                // An index with no enclosing declaration names nothing.
                None => ControlFlow::Continue(()),
            }
        }
        ExpressionKind::IntegerLiteral(_) | ExpressionKind::Atomic(_) => ControlFlow::Continue(()),
        ExpressionKind::SetExtension(members) => {
            for member in members {
                walk_expression(member, scope, v)?;
            }
            ControlFlow::Continue(())
        }
        ExpressionKind::Bool(pred) => walk_predicate(pred, scope, v),
        ExpressionKind::Binary { left, right, .. } => {
            walk_expression(left, scope, v)?;
            walk_expression(right, scope, v)
        }
        ExpressionKind::Associative { children, .. } => {
            for child in children {
                walk_expression(child, scope, v)?;
            }
            ControlFlow::Continue(())
        }
        ExpressionKind::Unary { child, .. } => walk_expression(child, scope, v),
        ExpressionKind::Quantified {
            decls,
            pred,
            expr,
            form,
            ..
        } => {
            // An implicit comprehension `{E ∣ P}` has no declaration
            // site: its binders are the identifiers free in E, and the
            // first occurrence there stands in for the declaration. No
            // Binder occurrence is reported for them — emitting one at
            // the stand-in span would double the occurrence.
            if *form != super::expression::Form::Implicit {
                decl_intros(decls, scope, v)?;
            }
            with_frame(
                decls,
                union_span(pred.span(), expr.span()),
                scope,
                v,
                |scope, v| {
                    walk_predicate(pred, scope, v)?;
                    walk_expression(expr, scope, v)
                },
            )
        }
        ExpressionKind::Ascription { expr, type_expr } => {
            walk_expression(expr, scope, v)?;
            walk_expression(type_expr, scope, v)
        }
        ExpressionKind::Extended { exprs, preds, .. } => {
            for child in exprs {
                walk_expression(child, scope, v)?;
            }
            for child in preds {
                walk_predicate(child, scope, v)?;
            }
            ControlFlow::Continue(())
        }
    }
}

/// Walk a predicate; see [`walk_expression`].
pub fn walk_predicate<V: OccurrenceVisitor>(
    p: &Predicate,
    scope: &mut Vec<DeclRef>,
    v: &mut V,
) -> ControlFlow<()> {
    match p.kind() {
        PredicateKind::Literal(_) | PredicateKind::PredicateVariable(_) => {
            ControlFlow::Continue(())
        }
        PredicateKind::Relational { left, right, .. } => {
            walk_expression(left, scope, v)?;
            walk_expression(right, scope, v)
        }
        PredicateKind::Binary { left, right, .. } => {
            walk_predicate(left, scope, v)?;
            walk_predicate(right, scope, v)
        }
        PredicateKind::Associative { children, .. } => {
            for child in children {
                walk_predicate(child, scope, v)?;
            }
            ControlFlow::Continue(())
        }
        PredicateKind::Not(child) => walk_predicate(child, scope, v),
        PredicateKind::Quantified { decls, pred, .. } => {
            decl_intros(decls, scope, v)?;
            with_frame(decls, pred.span(), scope, v, |scope, v| {
                walk_predicate(pred, scope, v)
            })
        }
        PredicateKind::Simple(child) => walk_expression(child, scope, v),
        PredicateKind::Multiple(children) => {
            for child in children {
                walk_expression(child, scope, v)?;
            }
            ControlFlow::Continue(())
        }
        PredicateKind::Application {
            function,
            function_span,
            args,
        } => {
            emit(
                v,
                function,
                *function_span,
                Role::PredicateCall,
                Resolution::Free,
                scope,
            )?;
            for arg in args {
                walk_expression(arg, scope, v)?;
            }
            ControlFlow::Continue(())
        }
        PredicateKind::Extended { exprs, preds, .. } => {
            for child in exprs {
                walk_expression(child, scope, v)?;
            }
            for child in preds {
                walk_predicate(child, scope, v)?;
            }
            ControlFlow::Continue(())
        }
    }
}

/// Walk an assignment: targets first (as [`Role::WriteTarget`]), then
/// the right-hand formulas; the primed declarations of a such-that
/// assignment bind over its condition.
pub fn walk_assignment<V: OccurrenceVisitor>(
    a: &Assignment,
    scope: &mut Vec<DeclRef>,
    v: &mut V,
) -> ControlFlow<()> {
    let targets = |idents: &[Expression], scope: &mut Vec<DeclRef>, v: &mut V| -> ControlFlow<()> {
        for ident in idents {
            let ExpressionKind::FreeIdentifier(name) = ident.kind() else {
                unreachable!("assignment targets are free identifiers");
            };
            emit(
                v,
                name,
                ident.span(),
                Role::WriteTarget,
                Resolution::Free,
                scope,
            )?;
        }
        ControlFlow::Continue(())
    };
    match a.kind() {
        AssignmentKind::BecomesEqualTo { idents, values } => {
            targets(idents, scope, v)?;
            for value in values {
                walk_expression(value, scope, v)?;
            }
            ControlFlow::Continue(())
        }
        AssignmentKind::BecomesMemberOf { idents, set } => {
            targets(idents, scope, v)?;
            walk_expression(set, scope, v)
        }
        AssignmentKind::BecomesSuchThat {
            idents,
            primed,
            pred,
        } => {
            targets(idents, scope, v)?;
            decl_intros(primed, scope, v)?;
            with_frame(primed, pred.span(), scope, v, |scope, v| {
                walk_predicate(pred, scope, v)
            })
        }
    }
}
