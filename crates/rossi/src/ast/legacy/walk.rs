//! Scope-aware identifier traversal over the parser's formula IR.
//!
//! The walker threads a binder stack through expressions and predicates and
//! reports every identifier occurrence — reads, binder declarations, and
//! predicate-application names — with the binders in scope at that point.
//! Its one production consumer is the lowering bridge,
//! which needs the implicit `{E∣P}` binding rule while translating the IR
//! onto the formula model; everything downstream resolves identifiers on the
//! model's occurrence walker instead.
//!
//! The walker is policy-free: it reports occurrences verbatim (including the
//! apostrophe-suffixed after-state form `x'` produced by before-after
//! predicates) and leaves filtering, canonicalisation, and scope resolution to
//! the [`IdentVisitor`] implementation.
//!
//! Identifiers in a binder's type annotation (`∀x⦂T·…`) are reported in the
//! *enclosing* scope, before the binder is pushed, so a carrier set or constant
//! used only as a bound-variable type is attributed correctly.

use std::ops::ControlFlow;

use super::{
    Expression, ExpressionKind, IdentPattern, Predicate, PredicateKind, Span, TypedIdentifier,
};

/// A binder in scope at an occurrence, innermost last.
#[derive(Debug, Clone)]
pub struct Binder {
    /// The bound variable's name.
    pub name: String,
}

/// The syntactic role of a reported identifier occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentRole {
    /// A read of an identifier (an `Expression::Identifier`).
    Usage,
    /// A binder declaration (quantifier / lambda / set-comprehension parameter).
    Binder,
    /// The name of a user-defined predicate application.
    PredicateCall,
}

/// One identifier occurrence reported by the walker.
pub struct IdentOccurrence<'a> {
    /// The identifier text, verbatim (a before-after read keeps its `'`).
    pub name: &'a str,
    /// What this occurrence is.
    pub role: IdentRole,
    /// The binders in scope here, innermost last. A binder declaration is *not*
    /// in its own snapshot.
    pub binders: &'a [Binder],
}

/// Invoked for every identifier occurrence the walker encounters. Returning
/// [`ControlFlow::Break`] aborts the rest of the traversal.
pub trait IdentVisitor {
    /// Visit one identifier occurrence.
    fn visit(&mut self, occ: IdentOccurrence<'_>) -> ControlFlow<()>;

    /// Invoked once per binding construct when the walker enters its body
    /// scope, with the binders it introduces (`frame`) and the source span over
    /// which they are in scope (`scope_span` — the binder body, excluding the
    /// declarations and their type annotations, which belong to the enclosing
    /// scope). Lets a visitor answer "which binders are in scope at this byte
    /// offset" without an identifier occurrence at that offset.
    ///
    /// The default does nothing, so a visitor that only inspects occurrences is
    /// unaffected. Returning [`ControlFlow::Break`] aborts the traversal.
    fn enter_scope(&mut self, _frame: &[Binder], _scope_span: Option<Span>) -> ControlFlow<()> {
        ControlFlow::Continue(())
    }
}

fn emit<V: IdentVisitor>(
    v: &mut V,
    name: &str,
    role: IdentRole,
    binders: &[Binder],
) -> ControlFlow<()> {
    v.visit(IdentOccurrence {
        name,
        role,
        binders,
    })
}

/// Walk a predicate, reporting every identifier occurrence. `binders` is the
/// stack of enclosing binders (empty at a top-level formula; seed it with event
/// parameters to scope guards / actions correctly).
pub fn walk_predicate<V: IdentVisitor>(
    p: &Predicate,
    binders: &mut Vec<Binder>,
    v: &mut V,
) -> ControlFlow<()> {
    match &p.kind {
        PredicateKind::True | PredicateKind::False => ControlFlow::Continue(()),
        PredicateKind::Comparison { left, right, .. } => {
            walk_expression(left, binders, v)?;
            walk_expression(right, binders, v)
        }
        PredicateKind::Not(inner) => walk_predicate(inner, binders, v),
        PredicateKind::Logical { left, right, .. } => {
            walk_predicate(left, binders, v)?;
            walk_predicate(right, binders, v)
        }
        PredicateKind::Quantified {
            identifiers,
            predicate,
            ..
        } => {
            binder_decls(identifiers, binders, v)?;
            with_binders(
                v,
                binders,
                binder_frame(identifiers),
                predicate.span,
                |binders, v| walk_predicate(predicate, binders, v),
            )
        }
        PredicateKind::Application {
            function,
            arguments,
        } => {
            emit(v, &function.name, IdentRole::PredicateCall, binders)?;
            for a in arguments {
                walk_expression(a, binders, v)?;
            }
            ControlFlow::Continue(())
        }
        PredicateKind::BuiltinApplication { arguments, .. } => {
            for a in arguments {
                walk_expression(a, binders, v)?;
            }
            ControlFlow::Continue(())
        }
    }
}

/// Walk an expression, reporting every identifier occurrence.
pub fn walk_expression<V: IdentVisitor>(
    e: &Expression,
    binders: &mut Vec<Binder>,
    v: &mut V,
) -> ControlFlow<()> {
    match &e.kind {
        ExpressionKind::Identifier(n) => emit(v, n, IdentRole::Usage, binders),
        // A relational atom is a builtin value, not an identifier usage — it
        // names no user declaration, so it is never reported as a free name.
        ExpressionKind::AtomicBuiltin(_)
        | ExpressionKind::Integer(_)
        | ExpressionKind::True
        | ExpressionKind::False
        | ExpressionKind::EmptySet
        | ExpressionKind::Naturals
        | ExpressionKind::Naturals1
        | ExpressionKind::Integers
        | ExpressionKind::BoolType => ControlFlow::Continue(()),
        ExpressionKind::Binary { left, right, .. } => {
            walk_expression(left, binders, v)?;
            walk_expression(right, binders, v)
        }
        ExpressionKind::Unary { operand, .. } => walk_expression(operand, binders, v),
        ExpressionKind::FunctionApplication { function, argument } => {
            walk_expression(function, binders, v)?;
            walk_expression(argument, binders, v)
        }
        ExpressionKind::BuiltinApplication { argument, .. } => {
            walk_expression(argument, binders, v)
        }
        ExpressionKind::SetEnumeration(items) => {
            for a in items {
                walk_expression(a, binders, v)?;
            }
            ControlFlow::Continue(())
        }
        ExpressionKind::Bool(p) => walk_predicate(p, binders, v),
        ExpressionKind::RelationalImage { relation, set } => {
            walk_expression(relation, binders, v)?;
            walk_expression(set, binders, v)
        }
        ExpressionKind::SetComprehension {
            identifiers,
            predicate,
            expression,
        } => {
            binder_decls(identifiers, binders, v)?;
            with_binders(
                v,
                binders,
                binder_frame(identifiers),
                union_span(predicate.span, expression.as_ref().and_then(|e| e.span)),
                |binders, v| {
                    walk_predicate(predicate, binders, v)?;
                    if let Some(e) = expression {
                        walk_expression(e, binders, v)?;
                    }
                    ControlFlow::Continue(())
                },
            )
        }
        ExpressionKind::SetBuilder {
            member_expression,
            predicate,
        } => {
            // `{E∣P}` implicitly binds, over both E and P, every
            // identifier free in E that no enclosing binder already
            // covers. There is no declaration site: the first
            // occurrence in E stands in for one, so the frame carries
            // its span and no [`IdentRole::Binder`] event is emitted.
            let frame = implicit_set_builder_frame(member_expression, binders);
            with_binders(
                v,
                binders,
                frame,
                union_span(member_expression.span, predicate.span),
                |binders, v| {
                    walk_expression(member_expression, binders, v)?;
                    walk_predicate(predicate, binders, v)
                },
            )
        }
        ExpressionKind::Lambda {
            pattern,
            predicate,
            expression,
        } => {
            pattern_decls(pattern, binders, v)?;
            let mut frame = Vec::new();
            pattern_frame(pattern, &mut frame);
            with_binders(
                v,
                binders,
                frame,
                union_span(predicate.span, expression.span),
                |binders, v| {
                    walk_predicate(predicate, binders, v)?;
                    walk_expression(expression, binders, v)
                },
            )
        }
        ExpressionKind::QuantifiedUnion {
            identifiers,
            predicate,
            expression,
        }
        | ExpressionKind::QuantifiedInter {
            identifiers,
            predicate,
            expression,
        } => {
            binder_decls(identifiers, binders, v)?;
            with_binders(
                v,
                binders,
                binder_frame(identifiers),
                union_span(predicate.span, expression.span),
                |binders, v| {
                    walk_predicate(predicate, binders, v)?;
                    walk_expression(expression, binders, v)
                },
            )
        }
    }
}

/// Report each binder declaration (in the enclosing scope) and walk its type
/// annotation, also in the enclosing scope.
fn binder_decls<V: IdentVisitor>(
    idents: &[TypedIdentifier],
    binders: &mut Vec<Binder>,
    v: &mut V,
) -> ControlFlow<()> {
    for ti in idents {
        emit(v, &ti.name, IdentRole::Binder, binders)?;
        if let Some(t) = &ti.type_expr {
            walk_expression(t, binders, v)?;
        }
    }
    ControlFlow::Continue(())
}

fn binder_frame(idents: &[TypedIdentifier]) -> Vec<Binder> {
    idents
        .iter()
        .map(|ti| Binder {
            name: ti.name.clone(),
        })
        .collect()
}

/// The implicit binders of `{E∣P}`: identifiers free within `E` (first
/// occurrence order, deduped) that `binders` does not already cover.
fn implicit_set_builder_frame(member_expression: &Expression, binders: &[Binder]) -> Vec<Binder> {
    struct Collector<'a> {
        outer: &'a [Binder],
        frame: Vec<Binder>,
    }
    impl IdentVisitor for Collector<'_> {
        fn visit(&mut self, occ: IdentOccurrence<'_>) -> ControlFlow<()> {
            if occ.role == IdentRole::Usage
                && !occ.binders.iter().any(|b| b.name == occ.name)
                && !self.outer.iter().any(|b| b.name == occ.name)
                && !self.frame.iter().any(|b| b.name == occ.name)
            {
                self.frame.push(Binder {
                    name: occ.name.to_string(),
                });
            }
            ControlFlow::Continue(())
        }
    }
    let mut collector = Collector {
        outer: binders,
        frame: Vec::new(),
    };
    let _ = walk_expression(member_expression, &mut Vec::new(), &mut collector);
    collector.frame
}

/// Report each leaf binder of a lambda pattern (enclosing scope) and walk its
/// type annotation.
fn pattern_decls<V: IdentVisitor>(
    pattern: &IdentPattern,
    binders: &mut Vec<Binder>,
    v: &mut V,
) -> ControlFlow<()> {
    match pattern {
        IdentPattern::Identifier(ti) => {
            emit(v, &ti.name, IdentRole::Binder, binders)?;
            if let Some(t) = &ti.type_expr {
                walk_expression(t, binders, v)?;
            }
            ControlFlow::Continue(())
        }
        IdentPattern::Maplet(l, r) => {
            pattern_decls(l, binders, v)?;
            pattern_decls(r, binders, v)
        }
    }
}

fn pattern_frame(pattern: &IdentPattern, out: &mut Vec<Binder>) {
    match pattern {
        IdentPattern::Identifier(ti) => out.push(Binder {
            name: ti.name.clone(),
        }),
        IdentPattern::Maplet(l, r) => {
            pattern_frame(l, out);
            pattern_frame(r, out);
        }
    }
}

/// Enter a binder scope: report it to the visitor, push `frame` onto `binders`,
/// run `body` with the binders in scope, then truncate back. Reporting and
/// pushing the same `frame` here keeps the two in lockstep — a binder construct
/// cannot bring names into scope for the body without also announcing the scope
/// via [`IdentVisitor::enter_scope`]. `scope_span` is the span of the body the
/// binders cover.
fn with_binders<V: IdentVisitor, F>(
    v: &mut V,
    binders: &mut Vec<Binder>,
    frame: Vec<Binder>,
    scope_span: Option<Span>,
    body: F,
) -> ControlFlow<()>
where
    F: FnOnce(&mut Vec<Binder>, &mut V) -> ControlFlow<()>,
{
    v.enter_scope(&frame, scope_span)?;
    let depth = binders.len();
    binders.extend(frame);
    let r = body(binders, v);
    binders.truncate(depth);
    r
}

/// The smallest span covering both `a` and `b`, used to span a binder body made
/// of several nodes (a comprehension / lambda / quantified-set has a predicate
/// and an expression). `None` only when both endpoints are unknown.
fn union_span(a: Option<Span>, b: Option<Span>) -> Option<Span> {
    match (a, b) {
        (Some(a), Some(b)) => Some(Span {
            start: a.start.min(b.start),
            end: a.end.max(b.end),
        }),
        (a, b) => a.or(b),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Records the `(binder names, scope span)` of every binder body the walker
    /// enters, so a test can check the reported scope.
    struct ScopeRecorder {
        scopes: Vec<(Vec<String>, Option<Span>)>,
    }

    impl IdentVisitor for ScopeRecorder {
        fn visit(&mut self, _occ: IdentOccurrence<'_>) -> ControlFlow<()> {
            ControlFlow::Continue(())
        }

        fn enter_scope(&mut self, frame: &[Binder], scope_span: Option<Span>) -> ControlFlow<()> {
            self.scopes
                .push((frame.iter().map(|b| b.name.clone()).collect(), scope_span));
            ControlFlow::Continue(())
        }
    }

    fn first_predicate_scope(src: &str) -> (Vec<String>, Span) {
        let predicate = crate::parser::parse_predicate_str_legacy(src).expect("parses");
        let mut rec = ScopeRecorder { scopes: Vec::new() };
        let _ = walk_predicate(&predicate, &mut Vec::new(), &mut rec);
        assert_eq!(rec.scopes.len(), 1, "exactly one binder body was entered");
        let (names, span) = rec.scopes.into_iter().next().unwrap();
        (names, span.expect("the binder body carries a span"))
    }

    #[test]
    fn enter_scope_reports_a_quantifier_body() {
        // `∀ x · x > 0`: the body scope is `x > 0`, covering the bound use but
        // not the `∀ x` declaration (declarations live in the enclosing scope).
        let src = "∀ x · x > 0";
        let (names, span) = first_predicate_scope(src);

        assert_eq!(names, vec!["x".to_string()]);
        let bound_use = src.rfind('x').unwrap();
        assert!(span.contains(bound_use), "the body covers the bound use");
        let declaration = src.find('x').unwrap();
        assert!(
            !span.contains(declaration),
            "the body excludes the `∀ x` declaration"
        );
    }

    #[test]
    fn enter_scope_spans_a_comprehension_predicate_and_expression() {
        // `{ x · x > 0 ∣ x + 1 }`: the body spans both the predicate `x > 0` and
        // the expression `x + 1`, so the union covers the trailing use too.
        let src = "s = { x · x > 0 ∣ x + 1 }";
        let (names, span) = first_predicate_scope(src);

        assert_eq!(names, vec!["x".to_string()]);
        let predicate_use = src.find("x > 0").unwrap();
        let expression_use = src.find("x + 1").unwrap();
        assert!(
            span.contains(predicate_use),
            "the body covers the predicate"
        );
        assert!(
            span.contains(expression_use),
            "the union extends to the expression"
        );
    }

    #[test]
    fn union_span_covers_both_endpoints() {
        let a = Span { start: 2, end: 5 };
        let b = Span { start: 7, end: 9 };
        assert_eq!(
            union_span(Some(a), Some(b)),
            Some(Span { start: 2, end: 9 })
        );
        assert_eq!(union_span(None, Some(b)), Some(b));
        assert_eq!(union_span(Some(a), None), Some(a));
        assert_eq!(union_span(None, None), None);
    }

    fn recorded_scopes(src: &str) -> Vec<Vec<String>> {
        let p = crate::parser::parse_predicate_str_legacy(src).expect(src);
        let mut rec = ScopeRecorder { scopes: Vec::new() };
        let _ = walk_predicate(&p, &mut Vec::new(), &mut rec);
        rec.scopes.into_iter().map(|(names, _)| names).collect()
    }

    #[test]
    fn set_builder_scopes_its_member_identifiers() {
        // `{n + m∣n < m}` implicitly binds n and m over both sides, in
        // first-occurrence order.
        assert_eq!(
            recorded_scopes("{n + m∣n < m} ⊆ s"),
            vec![vec!["n".to_string(), "m".to_string()]]
        );
    }

    #[test]
    fn set_builder_leaves_outer_bound_names_to_their_binder() {
        // The member expression's `x` reads the enclosing ∀ binder;
        // only `y` becomes an implicit declaration.
        assert_eq!(
            recorded_scopes("∀x·{x + y∣y < x} ⊆ s"),
            vec![vec!["x".to_string()], vec!["y".to_string()]]
        );
    }
}
