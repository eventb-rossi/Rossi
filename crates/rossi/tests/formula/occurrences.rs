//! The scope-aware occurrence walker: roles, exact resolution, and
//! scope events.

use std::ops::ControlFlow;

use rossi::ast::Span;
use rossi::formula::occurrences::{
    DeclRef, Occurrence, OccurrenceVisitor, Resolution, Role, walk_assignment, walk_predicate,
};
use rossi::formula::tag::{AssocPredOp, AtomicOp};

use crate::common::{bid, decl, eq_pred, ff, fid, forall, int};

/// A recorded occurrence: name, role, resolution, scope depth.
type Row = (String, Role, Resolution, usize);

#[derive(Default)]
struct Recorder {
    rows: Vec<Row>,
    scopes: Vec<(Vec<String>, Option<Span>)>,
    stop_at: Option<usize>,
}

impl OccurrenceVisitor for Recorder {
    fn visit(&mut self, occurrence: Occurrence<'_>) -> ControlFlow<()> {
        self.rows.push((
            occurrence.name.to_string(),
            occurrence.role,
            occurrence.resolution,
            occurrence.scope.len(),
        ));
        if self.stop_at == Some(self.rows.len()) {
            return ControlFlow::Break(());
        }
        ControlFlow::Continue(())
    }

    fn enter_scope(&mut self, frame: &[DeclRef], scope_span: Option<Span>) -> ControlFlow<()> {
        self.scopes
            .push((frame.iter().map(|d| d.name.clone()).collect(), scope_span));
        ControlFlow::Continue(())
    }
}

#[test]
fn roles_and_resolution_are_exact() {
    // ∀x⦂ℤ · x = y — the declaration and its annotation report in the
    // enclosing scope, the bound read resolves by index, y stays free.
    let annotated = ff().bound_ident_decl(
        "x",
        None,
        Some(ff().atomic_expression(AtomicOp::Integer, None, None)),
        None,
    );
    let pred = forall(vec![annotated], eq_pred(bid(0), fid("y")));

    let mut recorder = Recorder::default();
    let _ = walk_predicate(&pred, &mut Vec::new(), &mut recorder);

    assert_eq!(
        recorder.rows,
        vec![
            ("x".to_string(), Role::Binder, Resolution::Free, 0),
            (
                "x".to_string(),
                Role::Usage,
                Resolution::Bound { index: 0 },
                1
            ),
            ("y".to_string(), Role::Usage, Resolution::Free, 1),
        ]
    );
    assert_eq!(recorder.scopes.len(), 1);
    assert_eq!(recorder.scopes[0].0, ["x"]);
}

#[test]
fn shadowing_resolves_by_index_not_name() {
    // ∀x · (∀x · x = 1) ∧ x = 2 — both hints are "x"; the inner read
    // resolves to the inner declaration, the outer read to the outer.
    let inner = forall(vec![decl("x")], eq_pred(bid(0), int(1)));
    let outer = forall(
        vec![decl("x")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![inner, eq_pred(bid(0), int(2))],
            None,
        ),
    );
    let mut recorder = Recorder::default();
    let _ = walk_predicate(&outer, &mut Vec::new(), &mut recorder);

    let usages: Vec<&Row> = recorder
        .rows
        .iter()
        .filter(|(_, role, _, _)| *role == Role::Usage)
        .collect();
    // Inner read: depth 2, index 0 (the inner declaration). Outer
    // read: depth 1, index 0 (the outer declaration).
    assert_eq!(
        usages,
        [
            &(
                "x".to_string(),
                Role::Usage,
                Resolution::Bound { index: 0 },
                2
            ),
            &(
                "x".to_string(),
                Role::Usage,
                Resolution::Bound { index: 0 },
                1
            ),
        ]
    );
}

#[test]
fn assignments_report_targets_and_bind_primes() {
    // x :∣ x' = x + 1
    let assignment = ff().becomes_such_that(
        vec![fid("x")],
        vec![decl("x'")],
        eq_pred(
            bid(0),
            ff().associative_expression(
                rossi::formula::tag::AssocExprOp::Plus,
                vec![fid("x"), int(1)],
                None,
            ),
        ),
        None,
    );
    let mut recorder = Recorder::default();
    let _ = walk_assignment(&assignment, &mut Vec::new(), &mut recorder);

    assert_eq!(
        recorder.rows,
        vec![
            ("x".to_string(), Role::WriteTarget, Resolution::Free, 0),
            ("x'".to_string(), Role::Binder, Resolution::Free, 0),
            (
                "x'".to_string(),
                Role::Usage,
                Resolution::Bound { index: 0 },
                1
            ),
            ("x".to_string(), Role::Usage, Resolution::Free, 1),
        ]
    );
}

#[test]
fn seeded_scopes_resolve_outer_indices() {
    // A guard-like body referencing a parameter frame seeded by the
    // caller: b(0) = p.
    let pred = eq_pred(bid(0), int(1));
    let mut scope = vec![DeclRef {
        name: "p".to_string(),
        span: None,
    }];
    let mut recorder = Recorder::default();
    let _ = walk_predicate(&pred, &mut scope, &mut recorder);
    assert_eq!(
        recorder.rows,
        vec![(
            "p".to_string(),
            Role::Usage,
            Resolution::Bound { index: 0 },
            1
        )]
    );
    // The seeded frame survives the walk.
    assert_eq!(scope.len(), 1);
}

#[test]
fn predicate_applications_report_their_name() {
    let pred = ff().predicate_application(
        "connected",
        Some(Span { start: 0, end: 9 }),
        vec![fid("g")],
        None,
    );
    let mut recorder = Recorder::default();
    let _ = walk_predicate(&pred, &mut Vec::new(), &mut recorder);
    assert_eq!(recorder.rows[0].0, "connected");
    assert_eq!(recorder.rows[0].1, Role::PredicateCall);
    assert_eq!(recorder.rows[1].0, "g");
}

#[test]
fn breaking_stops_the_walk() {
    let pred = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![eq_pred(fid("a"), int(1)), eq_pred(fid("b"), int(2))],
        None,
    );
    let mut recorder = Recorder {
        stop_at: Some(1),
        ..Default::default()
    };
    let flow = walk_predicate(&pred, &mut Vec::new(), &mut recorder);
    assert_eq!(flow, ControlFlow::Break(()));
    assert_eq!(recorder.rows.len(), 1);
}

// ---------------------------------------------------------------------
// Parsed comprehension scoping
// ---------------------------------------------------------------------

#[test]
fn implicit_set_builder_binds_every_name_its_member_writes() {
    use rossi::{ExpressionKind, PredicateKind, parse_predicate_str};

    // In `∀x·{x + y∣y < x} ⊆ s` the member is read in a closed scope, so both
    // its names are the comprehension's own and its `x` shadows the enclosing
    // `∀x` — which is left with no occurrence. Rodin reads it the same way.
    let parsed = parse_predicate_str("∀x·{x + y∣y < x} ⊆ s").unwrap();
    let PredicateKind::Quantified { pred, .. } = parsed.kind() else {
        panic!("expected the universal quantifier");
    };
    let PredicateKind::Relational { left, .. } = pred.kind() else {
        panic!("expected the subset comparison");
    };
    let ExpressionKind::Quantified { decls, expr, .. } = left.kind() else {
        panic!("expected the comprehension");
    };
    let names: Vec<&str> = decls.iter().map(|d| d.name()).collect();
    assert_eq!(names, ["x", "y"]);

    // Declaration i is index n-1-i, so `x + y` is `BI_1 + BI_0`: both indices
    // land inside the comprehension. Had `x` still read the enclosing binder it
    // would be `BI_2`, one past the two declarations.
    let ExpressionKind::Associative { children, .. } = expr.kind() else {
        panic!("expected the sum");
    };
    let indices: Vec<&ExpressionKind> = children.iter().map(|child| child.kind()).collect();
    assert!(
        matches!(
            indices[..],
            [
                ExpressionKind::BoundIdentifier(1),
                ExpressionKind::BoundIdentifier(0)
            ]
        ),
        "expected BI_1 + BI_0, got {indices:?}"
    );
}
