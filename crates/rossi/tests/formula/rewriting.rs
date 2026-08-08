//! The rewrite driver, substitutions, and flattening.

use std::collections::HashMap;

use rossi::formula::tag::{AssocExprOp, AssocPredOp, LiteralPredOp, UnaryExprOp};
use rossi::formula::{Expression, ExpressionKind, FormulaRewriter, Predicate, PredicateKind};

use crate::common::{bid, decl, eq_pred, ff, fid, forall, int};

/// Pointer equality on expression handles.
fn same_expr(a: &Expression, b: &Expression) -> bool {
    // Equal cached hashes and structure could coincide; the pointer is
    // the contract under test.
    let a: *const ExpressionKind = a.kind();
    let b: *const ExpressionKind = b.kind();
    std::ptr::eq(a, b)
}

fn same_pred(a: &Predicate, b: &Predicate) -> bool {
    let a: *const PredicateKind = a.kind();
    let b: *const PredicateKind = b.kind();
    std::ptr::eq(a, b)
}

struct Identity;

impl FormulaRewriter for Identity {}

// --- driver contract ---

#[test]
fn identity_rewrite_returns_the_same_handles() {
    let pred = forall(
        vec![decl("x")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![eq_pred(bid(0), int(1)), eq_pred(fid("y"), int(2))],
            None,
        ),
    );
    let rewritten = pred.rewrite(&mut Identity);
    assert!(same_pred(&rewritten, &pred));
}

#[test]
fn rewriter_sees_binding_depth() {
    /// Records the depth at which each free identifier is visited.
    struct DepthRecorder {
        depth: usize,
        seen: Vec<(String, usize)>,
    }

    impl FormulaRewriter for DepthRecorder {
        fn entering_quantifier(&mut self, n: usize) {
            self.depth += n;
        }
        fn leaving_quantifier(&mut self, n: usize) {
            self.depth -= n;
        }
        fn rewrite_expression(&mut self, expr: &Expression) -> Expression {
            if let ExpressionKind::FreeIdentifier(name) = expr.kind() {
                self.seen.push((name.clone(), self.depth));
            }
            expr.clone()
        }
    }

    // y at depth 0, then ∀a,b · z at depth 2.
    let pred = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            eq_pred(fid("y"), int(1)),
            forall(vec![decl("a"), decl("b")], eq_pred(fid("z"), int(2))),
        ],
        None,
    );
    let mut recorder = DepthRecorder {
        depth: 0,
        seen: Vec::new(),
    };
    pred.rewrite(&mut recorder);
    assert_eq!(recorder.seen, [("y".to_string(), 0), ("z".to_string(), 2)]);
}

// --- shifting ---

#[test]
fn shift_renumbers_only_dangling_indices() {
    // ∀x · b(0) = b(1): 0 is bound, 1 dangles.
    let pred = forall(vec![decl("x")], eq_pred(bid(0), bid(1)));
    let shifted = pred.shift_bound_identifiers(2);
    assert_eq!(shifted, forall(vec![decl("x")], eq_pred(bid(0), bid(3))));

    // Shifting back restores the original.
    assert_eq!(shifted.shift_bound_identifiers(-2), pred);
}

#[test]
fn zero_shift_is_free() {
    let pred = eq_pred(bid(4), int(1));
    assert!(same_pred(&pred.shift_bound_identifiers(0), &pred));
}

#[test]
#[should_panic(expected = "capture")]
fn shift_underflow_panics() {
    eq_pred(bid(0), int(1)).shift_bound_identifiers(-1);
}

// --- free-identifier substitution ---

#[test]
fn substitution_replaces_at_any_depth() {
    let map: HashMap<String, Expression> = [("y".to_string(), int(7))].into_iter().collect();

    // y = 1 ∧ (∀x · y = b(0))
    let pred = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            eq_pred(fid("y"), int(1)),
            forall(vec![decl("x")], eq_pred(fid("y"), bid(0))),
        ],
        None,
    );
    let substituted = pred.substitute_free_idents(&map);
    let expected = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            eq_pred(int(7), int(1)),
            forall(vec![decl("x")], eq_pred(int(7), bid(0))),
        ],
        None,
    );
    assert_eq!(substituted, expected);
}

#[test]
fn open_replacements_are_shifted_to_their_insertion_depth() {
    // Replace y by b(0) — an index meaningful in the *caller's* scope.
    let map: HashMap<String, Expression> = [("y".to_string(), bid(0))].into_iter().collect();

    // Under ∀x, the inserted index must skip the local binder: b(1).
    let pred = forall(vec![decl("x")], eq_pred(fid("y"), bid(0)));
    let substituted = pred.substitute_free_idents(&map);
    assert_eq!(
        substituted,
        forall(vec![decl("x")], eq_pred(bid(1), bid(0)))
    );
}

#[test]
fn substitution_without_hits_is_free() {
    let map: HashMap<String, Expression> = [("missing".to_string(), int(1))].into_iter().collect();
    let pred = eq_pred(fid("y"), int(2));
    assert!(same_pred(&pred.substitute_free_idents(&map), &pred));
}

// --- binding ---

#[test]
fn binding_follows_declaration_order_and_shifts_existing_indices() {
    // ∀x · x = y ∧ y = z, then bind [y, z] around it: inside the ∀,
    // y gets index 2 and z gets index 1 (the last name binds tightest).
    let pred = forall(
        vec![decl("x")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![eq_pred(bid(0), fid("y")), eq_pred(fid("y"), fid("z"))],
            None,
        ),
    );
    let bound = pred.bind_idents(&["y", "z"]);
    let expected = forall(
        vec![decl("x")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![eq_pred(bid(0), bid(2)), eq_pred(bid(2), bid(1))],
            None,
        ),
    );
    assert_eq!(bound, expected);
    // The formula is now ready to sit under a binder declaring [y, z]:
    // its dangling indices are exactly 0 and 1.
    assert_eq!(bound.dangling_bound_indices(), [0, 1]);

    // A pre-existing dangling index is shifted past the new binders.
    let with_dangling = eq_pred(fid("y"), bid(0));
    let bound = with_dangling.bind_idents(&["y"]);
    assert_eq!(bound, eq_pred(bid(0), bid(1)));
}

// --- instantiation ---

#[test]
fn instantiate_replaces_and_renumbers() {
    // ∀x,y · x = y, instantiating x ≔ 7 keeps ∀y · 7 = y.
    let pred = forall(vec![decl("x"), decl("y")], eq_pred(bid(1), bid(0)));
    let partial = pred.instantiate(&[Some(int(7)), None]);
    assert_eq!(partial, forall(vec![decl("y")], eq_pred(int(7), bid(0))));

    // Instantiating everything drops the quantifier.
    let full = pred.instantiate(&[Some(int(7)), Some(fid("k"))]);
    assert_eq!(full, eq_pred(int(7), fid("k")));
}

#[test]
fn instantiate_shifts_open_replacements_past_kept_declarations() {
    // ∀x,y · x = y with x ≔ b(0): the replacement's index must skip
    // the kept declaration y to still mean the caller's b(0).
    let pred = forall(vec![decl("x"), decl("y")], eq_pred(bid(1), bid(0)));
    let partial = pred.instantiate(&[Some(bid(0)), None]);
    assert_eq!(partial, forall(vec![decl("y")], eq_pred(bid(1), bid(0))));
}

#[test]
#[should_panic(expected = "quantified")]
fn instantiate_requires_a_quantifier() {
    eq_pred(int(1), int(2)).instantiate(&[]);
}

// --- flattening ---

#[test]
fn flatten_merges_nested_associative_nodes() {
    let nested = ff().associative_expression(
        AssocExprOp::Plus,
        vec![
            fid("a"),
            ff().associative_expression(AssocExprOp::Plus, vec![fid("b"), fid("c")], None),
        ],
        None,
    );
    let flat =
        ff().associative_expression(AssocExprOp::Plus, vec![fid("a"), fid("b"), fid("c")], None);
    assert_eq!(nested.flatten(), flat);
    // A different operator underneath is not merged.
    let mixed = ff().associative_expression(
        AssocExprOp::Plus,
        vec![
            fid("a"),
            ff().associative_expression(AssocExprOp::Mul, vec![fid("b"), fid("c")], None),
        ],
        None,
    );
    assert!(same_expr(&mixed.flatten(), &mixed));
}

#[test]
fn flatten_drops_unused_declarations() {
    // ∀x,y · y = 1 — x (index 1) is unused.
    let pred = forall(vec![decl("x"), decl("y")], eq_pred(bid(0), int(1)));
    assert_eq!(
        pred.flatten(),
        forall(vec![decl("y")], eq_pred(bid(0), int(1)))
    );

    // All declarations unused: the quantifier disappears.
    let vacuous = forall(vec![decl("x")], eq_pred(int(1), int(2)));
    assert_eq!(vacuous.flatten(), eq_pred(int(1), int(2)));
}

#[test]
fn flatten_merges_directly_nested_quantifiers() {
    // ∀x · ∀y · x = y  ⇒  ∀x,y · x = y (indices unchanged).
    let nested = forall(
        vec![decl("x")],
        forall(vec![decl("y")], eq_pred(bid(1), bid(0))),
    );
    let merged = forall(vec![decl("x"), decl("y")], eq_pred(bid(1), bid(0)));
    assert_eq!(nested.flatten(), merged);
}

#[test]
fn flatten_folds_negated_literals() {
    let negated = ff().unary_expression(UnaryExprOp::UnMinus, int(5), None);
    assert_eq!(negated.flatten(), int(-5));
    // But not the negation of anything else.
    let neg_ident = ff().unary_expression(UnaryExprOp::UnMinus, fid("x"), None);
    assert!(same_expr(&neg_ident.flatten(), &neg_ident));
}

#[test]
fn flatten_is_idempotent() {
    let pred = forall(
        vec![decl("x"), decl("unused")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![
                eq_pred(bid(1), int(1)),
                ff().associative_predicate(
                    AssocPredOp::LAnd,
                    vec![
                        ff().literal_predicate(LiteralPredOp::BTrue, None),
                        eq_pred(
                            bid(1),
                            ff().unary_expression(UnaryExprOp::UnMinus, int(3), None),
                        ),
                    ],
                    None,
                ),
            ],
            None,
        ),
    );
    let once = pred.flatten();
    let twice = once.flatten();
    assert!(same_pred(&twice, &once));
}

// --- handle identity sanity ---

#[test]
fn clones_share_the_node() {
    let e = fid("x");
    let c = e.clone();
    assert!(same_expr(&e, &c));
}
