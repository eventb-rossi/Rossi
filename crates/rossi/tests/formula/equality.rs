//! Equality, alpha-equivalence, hashing, and construction invariants.

use std::hash::{DefaultHasher, Hash, Hasher};

use rossi::formula::tag::{AssocExprOp, BinaryExprOp, QuantExprOp, RelationalOp};
use rossi::formula::{Expression, Form, Type};

use crate::common::{bid, decl, decl_ty, eq_pred, ff, fid, fid_ty, forall, int, span};

fn hash_of(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

// --- spans ---

#[test]
fn spans_do_not_participate_in_equality_or_hash() {
    let bare = eq_pred(fid("x"), int(1));
    let spanned = ff().relational_predicate(
        RelationalOp::Equal,
        ff().free_identifier("x", Some(span(0, 1)), None),
        ff().integer_literal(1, Some(span(4, 5))),
        Some(span(0, 5)),
    );
    assert_eq!(bare, spanned);
    assert_eq!(hash_of(&bare), hash_of(&spanned));
}

// --- types ---

#[test]
fn solved_types_participate_in_equality() {
    assert_ne!(fid("x"), fid_ty("x", Type::Int));
    assert_ne!(fid_ty("x", Type::Int), fid_ty("x", Type::Bool));
    assert_eq!(fid_ty("x", Type::Int), fid_ty("x", Type::Int));
}

#[test]
fn typed_and_untyped_share_a_hash() {
    // The cached hash is computed before types are solved, so a typed
    // rebuild keeps its untyped hash: unequal but colliding, which is
    // what lets the type-checker reuse unchanged subtrees.
    assert_eq!(hash_of(&fid("x")), hash_of(&fid_ty("x", Type::Int)));
}

// --- alpha-equivalence ---

#[test]
fn quantifiers_are_equal_up_to_declaration_names() {
    let under_x = forall(vec![decl("x")], eq_pred(bid(0), int(0)));
    let under_y = forall(vec![decl("y")], eq_pred(bid(0), int(0)));
    assert_eq!(under_x, under_y);
    assert_eq!(hash_of(&under_x), hash_of(&under_y));
}

#[test]
fn declaration_types_still_participate_under_quantifiers() {
    let int_decl = forall(vec![decl_ty("x", Type::Int)], eq_pred(bid(0), int(0)));
    let renamed = forall(vec![decl_ty("y", Type::Int)], eq_pred(bid(0), int(0)));
    let bool_decl = forall(vec![decl_ty("x", Type::Bool)], eq_pred(bid(0), int(0)));
    assert_eq!(int_decl, renamed);
    assert_ne!(int_decl, bool_decl);
}

#[test]
fn standalone_declarations_compare_by_name_and_type() {
    assert_ne!(decl("x"), decl("y"));
    assert_eq!(decl("x"), decl("x"));
    assert_ne!(decl("x"), decl_ty("x", Type::Int));
    // The source annotation is presentation only.
    let annotated = ff().bound_ident_decl(
        "x",
        None,
        Some(ff().atomic_expression(rossi::formula::tag::AtomicOp::Integer, None, None)),
        None,
    );
    assert_eq!(annotated, decl("x"));
}

// --- structural discrimination ---

#[test]
fn different_operators_are_unequal() {
    let equal = eq_pred(fid("x"), int(1));
    let not_equal = ff().relational_predicate(RelationalOp::NotEqual, fid("x"), int(1), None);
    assert_ne!(equal, not_equal);
}

#[test]
fn independently_built_identical_trees_are_equal() {
    let build =
        || ff().associative_expression(AssocExprOp::Plus, vec![fid("a"), fid("b"), int(3)], None);
    assert_eq!(build(), build());
    assert_eq!(hash_of(&build()), hash_of(&build()));
}

#[test]
fn such_that_assignments_ignore_primed_declaration_names() {
    let build = |primed: &str| {
        ff().becomes_such_that(
            vec![fid("x")],
            vec![decl(primed)],
            eq_pred(bid(0), int(1)),
            None,
        )
    };
    assert_eq!(build("x'"), build("z'"));
    assert_eq!(hash_of(&build("x'")), hash_of(&build("z'")));
}

// --- identifier caches ---

#[test]
fn free_identifiers_are_sorted_and_deduplicated() {
    let sum =
        ff().associative_expression(AssocExprOp::Plus, vec![fid("b"), fid("a"), fid("b")], None);
    assert_eq!(sum.free_identifiers(), ["a", "b"]);
    assert!(sum.dangling_bound_indices().is_empty());
}

#[test]
fn quantifiers_renumber_escaping_indices() {
    // ∀x · b(0) = b(1): index 0 is bound here, index 1 escapes as 0.
    let body = eq_pred(bid(0), bid(1));
    assert_eq!(body.dangling_bound_indices(), [0, 1]);
    let quantified = forall(vec![decl("x")], body);
    assert_eq!(quantified.dangling_bound_indices(), [0]);
}

#[test]
fn declaration_annotations_are_scoped_to_the_enclosing_context() {
    // The annotation of a declaration references the *enclosing* binder
    // context, so its dangling indices pass through unrenumbered and
    // its free names count as used by the quantifier.
    let annotated = ff().bound_ident_decl(
        "y",
        None,
        Some(ff().binary_expression(BinaryExprOp::FunImage, fid("f"), bid(0), None)),
        None,
    );
    let quantified = forall(vec![annotated], eq_pred(bid(0), int(0)));
    assert_eq!(quantified.free_identifiers(), ["f"]);
    assert_eq!(quantified.dangling_bound_indices(), [0]);
}

#[test]
fn solved_declaration_types_contribute_their_given_sets() {
    let quantified = forall(
        vec![decl_ty("x", Type::pow(Type::given("USERS")))],
        eq_pred(bid(0), fid("s")),
    );
    assert_eq!(quantified.free_identifiers(), ["USERS", "s"]);
}

// --- print-form validation ---

fn cset(
    decls: Vec<rossi::formula::BoundIdentDecl>,
    pred: rossi::formula::Predicate,
    expr: Expression,
    form: Form,
) -> Expression {
    ff().quantified_expression(QuantExprOp::CSet, decls, pred, expr, None, form)
}

fn form_of(expr: &Expression) -> Form {
    match expr.kind() {
        rossi::formula::ExpressionKind::Quantified { form, .. } => *form,
        _ => panic!("not a quantified expression"),
    }
}

fn maplet(left: Expression, right: Expression) -> Expression {
    ff().binary_expression(BinaryExprOp::Mapsto, left, right, None)
}

#[test]
fn lambda_form_requires_a_decreasing_pattern() {
    // λ x ↦ y · ⊤ ∣ x  — pattern (1 ↦ 0), body references x.
    let good = cset(
        vec![decl("x"), decl("y")],
        eq_pred(bid(1), bid(0)),
        maplet(maplet(bid(1), bid(0)), bid(1)),
        Form::Lambda,
    );
    assert_eq!(form_of(&good), Form::Lambda);

    // Pattern (0 ↦ 1) is not a lambda pattern; the expression still
    // references exactly the two locals, so it downgrades to Implicit.
    let swapped = cset(
        vec![decl("x"), decl("y")],
        eq_pred(bid(1), bid(0)),
        maplet(maplet(bid(0), bid(1)), bid(1)),
        Form::Lambda,
    );
    assert_eq!(form_of(&swapped), Form::Implicit);
}

#[test]
fn implicit_form_requires_exactly_the_local_identifiers() {
    // {x + 1 ∣ x ∈ S} — expression references only the local.
    let good = cset(
        vec![decl("x")],
        eq_pred(bid(0), fid("s")),
        ff().associative_expression(AssocExprOp::Plus, vec![bid(0), int(1)], None),
        Form::Implicit,
    );
    assert_eq!(form_of(&good), Form::Implicit);

    // A free identifier in the expression forces the explicit form.
    let with_free = cset(
        vec![decl("x")],
        eq_pred(bid(0), fid("s")),
        ff().associative_expression(AssocExprOp::Plus, vec![bid(0), fid("k")], None),
        Form::Implicit,
    );
    assert_eq!(form_of(&with_free), Form::Explicit);

    // An unreferenced local also forces the explicit form.
    let unused_local = cset(
        vec![decl("x"), decl("y")],
        eq_pred(bid(0), bid(1)),
        bid(0),
        Form::Implicit,
    );
    assert_eq!(form_of(&unused_local), Form::Explicit);
}

#[test]
fn ident_list_form_requires_the_canonical_maplet_chain() {
    let single = cset(
        vec![decl("x")],
        eq_pred(bid(0), int(1)),
        bid(0),
        Form::IdentList,
    );
    assert_eq!(form_of(&single), Form::IdentList);

    // Left-nested chain b2 ↦ b1 ↦ b0 for three declarations.
    let three = cset(
        vec![decl("x"), decl("y"), decl("z")],
        eq_pred(bid(2), bid(0)),
        maplet(maplet(bid(2), bid(1)), bid(0)),
        Form::IdentList,
    );
    assert_eq!(form_of(&three), Form::IdentList);

    // A right-nested chain is not the canonical spelling: it would
    // print as an ident list but re-parse left-nested. It still
    // qualifies for the implicit form.
    let right_nested = cset(
        vec![decl("x"), decl("y"), decl("z")],
        eq_pred(bid(2), bid(0)),
        maplet(bid(2), maplet(bid(1), bid(0))),
        Form::IdentList,
    );
    assert_eq!(form_of(&right_nested), Form::Implicit);
}

#[test]
fn explicit_form_is_always_kept() {
    let explicit = cset(
        vec![decl("x")],
        eq_pred(bid(0), int(1)),
        bid(0),
        Form::Explicit,
    );
    assert_eq!(form_of(&explicit), Form::Explicit);
}

#[test]
fn print_form_does_not_participate_in_equality() {
    let implicit = cset(
        vec![decl("x")],
        eq_pred(bid(0), int(1)),
        bid(0),
        Form::Implicit,
    );
    let ident_list = cset(
        vec![decl("x")],
        eq_pred(bid(0), int(1)),
        bid(0),
        Form::IdentList,
    );
    assert_eq!(implicit, ident_list);
    assert_eq!(hash_of(&implicit), hash_of(&ident_list));
}

// --- construction invariants ---

#[test]
#[should_panic(expected = "at least two children")]
fn associative_expressions_need_two_children() {
    ff().associative_expression(AssocExprOp::Plus, vec![int(1)], None);
}

#[test]
#[should_panic(expected = "at least one member")]
fn set_extensions_are_never_empty() {
    ff().set_extension(vec![], None);
}

#[test]
#[should_panic(expected = "must line up")]
fn assignment_targets_and_values_must_line_up() {
    ff().becomes_equal_to(vec![fid("x")], vec![int(1), int(2)], None);
}

#[test]
#[should_panic(expected = "must be free identifiers")]
fn assignment_targets_must_be_free_identifiers() {
    ff().becomes_equal_to(vec![int(1)], vec![int(2)], None);
}

#[test]
#[should_panic(expected = "one primed declaration per assignment target")]
fn such_that_assignments_pair_targets_with_primed_declarations() {
    ff().becomes_such_that(
        vec![fid("x"), fid("y")],
        vec![decl("x'")],
        eq_pred(bid(0), int(1)),
        None,
    );
}
