//! Bottom-up type synthesis: nodes built from type-checked parts are
//! type-checked by construction.

use rossi::formula::tag::{AssocExprOp, AtomicOp, BinaryExprOp, QuantExprOp, UnaryExprOp};
use rossi::formula::{Expression, Form, Type};

use crate::common::{decl_ty, eq_pred, ff, fid, fid_ty, int};

fn pow(t: Type) -> Type {
    Type::pow(t)
}

fn rel(l: Type, r: Type) -> Type {
    Type::relation(l, r)
}

/// A typed relation `f ⦂ ℙ(ℤ×BOOL)`.
fn f_int_bool() -> Expression {
    fid_ty("f", rel(Type::Int, Type::Bool))
}

// --- leaves and atoms ---

#[test]
fn integer_literals_are_typed_by_construction() {
    assert_eq!(int(5).ty(), Some(&Type::Int));
    assert!(int(5).is_type_checked());
}

#[test]
fn closed_atomic_operators_have_fixed_types() {
    let cases = [
        (AtomicOp::Integer, pow(Type::Int)),
        (AtomicOp::Natural, pow(Type::Int)),
        (AtomicOp::Natural1, pow(Type::Int)),
        (AtomicOp::Bool, pow(Type::Bool)),
        (AtomicOp::True, Type::Bool),
        (AtomicOp::False, Type::Bool),
        (AtomicOp::KPred, rel(Type::Int, Type::Int)),
        (AtomicOp::KSucc, rel(Type::Int, Type::Int)),
    ];
    for (op, expected) in cases {
        let atom = ff().atomic_expression(op, None, None);
        assert_eq!(atom.ty(), Some(&expected), "{op:?}");
    }
}

#[test]
fn generic_atomic_operators_stay_untyped_without_ascription() {
    for op in [
        AtomicOp::EmptySet,
        AtomicOp::KIdGen,
        AtomicOp::KPrj1Gen,
        AtomicOp::KPrj2Gen,
    ] {
        assert_eq!(ff().atomic_expression(op, None, None).ty(), None, "{op:?}");
    }
}

#[test]
fn generic_atomic_operators_accept_fitting_types() {
    let empty = ff().atomic_expression(AtomicOp::EmptySet, None, Some(pow(Type::Int)));
    assert_eq!(empty.ty(), Some(&pow(Type::Int)));

    let id = ff().atomic_expression(
        AtomicOp::KIdGen,
        None,
        Some(rel(Type::given("S"), Type::given("S"))),
    );
    assert!(id.is_type_checked());

    // prj1 ⦂ ℙ((ℤ×BOOL)×ℤ), prj2 ⦂ ℙ((ℤ×BOOL)×BOOL)
    let pair = Type::prod(Type::Int, Type::Bool);
    let prj1 = ff().atomic_expression(AtomicOp::KPrj1Gen, None, Some(rel(pair.clone(), Type::Int)));
    assert!(prj1.is_type_checked());
    let prj2 = ff().atomic_expression(AtomicOp::KPrj2Gen, None, Some(rel(pair, Type::Bool)));
    assert!(prj2.is_type_checked());
}

#[test]
#[should_panic(expected = "does not fit the operator")]
fn empty_set_rejects_a_non_set_type() {
    ff().atomic_expression(AtomicOp::EmptySet, None, Some(Type::Int));
}

#[test]
#[should_panic(expected = "does not fit the operator")]
fn identity_rejects_asymmetric_types() {
    ff().atomic_expression(AtomicOp::KIdGen, None, Some(rel(Type::Int, Type::Bool)));
}

#[test]
#[should_panic(expected = "does not fit the operator")]
fn closed_operators_reject_foreign_types() {
    ff().atomic_expression(AtomicOp::True, None, Some(Type::Int));
}

// --- binary operators ---

#[test]
fn maplet_builds_a_product() {
    let m = ff().binary_expression(
        BinaryExprOp::Mapsto,
        fid_ty("x", Type::Int),
        fid_ty("y", Type::Bool),
        None,
    );
    assert_eq!(m.ty(), Some(&Type::prod(Type::Int, Type::Bool)));
}

#[test]
fn relation_arrows_build_relation_sets() {
    for op in [
        BinaryExprOp::Rel,
        BinaryExprOp::TRel,
        BinaryExprOp::SRel,
        BinaryExprOp::STRel,
        BinaryExprOp::PFun,
        BinaryExprOp::TFun,
        BinaryExprOp::PInj,
        BinaryExprOp::TInj,
        BinaryExprOp::PSur,
        BinaryExprOp::TSur,
        BinaryExprOp::TBij,
    ] {
        let arrow = ff().binary_expression(
            op,
            fid_ty("a", pow(Type::Int)),
            fid_ty("b", pow(Type::Bool)),
            None,
        );
        assert_eq!(arrow.ty(), Some(&pow(rel(Type::Int, Type::Bool))), "{op:?}");
    }
}

#[test]
fn set_difference_requires_equal_set_types() {
    let same = ff().binary_expression(
        BinaryExprOp::SetMinus,
        fid_ty("a", pow(Type::Int)),
        fid_ty("b", pow(Type::Int)),
        None,
    );
    assert_eq!(same.ty(), Some(&pow(Type::Int)));

    let mixed = ff().binary_expression(
        BinaryExprOp::SetMinus,
        fid_ty("a", pow(Type::Int)),
        fid_ty("b", pow(Type::Bool)),
        None,
    );
    assert_eq!(mixed.ty(), None);
}

#[test]
fn products_and_restrictions_synthesize() {
    let cprod = ff().binary_expression(
        BinaryExprOp::CProd,
        fid_ty("a", pow(Type::Int)),
        fid_ty("b", pow(Type::Bool)),
        None,
    );
    assert_eq!(cprod.ty(), Some(&rel(Type::Int, Type::Bool)));

    // ℙ(ℤ×BOOL) ⊗ ℙ(ℤ×S) → ℙ(ℤ×(BOOL×S))
    let dprod = ff().binary_expression(
        BinaryExprOp::DProd,
        f_int_bool(),
        fid_ty("g", rel(Type::Int, Type::given("S"))),
        None,
    );
    assert_eq!(
        dprod.ty(),
        Some(&rel(Type::Int, Type::prod(Type::Bool, Type::given("S"))))
    );

    // ℙ(ℤ×BOOL) ∥ ℙ(S×T) → ℙ((ℤ×S)×(BOOL×T))
    let pprod = ff().binary_expression(
        BinaryExprOp::PProd,
        f_int_bool(),
        fid_ty("g", rel(Type::given("S"), Type::given("T"))),
        None,
    );
    assert_eq!(
        pprod.ty(),
        Some(&rel(
            Type::prod(Type::Int, Type::given("S")),
            Type::prod(Type::Bool, Type::given("T")),
        ))
    );

    let domres = ff().binary_expression(
        BinaryExprOp::DomRes,
        fid_ty("s", pow(Type::Int)),
        f_int_bool(),
        None,
    );
    assert_eq!(domres.ty(), Some(&rel(Type::Int, Type::Bool)));

    let ransub = ff().binary_expression(
        BinaryExprOp::RanSub,
        f_int_bool(),
        fid_ty("s", pow(Type::Bool)),
        None,
    );
    assert_eq!(ransub.ty(), Some(&rel(Type::Int, Type::Bool)));
}

#[test]
fn arithmetic_and_intervals_synthesize() {
    let upto = ff().binary_expression(BinaryExprOp::UpTo, int(1), int(9), None);
    assert_eq!(upto.ty(), Some(&pow(Type::Int)));

    for op in [
        BinaryExprOp::Minus,
        BinaryExprOp::Div,
        BinaryExprOp::Mod,
        BinaryExprOp::Expn,
    ] {
        let e = ff().binary_expression(op, int(6), int(2), None);
        assert_eq!(e.ty(), Some(&Type::Int), "{op:?}");
    }
}

#[test]
fn function_application_types_as_the_codomain() {
    let app = ff().binary_expression(
        BinaryExprOp::FunImage,
        f_int_bool(),
        fid_ty("x", Type::Int),
        None,
    );
    assert_eq!(app.ty(), Some(&Type::Bool));

    let wrong_arg = ff().binary_expression(
        BinaryExprOp::FunImage,
        f_int_bool(),
        fid_ty("x", Type::Bool),
        None,
    );
    assert_eq!(wrong_arg.ty(), None);
}

#[test]
fn relational_image_types_as_a_codomain_set() {
    let image = ff().binary_expression(
        BinaryExprOp::RelImage,
        f_int_bool(),
        fid_ty("s", pow(Type::Int)),
        None,
    );
    assert_eq!(image.ty(), Some(&pow(Type::Bool)));
}

// --- associative operators ---

#[test]
fn set_operations_require_uniform_set_types() {
    let union = ff().associative_expression(
        AssocExprOp::BUnion,
        vec![fid_ty("a", pow(Type::Int)), fid_ty("b", pow(Type::Int))],
        None,
    );
    assert_eq!(union.ty(), Some(&pow(Type::Int)));

    let mixed = ff().associative_expression(
        AssocExprOp::BUnion,
        vec![fid_ty("a", pow(Type::Int)), fid_ty("b", pow(Type::Bool))],
        None,
    );
    assert_eq!(mixed.ty(), None);
}

#[test]
fn override_requires_relational_children() {
    let ovr = ff().associative_expression(AssocExprOp::Ovr, vec![f_int_bool(), f_int_bool()], None);
    assert_eq!(ovr.ty(), Some(&rel(Type::Int, Type::Bool)));

    let plain_sets = ff().associative_expression(
        AssocExprOp::Ovr,
        vec![fid_ty("a", pow(Type::Int)), fid_ty("b", pow(Type::Int))],
        None,
    );
    assert_eq!(plain_sets.ty(), None);
}

#[test]
fn compositions_chain_types() {
    // f ; g with f ⦂ ℙ(ℤ×BOOL), g ⦂ ℙ(BOOL×S) → ℙ(ℤ×S)
    let fcomp = ff().associative_expression(
        AssocExprOp::FComp,
        vec![f_int_bool(), fid_ty("g", rel(Type::Bool, Type::given("S")))],
        None,
    );
    assert_eq!(fcomp.ty(), Some(&rel(Type::Int, Type::given("S"))));

    // g ∘ f applies f first: same result type.
    let bcomp = ff().associative_expression(
        AssocExprOp::BComp,
        vec![fid_ty("g", rel(Type::Bool, Type::given("S"))), f_int_bool()],
        None,
    );
    assert_eq!(bcomp.ty(), Some(&rel(Type::Int, Type::given("S"))));

    // A broken chain stays untyped.
    let broken =
        ff().associative_expression(AssocExprOp::FComp, vec![f_int_bool(), f_int_bool()], None);
    assert_eq!(broken.ty(), None);
}

#[test]
fn arithmetic_folds_to_integer() {
    let sum = ff().associative_expression(AssocExprOp::Plus, vec![int(1), int(2), int(3)], None);
    assert_eq!(sum.ty(), Some(&Type::Int));
}

// --- unary operators ---

#[test]
fn unary_operators_synthesize() {
    let set = fid_ty("s", pow(Type::Int));

    let card = ff().unary_expression(UnaryExprOp::KCard, set.clone(), None);
    assert_eq!(card.ty(), Some(&Type::Int));

    let powerset = ff().unary_expression(UnaryExprOp::Pow, set.clone(), None);
    assert_eq!(powerset.ty(), Some(&pow(pow(Type::Int))));

    let family = fid_ty("ss", pow(pow(Type::Int)));
    let union = ff().unary_expression(UnaryExprOp::KUnion, family, None);
    assert_eq!(union.ty(), Some(&pow(Type::Int)));

    // union(S) needs a set of sets.
    let flat = ff().unary_expression(UnaryExprOp::KUnion, set.clone(), None);
    assert_eq!(flat.ty(), None);

    let dom = ff().unary_expression(UnaryExprOp::KDom, f_int_bool(), None);
    assert_eq!(dom.ty(), Some(&pow(Type::Int)));
    let ran = ff().unary_expression(UnaryExprOp::KRan, f_int_bool(), None);
    assert_eq!(ran.ty(), Some(&pow(Type::Bool)));

    let minimum = ff().unary_expression(UnaryExprOp::KMin, set, None);
    assert_eq!(minimum.ty(), Some(&Type::Int));

    let converse = ff().unary_expression(UnaryExprOp::Converse, f_int_bool(), None);
    assert_eq!(converse.ty(), Some(&rel(Type::Bool, Type::Int)));

    let negated = ff().unary_expression(UnaryExprOp::UnMinus, int(3), None);
    assert_eq!(negated.ty(), Some(&Type::Int));
}

// --- compound constructions ---

#[test]
fn set_extensions_require_uniform_member_types() {
    let uniform = ff().set_extension(vec![int(1), int(2)], None);
    assert_eq!(uniform.ty(), Some(&pow(Type::Int)));

    let mixed = ff().set_extension(vec![int(1), fid_ty("b", Type::Bool)], None);
    assert_eq!(mixed.ty(), None);

    let untyped_member = ff().set_extension(vec![int(1), fid("x")], None);
    assert_eq!(untyped_member.ty(), None);
}

#[test]
fn bool_reifies_a_type_checked_predicate() {
    let checked = ff().bool_expression(eq_pred(int(1), int(2)), None);
    assert_eq!(checked.ty(), Some(&Type::Bool));

    let unchecked = ff().bool_expression(eq_pred(fid("x"), int(2)), None);
    assert_eq!(unchecked.ty(), None);
}

#[test]
fn comprehensions_and_quantified_unions_synthesize() {
    let cset = ff().quantified_expression(
        QuantExprOp::CSet,
        vec![decl_ty("x", Type::Int)],
        eq_pred(ff().bound_identifier(0, None, Some(Type::Int)), int(1)),
        ff().bound_identifier(0, None, Some(Type::Int)),
        None,
        Form::Implicit,
    );
    assert_eq!(cset.ty(), Some(&pow(Type::Int)));

    let qunion = ff().quantified_expression(
        QuantExprOp::QUnion,
        vec![decl_ty("x", Type::Int)],
        eq_pred(ff().bound_identifier(0, None, Some(Type::Int)), int(1)),
        fid_ty("s", pow(Type::Bool)),
        None,
        Form::Explicit,
    );
    assert_eq!(qunion.ty(), Some(&pow(Type::Bool)));

    // A quantified union over a non-set expression stays untyped.
    let scalar = ff().quantified_expression(
        QuantExprOp::QUnion,
        vec![decl_ty("x", Type::Int)],
        eq_pred(ff().bound_identifier(0, None, Some(Type::Int)), int(1)),
        int(7),
        None,
        Form::Explicit,
    );
    assert_eq!(scalar.ty(), None);
}

#[test]
fn ascriptions_share_their_expressions_type() {
    let typed = ff().ascription(
        fid_ty("x", Type::Int),
        ff().atomic_expression(AtomicOp::Integer, None, None),
        None,
    );
    assert_eq!(typed.ty(), Some(&Type::Int));

    let untyped = ff().ascription(
        fid("x"),
        ff().atomic_expression(AtomicOp::Integer, None, None),
        None,
    );
    assert_eq!(untyped.ty(), None);
}

#[test]
fn untyped_children_block_synthesis() {
    let app = ff().binary_expression(
        BinaryExprOp::FunImage,
        fid("f"),
        fid_ty("x", Type::Int),
        None,
    );
    assert_eq!(app.ty(), None);
    assert!(!app.is_type_checked());
}

#[test]
fn predicates_report_type_checked_from_their_expressions() {
    assert!(eq_pred(int(1), int(2)).is_type_checked());
    assert!(!eq_pred(fid("x"), int(2)).is_type_checked());
}
