//! Datatype extension bundles: typing, recursion, and destructor WD.

use rossi::formula::extension::datatype::{Datatype, DatatypeBuilder, DatatypeError};

use crate::common::env;
use rossi::formula::tag::{QuantPredOp, RelationalOp};
use rossi::formula::{ExpressionKind, PredicateKind, Type};

/// `List(T) ::= nil ∥ cons(head: T, tail: List(T))`
fn list() -> &'static Datatype {
    static LIST: std::sync::LazyLock<Datatype> = std::sync::LazyLock::new(|| {
        let mut builder = DatatypeBuilder::new("List", &["T"]);
        let tail_ty = builder.self_type();
        builder.constructor("nil");
        builder
            .constructor("cons")
            .arg(Some("head"), Type::given("T"))
            .arg(Some("tail"), tail_ty);
        builder.finalize().expect("valid declaration")
    });
    &LIST
}

fn list_int() -> Type {
    Type::Parametric {
        tag: list().tag(),
        symbol: "List".into(),
        params: vec![Type::Int],
    }
}

#[test]
fn declarations_are_validated() {
    assert_eq!(
        DatatypeBuilder::new("Empty", &[]).finalize().unwrap_err(),
        DatatypeError::NoConstructors
    );

    let mut clash = DatatypeBuilder::new("D", &[]);
    clash.constructor("mk").arg(Some("D"), Type::Int);
    assert_eq!(
        clash.finalize().unwrap_err(),
        DatatypeError::DuplicateName("D".into())
    );
}

#[test]
fn type_constructor_instances_denote_sets() {
    let dt = list();
    let ff = dt.factory();
    // List(ℤ) — over the integer set — has type ℙ(List(ℤ)).
    let applied = ff
        .extended_expression(
            &dt.type_constructor(),
            vec![Type::Int.to_expression(&ff)],
            vec![],
            None,
            None,
        )
        .expect("arity fits");
    assert_eq!(applied.ty(), Some(&Type::pow(list_int())));
    assert_eq!(list_int().to_rodin_canonical(), "List(ℤ)");
}

#[test]
fn constructors_type_and_infer() {
    let dt = list();
    let ff = dt.factory();

    // cons(1, l) = m infers l, m ⦂ List(ℤ).
    let node = ff
        .extended_expression(
            &dt.constructor("cons").expect("declared"),
            vec![
                ff.integer_literal(1, None),
                ff.free_identifier("l", None, None),
            ],
            vec![],
            None,
            None,
        )
        .expect("arity fits");
    let pred = ff.relational_predicate(
        RelationalOp::Equal,
        node,
        ff.free_identifier("m", None, None),
        None,
    );
    let result = pred.type_check(&env(&[]));
    assert!(result.is_success(), "problems: {:?}", result.problems);
    assert_eq!(result.inferred.get("l"), Some(&list_int()));
    assert_eq!(result.inferred.get("m"), Some(&list_int()));

    // Typed children synthesize the instance by construction.
    let nil = ff
        .extended_expression(
            &dt.constructor("nil").expect("declared"),
            vec![],
            vec![],
            None,
            None,
        )
        .expect("arity fits");
    // A nullary constructor cannot know its parameters.
    assert_eq!(nil.ty(), None);
    let typed_cons = ff
        .extended_expression(
            &dt.constructor("cons").expect("declared"),
            vec![
                ff.integer_literal(1, None),
                ff.free_identifier("l", None, Some(list_int())),
            ],
            vec![],
            None,
            None,
        )
        .expect("arity fits");
    assert_eq!(typed_cons.ty(), Some(&list_int()));
}

#[test]
fn destructors_project_and_guard() {
    let dt = list();
    let ff = dt.factory();

    // head(l) with l ⦂ List(ℤ) types as ℤ; tail(l) as List(ℤ).
    let l = || ff.free_identifier("l", None, None);
    let head = ff
        .extended_expression(
            &dt.destructor("head").expect("declared"),
            vec![l()],
            vec![],
            None,
            None,
        )
        .expect("arity fits");
    let pred =
        ff.relational_predicate(RelationalOp::Equal, head, ff.integer_literal(0, None), None);
    let result = pred.type_check(&env(&[]));
    assert!(result.is_success(), "problems: {:?}", result.problems);
    assert_eq!(result.inferred.get("l"), Some(&list_int()));

    // The WD lemma is ∃head0, tail1 · l = cons(head0, tail1).
    let typed = result.typed.expect("typed");
    let lemma = typed.wd_lemma();
    let PredicateKind::Quantified {
        op: QuantPredOp::Exists,
        decls,
        pred: body,
    } = lemma.kind()
    else {
        panic!("expected an existential lemma, got {lemma:?}");
    };
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name(), "head0");
    assert_eq!(decls[0].ty(), Some(&Type::Int));
    assert_eq!(decls[1].name(), "tail1");
    assert_eq!(decls[1].ty(), Some(&list_int()));
    let PredicateKind::Relational {
        op: RelationalOp::Equal,
        right,
        ..
    } = body.kind()
    else {
        panic!("expected an equality body");
    };
    assert!(matches!(right.kind(), ExpressionKind::Extended { .. }));
}

#[test]
fn single_constructor_destructors_are_total() {
    static PAIR: std::sync::LazyLock<Datatype> = std::sync::LazyLock::new(|| {
        let mut builder = DatatypeBuilder::new("MyPair", &["A", "B"]);
        builder
            .constructor("mk")
            .arg(Some("fst"), Type::given("A"))
            .arg(Some("snd"), Type::given("B"));
        builder.finalize().expect("valid declaration")
    });
    let ff = PAIR.factory();
    let pair_ty = Type::Parametric {
        tag: PAIR.tag(),
        symbol: "MyPair".into(),
        params: vec![Type::Int, Type::Bool],
    };
    let fst = ff
        .extended_expression(
            &PAIR.destructor("fst").expect("declared"),
            vec![ff.free_identifier("p", None, Some(pair_ty))],
            vec![],
            None,
            None,
        )
        .expect("arity fits");
    assert_eq!(fst.ty(), Some(&Type::Int));
    let pred = ff.relational_predicate(RelationalOp::Equal, fst, ff.integer_literal(0, None), None);
    let typed = pred.type_check(&env(&[])).typed.expect("typed");
    assert_eq!(
        typed.wd_lemma(),
        ff.literal_predicate(rossi::formula::tag::LiteralPredOp::BTrue, None)
    );
}
