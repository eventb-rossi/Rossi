//! Property tests for the formula-layer invariants.

use std::collections::HashMap;

use proptest::prelude::*;

use crate::common::{ff, hash_of};

use rossi::formula::tag::{
    AssocExprOp, AssocPredOp, BinaryExprOp, BinaryPredOp, QuantPredOp, RelationalOp, UnaryExprOp,
};
use rossi::formula::{
    Expression, FormulaRewriter, Predicate, SealedTypeEnvironment, Type, TypeEnvironmentBuilder,
};

/// The fixed environment the type-directed generators target.
fn base_env() -> SealedTypeEnvironment {
    let mut builder = TypeEnvironmentBuilder::new();
    builder.insert("a", Type::Int);
    builder.insert("b", Type::Int);
    builder.insert("s", Type::pow(Type::Int));
    builder.insert("f", Type::relation(Type::Int, Type::Int));
    builder.make_snapshot()
}

/// Integer-valued expressions over the base environment; `depth`
/// integer-typed binders are in scope.
fn int_expr(depth: u32, size: u32) -> BoxedStrategy<Expression> {
    let leaf = {
        let mut choices: Vec<BoxedStrategy<Expression>> = vec![
            (-9i64..10)
                .prop_map(|n| ff().integer_literal(n, None))
                .boxed(),
            Just(ff().free_identifier("a", None, None)).boxed(),
            Just(ff().free_identifier("b", None, None)).boxed(),
        ];
        if depth > 0 {
            choices.push(
                (0..depth)
                    .prop_map(|i| ff().bound_identifier(i, None, None))
                    .boxed(),
            );
        }
        proptest::strategy::Union::new(choices).boxed()
    };
    if size == 0 {
        return leaf;
    }
    let smaller = move || int_expr(depth, size - 1);
    prop_oneof![
        3 => leaf,
        1 => (smaller(), smaller()).prop_map(|(l, r)| {
            ff().binary_expression(BinaryExprOp::Minus, l, r, None)
        }),
        1 => (smaller(), smaller()).prop_map(|(l, r)| {
            ff().binary_expression(BinaryExprOp::Div, l, r, None)
        }),
        1 => proptest::collection::vec(smaller(), 2..4).prop_map(|children| {
            ff().associative_expression(AssocExprOp::Plus, children, None)
        }),
        1 => smaller().prop_map(|c| {
            ff().unary_expression(UnaryExprOp::UnMinus, c, None)
        }),
        1 => smaller().prop_map(|x| {
            ff().binary_expression(
                BinaryExprOp::FunImage,
                ff().free_identifier("f", None, None),
                x,
                None,
            )
        }),
        1 => set_expr(depth, size - 1).prop_map(|s| {
            ff().unary_expression(UnaryExprOp::KCard, s, None)
        }),
    ]
    .boxed()
}

/// Integer-set expressions over the base environment.
fn set_expr(depth: u32, size: u32) -> BoxedStrategy<Expression> {
    let leaf = Just(ff().free_identifier("s", None, None)).boxed();
    if size == 0 {
        return leaf;
    }
    let smaller = move || set_expr(depth, size - 1);
    prop_oneof![
        2 => leaf,
        1 => proptest::collection::vec(int_expr(depth, size - 1), 1..3)
            .prop_map(|members| ff().set_extension(members, None)),
        1 => (smaller(), smaller()).prop_map(|(l, r)| {
            ff().associative_expression(AssocExprOp::BUnion, vec![l, r], None)
        }),
        1 => (int_expr(depth, size - 1), int_expr(depth, size - 1)).prop_map(
            |(l, r)| ff().binary_expression(BinaryExprOp::UpTo, l, r, None)
        ),
        1 => Just(ff().unary_expression(
            UnaryExprOp::KDom,
            ff().free_identifier("f", None, None),
            None,
        )),
    ]
    .boxed()
}

/// Well-typeable predicates over the base environment.
fn pred(depth: u32, size: u32) -> BoxedStrategy<Predicate> {
    let comparison = (int_expr(depth, size), int_expr(depth, size)).prop_flat_map(|(l, r)| {
        prop_oneof![
            Just(RelationalOp::Equal),
            Just(RelationalOp::Lt),
            Just(RelationalOp::Ge),
        ]
        .prop_map(move |op| ff().relational_predicate(op, l.clone(), r.clone(), None))
    });
    let membership = (int_expr(depth, size), set_expr(depth, size))
        .prop_map(|(element, set)| ff().relational_predicate(RelationalOp::In, element, set, None));
    let leaf = prop_oneof![comparison, membership].boxed();
    if size == 0 {
        return leaf;
    }
    let smaller = move || pred(depth, size - 1);
    prop_oneof![
        3 => leaf,
        1 => proptest::collection::vec(smaller(), 2..4).prop_flat_map(|children| {
            prop_oneof![Just(AssocPredOp::LAnd), Just(AssocPredOp::LOr)].prop_map(
                move |op| ff().associative_predicate(op, children.clone(), None),
            )
        }),
        1 => (smaller(), smaller()).prop_map(|(l, r)| {
            ff().binary_predicate(BinaryPredOp::LImp, l, r, None)
        }),
        1 => smaller().prop_map(|c| ff().not_predicate(c, None)),
        1 => (1u32..3).prop_flat_map(move |n| {
            pred(depth + n, size - 1).prop_flat_map(move |body| {
                prop_oneof![Just(QuantPredOp::Forall), Just(QuantPredOp::Exists)]
                    .prop_map(move |op| {
                        let decls = (0..n)
                            .map(|i| {
                                ff().bound_ident_decl(
                                    format!("x{i}"),
                                    None,
                                    None,
                                    Some(Type::Int),
                                )
                            })
                            .collect();
                        ff().quantified_predicate(op, decls, body.clone(), None)
                    })
            })
        }),
    ]
    .boxed()
}

struct Identity;

impl FormulaRewriter for Identity {}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// An identity rewrite returns the same handle at the root.
    #[test]
    fn identity_rewrite_is_free(p in pred(0, 3)) {
        let rewritten = p.rewrite(&mut Identity);
        let a: *const rossi::formula::PredicateKind = p.kind();
        let b: *const rossi::formula::PredicateKind = rewritten.kind();
        prop_assert!(std::ptr::eq(a, b));
    }

    /// Flattening is idempotent.
    #[test]
    fn flatten_is_idempotent(p in pred(0, 3)) {
        let once = p.flatten();
        let twice = once.flatten();
        prop_assert_eq!(&once, &twice);
    }

    /// Every collected position resolves, and replacing a subformula
    /// with itself is the identity.
    #[test]
    fn positions_are_coherent(p in pred(0, 3)) {
        for position in p.positions(&mut |_| true) {
            let sub = p.sub_formula(&position);
            prop_assert!(sub.is_some(), "unresolvable position {}", position);
            let rewritten = p
                .rewrite_sub_formula(&position, sub.expect("resolved"))
                .expect("self-replacement fits");
            prop_assert_eq!(&rewritten, &p, "at {}", position);
        }
    }

    /// Shifting dangling indices up and back down is the identity.
    #[test]
    fn shift_round_trips(p in pred(2, 3), offset in 1i32..4) {
        let shifted = p.shift_bound_identifiers(offset);
        prop_assert_eq!(&shifted.shift_bound_identifiers(-offset), &p);
    }

    /// Equal formulas hash equally (spot-checked via substitution of a
    /// name by itself, which rebuilds the tree).
    #[test]
    fn equal_formulas_hash_equally(p in pred(0, 3)) {
        let map: HashMap<String, Expression> =
            [("a".to_string(), ff().free_identifier("a", None, None))]
                .into_iter()
                .collect();
        let rebuilt = p.substitute_free_idents(&map);
        prop_assert_eq!(&rebuilt, &p);
        prop_assert_eq!(hash_of(&rebuilt), hash_of(&p));
    }

    /// Generated formulas type-check, the typed rebuild is stable, and
    /// the WD lemma of a typed formula type-checks in the same
    /// environment.
    #[test]
    fn type_checking_and_wd_are_coherent(p in pred(0, 3)) {
        let environment = base_env();
        let result = p.type_check(&environment);
        prop_assert!(result.is_success(), "problems: {:?}", result.problems);
        let typed = result.typed.expect("typed");

        let again = typed.type_check(&environment);
        prop_assert!(again.is_success());
        prop_assert_eq!(&again.typed.expect("typed"), &typed);

        let lemma = typed.wd_lemma();
        let lemma_check = lemma.type_check(&environment);
        prop_assert!(
            lemma_check.is_success(),
            "lemma problems: {:?}",
            lemma_check.problems
        );
    }
}
