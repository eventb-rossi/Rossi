//! Simplifying constructors for well-definedness lemmas.
//!
//! Lemmas are built through these helpers so the obvious tautologies
//! never materialize: `⊤` is dropped from conjunctions, an implication
//! of `⊤` (or of itself) collapses, right-nested implications curry
//! into a conjunction of hypotheses, and a quantifier over `⊤` is `⊤`.

use super::super::decl::BoundIdentDecl;
use super::super::expression::Expression;
use super::super::factory::FormulaFactory;
use super::super::predicate::{Predicate, PredicateKind};
use super::super::tag::{
    self, BinaryExprOp, BinaryPredOp, LiteralPredOp, QuantPredOp, RelationalOp, UnaryExprOp,
};
use super::super::types::Type;

pub(super) struct FormulaBuilder {
    pub(super) ff: FormulaFactory,
    btrue: Predicate,
}

pub(super) fn is_btrue(p: &Predicate) -> bool {
    p.tag() == tag::FIRST_LITERAL_PREDICATE
}

impl FormulaBuilder {
    pub(super) fn new(ff: FormulaFactory) -> Self {
        let btrue = ff.literal_predicate(LiteralPredOp::BTrue, None);
        FormulaBuilder { ff, btrue }
    }

    pub(super) fn btrue(&self) -> Predicate {
        self.btrue.clone()
    }

    /// Simplified binary conjunction: `⊤` is neutral.
    pub(super) fn land(&self, left: Predicate, right: Predicate) -> Predicate {
        if is_btrue(&left) {
            return right;
        }
        if is_btrue(&right) {
            return left;
        }
        self.ff
            .associative_predicate(tag::AssocPredOp::LAnd, vec![left, right], None)
    }

    /// Simplified n-ary conjunction.
    pub(super) fn land_all(&self, children: impl IntoIterator<Item = Predicate>) -> Predicate {
        let mut conjuncts: Vec<Predicate> = children.into_iter().filter(|c| !is_btrue(c)).collect();
        match conjuncts.len() {
            0 => self.btrue(),
            1 => conjuncts.pop().expect("one conjunct"),
            _ => self
                .ff
                .associative_predicate(tag::AssocPredOp::LAnd, conjuncts, None),
        }
    }

    /// Simplified implication: `⊤` hypotheses and conclusions vanish,
    /// `P ⇒ P` is `⊤`, and `A ⇒ (B ⇒ C)` curries to `A ∧ B ⇒ C`.
    pub(super) fn limp(&self, left: Predicate, right: Predicate) -> Predicate {
        if is_btrue(&left) || is_btrue(&right) {
            return right;
        }
        if let PredicateKind::Binary {
            op: BinaryPredOp::LImp,
            left: hypothesis,
            right: conclusion,
        } = right.kind()
        {
            let curried = self.land(left, hypothesis.clone());
            return self.limp(curried, conclusion.clone());
        }
        if left == right {
            return self.btrue();
        }
        self.ff
            .binary_predicate(BinaryPredOp::LImp, left, right, None)
    }

    /// Simplified disjunction: `⊤` absorbs.
    pub(super) fn lor(&self, left: Predicate, right: Predicate) -> Predicate {
        if is_btrue(&left) {
            return left;
        }
        if is_btrue(&right) {
            return right;
        }
        self.ff
            .associative_predicate(tag::AssocPredOp::LOr, vec![left, right], None)
    }

    /// `∀ decls · pred`, unless the body is `⊤`.
    pub(super) fn forall(&self, decls: Vec<BoundIdentDecl>, pred: Predicate) -> Predicate {
        if is_btrue(&pred) {
            return pred;
        }
        self.ff
            .quantified_predicate(QuantPredOp::Forall, decls, pred, None)
    }

    /// `∃ decls · pred`, unless the body is `⊤`.
    pub(super) fn exists(&self, decls: Vec<BoundIdentDecl>, pred: Predicate) -> Predicate {
        if is_btrue(&pred) {
            return pred;
        }
        self.ff
            .quantified_predicate(QuantPredOp::Exists, decls, pred, None)
    }

    fn zero(&self) -> Expression {
        self.ff.integer_literal(0, None)
    }

    /// `expr ≠ 0`
    pub(super) fn not_zero(&self, expr: Expression) -> Predicate {
        let zero = self.zero();
        self.ff
            .relational_predicate(RelationalOp::NotEqual, expr, zero, None)
    }

    /// `0 ≤ expr`
    pub(super) fn non_negative(&self, expr: Expression) -> Predicate {
        let zero = self.zero();
        self.ff
            .relational_predicate(RelationalOp::Le, zero, expr, None)
    }

    /// `0 < expr`
    pub(super) fn positive(&self, expr: Expression) -> Predicate {
        let zero = self.zero();
        self.ff
            .relational_predicate(RelationalOp::Lt, zero, expr, None)
    }

    /// `finite(expr)`
    pub(super) fn finite(&self, expr: Expression) -> Predicate {
        self.ff.simple_predicate(expr, None)
    }

    /// `expr ≠ ∅`, with the empty set typed like `expr`.
    pub(super) fn not_empty(&self, expr: Expression) -> Predicate {
        let ty = expr.ty().expect("well-definedness needs types").clone();
        let empty = self
            .ff
            .atomic_expression(tag::AtomicOp::EmptySet, None, Some(ty));
        self.ff
            .relational_predicate(RelationalOp::NotEqual, expr, empty, None)
    }

    /// `expr ∈ dom(fun)`
    pub(super) fn in_domain(&self, fun: Expression, expr: Expression) -> Predicate {
        let dom = self.ff.unary_expression(UnaryExprOp::KDom, fun, None);
        self.ff
            .relational_predicate(RelationalOp::In, expr, dom, None)
    }

    /// `fun ∈ S ⇸ T`, with `S` and `T` spelled from `fun`'s type.
    pub(super) fn partial(&self, fun: Expression) -> Predicate {
        let ty = fun.ty().expect("well-definedness needs types");
        let source = ty.source().expect("a function has a relational type");
        let target = ty.target().expect("a function has a relational type");
        let pfun = self.ff.binary_expression(
            BinaryExprOp::PFun,
            source.to_expression(&self.ff),
            target.to_expression(&self.ff),
            None,
        );
        self.ff
            .relational_predicate(RelationalOp::In, fun, pfun, None)
    }

    /// `∃b · ∀x · x ∈ set ⇒ b ≤ x` (lower bound) or `… b ≥ x` (upper).
    pub(super) fn bounded(&self, set: Expression, lower: bool) -> Predicate {
        let b = self.ff.bound_identifier(1, None, Some(Type::Int));
        let x = self.ff.bound_identifier(0, None, Some(Type::Int));
        let op = if lower {
            RelationalOp::Le
        } else {
            RelationalOp::Ge
        };
        let rel = self.ff.relational_predicate(op, b, x.clone(), None);
        let x_in_set =
            self.ff
                .relational_predicate(RelationalOp::In, x, set.shift_bound_identifiers(2), None);
        // Built directly: the implication must stay explicit here.
        let body = self
            .ff
            .binary_predicate(BinaryPredOp::LImp, x_in_set, rel, None);
        let x_decl = self.ff.bound_ident_decl("x", None, None, Some(Type::Int));
        let inner = self
            .ff
            .quantified_predicate(QuantPredOp::Forall, vec![x_decl], body, None);
        let b_decl = self.ff.bound_ident_decl("b", None, None, Some(Type::Int));
        self.ff
            .quantified_predicate(QuantPredOp::Exists, vec![b_decl], inner, None)
    }
}
