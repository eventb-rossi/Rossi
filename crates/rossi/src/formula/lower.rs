//! Lowering parsed formulas onto the typed model.
//!
//! The parser builds the name-bound legacy tree; this pass resolves
//! names to de Bruijn indices against a binder stack and produces the
//! equivalent formula-model tree, preserving spans and print forms.
//! It is the transitional bridge while the parser still targets the
//! legacy types, and is deleted with them.
//!
//! Scoping notes:
//! - `{E ∣ P}` binds: every identifier of `E` (first occurrence order)
//!   becomes a declaration of the comprehension, and `P` is scoped
//!   under them. The legacy tree left these occurrences free.
//! - A such-that action binds its primed identifiers: `x'` reads in
//!   the condition resolve to the primed declarations.
//! - Same-operator chains of associative operators flatten into one
//!   n-ary node.

use crate::ast::legacy::expression::{AtomicBuiltinKind, BinaryOp, UnaryOp};
use crate::ast::legacy::predicate::{ComparisonOp, LogicalOp, Quantifier};
use crate::ast::legacy::{
    self, ActionKind, BuiltinFunction, BuiltinPredicate, ExpressionKind, IdentPattern,
    PredicateKind, TypedIdentifier,
};

use super::assignment::Assignment;
use super::decl::BoundIdentDecl;
use super::expression::{Expression, Form};
use super::factory::FormulaFactory;
use super::predicate::Predicate;
use super::tag::{
    AssocExprOp, AssocPredOp, AtomicOp, BinaryExprOp, BinaryPredOp, LiteralPredOp, QuantExprOp,
    QuantPredOp, RelationalOp, UnaryExprOp,
};

/// Lowers a parsed predicate.
pub fn lower_predicate(pred: &legacy::Predicate) -> Predicate {
    Lowerer::new().pred(pred)
}

/// Lowers a parsed expression.
pub fn lower_expression(expr: &legacy::Expression) -> Expression {
    Lowerer::new().expr(expr)
}

/// Lowers a parsed action; `skip` has no formula and lowers to `None`.
pub fn lower_action(action: &legacy::Action) -> Option<Assignment> {
    Lowerer::new().action(action)
}

thread_local! {
    static SPAN_BASE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Runs `f` with the spans produced by the lowering shifted by `delta`
/// beyond the enclosing scope's shift. Used by error recovery, which
/// parses clause segments out of their document position: the legacy
/// tree keeps segment-relative spans and the lowering lifts them to
/// document coordinates.
pub fn with_span_base<T>(delta: usize, f: impl FnOnce() -> T) -> T {
    let previous = SPAN_BASE.with(|base| base.get());
    SPAN_BASE.with(|base| base.set(previous + delta));
    let result = f();
    SPAN_BASE.with(|base| base.set(previous));
    result
}

struct Lowerer {
    ff: FormulaFactory,
    /// Names in scope, innermost last.
    binders: Vec<String>,
    /// Added to every span copied off the legacy tree (see
    /// [`with_span_base`]); zero outside error recovery.
    base: usize,
}

impl Lowerer {
    fn new() -> Self {
        Lowerer {
            ff: FormulaFactory::default_factory(),
            binders: Vec::new(),
            base: SPAN_BASE.with(|base| base.get()),
        }
    }

    /// A legacy span lifted into the enclosing document's coordinates.
    fn at(&self, span: Option<crate::ast::Span>) -> Option<crate::ast::Span> {
        span.map(|s| crate::ast::Span {
            start: s.start + self.base,
            end: s.end + self.base,
        })
    }

    /// A name occurrence: bound if a binder is in scope, free otherwise.
    fn identifier(&self, name: &str, span: Option<crate::ast::Span>) -> Expression {
        match self.binders.iter().rev().position(|b| b == name) {
            Some(index) => self.ff.bound_identifier(index as u32, span, None),
            None => self.ff.free_identifier(name, span, None),
        }
    }

    fn decl(&mut self, ident: &TypedIdentifier) -> BoundIdentDecl {
        // Annotations are scoped to the enclosing context.
        let annotation = ident.type_expr.as_deref().map(|t| self.expr(t));
        self.ff
            .bound_ident_decl(&ident.name, self.at(ident.span), annotation, None)
    }

    fn decls(&mut self, idents: &[TypedIdentifier]) -> Vec<BoundIdentDecl> {
        idents.iter().map(|ident| self.decl(ident)).collect()
    }

    fn push(&mut self, names: impl IntoIterator<Item = String>) -> usize {
        let depth = self.binders.len();
        self.binders.extend(names);
        depth
    }

    fn expr(&mut self, e: &legacy::Expression) -> Expression {
        let span = self.at(e.span);
        match &e.kind {
            ExpressionKind::Integer(n) => self.ff.integer_literal(*n, span),
            ExpressionKind::Identifier(name) => self.identifier(name, span),
            ExpressionKind::True => self.ff.atomic_expression(AtomicOp::True, span, None),
            ExpressionKind::False => self.ff.atomic_expression(AtomicOp::False, span, None),
            ExpressionKind::EmptySet => self.ff.atomic_expression(AtomicOp::EmptySet, span, None),
            ExpressionKind::Naturals => self.ff.atomic_expression(AtomicOp::Natural, span, None),
            ExpressionKind::Naturals1 => self.ff.atomic_expression(AtomicOp::Natural1, span, None),
            ExpressionKind::Integers => self.ff.atomic_expression(AtomicOp::Integer, span, None),
            ExpressionKind::BoolType => self.ff.atomic_expression(AtomicOp::Bool, span, None),
            ExpressionKind::AtomicBuiltin(kind) => {
                let op = match kind {
                    AtomicBuiltinKind::Id => AtomicOp::KIdGen,
                    AtomicBuiltinKind::Prj1 => AtomicOp::KPrj1Gen,
                    AtomicBuiltinKind::Prj2 => AtomicOp::KPrj2Gen,
                    AtomicBuiltinKind::Pred => AtomicOp::KPred,
                    AtomicBuiltinKind::Succ => AtomicOp::KSucc,
                };
                self.ff.atomic_expression(op, span, None)
            }
            ExpressionKind::SetEnumeration(elements) => {
                if elements.is_empty() {
                    // An empty enumeration denotes the empty set.
                    return self.ff.atomic_expression(AtomicOp::EmptySet, span, None);
                }
                let members = elements.iter().map(|m| self.expr(m)).collect();
                self.ff.set_extension(members, span)
            }
            ExpressionKind::Bool(pred) => {
                let lowered = self.pred(pred);
                self.ff.bool_expression(lowered, span)
            }
            ExpressionKind::FunctionApplication { function, argument } => {
                let function = self.expr(function);
                let argument = self.expr(argument);
                self.ff
                    .binary_expression(BinaryExprOp::FunImage, function, argument, span)
            }
            ExpressionKind::RelationalImage { relation, set } => {
                let relation = self.expr(relation);
                let set = self.expr(set);
                self.ff
                    .binary_expression(BinaryExprOp::RelImage, relation, set, span)
            }
            ExpressionKind::BuiltinApplication { function, argument } => {
                let op = match function {
                    BuiltinFunction::Card => UnaryExprOp::KCard,
                    BuiltinFunction::Min => UnaryExprOp::KMin,
                    BuiltinFunction::Max => UnaryExprOp::KMax,
                    BuiltinFunction::Union => UnaryExprOp::KUnion,
                    BuiltinFunction::Inter => UnaryExprOp::KInter,
                };
                let argument = self.expr(argument);
                self.ff.unary_expression(op, argument, span)
            }
            ExpressionKind::Unary { op, operand } => {
                let new_op = match op {
                    UnaryOp::Minus => UnaryExprOp::UnMinus,
                    UnaryOp::PowerSet => UnaryExprOp::Pow,
                    UnaryOp::PowerSet1 => UnaryExprOp::Pow1,
                    UnaryOp::Domain => UnaryExprOp::KDom,
                    UnaryOp::Range => UnaryExprOp::KRan,
                    UnaryOp::Inverse => UnaryExprOp::Converse,
                };
                let operand = self.expr(operand);
                self.ff.unary_expression(new_op, operand, span)
            }
            ExpressionKind::Binary { op, left, right } => {
                if *op == BinaryOp::OfType {
                    let expr = self.expr(left);
                    let type_expr = self.expr(right);
                    return self.ff.ascription(expr, type_expr, span);
                }
                if let Some(assoc) = assoc_of(*op) {
                    // Flatten the parser's left-nested same-operator
                    // chain into one n-ary node.
                    let mut children = Vec::new();
                    self.collect_assoc(*op, left, &mut children);
                    children.push(self.expr(right));
                    return self.ff.associative_expression(assoc, children, span);
                }
                let new_op = binary_of(*op);
                let left = self.expr(left);
                let right = self.expr(right);
                self.ff.binary_expression(new_op, left, right, span)
            }
            ExpressionKind::SetComprehension {
                identifiers,
                predicate,
                expression,
            } => {
                let decls = self.decls(identifiers);
                let names: Vec<String> = identifiers.iter().map(|i| i.name.clone()).collect();
                let count = names.len();
                let depth = self.push(names);
                let (value, form) = match expression {
                    Some(expression) => (self.expr(expression), Form::Explicit),
                    None => (self.ident_chain(count), Form::IdentList),
                };
                let pred = self.pred(predicate);
                self.binders.truncate(depth);
                self.ff
                    .quantified_expression(QuantExprOp::CSet, decls, pred, value, span, form)
            }
            ExpressionKind::SetBuilder {
                member_expression,
                predicate,
            } => {
                // Every identifier free in the member expression becomes
                // a declaration, in first-occurrence order. Occurrences
                // already bound by an enclosing binder stay references
                // to it — the member expression is read in the enclosing
                // scope, and only what is free there gets bound.
                let mut names: Vec<String> = Vec::new();
                collect_identifiers(member_expression, &mut names);
                names.retain(|name| !self.binders.contains(name));
                let decls: Vec<BoundIdentDecl> = names
                    .iter()
                    .map(|name| self.ff.bound_ident_decl(name, None, None, None))
                    .collect();
                let depth = self.push(names.iter().cloned());
                let value = self.expr(member_expression);
                let pred = self.pred(predicate);
                self.binders.truncate(depth);
                self.ff.quantified_expression(
                    QuantExprOp::CSet,
                    decls,
                    pred,
                    value,
                    span,
                    Form::Implicit,
                )
            }
            ExpressionKind::Lambda {
                pattern,
                predicate,
                expression,
            } => {
                let mut leaves = Vec::new();
                pattern_leaves(pattern, &mut leaves);
                let decls: Vec<BoundIdentDecl> =
                    leaves.iter().map(|leaf| self.decl(leaf)).collect();
                let names: Vec<String> = leaves.iter().map(|l| l.name.clone()).collect();
                let depth = self.push(names);
                let pattern_expr = self.pattern_expr(pattern);
                let body = self.expr(expression);
                let pred = self.pred(predicate);
                self.binders.truncate(depth);
                let value =
                    self.ff
                        .binary_expression(BinaryExprOp::Mapsto, pattern_expr, body, None);
                self.ff.quantified_expression(
                    QuantExprOp::CSet,
                    decls,
                    pred,
                    value,
                    span,
                    Form::Lambda,
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
                let op = if matches!(e.kind, ExpressionKind::QuantifiedUnion { .. }) {
                    QuantExprOp::QUnion
                } else {
                    QuantExprOp::QInter
                };
                let decls = self.decls(identifiers);
                let names: Vec<String> = identifiers.iter().map(|i| i.name.clone()).collect();
                let depth = self.push(names);
                let pred = self.pred(predicate);
                let value = self.expr(expression);
                self.binders.truncate(depth);
                self.ff
                    .quantified_expression(op, decls, pred, value, span, Form::Explicit)
            }
        }
    }

    /// Collects the left spine of a same-operator chain, lowering each
    /// leaf.
    fn collect_assoc(&mut self, op: BinaryOp, e: &legacy::Expression, out: &mut Vec<Expression>) {
        if let ExpressionKind::Binary {
            op: child_op,
            left,
            right,
        } = &e.kind
        {
            if *child_op == op {
                self.collect_assoc(op, left, out);
                out.push(self.expr(right));
                return;
            }
        }
        out.push(self.expr(e));
    }

    /// The canonical left-nested maplet chain of the last `count`
    /// declarations (for the ident-list comprehension form).
    fn ident_chain(&self, count: usize) -> Expression {
        let mut chain = self.ff.bound_identifier(count as u32 - 1, None, None);
        for index in (0..count - 1).rev() {
            let right = self.ff.bound_identifier(index as u32, None, None);
            chain = self
                .ff
                .binary_expression(BinaryExprOp::Mapsto, chain, right, None);
        }
        chain
    }

    /// A lambda pattern as an expression over the bound declarations.
    fn pattern_expr(&mut self, pattern: &IdentPattern) -> Expression {
        match pattern {
            IdentPattern::Identifier(ident) => self.identifier(&ident.name, self.at(ident.span)),
            IdentPattern::Maplet(left, right) => {
                let left = self.pattern_expr(left);
                let right = self.pattern_expr(right);
                self.ff
                    .binary_expression(BinaryExprOp::Mapsto, left, right, None)
            }
        }
    }

    fn pred(&mut self, p: &legacy::Predicate) -> Predicate {
        let span = self.at(p.span);
        match &p.kind {
            PredicateKind::True => self.ff.literal_predicate(LiteralPredOp::BTrue, span),
            PredicateKind::False => self.ff.literal_predicate(LiteralPredOp::BFalse, span),
            PredicateKind::Comparison { op, left, right } => {
                let new_op = match op {
                    ComparisonOp::Equal => RelationalOp::Equal,
                    ComparisonOp::NotEqual => RelationalOp::NotEqual,
                    ComparisonOp::LessThan => RelationalOp::Lt,
                    ComparisonOp::LessEqual => RelationalOp::Le,
                    ComparisonOp::GreaterThan => RelationalOp::Gt,
                    ComparisonOp::GreaterEqual => RelationalOp::Ge,
                    ComparisonOp::In => RelationalOp::In,
                    ComparisonOp::NotIn => RelationalOp::NotIn,
                    // The legacy names use `Subset` for the inclusive
                    // operator; the model reserves it for the strict one.
                    ComparisonOp::Subset => RelationalOp::SubsetEq,
                    ComparisonOp::NotSubset => RelationalOp::NotSubsetEq,
                    ComparisonOp::SubsetStrict => RelationalOp::Subset,
                    ComparisonOp::NotSubsetStrict => RelationalOp::NotSubset,
                };
                let left = self.expr(left);
                let right = self.expr(right);
                self.ff.relational_predicate(new_op, left, right, span)
            }
            PredicateKind::Not(inner) => {
                let inner = self.pred(inner);
                self.ff.not_predicate(inner, span)
            }
            PredicateKind::Logical { op, left, right } => match op {
                LogicalOp::And | LogicalOp::Or => {
                    let assoc = if *op == LogicalOp::And {
                        AssocPredOp::LAnd
                    } else {
                        AssocPredOp::LOr
                    };
                    let mut children = Vec::new();
                    self.collect_logical(*op, left, &mut children);
                    children.push(self.pred(right));
                    self.ff.associative_predicate(assoc, children, span)
                }
                LogicalOp::Implies | LogicalOp::Equivalent => {
                    let new_op = if *op == LogicalOp::Implies {
                        BinaryPredOp::LImp
                    } else {
                        BinaryPredOp::LEqv
                    };
                    let left = self.pred(left);
                    let right = self.pred(right);
                    self.ff.binary_predicate(new_op, left, right, span)
                }
            },
            PredicateKind::Quantified {
                quantifier,
                identifiers,
                predicate,
            } => {
                let op = match quantifier {
                    Quantifier::ForAll => QuantPredOp::Forall,
                    Quantifier::Exists => QuantPredOp::Exists,
                };
                let decls = self.decls(identifiers);
                let names: Vec<String> = identifiers.iter().map(|i| i.name.clone()).collect();
                let depth = self.push(names);
                let body = self.pred(predicate);
                self.binders.truncate(depth);
                self.ff.quantified_predicate(op, decls, body, span)
            }
            PredicateKind::Application {
                function,
                arguments,
            } => {
                let args = arguments.iter().map(|a| self.expr(a)).collect();
                self.ff
                    .predicate_application(&function.name, self.at(function.span), args, span)
            }
            PredicateKind::BuiltinApplication {
                predicate,
                arguments,
            } => match predicate {
                BuiltinPredicate::Finite => {
                    let arg = self.expr(&arguments[0]);
                    self.ff.simple_predicate(arg, span)
                }
                BuiltinPredicate::Partition => {
                    let args = arguments.iter().map(|a| self.expr(a)).collect();
                    self.ff.multiple_predicate(args, span)
                }
            },
        }
    }

    fn collect_logical(&mut self, op: LogicalOp, p: &legacy::Predicate, out: &mut Vec<Predicate>) {
        if let PredicateKind::Logical {
            op: child_op,
            left,
            right,
        } = &p.kind
        {
            if *child_op == op {
                self.collect_logical(op, left, out);
                out.push(self.pred(right));
                return;
            }
        }
        out.push(self.pred(p));
    }

    fn action(&mut self, a: &legacy::Action) -> Option<Assignment> {
        let span = self.at(a.span);
        match &a.kind {
            ActionKind::Skip => None,
            ActionKind::Assignment { assignments } => {
                let idents = assignments
                    .iter()
                    .map(|(ident, _)| {
                        self.ff
                            .free_identifier(ident.as_str(), self.at(ident.span), None)
                    })
                    .collect();
                let values = assignments
                    .iter()
                    .map(|(_, value)| self.expr(value))
                    .collect();
                Some(self.ff.becomes_equal_to(idents, values, span))
            }
            ActionKind::BecomesIn { variables, set } => {
                let idents = variables
                    .iter()
                    .map(|ident| {
                        self.ff
                            .free_identifier(ident.as_str(), self.at(ident.span), None)
                    })
                    .collect();
                let set = self.expr(set);
                Some(self.ff.becomes_member_of(idents, set, span))
            }
            ActionKind::BecomesSuchThat {
                variables,
                predicate,
            } => {
                let idents: Vec<Expression> = variables
                    .iter()
                    .map(|ident| {
                        self.ff
                            .free_identifier(ident.as_str(), self.at(ident.span), None)
                    })
                    .collect();
                let primed: Vec<BoundIdentDecl> = variables
                    .iter()
                    .map(|ident| {
                        self.ff
                            .bound_ident_decl(format!("{}'", ident.as_str()), None, None, None)
                    })
                    .collect();
                let names: Vec<String> = primed.iter().map(|d| d.name().to_string()).collect();
                let depth = self.push(names);
                let pred = self.pred(predicate);
                self.binders.truncate(depth);
                Some(self.ff.becomes_such_that(idents, primed, pred, span))
            }
        }
    }
}

fn binary_of(op: BinaryOp) -> BinaryExprOp {
    match op {
        BinaryOp::Subtract => BinaryExprOp::Minus,
        BinaryOp::Divide => BinaryExprOp::Div,
        BinaryOp::Modulo => BinaryExprOp::Mod,
        BinaryOp::Exponent => BinaryExprOp::Expn,
        BinaryOp::Range => BinaryExprOp::UpTo,
        BinaryOp::Difference => BinaryExprOp::SetMinus,
        BinaryOp::CartesianProduct => BinaryExprOp::CProd,
        BinaryOp::Relation => BinaryExprOp::Rel,
        BinaryOp::TotalRelation => BinaryExprOp::TRel,
        BinaryOp::SurjectiveRelation => BinaryExprOp::SRel,
        BinaryOp::TotalSurjectiveRelation => BinaryExprOp::STRel,
        BinaryOp::TotalFunction => BinaryExprOp::TFun,
        BinaryOp::PartialFunction => BinaryExprOp::PFun,
        BinaryOp::TotalInjection => BinaryExprOp::TInj,
        BinaryOp::PartialInjection => BinaryExprOp::PInj,
        BinaryOp::TotalSurjection => BinaryExprOp::TSur,
        BinaryOp::PartialSurjection => BinaryExprOp::PSur,
        BinaryOp::Bijection => BinaryExprOp::TBij,
        BinaryOp::DomainRestriction => BinaryExprOp::DomRes,
        BinaryOp::DomainSubtraction => BinaryExprOp::DomSub,
        BinaryOp::RangeRestriction => BinaryExprOp::RanRes,
        BinaryOp::RangeSubtraction => BinaryExprOp::RanSub,
        BinaryOp::DirectProduct => BinaryExprOp::DProd,
        BinaryOp::ParallelProduct => BinaryExprOp::PProd,
        BinaryOp::Maplet => BinaryExprOp::Mapsto,
        BinaryOp::Add
        | BinaryOp::Multiply
        | BinaryOp::Union
        | BinaryOp::Intersection
        | BinaryOp::Overwrite
        | BinaryOp::Composition
        | BinaryOp::Semicolon
        | BinaryOp::OfType => unreachable!("handled before the binary mapping"),
    }
}

fn assoc_of(op: BinaryOp) -> Option<AssocExprOp> {
    match op {
        BinaryOp::Add => Some(AssocExprOp::Plus),
        BinaryOp::Multiply => Some(AssocExprOp::Mul),
        BinaryOp::Union => Some(AssocExprOp::BUnion),
        BinaryOp::Intersection => Some(AssocExprOp::BInter),
        BinaryOp::Overwrite => Some(AssocExprOp::Ovr),
        BinaryOp::Composition => Some(AssocExprOp::BComp),
        BinaryOp::Semicolon => Some(AssocExprOp::FComp),
        _ => None,
    }
}

/// Identifier names of an expression, first occurrence order, deduped.
fn collect_identifiers(e: &legacy::Expression, out: &mut Vec<String>) {
    use std::ops::ControlFlow;

    struct Collector<'a> {
        out: &'a mut Vec<String>,
    }
    impl legacy::walk::IdentVisitor for Collector<'_> {
        fn visit(&mut self, occ: legacy::walk::IdentOccurrence<'_>) -> ControlFlow<()> {
            // Only identifiers free within the expression: skip reads
            // that resolve to a binder nested inside it.
            if occ.role == legacy::walk::IdentRole::Usage
                && !occ.binders.iter().any(|b| b.name == occ.name)
                && !self.out.iter().any(|n| n == occ.name)
            {
                self.out.push(occ.name.to_string());
            }
            ControlFlow::Continue(())
        }
    }
    let _ = legacy::walk::walk_expression(e, &mut Vec::new(), &mut Collector { out });
}

/// Lower an action onto the surface [`ActionBody`]: `skip` stays the
/// explicit no-op, everything else becomes a modelled assignment.
pub fn lower_action_body(action: &legacy::Action) -> crate::ast::ActionBody {
    match lower_action(action) {
        Some(assignment) => crate::ast::ActionBody::Assignment(assignment),
        None => crate::ast::ActionBody::Skip,
    }
}

/// The pattern's leaves, left to right.
fn pattern_leaves<'a>(pattern: &'a IdentPattern, out: &mut Vec<&'a TypedIdentifier>) {
    match pattern {
        IdentPattern::Identifier(ident) => out.push(ident),
        IdentPattern::Maplet(left, right) => {
            pattern_leaves(left, out);
            pattern_leaves(right, out);
        }
    }
}
