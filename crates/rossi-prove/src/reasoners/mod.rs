//! Reasoner implementations, keyed by the registry.
//!
//! Each implemented reasoner re-derives its rule from a sequent and
//! the stored rule (the input-recovery bridge: anything the storage
//! does not serialize explicitly is recovered from the recorded
//! rule). The table below is the replay counterpart of the registry:
//! only trusted descriptors resolve, so a version-conflicting or
//! unknown reasoner never replays.

pub(crate) mod auto_rewriter;
pub(crate) mod driver;
pub(crate) mod genmp;
pub mod inference;
pub(crate) mod manual;
pub(crate) mod one_point;
pub mod rewrites;
pub mod structural;

use rossi::formula::tag::AssocPredOp;
use rossi::formula::{
    BoundIdentDecl, Expression, FreshNameSolver, Predicate, PredicateKind, SealedTypeEnvironment,
};
use rossi::pretty::PrettyPrinter;

use crate::builder::Reasoner;
use crate::registry::ReasonerDesc;
use crate::sequent::TypedIdent;

/// The `autoRewritesL5` rewriter fixpoint on a single predicate —
/// exactly the rewriting the fixpoint pass iterates, without the
/// surrounding rule construction. `None` when the first pass changes
/// nothing. Public for harnesses diffing the rewriter against a live
/// reference one.
pub fn auto_rewrite_fixpoint(pred: &Predicate) -> Option<Predicate> {
    driver::recursive_rewrite(pred, &mut auto_rewriter::AutoRewriter)
}

/// The implementation for `desc`, when the descriptor is trusted and a
/// Rust implementation exists at its version.
pub fn implementation(desc: &ReasonerDesc) -> Option<&'static dyn Reasoner> {
    if !desc.is_trusted() {
        return None;
    }
    let short = desc.id().strip_prefix("org.eventb.core.seqprover.")?;
    let imp: &'static dyn Reasoner = match short {
        "trueGoal" => &structural::TrueGoal,
        "falseHyp" => &structural::FalseHyp,
        "hyp" => &structural::Hyp,
        "impI" => &structural::ImpI,
        "allI" => &structural::AllI,
        "conj" => &structural::Conj,
        "contrHyps" => &structural::ContrHyps,
        "review" => &structural::Review,
        "mngHyp" => &structural::MngHyp,
        "exI" => &inference::ExI,
        "cut" => &inference::Cut,
        "doCase" => &inference::DoCase,
        "disjE" => &inference::DisjE,
        "impE" => &inference::ImpE,
        "mt" => &inference::ModusTollens,
        "exF" => &inference::ExF,
        "exE" => &inference::ExE,
        "eqL2" => &inference::EqL2,
        "heL2" => &inference::HeL2,
        "autoImpE" => &inference::AutoImpE,
        "negEnum" => &inference::NegEnum,
        "allD" => &inference::AllD,
        "allmpD" => &inference::AllmpD,
        "allmtD" => &inference::AllmtD,
        "typeRewrites" => &rewrites::TypeRewrites,
        "autoRewritesL5" => &auto_rewriter::AutoRewritesL5,
        "genMPL4" => &genmp::GenMPL4,
        "partitionRewrites" => &manual::PartitionRewrites,
        "funImgSimplifies" => &manual::FunImgSimplifies,
        "totalDom" => &manual::TotalDom,
        "funImgGoal" => &manual::FunImageGoal,
        "rn" => &manual::RemoveNegation,
        "rmL1" => &manual::RemoveMembershipL1,
        "funOvr" => &manual::FunOvr,
        "onePointRule" => &inference::OnePointRule,
        "isFunGoal" => &structural::IsFunGoal,
        "finiteHypBoundedGoal" => &structural::FiniteHypBoundedGoal,
        "hypOr" => &structural::HypOr,
        "finiteSetMinus" => &structural::FiniteSetMinus,
        "finiteInter" => &structural::FiniteInter,
        "finiteSet" => &inference::FiniteSet,
        "conjF" => &inference::ConjF,
        "ri" => &manual::RemoveInclusion,
        "eqvRewrites" => &manual::EqvRewrites,
        "relImgUnionRightRewrites" => &manual::RelImgUnionRight,
        "disjToImplRewrites" => &manual::DisjToImpl,
        "funSingletonImg" => &manual::FunSingletonImg,
        "locEq" => &manual::LocalEq,
        _ => return None,
    };
    Some(imp)
}

/// A literal value, seeing through the unary minus this crate's
/// parse-normal form keeps (the reference parser folds them).
pub(crate) fn as_literal(expr: &Expression) -> Option<num_bigint::BigInt> {
    use rossi::formula::ExpressionKind;
    use rossi::formula::tag::UnaryExprOp;
    match expr.kind() {
        ExpressionKind::IntegerLiteral(value) => Some(value.clone()),
        ExpressionKind::Unary {
            op: UnaryExprOp::UnMinus,
            child,
        } => match child.kind() {
            ExpressionKind::IntegerLiteral(value) => Some(-value.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// `rewrite_sub_formula` followed by the round-trip normalization
/// every produced rule needs: a replacement product can violate the
/// print→parse shape stored rules exist in (see [`as_parsed_pred`]),
/// so a rewrite-at-position must never escape unnormalized.
pub(crate) fn rewrite_at(
    pred: &Predicate,
    position: &rossi::formula::position::Position,
    replacement: rossi::formula::position::FormulaRef<'_>,
) -> Result<Predicate, rossi::formula::position::PositionError> {
    let rewritten = pred.rewrite_sub_formula(position, replacement)?;
    Ok(as_parsed_pred(&rewritten).unwrap_or(rewritten))
}

/// Negate, removing an existing negation. One shared helper.
pub(crate) fn make_neg(pred: &Predicate) -> Predicate {
    if let PredicateKind::Not(inner) = pred.kind() {
        return inner.clone();
    }
    pred.factory().not_predicate(pred.clone(), None)
}

/// The conjuncts of a conjunction (or the
/// predicate itself), duplicates removed keeping first positions.
pub(crate) fn break_possible_conjunct(pred: &Predicate) -> Vec<Predicate> {
    let conjuncts: Vec<Predicate> = match pred.kind() {
        PredicateKind::Associative {
            op: AssocPredOp::LAnd,
            children,
        } => children.clone(),
        _ => vec![pred.clone()],
    };
    dedup_preserving_order(conjuncts)
}

/// The print→parse round-trip shape of a formula: an associative
/// node's same-operator FIRST child prints without parentheses, so
/// its left spine merges into the run on re-parsing, while later
/// same-operator children keep their parentheses. Formulas parsed
/// from stored output are already in this shape; substitution and
/// position-replacement products may not be, and stored rules only
/// exist post-round-trip. `None` means already normal. Contrast
/// `inference::parse_normal`, which models the constructor-level
/// flattening (every same-operator child merges) for instantiation
/// products.
pub(crate) fn as_parsed_pred(pred: &Predicate) -> Option<Predicate> {
    use rossi::formula::PredicateKind;
    let ff = pred.factory().clone();
    match pred.kind() {
        PredicateKind::Literal(_)
        | PredicateKind::PredicateVariable(_)
        | PredicateKind::Application { .. }
        | PredicateKind::Extended { .. } => None,
        PredicateKind::Not(child) => as_parsed_pred(child).map(|p| ff.not_predicate(p, None)),
        PredicateKind::Binary { op, left, right } => {
            let l = as_parsed_pred(left);
            let r = as_parsed_pred(right);
            (l.is_some() || r.is_some()).then(|| {
                ff.binary_predicate(
                    *op,
                    l.unwrap_or_else(|| left.clone()),
                    r.unwrap_or_else(|| right.clone()),
                    None,
                )
            })
        }
        PredicateKind::Associative { op, children } => {
            let mut out: Vec<Predicate> = Vec::with_capacity(children.len());
            let mut changed = false;
            for child in children {
                match as_parsed_pred(child) {
                    Some(c) => {
                        changed = true;
                        out.push(c);
                    }
                    None => out.push(child.clone()),
                }
            }
            while let Some(first) = out.first().cloned() {
                let PredicateKind::Associative {
                    op: inner,
                    children: nested,
                } = first.kind()
                else {
                    break;
                };
                if inner != op {
                    break;
                }
                changed = true;
                let mut merged = nested.clone();
                merged.extend(out.drain(1..));
                out = merged;
            }
            changed.then(|| ff.associative_predicate(*op, out, None))
        }
        PredicateKind::Quantified {
            op,
            decls,
            pred: body,
        } => as_parsed_pred(body).map(|p| ff.quantified_predicate(*op, decls.clone(), p, None)),
        PredicateKind::Relational { op, left, right } => {
            let l = as_parsed_expr(left);
            let r = as_parsed_expr(right);
            (l.is_some() || r.is_some()).then(|| {
                ff.relational_predicate(
                    *op,
                    l.unwrap_or_else(|| left.clone()),
                    r.unwrap_or_else(|| right.clone()),
                    None,
                )
            })
        }
        PredicateKind::Simple(child) => as_parsed_expr(child).map(|e| ff.simple_predicate(e, None)),
        PredicateKind::Multiple(children) => {
            let mut out: Vec<Expression> = Vec::with_capacity(children.len());
            let mut changed = false;
            for child in children {
                match as_parsed_expr(child) {
                    Some(c) => {
                        changed = true;
                        out.push(c);
                    }
                    None => out.push(child.clone()),
                }
            }
            changed.then(|| ff.multiple_predicate(out, None))
        }
    }
}

/// See [`as_parsed_pred`].
pub(crate) fn as_parsed_expr(expr: &Expression) -> Option<Expression> {
    use rossi::formula::ExpressionKind;
    let ff = expr.factory().clone();
    match expr.kind() {
        ExpressionKind::FreeIdentifier(_)
        | ExpressionKind::BoundIdentifier(_)
        | ExpressionKind::IntegerLiteral(_)
        | ExpressionKind::Atomic(_)
        | ExpressionKind::Ascription { .. }
        | ExpressionKind::Extended { .. } => None,
        ExpressionKind::SetExtension(members) => {
            let mut out: Vec<Expression> = Vec::with_capacity(members.len());
            let mut changed = false;
            for member in members {
                match as_parsed_expr(member) {
                    Some(m) => {
                        changed = true;
                        out.push(m);
                    }
                    None => out.push(member.clone()),
                }
            }
            changed.then(|| ff.set_extension(out, None))
        }
        ExpressionKind::Bool(pred) => as_parsed_pred(pred).map(|p| ff.bool_expression(p, None)),
        ExpressionKind::Binary { op, left, right } => {
            let l = as_parsed_expr(left);
            let r = as_parsed_expr(right);
            (l.is_some() || r.is_some()).then(|| {
                ff.binary_expression(
                    *op,
                    l.unwrap_or_else(|| left.clone()),
                    r.unwrap_or_else(|| right.clone()),
                    None,
                )
            })
        }
        ExpressionKind::Associative { op, children } => {
            let mut out: Vec<Expression> = Vec::with_capacity(children.len());
            let mut changed = false;
            for child in children {
                match as_parsed_expr(child) {
                    Some(c) => {
                        changed = true;
                        out.push(c);
                    }
                    None => out.push(child.clone()),
                }
            }
            while let Some(first) = out.first().cloned() {
                let ExpressionKind::Associative {
                    op: inner,
                    children: nested,
                } = first.kind()
                else {
                    break;
                };
                if inner != op {
                    break;
                }
                changed = true;
                let mut merged = nested.clone();
                merged.extend(out.drain(1..));
                out = merged;
            }
            changed.then(|| ff.associative_expression(*op, out, None))
        }
        ExpressionKind::Unary { op, child } => {
            as_parsed_expr(child).map(|e| ff.unary_expression(*op, e, None))
        }
        ExpressionKind::Quantified {
            op,
            decls,
            pred,
            expr: value,
            form,
        } => {
            let p = as_parsed_pred(pred);
            let v = as_parsed_expr(value);
            (p.is_some() || v.is_some()).then(|| {
                ff.quantified_expression(
                    *op,
                    decls.clone(),
                    p.unwrap_or_else(|| pred.clone()),
                    v.unwrap_or_else(|| value.clone()),
                    None,
                    *form,
                )
            })
        }
    }
}

/// The component binder: one declaration per scalar
/// component of a set's element type — a maplet pattern mirrors a
/// product — with the set shifted under the new binder. The reference
/// names
/// every declaration `x` and lets its serializer resolve clashes; the
/// names here follow that resolution against the set's free
/// identifiers, which is what the stored round-trip carries. Returns
/// (declarations, pattern, shifted set).
pub(crate) fn component_binder(
    set: &Expression,
) -> Option<(Vec<BoundIdentDecl>, Expression, Expression)> {
    use rossi::formula::Type;
    let ff = set.factory();
    let Some(Type::Pow(element)) = set.ty() else {
        return None;
    };
    fn count(ty: &Type) -> u32 {
        match ty {
            Type::Prod(left, right) => count(left) + count(right),
            _ => 1,
        }
    }
    fn decls_for(
        ff: &rossi::formula::FormulaFactory,
        ty: &Type,
        solver: &mut FreshNameSolver,
        out: &mut Vec<BoundIdentDecl>,
    ) {
        match ty {
            Type::Prod(left, right) => {
                decls_for(ff, left, solver, out);
                decls_for(ff, right, solver, out);
            }
            _ => {
                let name = solver.solve_and_add("x");
                out.push(ff.bound_ident_decl(&name, None, None, Some(ty.clone())));
            }
        }
    }
    let n = count(element);
    let mut solver = FreshNameSolver::new(set.free_identifiers().iter().cloned());
    let mut decls = Vec::with_capacity(n as usize);
    decls_for(ff, element, &mut solver, &mut decls);
    let member = type_pattern(ff, element, n - 1);
    Some((decls, member, set.shift_bound_identifiers(n as i32)))
}

/// The bound declarations and expression over a bare
/// type: one declaration per scalar component (all named `x` like
/// the stored ones — declaration names are alpha-irrelevant), and
/// the maplet
/// pattern over indices `n-1‥0`.
pub(crate) fn type_binder(
    ff: &rossi::formula::FormulaFactory,
    ty: &rossi::formula::Type,
) -> (Vec<BoundIdentDecl>, Expression) {
    use rossi::formula::Type;
    fn decls_for(ff: &rossi::formula::FormulaFactory, ty: &Type, out: &mut Vec<BoundIdentDecl>) {
        match ty {
            Type::Prod(left, right) => {
                decls_for(ff, left, out);
                decls_for(ff, right, out);
            }
            _ => out.push(ff.bound_ident_decl("x", None, None, Some(ty.clone()))),
        }
    }
    let mut decls = Vec::new();
    decls_for(ff, ty, &mut decls);
    let member = type_pattern(ff, ty, decls.len() as u32 - 1);
    (decls, member)
}

/// The maplet pattern over a type with indices descending from
/// `start`.
pub(crate) fn type_pattern(
    ff: &rossi::formula::FormulaFactory,
    ty: &rossi::formula::Type,
    start: u32,
) -> Expression {
    use rossi::formula::Type;
    fn build(ff: &rossi::formula::FormulaFactory, ty: &Type, next: &mut u32) -> Expression {
        match ty {
            Type::Prod(left, right) => {
                let l = build(ff, left, next);
                let r = build(ff, right, next);
                ff.binary_expression(rossi::formula::tag::BinaryExprOp::Mapsto, l, r, None)
            }
            _ => {
                *next -= 1;
                ff.bound_identifier(*next, None, Some(ty.clone()))
            }
        }
    }
    let mut next = start + 1;
    build(ff, ty, &mut next)
}

/// Insertion-ordered set semantics: first occurrence wins, order kept.
pub(crate) fn dedup_preserving_order(preds: Vec<Predicate>) -> Vec<Predicate> {
    let mut out: Vec<Predicate> = Vec::with_capacity(preds.len());
    for pred in preds {
        if !out.contains(&pred) {
            out.push(pred);
        }
    }
    out
}

/// The predicate's stored string form, used inside display strings.
pub(crate) fn display_pred(pred: &Predicate) -> String {
    PrettyPrinter::rodin_formula_string().print_formula_predicate(pred)
}

/// The expression's stored string form, used inside display strings.
pub(crate) fn display_expr(expr: &Expression) -> String {
    PrettyPrinter::rodin_formula_string().print_formula_expression(expr)
}

/// Fresh instantiation: frees the declarations of a
/// quantified predicate with identifiers fresh in `typenv`. `names`
/// override the declarations' own printing hints, position-wise.
/// Returns the freed identifiers and the instantiated body.
pub(crate) fn fresh_instantiation(
    decls: &[BoundIdentDecl],
    quantified: &Predicate,
    typenv: &SealedTypeEnvironment,
    names: &[&str],
) -> Result<(Vec<TypedIdent>, Predicate), String> {
    let mut solver = FreshNameSolver::new(typenv.iter().map(|(name, _)| name.to_string()));
    let ff = quantified.factory().clone();
    let mut idents = Vec::with_capacity(decls.len());
    let mut replacements = Vec::with_capacity(decls.len());
    for (index, decl) in decls.iter().enumerate() {
        let hint = names.get(index).copied().unwrap_or(decl.name());
        let ty = decl.ty().ok_or("untyped bound declaration")?.clone();
        let fresh = solver.solve_and_add(hint);
        replacements.push(Some(ff.free_identifier(&fresh, None, Some(ty.clone()))));
        idents.push(TypedIdent::new(fresh, ty));
    }
    Ok((idents, quantified.instantiate(&replacements)))
}
