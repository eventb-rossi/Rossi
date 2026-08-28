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
        "isFunGoal" => &structural::IsFunGoal,
        "finiteHypBoundedGoal" => &structural::FiniteHypBoundedGoal,
        _ => return None,
    };
    Some(imp)
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
