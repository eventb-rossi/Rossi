//! Path-based subformula addressing.
//!
//! A [`Position`] is the path of child indices from a root formula to
//! one of its subformulas. The child numbering is part of the model's
//! contract: binary nodes are `0 = left, 1 = right`; list-shaped nodes
//! number their elements; a quantified predicate numbers its
//! declarations `0..n-1` and its body `n`; a quantified expression adds
//! its value expression at `n+1`; an ascription is `0 = expression,
//! 1 = spelled type`; extension nodes number expression children before
//! predicate children. Declarations are leaves. Assignments do not
//! support positions.
//!
//! Positions order themselves in pre-order: a formula's positions,
//! collected root-first, are sorted.

use std::fmt;
use std::str::FromStr;

use super::decl::BoundIdentDecl;
use super::expression::{Expression, ExpressionKind};
use super::predicate::{Predicate, PredicateKind};

/// The path of child indices leading to a subformula; empty = the
/// formula itself.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Position(Vec<u32>);

impl Position {
    /// The root position (the formula itself).
    pub fn root() -> Position {
        Position(Vec::new())
    }

    /// Whether this is the root position.
    pub fn is_root(&self) -> bool {
        self.0.is_empty()
    }

    /// The child indices from the root.
    pub fn indices(&self) -> &[u32] {
        &self.0
    }

    /// The position of the enclosing formula; `None` at the root.
    pub fn parent(&self) -> Option<Position> {
        let mut indices = self.0.clone();
        indices.pop().map(|_| Position(indices))
    }

    /// The position of child `index` of this position.
    pub fn child(&self, index: u32) -> Position {
        let mut indices = self.0.clone();
        indices.push(index);
        Position(indices)
    }

    /// This subformula's index within its parent; `None` at the root.
    pub fn child_index(&self) -> Option<u32> {
        self.0.last().copied()
    }

    /// The position of the next sibling; `None` at the root.
    pub fn next_sibling(&self) -> Option<Position> {
        let mut indices = self.0.clone();
        let last = indices.pop()?;
        indices.push(last + 1);
        Some(Position(indices))
    }

    /// The position of the previous sibling; `None` at the root or on a
    /// first child.
    pub fn previous_sibling(&self) -> Option<Position> {
        let mut indices = self.0.clone();
        let last = indices.pop()?;
        if last == 0 {
            return None;
        }
        indices.push(last - 1);
        Some(Position(indices))
    }
}

impl fmt::Display for Position {
    /// Dot-separated indices; the root prints as the empty string.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for index in &self.0 {
            if !first {
                write!(f, ".")?;
            }
            write!(f, "{index}")?;
            first = false;
        }
        Ok(())
    }
}

/// A malformed textual position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidPosition;

impl fmt::Display for InvalidPosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid position")
    }
}

impl std::error::Error for InvalidPosition {}

impl FromStr for Position {
    type Err = InvalidPosition;

    fn from_str(s: &str) -> Result<Position, InvalidPosition> {
        if s.is_empty() {
            return Ok(Position::root());
        }
        s.split('.')
            .map(|part| part.parse().map_err(|_| InvalidPosition))
            .collect::<Result<Vec<u32>, _>>()
            .map(Position)
    }
}

/// A borrowed reference to any positional formula node.
#[derive(Debug, Clone, Copy)]
pub enum FormulaRef<'a> {
    /// An expression node.
    Expr(&'a Expression),
    /// A predicate node.
    Pred(&'a Predicate),
    /// A bound-identifier declaration.
    Decl(&'a BoundIdentDecl),
}

impl<'a> FormulaRef<'a> {
    /// The number of positional children.
    pub fn child_count(&self) -> usize {
        match self {
            FormulaRef::Expr(e) => expr_child_count(e),
            FormulaRef::Pred(p) => pred_child_count(p),
            FormulaRef::Decl(_) => 0,
        }
    }

    /// The positional child at `index`.
    pub fn child(&self, index: usize) -> Option<FormulaRef<'a>> {
        match self {
            FormulaRef::Expr(e) => expr_child(e, index),
            FormulaRef::Pred(p) => pred_child(p, index),
            FormulaRef::Decl(_) => None,
        }
    }
}

/// A failed position lookup or replacement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PositionError {
    /// The position does not address a subformula of this formula.
    OutOfRange,
    /// The replacement is of the wrong syntactic class or changes the
    /// type of a typed subformula.
    IncompatibleReplacement,
}

impl fmt::Display for PositionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PositionError::OutOfRange => f.write_str("position out of range"),
            PositionError::IncompatibleReplacement => f.write_str("incompatible replacement"),
        }
    }
}

impl std::error::Error for PositionError {}

impl Expression {
    /// The subformula at `position`, if any.
    pub fn sub_formula(&self, position: &Position) -> Option<FormulaRef<'_>> {
        descend(FormulaRef::Expr(self), position)
    }

    /// The positions of all subformulas accepted by `filter`, in
    /// pre-order.
    pub fn positions(&self, filter: &mut dyn FnMut(FormulaRef<'_>) -> bool) -> Vec<Position> {
        let mut found = Vec::new();
        collect(FormulaRef::Expr(self), filter, &mut Vec::new(), &mut found);
        found
    }

    /// Replaces the subformula at `position`. The replacement must be
    /// of the same syntactic class and, when the subformula is typed,
    /// of the same type.
    pub fn rewrite_sub_formula(
        &self,
        position: &Position,
        replacement: FormulaRef<'_>,
    ) -> Result<Expression, PositionError> {
        rewrite_expr_at(self, position.indices(), replacement)
    }
}

impl Predicate {
    /// The subformula at `position`, if any.
    pub fn sub_formula(&self, position: &Position) -> Option<FormulaRef<'_>> {
        descend(FormulaRef::Pred(self), position)
    }

    /// The positions of all subformulas accepted by `filter`, in
    /// pre-order.
    pub fn positions(&self, filter: &mut dyn FnMut(FormulaRef<'_>) -> bool) -> Vec<Position> {
        let mut found = Vec::new();
        collect(FormulaRef::Pred(self), filter, &mut Vec::new(), &mut found);
        found
    }

    /// The positions of the leaves of this predicate's propositional
    /// skeleton, left to right.
    ///
    /// The skeleton is the `∧ ∨ ⇒ ⇔ ¬` tree. This descends through those
    /// connectives and stops everywhere else, so a quantifier is a leaf and
    /// its body is never entered, as is a relational predicate whose operands
    /// embed a `bool(P)`, and so is an extension node whatever it denotes.
    /// The result is never empty: a predicate built from no connective is its
    /// own single leaf, at the root position.
    ///
    /// The returned positions are sorted, form a subset of
    /// [`Self::positions`], and each addresses a [`FormulaRef::Pred`], so a
    /// leaf can be read back with [`Self::sub_formula`]. A flat 0-based index
    /// is `.iter().enumerate()`.
    ///
    /// [`Self::positions`] cannot express this: its filter selects nodes but
    /// does not stop the descent, so it would also return the subpredicates of
    /// a leaf.
    pub fn propositional_leaves(&self) -> Vec<Position> {
        let mut found = Vec::new();
        collect_leaves(self, &mut Vec::new(), &mut found);
        found
    }

    /// Replaces the subformula at `position`; see
    /// [`Expression::rewrite_sub_formula`].
    pub fn rewrite_sub_formula(
        &self,
        position: &Position,
        replacement: FormulaRef<'_>,
    ) -> Result<Predicate, PositionError> {
        rewrite_pred_at(self, position.indices(), replacement)
    }
}

/// Whether `p` is a connective of the propositional skeleton — the nodes
/// [`Predicate::propositional_leaves`] descends through.
///
/// The kind alone decides it: `AssocPredOp` is `∧`/`∨` and `BinaryPredOp` is
/// `⇒`/`⇔`, both exhaustive. An extension node is deliberately not a
/// connective: what its children mean is the extension's business, so it
/// stands as one condition rather than being taken apart.
fn is_connective(p: &Predicate) -> bool {
    matches!(
        p.kind(),
        PredicateKind::Associative { .. } | PredicateKind::Binary { .. } | PredicateKind::Not(_)
    )
}

fn collect_leaves(p: &Predicate, path: &mut Vec<u32>, found: &mut Vec<Position>) {
    if !is_connective(p) {
        found.push(Position(path.clone()));
        return;
    }
    // Taking the predicate children through `pred_child` rather than
    // re-deriving indices per kind is what keeps a leaf's position the same
    // one `sub_formula` resolves.
    for index in 0..pred_child_count(p) {
        if let Some(FormulaRef::Pred(child)) = pred_child(p, index) {
            path.push(index as u32);
            collect_leaves(child, path, found);
            path.pop();
        }
    }
}

fn descend<'a>(node: FormulaRef<'a>, position: &Position) -> Option<FormulaRef<'a>> {
    let mut current = node;
    for index in position.indices() {
        current = current.child(*index as usize)?;
    }
    Some(current)
}

fn collect(
    node: FormulaRef<'_>,
    filter: &mut dyn FnMut(FormulaRef<'_>) -> bool,
    path: &mut Vec<u32>,
    found: &mut Vec<Position>,
) {
    if filter(node) {
        found.push(Position(path.clone()));
    }
    for index in 0..node.child_count() {
        let child = node.child(index).expect("child within count");
        path.push(index as u32);
        collect(child, filter, path, found);
        path.pop();
    }
}

fn expr_child_count(e: &Expression) -> usize {
    match e.kind() {
        ExpressionKind::FreeIdentifier(_)
        | ExpressionKind::BoundIdentifier(_)
        | ExpressionKind::IntegerLiteral(_)
        | ExpressionKind::Atomic(_) => 0,
        ExpressionKind::SetExtension(members) => members.len(),
        ExpressionKind::Bool(_) => 1,
        ExpressionKind::Binary { .. } => 2,
        ExpressionKind::Associative { children, .. } => children.len(),
        ExpressionKind::Unary { .. } => 1,
        ExpressionKind::Quantified { decls, .. } => decls.len() + 2,
        ExpressionKind::Ascription { .. } => 2,
        ExpressionKind::Extended { exprs, preds, .. } => exprs.len() + preds.len(),
    }
}

fn expr_child<'a>(e: &'a Expression, index: usize) -> Option<FormulaRef<'a>> {
    match e.kind() {
        ExpressionKind::FreeIdentifier(_)
        | ExpressionKind::BoundIdentifier(_)
        | ExpressionKind::IntegerLiteral(_)
        | ExpressionKind::Atomic(_) => None,
        ExpressionKind::SetExtension(members) => members.get(index).map(FormulaRef::Expr),
        ExpressionKind::Bool(pred) => (index == 0).then_some(FormulaRef::Pred(pred)),
        ExpressionKind::Binary { left, right, .. } => match index {
            0 => Some(FormulaRef::Expr(left)),
            1 => Some(FormulaRef::Expr(right)),
            _ => None,
        },
        ExpressionKind::Associative { children, .. } => children.get(index).map(FormulaRef::Expr),
        ExpressionKind::Unary { child, .. } => (index == 0).then_some(FormulaRef::Expr(child)),
        ExpressionKind::Quantified {
            decls, pred, expr, ..
        } => {
            let n = decls.len();
            if index < n {
                Some(FormulaRef::Decl(&decls[index]))
            } else if index == n {
                Some(FormulaRef::Pred(pred))
            } else if index == n + 1 {
                Some(FormulaRef::Expr(expr))
            } else {
                None
            }
        }
        ExpressionKind::Ascription { expr, type_expr } => match index {
            0 => Some(FormulaRef::Expr(expr)),
            1 => Some(FormulaRef::Expr(type_expr)),
            _ => None,
        },
        ExpressionKind::Extended { exprs, preds, .. } => {
            if index < exprs.len() {
                Some(FormulaRef::Expr(&exprs[index]))
            } else {
                preds.get(index - exprs.len()).map(FormulaRef::Pred)
            }
        }
    }
}

fn pred_child_count(p: &Predicate) -> usize {
    match p.kind() {
        PredicateKind::Literal(_) | PredicateKind::PredicateVariable(_) => 0,
        PredicateKind::Relational { .. } => 2,
        PredicateKind::Binary { .. } => 2,
        PredicateKind::Associative { children, .. } => children.len(),
        PredicateKind::Not(_) => 1,
        PredicateKind::Quantified { decls, .. } => decls.len() + 1,
        PredicateKind::Simple(_) => 1,
        PredicateKind::Multiple(children) => children.len(),
        PredicateKind::Application { args, .. } => args.len(),
        PredicateKind::Extended { exprs, preds, .. } => exprs.len() + preds.len(),
    }
}

fn pred_child<'a>(p: &'a Predicate, index: usize) -> Option<FormulaRef<'a>> {
    match p.kind() {
        PredicateKind::Literal(_) | PredicateKind::PredicateVariable(_) => None,
        PredicateKind::Relational { left, right, .. } => match index {
            0 => Some(FormulaRef::Expr(left)),
            1 => Some(FormulaRef::Expr(right)),
            _ => None,
        },
        PredicateKind::Binary { left, right, .. } => match index {
            0 => Some(FormulaRef::Pred(left)),
            1 => Some(FormulaRef::Pred(right)),
            _ => None,
        },
        PredicateKind::Associative { children, .. } => children.get(index).map(FormulaRef::Pred),
        PredicateKind::Not(child) => (index == 0).then_some(FormulaRef::Pred(child)),
        PredicateKind::Quantified { decls, pred, .. } => {
            let n = decls.len();
            if index < n {
                Some(FormulaRef::Decl(&decls[index]))
            } else if index == n {
                Some(FormulaRef::Pred(pred))
            } else {
                None
            }
        }
        PredicateKind::Simple(child) => (index == 0).then_some(FormulaRef::Expr(child)),
        PredicateKind::Multiple(children) => children.get(index).map(FormulaRef::Expr),
        PredicateKind::Application { args, .. } => args.get(index).map(FormulaRef::Expr),
        PredicateKind::Extended { exprs, preds, .. } => {
            if index < exprs.len() {
                Some(FormulaRef::Expr(&exprs[index]))
            } else {
                preds.get(index - exprs.len()).map(FormulaRef::Pred)
            }
        }
    }
}

fn compatible_expr(src: &Expression, dst: &Expression) -> bool {
    match src.ty() {
        Some(ty) => dst.ty() == Some(ty),
        None => true,
    }
}

fn compatible_decl(src: &BoundIdentDecl, dst: &BoundIdentDecl) -> bool {
    match src.ty() {
        Some(ty) => dst.ty() == Some(ty),
        None => true,
    }
}

fn rewrite_expr_at(
    e: &Expression,
    path: &[u32],
    replacement: FormulaRef<'_>,
) -> Result<Expression, PositionError> {
    let Some((&index, rest)) = path.split_first() else {
        let FormulaRef::Expr(dst) = replacement else {
            return Err(PositionError::IncompatibleReplacement);
        };
        if !compatible_expr(e, dst) {
            return Err(PositionError::IncompatibleReplacement);
        }
        return Ok(dst.clone());
    };
    let index = index as usize;
    let ff = e.factory().clone();
    match e.kind() {
        ExpressionKind::SetExtension(members) => {
            let members = replace_expr_list(members, index, rest, replacement)?;
            Ok(ff.set_extension(members, e.span()))
        }
        ExpressionKind::Bool(pred) if index == 0 => {
            Ok(ff.bool_expression(rewrite_pred_at(pred, rest, replacement)?, e.span()))
        }
        ExpressionKind::Binary { op, left, right } => match index {
            0 => Ok(ff.binary_expression(
                *op,
                rewrite_expr_at(left, rest, replacement)?,
                right.clone(),
                e.span(),
            )),
            1 => Ok(ff.binary_expression(
                *op,
                left.clone(),
                rewrite_expr_at(right, rest, replacement)?,
                e.span(),
            )),
            _ => Err(PositionError::OutOfRange),
        },
        ExpressionKind::Associative { op, children } => {
            let children = replace_expr_list(children, index, rest, replacement)?;
            Ok(ff.associative_expression(*op, children, e.span()))
        }
        ExpressionKind::Unary { op, child } if index == 0 => {
            Ok(ff.unary_expression(*op, rewrite_expr_at(child, rest, replacement)?, e.span()))
        }
        ExpressionKind::Quantified {
            op,
            decls,
            pred,
            expr,
            form,
        } => {
            let n = decls.len();
            if index < n {
                let decls = replace_decl_list(decls, index, rest, replacement)?;
                Ok(ff.quantified_expression(
                    *op,
                    decls,
                    pred.clone(),
                    expr.clone(),
                    e.span(),
                    *form,
                ))
            } else if index == n {
                Ok(ff.quantified_expression(
                    *op,
                    decls.clone(),
                    rewrite_pred_at(pred, rest, replacement)?,
                    expr.clone(),
                    e.span(),
                    *form,
                ))
            } else if index == n + 1 {
                Ok(ff.quantified_expression(
                    *op,
                    decls.clone(),
                    pred.clone(),
                    rewrite_expr_at(expr, rest, replacement)?,
                    e.span(),
                    *form,
                ))
            } else {
                Err(PositionError::OutOfRange)
            }
        }
        ExpressionKind::Ascription { expr, type_expr } => match index {
            0 => Ok(ff.ascription(
                rewrite_expr_at(expr, rest, replacement)?,
                type_expr.clone(),
                e.span(),
            )),
            1 => Ok(ff.ascription(
                expr.clone(),
                rewrite_expr_at(type_expr, rest, replacement)?,
                e.span(),
            )),
            _ => Err(PositionError::OutOfRange),
        },
        ExpressionKind::Extended { tag, exprs, preds } => {
            let Some(super::extension::Extension::Expr(ext)) = ff.extension(*tag).cloned() else {
                return Err(PositionError::OutOfRange);
            };
            let (exprs, preds) = replace_extended_children(exprs, preds, index, rest, replacement)?;
            ff.extended_expression(&ext, exprs, preds, e.span(), None)
                .map_err(|_| PositionError::IncompatibleReplacement)
        }
        _ => Err(PositionError::OutOfRange),
    }
}

fn rewrite_pred_at(
    p: &Predicate,
    path: &[u32],
    replacement: FormulaRef<'_>,
) -> Result<Predicate, PositionError> {
    let Some((&index, rest)) = path.split_first() else {
        let FormulaRef::Pred(dst) = replacement else {
            return Err(PositionError::IncompatibleReplacement);
        };
        return Ok(dst.clone());
    };
    let index = index as usize;
    let ff = p.factory().clone();
    match p.kind() {
        PredicateKind::Relational { op, left, right } => match index {
            0 => Ok(ff.relational_predicate(
                *op,
                rewrite_expr_at(left, rest, replacement)?,
                right.clone(),
                p.span(),
            )),
            1 => Ok(ff.relational_predicate(
                *op,
                left.clone(),
                rewrite_expr_at(right, rest, replacement)?,
                p.span(),
            )),
            _ => Err(PositionError::OutOfRange),
        },
        PredicateKind::Binary { op, left, right } => match index {
            0 => Ok(ff.binary_predicate(
                *op,
                rewrite_pred_at(left, rest, replacement)?,
                right.clone(),
                p.span(),
            )),
            1 => Ok(ff.binary_predicate(
                *op,
                left.clone(),
                rewrite_pred_at(right, rest, replacement)?,
                p.span(),
            )),
            _ => Err(PositionError::OutOfRange),
        },
        PredicateKind::Associative { op, children } => Ok(ff.associative_predicate(
            *op,
            replace_pred_list(children, index, rest, replacement)?,
            p.span(),
        )),
        PredicateKind::Not(child) if index == 0 => {
            Ok(ff.not_predicate(rewrite_pred_at(child, rest, replacement)?, p.span()))
        }
        PredicateKind::Quantified { op, decls, pred } => {
            let n = decls.len();
            if index < n {
                let decls = replace_decl_list(decls, index, rest, replacement)?;
                Ok(ff.quantified_predicate(*op, decls, pred.clone(), p.span()))
            } else if index == n {
                Ok(ff.quantified_predicate(
                    *op,
                    decls.clone(),
                    rewrite_pred_at(pred, rest, replacement)?,
                    p.span(),
                ))
            } else {
                Err(PositionError::OutOfRange)
            }
        }
        PredicateKind::Simple(child) if index == 0 => {
            Ok(ff.simple_predicate(rewrite_expr_at(child, rest, replacement)?, p.span()))
        }
        PredicateKind::Multiple(children) => {
            let children = replace_expr_list(children, index, rest, replacement)?;
            Ok(ff.multiple_predicate(children, p.span()))
        }
        PredicateKind::Application {
            function,
            function_span,
            args,
        } => {
            let args = replace_expr_list(args, index, rest, replacement)?;
            Ok(ff.predicate_application(function, *function_span, args, p.span()))
        }
        PredicateKind::Extended { tag, exprs, preds } => {
            let Some(super::extension::Extension::Pred(ext)) = ff.extension(*tag).cloned() else {
                return Err(PositionError::OutOfRange);
            };
            let (exprs, preds) = replace_extended_children(exprs, preds, index, rest, replacement)?;
            ff.extended_predicate(&ext, exprs, preds, p.span())
                .map_err(|_| PositionError::IncompatibleReplacement)
        }
        _ => Err(PositionError::OutOfRange),
    }
}

/// Replaces one positional child of an extended node (expressions
/// first, then predicates).
fn replace_extended_children(
    exprs: &[Expression],
    preds: &[Predicate],
    index: usize,
    rest: &[u32],
    replacement: FormulaRef<'_>,
) -> Result<(Vec<Expression>, Vec<Predicate>), PositionError> {
    if index < exprs.len() {
        let exprs = replace_expr_list(exprs, index, rest, replacement)?;
        Ok((exprs, preds.to_vec()))
    } else {
        let preds = replace_pred_list(preds, index - exprs.len(), rest, replacement)?;
        Ok((exprs.to_vec(), preds))
    }
}

fn replace_pred_list(
    list: &[Predicate],
    index: usize,
    rest: &[u32],
    replacement: FormulaRef<'_>,
) -> Result<Vec<Predicate>, PositionError> {
    let child = list.get(index).ok_or(PositionError::OutOfRange)?;
    let mut list = list.to_vec();
    list[index] = rewrite_pred_at(child, rest, replacement)?;
    Ok(list)
}

fn replace_expr_list(
    list: &[Expression],
    index: usize,
    rest: &[u32],
    replacement: FormulaRef<'_>,
) -> Result<Vec<Expression>, PositionError> {
    let child = list.get(index).ok_or(PositionError::OutOfRange)?;
    let mut list = list.to_vec();
    list[index] = rewrite_expr_at(child, rest, replacement)?;
    Ok(list)
}

fn replace_decl_list(
    decls: &[BoundIdentDecl],
    index: usize,
    rest: &[u32],
    replacement: FormulaRef<'_>,
) -> Result<Vec<BoundIdentDecl>, PositionError> {
    if !rest.is_empty() {
        return Err(PositionError::OutOfRange);
    }
    let FormulaRef::Decl(dst) = replacement else {
        return Err(PositionError::IncompatibleReplacement);
    };
    let src = decls.get(index).ok_or(PositionError::OutOfRange)?;
    if !compatible_decl(src, dst) {
        return Err(PositionError::IncompatibleReplacement);
    }
    let mut decls = decls.to_vec();
    decls[index] = dst.clone();
    Ok(decls)
}
