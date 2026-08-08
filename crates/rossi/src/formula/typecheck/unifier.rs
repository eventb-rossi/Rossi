//! Unification over types extended with inference variables.
//!
//! Inference variables exist only inside this arena and never escape
//! into public [`Type`]s: `solve` either produces a fully solved type
//! or reports that a variable remains.

use super::super::tag::Tag;
use super::super::types::Type;

/// A handle into the unifier's arena.
pub(super) type TRef = u32;

#[derive(Debug, Clone)]
enum TNode {
    /// An inference variable, possibly bound to another node.
    Var {
        binding: Option<TRef>,
    },
    Bool,
    Int,
    Given(String),
    Pow(TRef),
    Prod(TRef, TRef),
    Parametric {
        tag: Tag,
        symbol: String,
        params: Vec<TRef>,
    },
}

/// Why two types failed to unify.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum UnifyError {
    /// Structurally incompatible.
    Mismatch,
    /// A variable would contain itself.
    Circular,
}

#[derive(Default)]
pub(super) struct TypeUnifier {
    nodes: Vec<TNode>,
}

impl TypeUnifier {
    pub(super) fn new() -> Self {
        Self::default()
    }

    fn push(&mut self, node: TNode) -> TRef {
        let index = self.nodes.len() as TRef;
        self.nodes.push(node);
        index
    }

    /// A fresh inference variable.
    pub(super) fn fresh(&mut self) -> TRef {
        self.push(TNode::Var { binding: None })
    }

    pub(super) fn int(&mut self) -> TRef {
        self.push(TNode::Int)
    }

    pub(super) fn bool(&mut self) -> TRef {
        self.push(TNode::Bool)
    }

    pub(super) fn pow(&mut self, base: TRef) -> TRef {
        self.push(TNode::Pow(base))
    }

    pub(super) fn prod(&mut self, left: TRef, right: TRef) -> TRef {
        self.push(TNode::Prod(left, right))
    }

    /// `ℙ(left × right)`.
    pub(super) fn relation(&mut self, left: TRef, right: TRef) -> TRef {
        let prod = self.prod(left, right);
        self.pow(prod)
    }

    /// An instance of a registered type constructor.
    pub(super) fn parametric(&mut self, tag: Tag, symbol: &str, params: Vec<TRef>) -> TRef {
        self.push(TNode::Parametric {
            tag,
            symbol: symbol.to_string(),
            params,
        })
    }

    /// Lifts a solved type into the arena.
    pub(super) fn lift(&mut self, ty: &Type) -> TRef {
        match ty {
            Type::Bool => self.bool(),
            Type::Int => self.int(),
            Type::Given(name) => self.push(TNode::Given(name.clone())),
            Type::Pow(inner) => {
                let inner = self.lift(inner);
                self.pow(inner)
            }
            Type::Prod(left, right) => {
                let left = self.lift(left);
                let right = self.lift(right);
                self.prod(left, right)
            }
            Type::Parametric {
                tag,
                symbol,
                params,
            } => {
                let params = params.iter().map(|p| self.lift(p)).collect();
                self.push(TNode::Parametric {
                    tag: *tag,
                    symbol: symbol.clone(),
                    params,
                })
            }
        }
    }

    /// Follows variable bindings to the representative node.
    fn resolve(&self, mut t: TRef) -> TRef {
        while let TNode::Var {
            binding: Some(next),
        } = self.nodes[t as usize]
        {
            t = next;
        }
        t
    }

    /// Whether the variable `var` occurs in `t`.
    fn occurs(&self, var: TRef, t: TRef) -> bool {
        let t = self.resolve(t);
        if t == var {
            return true;
        }
        match &self.nodes[t as usize] {
            TNode::Var { .. } | TNode::Bool | TNode::Int | TNode::Given(_) => false,
            TNode::Pow(inner) => self.occurs(var, *inner),
            TNode::Prod(left, right) => self.occurs(var, *left) || self.occurs(var, *right),
            TNode::Parametric { params, .. } => params.iter().any(|p| self.occurs(var, *p)),
        }
    }

    /// Makes `a` and `b` equal, binding variables as needed.
    pub(super) fn unify(&mut self, a: TRef, b: TRef) -> Result<(), UnifyError> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        if a == b {
            return Ok(());
        }
        // Bind a variable, with the occurs check.
        if matches!(self.nodes[a as usize], TNode::Var { .. }) {
            if self.occurs(a, b) {
                return Err(UnifyError::Circular);
            }
            self.nodes[a as usize] = TNode::Var { binding: Some(b) };
            return Ok(());
        }
        if matches!(self.nodes[b as usize], TNode::Var { .. }) {
            if self.occurs(b, a) {
                return Err(UnifyError::Circular);
            }
            self.nodes[b as usize] = TNode::Var { binding: Some(a) };
            return Ok(());
        }
        match (
            self.nodes[a as usize].clone(),
            self.nodes[b as usize].clone(),
        ) {
            (TNode::Bool, TNode::Bool) | (TNode::Int, TNode::Int) => Ok(()),
            (TNode::Given(x), TNode::Given(y)) if x == y => Ok(()),
            (TNode::Pow(x), TNode::Pow(y)) => self.unify(x, y),
            (TNode::Prod(l, r), TNode::Prod(l2, r2)) => {
                self.unify(l, l2)?;
                self.unify(r, r2)
            }
            (
                TNode::Parametric { tag, params, .. },
                TNode::Parametric {
                    tag: tag2,
                    params: params2,
                    ..
                },
            ) if tag == tag2 && params.len() == params2.len() => {
                for (p, p2) in params.iter().zip(&params2) {
                    self.unify(*p, *p2)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::Mismatch),
        }
    }

    /// Whether the type is fully solved (no variable remains), without
    /// materializing it — the validation pass over every shadow slot
    /// only needs the verdict.
    pub(super) fn is_solved(&self, t: TRef) -> bool {
        let t = self.resolve(t);
        match &self.nodes[t as usize] {
            TNode::Var { .. } => false,
            TNode::Bool | TNode::Int | TNode::Given(_) => true,
            TNode::Pow(inner) => self.is_solved(*inner),
            TNode::Prod(left, right) => self.is_solved(*left) && self.is_solved(*right),
            TNode::Parametric { params, .. } => params.iter().all(|p| self.is_solved(*p)),
        }
    }

    /// The fully solved type, or `None` if a variable remains.
    pub(super) fn solve(&self, t: TRef) -> Option<Type> {
        let t = self.resolve(t);
        match &self.nodes[t as usize] {
            TNode::Var { .. } => None,
            TNode::Bool => Some(Type::Bool),
            TNode::Int => Some(Type::Int),
            TNode::Given(name) => Some(Type::Given(name.clone())),
            TNode::Pow(inner) => Some(Type::pow(self.solve(*inner)?)),
            TNode::Prod(left, right) => Some(Type::prod(self.solve(*left)?, self.solve(*right)?)),
            TNode::Parametric {
                tag,
                symbol,
                params,
            } => Some(Type::Parametric {
                tag: *tag,
                symbol: symbol.clone(),
                params: params
                    .iter()
                    .map(|p| self.solve(*p))
                    .collect::<Option<Vec<Type>>>()?,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unifies_structurally() {
        let mut u = TypeUnifier::new();
        // ℙ(α × ℤ) = ℙ(BOOL × β)  ⇒  α = BOOL, β = ℤ
        let alpha = u.fresh();
        let beta = u.fresh();
        let int = u.int();
        let boolean = u.bool();
        let left = u.relation(alpha, int);
        let right = u.relation(boolean, beta);
        u.unify(left, right).expect("unifies");
        assert_eq!(u.solve(alpha), Some(Type::Bool));
        assert_eq!(u.solve(beta), Some(Type::Int));
    }

    #[test]
    fn rejects_mismatches_and_cycles() {
        let mut u = TypeUnifier::new();
        let int = u.int();
        let boolean = u.bool();
        assert_eq!(u.unify(int, boolean), Err(UnifyError::Mismatch));

        let alpha = u.fresh();
        let pow_alpha = u.pow(alpha);
        assert_eq!(u.unify(alpha, pow_alpha), Err(UnifyError::Circular));
    }

    #[test]
    fn unsolved_variables_stay_unsolved() {
        let mut u = TypeUnifier::new();
        let alpha = u.fresh();
        let pow = u.pow(alpha);
        assert_eq!(u.solve(pow), None);
    }

    #[test]
    fn distinct_given_sets_do_not_unify() {
        let mut u = TypeUnifier::new();
        let s = u.lift(&Type::given("S"));
        let t = u.lift(&Type::given("T"));
        let s2 = u.lift(&Type::given("S"));
        assert_eq!(u.unify(s, t), Err(UnifyError::Mismatch));
        assert_eq!(u.unify(s, s2), Ok(()));
    }
}
