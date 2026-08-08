//! Mathematical types carried by checked formula nodes.
//!
//! The canonical string produced by [`Type::to_rodin_canonical`] is the
//! form written into the `org.eventb.core.type` attribute of checked
//! elements, e.g. `ℙ(USERS×(AUCTIONS×ITEMS))`.
//!
//! Types are always fully solved: there is no type-variable form here.
//! Inference variables exist only inside the type-checker and never
//! escape into node types.

use std::sync::Arc;

use super::tag::Tag;

/// The type of an Event-B expression.
///
/// Inner types are shared with [`Arc`], so cloning a type — which
/// happens for every node a type-check rebuilds — never copies the
/// spine.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// `BOOL`
    Bool,
    /// `ℤ`
    Int,
    /// A given set from a carrier-set declaration, e.g. `USERS`.
    Given(String),
    /// `ℙ(T)`
    Pow(Arc<Type>),
    /// `T × U` (left, right)
    Prod(Arc<Type>, Arc<Type>),
    /// An instance of a registered type constructor, e.g. `List(ℤ)`.
    ///
    /// Identified by the constructor's extension tag; the symbol is
    /// carried for display. Tags are stable only within one process, so
    /// parametric types must never be persisted by tag.
    Parametric {
        /// The type constructor's extension tag.
        tag: Tag,
        /// The type constructor's syntax symbol, e.g. `List`.
        symbol: String,
        /// The type parameters, in declaration order.
        params: Vec<Type>,
    },
}

impl Type {
    /// A given set: `Type::given("USERS")` → `USERS`.
    pub fn given(name: impl Into<String>) -> Type {
        Type::Given(name.into())
    }

    /// Powerset convenience constructor: `Type::pow(Type::Int)` → `ℙ(ℤ)`.
    pub fn pow(t: Type) -> Type {
        Type::Pow(Arc::new(t))
    }

    /// Cartesian product convenience constructor.
    pub fn prod(left: Type, right: Type) -> Type {
        Type::Prod(Arc::new(left), Arc::new(right))
    }

    /// Relation / function type `ℙ(left × right)` — Event-B's `left ↔ right`.
    pub fn relation(left: Type, right: Type) -> Type {
        Type::pow(Type::prod(left, right))
    }

    /// A carrier-set `S` has type `ℙ(S)` — the type of the set itself,
    /// not of its elements.
    pub fn carrier_set_type(name: &str) -> Type {
        Type::pow(Type::given(name))
    }

    /// The element type if this is a powerset: `ℙ(T)` → `T`.
    pub fn base_type(&self) -> Option<&Type> {
        match self {
            Type::Pow(inner) => Some(inner),
            _ => None,
        }
    }

    /// The domain type if this is a relational type: `ℙ(α × β)` → `α`.
    pub fn source(&self) -> Option<&Type> {
        match self.base_type()? {
            Type::Prod(left, _) => Some(left),
            _ => None,
        }
    }

    /// The range type if this is a relational type: `ℙ(α × β)` → `β`.
    pub fn target(&self) -> Option<&Type> {
        match self.base_type()? {
            Type::Prod(_, right) => Some(right),
            _ => None,
        }
    }

    /// Appends the names of the given sets occurring in this type, in
    /// traversal order and possibly with duplicates.
    pub fn collect_given_sets(&self, out: &mut Vec<String>) {
        match self {
            Type::Bool | Type::Int => {}
            Type::Given(name) => out.push(name.clone()),
            Type::Pow(inner) => inner.collect_given_sets(out),
            Type::Prod(left, right) => {
                left.collect_given_sets(out);
                right.collect_given_sets(out);
            }
            Type::Parametric { params, .. } => {
                for param in params {
                    param.collect_given_sets(out);
                }
            }
        }
    }

    /// The canonical string, as it appears in the
    /// `org.eventb.core.type="..."` attribute of `.bcc`/`.bcm` elements.
    ///
    /// The form collapses whitespace and uses Unicode symbols only:
    /// - `BOOL`
    /// - `ℤ`
    /// - `USERS`
    /// - `ℙ(ℤ)`
    /// - `USERS×AUCTIONS`
    /// - `ℙ(USERS×(AUCTIONS×ITEMS))`
    /// - `List(ℤ)`
    ///
    /// Products are right-associative and parenthesised only on the
    /// right-hand side of another product (confirmed against
    /// `AuctionMachine.bcm` and `binary-search/M2.bcm`).
    pub fn to_rodin_canonical(&self) -> String {
        let mut out = String::new();
        self.write_canonical(&mut out);
        out
    }

    fn write_canonical(&self, out: &mut String) {
        match self {
            Type::Bool => out.push_str("BOOL"),
            Type::Int => out.push('ℤ'),
            Type::Given(name) => out.push_str(name),
            Type::Pow(inner) => {
                out.push('ℙ');
                out.push('(');
                inner.write_canonical(out);
                out.push(')');
            }
            Type::Prod(left, right) => {
                left.write_canonical(out);
                out.push('×');
                // Right operand of a product gets parenthesised if it is
                // itself a product; the left one never is.
                match right.as_ref() {
                    Type::Prod(..) => {
                        out.push('(');
                        right.write_canonical(out);
                        out.push(')');
                    }
                    _ => right.write_canonical(out),
                }
            }
            Type::Parametric { symbol, params, .. } => {
                out.push_str(symbol);
                if let Some((first, rest)) = params.split_first() {
                    out.push('(');
                    first.write_canonical(out);
                    for param in rest {
                        out.push(',');
                        param.write_canonical(out);
                    }
                    out.push(')');
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_primitives() {
        assert_eq!(Type::Int.to_rodin_canonical(), "ℤ");
        assert_eq!(Type::Bool.to_rodin_canonical(), "BOOL");
        assert_eq!(Type::given("USERS").to_rodin_canonical(), "USERS");
    }

    #[test]
    fn canonical_carrier_set() {
        // A carrier set USERS has type ℙ(USERS) — what appears on
        // scCarrierSet.
        assert_eq!(
            Type::carrier_set_type("USERS").to_rodin_canonical(),
            "ℙ(USERS)"
        );
    }

    #[test]
    fn canonical_flat_product() {
        // AUCTIONS × ITEMS
        let t = Type::prod(Type::given("AUCTIONS"), Type::given("ITEMS"));
        assert_eq!(t.to_rodin_canonical(), "AUCTIONS×ITEMS");
    }

    #[test]
    fn canonical_right_nested_product() {
        // USERS × (AUCTIONS × ITEMS) — from AuctionMachine.bcm's `buyer`.
        let t = Type::prod(
            Type::given("USERS"),
            Type::prod(Type::given("AUCTIONS"), Type::given("ITEMS")),
        );
        assert_eq!(t.to_rodin_canonical(), "USERS×(AUCTIONS×ITEMS)");
    }

    #[test]
    fn canonical_left_nested_product_stays_flat() {
        // (A × B) × C prints without parentheses: the form is
        // right-associative, so the flat spelling A×B×C re-reads as
        // A×(B×C) — the parenthesised right operand is what preserves
        // the distinction.
        let t = Type::prod(
            Type::prod(Type::given("A"), Type::given("B")),
            Type::given("C"),
        );
        assert_eq!(t.to_rodin_canonical(), "A×B×C");
    }

    #[test]
    fn canonical_powerset_of_product() {
        let t = Type::pow(Type::prod(
            Type::given("USERS"),
            Type::prod(Type::given("AUCTIONS"), Type::given("ITEMS")),
        ));
        assert_eq!(t.to_rodin_canonical(), "ℙ(USERS×(AUCTIONS×ITEMS))");
    }

    #[test]
    fn canonical_parametric() {
        let list_int = Type::Parametric {
            tag: 1000,
            symbol: "List".into(),
            params: vec![Type::Int],
        };
        assert_eq!(list_int.to_rodin_canonical(), "List(ℤ)");

        let pair = Type::Parametric {
            tag: 1001,
            symbol: "Pair".into(),
            params: vec![Type::Int, Type::Bool],
        };
        assert_eq!(pair.to_rodin_canonical(), "Pair(ℤ,BOOL)");

        let enumeration = Type::Parametric {
            tag: 1002,
            symbol: "Direction".into(),
            params: vec![],
        };
        assert_eq!(enumeration.to_rodin_canonical(), "Direction");
    }

    #[test]
    fn relation_constructor() {
        // relation(α, β) is ℙ(α×β) — equal to the primitive spelling and
        // rendering the same canonical string.
        let r = Type::relation(Type::Int, Type::given("S"));
        assert_eq!(r, Type::pow(Type::prod(Type::Int, Type::given("S"))));
        assert_eq!(r.to_rodin_canonical(), "ℙ(ℤ×S)");
    }

    #[test]
    fn relational_accessors() {
        let r = Type::relation(Type::Int, Type::given("S"));
        assert_eq!(
            r.base_type(),
            Some(&Type::prod(Type::Int, Type::given("S")))
        );
        assert_eq!(r.source(), Some(&Type::Int));
        assert_eq!(r.target(), Some(&Type::given("S")));

        // A powerset of a non-product has a base type but no source or
        // target; a bare type has neither.
        let p = Type::pow(Type::Int);
        assert_eq!(p.base_type(), Some(&Type::Int));
        assert_eq!(p.source(), None);
        assert_eq!(p.target(), None);
        assert_eq!(Type::Int.base_type(), None);
        assert_eq!(Type::Int.source(), None);
    }
}
