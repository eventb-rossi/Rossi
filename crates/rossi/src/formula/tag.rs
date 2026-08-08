//! Numeric tags classifying formula nodes and operators.
//!
//! Every formula node carries a stable numeric [`Tag`]. Leaf and
//! assignment nodes have fixed small tags; each operator family occupies
//! a dense range anchored at a `FIRST_*` base, so an operator enum
//! converts to its tag with a plain cast. Tags from
//! [`FIRST_EXTENSION_TAG`] upward are allocated dynamically for
//! registered operator extensions and are stable only within one
//! process.
//!
//! The operator enums below are the type-safe face of the same layout:
//! their `#[repr(u32)]` discriminants are anchored to the range bases,
//! which the tests in this module pin exactly.

/// Numeric classification of a formula node.
pub type Tag = u32;

/// Sentinel for "no tag"; never carried by a constructed node.
pub const NO_TAG: Tag = 0;

/// A free identifier occurrence.
pub const FREE_IDENT: Tag = 1;
/// A bound identifier declaration attached to a quantifier.
pub const BOUND_IDENT_DECL: Tag = 2;
/// A bound identifier occurrence (de Bruijn index).
pub const BOUND_IDENT: Tag = 3;
/// An integer literal.
pub const INTLIT: Tag = 4;
/// A set defined in extension: `{a, b, c}`.
pub const SETEXT: Tag = 5;
/// A deterministic assignment: `x ≔ E`.
pub const BECOMES_EQUAL_TO: Tag = 6;
/// A set-membership assignment: `x :∈ S`.
pub const BECOMES_MEMBER_OF: Tag = 7;
/// A before-after-predicate assignment: `x :∣ P`.
pub const BECOMES_SUCH_THAT: Tag = 8;
/// A predicate meta-variable: `$P`.
pub const PREDICATE_VARIABLE: Tag = 9;

/// First tag of the relational-predicate range.
pub const FIRST_RELATIONAL_PREDICATE: Tag = 101;
/// First tag of the binary-expression range.
pub const FIRST_BINARY_EXPRESSION: Tag = 201;
/// First tag of the binary-predicate range.
pub const FIRST_BINARY_PREDICATE: Tag = 251;
/// First tag of the associative-expression range.
pub const FIRST_ASSOCIATIVE_EXPRESSION: Tag = 301;
/// First tag of the associative-predicate range.
pub const FIRST_ASSOCIATIVE_PREDICATE: Tag = 351;
/// First tag of the atomic-expression range.
pub const FIRST_ATOMIC_EXPRESSION: Tag = 401;
/// The `bool(P)` expression.
pub const KBOOL: Tag = 601;
/// First tag of the literal-predicate range.
pub const FIRST_LITERAL_PREDICATE: Tag = 610;
/// First tag of the simple-predicate range.
pub const FIRST_SIMPLE_PREDICATE: Tag = 620;
/// First tag of the unary-predicate range.
pub const FIRST_UNARY_PREDICATE: Tag = 701;
/// First tag of the unary-expression range.
pub const FIRST_UNARY_EXPRESSION: Tag = 751;
/// First tag of the quantified-expression range.
pub const FIRST_QUANTIFIED_EXPRESSION: Tag = 801;
/// First tag of the quantified-predicate range.
pub const FIRST_QUANTIFIED_PREDICATE: Tag = 851;
/// First tag of the multiple-predicate range.
pub const FIRST_MULTIPLE_PREDICATE: Tag = 901;

/// Type ascription `E ⦂ T`.
///
/// A surface-language extra: rossi accepts an ascription on any
/// expression, so it is a real node rather than being consumed at
/// construction. Kept clear of the operator ranges above.
pub const OFTYPE: Tag = 951;
/// User predicate application `p(x, y)`.
///
/// A surface-language tolerance node: it parses, prints and round-trips,
/// but never type-checks (there is no way to declare a predicate
/// operator yet). Kept clear of the operator ranges above.
pub const PRED_APPL: Tag = 952;

/// First tag allocated to registered operator extensions.
pub const FIRST_EXTENSION_TAG: Tag = 1000;

/// Relational predicate operators: `E op F`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum RelationalOp {
    /// `=`
    Equal = 101,
    /// `≠`
    NotEqual,
    /// `<`
    Lt,
    /// `≤`
    Le,
    /// `>`
    Gt,
    /// `≥`
    Ge,
    /// `∈`
    In,
    /// `∉`
    NotIn,
    /// `⊂` (strict subset)
    Subset,
    /// `⊄`
    NotSubset,
    /// `⊆`
    SubsetEq,
    /// `⊈`
    NotSubsetEq,
}

impl RelationalOp {
    /// All operators, in tag order.
    pub const ALL: [RelationalOp; 12] = [
        Self::Equal,
        Self::NotEqual,
        Self::Lt,
        Self::Le,
        Self::Gt,
        Self::Ge,
        Self::In,
        Self::NotIn,
        Self::Subset,
        Self::NotSubset,
        Self::SubsetEq,
        Self::NotSubsetEq,
    ];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Binary expression operators: `E op F`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum BinaryExprOp {
    /// `↦`
    Mapsto = 201,
    /// `↔`
    Rel,
    /// Total relation (private-use glyph, ASCII `<<->`)
    TRel,
    /// Surjective relation (private-use glyph, ASCII `<->>`)
    SRel,
    /// Total surjective relation (private-use glyph, ASCII `<<->>`)
    STRel,
    /// `⇸`
    PFun,
    /// `→`
    TFun,
    /// `⤔`
    PInj,
    /// `↣`
    TInj,
    /// `⤀`
    PSur,
    /// `↠`
    TSur,
    /// `⤖`
    TBij,
    /// `∖`
    SetMinus,
    /// `×`
    CProd,
    /// `⊗`
    DProd,
    /// `∥`
    PProd,
    /// `◁`
    DomRes,
    /// `⩤`
    DomSub,
    /// `▷`
    RanRes,
    /// `⩥`
    RanSub,
    /// `‥`
    UpTo,
    /// `−`
    Minus,
    /// `÷`
    Div,
    /// `mod`
    Mod,
    /// `^`
    Expn,
    /// Function application `f(x)`
    FunImage,
    /// Relational image `r[S]`
    RelImage,
}

impl BinaryExprOp {
    /// All operators, in tag order.
    pub const ALL: [BinaryExprOp; 27] = [
        Self::Mapsto,
        Self::Rel,
        Self::TRel,
        Self::SRel,
        Self::STRel,
        Self::PFun,
        Self::TFun,
        Self::PInj,
        Self::TInj,
        Self::PSur,
        Self::TSur,
        Self::TBij,
        Self::SetMinus,
        Self::CProd,
        Self::DProd,
        Self::PProd,
        Self::DomRes,
        Self::DomSub,
        Self::RanRes,
        Self::RanSub,
        Self::UpTo,
        Self::Minus,
        Self::Div,
        Self::Mod,
        Self::Expn,
        Self::FunImage,
        Self::RelImage,
    ];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Binary predicate operators: `P op Q`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum BinaryPredOp {
    /// `⇒`
    LImp = 251,
    /// `⇔`
    LEqv,
}

impl BinaryPredOp {
    /// All operators, in tag order.
    pub const ALL: [BinaryPredOp; 2] = [Self::LImp, Self::LEqv];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Associative expression operators: `E₁ op E₂ op … op Eₙ`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum AssocExprOp {
    /// `∪`
    BUnion = 301,
    /// `∩`
    BInter,
    /// `∘` (backward composition)
    BComp,
    /// `;` (forward composition)
    FComp,
    /// Relational override (private-use glyph, ASCII `<+`)
    Ovr,
    /// `+`
    Plus,
    /// `∗`
    Mul,
}

impl AssocExprOp {
    /// All operators, in tag order.
    pub const ALL: [AssocExprOp; 7] = [
        Self::BUnion,
        Self::BInter,
        Self::BComp,
        Self::FComp,
        Self::Ovr,
        Self::Plus,
        Self::Mul,
    ];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Associative predicate operators: `P₁ op P₂ op … op Pₙ`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum AssocPredOp {
    /// `∧`
    LAnd = 351,
    /// `∨`
    LOr,
}

impl AssocPredOp {
    /// All operators, in tag order.
    pub const ALL: [AssocPredOp; 2] = [Self::LAnd, Self::LOr];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Atomic (nullary) expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum AtomicOp {
    /// `ℤ`
    Integer = 401,
    /// `ℕ`
    Natural,
    /// `ℕ1`
    Natural1,
    /// `BOOL`
    Bool,
    /// `TRUE`
    True,
    /// `FALSE`
    False,
    /// `∅`
    EmptySet,
    /// `pred` (predecessor relation on integers)
    KPred,
    /// `succ` (successor relation on integers)
    KSucc,
    /// `prj1` (generic first projection)
    KPrj1Gen,
    /// `prj2` (generic second projection)
    KPrj2Gen,
    /// `id` (generic identity relation)
    KIdGen,
}

impl AtomicOp {
    /// All operators, in tag order.
    pub const ALL: [AtomicOp; 12] = [
        Self::Integer,
        Self::Natural,
        Self::Natural1,
        Self::Bool,
        Self::True,
        Self::False,
        Self::EmptySet,
        Self::KPred,
        Self::KSucc,
        Self::KPrj1Gen,
        Self::KPrj2Gen,
        Self::KIdGen,
    ];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Literal (nullary) predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum LiteralPredOp {
    /// `⊤`
    BTrue = 610,
    /// `⊥`
    BFalse,
}

impl LiteralPredOp {
    /// All operators, in tag order.
    pub const ALL: [LiteralPredOp; 2] = [Self::BTrue, Self::BFalse];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Unary expression operators.
///
/// Discriminants 758–760 are deliberately left unassigned; the numbering
/// of the later operators is part of the pinned layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum UnaryExprOp {
    /// `card(S)`
    KCard = 751,
    /// `ℙ(S)`
    Pow,
    /// `ℙ1(S)`
    Pow1,
    /// `union(S)`
    KUnion,
    /// `inter(S)`
    KInter,
    /// `dom(r)`
    KDom,
    /// `ran(r)`
    KRan,
    /// `min(S)`
    KMin = 761,
    /// `max(S)`
    KMax,
    /// `r∼` (converse)
    Converse,
    /// `−E` (unary minus)
    UnMinus,
}

impl UnaryExprOp {
    /// All operators, in tag order.
    pub const ALL: [UnaryExprOp; 11] = [
        Self::KCard,
        Self::Pow,
        Self::Pow1,
        Self::KUnion,
        Self::KInter,
        Self::KDom,
        Self::KRan,
        Self::KMin,
        Self::KMax,
        Self::Converse,
        Self::UnMinus,
    ];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Quantified expression operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum QuantExprOp {
    /// `⋃ x · P ∣ E`
    QUnion = 801,
    /// `⋂ x · P ∣ E`
    QInter,
    /// Comprehension set `{x · P ∣ E}` (also `{E ∣ P}` and `λ`)
    CSet,
}

impl QuantExprOp {
    /// All operators, in tag order.
    pub const ALL: [QuantExprOp; 3] = [Self::QUnion, Self::QInter, Self::CSet];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

/// Quantified predicate operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum QuantPredOp {
    /// `∀ x · P`
    Forall = 851,
    /// `∃ x · P`
    Exists,
}

impl QuantPredOp {
    /// All operators, in tag order.
    pub const ALL: [QuantPredOp; 2] = [Self::Forall, Self::Exists];

    /// The operator's numeric tag.
    pub const fn tag(self) -> Tag {
        self as Tag
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each enum's discriminants are contiguous from its range base, in
    /// `ALL` order, except for the documented gap in [`UnaryExprOp`].
    #[test]
    fn discriminants_are_anchored_to_range_bases() {
        for (i, op) in RelationalOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_RELATIONAL_PREDICATE + i as Tag);
        }
        for (i, op) in BinaryExprOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_BINARY_EXPRESSION + i as Tag);
        }
        for (i, op) in BinaryPredOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_BINARY_PREDICATE + i as Tag);
        }
        for (i, op) in AssocExprOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_ASSOCIATIVE_EXPRESSION + i as Tag);
        }
        for (i, op) in AssocPredOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_ASSOCIATIVE_PREDICATE + i as Tag);
        }
        for (i, op) in AtomicOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_ATOMIC_EXPRESSION + i as Tag);
        }
        for (i, op) in LiteralPredOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_LITERAL_PREDICATE + i as Tag);
        }
        for (i, op) in QuantExprOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_QUANTIFIED_EXPRESSION + i as Tag);
        }
        for (i, op) in QuantPredOp::ALL.iter().enumerate() {
            assert_eq!(op.tag(), FIRST_QUANTIFIED_PREDICATE + i as Tag);
        }
    }

    /// The unary-expression range skips 758–760.
    #[test]
    fn unary_expression_layout_has_reserved_gap() {
        let expected: [(UnaryExprOp, Tag); 11] = [
            (UnaryExprOp::KCard, 751),
            (UnaryExprOp::Pow, 752),
            (UnaryExprOp::Pow1, 753),
            (UnaryExprOp::KUnion, 754),
            (UnaryExprOp::KInter, 755),
            (UnaryExprOp::KDom, 756),
            (UnaryExprOp::KRan, 757),
            (UnaryExprOp::KMin, 761),
            (UnaryExprOp::KMax, 762),
            (UnaryExprOp::Converse, 763),
            (UnaryExprOp::UnMinus, 764),
        ];
        assert_eq!(UnaryExprOp::ALL.len(), expected.len());
        for ((op, tag), all) in expected.iter().zip(UnaryExprOp::ALL) {
            assert_eq!(all, *op);
            assert_eq!(op.tag(), *tag);
        }
    }

    /// Spot-pin the boundary tags of every range and the fixed tags, so
    /// a reordered variant cannot silently renumber a family.
    #[test]
    fn boundary_tags_are_pinned() {
        assert_eq!(NO_TAG, 0);
        assert_eq!(FREE_IDENT, 1);
        assert_eq!(BOUND_IDENT_DECL, 2);
        assert_eq!(BOUND_IDENT, 3);
        assert_eq!(INTLIT, 4);
        assert_eq!(SETEXT, 5);
        assert_eq!(BECOMES_EQUAL_TO, 6);
        assert_eq!(BECOMES_MEMBER_OF, 7);
        assert_eq!(BECOMES_SUCH_THAT, 8);
        assert_eq!(PREDICATE_VARIABLE, 9);
        assert_eq!(RelationalOp::NotSubsetEq.tag(), 112);
        assert_eq!(BinaryExprOp::RelImage.tag(), 227);
        assert_eq!(BinaryPredOp::LEqv.tag(), 252);
        assert_eq!(AssocExprOp::Mul.tag(), 307);
        assert_eq!(AssocPredOp::LOr.tag(), 352);
        assert_eq!(AtomicOp::KIdGen.tag(), 412);
        assert_eq!(KBOOL, 601);
        assert_eq!(LiteralPredOp::BFalse.tag(), 611);
        assert_eq!(FIRST_SIMPLE_PREDICATE, 620);
        assert_eq!(FIRST_UNARY_PREDICATE, 701);
        assert_eq!(QuantExprOp::CSet.tag(), 803);
        assert_eq!(QuantPredOp::Exists.tag(), 852);
        assert_eq!(FIRST_MULTIPLE_PREDICATE, 901);
        assert_eq!(OFTYPE, 951);
        assert_eq!(PRED_APPL, 952);
        assert_eq!(FIRST_EXTENSION_TAG, 1000);
    }
}
