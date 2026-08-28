//! Proof confidence levels.

/// The confidence attached to a proof rule or a whole proof tree.
///
/// The scale: a closed node carries its rule's confidence
/// and a tree's confidence is the minimum over its nodes, so any
/// uncertain step caps the whole proof. The named constants bound the
/// meaningful ranges — discharged is `(REVIEWED_MAX, DISCHARGED_MAX]`,
/// reviewed `(UNCERTAIN_MAX, REVIEWED_MAX]`, uncertain
/// `(PENDING, UNCERTAIN_MAX]` — and [`Confidence::UNATTEMPTED`] marks
/// a proof tree that was never worked on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Confidence(pub i32);

impl Confidence {
    /// A proof tree with an open root and no comment.
    pub const UNATTEMPTED: Confidence = Confidence(-99);
    /// An open proof tree node.
    pub const PENDING: Confidence = Confidence(0);
    /// Upper bound of the uncertain range: an unknown reasoner or a
    /// stale reasoner version.
    pub const UNCERTAIN_MAX: Confidence = Confidence(100);
    /// Upper bound of the reviewed range: accepted by a human, not a
    /// prover.
    pub const REVIEWED_MAX: Confidence = Confidence(500);
    /// Upper bound of the scale: fully discharged.
    pub const DISCHARGED_MAX: Confidence = Confidence(1000);
}

#[cfg(test)]
mod tests {
    use super::Confidence;

    #[test]
    fn ordering_follows_the_scale() {
        assert!(Confidence::UNATTEMPTED < Confidence::PENDING);
        assert!(Confidence::PENDING < Confidence::UNCERTAIN_MAX);
        assert!(Confidence::UNCERTAIN_MAX < Confidence::REVIEWED_MAX);
        assert!(Confidence::REVIEWED_MAX < Confidence::DISCHARGED_MAX);
        // Aggregation over a tree is plain `min`.
        assert_eq!(
            Confidence(750).min(Confidence::DISCHARGED_MAX),
            Confidence(750)
        );
    }
}
