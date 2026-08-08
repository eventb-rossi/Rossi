//! Structural-hash helpers shared by the formula node constructors.
//!
//! Every node caches a structural hash computed bottom-up at
//! construction, so equality gets a constant-time reject and hashing a
//! formula is a field read. The hash covers the node kind (tag) and the
//! children, but neither spans nor solved types: a typed rebuild of a
//! formula keeps the same hash as its untyped original, which is legal
//! (they compare unequal but may collide) and lets the type-checker
//! reuse subtrees without rehashing.

use std::hash::{DefaultHasher, Hash, Hasher};

/// Combines two hashes, order-sensitively.
pub(super) fn combine(h1: u64, h2: u64) -> u64 {
    h1.wrapping_mul(17).wrapping_add(h2)
}

/// Folds a sequence of hashes, order-sensitively, from seed 0.
pub(super) fn fold(hashes: impl IntoIterator<Item = u64>) -> u64 {
    hashes.into_iter().fold(0, combine)
}

/// Hashes one `Hash` value (used for names and integer literals).
pub(super) fn hash_one(value: impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
