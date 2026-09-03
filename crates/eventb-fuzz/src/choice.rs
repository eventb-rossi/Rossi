//! The source of every decision a generator makes.
//!
//! Generation is a fold over a stream of choices. Keeping that stream behind a
//! trait means the same generator can be driven by a seeded PRNG (reproducible
//! runs, shrinking) or, later, by a coverage-guided fuzzer's byte stream
//! (`arbitrary::Unstructured` implements the same three primitives).

/// A stream of generation decisions.
///
/// Implementors provide [`ByteSource::next_u32`]; the rest are conveniences
/// derived from it, so a new source is a dozen lines.
pub trait ByteSource {
    /// The next raw word. May repeat or run out of entropy; a source that has
    /// run dry must keep returning values rather than fail, so generation
    /// always terminates.
    fn next_u32(&mut self) -> u32;

    /// A value in `0..n`, or `0` when `n` is zero.
    fn below(&mut self, n: usize) -> usize {
        if n <= 1 {
            0
        } else {
            // Modulo bias is irrelevant here: the ranges are tiny (grammar
            // alternatives, repeat counts) and the goal is diversity, not a
            // uniform distribution.
            self.next_u32() as usize % n
        }
    }

    /// A value in `low..=high`, clamped when the range is inverted.
    fn between(&mut self, low: usize, high: usize) -> usize {
        if high <= low {
            low
        } else {
            low + self.below(high - low + 1)
        }
    }

    /// True with probability `num / den`.
    fn ratio(&mut self, num: usize, den: usize) -> bool {
        den > 0 && self.below(den) < num
    }
}

/// The generic conveniences, kept out of [`ByteSource`] itself so that trait
/// stays usable as `dyn ByteSource` — the generators take it that way to avoid
/// monomorphising the whole walk per source.
pub trait ByteSourceExt: ByteSource {
    /// One element of `items`, or `None` when it is empty.
    fn pick<'a, T>(&mut self, items: &'a [T]) -> Option<&'a T> {
        if items.is_empty() {
            None
        } else {
            let index = self.below(items.len());
            items.get(index)
        }
    }
}

impl<S: ByteSource + ?Sized> ByteSourceExt for S {}

/// A seeded SplitMix64 generator: small, fast, and reproducible across
/// platforms, which is what a fuzz corpus needs (a finding is replayed by its
/// seed alone).
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// A generator started from `seed`.
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

impl ByteSource for SplitMix64 {
    fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_seed_yields_the_same_stream() {
        let mut a = SplitMix64::new(42);
        let mut b = SplitMix64::new(42);
        for _ in 0..64 {
            assert_eq!(a.next_u32(), b.next_u32());
        }
    }

    #[test]
    fn different_seeds_diverge() {
        let mut a = SplitMix64::new(1);
        let mut b = SplitMix64::new(2);
        let left: Vec<u32> = (0..16).map(|_| a.next_u32()).collect();
        let right: Vec<u32> = (0..16).map(|_| b.next_u32()).collect();
        assert_ne!(left, right);
    }

    #[test]
    fn below_stays_in_range_and_handles_degenerate_bounds() {
        let mut rng = SplitMix64::new(7);
        assert_eq!(rng.below(0), 0);
        assert_eq!(rng.below(1), 0);
        for _ in 0..1000 {
            assert!(rng.below(5) < 5);
        }
    }

    #[test]
    fn between_covers_its_bounds_and_clamps_inverted_ranges() {
        let mut rng = SplitMix64::new(9);
        assert_eq!(rng.between(3, 3), 3);
        assert_eq!(rng.between(4, 2), 4);
        let mut seen_low = false;
        let mut seen_high = false;
        for _ in 0..1000 {
            let value = rng.between(2, 4);
            assert!((2..=4).contains(&value));
            seen_low |= value == 2;
            seen_high |= value == 4;
        }
        assert!(seen_low && seen_high);
    }

    #[test]
    fn pick_returns_none_only_for_an_empty_slice() {
        let mut rng = SplitMix64::new(11);
        assert!(rng.pick::<u8>(&[]).is_none());
        assert_eq!(rng.pick(&[7]), Some(&7));
    }
}
