/// A `PartialReciprocal` represents an integer (floored) division
/// by a `u64` that's not 0, 1 or u64::MAX.
///
/// Once constructed for a given `d`, `apply`ing a `PartialReciprocal`
/// to a `u64` computes an integer division of that argument by `d`.
/// The parameters represent an expression of the form
///   `f(x) = (x + increment) * multiplier >> (64 + shift)`
/// in full 128-bit arithmetic; for appropriately chosen values,
/// this expression can implement any (unsigned) integer division.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PartialReciprocal {
    multiplier: u64,
    shift: u8,
    increment: u8,
}

/// A `Reciprocal` represents an integer division by any non-zero
/// `u64`.  It replaces `PartialReciprocal`'s expression,
///   `f(x) = (x + increment) * multiplier >> (64 + shift)`, where
/// the inner addition is a saturating add by 0 or 1, with
///   `g(x) = (x * multiplier + summand) >> (64 + shift)`, where
/// both the multiplication and additions are in full 128 bit
/// arithmetic.  This additional work lets us handle all the cases,
/// including divisions by 1 and by `u64::MAX`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Reciprocal {
    multiplier: u64,
    summand: u64, // Always 0 (round up) or `multiplier` (round down)
    shift: u8,
}

impl PartialReciprocal {
    /// Constructs a `PartialReciprocal` that computes a floored
    /// division by `d`.
    ///
    /// Returns `None` if `d == 0`, or if `d == 1 || d == u64::MAX`:
    /// these last two divisors cannot be safely implemented as
    /// `PartialReciprocal` (the sequence would fail for `u64::MAX /
    /// 1` and `u64::MAX / u64::MAX`).
    ///
    /// The full `Reciprocal` handles these last two cases, at the
    /// expense of one more `u64` field and a branch.
    pub fn new(d: u64) -> Option<PartialReciprocal> {
        // Division by `d \in {1, u64::MAX}` are special because
        // `u64::MAX / d` differs from `(u64::MAX - 1) / d`,
        // and can't be computed by an increment-less sequence.
        //
        // We must give up on those... and 0, obviously.
        if d <= 1 || d == u64::MAX {
            return None;
        }

        // ilog2_d = floor(log_2(x)).
        let ilog2_d = 63 - d.leading_zeros();
        assert!(d >= 1u64 << ilog2_d);

        // Handle powers of two.
        if (d & (d - 1)) == 0 {
            assert!(d == 1u64 << ilog2_d);
            assert!(ilog2_d >= 1); // We guard against d == 1.

            // We want to shift right by ilog2_d >= 1, but we
            // don't have that in our PartialReciprocal expression.
            // What we do have is a full multiplication by a 64-bit
            // constant followed by a shift right by 64.  Let's
            // multiply by `1 << (64 - ilog2_d)`; after the shift
            // right by 64, that's equivalent to a shift by `ilog2_d`.
            return Some(PartialReciprocal {
                multiplier: 1u64 << (64 - ilog2_d),
                shift: 0,
                increment: 0,
            });
        }

        // We need `64 + ceil(log_2(d))` bits of precision in our
        // fixed-point approximation, to ensure the final truncated
        // result is error-free.
        //
        // We'll get that by rounding the approximation to nearest,
        // so we only need `64 + ceil(log_2(d)) - 1 = 64 + ilog2_d`
        // bits in our approximation.
        let shift = ilog2_d;
        let unity = 1u128 << (64 + shift);
        let scale = unity / (d as u128);
        let rem = unity % (d as u128);

        assert!(scale <= u64::MAX as u128);
        // If we want to round the approximation down...
        if rem as u64 <= d / 2 {
            // Then we have to nudge the runtime multiplicand up by 1
            // before the fixed multiplication.
            //
            // That's the multiply-and-add scheme of Arch Robison
            // [N-Bit Unsigned Division Via N-Bit Multiply-Add](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.512.2627&rep=rep1&type=pdf)
            Some(PartialReciprocal {
                multiplier: scale as u64,
                shift: shift as u8,
                increment: 1,
            })
        } else {
            // Otherwise, we can round our approximation up.
            // That's the usual div-by-mul scheme described in, e.g.,
            // Granlund and Montgomery's
            // [Division by invariant integers using multiplication](https://gmplib.org/~tege/divcnst-pldi94.pdf)

            // Rounding up can't overflow because that would be
            // equivalent to a division by a power of two, and we
            // handled those earlier.
            assert!(scale < u64::MAX as u128);
            Some(PartialReciprocal {
                multiplier: (scale + 1) as u64,
                shift: shift as u8,
                increment: 0,
            })
        }
    }

    /// Computes `x / d`, where `d` is the divison for which this
    /// reciprocal was constructed.
    ///
    /// The library tries to dispatch to a reasonable implementation
    /// for each platform.
    #[inline]
    #[must_use]
    #[cfg(target_arch = "x86_64")]
    pub fn apply(self, x: u64) -> u64 {
        self.apply_overflowing(x)
    }

    /// Computes `x / d`, where `d` is the divison for which this
    /// reciprocal was constructed.
    ///
    /// The library tries to dispatch to a reasonable implementation
    /// for each platform.
    #[inline]
    #[must_use]
    #[cfg(not(target_arch = "x86_64"))]
    pub fn apply(self, x: u64) -> u64 {
        self.apply_saturating(x)
    }

    /// Computes `x / d` with saturating arithmetic.
    #[inline]
    #[must_use]
    pub fn apply_saturating(self, x: u64) -> u64 {
        let shifted = x.saturating_add(self.increment as u64);
        let hi = ((self.multiplier as u128 * shifted as u128) >> 64) as u64;

        hi >> self.shift
    }

    /// Computes `x / d` with an alternative saturating increment that
    /// is shorter and equally efficient on x86-64.
    #[inline]
    #[must_use]
    pub fn apply_overflowing(self, x: u64) -> u64 {
        // Manually implement a saturating increment: we know
        // `increment` is only 0 or 1, so we can recover from any
        // overflow by subtracting 1 from `shifted`.  We can then
        // expect LLVM to implement that as a subtract-with-borrow on
        // x86-64.
        let (mut shifted, overflow) = x.overflowing_add(self.increment as u64);
        if overflow {
            shifted = shifted.wrapping_sub(1);
        }

        let hi = ((self.multiplier as u128 * shifted as u128) >> 64) as u64;

        hi >> self.shift
    }
}

impl Reciprocal {
    /// Constructs a `Reciprocal` that computes a floored division by `d`.
    ///
    /// Returns None if `d == 0`.
    pub fn new(d: u64) -> Option<Reciprocal> {
        if d == 0 {
            return None;
        }

        if let Some(base) = PartialReciprocal::new(d) {
            return Some(Reciprocal {
                multiplier: base.multiplier,
                summand: base.multiplier * base.increment as u64,
                shift: base.shift,
            });
        }

        // The two special cases below work in 64.64 fixed point.
        // While they have the usual `summand = multiplier` structure,
        // their results differ when dividing u64::MAX and (u64::MAX -
        // 1).  That's why we can't use the same constants for the
        // `PartialReciprocal` sequence, which
        // pre-saturating-increments the dividend, instead of actually
        // adding the summand to the intermediate 128-bit product.

        // We can thus determine whether to use `u64_max_result` by
        // checking if the increment overflows.
        assert!(d == 1 || d == u64::MAX);
        if d == 1 {
            // We want to divide by 1, i.e., multiply by 1.
            //
            // We can fake it by scaling by by u64::MAX / 2**64 (1 -
            // 2**-64), and adding (1 - 2**-64) again.
            //
            // It would even be correct to add 1 (x * u64::MAX / 2**64
            // truncates to x - 1 for all u64 values), but that
            // doesn't fit our pattern... and adding (1 - 2**-64)
            // suffices to compensate even the worst-case
            // approximation error (max x * [1 - (1 - 2**-64)]
            // = max x / 2**64 = u64::MAX / 2**-64).
            return Some(Reciprocal {
                multiplier: u64::MAX,
                summand: u64::MAX,
                shift: 0,
            });
        }

        // And we can fake a division by u64::MAX with a
        // multiplication by 2**-64, followed by adding 2**-64 again..
        //
        // For any value less than u64::MAX, the result is less than
        // 1, so truncates to 0.  For u64::MAX, we get exactly 1.
        Some(Reciprocal {
            multiplier: 1,
            summand: 1,
            shift: 0,
        })
    }

    /// Computes `x / d`, where `d` is the divison for which this
    /// reciprocal was constructed.
    #[inline]
    #[must_use]
    pub fn apply(&self, x: u64) -> u64 {
        let mut product = x as u128 * self.multiplier as u128;
        product += self.summand as u128;

        (product >> 64) as u64 >> self.shift
    }
}

#[cfg(test)]
mod tests {
    const PROBE_RANGE: u64 = 1u64 << 12;

    fn check(d: u64) {
        let partial = crate::PartialReciprocal::new(d);
        let recip = crate::Reciprocal::new(d);

        let probe = |x: u64| {
            let expected = x / d;
            if let Some(p) = partial {
                assert_eq!(p.apply_saturating(x), expected, "d={}, x={}", d, x);
                assert_eq!(p.apply_overflowing(x), expected, "d={}, x={}", d, x);
            }

            if let Some(r) = recip {
                assert_eq!(r.apply(x), expected, "d={}, x={}", d, x);
            }
        };

        if partial.is_none() && recip.is_none() {
            assert!(d == 0);
            return;
        }

        assert!(d > 0);
        assert_ne!(recip, None);
        if d != 1 && d != u64::MAX {
            assert_ne!(partial, None);
        }

        // The `center` is the largest `u64` multiple of `d`.
        let center = d * (u64::MAX / d);
        for i in 0..=PROBE_RANGE {
            // Probe around 0.
            probe(i);
            // Probe around u64::MAX.
            probe(u64::MAX - i);

            // Probe a symmetrical range around `d`
            probe(d.wrapping_add(i));
            probe(d.wrapping_sub(i));
            // Another symmetrical range around `center - d`.
            probe(center.wrapping_sub(d).wrapping_add(i));
            probe(center.wrapping_sub(d).wrapping_sub(i));
            // A symmetrical range around `center`
            probe(center.wrapping_add(i));
            probe(center.wrapping_sub(i));

            // And a last symmetrical range around `u64::MAX - d`.
            probe(u64::MAX.wrapping_sub(d).wrapping_add(i));
            probe(u64::MAX.wrapping_sub(d).wrapping_sub(i));
        }
    }

    #[test]
    fn check_edge_cases() {
        for d in [0, 1, 2, u64::MAX - 1, u64::MAX].iter().copied() {
            check(d);
        }
    }

    #[test]
    fn check_powers_of_two() {
        for p in 0..64 {
            check(1u64 << p);
        }
    }

    #[test]
    fn test_small_divisors() {
        for d in 0..256 {
            check(d);
            check(u64::MAX - d);
        }
    }

    #[test]
    fn test_sparse_divisors() {
        for i in 0..64 {
            for j in i..64 {
                let d = (1u64 << i) | (1u64 << j);

                check(d);
                // Also check the bitwise complement (dense divisors).
                check(!d);
            }
        }
    }

    #[test]
    fn test_near_powers_of_two() {
        for p in 0..64 {
            let po2 = 1u64 << p;
            for i in 1..=8 {
                check(po2.wrapping_sub(i));
                check(po2.wrapping_add(i));
            }
        }
    }

    #[test]
    fn test_powers_of_two_and_half() {
        for p in 0..64 {
            let po2 = 1u64 << p;
            let delta = po2 / 2;

            let x = po2.wrapping_sub(delta / 4);
            let y = po2.wrapping_add(delta);

            check(x);
            check(y);
            for i in 1..=8 {
                check(x.wrapping_sub(i));
                check(x.wrapping_add(i));
                check(y.wrapping_sub(i));
                check(y.wrapping_add(i));
            }
        }
    }

    #[test]
    fn test_factors_of_u64_max() {
        // Factors of u64::MAX are the only ones for which
        // dividing u64::MAX and u64::MAX - 1 yields different
        // values (1 and u64::MAX also count, but we test those
        // separately in `check_edge_cases`).
        let factors = [3, 5, 17, 257, 641, 65537, 6700417];

        assert_eq!(factors.iter().product::<u64>(), u64::MAX);
        for d in factors.iter().copied() {
            check(d);
        }
    }
}
