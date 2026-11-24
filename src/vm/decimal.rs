//! Zero-allocation exact 128-bit fixed-point `Decimal` arithmetic (scale `10^18`,
//! symmetric range `[-(2^127 - 1), +(2^127 - 1)]`) matching `BigInt` Euclidean
//! fixed-point semantics bit-for-bit across all sign combinations and edge cases.

use crate::core::bigint::{DEC_MAX, DEC_MIN, DEC_SCALE};
use crate::core::syntax::BugKind;

const DEC_SCALE_U128: u128 = 1_000_000_000_000_000_000;
const DEC_MAX_U128: u128 = DEC_MAX as u128;

const _: () = assert!(DEC_MAX == i128::MAX);

#[inline]
#[must_use]
pub const fn in_dec_range(v: i128) -> bool {
    v >= DEC_MIN
}

#[inline]
#[must_use]
pub const fn dec_add(a: i128, b: i128) -> Option<i128> {
    match a.checked_add(b) {
        Some(v) if in_dec_range(v) => Some(v),
        _ => None,
    }
}

#[inline]
#[must_use]
pub const fn dec_sub(a: i128, b: i128) -> Option<i128> {
    match a.checked_sub(b) {
        Some(v) if in_dec_range(v) => Some(v),
        _ => None,
    }
}

#[inline]
#[must_use]
pub const fn dec_neg(a: i128) -> Option<i128> {
    if in_dec_range(a) { Some(-a) } else { None }
}

#[inline]
#[must_use]
pub const fn dec_int_to_dec(n: i64) -> Option<i128> {
    match (n as i128).checked_mul(DEC_SCALE) {
        Some(v) if in_dec_range(v) => Some(v),
        _ => None,
    }
}

#[inline]
#[must_use]
pub const fn dec_bool_to_dec(b: bool) -> i128 {
    if b { DEC_SCALE } else { 0 }
}

/// Exact widening 128×128 -> 256-bit unsigned product in little-endian `u64` limbs.
#[inline]
const fn mul_u128_wide(a: u128, b: u128) -> [u64; 4] {
    let a0 = a as u64 as u128;
    let a1 = a >> 64;
    let b0 = b as u64 as u128;
    let b1 = b >> 64;

    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;

    let l0 = p00 as u64;

    let mid1 = (p00 >> 64) + (p01 as u64 as u128) + (p10 as u64 as u128);
    let l1 = mid1 as u64;

    let mid2 = (mid1 >> 64) + (p01 >> 64) + (p10 >> 64) + (p11 as u64 as u128);
    let l2 = mid2 as u64;

    let l3 = ((mid2 >> 64) + (p11 >> 64)) as u64;
    [l0, l1, l2, l3]
}

/// Exact widening `a * DEC_SCALE` -> 192-bit unsigned product in little-endian `u64` limbs.
#[inline]
const fn mul_u128_by_scale(a: u128) -> [u64; 3] {
    let a0 = a as u64 as u128;
    let a1 = a >> 64;
    let p0 = a0 * DEC_SCALE_U128;
    let p1 = a1 * DEC_SCALE_U128 + (p0 >> 64);
    [p0 as u64, p1 as u64, (p1 >> 64) as u64]
}

#[inline]
fn add_one_u256(limbs: &mut [u64; 4]) -> bool {
    let mut carry = 1u64;
    for l in limbs.iter_mut() {
        let (v, ov) = l.overflowing_add(carry);
        *l = v;
        carry = u64::from(ov);
        if carry == 0 {
            break;
        }
    }
    carry != 0
}

#[inline]
fn add_one_u192(limbs: &mut [u64; 3]) -> bool {
    let mut carry = 1u64;
    for l in limbs.iter_mut() {
        let (v, ov) = l.overflowing_add(carry);
        *l = v;
        carry = u64::from(ov);
        if carry == 0 {
            break;
        }
    }
    carry != 0
}

/// Exact Euclidean fixed-point multiplication `(a * b).div_euclid(DEC_SCALE)`,
/// checked against `[DEC_MIN, DEC_MAX]`.
#[must_use]
pub fn dec_mul_euclid(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let prod_neg = (a < 0) != (b < 0);
    let prod = mul_u128_wide(a.unsigned_abs(), b.unsigned_abs());

    // Divide 256-bit `prod` by `DEC_SCALE_U128 < 2^60` (so `rem << 64` never overflows `u128`).
    let mut rem = 0u128;
    let mut q = [0u64; 4];
    for i in (0..4).rev() {
        let cur = (rem << 64) | u128::from(prod[i]);
        q[i] = (cur / DEC_SCALE_U128) as u64;
        rem = cur % DEC_SCALE_U128;
    }

    if prod_neg && rem != 0 && add_one_u256(&mut q) {
        return None;
    }
    if q[2] != 0 || q[3] != 0 {
        return None;
    }
    let mag = u128::from(q[0]) | (u128::from(q[1]) << 64);
    if mag > DEC_MAX_U128 {
        return None;
    }
    let signed = if prod_neg && mag != 0 {
        -(mag as i128)
    } else {
        mag as i128
    };
    in_dec_range(signed).then_some(signed)
}

/// Exact unsigned 192-bit by 128-bit division returning `(quotient, rem_nonzero)`.
/// Precondition: `d > 0`.
fn div_u192_by_u128(n: [u64; 3], d: u128) -> ([u64; 3], bool) {
    if d <= u128::from(u64::MAX) {
        // Since `rem < d <= 2^64 - 1`, `(rem << 64) | n[i] <= (2^64 - 2)*2^64 + (2^64 - 1) < 2^128`.
        let mut rem = 0u128;
        let mut q = [0u64; 3];
        for i in (0..3).rev() {
            let cur = (rem << 64) | u128::from(n[i]);
            q[i] = (cur / d) as u64;
            rem = cur % d;
        }
        return (q, rem != 0);
    }

    // Binary restoring division for `d > u64::MAX`: 192 iterations, 0 allocations.
    let mut q = [0u64; 3];
    let mut rem: u128 = 0;
    let mut rem_top = false;

    for limb_idx in (0..3).rev() {
        let limb = n[limb_idx];
        let mut q_limb = 0u64;
        for bit_in_limb in (0..64).rev() {
            let bit = u128::from((limb >> bit_in_limb) & 1);
            let next_top = (rem >> 127) != 0;
            rem = (rem << 1) | bit;
            rem_top = next_top;
            if rem_top || rem >= d {
                rem = rem.wrapping_sub(d);
                rem_top = false;
                q_limb |= 1u64 << bit_in_limb;
            }
        }
        q[limb_idx] = q_limb;
    }
    (q, rem_top || rem != 0)
}

/// Exact Euclidean fixed-point division `(a * DEC_SCALE).div_euclid(b)`,
/// returning `Err(BugKind::DivByZero)` when `b == 0` and
/// `Err(BugKind::DecimalOverflow)` when the quotient leaves `[DEC_MIN, DEC_MAX]`.
pub fn dec_div_euclid(a: i128, b: i128) -> Result<i128, BugKind> {
    if b == 0 {
        return Err(BugKind::DivByZero);
    }
    if a == 0 {
        return Ok(0);
    }
    let num_neg = a < 0;
    let den_neg = b < 0;
    let num = mul_u128_by_scale(a.unsigned_abs());
    let (mut q, rem_nonzero) = div_u192_by_u128(num, b.unsigned_abs());

    // Match `BigInt::div_rem_euclid`:
    //   num >= 0:                q_neg = den_neg,  mag = q
    //   num < 0 && rem == 0:     q_neg = !den_neg, mag = q
    //   num < 0 && rem != 0:     q_neg = !den_neg, mag = q + 1
    let q_neg = if !num_neg { den_neg } else { !den_neg };
    if num_neg && rem_nonzero && add_one_u192(&mut q) {
        return Err(BugKind::DecimalOverflow);
    }

    if q[2] != 0 {
        return Err(BugKind::DecimalOverflow);
    }
    let mag = u128::from(q[0]) | (u128::from(q[1]) << 64);
    if mag > DEC_MAX_U128 {
        return Err(BugKind::DecimalOverflow);
    }
    let signed = if q_neg && mag != 0 {
        -(mag as i128)
    } else {
        mag as i128
    };
    if in_dec_range(signed) {
        Ok(signed)
    } else {
        Err(BugKind::DecimalOverflow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::bigint::BigInt;

    fn bigint_mul_dec(a: i128, b: i128) -> Option<i128> {
        let scale = BigInt::from(DEC_SCALE);
        let q = (&BigInt::from(a) * &BigInt::from(b))
            .div_euclid(&scale)
            .unwrap_or(BigInt::ZERO);
        if q.in_decimal_range() {
            q.to_i128()
        } else {
            None
        }
    }

    fn bigint_div_dec(a: i128, b: i128) -> Result<i128, BugKind> {
        if b == 0 {
            return Err(BugKind::DivByZero);
        }
        let scale = BigInt::from(DEC_SCALE);
        let q = (&BigInt::from(a) * &scale)
            .div_euclid(&BigInt::from(b))
            .ok_or(BugKind::DivByZero)?;
        if q.in_decimal_range() {
            q.to_i128().ok_or(BugKind::DecimalOverflow)
        } else {
            Err(BugKind::DecimalOverflow)
        }
    }

    #[test]
    fn decimal_mul_div_matches_bigint_across_edge_and_random_inputs() {
        let edges: [i128; 16] = [
            0,
            1,
            -1,
            2,
            -2,
            3,
            -3,
            DEC_SCALE,
            -DEC_SCALE,
            DEC_SCALE / 2,
            -(DEC_SCALE / 2),
            i128::from(u64::MAX),
            -i128::from(u64::MAX),
            DEC_MAX,
            DEC_MIN,
            DEC_MAX / 2,
        ];
        for &a in &edges {
            for &b in &edges {
                assert_eq!(
                    dec_mul_euclid(a, b),
                    bigint_mul_dec(a, b),
                    "mul mismatch for a={a}, b={b}"
                );
                assert_eq!(
                    dec_div_euclid(a, b),
                    bigint_div_dec(a, b),
                    "div mismatch for a={a}, b={b}"
                );
            }
        }

        // Deterministic SplitMix64 fuzzing (2,000 pairs spanning 64-bit & 128-bit magnitudes).
        let mut s = 0x5EED_DEC1_0000_0001u64;
        let mut next = || -> u64 {
            s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        for _ in 0..2_000 {
            let lo_a = u128::from(next());
            let hi_a = u128::from(next() >> (next() % 64));
            let mag_a = (lo_a | (hi_a << 64)) & DEC_MAX_U128;
            let a = if (next() & 1) == 0 {
                mag_a as i128
            } else {
                -(mag_a as i128)
            };

            let lo_b = u128::from(next());
            let hi_b = u128::from(next() >> (next() % 64));
            let mag_b = (lo_b | (hi_b << 64)) & DEC_MAX_U128;
            let b = if (next() & 1) == 0 {
                mag_b as i128
            } else {
                -(mag_b as i128)
            };

            assert_eq!(dec_mul_euclid(a, b), bigint_mul_dec(a, b));
            assert_eq!(dec_div_euclid(a, b), bigint_div_dec(a, b));
        }
    }
}
