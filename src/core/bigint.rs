//! Zero-crate arbitrary-precision signed integer (`BigInt`) matching Lean 4 `Int` semantics.
//!
//! Provides exact Euclidean division (`div_euclid` / `rem_euclid` matching Lean 4 `Int.ediv` /
//! `Int.emod`), arbitrary-precision Decimal intermediates (256+ bits for `mulDec`/`divDec`),
//! canonical decimal string parsing/formatting, and IEEE-754 `f64` conversion.

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};
use std::str::FromStr;

pub const INT64_MIN: i64 = i64::MIN;
pub const INT64_MAX: i64 = i64::MAX;

pub const DEC_SCALE: i128 = 1_000_000_000_000_000_000;
pub const DEC_MAX: i128 = i128::MAX; // 2^127 - 1
pub const DEC_MIN: i128 = -i128::MAX; // -(2^127 - 1)

/// Arbitrary-precision signed integer represented as sign + little-endian base-2^32 limbs.
/// Zero is canonically represented as `neg = false, limbs = []`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct BigInt {
    neg: bool,
    limbs: Vec<u32>,
}

impl BigInt {
    pub const ZERO: Self = Self {
        neg: false,
        limbs: Vec::new(),
    };

    #[must_use]
    pub fn zero() -> Self {
        Self::ZERO
    }

    #[must_use]
    pub fn one() -> Self {
        Self {
            neg: false,
            limbs: vec![1],
        }
    }

    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.neg && !self.limbs.is_empty()
    }

    #[must_use]
    pub fn is_positive(&self) -> bool {
        !self.neg && !self.limbs.is_empty()
    }

    #[must_use]
    pub fn abs(&self) -> Self {
        Self {
            neg: false,
            limbs: self.limbs.clone(),
        }
    }

    #[must_use]
    pub fn to_i64(&self) -> Option<i64> {
        if self.limbs.is_empty() {
            return Some(0);
        }
        if self.limbs.len() > 2 {
            return None;
        }
        let lo = u64::from(self.limbs[0]);
        let hi = self.limbs.get(1).copied().map_or(0, u64::from);
        let mag = lo | (hi << 32);
        if !self.neg {
            i64::try_from(mag).ok()
        } else if mag == (1u64 << 63) {
            Some(i64::MIN)
        } else {
            i64::try_from(mag).ok().map(|v| -v)
        }
    }

    #[must_use]
    pub fn to_u64(&self) -> Option<u64> {
        if self.neg {
            return None;
        }
        if self.limbs.is_empty() {
            return Some(0);
        }
        if self.limbs.len() > 2 {
            return None;
        }
        let lo = u64::from(self.limbs[0]);
        let hi = self.limbs.get(1).copied().map_or(0, u64::from);
        Some(lo | (hi << 32))
    }

    #[must_use]
    pub fn to_usize(&self) -> Option<usize> {
        self.to_u64().and_then(|v| usize::try_from(v).ok())
    }

    #[must_use]
    pub fn to_usize_saturating(&self) -> usize {
        if self.neg {
            return 0;
        }
        self.to_usize().unwrap_or(usize::MAX)
    }

    #[must_use]
    pub fn to_i128(&self) -> Option<i128> {
        if self.limbs.is_empty() {
            return Some(0);
        }
        if self.limbs.len() > 4 {
            return None;
        }
        let mut mag = 0u128;
        for (i, &limb) in self.limbs.iter().enumerate() {
            mag |= u128::from(limb) << (i * 32);
        }
        if !self.neg {
            i128::try_from(mag).ok()
        } else if mag == (1u128 << 127) {
            Some(i128::MIN)
        } else {
            i128::try_from(mag).ok().map(|v| -v)
        }
    }

    #[must_use]
    pub fn in_int64_range(&self) -> bool {
        self.to_i64().is_some()
    }

    #[must_use]
    pub fn in_decimal_range(&self) -> bool {
        self.to_i128()
            .is_some_and(|v| (DEC_MIN..=DEC_MAX).contains(&v))
    }

    /// Convert to IEEE-754 binary64 using round-to-nearest-even (matching Lean `Float.ofInt`).
    #[must_use]
    pub fn to_f64(&self) -> f64 {
        if self.is_zero() {
            return 0.0;
        }
        if let Some(v) = self.to_i128() {
            return v as f64;
        }
        let bits = bit_len(&self.limbs);
        if bits > 1024 {
            return if self.neg {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            };
        }
        // Extract top 54 bits (bits - 1 down to bits - 54), plus sticky bit below.
        let shift = bits - 54;
        let mut sig54 = 0u64;
        for i in 0..54 {
            let b = get_bit(&self.limbs, shift + i);
            sig54 |= u64::from(b) << i;
        }
        let sticky = has_any_bit_below(&self.limbs, shift);
        let lsb = (sig54 >> 1) & 1;
        let guard = sig54 & 1;
        let round_up = guard == 1 && (sticky || lsb == 1);
        let mut mant = (sig54 >> 1) + u64::from(round_up);
        let mut exp: u64 = (bits - 1) as u64 + 1023;
        if mant == (1u64 << 53) {
            mant >>= 1;
            exp += 1;
        }
        if exp >= 2047 {
            return if self.neg {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            };
        }
        let sign_bit = if self.neg { 1u64 << 63 } else { 0 };
        let frac = mant & ((1u64 << 52) - 1);
        f64::from_bits(sign_bit | (exp << 52) | frac)
    }

    /// Euclidean division & remainder matching Lean 4 `Int.ediv` (`/`) and `Int.emod` (`%`).
    /// Returns `None` iff `divisor == 0`.
    /// For `divisor != 0`, returns `(q, r)` with `self == divisor * q + r` and `0 <= r < |divisor|`.
    #[must_use]
    pub fn div_rem_euclid(&self, divisor: &Self) -> Option<(Self, Self)> {
        if divisor.is_zero() {
            return None;
        }
        let (q_mag, r_mag) = div_rem_mag(&self.limbs, &divisor.limbs);
        if !self.neg {
            let q = Self::from_sign_limbs(divisor.neg, q_mag);
            let r = Self::from_sign_limbs(false, r_mag);
            Some((q, r))
        } else if r_mag.is_empty() {
            let q = Self::from_sign_limbs(!divisor.neg, q_mag);
            Some((q, Self::ZERO))
        } else {
            let q_plus_one = add_mag(&q_mag, &[1]);
            let r_adj = sub_mag(&divisor.limbs, &r_mag);
            let q = Self::from_sign_limbs(!divisor.neg, q_plus_one);
            let r = Self::from_sign_limbs(false, r_adj);
            Some((q, r))
        }
    }

    #[must_use]
    pub fn div_euclid(&self, divisor: &Self) -> Option<Self> {
        self.div_rem_euclid(divisor).map(|(q, _)| q)
    }

    #[must_use]
    pub fn rem_euclid(&self, divisor: &Self) -> Option<Self> {
        self.div_rem_euclid(divisor).map(|(_, r)| r)
    }

    fn from_sign_limbs(neg: bool, mut limbs: Vec<u32>) -> Self {
        normalize(&mut limbs);
        Self {
            neg: neg && !limbs.is_empty(),
            limbs,
        }
    }

    fn from_u128_sign(neg: bool, mut v: u128) -> Self {
        let mut limbs = Vec::new();
        while v != 0 {
            limbs.push((v & 0xFFFF_FFFF) as u32);
            v >>= 32;
        }
        Self {
            neg: neg && !limbs.is_empty(),
            limbs,
        }
    }
}

fn normalize(limbs: &mut Vec<u32>) {
    while limbs.last() == Some(&0) {
        limbs.pop();
    }
}

fn cmp_mag(a: &[u32], b: &[u32]) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Equal => {
            for i in (0..a.len()).rev() {
                match a[i].cmp(&b[i]) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
            }
            Ordering::Equal
        }
        ord => ord,
    }
}

fn add_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    let n = a.len().max(b.len());
    let mut out = Vec::with_capacity(n + 1);
    let mut carry = 0u64;
    for i in 0..n {
        let av = a.get(i).copied().map_or(0, u64::from);
        let bv = b.get(i).copied().map_or(0, u64::from);
        let sum = av + bv + carry;
        out.push((sum & 0xFFFF_FFFF) as u32);
        carry = sum >> 32;
    }
    if carry != 0 {
        out.push(carry as u32);
    }
    normalize(&mut out);
    out
}

/// Requires `a >= b`.
fn sub_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i64;
    for (i, &av_u32) in a.iter().enumerate() {
        let av = i64::from(av_u32);
        let bv = b.get(i).copied().map_or(0, i64::from);
        let mut diff = av - bv - borrow;
        if diff < 0 {
            diff += 1i64 << 32;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out.push(diff as u32);
    }
    normalize(&mut out);
    out
}

fn mul_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u32; a.len() + b.len()];
    for (i, &av) in a.iter().enumerate() {
        let av64 = u64::from(av);
        let mut carry = 0u64;
        for (j, &bv) in b.iter().enumerate() {
            let cur = u64::from(out[i + j]) + av64 * u64::from(bv) + carry;
            out[i + j] = (cur & 0xFFFF_FFFF) as u32;
            carry = cur >> 32;
        }
        out[i + b.len()] = (u64::from(out[i + b.len()]) + carry) as u32;
    }
    normalize(&mut out);
    out
}

fn bit_len(a: &[u32]) -> usize {
    match a.last() {
        None => 0,
        Some(&top) => (a.len() - 1) * 32 + (32 - top.leading_zeros() as usize),
    }
}

fn get_bit(a: &[u32], bit_idx: usize) -> u32 {
    let limb_idx = bit_idx / 32;
    let shift = bit_idx % 32;
    a.get(limb_idx).copied().map_or(0, |l| (l >> shift) & 1)
}

fn has_any_bit_below(a: &[u32], bit_idx: usize) -> bool {
    let full_limbs = bit_idx / 32;
    let rem_bits = bit_idx % 32;
    if a.iter().take(full_limbs).any(|&l| l != 0) {
        return true;
    }
    if rem_bits > 0 && full_limbs < a.len() {
        let mask = (1u32 << rem_bits) - 1;
        if (a[full_limbs] & mask) != 0 {
            return true;
        }
    }
    false
}

fn shl1_add_bit(limbs: &mut Vec<u32>, bit: u32) {
    let mut carry = bit & 1;
    for l in limbs.iter_mut() {
        let next_carry = *l >> 31;
        *l = (*l << 1) | carry;
        carry = next_carry;
    }
    if carry != 0 {
        limbs.push(carry);
    }
}

fn div_rem_u32(a: &[u32], d: u32) -> (Vec<u32>, u32) {
    let d64 = u64::from(d);
    let mut q = vec![0u32; a.len()];
    let mut rem = 0u64;
    for i in (0..a.len()).rev() {
        let cur = (rem << 32) | u64::from(a[i]);
        q[i] = (cur / d64) as u32;
        rem = cur % d64;
    }
    normalize(&mut q);
    (q, rem as u32)
}

/// Requires `!b.is_empty()`.
fn div_rem_mag(a: &[u32], b: &[u32]) -> (Vec<u32>, Vec<u32>) {
    if cmp_mag(a, b) == Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    if b.len() == 1 {
        let (q, rem) = div_rem_u32(a, b[0]);
        let r = if rem == 0 { Vec::new() } else { vec![rem] };
        return (q, r);
    }
    let total_bits = bit_len(a);
    let mut q = vec![0u32; a.len()];
    let mut r: Vec<u32> = Vec::new();
    for bit_idx in (0..total_bits).rev() {
        let bit = get_bit(a, bit_idx);
        shl1_add_bit(&mut r, bit);
        if cmp_mag(&r, b) != Ordering::Less {
            r = sub_mag(&r, b);
            q[bit_idx / 32] |= 1u32 << (bit_idx % 32);
        }
    }
    normalize(&mut q);
    normalize(&mut r);
    (q, r)
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_negative(), other.is_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => cmp_mag(&self.limbs, &other.limbs),
            (true, true) => cmp_mag(&other.limbs, &self.limbs),
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Neg for &BigInt {
    type Output = BigInt;
    fn neg(self) -> BigInt {
        BigInt {
            neg: !self.neg && !self.limbs.is_empty(),
            limbs: self.limbs.clone(),
        }
    }
}

impl Neg for BigInt {
    type Output = BigInt;
    fn neg(mut self) -> BigInt {
        if !self.limbs.is_empty() {
            self.neg = !self.neg;
        }
        self
    }
}

impl Add for &BigInt {
    type Output = BigInt;
    fn add(self, rhs: &BigInt) -> BigInt {
        if self.neg == rhs.neg {
            BigInt::from_sign_limbs(self.neg, add_mag(&self.limbs, &rhs.limbs))
        } else {
            match cmp_mag(&self.limbs, &rhs.limbs) {
                Ordering::Equal => BigInt::ZERO,
                Ordering::Greater => {
                    BigInt::from_sign_limbs(self.neg, sub_mag(&self.limbs, &rhs.limbs))
                }
                Ordering::Less => {
                    BigInt::from_sign_limbs(rhs.neg, sub_mag(&rhs.limbs, &self.limbs))
                }
            }
        }
    }
}

impl Add for BigInt {
    type Output = BigInt;
    fn add(self, rhs: BigInt) -> BigInt {
        &self + &rhs
    }
}

impl Sub for &BigInt {
    type Output = BigInt;
    fn sub(self, rhs: &BigInt) -> BigInt {
        self + &(-rhs)
    }
}

impl Sub for BigInt {
    type Output = BigInt;
    fn sub(self, rhs: BigInt) -> BigInt {
        &self - &rhs
    }
}

impl Mul for &BigInt {
    type Output = BigInt;
    fn mul(self, rhs: &BigInt) -> BigInt {
        BigInt::from_sign_limbs(self.neg != rhs.neg, mul_mag(&self.limbs, &rhs.limbs))
    }
}

impl Mul for BigInt {
    type Output = BigInt;
    fn mul(self, rhs: BigInt) -> BigInt {
        &self * &rhs
    }
}

impl From<i32> for BigInt {
    fn from(v: i32) -> Self {
        Self::from(i128::from(v))
    }
}

impl From<i64> for BigInt {
    fn from(v: i64) -> Self {
        Self::from(i128::from(v))
    }
}

impl From<i128> for BigInt {
    fn from(v: i128) -> Self {
        Self::from_u128_sign(v < 0, v.unsigned_abs())
    }
}

impl From<u64> for BigInt {
    fn from(v: u64) -> Self {
        Self::from_u128_sign(false, u128::from(v))
    }
}

impl From<usize> for BigInt {
    fn from(v: usize) -> Self {
        Self::from_u128_sign(false, v as u128)
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.limbs.is_empty() {
            return f.write_str("0");
        }
        if self.neg {
            f.write_str("-")?;
        }
        const CHUNK_BASE: u32 = 1_000_000_000;
        let mut cur = self.limbs.clone();
        let mut chunks: Vec<u32> = Vec::new();
        while !cur.is_empty() {
            let (q, rem) = div_rem_u32(&cur, CHUNK_BASE);
            chunks.push(rem);
            cur = q;
        }
        if let Some((&top, rest)) = chunks.split_last() {
            write!(f, "{top}")?;
            for &chunk in rest.iter().rev() {
                write!(f, "{chunk:09}")?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseBigIntError;

impl fmt::Display for ParseBigIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid integer literal")
    }
}

impl std::error::Error for ParseBigIntError {}

impl FromStr for BigInt {
    type Err = ParseBigIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (neg, digits) = match s.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, s),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(ParseBigIntError);
        }
        let mut acc: Vec<u32> = Vec::new();
        for chunk in digits.as_bytes().chunks(9) {
            let mut chunk_val = 0u32;
            let mut chunk_mul = 1u32;
            for &b in chunk {
                chunk_val = chunk_val * 10 + u32::from(b - b'0');
                chunk_mul *= 10;
            }
            if !acc.is_empty() {
                acc = mul_mag(&acc, &[chunk_mul]);
            }
            if chunk_val != 0 {
                acc = add_mag(&acc, &[chunk_val]);
            }
        }
        Ok(Self::from_sign_limbs(neg, acc))
    }
}
