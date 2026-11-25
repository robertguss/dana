//! Canonical `val_eq`-consistent columnar hashing and comparison for
//! zero-allocation `HashJoin`, `HashAggregate`, `Distinct`, and `Window`.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use crate::core::syntax::Float64;
use crate::oracle::value::{Val, float_order_key, val_cmp, val_eq};
use crate::vm::batch::{Column, ColumnData};

/// Fast, deterministic FNV-1a / Sip-free 64-bit mixer (`FxHash`-style) for internal
/// hash tables and deterministic radix partitioning (never exposed externally).
#[derive(Clone, Copy, Debug)]
pub struct FastHasher(u64);

impl Default for FastHasher {
    fn default() -> Self {
        Self(0x517C_C1B7_2722_0A95)
    }
}

impl FastHasher {
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(0x517C_C1B7_2722_0A95)
    }

    #[inline]
    fn mix_u64(&mut self, v: u64) {
        self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x517C_C1B7_2722_0A95);
    }

    #[inline]
    #[must_use]
    pub const fn finish_u64(&self) -> u64 {
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

impl Hasher for FastHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.finish_u64()
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let (chunks, rem) = bytes.as_chunks::<8>();
        for &c in chunks {
            self.mix_u64(u64::from_le_bytes(c));
        }
        if !rem.is_empty() {
            let mut tail = [0u8; 8];
            tail[..rem.len()].copy_from_slice(rem);
            self.mix_u64(u64::from_le_bytes(tail));
        }
        self.mix_u64(bytes.len() as u64);
    }

    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.mix_u64(u64::from(i));
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.mix_u64(i);
    }

    #[inline]
    fn write_i64(&mut self, i: i64) {
        self.mix_u64(i as u64);
    }

    #[inline]
    fn write_i128(&mut self, i: i128) {
        self.mix_u64(i as u64);
        self.mix_u64((i as u128 >> 64) as u64);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.mix_u64(i as u64);
    }
}

/// Hash a [`Val`] consistently with `val_eq` AND with [`hash_col_cell`].
pub fn hash_val<H: Hasher>(v: &Val, h: &mut H) {
    match v {
        Val::OptNone => h.write_u8(0),
        Val::Unit => h.write_u8(1),
        Val::Bool(b) => {
            h.write_u8(2);
            h.write_u8(u8::from(*b));
        }
        Val::Int(n) => {
            if let Some(x) = n.to_i64() {
                h.write_u8(3);
                h.write_i64(x);
            } else {
                h.write_u8(30);
                n.hash(h);
            }
        }
        Val::Decimal(d) => {
            if let Some(x) = d.to_i128() {
                h.write_u8(4);
                h.write_i128(x);
            } else {
                h.write_u8(40);
                d.hash(h);
            }
        }
        Val::Float(f) => {
            h.write_u8(5);
            h.write_u64(f.bits);
        }
        Val::Text(s) => {
            h.write_u8(6);
            h.write(s.as_bytes());
        }
        Val::Bytes(bs) => {
            h.write_u8(7);
            h.write(bs);
        }
        Val::Date(d) => {
            if let Some(x) = d.to_i64() {
                h.write_u8(8);
                h.write_i64(x);
            } else {
                h.write_u8(80);
                d.hash(h);
            }
        }
        Val::Timestamp(ts) => {
            if let Some(x) = ts.to_i64() {
                h.write_u8(9);
                h.write_i64(x);
            } else {
                h.write_u8(90);
                ts.hash(h);
            }
        }
        Val::Duration(dur) => {
            if let Some(x) = dur.to_i64() {
                h.write_u8(10);
                h.write_i64(x);
            } else {
                h.write_u8(100);
                dur.hash(h);
            }
        }
        Val::OptSome(inner) => {
            h.write_u8(11);
            hash_val(inner, h);
        }
        Val::ResOk(inner) => {
            h.write_u8(12);
            hash_val(inner, h);
        }
        Val::ResErr(inner) => {
            h.write_u8(13);
            hash_val(inner, h);
        }
        Val::Tuple(xs) => {
            h.write_u8(14);
            h.write_usize(xs.len());
            for x in xs {
                hash_val(x, h);
            }
        }
        Val::List(xs) => {
            h.write_u8(15);
            h.write_usize(xs.len());
            for x in xs {
                hash_val(x, h);
            }
        }
        Val::Map(pairs) => {
            h.write_u8(16);
            h.write_usize(pairs.len());
            for (k, val) in pairs {
                hash_val(k, h);
                hash_val(val, h);
            }
        }
        Val::Ctor {
            type_name,
            ctor_name,
            fields,
        } => {
            h.write_u8(17);
            h.write(type_name.as_bytes());
            h.write(ctor_name.as_bytes());
            h.write_usize(fields.len());
            for f in fields {
                hash_val(f, h);
            }
        }
        Val::LinearModel {
            slope,
            intercept,
            r2,
        } => {
            h.write_u8(23);
            h.write_u64(slope.bits);
            h.write_u64(intercept.bits);
            h.write_u64(r2.bits);
        }
        Val::StatTest { stat, p_value } => {
            h.write_u8(24);
            h.write_u64(stat.bits);
            h.write_u64(p_value.bits);
        }
        Val::Profile(p) => {
            h.write_u8(22);
            p.hash(h);
        }
        _ => {
            h.write_u8(25);
        }
    }
}

/// Zero-allocation columnar cell hash guaranteed to produce the exact same hash
/// stream as `hash_val(&col.get_val(row), h)`.
#[inline]
pub fn hash_col_cell<H: Hasher>(col: &Column, row: usize, h: &mut H) {
    if let Some(bm) = &col.validity {
        if !bm.is_valid(row) {
            h.write_u8(0);
            return;
        }
        h.write_u8(11);
    }
    match &col.data {
        ColumnData::Unit(_) => h.write_u8(1),
        ColumnData::Bool(v) => {
            h.write_u8(2);
            h.write_u8(v[row]);
        }
        ColumnData::Int(v) => {
            h.write_u8(3);
            h.write_i64(v[row]);
        }
        ColumnData::Decimal(v) => {
            h.write_u8(4);
            h.write_i128(v[row]);
        }
        ColumnData::Float(v) => {
            h.write_u8(5);
            h.write_u64(v[row]);
        }
        ColumnData::Text { offsets, data } => {
            h.write_u8(6);
            h.write(&data[offsets[row]..offsets[row + 1]]);
        }
        ColumnData::Bytes { offsets, data } => {
            h.write_u8(7);
            h.write(&data[offsets[row]..offsets[row + 1]]);
        }
        ColumnData::Date(v) => {
            h.write_u8(8);
            h.write_i64(v[row]);
        }
        ColumnData::Timestamp(v) => {
            h.write_u8(9);
            h.write_i64(v[row]);
        }
        ColumnData::Duration(v) => {
            h.write_u8(10);
            h.write_i64(v[row]);
        }
        ColumnData::Generic(v) => hash_val(&v[row], h),
    }
}

/// Compute a 64-bit hash of a composite key across `key_cols` at `row` with zero allocations.
#[inline]
#[must_use]
pub fn hash_row_key(cols: &[Column], key_idxs: &[usize], row: usize) -> u64 {
    let mut h = FastHasher::new();
    for &ci in key_idxs {
        hash_col_cell(&cols[ci], row, &mut h);
    }
    h.finish_u64()
}

/// Compute a 64-bit hash of a slice of `Val`s.
#[inline]
#[must_use]
pub fn hash_val_slice(vals: &[Val]) -> u64 {
    let mut h = FastHasher::new();
    for v in vals {
        hash_val(v, &mut h);
    }
    h.finish_u64()
}

/// Zero-allocation equality check between cell `(col_a, row_a)` and `(col_b, row_b)`.
#[inline]
#[must_use]
pub fn eq_col_cells(col_a: &Column, row_a: usize, col_b: &Column, row_b: usize) -> bool {
    match (&col_a.validity, &col_b.validity) {
        (Some(ba), Some(bb)) => {
            let va = ba.is_valid(row_a);
            let vb = bb.is_valid(row_b);
            if va != vb {
                return false;
            }
            if !va {
                return true;
            }
        }
        (None, None) => {}
        _ => return val_eq(&col_a.get_val(row_a), &col_b.get_val(row_b)),
    }
    match (&col_a.data, &col_b.data) {
        (ColumnData::Unit(_), ColumnData::Unit(_)) => true,
        (ColumnData::Bool(a), ColumnData::Bool(b)) => a[row_a] == b[row_b],
        (ColumnData::Int(a), ColumnData::Int(b))
        | (ColumnData::Date(a), ColumnData::Date(b))
        | (ColumnData::Timestamp(a), ColumnData::Timestamp(b))
        | (ColumnData::Duration(a), ColumnData::Duration(b)) => a[row_a] == b[row_b],
        (ColumnData::Decimal(a), ColumnData::Decimal(b)) => a[row_a] == b[row_b],
        (ColumnData::Float(a), ColumnData::Float(b)) => a[row_a] == b[row_b],
        (
            ColumnData::Text {
                offsets: oa,
                data: da,
            },
            ColumnData::Text {
                offsets: ob,
                data: db,
            },
        )
        | (
            ColumnData::Bytes {
                offsets: oa,
                data: da,
            },
            ColumnData::Bytes {
                offsets: ob,
                data: db,
            },
        ) => da[oa[row_a]..oa[row_a + 1]] == db[ob[row_b]..ob[row_b + 1]],
        (ColumnData::Generic(a), ColumnData::Generic(b)) => val_eq(&a[row_a], &b[row_b]),
        _ => val_eq(&col_a.get_val(row_a), &col_b.get_val(row_b)),
    }
}

/// Zero-allocation structural comparison matching [`val_cmp`] on two columnar cells.
#[inline]
#[must_use]
pub fn cmp_col_cells(col_a: &Column, row_a: usize, col_b: &Column, row_b: usize) -> Ordering {
    match (&col_a.validity, &col_b.validity) {
        (Some(ba), Some(bb)) => match (ba.is_valid(row_a), bb.is_valid(row_b)) {
            (false, false) => return Ordering::Equal,
            (false, true) => return Ordering::Less,
            (true, false) => return Ordering::Greater,
            (true, true) => {}
        },
        (None, None) => {}
        _ => return val_cmp(&col_a.get_val(row_a), &col_b.get_val(row_b)),
    }
    match (&col_a.data, &col_b.data) {
        (ColumnData::Unit(_), ColumnData::Unit(_)) => Ordering::Equal,
        (ColumnData::Bool(a), ColumnData::Bool(b)) => a[row_a].cmp(&b[row_b]),
        (ColumnData::Int(a), ColumnData::Int(b))
        | (ColumnData::Date(a), ColumnData::Date(b))
        | (ColumnData::Timestamp(a), ColumnData::Timestamp(b))
        | (ColumnData::Duration(a), ColumnData::Duration(b)) => a[row_a].cmp(&b[row_b]),
        (ColumnData::Decimal(a), ColumnData::Decimal(b)) => a[row_a].cmp(&b[row_b]),
        (ColumnData::Float(a), ColumnData::Float(b)) => {
            float_order_key(Float64::from_bits(a[row_a]))
                .cmp(&float_order_key(Float64::from_bits(b[row_b])))
        }
        (
            ColumnData::Text {
                offsets: oa,
                data: da,
            },
            ColumnData::Text {
                offsets: ob,
                data: db,
            },
        )
        | (
            ColumnData::Bytes {
                offsets: oa,
                data: da,
            },
            ColumnData::Bytes {
                offsets: ob,
                data: db,
            },
        ) => da[oa[row_a]..oa[row_a + 1]].cmp(&db[ob[row_b]..ob[row_b + 1]]),
        (ColumnData::Generic(a), ColumnData::Generic(b)) => val_cmp(&a[row_a], &b[row_b]),
        _ => val_cmp(&col_a.get_val(row_a), &col_b.get_val(row_b)),
    }
}

/// Wrapper around `Vec<Val>` implementing `PartialEq`, `Eq`, and `Hash` using
/// canonical [`val_eq`] and [`hash_val`].
#[derive(Clone, Debug)]
pub struct KeyTuple {
    pub vals: Vec<Val>,
    pub hash: u64,
}

impl KeyTuple {
    #[must_use]
    pub fn new(vals: Vec<Val>) -> Self {
        let hash = hash_val_slice(&vals);
        Self { vals, hash }
    }
}

impl PartialEq for KeyTuple {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
            && self.vals.len() == other.vals.len()
            && self.vals.iter().zip(&other.vals).all(|(a, b)| val_eq(a, b))
    }
}

impl Eq for KeyTuple {}

impl Hash for KeyTuple {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

/// Single-value key wrapper implementing `PartialEq`, `Eq`, `Hash` via `val_eq` + `hash_val`.
#[derive(Clone, Debug)]
pub struct SingleKey {
    pub val: Val,
    pub hash: u64,
}

impl SingleKey {
    #[must_use]
    pub fn new(val: Val) -> Self {
        let mut h = FastHasher::new();
        hash_val(&val, &mut h);
        Self {
            val,
            hash: h.finish_u64(),
        }
    }
}

impl PartialEq for SingleKey {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && val_eq(&self.val, &other.val)
    }
}

impl Eq for SingleKey {}

impl Hash for SingleKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}
