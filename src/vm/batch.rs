//! 2,048-row columnar batch representation with bit-packed null bitmaps,
//! contiguous typed vectors, Arrow-style offset string/bytes buffers,
//! and selection-vector compaction.

use crate::core::bigint::BigInt;
use crate::core::syntax::{ColSpec, Float64, ScalarTy};
use crate::oracle::value::{GroupMeta, TableRow, TableVal, Val};

/// Default vectorized batch size (2,048 rows — L1/L2 cache-resident per column).
pub const BATCH_SIZE: usize = 2_048;

/// Bit-packed validity bitmap (`1` = present / `Some`, `0` = null / `None`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NullBitmap {
    words: Vec<u64>,
    len: usize,
}

impl NullBitmap {
    #[must_use]
    pub fn all_valid(len: usize) -> Self {
        let n_words = len.div_ceil(64);
        let mut words = vec![u64::MAX; n_words];
        let rem = len % 64;
        if rem != 0
            && let Some(last) = words.last_mut()
        {
            *last = (1u64 << rem) - 1;
        }
        Self { words, len }
    }

    #[must_use]
    pub fn all_null(len: usize) -> Self {
        let n_words = len.div_ceil(64);
        Self {
            words: vec![0u64; n_words],
            len,
        }
    }

    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            words: Vec::with_capacity(cap.div_ceil(64)),
            len: 0,
        }
    }

    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    #[must_use]
    pub fn is_valid(&self, idx: usize) -> bool {
        let word = idx >> 6;
        let bit = idx & 63;
        self.words
            .get(word)
            .is_some_and(|&w| ((w >> bit) & 1u64) != 0)
    }

    #[inline]
    pub fn set_valid(&mut self, idx: usize, valid: bool) {
        let word = idx >> 6;
        let bit = idx & 63;
        if let Some(w) = self.words.get_mut(word) {
            if valid {
                *w |= 1u64 << bit;
            } else {
                *w &= !(1u64 << bit);
            }
        }
    }

    #[inline]
    pub fn push(&mut self, valid: bool) {
        let word = self.len >> 6;
        let bit = self.len & 63;
        if word >= self.words.len() {
            self.words.push(0);
        }
        if valid {
            self.words[word] |= 1u64 << bit;
        }
        self.len += 1;
    }

    #[must_use]
    pub fn count_valid(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    #[must_use]
    pub fn select(&self, sel: &[u16]) -> Self {
        let mut out = Self::with_capacity(sel.len());
        for &r in sel {
            out.push(self.is_valid(usize::from(r)));
        }
        out
    }

    #[must_use]
    pub fn slice(&self, start: usize, count: usize) -> Self {
        let end = (start + count).min(self.len);
        let mut out = Self::with_capacity(end.saturating_sub(start));
        for i in start..end {
            out.push(self.is_valid(i));
        }
        out
    }
}

/// Contiguous typed columnar payload for a single column inside a [`Batch`].
#[derive(Clone, Debug)]
pub enum ColumnData {
    Unit(usize),
    Bool(Vec<u8>),
    Int(Vec<i64>),
    Decimal(Vec<i128>),
    /// Canonical IEEE-754 binary64 bit patterns (`Float64::bits`).
    Float(Vec<u64>),
    /// Arrow-style contiguous UTF-8 offset buffer (`offsets.len() == rows + 1`).
    Text {
        offsets: Vec<usize>,
        data: Vec<u8>,
    },
    /// Arrow-style contiguous byte buffer (`offsets.len() == rows + 1`).
    Bytes {
        offsets: Vec<usize>,
        data: Vec<u8>,
    },
    Date(Vec<i64>),
    Timestamp(Vec<i64>),
    Duration(Vec<i64>),
    /// Fallback for ADTs (`ScalarTy::Data`), nested `Option(Option(T))`, or heterogeneous values.
    Generic(Vec<Val>),
}

impl ColumnData {
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Self::Unit(n) => *n,
            Self::Bool(v) => v.len(),
            Self::Int(v) | Self::Date(v) | Self::Timestamp(v) | Self::Duration(v) => v.len(),
            Self::Decimal(v) => v.len(),
            Self::Float(v) => v.len(),
            Self::Text { offsets, .. } | Self::Bytes { offsets, .. } => {
                offsets.len().saturating_sub(1)
            }
            Self::Generic(v) => v.len(),
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[must_use]
    pub fn text_at(&self, row: usize) -> Option<&str> {
        let Self::Text { offsets, data } = self else {
            return None;
        };
        let start = *offsets.get(row)?;
        let end = *offsets.get(row + 1)?;
        let bytes = data.get(start..end)?;
        std::str::from_utf8(bytes).ok()
    }

    #[inline]
    #[must_use]
    pub fn bytes_at(&self, row: usize) -> Option<&[u8]> {
        let Self::Bytes { offsets, data } = self else {
            return None;
        };
        let start = *offsets.get(row)?;
        let end = *offsets.get(row + 1)?;
        data.get(start..end)
    }

    /// Extract the non-null underlying scalar `Val` at `row` (ignoring any outer `NullBitmap`).
    #[must_use]
    pub fn get_raw_val(&self, row: usize) -> Val {
        match self {
            Self::Unit(_) => Val::Unit,
            Self::Bool(v) => Val::Bool(v.get(row).copied().unwrap_or(0) != 0),
            Self::Int(v) => Val::Int(BigInt::from(v.get(row).copied().unwrap_or(0))),
            Self::Decimal(v) => Val::Decimal(BigInt::from(v.get(row).copied().unwrap_or(0))),
            Self::Float(v) => Val::Float(Float64::from_bits(v.get(row).copied().unwrap_or(0))),
            Self::Text { .. } => Val::Text(self.text_at(row).unwrap_or("").to_string()),
            Self::Bytes { .. } => Val::Bytes(self.bytes_at(row).unwrap_or(&[]).to_vec()),
            Self::Date(v) => Val::Date(BigInt::from(v.get(row).copied().unwrap_or(0))),
            Self::Timestamp(v) => Val::Timestamp(BigInt::from(v.get(row).copied().unwrap_or(0))),
            Self::Duration(v) => Val::Duration(BigInt::from(v.get(row).copied().unwrap_or(0))),
            Self::Generic(v) => v.get(row).cloned().unwrap_or(Val::Unit),
        }
    }

    #[must_use]
    pub fn select(&self, sel: &[u16]) -> Self {
        match self {
            Self::Unit(_) => Self::Unit(sel.len()),
            Self::Bool(v) => Self::Bool(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Int(v) => Self::Int(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Decimal(v) => Self::Decimal(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Float(v) => Self::Float(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Date(v) => Self::Date(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Timestamp(v) => Self::Timestamp(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Duration(v) => Self::Duration(sel.iter().map(|&r| v[usize::from(r)]).collect()),
            Self::Text { offsets, data } => {
                let mut new_offsets = Vec::with_capacity(sel.len() + 1);
                let mut new_data = Vec::new();
                new_offsets.push(0);
                for &r in sel {
                    let ri = usize::from(r);
                    let slice = &data[offsets[ri]..offsets[ri + 1]];
                    new_data.extend_from_slice(slice);
                    new_offsets.push(new_data.len());
                }
                Self::Text {
                    offsets: new_offsets,
                    data: new_data,
                }
            }
            Self::Bytes { offsets, data } => {
                let mut new_offsets = Vec::with_capacity(sel.len() + 1);
                let mut new_data = Vec::new();
                new_offsets.push(0);
                for &r in sel {
                    let ri = usize::from(r);
                    let slice = &data[offsets[ri]..offsets[ri + 1]];
                    new_data.extend_from_slice(slice);
                    new_offsets.push(new_data.len());
                }
                Self::Bytes {
                    offsets: new_offsets,
                    data: new_data,
                }
            }
            Self::Generic(v) => {
                Self::Generic(sel.iter().map(|&r| v[usize::from(r)].clone()).collect())
            }
        }
    }

    #[must_use]
    pub fn slice(&self, start: usize, count: usize) -> Self {
        let end = (start + count).min(self.len());
        match self {
            Self::Unit(_) => Self::Unit(end.saturating_sub(start)),
            Self::Bool(v) => Self::Bool(v[start..end].to_vec()),
            Self::Int(v) => Self::Int(v[start..end].to_vec()),
            Self::Decimal(v) => Self::Decimal(v[start..end].to_vec()),
            Self::Float(v) => Self::Float(v[start..end].to_vec()),
            Self::Date(v) => Self::Date(v[start..end].to_vec()),
            Self::Timestamp(v) => Self::Timestamp(v[start..end].to_vec()),
            Self::Duration(v) => Self::Duration(v[start..end].to_vec()),
            Self::Text { offsets, data } => {
                if start >= end {
                    return Self::Text {
                        offsets: vec![0],
                        data: Vec::new(),
                    };
                }
                let base = offsets[start];
                let end_byte = offsets[end];
                let new_offsets = offsets[start..=end].iter().map(|&o| o - base).collect();
                let new_data = data[base..end_byte].to_vec();
                Self::Text {
                    offsets: new_offsets,
                    data: new_data,
                }
            }
            Self::Bytes { offsets, data } => {
                if start >= end {
                    return Self::Bytes {
                        offsets: vec![0],
                        data: Vec::new(),
                    };
                }
                let base = offsets[start];
                let end_byte = offsets[end];
                let new_offsets = offsets[start..=end].iter().map(|&o| o - base).collect();
                let new_data = data[base..end_byte].to_vec();
                Self::Bytes {
                    offsets: new_offsets,
                    data: new_data,
                }
            }
            Self::Generic(v) => Self::Generic(v[start..end].to_vec()),
        }
    }
}

/// One typed column inside a [`Batch`], carrying its [`ColSpec`] metadata,
/// contiguous [`ColumnData`], and optional bit-packed [`NullBitmap`].
#[derive(Clone, Debug)]
pub struct Column {
    pub spec: ColSpec,
    pub data: ColumnData,
    /// `None` for non-nullable columns (`T`) or `ColumnData::Generic` (where `Val` itself
    /// encodes `OptNone`/`OptSome`). `Some(bitmap)` for single-level `Option(T)` columns.
    pub validity: Option<NullBitmap>,
}

impl Column {
    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    #[must_use]
    pub fn get_val(&self, row: usize) -> Val {
        if let Some(bm) = &self.validity {
            if bm.is_valid(row) {
                Val::OptSome(Box::new(self.data.get_raw_val(row)))
            } else {
                Val::OptNone
            }
        } else {
            self.data.get_raw_val(row)
        }
    }

    #[must_use]
    pub fn select(&self, sel: &[u16]) -> Self {
        Self {
            spec: self.spec.clone(),
            data: self.data.select(sel),
            validity: self.validity.as_ref().map(|bm| bm.select(sel)),
        }
    }

    #[must_use]
    pub fn slice(&self, start: usize, count: usize) -> Self {
        Self {
            spec: self.spec.clone(),
            data: self.data.slice(start, count),
            validity: self.validity.as_ref().map(|bm| bm.slice(start, count)),
        }
    }

    /// Construct a columnar [`Column`] from a slice of [`Val`]s using `spec.ty` (or
    /// dynamically inferring the contiguous column layout when `spec.ty == ScalarTy::Unit`).
    #[must_use]
    pub fn from_vals(spec: ColSpec, vals: &[Val]) -> Self {
        let target_ty = if spec.ty == ScalarTy::Unit {
            infer_scalar_ty_from_vals(vals).unwrap_or(ScalarTy::Unit)
        } else {
            spec.ty.clone()
        };
        let (data, validity) = pack_vals_for_scalar_ty(&target_ty, vals);
        Self {
            spec,
            data,
            validity,
        }
    }

    /// Construct a columnar [`Column`] from a slice of `TableRow`s at column index `col_idx`.
    #[must_use]
    pub fn from_table_rows(spec: ColSpec, rows: &[TableRow], col_idx: usize) -> Self {
        let target_ty = if spec.ty == ScalarTy::Unit {
            infer_scalar_ty_from_rows(rows, col_idx).unwrap_or(ScalarTy::Unit)
        } else {
            spec.ty.clone()
        };
        let (data, validity) = pack_rows_for_scalar_ty(&target_ty, rows, col_idx);
        Self {
            spec,
            data,
            validity,
        }
    }

    /// Convert to a `Generic` column if needed for heterogeneous merges.
    #[must_use]
    pub fn to_vals(&self) -> Vec<Val> {
        (0..self.len()).map(|i| self.get_val(i)).collect()
    }
}

fn scalar_ty_of_val(v: &Val) -> Option<ScalarTy> {
    match v {
        Val::Unit => Some(ScalarTy::Unit),
        Val::Bool(_) => Some(ScalarTy::Bool),
        Val::Int(_) => Some(ScalarTy::Int),
        Val::Decimal(_) => Some(ScalarTy::Decimal),
        Val::Float(_) => Some(ScalarTy::Float),
        Val::Text(_) => Some(ScalarTy::Text),
        Val::Bytes(_) => Some(ScalarTy::Bytes),
        Val::Date(_) => Some(ScalarTy::Date),
        Val::Timestamp(_) => Some(ScalarTy::Timestamp),
        Val::Duration(_) => Some(ScalarTy::Duration),
        Val::Ctor { type_name, .. } => Some(ScalarTy::Data(type_name.clone())),
        Val::OptSome(inner) => scalar_ty_of_val(inner).map(|t| ScalarTy::Option(Box::new(t))),
        _ => None,
    }
}

fn infer_scalar_ty_from_vals(vals: &[Val]) -> Option<ScalarTy> {
    let mut saw_none = false;
    let mut inferred: Option<ScalarTy> = None;
    for v in vals {
        match v {
            Val::OptNone => saw_none = true,
            Val::OptSome(inner) => {
                saw_none = true;
                let inner_ty = scalar_ty_of_val(inner)?;
                if inner_ty.is_option() {
                    return None;
                }
                match &inferred {
                    None => inferred = Some(inner_ty),
                    Some(prev) if *prev == inner_ty => {}
                    Some(_) => return None,
                }
            }
            other => {
                let ty = scalar_ty_of_val(other)?;
                match &inferred {
                    None => inferred = Some(ty),
                    Some(prev) if *prev == ty => {}
                    Some(_) => return None,
                }
            }
        }
    }
    match (saw_none, inferred) {
        (true, Some(inner)) => Some(ScalarTy::Option(Box::new(inner))),
        (false, Some(ty)) => Some(ty),
        _ => None,
    }
}

fn infer_scalar_ty_from_rows(rows: &[TableRow], col_idx: usize) -> Option<ScalarTy> {
    let mut saw_none = false;
    let mut inferred: Option<ScalarTy> = None;
    for r in rows {
        let v = r.cells.get(col_idx)?;
        match v {
            Val::OptNone => saw_none = true,
            Val::OptSome(inner) => {
                saw_none = true;
                let inner_ty = scalar_ty_of_val(inner)?;
                if inner_ty.is_option() {
                    return None;
                }
                match &inferred {
                    None => inferred = Some(inner_ty),
                    Some(prev) if *prev == inner_ty => {}
                    Some(_) => return None,
                }
            }
            other => {
                let ty = scalar_ty_of_val(other)?;
                match &inferred {
                    None => inferred = Some(ty),
                    Some(prev) if *prev == ty => {}
                    Some(_) => return None,
                }
            }
        }
    }
    match (saw_none, inferred) {
        (true, Some(inner)) => Some(ScalarTy::Option(Box::new(inner))),
        (false, Some(ty)) => Some(ty),
        _ => None,
    }
}

fn pack_vals_for_scalar_ty(ty: &ScalarTy, vals: &[Val]) -> (ColumnData, Option<NullBitmap>) {
    match ty {
        ScalarTy::Option(inner) if !inner.is_option() => {
            if let Some((data, bm)) = try_pack_nullable(inner, vals.len(), |i| &vals[i]) {
                return (data, Some(bm));
            }
            (ColumnData::Generic(vals.to_vec()), None)
        }
        other => {
            if let Some(data) = try_pack_non_null(other, vals.len(), |i| &vals[i]) {
                return (data, None);
            }
            (ColumnData::Generic(vals.to_vec()), None)
        }
    }
}

fn pack_rows_for_scalar_ty(
    ty: &ScalarTy,
    rows: &[TableRow],
    col_idx: usize,
) -> (ColumnData, Option<NullBitmap>) {
    let fallback = || {
        ColumnData::Generic(
            rows.iter()
                .map(|r| r.cells.get(col_idx).cloned().unwrap_or(Val::Unit))
                .collect(),
        )
    };
    if rows.iter().any(|r| col_idx >= r.cells.len()) {
        return (fallback(), None);
    }
    match ty {
        ScalarTy::Option(inner) if !inner.is_option() => {
            if let Some((data, bm)) =
                try_pack_nullable(inner, rows.len(), |i| &rows[i].cells[col_idx])
            {
                return (data, Some(bm));
            }
            (fallback(), None)
        }
        other => {
            if let Some(data) = try_pack_non_null(other, rows.len(), |i| &rows[i].cells[col_idx]) {
                return (data, None);
            }
            (fallback(), None)
        }
    }
}

fn try_pack_non_null<'a, F>(ty: &ScalarTy, n: usize, get: F) -> Option<ColumnData>
where
    F: Fn(usize) -> &'a Val,
{
    match ty {
        ScalarTy::Unit => {
            for i in 0..n {
                if !matches!(get(i), Val::Unit) {
                    return None;
                }
            }
            Some(ColumnData::Unit(n))
        }
        ScalarTy::Bool => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Bool(b) = get(i) else { return None };
                out.push(u8::from(*b));
            }
            Some(ColumnData::Bool(out))
        }
        ScalarTy::Int => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Int(x) = get(i) else { return None };
                out.push(x.to_i64()?);
            }
            Some(ColumnData::Int(out))
        }
        ScalarTy::Decimal => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Decimal(d) = get(i) else {
                    return None;
                };
                out.push(d.to_i128()?);
            }
            Some(ColumnData::Decimal(out))
        }
        ScalarTy::Float => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Float(f) = get(i) else { return None };
                out.push(f.bits);
            }
            Some(ColumnData::Float(out))
        }
        ScalarTy::Text => {
            let mut offsets = Vec::with_capacity(n + 1);
            let mut data = Vec::new();
            offsets.push(0);
            for i in 0..n {
                let Val::Text(s) = get(i) else { return None };
                data.extend_from_slice(s.as_bytes());
                offsets.push(data.len());
            }
            Some(ColumnData::Text { offsets, data })
        }
        ScalarTy::Bytes => {
            let mut offsets = Vec::with_capacity(n + 1);
            let mut data = Vec::new();
            offsets.push(0);
            for i in 0..n {
                let Val::Bytes(bs) = get(i) else {
                    return None;
                };
                data.extend_from_slice(bs);
                offsets.push(data.len());
            }
            Some(ColumnData::Bytes { offsets, data })
        }
        ScalarTy::Date => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Date(x) = get(i) else { return None };
                out.push(x.to_i64()?);
            }
            Some(ColumnData::Date(out))
        }
        ScalarTy::Timestamp => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Timestamp(x) = get(i) else {
                    return None;
                };
                out.push(x.to_i64()?);
            }
            Some(ColumnData::Timestamp(out))
        }
        ScalarTy::Duration => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let Val::Duration(x) = get(i) else {
                    return None;
                };
                out.push(x.to_i64()?);
            }
            Some(ColumnData::Duration(out))
        }
        ScalarTy::Data(_) | ScalarTy::Option(_) => None,
    }
}

fn try_pack_nullable<'a, F>(inner: &ScalarTy, n: usize, get: F) -> Option<(ColumnData, NullBitmap)>
where
    F: Fn(usize) -> &'a Val,
{
    let mut bm = NullBitmap::with_capacity(n);
    match inner {
        ScalarTy::Unit => {
            for i in 0..n {
                match get(i) {
                    Val::OptNone => bm.push(false),
                    Val::OptSome(u) if matches!(u.as_ref(), Val::Unit) => bm.push(true),
                    _ => return None,
                }
            }
            Some((ColumnData::Unit(n), bm))
        }
        ScalarTy::Bool => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Bool(b) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(u8::from(*b));
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Bool(out), bm))
        }
        ScalarTy::Int => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Int(x) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(x.to_i64()?);
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Int(out), bm))
        }
        ScalarTy::Decimal => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Decimal(d) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(d.to_i128()?);
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Decimal(out), bm))
        }
        ScalarTy::Float => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Float(f) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(f.bits);
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Float(out), bm))
        }
        ScalarTy::Text => {
            let mut offsets = Vec::with_capacity(n + 1);
            let mut data = Vec::new();
            offsets.push(0);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        offsets.push(data.len());
                    }
                    Val::OptSome(u) => {
                        let Val::Text(s) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        data.extend_from_slice(s.as_bytes());
                        offsets.push(data.len());
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Text { offsets, data }, bm))
        }
        ScalarTy::Bytes => {
            let mut offsets = Vec::with_capacity(n + 1);
            let mut data = Vec::new();
            offsets.push(0);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        offsets.push(data.len());
                    }
                    Val::OptSome(u) => {
                        let Val::Bytes(bs) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        data.extend_from_slice(bs);
                        offsets.push(data.len());
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Bytes { offsets, data }, bm))
        }
        ScalarTy::Date => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Date(x) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(x.to_i64()?);
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Date(out), bm))
        }
        ScalarTy::Timestamp => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Timestamp(x) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(x.to_i64()?);
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Timestamp(out), bm))
        }
        ScalarTy::Duration => {
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                match get(i) {
                    Val::OptNone => {
                        bm.push(false);
                        out.push(0);
                    }
                    Val::OptSome(u) => {
                        let Val::Duration(x) = u.as_ref() else {
                            return None;
                        };
                        bm.push(true);
                        out.push(x.to_i64()?);
                    }
                    _ => return None,
                }
            }
            Some((ColumnData::Duration(out), bm))
        }
        ScalarTy::Data(_) | ScalarTy::Option(_) => None,
    }
}

/// Columnar batch holding up to `BATCH_SIZE` (2,048) rows with optional active
/// row selection vector and optional group cardinality metadata.
#[derive(Clone, Debug)]
pub struct Batch {
    pub cols: Vec<Column>,
    pub len: usize,
    pub selection: Option<Vec<u16>>,
    pub group_meta: Option<Vec<GroupMeta>>,
}

impl Batch {
    #[must_use]
    pub fn empty_with_schema(specs: &[ColSpec]) -> Self {
        let cols = specs
            .iter()
            .map(|s| Column::from_vals(s.clone(), &[]))
            .collect();
        Self {
            cols,
            len: 0,
            selection: None,
            group_meta: None,
        }
    }

    #[inline]
    #[must_use]
    pub fn active_len(&self) -> usize {
        self.selection.as_ref().map_or(self.len, Vec::len)
    }

    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.active_len() == 0
    }

    #[must_use]
    pub fn col_specs(&self) -> Vec<ColSpec> {
        self.cols.iter().map(|c| c.spec.clone()).collect()
    }

    #[must_use]
    pub fn find_col_idx(&self, name: &str) -> Option<usize> {
        self.cols.iter().position(|c| c.spec.name == name)
    }

    /// Return the active row indices as a compact `Vec<u16>`.
    #[must_use]
    pub fn active_indices(&self) -> Vec<u16> {
        match &self.selection {
            Some(sel) => sel.clone(),
            None => (0..self.len).map(|i| i as u16).collect(),
        }
    }

    /// Materialize the selection vector into contiguous columns (`selection = None`).
    #[must_use]
    pub fn compact(self) -> Self {
        let Some(sel) = self.selection else {
            return self;
        };
        let new_len = sel.len();
        let cols = self.cols.into_iter().map(|c| c.select(&sel)).collect();
        let group_meta = self
            .group_meta
            .map(|gm| sel.iter().map(|&r| gm[usize::from(r)]).collect());
        Self {
            cols,
            len: new_len,
            selection: None,
            group_meta,
        }
    }

    /// Slice `count` active rows starting at active offset `start`.
    #[must_use]
    pub fn take_first(&self, count: usize) -> Self {
        let active = self.active_len();
        let take_n = count.min(active);
        match &self.selection {
            Some(sel) => Self {
                cols: self.cols.clone(),
                len: self.len,
                selection: Some(sel[..take_n].to_vec()),
                group_meta: self.group_meta.clone(),
            },
            None => Self {
                cols: self.cols.iter().map(|c| c.slice(0, take_n)).collect(),
                len: take_n,
                selection: None,
                group_meta: self.group_meta.as_ref().map(|gm| gm[..take_n].to_vec()),
            },
        }
    }
}

/// Convert a row-oriented [`TableVal`] into a vector of columnar [`Batch`]es of at most
/// `batch_size` rows (clamped to `1..=u16::MAX as usize`).
#[must_use]
pub fn table_to_batches(tv: &TableVal, batch_size: usize) -> Vec<Batch> {
    let chunk = batch_size.clamp(1, usize::from(u16::MAX));
    if tv.rows.is_empty() {
        return Vec::new();
    }
    let has_meta = tv.rows.iter().any(|r| r.group_meta.is_some());
    let mut batches = Vec::with_capacity(tv.rows.len().div_ceil(chunk));
    for slice in tv.rows.chunks(chunk) {
        let cols: Vec<Column> = tv
            .cols
            .iter()
            .enumerate()
            .map(|(ci, spec)| Column::from_table_rows(spec.clone(), slice, ci))
            .collect();
        let group_meta = if has_meta {
            Some(
                slice
                    .iter()
                    .map(|r| r.group_meta.unwrap_or_default())
                    .collect(),
            )
        } else {
            None
        };
        batches.push(Batch {
            cols,
            len: slice.len(),
            selection: None,
            group_meta,
        });
    }
    batches
}

/// Materialize columnar [`Batch`]es back into a [`TableVal`].
#[must_use]
pub fn batches_to_table(schema: Vec<ColSpec>, batches: &[Batch]) -> TableVal {
    let total_rows: usize = batches.iter().map(Batch::active_len).sum();
    let mut rows = Vec::with_capacity(total_rows);
    for b in batches {
        if b.is_empty() {
            continue;
        }
        let ncols = b.cols.len();
        match &b.selection {
            Some(sel) => {
                for &r_u16 in sel {
                    let r = usize::from(r_u16);
                    let mut cells = Vec::with_capacity(ncols);
                    for c in &b.cols {
                        cells.push(c.get_val(r));
                    }
                    rows.push(TableRow {
                        cells,
                        group_meta: b.group_meta.as_ref().and_then(|gm| gm.get(r).copied()),
                    });
                }
            }
            None => {
                for r in 0..b.len {
                    let mut cells = Vec::with_capacity(ncols);
                    for c in &b.cols {
                        cells.push(c.get_val(r));
                    }
                    rows.push(TableRow {
                        cells,
                        group_meta: b.group_meta.as_ref().and_then(|gm| gm.get(r).copied()),
                    });
                }
            }
        }
    }
    TableVal { cols: schema, rows }
}

/// Build columnar [`Batch`]es from a flat slice of [`TableRow`]s and schema.
#[must_use]
pub fn rows_to_batches(schema: &[ColSpec], rows: &[TableRow], batch_size: usize) -> Vec<Batch> {
    let tv = TableVal {
        cols: schema.to_vec(),
        rows: rows.to_vec(),
    };
    table_to_batches(&tv, batch_size)
}
