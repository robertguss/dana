//! Runtime values, structural equality, IEEE-754 total ordering, canonical sorting/dedup,
//! and safe-by-default `[REDACTED:tag]` diagnostic formatting.
//!
//! Mirrors `formal/DanaCore/Eval.lean` §1–§3 byte-for-byte.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::core::bigint::{BigInt, DEC_SCALE};
use crate::core::check::{ArcTyEnv, TyEnv};
use crate::core::syntax::{
    BugKind, ChartKind, ColSpec, Expr, Float64, Ident, LTy, ScalarTy, TagSet,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum CapHandle {
    #[default]
    Real,
    Fake(usize),
}

/// Hidden group cardinality metadata tracked across `Summarize -> SuppressSmallGroups`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct GroupMeta {
    pub row_count: usize,
    pub distinct_count: Option<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ProfileColSummary {
    pub col_name: Ident,
    pub ty_name: String,
    pub row_count: usize,
    pub null_count: usize,
    pub distinct_count: usize,
    pub min_display: Option<String>,
    pub max_display: Option<String>,
    /// Percentage of null cells in `[0.0, 100.0]` (Phase 4B rich metadata; `0.0` in Core IR).
    pub null_pct: Float64,
    /// Public numeric summary statistics (`None` when redacted or non-numeric).
    pub mean: Option<Float64>,
    pub stddev: Option<Float64>,
    pub min: Option<Float64>,
    pub p25: Option<Float64>,
    pub median: Option<Float64>,
    pub p75: Option<Float64>,
    pub max: Option<Float64>,
    /// 8-bin Unicode sparkline (`▁▂▃▄▅▆▇█`) for public numeric columns (`None` when redacted).
    pub sparkline: Option<String>,
    /// Top-3 categorical values `(display, count)` for public columns (empty when redacted).
    pub top_values: Vec<(String, usize)>,
    /// Sorted sensitivity tags when this column was redacted (empty for public columns).
    pub redacted_tags: Vec<String>,
}

impl ProfileColSummary {
    /// Returns `true` when value-derived statistics for this column were redacted.
    #[must_use]
    pub fn is_redacted(&self) -> bool {
        !self.redacted_tags.is_empty()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ProfileVal {
    pub cols: Vec<ProfileColSummary>,
}

#[derive(Clone, Debug, Default)]
pub struct TableRow {
    pub cells: Vec<Val>,
    pub group_meta: Option<GroupMeta>,
}

#[derive(Clone, Debug, Default)]
pub struct TableVal {
    pub cols: Vec<ColSpec>,
    pub rows: Vec<TableRow>,
}

#[derive(Clone, Debug, Default)]
pub struct ChartVal {
    pub kind: ChartKind,
    pub title: String,
    pub col_names: Vec<Ident>,
    pub series: Vec<Vec<Val>>,
    /// Explicit column role mappings (Phase 4B rich metadata; `None` in Core IR).
    pub x_col: Option<Ident>,
    pub y_col: Option<Ident>,
    pub color_col: Option<Ident>,
    pub value_col: Option<Ident>,
    /// Explicit histogram bin count (Sturges default when `None`).
    pub bins: Option<usize>,
    /// Optional OLS linear trendline overlay `(slope, intercept, r_squared)`.
    pub trendline: Option<(f64, f64, f64)>,
}

#[derive(Clone, Debug, Default)]
pub struct ReportVal {
    pub title: String,
    pub summaries: Vec<String>,
    pub charts: Vec<ChartVal>,
    pub tables: Vec<(Vec<Ident>, Vec<Vec<Val>>)>,
}

#[derive(Clone, Debug)]
pub struct EnvEntry {
    pub name: Ident,
    pub lty: LTy,
    pub val: Val,
}

pub type Env = Vec<EnvEntry>;

#[derive(Clone, Debug)]
struct EnvNode {
    entry: EnvEntry,
    next: Option<Arc<EnvNode>>,
}

/// Persistent `Arc`-backed singly-linked runtime environment giving O(1) extension on `LetE`,
/// O(1) lexical capture on `Expr::Lam` (eliminating exponential $O(2^n)$ closure-chain cloning),
/// and O(1) type-environment projection while remaining `Send + Sync` with iterative `Drop`.
#[derive(Clone, Debug, Default)]
pub struct EnvList {
    head: Option<Arc<EnvNode>>,
    ty_env: ArcTyEnv,
}

impl EnvList {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            head: None,
            ty_env: ArcTyEnv::empty(),
        }
    }

    #[must_use]
    pub fn from_slice(entries: &[EnvEntry]) -> Self {
        let mut cur = Self::empty();
        for e in entries.iter().rev() {
            cur = Self::cons(e.clone(), cur);
        }
        cur
    }

    #[must_use]
    pub fn from_vec(entries: Vec<EnvEntry>) -> Self {
        let mut cur = Self::empty();
        for e in entries.into_iter().rev() {
            cur = Self::cons(e, cur);
        }
        cur
    }

    #[must_use]
    pub fn cons(entry: EnvEntry, mut tail: Self) -> Self {
        let ty_env = ArcTyEnv::cons(
            entry.name.clone(),
            entry.lty.clone(),
            std::mem::take(&mut tail.ty_env),
        );
        let head = Some(Arc::new(EnvNode {
            entry,
            next: tail.head.take(),
        }));
        Self { head, ty_env }
    }

    #[must_use]
    pub fn prepend_entries(&self, entries: Vec<EnvEntry>) -> Self {
        let mut cur = self.clone();
        for e in entries.into_iter().rev() {
            cur = Self::cons(e, cur);
        }
        cur
    }

    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<(&LTy, &Val)> {
        let mut cur = self.head.as_deref();
        while let Some(node) = cur {
            if node.entry.name == name {
                return Some((&node.entry.lty, &node.entry.val));
            }
            cur = node.next.as_deref();
        }
        None
    }

    #[must_use]
    pub(crate) const fn as_arc_ty_env(&self) -> &ArcTyEnv {
        &self.ty_env
    }

    #[must_use]
    pub fn to_ty_env(&self) -> TyEnv {
        let mut out = Vec::new();
        let mut cur = self.head.as_deref();
        while let Some(node) = cur {
            out.push((node.entry.name.clone(), node.entry.lty.clone()));
            cur = node.next.as_deref();
        }
        out
    }

    #[must_use]
    pub fn to_vec(&self) -> Env {
        let mut out = Vec::new();
        let mut cur = self.head.as_deref();
        while let Some(node) = cur {
            out.push(node.entry.clone());
            cur = node.next.as_deref();
        }
        out
    }

    fn drain_unique_into(&mut self, stack: &mut Vec<Val>) {
        self.ty_env = ArcTyEnv::empty();
        let mut cur = self.head.take();
        while let Some(arc) = cur {
            match Arc::try_unwrap(arc) {
                Ok(mut node) => {
                    cur = node.next.take();
                    if is_recursive_val(&node.entry.val) {
                        stack.push(node.entry.val);
                    }
                }
                Err(_) => break,
            }
        }
    }
}

impl Drop for EnvList {
    fn drop(&mut self) {
        self.ty_env = ArcTyEnv::empty();
        if self.head.is_none() {
            return;
        }
        let mut stack = Vec::new();
        self.drain_unique_into(&mut stack);
        while let Some(mut node) = stack.pop() {
            push_val_children(&mut node, &mut stack);
        }
    }
}

#[derive(Clone, Debug)]
pub struct ClosureVal {
    pub params: Vec<(Ident, LTy)>,
    pub fn_pc: TagSet,
    pub ret_lty: LTy,
    pub body: Arc<Expr>,
    pub captured_env: EnvList,
}

#[derive(Clone, Debug, Default)]
pub enum Val {
    #[default]
    Unit,
    Bool(bool),
    Int(BigInt),
    Decimal(BigInt),
    Float(Float64),
    Text(String),
    Bytes(Vec<u8>),
    Date(BigInt),
    Timestamp(BigInt),
    Duration(BigInt),
    OptNone,
    OptSome(Box<Val>),
    ResOk(Box<Val>),
    ResErr(Box<Val>),
    Tuple(Vec<Val>),
    List(Vec<Val>),
    Map(Vec<(Val, Val)>),
    Ctor {
        type_name: Ident,
        ctor_name: Ident,
        fields: Vec<Val>,
    },
    Table(TableVal),
    DynTable {
        headers: Vec<String>,
        rows: Vec<Vec<Val>>,
    },
    Chart(Box<ChartVal>),
    Report(Box<ReportVal>),
    Profile(ProfileVal),
    LinearModel {
        slope: Float64,
        intercept: Float64,
        r2: Float64,
    },
    StatTest {
        stat: Float64,
        p_value: Float64,
    },
    Closure(Box<ClosureVal>),
    // First-class capability values
    CapArgs,
    CapClock,
    CapConsole {
        handle: CapHandle,
        allows: TagSet,
    },
    CapReadFiles(CapHandle),
    CapWriteFiles {
        handle: CapHandle,
        root: String,
        allows: TagSet,
    },
    CapReadDB {
        handle: CapHandle,
        db: Ident,
    },
    CapWriteTable {
        handle: CapHandle,
        db: Ident,
        table_name: Ident,
    },
    CapRawReadDB(Ident),
    CapHttpsAllow {
        handle: CapHandle,
        host: String,
        allows: TagSet,
    },
    CapSecret {
        handle: CapHandle,
        name: String,
    },
    CapDeclassify(TagSet),
}

impl Val {
    #[must_use]
    pub fn into_table(mut self) -> Option<TableVal> {
        match &mut self {
            Self::Table(tv) => Some(std::mem::take(tv)),
            _ => None,
        }
    }
}

fn is_recursive_val(val: &Val) -> bool {
    matches!(
        val,
        Val::OptSome(_)
            | Val::ResOk(_)
            | Val::ResErr(_)
            | Val::Tuple(_)
            | Val::List(_)
            | Val::Map(_)
            | Val::Ctor { .. }
            | Val::Table(_)
            | Val::DynTable { .. }
            | Val::Chart(_)
            | Val::Report(_)
            | Val::Closure { .. }
    )
}

fn push_val_children(val: &mut Val, stack: &mut Vec<Val>) {
    match val {
        Val::OptSome(inner) | Val::ResOk(inner) | Val::ResErr(inner) => {
            if is_recursive_val(inner) {
                stack.push(std::mem::replace(inner.as_mut(), Val::Unit));
            }
        }
        Val::Tuple(xs) | Val::List(xs) | Val::Ctor { fields: xs, .. } => {
            for x in std::mem::take(xs) {
                if is_recursive_val(&x) {
                    stack.push(x);
                }
            }
        }
        Val::Map(pairs) => {
            for (k, v) in std::mem::take(pairs) {
                if is_recursive_val(&k) {
                    stack.push(k);
                }
                if is_recursive_val(&v) {
                    stack.push(v);
                }
            }
        }
        Val::Table(tv) => {
            for row in std::mem::take(&mut tv.rows) {
                for cell in row.cells {
                    if is_recursive_val(&cell) {
                        stack.push(cell);
                    }
                }
            }
        }
        Val::DynTable { rows, .. } => {
            for row in std::mem::take(rows) {
                for cell in row {
                    if is_recursive_val(&cell) {
                        stack.push(cell);
                    }
                }
            }
        }
        Val::Chart(cv) => {
            for series in std::mem::take(&mut cv.series) {
                for v in series {
                    if is_recursive_val(&v) {
                        stack.push(v);
                    }
                }
            }
        }
        Val::Report(rv) => {
            for ch in std::mem::take(&mut rv.charts) {
                for series in ch.series {
                    for v in series {
                        if is_recursive_val(&v) {
                            stack.push(v);
                        }
                    }
                }
            }
            for (_, rows) in std::mem::take(&mut rv.tables) {
                for row in rows {
                    for v in row {
                        if is_recursive_val(&v) {
                            stack.push(v);
                        }
                    }
                }
            }
        }
        Val::Closure(cl) => {
            cl.captured_env.drain_unique_into(stack);
        }
        _ => {}
    }
}

impl Drop for Val {
    fn drop(&mut self) {
        if !is_recursive_val(self) {
            return;
        }
        let mut stack = Vec::new();
        push_val_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            push_val_children(&mut node, &mut stack);
        }
    }
}

#[must_use]
pub fn lookup_env<'a>(env: &'a [EnvEntry], name: &str) -> Option<(&'a LTy, &'a Val)> {
    env.iter()
        .find(|e| e.name == name)
        .map(|e| (&e.lty, &e.val))
}

#[must_use]
pub fn env_to_ty_env(env: &[EnvEntry]) -> TyEnv {
    env.iter()
        .map(|e| (e.name.clone(), e.lty.clone()))
        .collect()
}

// ---------------------------------------------------------------------------
// IEEE-754 Total Ordering, Conversions & Structural Equality
// ---------------------------------------------------------------------------

/// IEEE-754 totalOrder key mapping binary64 bits to `[0, 2^64)` injectively.
#[must_use]
pub const fn float_order_key(f: Float64) -> u64 {
    const SIGN_BIT: u64 = 1u64 << 63;
    if f.bits >= SIGN_BIT {
        u64::MAX - f.bits
    } else {
        f.bits + SIGN_BIT
    }
}

#[must_use]
pub fn val_to_float(v: &Val) -> Option<f64> {
    match v {
        Val::Float(f) => Some(f.to_f64()),
        Val::Int(n) => Some(n.to_f64()),
        Val::Decimal(d) => Some(d.to_f64() / (DEC_SCALE as f64)),
        _ => None,
    }
}

#[must_use]
pub fn unwrap_numeric_float(v: &Val) -> Option<f64> {
    match v {
        Val::OptNone => None,
        Val::OptSome(inner) => val_to_float(inner),
        other => val_to_float(other),
    }
}

fn val_rank(v: &Val) -> u8 {
    match v {
        Val::OptNone => 0,
        Val::Unit => 1,
        Val::Bool(_) => 2,
        Val::Int(_) => 3,
        Val::Decimal(_) => 4,
        Val::Float(_) => 5,
        Val::Text(_) => 6,
        Val::Bytes(_) => 7,
        Val::Date(_) => 8,
        Val::Timestamp(_) => 9,
        Val::Duration(_) => 10,
        Val::OptSome(_) => 11,
        Val::ResOk(_) => 12,
        Val::ResErr(_) => 13,
        Val::Tuple(_) => 14,
        Val::List(_) => 15,
        Val::Map(_) => 16,
        Val::Ctor { .. } => 17,
        Val::Table(_) => 18,
        Val::DynTable { .. } => 19,
        Val::Chart(_) => 20,
        Val::Report(_) => 21,
        Val::Profile(_) => 22,
        Val::LinearModel { .. } => 23,
        Val::StatTest { .. } => 24,
        Val::Closure { .. }
        | Val::CapArgs
        | Val::CapClock
        | Val::CapConsole { .. }
        | Val::CapReadFiles(_)
        | Val::CapWriteFiles { .. }
        | Val::CapReadDB { .. }
        | Val::CapWriteTable { .. }
        | Val::CapRawReadDB(_)
        | Val::CapHttpsAllow { .. }
        | Val::CapSecret { .. }
        | Val::CapDeclassify(_) => 25,
    }
}

/// Structural equality on observable runtime data values (mirrors `Eval.lean:valEq`).
#[must_use]
pub fn val_eq(v1: &Val, v2: &Val) -> bool {
    let mut stack = vec![(v1, v2)];
    while let Some((a, b)) = stack.pop() {
        match (a, b) {
            (Val::Unit, Val::Unit) | (Val::OptNone, Val::OptNone) => {}
            (Val::Bool(x), Val::Bool(y)) => {
                if x != y {
                    return false;
                }
            }
            (Val::Int(x), Val::Int(y))
            | (Val::Decimal(x), Val::Decimal(y))
            | (Val::Date(x), Val::Date(y))
            | (Val::Timestamp(x), Val::Timestamp(y))
            | (Val::Duration(x), Val::Duration(y)) => {
                if x != y {
                    return false;
                }
            }
            (Val::Float(x), Val::Float(y)) => {
                if x != y {
                    return false;
                }
            }
            (Val::Text(x), Val::Text(y)) => {
                if x != y {
                    return false;
                }
            }
            (Val::Bytes(x), Val::Bytes(y)) => {
                if x != y {
                    return false;
                }
            }
            (Val::OptSome(x), Val::OptSome(y))
            | (Val::ResOk(x), Val::ResOk(y))
            | (Val::ResErr(x), Val::ResErr(y)) => stack.push((x, y)),
            (Val::Tuple(xs), Val::Tuple(ys)) | (Val::List(xs), Val::List(ys)) => {
                if xs.len() != ys.len() {
                    return false;
                }
                for (x, y) in xs.iter().zip(ys) {
                    stack.push((x, y));
                }
            }
            (Val::Map(xs), Val::Map(ys)) => {
                if xs.len() != ys.len() {
                    return false;
                }
                for ((k1, x1), (k2, x2)) in xs.iter().zip(ys) {
                    stack.push((x1, x2));
                    stack.push((k1, k2));
                }
            }
            (
                Val::Ctor {
                    type_name: tn1,
                    ctor_name: cn1,
                    fields: fs1,
                },
                Val::Ctor {
                    type_name: tn2,
                    ctor_name: cn2,
                    fields: fs2,
                },
            ) => {
                if tn1 != tn2 || cn1 != cn2 || fs1.len() != fs2.len() {
                    return false;
                }
                for (f1, f2) in fs1.iter().zip(fs2) {
                    stack.push((f1, f2));
                }
            }
            (Val::Table(t1), Val::Table(t2)) => {
                if t1.cols.len() != t2.cols.len()
                    || !t1
                        .cols
                        .iter()
                        .zip(&t2.cols)
                        .all(|(c1, c2)| c1.name == c2.name)
                    || t1.rows.len() != t2.rows.len()
                {
                    return false;
                }
                for (r1, r2) in t1.rows.iter().zip(&t2.rows) {
                    if r1.cells.len() != r2.cells.len() {
                        return false;
                    }
                    for (c1, c2) in r1.cells.iter().zip(&r2.cells) {
                        stack.push((c1, c2));
                    }
                }
            }
            (
                Val::DynTable {
                    headers: h1,
                    rows: r1,
                },
                Val::DynTable {
                    headers: h2,
                    rows: r2,
                },
            ) => {
                if h1 != h2 || r1.len() != r2.len() {
                    return false;
                }
                for (row1, row2) in r1.iter().zip(r2) {
                    if row1.len() != row2.len() {
                        return false;
                    }
                    for (c1, c2) in row1.iter().zip(row2) {
                        stack.push((c1, c2));
                    }
                }
            }
            (
                Val::LinearModel {
                    slope: s1,
                    intercept: i1,
                    r2: r1,
                },
                Val::LinearModel {
                    slope: s2,
                    intercept: i2,
                    r2: r2_b,
                },
            ) => {
                if s1 != s2 || i1 != i2 || r1 != r2_b {
                    return false;
                }
            }
            (
                Val::StatTest {
                    stat: s1,
                    p_value: p1,
                },
                Val::StatTest {
                    stat: s2,
                    p_value: p2,
                },
            ) => {
                if s1 != s2 || p1 != p2 {
                    return false;
                }
            }
            (Val::Profile(p1), Val::Profile(p2)) => {
                if p1 != p2 {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

#[must_use]
pub fn val_list_eq(xs: &[Val], ys: &[Val]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(a, b)| val_eq(a, b))
}

/// Three-way structural comparator on runtime values (mirrors `Eval.lean:valCmp`).
#[must_use]
pub fn val_cmp(v1: &Val, v2: &Val) -> Ordering {
    enum CmpWork<'a> {
        Val(&'a Val, &'a Val),
        Len(usize, usize),
    }
    let mut stack = vec![CmpWork::Val(v1, v2)];
    while let Some(item) = stack.pop() {
        let ord = match item {
            CmpWork::Len(l1, l2) => l1.cmp(&l2),
            CmpWork::Val(a, b) => match (a, b) {
                (Val::OptNone, Val::OptNone) | (Val::Unit, Val::Unit) => Ordering::Equal,
                (Val::Bool(x), Val::Bool(y)) => x.cmp(y),
                (Val::Int(x), Val::Int(y))
                | (Val::Decimal(x), Val::Decimal(y))
                | (Val::Date(x), Val::Date(y))
                | (Val::Timestamp(x), Val::Timestamp(y))
                | (Val::Duration(x), Val::Duration(y)) => x.cmp(y),
                (Val::Float(x), Val::Float(y)) => float_order_key(*x).cmp(&float_order_key(*y)),
                (Val::Text(x), Val::Text(y)) => x.cmp(y),
                (Val::Bytes(x), Val::Bytes(y)) => x.cmp(y),
                (Val::OptSome(x), Val::OptSome(y))
                | (Val::ResOk(x), Val::ResOk(y))
                | (Val::ResErr(x), Val::ResErr(y)) => {
                    stack.push(CmpWork::Val(x, y));
                    Ordering::Equal
                }
                (Val::Tuple(xs), Val::Tuple(ys)) | (Val::List(xs), Val::List(ys)) => {
                    stack.push(CmpWork::Len(xs.len(), ys.len()));
                    for (x, y) in xs.iter().zip(ys).rev() {
                        stack.push(CmpWork::Val(x, y));
                    }
                    Ordering::Equal
                }
                (Val::Map(xs), Val::Map(ys)) => {
                    stack.push(CmpWork::Len(xs.len(), ys.len()));
                    for ((k1, x1), (k2, x2)) in xs.iter().zip(ys).rev() {
                        stack.push(CmpWork::Val(x1, x2));
                        stack.push(CmpWork::Val(k1, k2));
                    }
                    Ordering::Equal
                }
                (
                    Val::Ctor {
                        type_name: tn1,
                        ctor_name: cn1,
                        fields: fs1,
                    },
                    Val::Ctor {
                        type_name: tn2,
                        ctor_name: cn2,
                        fields: fs2,
                    },
                ) => {
                    let head = tn1.cmp(tn2).then_with(|| cn1.cmp(cn2));
                    if head == Ordering::Equal {
                        stack.push(CmpWork::Len(fs1.len(), fs2.len()));
                        for (f1, f2) in fs1.iter().zip(fs2).rev() {
                            stack.push(CmpWork::Val(f1, f2));
                        }
                    }
                    head
                }
                (Val::Profile(p1), Val::Profile(p2)) => {
                    repr_profile_val(p1).cmp(&repr_profile_val(p2))
                }
                (
                    Val::LinearModel {
                        slope: s1,
                        intercept: i1,
                        r2: r1,
                    },
                    Val::LinearModel {
                        slope: s2,
                        intercept: i2,
                        r2: r2_b,
                    },
                ) => float_order_key(*s1)
                    .cmp(&float_order_key(*s2))
                    .then_with(|| float_order_key(*i1).cmp(&float_order_key(*i2)))
                    .then_with(|| float_order_key(*r1).cmp(&float_order_key(*r2_b))),
                (
                    Val::StatTest {
                        stat: s1,
                        p_value: p1,
                    },
                    Val::StatTest {
                        stat: s2,
                        p_value: p2,
                    },
                ) => float_order_key(*s1)
                    .cmp(&float_order_key(*s2))
                    .then_with(|| float_order_key(*p1).cmp(&float_order_key(*p2))),
                (x, y) => val_rank(x).cmp(&val_rank(y)),
            },
        };
        if ord != Ordering::Equal {
            return ord;
        }
    }
    Ordering::Equal
}

#[must_use]
pub fn val_list_cmp(xs: &[Val], ys: &[Val]) -> Ordering {
    for (a, b) in xs.iter().zip(ys) {
        match val_cmp(a, b) {
            Ordering::Equal => {}
            ord => return ord,
        }
    }
    xs.len().cmp(&ys.len())
}

#[must_use]
pub fn val_lt(a: &Val, b: &Val) -> bool {
    val_cmp(a, b) == Ordering::Less
}

#[must_use]
pub fn val_list_lt(xs: &[Val], ys: &[Val]) -> bool {
    val_list_cmp(xs, ys) == Ordering::Less
}

// ---------------------------------------------------------------------------
// Canonical Insertion Sort & Deduplication Helpers
// ---------------------------------------------------------------------------

/// Stable right-to-left insertion sort matching `Eval.lean:insertionSortBy` verbatim.
#[must_use]
pub fn insertion_sort_by<T: Clone>(items: &[T], lt: impl Fn(&T, &T) -> bool) -> Vec<T> {
    let mut out: Vec<T> = Vec::with_capacity(items.len());
    for x in items.iter().rev() {
        let mut pos = 0;
        while pos < out.len() && lt(&out[pos], x) {
            pos += 1;
        }
        out.insert(pos, x.clone());
    }
    out
}

/// Deduplicate an already sorted slice by dropping earlier adjacent duplicates
/// (matching `Eval.lean:dedupAdjacentBy`).
#[must_use]
pub fn dedup_adjacent_by<T: Clone>(items: &[T], eq: impl Fn(&T, &T) -> bool) -> Vec<T> {
    let mut out = Vec::with_capacity(items.len());
    for i in 0..items.len() {
        if i + 1 < items.len() && eq(&items[i], &items[i + 1]) {
            continue;
        }
        out.push(items[i].clone());
    }
    out
}

// ---------------------------------------------------------------------------
// Lean `reprStr` Compatibility & Safe-by-Default Runtime Redaction
// ---------------------------------------------------------------------------

#[must_use]
pub fn repr_bug_kind(kind: BugKind) -> &'static str {
    match kind {
        BugKind::IntOverflow => "DanaCore.BugKind.intOverflow",
        BugKind::DecimalOverflow => "DanaCore.BugKind.decimalOverflow",
        BugKind::DivByZero => "DanaCore.BugKind.divByZero",
        BugKind::UnwrapNone => "DanaCore.BugKind.unwrapNone",
        BugKind::JoinCardinality => "DanaCore.BugKind.joinCardinality",
        BugKind::PromiseViolation => "DanaCore.BugKind.promiseViolation",
        BugKind::SchemaConstraint => "DanaCore.BugKind.schemaConstraint",
        BugKind::ExportGateDenied => "DanaCore.BugKind.exportGateDenied",
        BugKind::OutsideBoundary => "DanaCore.BugKind.outsideBoundary",
        BugKind::UserStop => "DanaCore.BugKind.userStop",
    }
}

fn lean_quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || (c as u32) == 0x7F => {
                use std::fmt::Write as _;
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[must_use]
pub fn repr_scalar_ty(ty: &ScalarTy) -> String {
    let mut depth = 0usize;
    let mut cur = ty;
    while let ScalarTy::Option(inner) = cur {
        depth += 1;
        cur = inner;
    }
    let leaf = match cur {
        ScalarTy::Unit => "DanaCore.ScalarTy.unit".to_string(),
        ScalarTy::Bool => "DanaCore.ScalarTy.bool".to_string(),
        ScalarTy::Int => "DanaCore.ScalarTy.int".to_string(),
        ScalarTy::Decimal => "DanaCore.ScalarTy.decimal".to_string(),
        ScalarTy::Float => "DanaCore.ScalarTy.float".to_string(),
        ScalarTy::Text => "DanaCore.ScalarTy.text".to_string(),
        ScalarTy::Bytes => "DanaCore.ScalarTy.bytes".to_string(),
        ScalarTy::Date => "DanaCore.ScalarTy.date".to_string(),
        ScalarTy::Timestamp => "DanaCore.ScalarTy.timestamp".to_string(),
        ScalarTy::Duration => "DanaCore.ScalarTy.duration".to_string(),
        ScalarTy::Data(name) => format!("DanaCore.ScalarTy.data {}", lean_quote_string(name)),
        ScalarTy::Option(_) => unreachable!("peeled above"),
    };
    if depth == 0 {
        return leaf;
    }
    let mut out = String::with_capacity(depth * 27 + leaf.len());
    for _ in 0..depth {
        out.push_str("DanaCore.ScalarTy.option (");
    }
    out.push_str(&leaf);
    for _ in 0..depth {
        out.push(')');
    }
    out
}

#[must_use]
pub fn repr_profile_val(p: &ProfileVal) -> String {
    if p.cols.is_empty() {
        return "{ cols := [] }".to_string();
    }
    let items: Vec<String> = p
        .cols
        .iter()
        .map(|c| {
            let min_s = match &c.min_display {
                None => "none".to_string(),
                Some(s) => format!("some {}", lean_quote_string(s)),
            };
            let max_s = match &c.max_display {
                None => "none".to_string(),
                Some(s) => format!("some {}", lean_quote_string(s)),
            };
            format!(
                "{{ colName := {}, tyName := {}, rowCount := {}, nullCount := {}, distinctCount := {}, minDisplay := {}, maxDisplay := {} }}",
                lean_quote_string(&c.col_name),
                lean_quote_string(&c.ty_name),
                c.row_count,
                c.null_count,
                c.distinct_count,
                min_s,
                max_s,
            )
        })
        .collect();
    format!("{{ cols := [{}] }}", items.join(", "))
}

/// Canonical redaction marker for non-empty sensitivity tag sets (`[REDACTED:tag]`).
#[must_use]
pub fn redact_tags(ts: &TagSet) -> String {
    format!("[REDACTED:{}]", ts.elems().join(","))
}

#[must_use]
pub fn render_decimal(scaled: &BigInt) -> String {
    let sign = if scaled.is_negative() { "-" } else { "" };
    let abs_val = scaled.abs();
    let scale = BigInt::from(DEC_SCALE);
    let (whole, frac) = match abs_val.div_rem_euclid(&scale) {
        Some(pair) => pair,
        None => (BigInt::ZERO, BigInt::ZERO),
    };
    if frac.is_zero() {
        format!("{sign}{whole}.0")
    } else {
        let frac_str = frac.to_string();
        let pad_len = 18usize.saturating_sub(frac_str.len());
        let mut padded = String::with_capacity(18);
        for _ in 0..pad_len {
            padded.push('0');
        }
        padded.push_str(&frac_str);
        let trimmed = padded.trim_end_matches('0');
        format!("{sign}{whole}.{trimmed}")
    }
}

/// Format a runtime value when public (`[]`), matching `Eval.lean:renderPublicVal`.
#[must_use]
pub fn render_public_val(val: &Val) -> String {
    use std::fmt::Write as _;
    enum Task<'a> {
        Val(&'a Val),
        Lit(&'a str),
    }
    let mut out = String::new();
    let mut stack = vec![Task::Val(val)];
    while let Some(task) = stack.pop() {
        match task {
            Task::Lit(s) => out.push_str(s),
            Task::Val(cur) => match cur {
                Val::Unit => out.push_str("Unit"),
                Val::Bool(true) => out.push_str("true"),
                Val::Bool(false) => out.push_str("false"),
                Val::Int(n) => {
                    let _ = write!(out, "{n}");
                }
                Val::Decimal(d) => out.push_str(&render_decimal(d)),
                Val::Float(f) => {
                    let _ = write!(out, "float64({})", f.bits);
                }
                Val::Text(s) => out.push_str(s),
                Val::Bytes(bs) => {
                    let _ = write!(out, "bytes({})", bs.len());
                }
                Val::Date(d) => {
                    let _ = write!(out, "date({d})");
                }
                Val::Timestamp(ts) => {
                    let _ = write!(out, "timestamp({ts})");
                }
                Val::Duration(dur) => {
                    let _ = write!(out, "duration({dur})");
                }
                Val::OptNone => out.push_str("none"),
                Val::OptSome(v) => {
                    out.push_str("some(");
                    stack.push(Task::Lit(")"));
                    stack.push(Task::Val(v));
                }
                Val::ResOk(v) => {
                    out.push_str("Ok(");
                    stack.push(Task::Lit(")"));
                    stack.push(Task::Val(v));
                }
                Val::ResErr(e) => {
                    out.push_str("Error(");
                    stack.push(Task::Lit(")"));
                    stack.push(Task::Val(e));
                }
                Val::Tuple(vs) => {
                    out.push('(');
                    stack.push(Task::Lit(")"));
                    for (i, v) in vs.iter().enumerate().rev() {
                        stack.push(Task::Val(v));
                        if i > 0 {
                            stack.push(Task::Lit(", "));
                        }
                    }
                }
                Val::List(vs) => {
                    out.push('[');
                    stack.push(Task::Lit("]"));
                    for (i, v) in vs.iter().enumerate().rev() {
                        stack.push(Task::Val(v));
                        if i > 0 {
                            stack.push(Task::Lit(", "));
                        }
                    }
                }
                Val::Ctor {
                    ctor_name, fields, ..
                } => {
                    out.push_str(ctor_name);
                    if !fields.is_empty() {
                        out.push('(');
                        stack.push(Task::Lit(")"));
                        for (i, v) in fields.iter().enumerate().rev() {
                            stack.push(Task::Val(v));
                            if i > 0 {
                                stack.push(Task::Lit(", "));
                            }
                        }
                    }
                }
                Val::Table(tv) => {
                    let _ = write!(out, "Table(rows={})", tv.rows.len());
                }
                Val::DynTable { headers, rows } => {
                    let _ = write!(
                        out,
                        "DynamicTable(cols={}, rows={})",
                        headers.len(),
                        rows.len()
                    );
                }
                Val::Map(_)
                | Val::Chart(_)
                | Val::Report(_)
                | Val::Profile(_)
                | Val::LinearModel { .. }
                | Val::StatTest { .. }
                | Val::Closure { .. }
                | Val::CapArgs
                | Val::CapClock
                | Val::CapConsole { .. }
                | Val::CapReadFiles(_)
                | Val::CapWriteFiles { .. }
                | Val::CapReadDB { .. }
                | Val::CapWriteTable { .. }
                | Val::CapRawReadDB(_)
                | Val::CapHttpsAllow { .. }
                | Val::CapSecret { .. }
                | Val::CapDeclassify(_) => out.push_str("<value>"),
            },
        }
    }
    out
}

/// Privacy-preserving diagnostic formatter: NEVER inspects `v` whenever `ts` is non-empty!
#[must_use]
pub fn format_diag_detail(ts: &TagSet, v: &Val) -> String {
    if ts.is_empty() {
        render_public_val(v)
    } else {
        redact_tags(ts)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Bug {
    pub kind: BugKind,
    pub message: String,
}
