//! Dana Core IR v0.1 AST, canonical `TagSet` semilattice, schemas, types,
//! expressions, pure relational plans, policies, metadata, and programs.
//!
//! Mirrors `formal/DanaCore/Syntax.lean` 1-to-1.

use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

use crate::core::bigint::BigInt;

pub type Ident = String;
pub type Tag = String;

/// Built-in sensitivity tags available in every Dana program without declaration.
pub const BUILT_IN_TAGS: &[&str] = &["pii", "ferpa", "financial", "health", "secret"];

/// Canonical bounded join-semilattice of sensitivity tags `(Set(Tag), ∅, ∪, ⊆)`
/// represented as a strictly sorted, duplicate-free `Vec<Tag>` ordered by Unicode scalar value
/// (UTF-8 lexicographic order equals Unicode scalar order).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TagSet {
    elems: Vec<Tag>,
}

impl TagSet {
    #[must_use]
    pub const fn empty() -> Self {
        Self { elems: Vec::new() }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }

    #[must_use]
    pub fn elems(&self) -> &[Tag] {
        &self.elems
    }

    #[must_use]
    pub fn contains(&self, t: &str) -> bool {
        self.elems.binary_search_by(|x| x.as_str().cmp(t)).is_ok()
    }

    #[must_use]
    pub fn insert(&self, t: impl Into<Tag>) -> Self {
        let t = t.into();
        let mut elems = self.elems.clone();
        if let Err(pos) = elems.binary_search(&t) {
            elems.insert(pos, t);
        }
        Self { elems }
    }

    #[must_use]
    pub fn singleton(t: impl Into<Tag>) -> Self {
        Self {
            elems: vec![t.into()],
        }
    }

    #[must_use]
    pub fn of_list(mut ts: Vec<Tag>) -> Self {
        ts.sort();
        ts.dedup();
        Self { elems: ts }
    }

    /// Construct only if `ts` is already strictly sorted and duplicate-free.
    #[must_use]
    pub fn from_canonical_elems(ts: Vec<Tag>) -> Option<Self> {
        if ts.windows(2).all(|w| w[0] < w[1]) {
            Some(Self { elems: ts })
        } else {
            None
        }
    }

    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        if self.elems.is_empty() {
            return other.clone();
        }
        if other.elems.is_empty() {
            return self.clone();
        }
        let mut out = Vec::with_capacity(self.elems.len() + other.elems.len());
        let (mut i, mut j) = (0, 0);
        while i < self.elems.len() && j < other.elems.len() {
            match self.elems[i].cmp(&other.elems[j]) {
                std::cmp::Ordering::Less => {
                    out.push(self.elems[i].clone());
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(other.elems[j].clone());
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    out.push(self.elems[i].clone());
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.elems[i..]);
        out.extend_from_slice(&other.elems[j..]);
        Self { elems: out }
    }

    #[must_use]
    pub fn remove(&self, t: &str) -> Self {
        Self {
            elems: self
                .elems
                .iter()
                .filter(|x| x.as_str() != t)
                .cloned()
                .collect(),
        }
    }

    #[must_use]
    pub fn diff(&self, other: &Self) -> Self {
        Self {
            elems: self
                .elems
                .iter()
                .filter(|x| !other.contains(x))
                .cloned()
                .collect(),
        }
    }

    #[must_use]
    pub fn inter(&self, other: &Self) -> Self {
        Self {
            elems: self
                .elems
                .iter()
                .filter(|x| other.contains(x))
                .cloned()
                .collect(),
        }
    }

    #[must_use]
    pub fn is_subset(&self, other: &Self) -> bool {
        self.elems.iter().all(|x| other.contains(x))
    }

    #[must_use]
    pub fn union_list<'a>(sets: impl IntoIterator<Item = &'a Self>) -> Self {
        let mut acc = Self::empty();
        for s in sets {
            acc = acc.union(s);
        }
        acc
    }

    #[must_use]
    pub fn union_owned(sets: impl IntoIterator<Item = Self>) -> Self {
        let mut acc = Self::empty();
        for s in sets {
            acc = acc.union(&s);
        }
        acc
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum AggKind {
    #[default]
    Raw,
    GroupKey,
    Blending,
    NonBlending,
}

/// Monomorphic scalar / cell types permitted inside `Table` columns.
#[derive(Debug, Default, Eq)]
pub enum ScalarTy {
    #[default]
    Unit,
    Bool,
    Int,
    Decimal,
    Float,
    Text,
    Bytes,
    Date,
    Timestamp,
    Duration,
    Data(Ident),
    Option(Box<ScalarTy>),
}

impl Clone for ScalarTy {
    fn clone(&self) -> Self {
        let mut depth = 0usize;
        let mut cur = self;
        while let Self::Option(inner) = cur {
            depth += 1;
            cur = inner;
        }
        let mut out = match cur {
            Self::Unit => Self::Unit,
            Self::Bool => Self::Bool,
            Self::Int => Self::Int,
            Self::Decimal => Self::Decimal,
            Self::Float => Self::Float,
            Self::Text => Self::Text,
            Self::Bytes => Self::Bytes,
            Self::Date => Self::Date,
            Self::Timestamp => Self::Timestamp,
            Self::Duration => Self::Duration,
            Self::Data(n) => Self::Data(n.clone()),
            Self::Option(_) => unreachable!("peeled above"),
        };
        for _ in 0..depth {
            out = Self::Option(Box::new(out));
        }
        out
    }
}

impl PartialEq for ScalarTy {
    fn eq(&self, other: &Self) -> bool {
        let mut a = self;
        let mut b = other;
        loop {
            match (a, b) {
                (Self::Unit, Self::Unit)
                | (Self::Bool, Self::Bool)
                | (Self::Int, Self::Int)
                | (Self::Decimal, Self::Decimal)
                | (Self::Float, Self::Float)
                | (Self::Text, Self::Text)
                | (Self::Bytes, Self::Bytes)
                | (Self::Date, Self::Date)
                | (Self::Timestamp, Self::Timestamp)
                | (Self::Duration, Self::Duration) => return true,
                (Self::Data(x), Self::Data(y)) => return x == y,
                (Self::Option(x), Self::Option(y)) => {
                    a = x;
                    b = y;
                }
                _ => return false,
            }
        }
    }
}

impl Hash for ScalarTy {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut cur = self;
        loop {
            std::mem::discriminant(cur).hash(state);
            match cur {
                Self::Data(n) => {
                    n.hash(state);
                    return;
                }
                Self::Option(inner) => cur = inner,
                _ => return,
            }
        }
    }
}

impl ScalarTy {
    #[must_use]
    pub fn is_option(&self) -> bool {
        matches!(self, Self::Option(_))
    }

    #[must_use]
    pub fn to_ty(&self) -> Ty {
        let mut depth = 0usize;
        let mut cur = self;
        while let Self::Option(inner) = cur {
            depth += 1;
            cur = inner;
        }
        let mut out = match cur {
            Self::Unit => Ty::Unit,
            Self::Bool => Ty::Bool,
            Self::Int => Ty::Int,
            Self::Decimal => Ty::Decimal,
            Self::Float => Ty::Float,
            Self::Text => Ty::Text,
            Self::Bytes => Ty::Bytes,
            Self::Date => Ty::Date,
            Self::Timestamp => Ty::Timestamp,
            Self::Duration => Ty::Duration,
            Self::Data(n) => Ty::Data(n.clone()),
            Self::Option(_) => unreachable!("peeled above"),
        };
        for _ in 0..depth {
            out = Ty::Option(Box::new(out));
        }
        out
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ColSpec {
    pub name: Ident,
    pub ty: ScalarTy,
    pub tags: TagSet,
    pub bucketed: bool,
    pub agg_kind: AggKind,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TableTy {
    pub cols: Vec<ColSpec>,
    pub row_tags: TagSet,
    pub order_tags: TagSet,
    pub grouped_by: Option<Vec<Ident>>,
    pub summarized: bool,
    pub distinct_by: Option<Ident>,
}

impl TableTy {
    #[must_use]
    pub fn find_col(&self, name: &str) -> Option<&ColSpec> {
        self.cols.iter().find(|c| c.name == name)
    }

    #[must_use]
    pub fn col_names(&self) -> Vec<Ident> {
        self.cols.iter().map(|c| c.name.clone()).collect()
    }

    #[must_use]
    pub fn all_col_tags(&self) -> TagSet {
        TagSet::union_list(self.cols.iter().map(|c| &c.tags))
    }

    #[must_use]
    pub fn total_tags(&self) -> TagSet {
        self.row_tags
            .union(&self.order_tags)
            .union(&self.all_col_tags())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LocalHttpTarget {
    Pinned(String),
    Named(Ident),
}

impl LocalHttpTarget {
    #[must_use]
    pub fn policy_key(&self) -> &str {
        match self {
            Self::Pinned(s) | Self::Named(s) => s.as_str(),
        }
    }

    #[must_use]
    pub fn display_label(&self) -> String {
        match self {
            Self::Pinned(s) => format!("\"{s}\""),
            Self::Named(n) => n.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LocalSocketTarget {
    Pinned(String),
    Named(Ident),
}

impl LocalSocketTarget {
    #[must_use]
    pub fn policy_key(&self) -> &str {
        match self {
            Self::Pinned(s) | Self::Named(s) => s.as_str(),
        }
    }

    #[must_use]
    pub fn display_label(&self) -> String {
        match self {
            Self::Pinned(s) => format!("\"{s}\""),
            Self::Named(n) => n.clone(),
        }
    }
}

#[derive(Debug, Default, Eq)]
pub enum Ty {
    #[default]
    Unit,
    Bool,
    Int,
    Decimal,
    Float,
    Text,
    Bytes,
    Date,
    Timestamp,
    Duration,
    Option(Box<Ty>),
    Result {
        ok_ty: Box<Ty>,
        err_ty: Box<Ty>,
    },
    Tuple(Vec<LTy>),
    List(Box<LTy>),
    Map {
        key: Box<LTy>,
        val: Box<LTy>,
    },
    Data(Ident),
    Table(TableTy),
    DynamicTable(TagSet),
    Chart(TagSet),
    Report(TagSet),
    Profile(TagSet),
    LinearModel,
    StatTest,
    Fn {
        params: Vec<LTy>,
        pc: TagSet,
        ret: Box<LTy>,
    },
    Args,
    Clock,
    Console(TagSet),
    ReadFiles,
    WriteFiles {
        root: String,
        allows: TagSet,
    },
    ReadDB(Ident),
    WriteTable {
        db: Ident,
        table_name: Ident,
        dest_cols: Vec<ColSpec>,
        dest_row_tags: TagSet,
        allows: TagSet,
    },
    RawReadDB(Ident),
    HttpsAllow {
        host: String,
        allows: TagSet,
    },
    LocalHttpAllow {
        target: LocalHttpTarget,
        allows: TagSet,
    },
    LocalSocketAllow {
        target: LocalSocketTarget,
        allows: TagSet,
    },
    Secret(String),
    Declassify(TagSet),
}

impl Clone for Ty {
    fn clone(&self) -> Self {
        enum Build<'a> {
            Option,
            Result,
            Tuple(&'a [LTy]),
            List(&'a TagSet),
            Map(&'a TagSet, &'a TagSet),
            Fn {
                params: &'a [LTy],
                pc: &'a TagSet,
                ret_tags: &'a TagSet,
            },
        }
        enum Task<'a> {
            Ty(&'a Ty),
            Build(Build<'a>),
        }
        let mut tasks = vec![Task::Ty(self)];
        let mut vals: Vec<Self> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Ty(cur) => match cur {
                    Self::Unit => vals.push(Self::Unit),
                    Self::Bool => vals.push(Self::Bool),
                    Self::Int => vals.push(Self::Int),
                    Self::Decimal => vals.push(Self::Decimal),
                    Self::Float => vals.push(Self::Float),
                    Self::Text => vals.push(Self::Text),
                    Self::Bytes => vals.push(Self::Bytes),
                    Self::Date => vals.push(Self::Date),
                    Self::Timestamp => vals.push(Self::Timestamp),
                    Self::Duration => vals.push(Self::Duration),
                    Self::LinearModel => vals.push(Self::LinearModel),
                    Self::StatTest => vals.push(Self::StatTest),
                    Self::Args => vals.push(Self::Args),
                    Self::Clock => vals.push(Self::Clock),
                    Self::ReadFiles => vals.push(Self::ReadFiles),
                    Self::Data(s) => vals.push(Self::Data(s.clone())),
                    Self::Table(tt) => vals.push(Self::Table(tt.clone())),
                    Self::DynamicTable(ts) => vals.push(Self::DynamicTable(ts.clone())),
                    Self::Chart(ts) => vals.push(Self::Chart(ts.clone())),
                    Self::Report(ts) => vals.push(Self::Report(ts.clone())),
                    Self::Profile(ts) => vals.push(Self::Profile(ts.clone())),
                    Self::Console(ts) => vals.push(Self::Console(ts.clone())),
                    Self::ReadDB(s) => vals.push(Self::ReadDB(s.clone())),
                    Self::RawReadDB(s) => vals.push(Self::RawReadDB(s.clone())),
                    Self::Secret(s) => vals.push(Self::Secret(s.clone())),
                    Self::Declassify(ts) => vals.push(Self::Declassify(ts.clone())),
                    Self::WriteFiles { root, allows } => vals.push(Self::WriteFiles {
                        root: root.clone(),
                        allows: allows.clone(),
                    }),
                    Self::WriteTable {
                        db,
                        table_name,
                        dest_cols,
                        dest_row_tags,
                        allows,
                    } => vals.push(Self::WriteTable {
                        db: db.clone(),
                        table_name: table_name.clone(),
                        dest_cols: dest_cols.clone(),
                        dest_row_tags: dest_row_tags.clone(),
                        allows: allows.clone(),
                    }),
                    Self::HttpsAllow { host, allows } => vals.push(Self::HttpsAllow {
                        host: host.clone(),
                        allows: allows.clone(),
                    }),
                    Self::LocalHttpAllow { target, allows } => vals.push(Self::LocalHttpAllow {
                        target: target.clone(),
                        allows: allows.clone(),
                    }),
                    Self::LocalSocketAllow { target, allows } => {
                        vals.push(Self::LocalSocketAllow {
                            target: target.clone(),
                            allows: allows.clone(),
                        })
                    }
                    Self::Option(inner) => {
                        tasks.push(Task::Build(Build::Option));
                        tasks.push(Task::Ty(inner));
                    }
                    Self::Result { ok_ty, err_ty } => {
                        tasks.push(Task::Build(Build::Result));
                        tasks.push(Task::Ty(err_ty));
                        tasks.push(Task::Ty(ok_ty));
                    }
                    Self::Tuple(elems) => {
                        tasks.push(Task::Build(Build::Tuple(elems)));
                        for e in elems.iter().rev() {
                            tasks.push(Task::Ty(&e.ty));
                        }
                    }
                    Self::List(elem) => {
                        tasks.push(Task::Build(Build::List(&elem.tags)));
                        tasks.push(Task::Ty(&elem.ty));
                    }
                    Self::Map { key, val } => {
                        tasks.push(Task::Build(Build::Map(&key.tags, &val.tags)));
                        tasks.push(Task::Ty(&val.ty));
                        tasks.push(Task::Ty(&key.ty));
                    }
                    Self::Fn { params, pc, ret } => {
                        tasks.push(Task::Build(Build::Fn {
                            params,
                            pc,
                            ret_tags: &ret.tags,
                        }));
                        tasks.push(Task::Ty(&ret.ty));
                        for p in params.iter().rev() {
                            tasks.push(Task::Ty(&p.ty));
                        }
                    }
                },
                Task::Build(build) => match build {
                    Build::Option => {
                        let Some(inner) = vals.pop() else {
                            unreachable!("stack balanced");
                        };
                        vals.push(Self::Option(Box::new(inner)));
                    }
                    Build::Result => {
                        let (Some(err_ty), Some(ok_ty)) = (vals.pop(), vals.pop()) else {
                            unreachable!("stack balanced");
                        };
                        vals.push(Self::Result {
                            ok_ty: Box::new(ok_ty),
                            err_ty: Box::new(err_ty),
                        });
                    }
                    Build::Tuple(elems) => {
                        let tys = vals.split_off(vals.len() - elems.len());
                        let out = tys
                            .into_iter()
                            .zip(elems)
                            .map(|(ty, e)| LTy::new(ty, e.tags.clone()))
                            .collect();
                        vals.push(Self::Tuple(out));
                    }
                    Build::List(tags) => {
                        let Some(ty) = vals.pop() else {
                            unreachable!("stack balanced");
                        };
                        vals.push(Self::List(Box::new(LTy::new(ty, tags.clone()))));
                    }
                    Build::Map(k_tags, v_tags) => {
                        let (Some(v_ty), Some(k_ty)) = (vals.pop(), vals.pop()) else {
                            unreachable!("stack balanced");
                        };
                        vals.push(Self::Map {
                            key: Box::new(LTy::new(k_ty, k_tags.clone())),
                            val: Box::new(LTy::new(v_ty, v_tags.clone())),
                        });
                    }
                    Build::Fn {
                        params,
                        pc,
                        ret_tags,
                    } => {
                        let Some(ret_ty) = vals.pop() else {
                            unreachable!("stack balanced");
                        };
                        let p_tys = vals.split_off(vals.len() - params.len());
                        let out_params = p_tys
                            .into_iter()
                            .zip(params)
                            .map(|(ty, p)| LTy::new(ty, p.tags.clone()))
                            .collect();
                        vals.push(Self::Fn {
                            params: out_params,
                            pc: pc.clone(),
                            ret: Box::new(LTy::new(ret_ty, ret_tags.clone())),
                        });
                    }
                },
            }
        }
        match vals.pop() {
            Some(res) => res,
            None => unreachable!("Ty::clone always produces one Ty"),
        }
    }
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (Self::Unit, Self::Unit)
                | (Self::Bool, Self::Bool)
                | (Self::Int, Self::Int)
                | (Self::Decimal, Self::Decimal)
                | (Self::Float, Self::Float)
                | (Self::Text, Self::Text)
                | (Self::Bytes, Self::Bytes)
                | (Self::Date, Self::Date)
                | (Self::Timestamp, Self::Timestamp)
                | (Self::Duration, Self::Duration)
                | (Self::LinearModel, Self::LinearModel)
                | (Self::StatTest, Self::StatTest)
                | (Self::Args, Self::Args)
                | (Self::Clock, Self::Clock)
                | (Self::ReadFiles, Self::ReadFiles) => {}
                (Self::Option(x), Self::Option(y)) => stack.push((x, y)),
                (
                    Self::Result {
                        ok_ty: ok1,
                        err_ty: err1,
                    },
                    Self::Result {
                        ok_ty: ok2,
                        err_ty: err2,
                    },
                ) => {
                    stack.push((ok1, ok2));
                    stack.push((err1, err2));
                }
                (Self::Tuple(xs), Self::Tuple(ys)) => {
                    if xs.len() != ys.len() {
                        return false;
                    }
                    for (x, y) in xs.iter().zip(ys) {
                        if x.tags != y.tags {
                            return false;
                        }
                        stack.push((&x.ty, &y.ty));
                    }
                }
                (Self::List(x), Self::List(y)) => {
                    if x.tags != y.tags {
                        return false;
                    }
                    stack.push((&x.ty, &y.ty));
                }
                (Self::Map { key: k1, val: v1 }, Self::Map { key: k2, val: v2 }) => {
                    if k1.tags != k2.tags || v1.tags != v2.tags {
                        return false;
                    }
                    stack.push((&k1.ty, &k2.ty));
                    stack.push((&v1.ty, &v2.ty));
                }
                (Self::Data(x), Self::Data(y))
                | (Self::ReadDB(x), Self::ReadDB(y))
                | (Self::RawReadDB(x), Self::RawReadDB(y))
                | (Self::Secret(x), Self::Secret(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (Self::Table(x), Self::Table(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (Self::DynamicTable(x), Self::DynamicTable(y))
                | (Self::Chart(x), Self::Chart(y))
                | (Self::Report(x), Self::Report(y))
                | (Self::Profile(x), Self::Profile(y))
                | (Self::Console(x), Self::Console(y))
                | (Self::Declassify(x), Self::Declassify(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (
                    Self::Fn {
                        params: p1,
                        pc: pc1,
                        ret: r1,
                    },
                    Self::Fn {
                        params: p2,
                        pc: pc2,
                        ret: r2,
                    },
                ) => {
                    if pc1 != pc2 || r1.tags != r2.tags || p1.len() != p2.len() {
                        return false;
                    }
                    stack.push((&r1.ty, &r2.ty));
                    for (x, y) in p1.iter().zip(p2) {
                        if x.tags != y.tags {
                            return false;
                        }
                        stack.push((&x.ty, &y.ty));
                    }
                }
                (
                    Self::WriteFiles {
                        root: r1,
                        allows: a1,
                    },
                    Self::WriteFiles {
                        root: r2,
                        allows: a2,
                    },
                ) => {
                    if r1 != r2 || a1 != a2 {
                        return false;
                    }
                }
                (
                    Self::WriteTable {
                        db: d1,
                        table_name: t1,
                        dest_cols: c1,
                        dest_row_tags: rt1,
                        allows: a1,
                    },
                    Self::WriteTable {
                        db: d2,
                        table_name: t2,
                        dest_cols: c2,
                        dest_row_tags: rt2,
                        allows: a2,
                    },
                ) => {
                    if d1 != d2 || t1 != t2 || c1 != c2 || rt1 != rt2 || a1 != a2 {
                        return false;
                    }
                }
                (
                    Self::HttpsAllow {
                        host: h1,
                        allows: a1,
                    },
                    Self::HttpsAllow {
                        host: h2,
                        allows: a2,
                    },
                ) => {
                    if h1 != h2 || a1 != a2 {
                        return false;
                    }
                }
                (
                    Self::LocalHttpAllow {
                        target: t1,
                        allows: a1,
                    },
                    Self::LocalHttpAllow {
                        target: t2,
                        allows: a2,
                    },
                ) => {
                    if t1 != t2 || a1 != a2 {
                        return false;
                    }
                }
                (
                    Self::LocalSocketAllow {
                        target: t1,
                        allows: a1,
                    },
                    Self::LocalSocketAllow {
                        target: t2,
                        allows: a2,
                    },
                ) => {
                    if t1 != t2 || a1 != a2 {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Hash for Ty {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut stack: Vec<&Self> = vec![self];
        while let Some(cur) = stack.pop() {
            std::mem::discriminant(cur).hash(state);
            match cur {
                Self::Option(inner) => stack.push(inner),
                Self::Result { ok_ty, err_ty } => {
                    stack.push(err_ty);
                    stack.push(ok_ty);
                }
                Self::Tuple(xs) => {
                    xs.len().hash(state);
                    for x in xs.iter().rev() {
                        x.tags.hash(state);
                        stack.push(&x.ty);
                    }
                }
                Self::List(x) => {
                    x.tags.hash(state);
                    stack.push(&x.ty);
                }
                Self::Map { key, val } => {
                    key.tags.hash(state);
                    val.tags.hash(state);
                    stack.push(&val.ty);
                    stack.push(&key.ty);
                }
                Self::Data(n) | Self::ReadDB(n) | Self::RawReadDB(n) | Self::Secret(n) => {
                    n.hash(state);
                }
                Self::Table(tt) => tt.hash(state),
                Self::DynamicTable(ts)
                | Self::Chart(ts)
                | Self::Report(ts)
                | Self::Profile(ts)
                | Self::Console(ts)
                | Self::Declassify(ts) => ts.hash(state),
                Self::Fn { params, pc, ret } => {
                    params.len().hash(state);
                    pc.hash(state);
                    ret.tags.hash(state);
                    stack.push(&ret.ty);
                    for p in params.iter().rev() {
                        p.tags.hash(state);
                        stack.push(&p.ty);
                    }
                }
                Self::WriteFiles { root, allows } => {
                    root.hash(state);
                    allows.hash(state);
                }
                Self::WriteTable {
                    db,
                    table_name,
                    dest_cols,
                    dest_row_tags,
                    allows,
                } => {
                    db.hash(state);
                    table_name.hash(state);
                    dest_cols.hash(state);
                    dest_row_tags.hash(state);
                    allows.hash(state);
                }
                Self::HttpsAllow { host, allows } => {
                    host.hash(state);
                    allows.hash(state);
                }
                Self::LocalHttpAllow { target, allows } => {
                    target.hash(state);
                    allows.hash(state);
                }
                Self::LocalSocketAllow { target, allows } => {
                    target.hash(state);
                    allows.hash(state);
                }
                _ => {}
            }
        }
    }
}

impl Ty {
    #[must_use]
    pub fn is_option(&self) -> bool {
        matches!(self, Self::Option(_))
    }

    #[must_use]
    pub fn into_table(mut self) -> Option<TableTy> {
        match &mut self {
            Self::Table(tt) => Some(std::mem::take(tt)),
            _ => None,
        }
    }

    #[must_use]
    pub fn to_scalar_ty(&self) -> Option<ScalarTy> {
        let mut depth = 0usize;
        let mut cur = self;
        while let Self::Option(inner) = cur {
            depth += 1;
            cur = inner;
        }
        let mut out = match cur {
            Self::Unit => ScalarTy::Unit,
            Self::Bool => ScalarTy::Bool,
            Self::Int => ScalarTy::Int,
            Self::Decimal => ScalarTy::Decimal,
            Self::Float => ScalarTy::Float,
            Self::Text => ScalarTy::Text,
            Self::Bytes => ScalarTy::Bytes,
            Self::Date => ScalarTy::Date,
            Self::Timestamp => ScalarTy::Timestamp,
            Self::Duration => ScalarTy::Duration,
            Self::Data(n) => ScalarTy::Data(n.clone()),
            _ => return None,
        };
        for _ in 0..depth {
            out = ScalarTy::Option(Box::new(out));
        }
        Some(out)
    }

    /// Union of all sensitivity tags appearing anywhere inside `Ty`.
    #[must_use]
    pub fn all_tags(&self) -> TagSet {
        match self {
            Self::Unit
            | Self::Bool
            | Self::Int
            | Self::Decimal
            | Self::Float
            | Self::Text
            | Self::Bytes
            | Self::Date
            | Self::Timestamp
            | Self::Duration
            | Self::Data(_)
            | Self::LinearModel
            | Self::StatTest
            | Self::Args
            | Self::Clock
            | Self::ReadFiles
            | Self::ReadDB(_)
            | Self::RawReadDB(_) => TagSet::empty(),
            Self::Option(inner) => inner.all_tags(),
            Self::Result { ok_ty, err_ty } => ok_ty.all_tags().union(&err_ty.all_tags()),
            Self::Tuple(elems) => TagSet::union_owned(elems.iter().map(LTy::all_tags)),
            Self::List(elem) => elem.all_tags(),
            Self::Map { key, val } => key.all_tags().union(&val.all_tags()),
            Self::Table(tt) => tt.total_tags(),
            Self::DynamicTable(ts)
            | Self::Chart(ts)
            | Self::Report(ts)
            | Self::Profile(ts)
            | Self::Console(ts)
            | Self::Declassify(ts) => ts.clone(),
            Self::WriteFiles { allows, .. }
            | Self::WriteTable { allows, .. }
            | Self::HttpsAllow { allows, .. }
            | Self::LocalHttpAllow { allows, .. }
            | Self::LocalSocketAllow { allows, .. } => allows.clone(),
            Self::Secret(_) => TagSet::singleton("secret"),
            Self::Fn { params, pc, ret } => TagSet::union_owned(params.iter().map(LTy::all_tags))
                .union(&pc.union(&ret.all_tags())),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LTy {
    pub ty: Ty,
    pub tags: TagSet,
}

impl LTy {
    #[must_use]
    pub fn new(ty: Ty, tags: TagSet) -> Self {
        Self { ty, tags }
    }

    #[must_use]
    pub fn public(ty: Ty) -> Self {
        Self {
            ty,
            tags: TagSet::empty(),
        }
    }

    #[must_use]
    pub fn all_tags(&self) -> TagSet {
        self.ty.all_tags().union(&self.tags)
    }

    #[must_use]
    pub fn add_tags(&self, extra: &TagSet) -> Self {
        Self {
            ty: self.ty.clone(),
            tags: self.tags.union(extra),
        }
    }

    #[must_use]
    pub fn effective_tags(&self) -> TagSet {
        match &self.ty {
            Ty::Table(tt) => tt.total_tags().union(&self.tags),
            Ty::DynamicTable(dt) => dt.union(&self.tags),
            Ty::Chart(ct) => ct.union(&self.tags),
            Ty::Report(rt) => rt.union(&self.tags),
            Ty::Profile(pt) => pt.union(&self.tags),
            Ty::Secret(_) => TagSet::singleton("secret").union(&self.tags),
            ty => ty.all_tags().union(&self.tags),
        }
    }
}

/// IEEE-754 binary64 bit pattern with transparent structural equality.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Float64 {
    pub bits: u64,
}

impl Float64 {
    pub const ZERO: Self = Self { bits: 0 };
    pub const CANONICAL_NAN: Self = Self {
        bits: 0x7ff8_0000_0000_0000,
    };

    #[must_use]
    pub const fn from_bits(bits: u64) -> Self {
        Self { bits }
    }

    #[must_use]
    pub fn from_f64(x: f64) -> Self {
        if x.is_nan() {
            Self::CANONICAL_NAN
        } else {
            Self { bits: x.to_bits() }
        }
    }

    #[must_use]
    pub const fn to_f64(self) -> f64 {
        f64::from_bits(self.bits)
    }

    #[must_use]
    pub const fn is_nan(self) -> bool {
        let exp = (self.bits >> 52) & 0x7FF;
        let mant = self.bits & 0x000F_FFFF_FFFF_FFFF;
        exp == 0x7FF && mant != 0
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum Literal {
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
    NoneLit(Ty),
}

impl Literal {
    #[must_use]
    pub fn int(n: impl Into<BigInt>) -> Self {
        Self::Int(n.into())
    }

    #[must_use]
    pub fn decimal(scaled: impl Into<BigInt>) -> Self {
        Self::Decimal(scaled.into())
    }

    #[must_use]
    pub fn date(days: impl Into<BigInt>) -> Self {
        Self::Date(days.into())
    }

    #[must_use]
    pub fn timestamp(micros: impl Into<BigInt>) -> Self {
        Self::Timestamp(micros.into())
    }

    #[must_use]
    pub fn duration(micros: impl Into<BigInt>) -> Self {
        Self::Duration(micros.into())
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ChartKind {
    #[default]
    Bar,
    Line,
    Scatter,
    Histogram,
    Heatmap,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimOp {
    SomeVal(Ty),
    IsSome,
    IsNone,
    UnwrapOr,
    UnwrapBang,
    OkVal(Ty),
    ErrVal(Ty),
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    ModInt,
    NegInt,
    AddDec,
    SubDec,
    MulDec,
    DivDec,
    NegDec,
    IntToDec,
    BoolToDec,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    NotBool,
    AndBool,
    OrBool,
    ConcatText,
    TrimText,
    LowerAsciiText,
    ContainsText,
    EmptyText,
    IntToText,
    DecToText,
    DateTruncMonth,
    AddDuration,
    DiffTimestamp,
    ListLit(LTy),
    ListLen,
    ListEmpty,
    ListAppend,
    ListConcat,
    MapLit {
        key_lty: LTy,
        val_lty: LTy,
    },
    MapGet,
    TableCount,
    TableConcat(TableTy),
    TableProfile,
    StatsCorr {
        col_x: Ident,
        col_y: Ident,
    },
    StatsLinReg {
        col_x: Ident,
        col_y: Ident,
    },
    StatsTTest {
        col_x: Ident,
        col_y: Ident,
    },
    ChartMake {
        kind: ChartKind,
        cols: Vec<Ident>,
        title: String,
    },
    ReportNew,
    ReportAddSummary,
    ReportAddChart,
    ReportAddTable,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HostOp {
    ArgsGet,
    ClockNow,
    ConsolePrint,
    ConsoleError,
    ConsolePrintTable,
    ReadCsv(Ident),
    WriteFile,
    WriteReportHtml,
    WriteTable,
    DeclassifyApprove(TagSet),
    RawSqlQuery { db: Ident, out_schema: TableTy },
    HttpsGetJson,
    ReadParquet(TableTy),
    WriteParquet,
    WriteXlsx,
    FakeConsole(TagSet),
    FakeFiles(TagSet),
    FakeDB(Ident),
    FakeHttps { host: String, allows: TagSet },
    FakeSecret(String),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum BugKind {
    #[default]
    IntOverflow,
    DecimalOverflow,
    DivByZero,
    UnwrapNone,
    JoinCardinality,
    PromiseViolation,
    SchemaConstraint,
    ExportGateDenied,
    OutsideBoundary,
    UserStop,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum SortDir {
    #[default]
    Asc,
    Desc,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum JoinKind {
    #[default]
    InnerOne,
    InnerManyToOne,
    InnerMany,
    LeftOne,
    LeftManyToOne,
    Semi,
    Anti,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum JoinOn {
    SameKeys(Vec<Ident>),
    Pairs(Vec<(Ident, Ident)>),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum AggOp {
    #[default]
    Count,
    CountDistinct,
    Sum,
    Mean,
    Stddev,
    Variance,
    Median,
    Percentile(Float64),
    Min,
    Max,
    First,
    Last,
}

impl AggOp {
    #[must_use]
    pub const fn is_blending(self) -> bool {
        match self {
            Self::Count
            | Self::CountDistinct
            | Self::Sum
            | Self::Mean
            | Self::Stddev
            | Self::Variance => true,
            Self::Median
            | Self::Percentile(_)
            | Self::Min
            | Self::Max
            | Self::First
            | Self::Last => false,
        }
    }

    #[must_use]
    pub const fn is_order_sensitive(self) -> bool {
        matches!(self, Self::First | Self::Last)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum SuppressMode {
    #[default]
    Drop,
    MaskComplementary,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowExpr {
    Lit(Literal),
    Col(Ident),
    OuterVar(Ident),
    ConstRef(Ident),
    Prim {
        op: PrimOp,
        args: Vec<RowExpr>,
    },
    IfE {
        cond: Box<RowExpr>,
        then_br: Box<RowExpr>,
        else_br: Box<RowExpr>,
    },
    Coalesce {
        opt_expr: Box<RowExpr>,
        default_expr: Box<RowExpr>,
    },
    CallPure {
        fn_name: Ident,
        args: Vec<RowExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggItem {
    pub name: Ident,
    pub op: AggOp,
    pub arg: Option<RowExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeriveItem {
    ColExpr {
        name: Ident,
        expr: Box<RowExpr>,
    },
    BucketCol {
        name: Ident,
        source: Ident,
        cuts: Vec<Literal>,
        labels: Vec<String>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum WindowFn {
    Lag { col: Ident, offset: BigInt },
    Lead { col: Ident, offset: BigInt },
    RowNumber,
    Rank { col: Ident },
    RunningSum { col: Ident },
    RollingMean { col: Ident, window_size: BigInt },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WindowItem {
    pub name: Ident,
    pub win_fn: WindowFn,
    pub over: Vec<Ident>,
    pub order: Vec<(Ident, SortDir)>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RowLit {
    pub cells: Vec<Literal>,
}

pub type Suffixes = Option<(String, String)>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseArm {
    pub ctor: Ident,
    pub binders: Vec<Ident>,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Lit(Literal),
    Var(Ident),
    ConstRef(Ident),
    LetE {
        name: Ident,
        lty: LTy,
        bound: Box<Expr>,
        body: Box<Expr>,
    },
    IfE {
        cond: Box<Expr>,
        then_br: Box<Expr>,
        else_br: Box<Expr>,
    },
    CaseE {
        scrut: Box<Expr>,
        arms: Vec<CaseArm>,
    },
    Lam {
        params: Vec<(Ident, LTy)>,
        pc: TagSet,
        ret: LTy,
        body: Arc<Expr>,
    },
    App {
        fn_expr: Box<Expr>,
        args: Vec<Expr>,
    },
    Call {
        fn_name: Ident,
        args: Vec<Expr>,
    },
    Join {
        label: Ident,
        params: Vec<(Ident, LTy)>,
        rhs: Box<Expr>,
        body: Box<Expr>,
    },
    Jump {
        label: Ident,
        args: Vec<Expr>,
    },
    Tuple(Vec<Expr>),
    Proj {
        tup: Box<Expr>,
        idx: BigInt,
    },
    Ctor {
        type_name: Ident,
        ctor_name: Ident,
        args: Vec<Expr>,
    },
    TableLit {
        schema: TableTy,
        rows: Vec<RowLit>,
    },
    Prim {
        op: PrimOp,
        args: Vec<Expr>,
    },
    Rel(Box<Plan>),
    Host {
        op: HostOp,
        args: Vec<Expr>,
    },
    Stop {
        kind: BugKind,
        detail: Option<Box<Expr>>,
    },
    Fail(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Plan {
    SourceExpr(Box<Expr>),
    SourceDB {
        cap: Box<Expr>,
        table_name: Ident,
        schema: TableTy,
    },
    Select {
        input: Box<Plan>,
        cols: Vec<Ident>,
    },
    Drop {
        input: Box<Plan>,
        cols: Vec<Ident>,
    },
    Rename {
        input: Box<Plan>,
        pairs: Vec<(Ident, Ident)>,
    },
    Derive {
        input: Box<Plan>,
        items: Vec<DeriveItem>,
    },
    Filter {
        input: Box<Plan>,
        pred: RowExpr,
    },
    Distinct {
        input: Box<Plan>,
        cols: Vec<Ident>,
    },
    Sort {
        input: Box<Plan>,
        keys: Vec<(Ident, SortDir)>,
    },
    Limit {
        input: Box<Plan>,
        n: BigInt,
    },
    Join {
        kind: JoinKind,
        left: Box<Plan>,
        right: Box<Plan>,
        on: JoinOn,
        suffixes: Suffixes,
    },
    Union {
        left: Box<Plan>,
        right: Box<Plan>,
    },
    GroupBy {
        input: Box<Plan>,
        keys: Vec<Ident>,
    },
    Summarize {
        input: Box<Plan>,
        aggs: Vec<AggItem>,
        distinct_key: Option<Ident>,
    },
    SuppressSmallGroups {
        input: Box<Plan>,
        min_k: BigInt,
        distinct_by: Option<Ident>,
        mode: SuppressMode,
    },
    Window {
        input: Box<Plan>,
        items: Vec<WindowItem>,
    },
    FillGaps {
        input: Box<Plan>,
        col: Ident,
        step_micros: BigInt,
        over: Vec<Ident>,
        fill: Vec<(Ident, Literal)>,
    },
    PivotWider {
        input: Box<Plan>,
        names_from: Ident,
        values_from: Ident,
        static_cols: Vec<Ident>,
        fill: Literal,
    },
    Crosstab {
        input: Box<Plan>,
        rows_col: Ident,
        cols_col: Ident,
        values_col: Ident,
        fill: Literal,
    },
    Redact {
        input: Box<Plan>,
        col: Ident,
        replacement: String,
    },
    Pseudonymize {
        input: Box<Plan>,
        col: Ident,
        secret: Box<Expr>,
    },
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PolicyWriteRule {
    pub db: Ident,
    pub table: Ident,
    pub tags: TagSet,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Policy {
    pub min_group_size: BigInt,
    pub forbid_manual_declassify: bool,
    pub forbid_repl_sensitive: bool,
    pub forbid_local_http: bool,
    pub forbid_local_socket: bool,
    pub allow_console: TagSet,
    pub allow_export: Vec<(String, TagSet)>,
    pub allow_https: Vec<(String, TagSet)>,
    pub allow_local_http: Vec<(String, TagSet)>,
    pub allow_local_socket: Vec<(String, TagSet)>,
    pub allow_write: Vec<PolicyWriteRule>,
}

impl Default for Policy {
    fn default() -> Self {
        Self {
            min_group_size: BigInt::from(5u64),
            forbid_manual_declassify: false,
            forbid_repl_sensitive: false,
            forbid_local_http: false,
            forbid_local_socket: false,
            allow_console: TagSet::empty(),
            allow_export: Vec::new(),
            allow_https: Vec::new(),
            allow_local_http: Vec::new(),
            allow_local_socket: Vec::new(),
            allow_write: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct CtorDecl {
    pub name: Ident,
    pub fields: Vec<LTy>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct DataDecl {
    pub name: Ident,
    pub ctors: Vec<CtorDecl>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SchemaDecl {
    pub name: Ident,
    pub schema: TableTy,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ConstDecl {
    pub name: Ident,
    pub lty: LTy,
    pub value: Literal,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum FunKind {
    #[default]
    Function,
    Test,
    ExampleDecl,
    Promise,
}

impl FunKind {
    #[must_use]
    pub const fn is_spec(self) -> bool {
        match self {
            Self::Function => false,
            Self::Test | Self::ExampleDecl | Self::Promise => true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunDecl {
    pub name: Ident,
    pub kind: FunKind,
    pub is_pure: bool,
    pub params: Vec<(Ident, LTy)>,
    pub pc: TagSet,
    pub ret: LTy,
    pub body: Expr,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub file: String,
    pub start_line: BigInt,
    pub start_col: BigInt,
    pub end_line: BigInt,
    pub end_col: BigInt,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct MetaEntry {
    pub node_id: Ident,
    pub orig_name: Option<String>,
    pub span: Option<SourceSpan>,
}

/// Lossless compiler diagnostic metadata. Never read by typing or evaluation.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct CompilerMetadata {
    pub entries: Vec<MetaEntry>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CoreVersion {
    pub major: u64,
    pub minor: u64,
}

impl Default for CoreVersion {
    fn default() -> Self {
        Self { major: 0, minor: 1 }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub version: CoreVersion,
    pub tags: Vec<Tag>,
    pub policy: Option<Policy>,
    pub datas: Vec<DataDecl>,
    pub schemas: Vec<SchemaDecl>,
    pub consts: Vec<ConstDecl>,
    pub funs: Vec<FunDecl>,
    pub entry: Option<Ident>,
    pub metadata: CompilerMetadata,
}

impl Program {
    #[must_use]
    pub fn find_data(&self, name: &str) -> Option<&DataDecl> {
        self.datas.iter().find(|d| d.name == name)
    }

    #[must_use]
    pub fn find_schema(&self, name: &str) -> Option<&SchemaDecl> {
        self.schemas.iter().find(|s| s.name == name)
    }

    #[must_use]
    pub fn find_const(&self, name: &str) -> Option<&ConstDecl> {
        self.consts.iter().find(|c| c.name == name)
    }

    #[must_use]
    pub fn find_fun(&self, name: &str) -> Option<&FunDecl> {
        self.funs.iter().find(|f| f.name == name)
    }

    #[must_use]
    pub fn min_group_floor(&self) -> BigInt {
        let default_floor = BigInt::from(5u64);
        match &self.policy {
            None => default_floor,
            Some(p) => p.min_group_size.clone().max(default_floor),
        }
    }
}

// ---------------------------------------------------------------------------
// Iterative Drop Implementations (Prevent Drop-Time Stack Overflow on Deep ASTs)
// ---------------------------------------------------------------------------

impl Drop for ScalarTy {
    fn drop(&mut self) {
        let mut cur = match self {
            Self::Option(inner) if matches!(inner.as_ref(), Self::Option(_)) => {
                Some(std::mem::replace(inner.as_mut(), Self::Unit))
            }
            _ => None,
        };
        while let Some(mut node) = cur {
            cur = match &mut node {
                Self::Option(inner) if matches!(inner.as_ref(), Self::Option(_)) => {
                    Some(std::mem::replace(inner.as_mut(), Self::Unit))
                }
                _ => None,
            };
        }
    }
}

fn is_recursive_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Option(_)
            | Ty::Result { .. }
            | Ty::Tuple(_)
            | Ty::List(_)
            | Ty::Map { .. }
            | Ty::Fn { .. }
    )
}

fn push_ty_children(ty: &mut Ty, stack: &mut Vec<Ty>) {
    match ty {
        Ty::Option(inner) => {
            if is_recursive_ty(inner) {
                stack.push(std::mem::replace(inner.as_mut(), Ty::Unit));
            }
        }
        Ty::Result { ok_ty, err_ty } => {
            if is_recursive_ty(ok_ty) {
                stack.push(std::mem::replace(ok_ty.as_mut(), Ty::Unit));
            }
            if is_recursive_ty(err_ty) {
                stack.push(std::mem::replace(err_ty.as_mut(), Ty::Unit));
            }
        }
        Ty::Tuple(elems) => {
            for elem in std::mem::take(elems) {
                if is_recursive_ty(&elem.ty) {
                    stack.push(elem.ty);
                }
            }
        }
        Ty::List(inner) => {
            if is_recursive_ty(&inner.ty) {
                stack.push(std::mem::replace(&mut inner.ty, Ty::Unit));
            }
        }
        Ty::Map { key, val } => {
            if is_recursive_ty(&key.ty) {
                stack.push(std::mem::replace(&mut key.ty, Ty::Unit));
            }
            if is_recursive_ty(&val.ty) {
                stack.push(std::mem::replace(&mut val.ty, Ty::Unit));
            }
        }
        Ty::Fn { params, ret, .. } => {
            for p in std::mem::take(params) {
                if is_recursive_ty(&p.ty) {
                    stack.push(p.ty);
                }
            }
            if is_recursive_ty(&ret.ty) {
                stack.push(std::mem::replace(&mut ret.ty, Ty::Unit));
            }
        }
        _ => {}
    }
}

impl Drop for Ty {
    fn drop(&mut self) {
        if !is_recursive_ty(self) {
            return;
        }
        let mut stack = Vec::new();
        push_ty_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            push_ty_children(&mut node, &mut stack);
        }
    }
}

fn is_leaf_row_expr(re: &RowExpr) -> bool {
    matches!(
        re,
        RowExpr::Lit(_) | RowExpr::Col(_) | RowExpr::OuterVar(_) | RowExpr::ConstRef(_)
    )
}

fn push_row_expr_children(re: &mut RowExpr, stack: &mut Vec<RowExpr>) {
    match re {
        RowExpr::Lit(_) | RowExpr::Col(_) | RowExpr::OuterVar(_) | RowExpr::ConstRef(_) => {}
        RowExpr::Prim { args, .. } | RowExpr::CallPure { args, .. } => {
            for arg in std::mem::take(args) {
                if !is_leaf_row_expr(&arg) {
                    stack.push(arg);
                }
            }
        }
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            if !is_leaf_row_expr(cond) {
                stack.push(std::mem::replace(
                    cond.as_mut(),
                    RowExpr::Lit(Literal::Unit),
                ));
            }
            if !is_leaf_row_expr(then_br) {
                stack.push(std::mem::replace(
                    then_br.as_mut(),
                    RowExpr::Lit(Literal::Unit),
                ));
            }
            if !is_leaf_row_expr(else_br) {
                stack.push(std::mem::replace(
                    else_br.as_mut(),
                    RowExpr::Lit(Literal::Unit),
                ));
            }
        }
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            if !is_leaf_row_expr(opt_expr) {
                stack.push(std::mem::replace(
                    opt_expr.as_mut(),
                    RowExpr::Lit(Literal::Unit),
                ));
            }
            if !is_leaf_row_expr(default_expr) {
                stack.push(std::mem::replace(
                    default_expr.as_mut(),
                    RowExpr::Lit(Literal::Unit),
                ));
            }
        }
    }
}

impl Drop for RowExpr {
    fn drop(&mut self) {
        if is_leaf_row_expr(self) {
            return;
        }
        let mut stack: Vec<Self> = Vec::new();
        push_row_expr_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            push_row_expr_children(&mut node, &mut stack);
        }
    }
}

enum DropNode {
    Expr(Expr),
    Plan(Plan),
}

fn is_leaf_expr(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Lit(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::TableLit { .. }
    )
}

fn is_leaf_plan(p: &Plan) -> bool {
    matches!(p, Plan::SourceExpr(e) if is_leaf_expr(e))
}

fn push_expr_box(b: &mut Box<Expr>, stack: &mut Vec<DropNode>) {
    if !is_leaf_expr(b) {
        stack.push(DropNode::Expr(std::mem::replace(
            b.as_mut(),
            Expr::Lit(Literal::Unit),
        )));
    }
}

fn push_plan_box(b: &mut Box<Plan>, stack: &mut Vec<DropNode>) {
    if !is_leaf_plan(b) {
        stack.push(DropNode::Plan(std::mem::replace(
            b.as_mut(),
            Plan::SourceExpr(Box::new(Expr::Lit(Literal::Unit))),
        )));
    }
}

fn unit_expr_arc() -> Arc<Expr> {
    static UNIT_EXPR: OnceLock<Arc<Expr>> = OnceLock::new();
    Arc::clone(UNIT_EXPR.get_or_init(|| Arc::new(Expr::Lit(Literal::Unit))))
}

fn push_expr_children(expr: &mut Expr, stack: &mut Vec<DropNode>) {
    match expr {
        Expr::Lit(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::TableLit { .. } => {}
        Expr::LetE { bound, body, .. } => {
            push_expr_box(bound, stack);
            push_expr_box(body, stack);
        }
        Expr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            push_expr_box(cond, stack);
            push_expr_box(then_br, stack);
            push_expr_box(else_br, stack);
        }
        Expr::CaseE { scrut, arms } => {
            push_expr_box(scrut, stack);
            for arm in std::mem::take(arms) {
                if !is_leaf_expr(&arm.body) {
                    stack.push(DropNode::Expr(arm.body));
                }
            }
        }
        Expr::Lam { body, .. } => {
            let prev = std::mem::replace(body, unit_expr_arc());
            if let Ok(inner) = Arc::try_unwrap(prev)
                && !is_leaf_expr(&inner)
            {
                stack.push(DropNode::Expr(inner));
            }
        }
        Expr::Proj { tup: body, .. } | Expr::Fail(body) => {
            push_expr_box(body, stack);
        }
        Expr::App { fn_expr, args } => {
            push_expr_box(fn_expr, stack);
            for a in std::mem::take(args) {
                if !is_leaf_expr(&a) {
                    stack.push(DropNode::Expr(a));
                }
            }
        }
        Expr::Call { args, .. }
        | Expr::Jump { args, .. }
        | Expr::Tuple(args)
        | Expr::Ctor { args, .. }
        | Expr::Prim { args, .. }
        | Expr::Host { args, .. } => {
            for a in std::mem::take(args) {
                if !is_leaf_expr(&a) {
                    stack.push(DropNode::Expr(a));
                }
            }
        }
        Expr::Join { rhs, body, .. } => {
            push_expr_box(rhs, stack);
            push_expr_box(body, stack);
        }
        Expr::Rel(plan) => {
            push_plan_box(plan, stack);
        }
        Expr::Stop { detail, .. } => {
            if let Some(d) = detail.take()
                && !is_leaf_expr(&d)
            {
                stack.push(DropNode::Expr(*d));
            }
        }
    }
}

fn push_plan_children(plan: &mut Plan, stack: &mut Vec<DropNode>) {
    match plan {
        Plan::SourceExpr(e) | Plan::SourceDB { cap: e, .. } => {
            push_expr_box(e, stack);
        }
        Plan::Select { input, .. }
        | Plan::Drop { input, .. }
        | Plan::Rename { input, .. }
        | Plan::Derive { input, .. }
        | Plan::Filter { input, .. }
        | Plan::Distinct { input, .. }
        | Plan::Sort { input, .. }
        | Plan::Limit { input, .. }
        | Plan::GroupBy { input, .. }
        | Plan::Summarize { input, .. }
        | Plan::SuppressSmallGroups { input, .. }
        | Plan::Window { input, .. }
        | Plan::FillGaps { input, .. }
        | Plan::PivotWider { input, .. }
        | Plan::Crosstab { input, .. }
        | Plan::Redact { input, .. } => {
            push_plan_box(input, stack);
        }
        Plan::Join { left, right, .. } | Plan::Union { left, right } => {
            push_plan_box(left, stack);
            push_plan_box(right, stack);
        }
        Plan::Pseudonymize { input, secret, .. } => {
            push_plan_box(input, stack);
            push_expr_box(secret, stack);
        }
    }
}

fn drain_drop_stack(mut stack: Vec<DropNode>) {
    while let Some(mut node) = stack.pop() {
        match &mut node {
            DropNode::Expr(e) => push_expr_children(e, &mut stack),
            DropNode::Plan(p) => push_plan_children(p, &mut stack),
        }
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        if is_leaf_expr(self) {
            return;
        }
        let mut stack = Vec::new();
        push_expr_children(self, &mut stack);
        drain_drop_stack(stack);
    }
}

impl Drop for Plan {
    fn drop(&mut self) {
        if is_leaf_plan(self) {
            return;
        }
        let mut stack = Vec::new();
        push_plan_children(self, &mut stack);
        drain_drop_stack(stack);
    }
}
