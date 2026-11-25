//! Compiled vectorized row-expression bytecode engine (eliminating the UDF cliff).
//!
//! Compiles both Core IR [`RowExpr`] and Phase 2 [`ExecRowExpr`] into flat
//! register-based bytecode ([`RowProgram`]), automatically inlining non-recursive
//! pure user functions directly into columnar vector instructions!
//!
//! Guarantees exact earliest-active-lane `Bug` semantics even across nested `if`,
//! `coalesce`, and short-circuit `and`/`or` branches.

use std::collections::{HashMap, HashSet};

use crate::core::bigint::BigInt;
use crate::core::syntax::{BugKind, ColSpec, Expr, Float64, Ident, PrimOp, Program, RowExpr};
use crate::formats::time::{
    date_trunc_date, date_trunc_timestamp_duration, date_trunc_timestamp_unit,
    format_timestamp_in_tz, local_date_in_tz, months_between_days, round_decimal_bigint,
};
use crate::oracle::eval::{PrimResult, eval_literal, eval_prim_op};
use crate::oracle::value::{Bug, Val, float_order_key, render_decimal};
use crate::runtime::exec::{
    bigint_to_slice_bound, clamp_decimal_val, clamp_float_val, clamp_int_bigint, eval_in_list,
    round_to_float_val, slice_text, try_parse_date_text, try_parse_decimal_text,
    try_parse_float_text, try_parse_int_text,
};
use crate::runtime::ir::{ExecExpr, ExecPrimOp, ExecProgram, ExecRowExpr};
use crate::vm::batch::{Batch, Column, ColumnData, NullBitmap};
use crate::vm::decimal::{
    dec_add, dec_bool_to_dec, dec_div_euclid, dec_int_to_dec, dec_mul_euclid, dec_neg, dec_sub,
};

const MAX_INLINE_DEPTH: usize = 8;
const MAX_INLINE_NODES: usize = 256;

/// Runtime failure from evaluating a row expression on a batch.
#[derive(Clone, Debug)]
pub enum RowEvalErr {
    /// Deterministic trap at a specific row lane inside the batch.
    Stopped { lane: usize, bug: Bug },
    /// Non-stop runtime / type failure.
    Failed(String),
}

impl RowEvalErr {
    #[must_use]
    pub fn earliest(a: Self, b: Self) -> Self {
        match (a, b) {
            (Self::Stopped { lane: la, bug: ba }, Self::Stopped { lane: lb, bug: bb }) => {
                if la <= lb {
                    Self::Stopped { lane: la, bug: ba }
                } else {
                    Self::Stopped { lane: lb, bug: bb }
                }
            }
            (Self::Stopped { lane, bug }, Self::Failed(_))
            | (Self::Failed(_), Self::Stopped { lane, bug }) => Self::Stopped { lane, bug },
            (Self::Failed(m), Self::Failed(_)) => Self::Failed(m),
        }
    }
}

/// Register-based vectorized row bytecode program.
#[derive(Clone, Debug)]
pub struct RowProgram {
    pub num_regs: usize,
    pub instrs: Vec<RowInstr>,
    pub result_reg: usize,
}

#[derive(Clone, Debug)]
pub enum RowInstr {
    LoadLit {
        dst: usize,
        val: Val,
    },
    LoadCol {
        dst: usize,
        name: Ident,
    },
    LoadOuter {
        dst: usize,
        name: Ident,
    },
    LoadConst {
        dst: usize,
        name: Ident,
    },
    Copy {
        dst: usize,
        src: usize,
    },
    Prim {
        dst: usize,
        op: Box<ExecPrimOp>,
        args: Vec<usize>,
    },
    If {
        dst: usize,
        cond_reg: usize,
        then_prog: Box<RowProgram>,
        else_prog: Box<RowProgram>,
    },
    Coalesce {
        dst: usize,
        opt_reg: usize,
        default_prog: Box<RowProgram>,
    },
    ShortAnd {
        dst: usize,
        lhs_reg: usize,
        rhs_prog: Box<RowProgram>,
    },
    ShortOr {
        dst: usize,
        lhs_reg: usize,
        rhs_prog: Box<RowProgram>,
    },
    CallPureFallback {
        dst: usize,
        fn_name: Ident,
        args: Vec<usize>,
    },
}

/// Register payload during batch execution.
#[derive(Clone, Debug)]
pub enum RegVal {
    Broadcast(Val),
    Bool(Vec<u8>),
    Int(Vec<i64>),
    Decimal(Vec<i128>),
    Float(Vec<u64>),
    Date(Vec<i64>),
    Timestamp(Vec<i64>),
    Duration(Vec<i64>),
    Text {
        offsets: Vec<usize>,
        data: Vec<u8>,
    },
    Bytes {
        offsets: Vec<usize>,
        data: Vec<u8>,
    },
    Nullable {
        data: Box<ColumnData>,
        validity: NullBitmap,
    },
    Generic(Vec<Val>),
}

impl RegVal {
    #[must_use]
    pub fn from_column(col: &Column) -> Self {
        if let Some(bm) = &col.validity {
            return Self::Nullable {
                data: Box::new(col.data.clone()),
                validity: bm.clone(),
            };
        }
        match &col.data {
            ColumnData::Unit(n) => Self::Generic(vec![Val::Unit; *n]),
            ColumnData::Bool(v) => Self::Bool(v.clone()),
            ColumnData::Int(v) => Self::Int(v.clone()),
            ColumnData::Decimal(v) => Self::Decimal(v.clone()),
            ColumnData::Float(v) => Self::Float(v.clone()),
            ColumnData::Date(v) => Self::Date(v.clone()),
            ColumnData::Timestamp(v) => Self::Timestamp(v.clone()),
            ColumnData::Duration(v) => Self::Duration(v.clone()),
            ColumnData::Text { offsets, data } => Self::Text {
                offsets: offsets.clone(),
                data: data.clone(),
            },
            ColumnData::Bytes { offsets, data } => Self::Bytes {
                offsets: offsets.clone(),
                data: data.clone(),
            },
            ColumnData::Generic(v) => Self::Generic(v.clone()),
        }
    }

    #[must_use]
    pub fn get_val(&self, lane: usize) -> Val {
        match self {
            Self::Broadcast(v) => v.clone(),
            Self::Bool(v) => Val::Bool(v.get(lane).copied().unwrap_or(0) != 0),
            Self::Int(v) => Val::Int(BigInt::from(v.get(lane).copied().unwrap_or(0))),
            Self::Decimal(v) => Val::Decimal(BigInt::from(v.get(lane).copied().unwrap_or(0))),
            Self::Float(v) => Val::Float(Float64::from_bits(v.get(lane).copied().unwrap_or(0))),
            Self::Date(v) => Val::Date(BigInt::from(v.get(lane).copied().unwrap_or(0))),
            Self::Timestamp(v) => Val::Timestamp(BigInt::from(v.get(lane).copied().unwrap_or(0))),
            Self::Duration(v) => Val::Duration(BigInt::from(v.get(lane).copied().unwrap_or(0))),
            Self::Text { offsets, data } => {
                let s = offsets
                    .get(lane)
                    .zip(offsets.get(lane + 1))
                    .and_then(|(&a, &b)| data.get(a..b))
                    .and_then(|bs| std::str::from_utf8(bs).ok())
                    .unwrap_or("");
                Val::Text(s.to_string())
            }
            Self::Bytes { offsets, data } => {
                let bs = offsets
                    .get(lane)
                    .zip(offsets.get(lane + 1))
                    .and_then(|(&a, &b)| data.get(a..b))
                    .unwrap_or(&[]);
                Val::Bytes(bs.to_vec())
            }
            Self::Nullable { data, validity } => {
                if validity.is_valid(lane) {
                    Val::OptSome(Box::new(data.get_raw_val(lane)))
                } else {
                    Val::OptNone
                }
            }
            Self::Generic(v) => v.get(lane).cloned().unwrap_or(Val::Unit),
        }
    }

    /// Materialize this register into a [`Column`] of length `batch_len`.
    #[must_use]
    pub fn into_column(self, spec: ColSpec, batch_len: usize) -> Column {
        match self {
            Self::Bool(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Bool(v),
                validity: None,
            },
            Self::Int(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Int(v),
                validity: None,
            },
            Self::Decimal(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Decimal(v),
                validity: None,
            },
            Self::Float(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Float(v),
                validity: None,
            },
            Self::Date(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Date(v),
                validity: None,
            },
            Self::Timestamp(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Timestamp(v),
                validity: None,
            },
            Self::Duration(v) if v.len() == batch_len => Column {
                spec,
                data: ColumnData::Duration(v),
                validity: None,
            },
            Self::Text { offsets, data } if offsets.len() == batch_len + 1 => Column {
                spec,
                data: ColumnData::Text { offsets, data },
                validity: None,
            },
            Self::Bytes { offsets, data } if offsets.len() == batch_len + 1 => Column {
                spec,
                data: ColumnData::Bytes { offsets, data },
                validity: None,
            },
            Self::Nullable { data, validity } if data.len() == batch_len => Column {
                spec,
                data: *data,
                validity: Some(validity),
            },
            Self::Broadcast(v) => Column::from_vals(spec, &vec![v; batch_len]),
            Self::Generic(v) if v.len() == batch_len => Column::from_vals(spec, &v),
            other => {
                let vals: Vec<Val> = (0..batch_len).map(|i| other.get_val(i)).collect();
                Column::from_vals(spec, &vals)
            }
        }
    }
}

// ===========================================================================
// Compilation from Core IR `RowExpr` & Phase 2 `ExecRowExpr` (with Pure UDF Inlining)
// ===========================================================================

struct Compiler {
    next_reg: usize,
    instrs: Vec<RowInstr>,
}

impl Compiler {
    fn new(start_reg: usize) -> Self {
        Self {
            next_reg: start_reg,
            instrs: Vec::new(),
        }
    }

    fn alloc(&mut self) -> usize {
        let r = self.next_reg;
        self.next_reg += 1;
        r
    }
}

fn core_expr_inlinable_size(e: &Expr, budget: usize) -> Option<usize> {
    if budget == 0 {
        return None;
    }
    match e {
        Expr::Lit(_) | Expr::Var(_) | Expr::ConstRef(_) => Some(1),
        Expr::LetE { bound, body, .. } => {
            let s1 = core_expr_inlinable_size(bound, budget - 1)?;
            let s2 = core_expr_inlinable_size(body, budget - 1 - s1)?;
            Some(1 + s1 + s2)
        }
        Expr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let s1 = core_expr_inlinable_size(cond, budget - 1)?;
            let s2 = core_expr_inlinable_size(then_br, budget - 1 - s1)?;
            let s3 = core_expr_inlinable_size(else_br, budget - 1 - s1 - s2)?;
            Some(1 + s1 + s2 + s3)
        }
        Expr::Prim { args, .. } | Expr::Call { args, .. } => {
            let mut used = 1;
            for a in args {
                let s = core_expr_inlinable_size(a, budget.checked_sub(used)?)?;
                used += s;
            }
            Some(used)
        }
        _ => None,
    }
}

fn exec_expr_inlinable_size(e: &ExecExpr, budget: usize) -> Option<usize> {
    if budget == 0 {
        return None;
    }
    match e {
        ExecExpr::Lit(_) | ExecExpr::Var(_) | ExecExpr::ConstRef(_) => Some(1),
        ExecExpr::LetE { bound, body, .. } => {
            let s1 = exec_expr_inlinable_size(bound, budget - 1)?;
            let s2 = exec_expr_inlinable_size(body, budget - 1 - s1)?;
            Some(1 + s1 + s2)
        }
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let s1 = exec_expr_inlinable_size(cond, budget - 1)?;
            let s2 = exec_expr_inlinable_size(then_br, budget - 1 - s1)?;
            let s3 = exec_expr_inlinable_size(else_br, budget - 1 - s1 - s2)?;
            Some(1 + s1 + s2 + s3)
        }
        ExecExpr::Prim { args, .. } | ExecExpr::Call { args, .. } => {
            let mut used = 1;
            for a in args {
                let s = exec_expr_inlinable_size(a, budget.checked_sub(used)?)?;
                used += s;
            }
            Some(used)
        }
        _ => None,
    }
}

/// Compile a Core IR [`RowExpr`] into a flat [`RowProgram`], inlining non-recursive pure UDFs.
#[must_use]
pub fn compile_core_row_expr(re: &RowExpr, prog: &Program) -> RowProgram {
    let mut comp = Compiler::new(0);
    let mut stack = HashSet::new();
    let result_reg = compile_core_re(re, prog, &mut comp, &mut stack);
    RowProgram {
        num_regs: comp.next_reg,
        instrs: comp.instrs,
        result_reg,
    }
}

fn compile_core_re(
    re: &RowExpr,
    prog: &Program,
    comp: &mut Compiler,
    inlining: &mut HashSet<Ident>,
) -> usize {
    match re {
        RowExpr::Lit(l) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadLit {
                dst,
                val: eval_literal(l),
            });
            dst
        }
        RowExpr::Col(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadCol {
                dst,
                name: name.clone(),
            });
            dst
        }
        RowExpr::OuterVar(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadOuter {
                dst,
                name: name.clone(),
            });
            dst
        }
        RowExpr::ConstRef(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadConst {
                dst,
                name: name.clone(),
            });
            dst
        }
        RowExpr::Prim { op, args } => {
            // Note: In Core IR v0.1 (`Eval.lean`), ALL `PrimOp`s (including `AndBool`/`OrBool`)
            // evaluate their arguments eagerly left-to-right!
            let arg_regs: Vec<usize> = args
                .iter()
                .map(|a| compile_core_re(a, prog, comp, inlining))
                .collect();
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::Prim {
                dst,
                op: Box::new(ExecPrimOp::Core(op.clone())),
                args: arg_regs,
            });
            dst
        }
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let cond_reg = compile_core_re(cond, prog, comp, inlining);
            let mut then_comp = Compiler::new(comp.next_reg);
            let then_res = compile_core_re(then_br, prog, &mut then_comp, inlining);
            let mut else_comp = Compiler::new(comp.next_reg);
            let else_res = compile_core_re(else_br, prog, &mut else_comp, inlining);
            comp.next_reg = then_comp.next_reg.max(else_comp.next_reg);
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::If {
                dst,
                cond_reg,
                then_prog: Box::new(RowProgram {
                    num_regs: then_comp.next_reg,
                    instrs: then_comp.instrs,
                    result_reg: then_res,
                }),
                else_prog: Box::new(RowProgram {
                    num_regs: else_comp.next_reg,
                    instrs: else_comp.instrs,
                    result_reg: else_res,
                }),
            });
            dst
        }
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            let opt_reg = compile_core_re(opt_expr, prog, comp, inlining);
            let mut def_comp = Compiler::new(comp.next_reg);
            let def_res = compile_core_re(default_expr, prog, &mut def_comp, inlining);
            comp.next_reg = def_comp.next_reg;
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::Coalesce {
                dst,
                opt_reg,
                default_prog: Box::new(RowProgram {
                    num_regs: def_comp.next_reg,
                    instrs: def_comp.instrs,
                    result_reg: def_res,
                }),
            });
            dst
        }
        RowExpr::CallPure { fn_name, args } => {
            let arg_regs: Vec<usize> = args
                .iter()
                .map(|a| compile_core_re(a, prog, comp, inlining))
                .collect();
            if inlining.len() < MAX_INLINE_DEPTH
                && !inlining.contains(fn_name)
                && let Some(f_decl) = prog.find_fun(fn_name)
                && f_decl.params.len() == arg_regs.len()
                && core_expr_inlinable_size(&f_decl.body, MAX_INLINE_NODES).is_some()
            {
                let mut var_regs = HashMap::with_capacity(f_decl.params.len());
                for ((p, _), &r) in f_decl.params.iter().zip(&arg_regs) {
                    var_regs.insert(p.clone(), r);
                }
                inlining.insert(fn_name.clone());
                let res =
                    compile_inlined_core_expr(&f_decl.body, prog, &mut var_regs, comp, inlining);
                inlining.remove(fn_name);
                if let Some(r) = res {
                    return r;
                }
            }
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::CallPureFallback {
                dst,
                fn_name: fn_name.clone(),
                args: arg_regs,
            });
            dst
        }
    }
}

fn compile_inlined_core_expr(
    e: &Expr,
    prog: &Program,
    vars: &mut HashMap<Ident, usize>,
    comp: &mut Compiler,
    inlining: &mut HashSet<Ident>,
) -> Option<usize> {
    match e {
        Expr::Lit(l) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadLit {
                dst,
                val: eval_literal(l),
            });
            Some(dst)
        }
        Expr::Var(name) => vars.get(name).copied(),
        Expr::ConstRef(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadConst {
                dst,
                name: name.clone(),
            });
            Some(dst)
        }
        Expr::LetE {
            name, bound, body, ..
        } => {
            let b_reg = compile_inlined_core_expr(bound, prog, vars, comp, inlining)?;
            let prev = vars.insert(name.clone(), b_reg);
            let res = compile_inlined_core_expr(body, prog, vars, comp, inlining);
            match prev {
                Some(old) => {
                    vars.insert(name.clone(), old);
                }
                None => {
                    vars.remove(name);
                }
            }
            res
        }
        Expr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let cond_reg = compile_inlined_core_expr(cond, prog, vars, comp, inlining)?;
            let mut then_comp = Compiler::new(comp.next_reg);
            let then_res =
                compile_inlined_core_expr(then_br, prog, vars, &mut then_comp, inlining)?;
            let mut else_comp = Compiler::new(comp.next_reg);
            let else_res =
                compile_inlined_core_expr(else_br, prog, vars, &mut else_comp, inlining)?;
            comp.next_reg = then_comp.next_reg.max(else_comp.next_reg);
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::If {
                dst,
                cond_reg,
                then_prog: Box::new(RowProgram {
                    num_regs: then_comp.next_reg,
                    instrs: then_comp.instrs,
                    result_reg: then_res,
                }),
                else_prog: Box::new(RowProgram {
                    num_regs: else_comp.next_reg,
                    instrs: else_comp.instrs,
                    result_reg: else_res,
                }),
            });
            Some(dst)
        }
        Expr::Prim { op, args } => {
            let mut arg_regs = Vec::with_capacity(args.len());
            for a in args {
                arg_regs.push(compile_inlined_core_expr(a, prog, vars, comp, inlining)?);
            }
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::Prim {
                dst,
                op: Box::new(ExecPrimOp::Core(op.clone())),
                args: arg_regs,
            });
            Some(dst)
        }
        Expr::Call { fn_name, args } => {
            let mut arg_regs = Vec::with_capacity(args.len());
            for a in args {
                arg_regs.push(compile_inlined_core_expr(a, prog, vars, comp, inlining)?);
            }
            if inlining.len() < MAX_INLINE_DEPTH
                && !inlining.contains(fn_name)
                && let Some(f_decl) = prog.find_fun(fn_name)
                && f_decl.params.len() == arg_regs.len()
                && core_expr_inlinable_size(&f_decl.body, MAX_INLINE_NODES).is_some()
            {
                let mut child_vars = HashMap::with_capacity(f_decl.params.len());
                for ((p, _), &r) in f_decl.params.iter().zip(&arg_regs) {
                    child_vars.insert(p.clone(), r);
                }
                inlining.insert(fn_name.clone());
                let res =
                    compile_inlined_core_expr(&f_decl.body, prog, &mut child_vars, comp, inlining);
                inlining.remove(fn_name);
                if let Some(r) = res {
                    return Some(r);
                }
            }
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::CallPureFallback {
                dst,
                fn_name: fn_name.clone(),
                args: arg_regs,
            });
            Some(dst)
        }
        _ => None,
    }
}

/// Compile a Phase 2 [`ExecRowExpr`] into a flat [`RowProgram`], inlining non-recursive pure UDFs.
#[must_use]
pub fn compile_exec_row_expr(re: &ExecRowExpr, prog: &ExecProgram) -> RowProgram {
    let mut comp = Compiler::new(0);
    let mut stack = HashSet::new();
    let result_reg = compile_exec_re(re, prog, &mut comp, &mut stack);
    RowProgram {
        num_regs: comp.next_reg,
        instrs: comp.instrs,
        result_reg,
    }
}

fn compile_exec_re(
    re: &ExecRowExpr,
    prog: &ExecProgram,
    comp: &mut Compiler,
    inlining: &mut HashSet<Ident>,
) -> usize {
    match re {
        ExecRowExpr::Lit(l) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadLit {
                dst,
                val: eval_literal(l),
            });
            dst
        }
        ExecRowExpr::Col(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadCol {
                dst,
                name: name.clone(),
            });
            dst
        }
        ExecRowExpr::OuterVar(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadOuter {
                dst,
                name: name.clone(),
            });
            dst
        }
        ExecRowExpr::ConstRef(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadConst {
                dst,
                name: name.clone(),
            });
            dst
        }
        ExecRowExpr::Prim { op, args } => {
            if matches!(op, ExecPrimOp::Core(PrimOp::AndBool)) && args.len() == 2 {
                let lhs_reg = compile_exec_re(&args[0], prog, comp, inlining);
                let mut rhs_comp = Compiler::new(comp.next_reg);
                let rhs_res = compile_exec_re(&args[1], prog, &mut rhs_comp, inlining);
                comp.next_reg = rhs_comp.next_reg;
                let dst = comp.alloc();
                comp.instrs.push(RowInstr::ShortAnd {
                    dst,
                    lhs_reg,
                    rhs_prog: Box::new(RowProgram {
                        num_regs: rhs_comp.next_reg,
                        instrs: rhs_comp.instrs,
                        result_reg: rhs_res,
                    }),
                });
                return dst;
            }
            if matches!(op, ExecPrimOp::Core(PrimOp::OrBool)) && args.len() == 2 {
                let lhs_reg = compile_exec_re(&args[0], prog, comp, inlining);
                let mut rhs_comp = Compiler::new(comp.next_reg);
                let rhs_res = compile_exec_re(&args[1], prog, &mut rhs_comp, inlining);
                comp.next_reg = rhs_comp.next_reg;
                let dst = comp.alloc();
                comp.instrs.push(RowInstr::ShortOr {
                    dst,
                    lhs_reg,
                    rhs_prog: Box::new(RowProgram {
                        num_regs: rhs_comp.next_reg,
                        instrs: rhs_comp.instrs,
                        result_reg: rhs_res,
                    }),
                });
                return dst;
            }
            let arg_regs: Vec<usize> = args
                .iter()
                .map(|a| compile_exec_re(a, prog, comp, inlining))
                .collect();
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::Prim {
                dst,
                op: Box::new(op.clone()),
                args: arg_regs,
            });
            dst
        }
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let cond_reg = compile_exec_re(cond, prog, comp, inlining);
            let mut then_comp = Compiler::new(comp.next_reg);
            let then_res = compile_exec_re(then_br, prog, &mut then_comp, inlining);
            let mut else_comp = Compiler::new(comp.next_reg);
            let else_res = compile_exec_re(else_br, prog, &mut else_comp, inlining);
            comp.next_reg = then_comp.next_reg.max(else_comp.next_reg);
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::If {
                dst,
                cond_reg,
                then_prog: Box::new(RowProgram {
                    num_regs: then_comp.next_reg,
                    instrs: then_comp.instrs,
                    result_reg: then_res,
                }),
                else_prog: Box::new(RowProgram {
                    num_regs: else_comp.next_reg,
                    instrs: else_comp.instrs,
                    result_reg: else_res,
                }),
            });
            dst
        }
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            let opt_reg = compile_exec_re(opt_expr, prog, comp, inlining);
            let mut def_comp = Compiler::new(comp.next_reg);
            let def_res = compile_exec_re(default_expr, prog, &mut def_comp, inlining);
            comp.next_reg = def_comp.next_reg;
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::Coalesce {
                dst,
                opt_reg,
                default_prog: Box::new(RowProgram {
                    num_regs: def_comp.next_reg,
                    instrs: def_comp.instrs,
                    result_reg: def_res,
                }),
            });
            dst
        }
        ExecRowExpr::CallPure { fn_name, args } => {
            let arg_regs: Vec<usize> = args
                .iter()
                .map(|a| compile_exec_re(a, prog, comp, inlining))
                .collect();
            if inlining.len() < MAX_INLINE_DEPTH
                && !inlining.contains(fn_name)
                && let Some(f_decl) = prog.find_fun(fn_name)
                && f_decl.params.len() == arg_regs.len()
                && exec_expr_inlinable_size(&f_decl.body, MAX_INLINE_NODES).is_some()
            {
                let mut var_regs = HashMap::with_capacity(f_decl.params.len());
                for ((p, _), &r) in f_decl.params.iter().zip(&arg_regs) {
                    var_regs.insert(p.clone(), r);
                }
                inlining.insert(fn_name.clone());
                let res =
                    compile_inlined_exec_expr(&f_decl.body, prog, &mut var_regs, comp, inlining);
                inlining.remove(fn_name);
                if let Some(r) = res {
                    return r;
                }
            }
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::CallPureFallback {
                dst,
                fn_name: fn_name.clone(),
                args: arg_regs,
            });
            dst
        }
    }
}

fn compile_inlined_exec_expr(
    e: &ExecExpr,
    prog: &ExecProgram,
    vars: &mut HashMap<Ident, usize>,
    comp: &mut Compiler,
    inlining: &mut HashSet<Ident>,
) -> Option<usize> {
    match e {
        ExecExpr::Lit(l) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadLit {
                dst,
                val: eval_literal(l),
            });
            Some(dst)
        }
        ExecExpr::Var(name) => vars.get(name).copied(),
        ExecExpr::ConstRef(name) => {
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::LoadConst {
                dst,
                name: name.clone(),
            });
            Some(dst)
        }
        ExecExpr::LetE {
            name, bound, body, ..
        } => {
            let b_reg = compile_inlined_exec_expr(bound, prog, vars, comp, inlining)?;
            let prev = vars.insert(name.clone(), b_reg);
            let res = compile_inlined_exec_expr(body, prog, vars, comp, inlining);
            match prev {
                Some(old) => {
                    vars.insert(name.clone(), old);
                }
                None => {
                    vars.remove(name);
                }
            }
            res
        }
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let cond_reg = compile_inlined_exec_expr(cond, prog, vars, comp, inlining)?;
            let mut then_comp = Compiler::new(comp.next_reg);
            let then_res =
                compile_inlined_exec_expr(then_br, prog, vars, &mut then_comp, inlining)?;
            let mut else_comp = Compiler::new(comp.next_reg);
            let else_res =
                compile_inlined_exec_expr(else_br, prog, vars, &mut else_comp, inlining)?;
            comp.next_reg = then_comp.next_reg.max(else_comp.next_reg);
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::If {
                dst,
                cond_reg,
                then_prog: Box::new(RowProgram {
                    num_regs: then_comp.next_reg,
                    instrs: then_comp.instrs,
                    result_reg: then_res,
                }),
                else_prog: Box::new(RowProgram {
                    num_regs: else_comp.next_reg,
                    instrs: else_comp.instrs,
                    result_reg: else_res,
                }),
            });
            Some(dst)
        }
        ExecExpr::Prim { op, args } => {
            let mut arg_regs = Vec::with_capacity(args.len());
            for a in args {
                arg_regs.push(compile_inlined_exec_expr(a, prog, vars, comp, inlining)?);
            }
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::Prim {
                dst,
                op: Box::new(op.clone()),
                args: arg_regs,
            });
            Some(dst)
        }
        ExecExpr::Call { fn_name, args } => {
            let mut arg_regs = Vec::with_capacity(args.len());
            for a in args {
                arg_regs.push(compile_inlined_exec_expr(a, prog, vars, comp, inlining)?);
            }
            if inlining.len() < MAX_INLINE_DEPTH
                && !inlining.contains(fn_name)
                && let Some(f_decl) = prog.find_fun(fn_name)
                && f_decl.params.len() == arg_regs.len()
                && exec_expr_inlinable_size(&f_decl.body, MAX_INLINE_NODES).is_some()
            {
                let mut child_vars = HashMap::with_capacity(f_decl.params.len());
                for ((p, _), &r) in f_decl.params.iter().zip(&arg_regs) {
                    child_vars.insert(p.clone(), r);
                }
                inlining.insert(fn_name.clone());
                let res =
                    compile_inlined_exec_expr(&f_decl.body, prog, &mut child_vars, comp, inlining);
                inlining.remove(fn_name);
                if let Some(r) = res {
                    return Some(r);
                }
            }
            let dst = comp.alloc();
            comp.instrs.push(RowInstr::CallPureFallback {
                dst,
                fn_name: fn_name.clone(),
                args: arg_regs,
            });
            Some(dst)
        }
        _ => None,
    }
}

// ===========================================================================
// Vectorized Bytecode Execution Environment & Kernels
// ===========================================================================

/// External context needed while evaluating a compiled [`RowProgram`] over a [`Batch`].
pub trait RowEvalHost: Sync {
    fn lookup_outer(&self, name: &str) -> Option<Val>;
    fn lookup_const(&self, name: &str) -> Option<Val>;
    fn call_pure_fallback(&self, fn_name: &str, args: Vec<Val>) -> Result<Val, RowEvalErr>;
}

/// Execute a compiled [`RowProgram`] over the active lanes of `batch`.
pub fn eval_row_program(
    rp: &RowProgram,
    batch: &Batch,
    host: &dyn RowEvalHost,
) -> Result<RegVal, RowEvalErr> {
    let active = batch.active_indices();
    if active.is_empty() {
        return Ok(RegVal::Generic(vec![Val::Unit; batch.len]));
    }
    let mut regs = vec![RegVal::Broadcast(Val::Unit); rp.num_regs];
    exec_row_instrs(&rp.instrs, batch, &active, &mut regs, host)?;
    Ok(std::mem::replace(
        &mut regs[rp.result_reg],
        RegVal::Broadcast(Val::Unit),
    ))
}

fn exec_sub_program(
    rp: &RowProgram,
    batch: &Batch,
    active: &[u16],
    parent_regs: &[RegVal],
    host: &dyn RowEvalHost,
) -> Result<RegVal, RowEvalErr> {
    let mut regs = vec![RegVal::Broadcast(Val::Unit); rp.num_regs.max(parent_regs.len())];
    for (i, rv) in parent_regs.iter().enumerate() {
        regs[i] = rv.clone();
    }
    exec_row_instrs(&rp.instrs, batch, active, &mut regs, host)?;
    Ok(std::mem::replace(
        &mut regs[rp.result_reg],
        RegVal::Broadcast(Val::Unit),
    ))
}

fn exec_row_instrs(
    instrs: &[RowInstr],
    batch: &Batch,
    active: &[u16],
    regs: &mut [RegVal],
    host: &dyn RowEvalHost,
) -> Result<(), RowEvalErr> {
    if active.is_empty() {
        return Ok(());
    }
    let batch_len = batch.len;
    for instr in instrs {
        match instr {
            RowInstr::LoadLit { dst, val } => {
                regs[*dst] = RegVal::Broadcast(val.clone());
            }
            RowInstr::LoadCol { dst, name } => {
                let Some(ci) = batch.find_col_idx(name) else {
                    return Err(RowEvalErr::Failed(format!("unknown column `{name}`")));
                };
                regs[*dst] = RegVal::from_column(&batch.cols[ci]);
            }
            RowInstr::LoadOuter { dst, name } => {
                let Some(v) = host.lookup_outer(name) else {
                    return Err(RowEvalErr::Failed(format!(
                        "unknown outer variable `{name}`"
                    )));
                };
                regs[*dst] = RegVal::Broadcast(v);
            }
            RowInstr::LoadConst { dst, name } => {
                let Some(v) = host.lookup_const(name) else {
                    return Err(RowEvalErr::Failed(format!("unknown constant `{name}`")));
                };
                regs[*dst] = RegVal::Broadcast(v);
            }
            RowInstr::Copy { dst, src } => {
                regs[*dst] = regs[*src].clone();
            }
            RowInstr::Prim { dst, op, args } => {
                let out = eval_vec_prim(op, args, regs, batch_len, active)?;
                regs[*dst] = out;
            }
            RowInstr::If {
                dst,
                cond_reg,
                then_prog,
                else_prog,
            } => {
                let mut true_lanes = Vec::with_capacity(active.len());
                let mut false_lanes = Vec::with_capacity(active.len());
                split_bool_lanes(&regs[*cond_reg], active, &mut true_lanes, &mut false_lanes)?;

                let then_res = if !true_lanes.is_empty() {
                    Some(exec_sub_program(then_prog, batch, &true_lanes, regs, host))
                } else {
                    None
                };

                // Preserve exact earliest-lane trap order across the two branches!
                let else_lanes_eff: Vec<u16> = match &then_res {
                    Some(Err(RowEvalErr::Stopped { lane: t_lane, .. })) => false_lanes
                        .iter()
                        .copied()
                        .filter(|&l| usize::from(l) < *t_lane)
                        .collect(),
                    _ => false_lanes.clone(),
                };
                let else_res = if !else_lanes_eff.is_empty() {
                    Some(exec_sub_program(
                        else_prog,
                        batch,
                        &else_lanes_eff,
                        regs,
                        host,
                    ))
                } else {
                    None
                };

                match (then_res, else_res) {
                    (Some(Err(ea)), Some(Err(eb))) => return Err(RowEvalErr::earliest(ea, eb)),
                    (Some(Err(e)), _) | (_, Some(Err(e))) => return Err(e),
                    (Some(Ok(tv)), Some(Ok(ev))) => {
                        regs[*dst] =
                            merge_branch_regs(batch_len, &true_lanes, &tv, &false_lanes, &ev);
                    }
                    (Some(Ok(tv)), None) => regs[*dst] = tv,
                    (None, Some(Ok(ev))) => regs[*dst] = ev,
                    (None, None) => regs[*dst] = RegVal::Broadcast(Val::Unit),
                }
            }
            RowInstr::Coalesce {
                dst,
                opt_reg,
                default_prog,
            } => {
                let mut some_lanes = Vec::with_capacity(active.len());
                let mut none_lanes = Vec::with_capacity(active.len());
                let unwrapped_some = split_option_lanes(
                    &regs[*opt_reg],
                    batch_len,
                    active,
                    &mut some_lanes,
                    &mut none_lanes,
                )?;
                if none_lanes.is_empty() {
                    regs[*dst] = unwrapped_some;
                } else {
                    let def_val = exec_sub_program(default_prog, batch, &none_lanes, regs, host)?;
                    if some_lanes.is_empty() {
                        regs[*dst] = def_val;
                    } else {
                        regs[*dst] = merge_branch_regs(
                            batch_len,
                            &some_lanes,
                            &unwrapped_some,
                            &none_lanes,
                            &def_val,
                        );
                    }
                }
            }
            RowInstr::ShortAnd {
                dst,
                lhs_reg,
                rhs_prog,
            } => {
                let mut true_lanes = Vec::with_capacity(active.len());
                let mut false_lanes = Vec::with_capacity(active.len());
                split_bool_lanes(&regs[*lhs_reg], active, &mut true_lanes, &mut false_lanes)?;
                let mut out = vec![0u8; batch_len];
                if !true_lanes.is_empty() {
                    let rhs_val = exec_sub_program(rhs_prog, batch, &true_lanes, regs, host)?;
                    fill_bool_lanes(&rhs_val, &true_lanes, &mut out)?;
                }
                regs[*dst] = RegVal::Bool(out);
            }
            RowInstr::ShortOr {
                dst,
                lhs_reg,
                rhs_prog,
            } => {
                let mut true_lanes = Vec::with_capacity(active.len());
                let mut false_lanes = Vec::with_capacity(active.len());
                split_bool_lanes(&regs[*lhs_reg], active, &mut true_lanes, &mut false_lanes)?;
                let mut out = vec![0u8; batch_len];
                for &l in &true_lanes {
                    out[usize::from(l)] = 1;
                }
                if !false_lanes.is_empty() {
                    let rhs_val = exec_sub_program(rhs_prog, batch, &false_lanes, regs, host)?;
                    fill_bool_lanes(&rhs_val, &false_lanes, &mut out)?;
                }
                regs[*dst] = RegVal::Bool(out);
            }
            RowInstr::CallPureFallback { dst, fn_name, args } => {
                let mut out = vec![Val::Unit; batch_len];
                for &l_u16 in active {
                    let lane = usize::from(l_u16);
                    let mut vals = Vec::with_capacity(args.len());
                    for &ar in args {
                        vals.push(regs[ar].get_val(lane));
                    }
                    match host.call_pure_fallback(fn_name, vals) {
                        Ok(v) => out[lane] = v,
                        Err(RowEvalErr::Stopped { bug, .. }) => {
                            return Err(RowEvalErr::Stopped { lane, bug });
                        }
                        Err(RowEvalErr::Failed(m)) => return Err(RowEvalErr::Failed(m)),
                    }
                }
                regs[*dst] = RegVal::Generic(out);
            }
        }
    }
    Ok(())
}

fn split_bool_lanes(
    reg: &RegVal,
    active: &[u16],
    true_lanes: &mut Vec<u16>,
    false_lanes: &mut Vec<u16>,
) -> Result<(), RowEvalErr> {
    match reg {
        RegVal::Bool(bs) => {
            for &l in active {
                if bs[usize::from(l)] != 0 {
                    true_lanes.push(l);
                } else {
                    false_lanes.push(l);
                }
            }
            Ok(())
        }
        RegVal::Broadcast(Val::Bool(true)) => {
            true_lanes.extend_from_slice(active);
            Ok(())
        }
        RegVal::Broadcast(Val::Bool(false)) => {
            false_lanes.extend_from_slice(active);
            Ok(())
        }
        RegVal::Generic(vs) => {
            for &l in active {
                match vs.get(usize::from(l)) {
                    Some(Val::Bool(true)) => true_lanes.push(l),
                    Some(Val::Bool(false)) => false_lanes.push(l),
                    _ => return Err(RowEvalErr::Failed("expected Bool condition".to_string())),
                }
            }
            Ok(())
        }
        _ => Err(RowEvalErr::Failed("expected Bool condition".to_string())),
    }
}

fn fill_bool_lanes(reg: &RegVal, lanes: &[u16], out: &mut [u8]) -> Result<(), RowEvalErr> {
    match reg {
        RegVal::Bool(bs) => {
            for &l in lanes {
                let i = usize::from(l);
                out[i] = bs[i];
            }
            Ok(())
        }
        RegVal::Broadcast(Val::Bool(b)) => {
            let v = u8::from(*b);
            for &l in lanes {
                out[usize::from(l)] = v;
            }
            Ok(())
        }
        RegVal::Generic(vs) => {
            for &l in lanes {
                let i = usize::from(l);
                match vs.get(i) {
                    Some(Val::Bool(b)) => out[i] = u8::from(*b),
                    _ => return Err(RowEvalErr::Failed("expected Bool operand".to_string())),
                }
            }
            Ok(())
        }
        _ => Err(RowEvalErr::Failed("expected Bool operand".to_string())),
    }
}

fn split_option_lanes(
    reg: &RegVal,
    batch_len: usize,
    active: &[u16],
    some_lanes: &mut Vec<u16>,
    none_lanes: &mut Vec<u16>,
) -> Result<RegVal, RowEvalErr> {
    match reg {
        RegVal::Nullable { data, validity } => {
            for &l in active {
                if validity.is_valid(usize::from(l)) {
                    some_lanes.push(l);
                } else {
                    none_lanes.push(l);
                }
            }
            let unwrapped = match data.as_ref() {
                ColumnData::Bool(v) => RegVal::Bool(v.clone()),
                ColumnData::Int(v) => RegVal::Int(v.clone()),
                ColumnData::Decimal(v) => RegVal::Decimal(v.clone()),
                ColumnData::Float(v) => RegVal::Float(v.clone()),
                ColumnData::Date(v) => RegVal::Date(v.clone()),
                ColumnData::Timestamp(v) => RegVal::Timestamp(v.clone()),
                ColumnData::Duration(v) => RegVal::Duration(v.clone()),
                ColumnData::Text { offsets, data } => RegVal::Text {
                    offsets: offsets.clone(),
                    data: data.clone(),
                },
                ColumnData::Bytes { offsets, data } => RegVal::Bytes {
                    offsets: offsets.clone(),
                    data: data.clone(),
                },
                ColumnData::Unit(n) => RegVal::Generic(vec![Val::Unit; *n]),
                ColumnData::Generic(v) => RegVal::Generic(v.clone()),
            };
            Ok(unwrapped)
        }
        RegVal::Broadcast(Val::OptNone) => {
            none_lanes.extend_from_slice(active);
            Ok(RegVal::Broadcast(Val::Unit))
        }
        RegVal::Broadcast(Val::OptSome(inner)) => {
            some_lanes.extend_from_slice(active);
            Ok(RegVal::Broadcast(inner.as_ref().clone()))
        }
        RegVal::Generic(vs) => {
            let mut out = vec![Val::Unit; batch_len];
            for &l in active {
                let i = usize::from(l);
                match vs.get(i) {
                    Some(Val::OptNone) => none_lanes.push(l),
                    Some(Val::OptSome(inner)) => {
                        some_lanes.push(l);
                        out[i] = inner.as_ref().clone();
                    }
                    _ => return Err(RowEvalErr::Failed("coalesce on non-Option".to_string())),
                }
            }
            Ok(RegVal::Generic(out))
        }
        _ => Err(RowEvalErr::Failed("coalesce on non-Option".to_string())),
    }
}

fn merge_branch_regs(
    batch_len: usize,
    lanes_a: &[u16],
    reg_a: &RegVal,
    lanes_b: &[u16],
    reg_b: &RegVal,
) -> RegVal {
    // Fast typed merges for common numeric/bool outputs (zero Val boxing!).
    match (reg_a, reg_b) {
        (RegVal::Int(a), RegVal::Int(b)) => {
            let mut out = vec![0i64; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Int(out);
        }
        (RegVal::Int(a), RegVal::Broadcast(Val::Int(bv))) if bv.to_i64().is_some() => {
            let b_i = bv.to_i64().unwrap_or(0);
            let mut out = vec![0i64; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                out[usize::from(l)] = b_i;
            }
            return RegVal::Int(out);
        }
        (RegVal::Broadcast(Val::Int(av)), RegVal::Int(b)) if av.to_i64().is_some() => {
            let a_i = av.to_i64().unwrap_or(0);
            let mut out = vec![0i64; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = a_i;
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Int(out);
        }
        (RegVal::Broadcast(Val::Int(av)), RegVal::Broadcast(Val::Int(bv)))
            if av.to_i64().is_some() && bv.to_i64().is_some() =>
        {
            let a_i = av.to_i64().unwrap_or(0);
            let b_i = bv.to_i64().unwrap_or(0);
            let mut out = vec![0i64; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = a_i;
            }
            for &l in lanes_b {
                out[usize::from(l)] = b_i;
            }
            return RegVal::Int(out);
        }
        (RegVal::Decimal(a), RegVal::Decimal(b)) => {
            let mut out = vec![0i128; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Decimal(out);
        }
        (RegVal::Decimal(a), RegVal::Broadcast(Val::Decimal(bv))) if bv.to_i128().is_some() => {
            let b_d = bv.to_i128().unwrap_or(0);
            let mut out = vec![0i128; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                out[usize::from(l)] = b_d;
            }
            return RegVal::Decimal(out);
        }
        (RegVal::Broadcast(Val::Decimal(av)), RegVal::Decimal(b)) if av.to_i128().is_some() => {
            let a_d = av.to_i128().unwrap_or(0);
            let mut out = vec![0i128; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = a_d;
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Decimal(out);
        }
        (RegVal::Broadcast(Val::Decimal(av)), RegVal::Broadcast(Val::Decimal(bv)))
            if av.to_i128().is_some() && bv.to_i128().is_some() =>
        {
            let a_d = av.to_i128().unwrap_or(0);
            let b_d = bv.to_i128().unwrap_or(0);
            let mut out = vec![0i128; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = a_d;
            }
            for &l in lanes_b {
                out[usize::from(l)] = b_d;
            }
            return RegVal::Decimal(out);
        }
        (RegVal::Float(a), RegVal::Float(b)) => {
            let mut out = vec![0u64; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Float(out);
        }
        (RegVal::Float(a), RegVal::Broadcast(Val::Float(bf))) => {
            let mut out = vec![0u64; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                out[usize::from(l)] = bf.bits;
            }
            return RegVal::Float(out);
        }
        (RegVal::Broadcast(Val::Float(af)), RegVal::Float(b)) => {
            let mut out = vec![0u64; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = af.bits;
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Float(out);
        }
        (RegVal::Broadcast(Val::Float(af)), RegVal::Broadcast(Val::Float(bf))) => {
            let mut out = vec![0u64; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = af.bits;
            }
            for &l in lanes_b {
                out[usize::from(l)] = bf.bits;
            }
            return RegVal::Float(out);
        }
        (RegVal::Bool(a), RegVal::Bool(b)) => {
            let mut out = vec![0u8; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Bool(out);
        }
        (RegVal::Bool(a), RegVal::Broadcast(Val::Bool(bb))) => {
            let b_u = u8::from(*bb);
            let mut out = vec![0u8; batch_len];
            for &l in lanes_a {
                let i = usize::from(l);
                out[i] = a[i];
            }
            for &l in lanes_b {
                out[usize::from(l)] = b_u;
            }
            return RegVal::Bool(out);
        }
        (RegVal::Broadcast(Val::Bool(ab)), RegVal::Bool(b)) => {
            let a_u = u8::from(*ab);
            let mut out = vec![0u8; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = a_u;
            }
            for &l in lanes_b {
                let i = usize::from(l);
                out[i] = b[i];
            }
            return RegVal::Bool(out);
        }
        (RegVal::Broadcast(Val::Bool(ab)), RegVal::Broadcast(Val::Bool(bb))) => {
            let a_u = u8::from(*ab);
            let b_u = u8::from(*bb);
            let mut out = vec![0u8; batch_len];
            for &l in lanes_a {
                out[usize::from(l)] = a_u;
            }
            for &l in lanes_b {
                out[usize::from(l)] = b_u;
            }
            return RegVal::Bool(out);
        }
        _ => {}
    }

    let mut out = vec![Val::Unit; batch_len];
    for &l in lanes_a {
        let i = usize::from(l);
        out[i] = reg_a.get_val(i);
    }
    for &l in lanes_b {
        let i = usize::from(l);
        out[i] = reg_b.get_val(i);
    }
    RegVal::Generic(out)
}

// ===========================================================================
// Tight Vectorized Primitive Kernels (Zero-Boxing Fast Paths + Exact Fallback)
// ===========================================================================

fn eval_vec_prim(
    op: &ExecPrimOp,
    args: &[usize],
    regs: &[RegVal],
    batch_len: usize,
    active: &[u16],
) -> Result<RegVal, RowEvalErr> {
    // Constant folding when all inputs are Broadcast!
    if args
        .iter()
        .all(|&r| matches!(regs[r], RegVal::Broadcast(_)))
    {
        let vals: Vec<Val> = args.iter().map(|&r| regs[r].get_val(0)).collect();
        let lane = usize::from(active[0]);
        let v = eval_scalar_exec_prim(op, &vals, lane)?;
        return Ok(RegVal::Broadcast(v));
    }

    match (op, args) {
        // ---- Checked Int64 Arithmetic ----
        (ExecPrimOp::Core(PrimOp::AddInt), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i64(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    a.checked_add(b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Int(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::SubInt), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i64(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    a.checked_sub(b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Int(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::MulInt), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i64(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    a.checked_mul(b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Int(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::DivInt), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i64(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    if b == 0 {
                        return Err(RowEvalErr::Stopped {
                            lane,
                            bug: Bug {
                                kind: BugKind::DivByZero,
                                message: "integer division by zero".to_string(),
                            },
                        });
                    }
                    a.checked_div_euclid(b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Int(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::ModInt), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i64(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    if b == 0 {
                        return Err(RowEvalErr::Stopped {
                            lane,
                            bug: Bug {
                                kind: BugKind::DivByZero,
                                message: "integer modulo by zero".to_string(),
                            },
                        });
                    }
                    if a == i64::MIN && b == -1 {
                        return Ok(0);
                    }
                    a.checked_rem_euclid(b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Int(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::NegInt), &[ra]) => {
            if let RegVal::Int(vs) = &regs[ra] {
                let mut out = vec![0i64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = vs[i].checked_neg().ok_or_else(|| RowEvalErr::Stopped {
                        lane: i,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        },
                    })?;
                }
                return Ok(RegVal::Int(out));
            }
        }
        (ExecPrimOp::AbsInt, &[ra]) => {
            if let RegVal::Int(vs) = &regs[ra] {
                let mut out = vec![0i64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = vs[i].checked_abs().ok_or_else(|| RowEvalErr::Stopped {
                        lane: i,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 abs overflow".to_string(),
                        },
                    })?;
                }
                return Ok(RegVal::Int(out));
            }
        }

        // ---- Checked Fixed-Point Decimal (10^18, 128-bit zero-alloc) ----
        (ExecPrimOp::Core(PrimOp::AddDec), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i128(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    dec_add(a, b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Decimal(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::SubDec), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i128(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    dec_sub(a, b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Decimal(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::MulDec), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i128(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    dec_mul_euclid(a, b).ok_or_else(|| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal arithmetic overflow".to_string(),
                        },
                    })
                })?
            {
                return Ok(RegVal::Decimal(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::DivDec), &[ra, rb]) => {
            if let Some(res) =
                try_bin_i128(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    dec_div_euclid(a, b).map_err(|kind| RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind,
                            message: if kind == BugKind::DivByZero {
                                "decimal division by zero".to_string()
                            } else {
                                "Decimal arithmetic overflow".to_string()
                            },
                        },
                    })
                })?
            {
                return Ok(RegVal::Decimal(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::NegDec), &[ra]) => {
            if let RegVal::Decimal(vs) = &regs[ra] {
                let mut out = vec![0i128; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = dec_neg(vs[i]).ok_or_else(|| RowEvalErr::Stopped {
                        lane: i,
                        bug: Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal arithmetic overflow".to_string(),
                        },
                    })?;
                }
                return Ok(RegVal::Decimal(out));
            }
        }
        (ExecPrimOp::AbsDecimal, &[ra]) => {
            if let RegVal::Decimal(vs) = &regs[ra] {
                let mut out = vec![0i128; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = vs[i].abs();
                }
                return Ok(RegVal::Decimal(out));
            }
        }
        (ExecPrimOp::Core(PrimOp::IntToDec), &[ra]) => {
            if let RegVal::Int(vs) = &regs[ra] {
                let mut out = vec![0i128; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = dec_int_to_dec(vs[i]).ok_or_else(|| RowEvalErr::Stopped {
                        lane: i,
                        bug: Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal arithmetic overflow".to_string(),
                        },
                    })?;
                }
                return Ok(RegVal::Decimal(out));
            }
        }
        (ExecPrimOp::Core(PrimOp::BoolToDec), &[ra]) => {
            if let RegVal::Bool(vs) = &regs[ra] {
                let mut out = vec![0i128; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = dec_bool_to_dec(vs[i] != 0);
                }
                return Ok(RegVal::Decimal(out));
            }
        }

        // ---- Float64 Vector Arithmetic ----
        (ExecPrimOp::AddFloat, &[ra, rb]) => {
            if let Some(res) = try_bin_f64(&regs[ra], &regs[rb], batch_len, active, |a, b, _| {
                Ok(Float64::from_f64(a + b).bits)
            })? {
                return Ok(RegVal::Float(res));
            }
        }
        (ExecPrimOp::SubFloat, &[ra, rb]) => {
            if let Some(res) = try_bin_f64(&regs[ra], &regs[rb], batch_len, active, |a, b, _| {
                Ok(Float64::from_f64(a - b).bits)
            })? {
                return Ok(RegVal::Float(res));
            }
        }
        (ExecPrimOp::MulFloat, &[ra, rb]) => {
            if let Some(res) = try_bin_f64(&regs[ra], &regs[rb], batch_len, active, |a, b, _| {
                Ok(Float64::from_f64(a * b).bits)
            })? {
                return Ok(RegVal::Float(res));
            }
        }
        (ExecPrimOp::DivFloat, &[ra, rb]) => {
            if let Some(res) =
                try_bin_f64(&regs[ra], &regs[rb], batch_len, active, |a, b, lane| {
                    if b == 0.0 {
                        return Err(RowEvalErr::Stopped {
                            lane,
                            bug: Bug {
                                kind: BugKind::DivByZero,
                                message: "Float division by zero".to_string(),
                            },
                        });
                    }
                    Ok(Float64::from_f64(a / b).bits)
                })?
            {
                return Ok(RegVal::Float(res));
            }
        }
        (ExecPrimOp::NegFloat, &[ra]) => {
            if let RegVal::Float(vs) = &regs[ra] {
                let mut out = vec![0u64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = Float64::from_f64(-f64::from_bits(vs[i])).bits;
                }
                return Ok(RegVal::Float(out));
            }
        }
        (ExecPrimOp::AbsFloat, &[ra]) => {
            if let RegVal::Float(vs) = &regs[ra] {
                let mut out = vec![0u64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = Float64::from_f64(f64::from_bits(vs[i]).abs()).bits;
                }
                return Ok(RegVal::Float(out));
            }
        }
        (ExecPrimOp::IntToFloat, &[ra]) => {
            if let RegVal::Int(vs) = &regs[ra] {
                let mut out = vec![0u64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = Float64::from_f64(vs[i] as f64).bits;
                }
                return Ok(RegVal::Float(out));
            }
        }

        // ---- Boolean Logic ----
        (ExecPrimOp::Core(PrimOp::NotBool), &[ra]) => {
            if let RegVal::Bool(vs) = &regs[ra] {
                let mut out = vec![0u8; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = u8::from(vs[i] == 0);
                }
                return Ok(RegVal::Bool(out));
            }
        }
        (ExecPrimOp::Core(PrimOp::AndBool), &[ra, rb]) => {
            if let Some(res) = try_bin_bool(&regs[ra], &regs[rb], batch_len, active, |a, b| a & b) {
                return Ok(RegVal::Bool(res));
            }
        }
        (ExecPrimOp::Core(PrimOp::OrBool), &[ra, rb]) => {
            if let Some(res) = try_bin_bool(&regs[ra], &regs[rb], batch_len, active, |a, b| a | b) {
                return Ok(RegVal::Bool(res));
            }
        }

        // ---- Typed Vector Comparisons (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`) ----
        (
            ExecPrimOp::Core(
                cop @ (PrimOp::Eq | PrimOp::Ne | PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge),
            ),
            &[ra, rb],
        ) => {
            if let Some(res) = try_cmp_vec(cop, &regs[ra], &regs[rb], batch_len, active) {
                return Ok(RegVal::Bool(res));
            }
        }

        // ---- Option Helpers ----
        (ExecPrimOp::Core(PrimOp::IsSome), &[ra]) => {
            if let RegVal::Nullable { validity, .. } = &regs[ra] {
                let mut out = vec![0u8; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = u8::from(validity.is_valid(i));
                }
                return Ok(RegVal::Bool(out));
            }
        }
        (ExecPrimOp::Core(PrimOp::IsNone), &[ra]) => {
            if let RegVal::Nullable { validity, .. } = &regs[ra] {
                let mut out = vec![0u8; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = u8::from(!validity.is_valid(i));
                }
                return Ok(RegVal::Bool(out));
            }
        }
        (ExecPrimOp::Core(PrimOp::UnwrapBang), &[ra]) => {
            if let RegVal::Nullable { data, validity } = &regs[ra] {
                for &l in active {
                    let i = usize::from(l);
                    if !validity.is_valid(i) {
                        return Err(RowEvalErr::Stopped {
                            lane: i,
                            bug: Bug {
                                kind: BugKind::UnwrapNone,
                                message: "unwrapped none value".to_string(),
                            },
                        });
                    }
                }
                return Ok(RegVal::from_column(&Column {
                    spec: ColSpec::default(),
                    data: data.as_ref().clone(),
                    validity: None,
                }));
            }
        }
        (ExecPrimOp::LowerText, &[ra]) => {
            if let RegVal::Text { offsets, data } = &regs[ra] {
                let mut is_active = vec![false; batch_len];
                for &l in active {
                    is_active[usize::from(l)] = true;
                }
                let mut out_offsets = Vec::with_capacity(batch_len + 1);
                let mut out_data = Vec::with_capacity(data.len());
                out_offsets.push(0);
                for (i, &active_lane) in is_active.iter().enumerate() {
                    if active_lane
                        && let Ok(s) = std::str::from_utf8(&data[offsets[i]..offsets[i + 1]])
                    {
                        out_data.extend_from_slice(s.to_lowercase().as_bytes());
                    }
                    out_offsets.push(out_data.len());
                }
                return Ok(RegVal::Text {
                    offsets: out_offsets,
                    data: out_data,
                });
            }
        }
        (ExecPrimOp::UpperText, &[ra]) => {
            if let RegVal::Text { offsets, data } = &regs[ra] {
                let mut is_active = vec![false; batch_len];
                for &l in active {
                    is_active[usize::from(l)] = true;
                }
                let mut out_offsets = Vec::with_capacity(batch_len + 1);
                let mut out_data = Vec::with_capacity(data.len());
                out_offsets.push(0);
                for (i, &active_lane) in is_active.iter().enumerate() {
                    if active_lane
                        && let Ok(s) = std::str::from_utf8(&data[offsets[i]..offsets[i + 1]])
                    {
                        out_data.extend_from_slice(s.to_uppercase().as_bytes());
                    }
                    out_offsets.push(out_data.len());
                }
                return Ok(RegVal::Text {
                    offsets: out_offsets,
                    data: out_data,
                });
            }
        }
        (op_sw @ (ExecPrimOp::StartsWithText | ExecPrimOp::EndsWithText), &[ra, rb]) => {
            let is_starts = matches!(op_sw, ExecPrimOp::StartsWithText);
            match (&regs[ra], &regs[rb]) {
                (RegVal::Text { offsets, data }, RegVal::Broadcast(Val::Text(pat))) => {
                    let pb = pat.as_bytes();
                    let mut out = vec![0u8; batch_len];
                    for &l in active {
                        let i = usize::from(l);
                        let sb = &data[offsets[i]..offsets[i + 1]];
                        let m = if is_starts {
                            sb.starts_with(pb)
                        } else {
                            sb.ends_with(pb)
                        };
                        out[i] = u8::from(m);
                    }
                    return Ok(RegVal::Bool(out));
                }
                (
                    RegVal::Text {
                        offsets: oa,
                        data: da,
                    },
                    RegVal::Text {
                        offsets: ob,
                        data: db,
                    },
                ) => {
                    let mut out = vec![0u8; batch_len];
                    for &l in active {
                        let i = usize::from(l);
                        let sb = &da[oa[i]..oa[i + 1]];
                        let pb = &db[ob[i]..ob[i + 1]];
                        let m = if is_starts {
                            sb.starts_with(pb)
                        } else {
                            sb.ends_with(pb)
                        };
                        out[i] = u8::from(m);
                    }
                    return Ok(RegVal::Bool(out));
                }
                _ => {}
            }
        }
        (ExecPrimOp::ClampInt, &[ra, rb, rc]) => {
            if let (
                RegVal::Int(xs),
                RegVal::Broadcast(Val::Int(lo_b)),
                RegVal::Broadcast(Val::Int(hi_b)),
            ) = (&regs[ra], &regs[rb], &regs[rc])
            {
                if lo_b > hi_b {
                    if let Some(&l) = active.first() {
                        return Err(RowEvalErr::Stopped {
                            lane: usize::from(l),
                            bug: Bug {
                                kind: BugKind::OutsideBoundary,
                                message: format!(
                                    "DomainError: clamp bounds invalid ({lo_b} > {hi_b})"
                                ),
                            },
                        });
                    }
                    return Ok(RegVal::Int(vec![0i64; batch_len]));
                }
                if let (Some(lo), Some(hi)) = (lo_b.to_i64(), hi_b.to_i64()) {
                    let mut out = vec![0i64; batch_len];
                    for &l in active {
                        let i = usize::from(l);
                        out[i] = xs[i].clamp(lo, hi);
                    }
                    return Ok(RegVal::Int(out));
                }
            }
        }
        (ExecPrimOp::ClampFloat, &[ra, rb, rc]) => {
            if let (
                RegVal::Float(xs),
                RegVal::Broadcast(Val::Float(lo_v)),
                RegVal::Broadcast(Val::Float(hi_v)),
            ) = (&regs[ra], &regs[rb], &regs[rc])
            {
                let mut out = vec![0u64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    let res = clamp_float_val(Float64::from_bits(xs[i]), *lo_v, *hi_v)
                        .map_err(|bug| RowEvalErr::Stopped { lane: i, bug })?;
                    out[i] = res.bits;
                }
                return Ok(RegVal::Float(out));
            }
        }
        (ExecPrimOp::ClampDecimal, &[ra, rb, rc]) => {
            if let (
                RegVal::Decimal(xs),
                RegVal::Broadcast(Val::Decimal(lo_b)),
                RegVal::Broadcast(Val::Decimal(hi_b)),
            ) = (&regs[ra], &regs[rb], &regs[rc])
            {
                if lo_b > hi_b {
                    if let Some(&l) = active.first() {
                        return Err(RowEvalErr::Stopped {
                            lane: usize::from(l),
                            bug: Bug {
                                kind: BugKind::OutsideBoundary,
                                message: format!(
                                    "DomainError: clamp bounds invalid ({} > {})",
                                    render_decimal(lo_b),
                                    render_decimal(hi_b)
                                ),
                            },
                        });
                    }
                    return Ok(RegVal::Decimal(vec![0i128; batch_len]));
                }
                if let (Some(lo), Some(hi)) = (lo_b.to_i128(), hi_b.to_i128()) {
                    let mut out = vec![0i128; batch_len];
                    for &l in active {
                        let i = usize::from(l);
                        out[i] = xs[i].clamp(lo, hi);
                    }
                    return Ok(RegVal::Decimal(out));
                }
            }
        }
        (ExecPrimOp::RoundToFloat, &[ra, rb]) => {
            if let (RegVal::Float(xs), RegVal::Broadcast(Val::Float(step_v))) =
                (&regs[ra], &regs[rb])
            {
                let mut out = vec![0u64; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    let res = round_to_float_val(Float64::from_bits(xs[i]), *step_v)
                        .map_err(|bug| RowEvalErr::Stopped { lane: i, bug })?;
                    out[i] = res.bits;
                }
                return Ok(RegVal::Float(out));
            }
        }
        (ExecPrimOp::InList, &[ra, rb]) => {
            if let RegVal::Broadcast(Val::List(elems)) = &regs[rb] {
                if elems.is_empty() {
                    return Ok(RegVal::Bool(vec![0u8; batch_len]));
                }
                if let Some(res) = try_in_list_vec(&regs[ra], elems, batch_len, active) {
                    return Ok(RegVal::Bool(res));
                }
            }
        }
        _ => {}
    }

    // General exact per-lane fallback for Text, Date, Bytes, Generic, ADTs, Option(Option(T)), etc.
    let mut out = vec![Val::Unit; batch_len];
    let mut vals = Vec::with_capacity(args.len());
    for &l_u16 in active {
        let lane = usize::from(l_u16);
        vals.clear();
        for &ar in args {
            vals.push(regs[ar].get_val(lane));
        }
        out[lane] = eval_scalar_exec_prim(op, &vals, lane)?;
    }
    Ok(RegVal::Generic(out))
}

fn try_in_list_vec(
    ra: &RegVal,
    elems: &[Val],
    batch_len: usize,
    active: &[u16],
) -> Option<Vec<u8>> {
    match ra {
        RegVal::Int(xs) => {
            let targets: Option<Vec<i64>> = elems
                .iter()
                .map(|v| match v {
                    Val::Int(n) => n.to_i64(),
                    _ => None,
                })
                .collect();
            let targets = targets?;
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(targets.contains(&xs[i]));
            }
            Some(out)
        }
        RegVal::Date(xs) => {
            let targets: Option<Vec<i64>> = elems
                .iter()
                .map(|v| match v {
                    Val::Date(d) => d.to_i64(),
                    _ => None,
                })
                .collect();
            let targets = targets?;
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(targets.contains(&xs[i]));
            }
            Some(out)
        }
        RegVal::Bool(xs) => {
            let targets: Option<Vec<u8>> = elems
                .iter()
                .map(|v| match v {
                    Val::Bool(b) => Some(u8::from(*b)),
                    _ => None,
                })
                .collect();
            let targets = targets?;
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(targets.contains(&xs[i]));
            }
            Some(out)
        }
        RegVal::Text { offsets, data } => {
            let targets: Option<Vec<&[u8]>> = elems
                .iter()
                .map(|v| match v {
                    Val::Text(s) => Some(s.as_bytes()),
                    _ => None,
                })
                .collect();
            let targets = targets?;
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                let slice = &data[offsets[i]..offsets[i + 1]];
                out[i] = u8::from(targets.contains(&slice));
            }
            Some(out)
        }
        RegVal::Nullable { data, validity } => match data.as_ref() {
            ColumnData::Int(xs) => {
                let targets: Option<Vec<i64>> = elems
                    .iter()
                    .map(|v| match v {
                        Val::Int(n) => n.to_i64(),
                        _ => None,
                    })
                    .collect();
                let targets = targets?;
                let mut out = vec![0u8; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    out[i] = u8::from(validity.is_valid(i) && targets.contains(&xs[i]));
                }
                Some(out)
            }
            ColumnData::Text { offsets, data } => {
                let targets: Option<Vec<&[u8]>> = elems
                    .iter()
                    .map(|v| match v {
                        Val::Text(s) => Some(s.as_bytes()),
                        _ => None,
                    })
                    .collect();
                let targets = targets?;
                let mut out = vec![0u8; batch_len];
                for &l in active {
                    let i = usize::from(l);
                    let hit = validity.is_valid(i)
                        && targets.contains(&&data[offsets[i]..offsets[i + 1]]);
                    out[i] = u8::from(hit);
                }
                Some(out)
            }
            _ => None,
        },
        _ => None,
    }
}

fn try_bin_i64<F>(
    ra: &RegVal,
    rb: &RegVal,
    batch_len: usize,
    active: &[u16],
    f: F,
) -> Result<Option<Vec<i64>>, RowEvalErr>
where
    F: Fn(i64, i64, usize) -> Result<i64, RowEvalErr>,
{
    match (ra, rb) {
        (RegVal::Int(a), RegVal::Int(b)) => {
            let mut out = vec![0i64; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a[i], b[i], i)?;
            }
            Ok(Some(out))
        }
        (RegVal::Int(a), RegVal::Broadcast(Val::Int(bv))) => {
            let Some(b) = bv.to_i64() else {
                return Ok(None);
            };
            let mut out = vec![0i64; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a[i], b, i)?;
            }
            Ok(Some(out))
        }
        (RegVal::Broadcast(Val::Int(av)), RegVal::Int(b)) => {
            let Some(a) = av.to_i64() else {
                return Ok(None);
            };
            let mut out = vec![0i64; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a, b[i], i)?;
            }
            Ok(Some(out))
        }
        _ => Ok(None),
    }
}

fn try_bin_i128<F>(
    ra: &RegVal,
    rb: &RegVal,
    batch_len: usize,
    active: &[u16],
    f: F,
) -> Result<Option<Vec<i128>>, RowEvalErr>
where
    F: Fn(i128, i128, usize) -> Result<i128, RowEvalErr>,
{
    match (ra, rb) {
        (RegVal::Decimal(a), RegVal::Decimal(b)) => {
            let mut out = vec![0i128; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a[i], b[i], i)?;
            }
            Ok(Some(out))
        }
        (RegVal::Decimal(a), RegVal::Broadcast(Val::Decimal(bv))) => {
            let Some(b) = bv.to_i128() else {
                return Ok(None);
            };
            let mut out = vec![0i128; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a[i], b, i)?;
            }
            Ok(Some(out))
        }
        (RegVal::Broadcast(Val::Decimal(av)), RegVal::Decimal(b)) => {
            let Some(a) = av.to_i128() else {
                return Ok(None);
            };
            let mut out = vec![0i128; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a, b[i], i)?;
            }
            Ok(Some(out))
        }
        _ => Ok(None),
    }
}

fn try_bin_f64<F>(
    ra: &RegVal,
    rb: &RegVal,
    batch_len: usize,
    active: &[u16],
    f: F,
) -> Result<Option<Vec<u64>>, RowEvalErr>
where
    F: Fn(f64, f64, usize) -> Result<u64, RowEvalErr>,
{
    match (ra, rb) {
        (RegVal::Float(a), RegVal::Float(b)) => {
            let mut out = vec![0u64; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(f64::from_bits(a[i]), f64::from_bits(b[i]), i)?;
            }
            Ok(Some(out))
        }
        (RegVal::Float(a), RegVal::Broadcast(Val::Float(bv))) => {
            let b = bv.to_f64();
            let mut out = vec![0u64; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(f64::from_bits(a[i]), b, i)?;
            }
            Ok(Some(out))
        }
        (RegVal::Broadcast(Val::Float(av)), RegVal::Float(b)) => {
            let a = av.to_f64();
            let mut out = vec![0u64; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a, f64::from_bits(b[i]), i)?;
            }
            Ok(Some(out))
        }
        _ => Ok(None),
    }
}

fn try_bin_bool<F>(
    ra: &RegVal,
    rb: &RegVal,
    batch_len: usize,
    active: &[u16],
    f: F,
) -> Option<Vec<u8>>
where
    F: Fn(u8, u8) -> u8,
{
    match (ra, rb) {
        (RegVal::Bool(a), RegVal::Bool(b)) => {
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a[i], b[i]);
            }
            Some(out)
        }
        (RegVal::Bool(a), RegVal::Broadcast(Val::Bool(bv))) => {
            let b = u8::from(*bv);
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a[i], b);
            }
            Some(out)
        }
        (RegVal::Broadcast(Val::Bool(av)), RegVal::Bool(b)) => {
            let a = u8::from(*av);
            let mut out = vec![0u8; batch_len];
            for &l in active {
                let i = usize::from(l);
                out[i] = f(a, b[i]);
            }
            Some(out)
        }
        _ => None,
    }
}

#[inline]
fn cmp_ord_matches(op: &PrimOp, ord: std::cmp::Ordering) -> bool {
    match op {
        PrimOp::Eq => ord == std::cmp::Ordering::Equal,
        PrimOp::Ne => ord != std::cmp::Ordering::Equal,
        PrimOp::Lt => ord == std::cmp::Ordering::Less,
        PrimOp::Le => ord != std::cmp::Ordering::Greater,
        PrimOp::Gt => ord == std::cmp::Ordering::Greater,
        PrimOp::Ge => ord != std::cmp::Ordering::Less,
        _ => false,
    }
}

fn try_cmp_vec(
    op: &PrimOp,
    ra: &RegVal,
    rb: &RegVal,
    batch_len: usize,
    active: &[u16],
) -> Option<Vec<u8>> {
    let mut out = vec![0u8; batch_len];
    match (ra, rb) {
        (RegVal::Int(a), RegVal::Int(b))
        | (RegVal::Date(a), RegVal::Date(b))
        | (RegVal::Timestamp(a), RegVal::Timestamp(b))
        | (RegVal::Duration(a), RegVal::Duration(b)) => {
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a[i].cmp(&b[i])));
            }
            Some(out)
        }
        (RegVal::Int(a), RegVal::Broadcast(Val::Int(bv)))
        | (RegVal::Date(a), RegVal::Broadcast(Val::Date(bv)))
        | (RegVal::Timestamp(a), RegVal::Broadcast(Val::Timestamp(bv)))
        | (RegVal::Duration(a), RegVal::Broadcast(Val::Duration(bv))) => {
            let b = bv.to_i64()?;
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a[i].cmp(&b)));
            }
            Some(out)
        }
        (RegVal::Broadcast(Val::Int(av)), RegVal::Int(b))
        | (RegVal::Broadcast(Val::Date(av)), RegVal::Date(b))
        | (RegVal::Broadcast(Val::Timestamp(av)), RegVal::Timestamp(b))
        | (RegVal::Broadcast(Val::Duration(av)), RegVal::Duration(b)) => {
            let a = av.to_i64()?;
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a.cmp(&b[i])));
            }
            Some(out)
        }
        (RegVal::Decimal(a), RegVal::Decimal(b)) => {
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a[i].cmp(&b[i])));
            }
            Some(out)
        }
        (RegVal::Decimal(a), RegVal::Broadcast(Val::Decimal(bv))) => {
            let b = bv.to_i128()?;
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a[i].cmp(&b)));
            }
            Some(out)
        }
        (RegVal::Broadcast(Val::Decimal(av)), RegVal::Decimal(b)) => {
            let a = av.to_i128()?;
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a.cmp(&b[i])));
            }
            Some(out)
        }
        (RegVal::Float(a), RegVal::Float(b)) => {
            for &l in active {
                let i = usize::from(l);
                let ka = float_order_key(Float64::from_bits(a[i]));
                let kb = float_order_key(Float64::from_bits(b[i]));
                out[i] = u8::from(cmp_ord_matches(op, ka.cmp(&kb)));
            }
            Some(out)
        }
        (RegVal::Float(a), RegVal::Broadcast(Val::Float(bv))) => {
            let kb = float_order_key(*bv);
            for &l in active {
                let i = usize::from(l);
                let ka = float_order_key(Float64::from_bits(a[i]));
                out[i] = u8::from(cmp_ord_matches(op, ka.cmp(&kb)));
            }
            Some(out)
        }
        (RegVal::Broadcast(Val::Float(av)), RegVal::Float(b)) => {
            let ka = float_order_key(*av);
            for &l in active {
                let i = usize::from(l);
                let kb = float_order_key(Float64::from_bits(b[i]));
                out[i] = u8::from(cmp_ord_matches(op, ka.cmp(&kb)));
            }
            Some(out)
        }
        (
            RegVal::Text {
                offsets: oa,
                data: da,
            },
            RegVal::Broadcast(Val::Text(bs)),
        ) => {
            let b_bytes = bs.as_bytes();
            for &l in active {
                let i = usize::from(l);
                let a_bytes = &da[oa[i]..oa[i + 1]];
                out[i] = u8::from(cmp_ord_matches(op, a_bytes.cmp(b_bytes)));
            }
            Some(out)
        }
        (
            RegVal::Text {
                offsets: oa,
                data: da,
            },
            RegVal::Text {
                offsets: ob,
                data: db,
            },
        ) => {
            for &l in active {
                let i = usize::from(l);
                let a_bytes = &da[oa[i]..oa[i + 1]];
                let b_bytes = &db[ob[i]..ob[i + 1]];
                out[i] = u8::from(cmp_ord_matches(op, a_bytes.cmp(b_bytes)));
            }
            Some(out)
        }
        (RegVal::Bool(a), RegVal::Bool(b)) => {
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a[i].cmp(&b[i])));
            }
            Some(out)
        }
        (RegVal::Bool(a), RegVal::Broadcast(Val::Bool(bv))) => {
            let b = u8::from(*bv);
            for &l in active {
                let i = usize::from(l);
                out[i] = u8::from(cmp_ord_matches(op, a[i].cmp(&b)));
            }
            Some(out)
        }
        _ => None,
    }
}

/// Evaluate any scalar [`ExecPrimOp`] on one lane (exact fallback matching `src/oracle/eval.rs`
/// for `Core(PrimOp)` and `src/runtime/exec.rs` for Phase 2 surface extensions).
pub fn eval_scalar_exec_prim(
    op: &ExecPrimOp,
    args: &[Val],
    lane: usize,
) -> Result<Val, RowEvalErr> {
    match op {
        ExecPrimOp::Core(cop) => match eval_prim_op(cop, args) {
            PrimResult::Ok(v) => Ok(v),
            PrimResult::Stopped(bug) => Err(RowEvalErr::Stopped { lane, bug }),
            PrimResult::OutOfFuel => Err(RowEvalErr::Stopped {
                lane,
                bug: Bug {
                    kind: BugKind::OutsideBoundary,
                    message: "out of fuel".to_string(),
                },
            }),
            PrimResult::Wrong => Err(RowEvalErr::Failed(format!(
                "primitive type error in `{cop:?}`"
            ))),
        },
        ExecPrimOp::AddFloat => match args {
            [Val::Float(a), Val::Float(b)] => {
                Ok(Val::Float(Float64::from_f64(a.to_f64() + b.to_f64())))
            }
            _ => Err(RowEvalErr::Failed(
                "AddFloat requires two Float args".to_string(),
            )),
        },
        ExecPrimOp::SubFloat => match args {
            [Val::Float(a), Val::Float(b)] => {
                Ok(Val::Float(Float64::from_f64(a.to_f64() - b.to_f64())))
            }
            _ => Err(RowEvalErr::Failed(
                "SubFloat requires two Float args".to_string(),
            )),
        },
        ExecPrimOp::MulFloat => match args {
            [Val::Float(a), Val::Float(b)] => {
                Ok(Val::Float(Float64::from_f64(a.to_f64() * b.to_f64())))
            }
            _ => Err(RowEvalErr::Failed(
                "MulFloat requires two Float args".to_string(),
            )),
        },
        ExecPrimOp::DivFloat => match args {
            [Val::Float(a), Val::Float(b)] => {
                if b.to_f64() == 0.0 {
                    Err(RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::DivByZero,
                            message: "Float division by zero".to_string(),
                        },
                    })
                } else {
                    Ok(Val::Float(Float64::from_f64(a.to_f64() / b.to_f64())))
                }
            }
            _ => Err(RowEvalErr::Failed(
                "DivFloat requires two Float args".to_string(),
            )),
        },
        ExecPrimOp::NegFloat => match args {
            [Val::Float(a)] => Ok(Val::Float(Float64::from_f64(-a.to_f64()))),
            _ => Err(RowEvalErr::Failed("NegFloat requires Float".to_string())),
        },
        ExecPrimOp::AbsFloat => match args {
            [Val::Float(a)] => Ok(Val::Float(Float64::from_f64(a.to_f64().abs()))),
            _ => Err(RowEvalErr::Failed("AbsFloat requires Float".to_string())),
        },
        ExecPrimOp::AbsDecimal => match args {
            [Val::Decimal(d)] => Ok(Val::Decimal(if d.is_negative() {
                -d.clone()
            } else {
                d.clone()
            })),
            _ => Err(RowEvalErr::Failed(
                "AbsDecimal requires Decimal".to_string(),
            )),
        },
        ExecPrimOp::AbsInt => match args {
            [Val::Int(n)] => {
                let abs = if n.is_negative() {
                    -n.clone()
                } else {
                    n.clone()
                };
                if abs.in_int64_range() {
                    Ok(Val::Int(abs))
                } else {
                    Err(RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 abs overflow".to_string(),
                        },
                    })
                }
            }
            _ => Err(RowEvalErr::Failed("AbsInt requires Int".to_string())),
        },
        ExecPrimOp::RoundFloat => match args {
            [Val::Float(a), Val::Int(p)] => {
                let places = p.to_i64().unwrap_or(0).clamp(0, 15) as i32;
                let factor = 10f64.powi(places);
                let r = (a.to_f64() * factor).round() / factor;
                Ok(Val::Float(Float64::from_f64(r)))
            }
            _ => Err(RowEvalErr::Failed(
                "RoundFloat requires (Float, Int)".to_string(),
            )),
        },
        ExecPrimOp::RoundDecimal => match args {
            [Val::Decimal(d), Val::Int(p)] => {
                let places = p.to_i64().unwrap_or(0);
                Ok(Val::Decimal(round_decimal_bigint(d, places)))
            }
            _ => Err(RowEvalErr::Failed(
                "RoundDecimal requires (Decimal, Int)".to_string(),
            )),
        },
        ExecPrimOp::IntToFloat => match args {
            [Val::Int(n)] => Ok(Val::Float(
                Float64::from_f64(n.to_i64().unwrap_or(0) as f64),
            )),
            _ => Err(RowEvalErr::Failed("IntToFloat requires Int".to_string())),
        },
        ExecPrimOp::DecToFloat => match args {
            [Val::Decimal(d)] => {
                let f = render_decimal(d).parse::<f64>().unwrap_or(0.0);
                Ok(Val::Float(Float64::from_f64(f)))
            }
            _ => Err(RowEvalErr::Failed(
                "DecToFloat requires Decimal".to_string(),
            )),
        },
        ExecPrimOp::ValToText => match args {
            [v] => Ok(Val::Text(format_display_val_vm(v))),
            _ => Err(RowEvalErr::Failed("ValToText requires 1 arg".to_string())),
        },
        ExecPrimOp::DateTruncUnit(unit) => match args {
            [Val::Date(d)] => match date_trunc_date(d.to_i64().unwrap_or(0), unit) {
                Ok(td) => Ok(Val::Date(BigInt::from(td))),
                Err(e) => Err(RowEvalErr::Failed(e.message)),
            },
            [Val::Timestamp(ts)] => match date_trunc_timestamp_unit(ts.to_i64().unwrap_or(0), unit)
            {
                Ok(t) => Ok(Val::Timestamp(BigInt::from(t))),
                Err(e) => Err(RowEvalErr::Failed(e.message)),
            },
            _ => Err(RowEvalErr::Failed(
                "DateTruncUnit requires Date or Timestamp".to_string(),
            )),
        },
        ExecPrimOp::DateTruncDuration => match args {
            [Val::Timestamp(ts), Val::Duration(dur)] => {
                match date_trunc_timestamp_duration(
                    ts.to_i64().unwrap_or(0),
                    dur.to_i64().unwrap_or(0),
                ) {
                    Ok(t) => Ok(Val::Timestamp(BigInt::from(t))),
                    Err(e) => Err(RowEvalErr::Failed(e.message)),
                }
            }
            _ => Err(RowEvalErr::Failed(
                "DateTruncDuration requires (Timestamp, Duration)".to_string(),
            )),
        },
        ExecPrimOp::MonthsBetween => match args {
            [Val::Date(d1), Val::Date(d2)] => {
                let m = months_between_days(d1.to_i64().unwrap_or(0), d2.to_i64().unwrap_or(0));
                Ok(Val::Int(BigInt::from(m)))
            }
            _ => Err(RowEvalErr::Failed(
                "MonthsBetween requires two Dates".to_string(),
            )),
        },
        ExecPrimOp::InTz => match args {
            [Val::Timestamp(ts), Val::Text(zone)] => match ts.to_i64() {
                Some(us) => match format_timestamp_in_tz(us, zone) {
                    Ok(s) => Ok(Val::Text(s)),
                    Err(e) => Err(RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::OutsideBoundary,
                            message: e.message,
                        },
                    }),
                },
                None => Err(RowEvalErr::Failed("InTz Timestamp overflow".to_string())),
            },
            _ => Err(RowEvalErr::Failed(
                "InTz requires (Timestamp, Text)".to_string(),
            )),
        },
        ExecPrimOp::DateInTz => match args {
            [Val::Timestamp(ts), Val::Text(zone)] => match ts.to_i64() {
                Some(us) => match local_date_in_tz(us, zone) {
                    Ok(days) => Ok(Val::Date(BigInt::from(days))),
                    Err(e) => Err(RowEvalErr::Stopped {
                        lane,
                        bug: Bug {
                            kind: BugKind::OutsideBoundary,
                            message: e.message,
                        },
                    }),
                },
                None => Err(RowEvalErr::Failed(
                    "DateInTz Timestamp overflow".to_string(),
                )),
            },
            _ => Err(RowEvalErr::Failed(
                "DateInTz requires (Timestamp, Text)".to_string(),
            )),
        },
        ExecPrimOp::OptSubInt => match args {
            [Val::Int(_), Val::OptNone] => Ok(Val::OptNone),
            [Val::Int(a), Val::OptSome(b)] => match b.as_ref() {
                Val::Int(bv) => {
                    let diff = a - bv;
                    if diff.in_int64_range() {
                        Ok(Val::OptSome(Box::new(Val::Int(diff))))
                    } else {
                        Err(RowEvalErr::Stopped {
                            lane,
                            bug: Bug {
                                kind: BugKind::IntOverflow,
                                message: "Int64 overflow".to_string(),
                            },
                        })
                    }
                }
                _ => Err(RowEvalErr::Failed("OptSubInt type error".to_string())),
            },
            _ => Err(RowEvalErr::Failed(
                "OptSubInt requires (Int, Option(Int))".to_string(),
            )),
        },
        ExecPrimOp::OptSubDec => match args {
            [Val::Decimal(_), Val::OptNone] => Ok(Val::OptNone),
            [Val::Decimal(a), Val::OptSome(b)] => match b.as_ref() {
                Val::Decimal(bv) => {
                    let diff = a - bv;
                    if diff.in_decimal_range() {
                        Ok(Val::OptSome(Box::new(Val::Decimal(diff))))
                    } else {
                        Err(RowEvalErr::Stopped {
                            lane,
                            bug: Bug {
                                kind: BugKind::DecimalOverflow,
                                message: "Decimal overflow".to_string(),
                            },
                        })
                    }
                }
                _ => Err(RowEvalErr::Failed("OptSubDec type error".to_string())),
            },
            _ => Err(RowEvalErr::Failed(
                "OptSubDec requires (Decimal, Option(Decimal))".to_string(),
            )),
        },
        ExecPrimOp::OptSubFloat => match args {
            [Val::Float(_), Val::OptNone] => Ok(Val::OptNone),
            [Val::Float(a), Val::OptSome(b)] => match b.as_ref() {
                Val::Float(bv) => Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                    a.to_f64() - bv.to_f64(),
                ))))),
                _ => Err(RowEvalErr::Failed("OptSubFloat type error".to_string())),
            },
            _ => Err(RowEvalErr::Failed(
                "OptSubFloat requires (Float, Option(Float))".to_string(),
            )),
        },
        ExecPrimOp::RecordField { field_idx, .. } => match args {
            [Val::Ctor { fields, .. }] => fields
                .get(*field_idx)
                .cloned()
                .ok_or_else(|| RowEvalErr::Failed("record field index out of bounds".to_string())),
            [
                Val::LinearModel {
                    slope,
                    intercept,
                    r2,
                },
            ] => Ok(Val::Float(match field_idx {
                0 => *slope,
                1 => *intercept,
                _ => *r2,
            })),
            [Val::StatTest { stat, p_value }] => Ok(Val::Float(match field_idx {
                0 => *stat,
                1 => *p_value,
                _ => Float64::ZERO,
            })),
            _ => Err(RowEvalErr::Failed(
                "RecordField requires Ctor, LinearModel, or StatTest".to_string(),
            )),
        },
        ExecPrimOp::LinearModelPredict => match args {
            [
                Val::LinearModel {
                    slope, intercept, ..
                },
                x_val,
            ] => match crate::oracle::value::unwrap_numeric_float(x_val) {
                Some(x) => Ok(Val::Float(Float64::from_f64(
                    slope.to_f64() * x + intercept.to_f64(),
                ))),
                None => Err(RowEvalErr::Failed(
                    "LinearModel.predict requires a numeric argument".to_string(),
                )),
            },
            _ => Err(RowEvalErr::Failed(
                "LinearModel.predict requires (LinearModel, numeric)".to_string(),
            )),
        },
        ExecPrimOp::ListFirst => match args {
            [Val::List(xs)] => match xs.first() {
                Some(v) => Ok(Val::OptSome(Box::new(v.clone()))),
                None => Ok(Val::OptNone),
            },
            _ => Err(RowEvalErr::Failed("ListFirst requires List".to_string())),
        },
        ExecPrimOp::ListFirstBang => match args {
            [Val::List(xs)] => match xs.first() {
                Some(v) => Ok(v.clone()),
                None => Err(RowEvalErr::Stopped {
                    lane,
                    bug: Bug {
                        kind: BugKind::UnwrapNone,
                        message: "called `.first!` on an empty list".to_string(),
                    },
                }),
            },
            _ => Err(RowEvalErr::Failed(
                "ListFirstBang requires List".to_string(),
            )),
        },
        ExecPrimOp::LowerText => match args {
            [Val::Text(s)] => Ok(Val::Text(s.to_lowercase())),
            _ => Err(RowEvalErr::Failed("LowerText requires Text".to_string())),
        },
        ExecPrimOp::UpperText => match args {
            [Val::Text(s)] => Ok(Val::Text(s.to_uppercase())),
            _ => Err(RowEvalErr::Failed("UpperText requires Text".to_string())),
        },
        ExecPrimOp::SliceText => match args {
            [Val::Text(s), Val::Int(start), Val::Int(len)] => {
                let st = bigint_to_slice_bound(start);
                let ln = bigint_to_slice_bound(len);
                Ok(Val::Text(slice_text(s, st, ln)))
            }
            _ => Err(RowEvalErr::Failed(
                "SliceText requires (Text, Int, Int)".to_string(),
            )),
        },
        ExecPrimOp::StartsWithText => match args {
            [Val::Text(s), Val::Text(prefix)] => Ok(Val::Bool(s.starts_with(prefix.as_str()))),
            _ => Err(RowEvalErr::Failed(
                "StartsWithText requires (Text, Text)".to_string(),
            )),
        },
        ExecPrimOp::EndsWithText => match args {
            [Val::Text(s), Val::Text(suffix)] => Ok(Val::Bool(s.ends_with(suffix.as_str()))),
            _ => Err(RowEvalErr::Failed(
                "EndsWithText requires (Text, Text)".to_string(),
            )),
        },
        ExecPrimOp::TryParseDate => match args {
            [Val::Text(s)] => Ok(try_parse_date_text(s)),
            _ => Err(RowEvalErr::Failed("TryParseDate requires Text".to_string())),
        },
        ExecPrimOp::TryParseInt => match args {
            [Val::Text(s)] => Ok(try_parse_int_text(s)),
            _ => Err(RowEvalErr::Failed("TryParseInt requires Text".to_string())),
        },
        ExecPrimOp::TryParseDecimal => match args {
            [Val::Text(s)] => Ok(try_parse_decimal_text(s)),
            _ => Err(RowEvalErr::Failed(
                "TryParseDecimal requires Text".to_string(),
            )),
        },
        ExecPrimOp::TryParseFloat => match args {
            [Val::Text(s)] => Ok(try_parse_float_text(s)),
            _ => Err(RowEvalErr::Failed(
                "TryParseFloat requires Text".to_string(),
            )),
        },
        ExecPrimOp::InList => match args {
            [v, Val::List(xs)] => Ok(Val::Bool(eval_in_list(v, xs))),
            _ => Err(RowEvalErr::Failed(
                "InList requires (Val, List)".to_string(),
            )),
        },
        ExecPrimOp::ClampInt => match args {
            [Val::Int(x), Val::Int(lo), Val::Int(hi)] => clamp_int_bigint(x, lo, hi)
                .map(Val::Int)
                .map_err(|bug| RowEvalErr::Stopped { lane, bug }),
            _ => Err(RowEvalErr::Failed(
                "ClampInt requires (Int, Int, Int)".to_string(),
            )),
        },
        ExecPrimOp::ClampFloat => match args {
            [Val::Float(x), Val::Float(lo), Val::Float(hi)] => clamp_float_val(*x, *lo, *hi)
                .map(Val::Float)
                .map_err(|bug| RowEvalErr::Stopped { lane, bug }),
            _ => Err(RowEvalErr::Failed(
                "ClampFloat requires (Float, Float, Float)".to_string(),
            )),
        },
        ExecPrimOp::ClampDecimal => match args {
            [Val::Decimal(x), Val::Decimal(lo), Val::Decimal(hi)] => clamp_decimal_val(x, lo, hi)
                .map(Val::Decimal)
                .map_err(|bug| RowEvalErr::Stopped { lane, bug }),
            _ => Err(RowEvalErr::Failed(
                "ClampDecimal requires (Decimal, Decimal, Decimal)".to_string(),
            )),
        },
        ExecPrimOp::RoundToFloat => match args {
            [Val::Float(x), Val::Float(step)] => round_to_float_val(*x, *step)
                .map(Val::Float)
                .map_err(|bug| RowEvalErr::Stopped { lane, bug }),
            _ => Err(RowEvalErr::Failed(
                "RoundToFloat requires (Float, Float)".to_string(),
            )),
        },
        _ => Err(RowEvalErr::Failed(format!(
            "unsupported row primitive `{op:?}`"
        ))),
    }
}

fn format_display_val_vm(v: &Val) -> String {
    match v {
        Val::Text(s) => s.clone(),
        Val::Date(d) => d
            .to_i64()
            .map_or_else(|| d.to_string(), crate::formats::time::format_iso_date),
        Val::Timestamp(ts) => ts.to_i64().map_or_else(
            || ts.to_string(),
            crate::formats::time::format_iso_timestamp,
        ),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format!("{}", f.to_f64()),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => format_display_val_vm(inner),
        other => crate::oracle::value::render_public_val(other),
    }
}
