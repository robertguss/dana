/-
  DanaCore/Check.lean
  Decidable static schema, type, sensitivity-taint, declassification, capability,
  policy, and spec-code checker for Dana Core IR v0.1.
-/
import DanaCore.Syntax

namespace DanaCore

/-! ## Basic Uniqueness & Validity Helpers -/

def distinctIdents : List Ident → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && distinctIdents xs

def validTag (prog : Program) (t : Tag) : Bool :=
  builtInTags.contains t || prog.tags.contains t

def validTagSet (prog : Program) (ts : TagSet) : Bool :=
  ts.elems.all (validTag prog)

def ScalarTy.isOption : ScalarTy → Bool
  | .option _ => true
  | _ => false

def Ty.isOption : Ty → Bool
  | .option _ => true
  | _ => false

def validScalarTy (prog : Program) : ScalarTy → Bool
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration => true
  | .data name => (prog.findData? name).isSome
  | .option inner => !inner.isOption && validScalarTy prog inner

def validColSpec (prog : Program) (c : ColSpec) : Bool :=
  validScalarTy prog c.ty &&
  validTagSet prog c.tags &&
  (if c.bucketed then decide (c.ty = .text) else true)

def validTableTy (prog : Program) (tt : TableTy) : Bool :=
  let gks := tt.groupedBy.getD []
  distinctIdents (tt.cols.map ColSpec.name) &&
  tt.cols.all (fun c =>
    validColSpec prog c &&
    decide (decide (c.aggKind = .groupKey) = gks.contains c.name)) &&
  validTagSet prog tt.rowTags &&
  validTagSet prog tt.orderTags &&
  match tt.groupedBy with
  | none => true
  | some ks => distinctIdents ks && ks.all (fun k => (tt.findCol? k).isSome)

mutual
def validTy (prog : Program) : Ty → Bool
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .linearModel | .statTest
  | .args | .clock | .readFiles | .readDB _ | .rawReadDB _ | .secret _ => true
  | .option inner => !inner.isOption && validTy prog inner
  | .result okTy errTy => validTy prog okTy && validTy prog errTy
  | .tuple elems => validLTyList prog elems
  | .list elem => validLTy prog elem
  | .map k v => validLTy prog k && validLTy prog v
  | .data name => (prog.findData? name).isSome
  | .table tt => validTableTy prog tt
  | .dynamicTable ts | .chart ts | .report ts | .profile ts
  | .console ts | .declassify ts => validTagSet prog ts
  | .writeFiles _ ts | .httpsAllow _ ts => validTagSet prog ts
  | .writeTable _ _ cols rt allows =>
    distinctIdents (cols.map ColSpec.name) &&
    cols.all (validColSpec prog) &&
    validTagSet prog rt &&
    validTagSet prog allows
  | .fn params pc ret =>
    validLTyList prog params && validTagSet prog pc && validLTy prog ret

def validLTy (prog : Program) : LTy → Bool
  | .mk ty ts => validTy prog ty && validTagSet prog ts

def validLTyList (prog : Program) : List LTy → Bool
  | [] => true
  | l :: ls => validLTy prog l && validLTyList prog ls
end

/- First-order pure data types (free of closures and capabilities) that support
   structural equality `==` / `!=`. -/
mutual
def isEquatableTy : Ty → Bool
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .data _ | .linearModel | .statTest => true
  | .option inner => isEquatableTy inner
  | .result okTy errTy => isEquatableTy okTy && isEquatableTy errTy
  | .tuple elems => isEquatableLTyList elems
  | .list elem => isEquatableLTy elem
  | .map k v => isEquatableLTy k && isEquatableLTy v
  | .table _ => true
  | _ => false

def isEquatableLTy : LTy → Bool
  | .mk ty _ => isEquatableTy ty

def isEquatableLTyList : List LTy → Bool
  | [] => true
  | l :: ls => isEquatableLTy l && isEquatableLTyList ls
end

def isOrderedScalarTy : Ty → Bool
  | .bool | .int | .decimal | .float | .text | .date | .timestamp | .duration => true
  | _ => false

def isNumericBaseScalar : ScalarTy → Bool
  | .int | .decimal | .float => true
  | _ => false

def numericCoreOfScalar? : ScalarTy → Option ScalarTy
  | .int | .option .int => some .int
  | .decimal | .option .decimal => some .decimal
  | .float | .option .float => some .float
  | _ => none

def baseOfScalar : ScalarTy → ScalarTy
  | .option inner => inner
  | s => s

def ensureOptionScalar : ScalarTy → ScalarTy
  | .option inner => .option inner
  | s => .option s

/-! ## Environments & Subtyping -/

abbrev TyEnv := List (Ident × LTy)

def lookupTyEnv (env : TyEnv) (name : Ident) : Option LTy :=
  match env with
  | [] => none
  | (k, v) :: rest => if k = name then some v else lookupTyEnv rest name

def extendTyEnv (env : TyEnv) (bindings : List (Ident × LTy)) : TyEnv :=
  bindings ++ env

/-- Join point signature: `(params, joinPc, retLTy)`. -/
structure JoinSig where
  params : List (Ident × LTy)
  joinPc : TagSet
  retLTy : LTy
  deriving DecidableEq, Repr

abbrev JoinEnv := List (Ident × JoinSig)

def lookupJoinEnv (jenv : JoinEnv) (label : Ident) : Option JoinSig :=
  match jenv with
  | [] => none
  | (k, v) :: rest => if k = label then some v else lookupJoinEnv rest label

/-- Label-subtyping check: identical structural `Ty` (modulo upward tag monotonicity on
    top-level `LTy.tags` and `TableTy` taint sets when binding into an annotated `LTy`). -/
def ltySubtype (sub sup : LTy) : Bool :=
  decide (sub.ty = sup.ty) && sub.tags.subset sup.tags

/-! ## Tail-Jump Restriction Checker -/

/- Returns `true` iff `e` contains NO `Jump` outside an enclosing `Join` inside `e`.
   Enforces that `Jump` only appears in tail position of its target `Join`. -/
mutual
def noFreeJumps (boundLabels : List Ident) : Expr → Bool
  | .lit _ | .var _ | .constRef _ | .tableLit _ _ => true
  | .letE _ _ bound body =>
    noFreeJumps [] bound && noFreeJumps boundLabels body
  | .ifE cond tBr eBr =>
    noFreeJumps [] cond && noFreeJumps boundLabels tBr && noFreeJumps boundLabels eBr
  | .caseE scrut arms =>
    noFreeJumps [] scrut && noFreeJumpsArms boundLabels arms
  | .lam _ _ _ body =>
    noFreeJumps [] body
  | .app fnExpr args =>
    noFreeJumps [] fnExpr && noFreeJumpsList args
  | .call _ args =>
    noFreeJumpsList args
  | .join label _ rhs body =>
    noFreeJumps (label :: boundLabels) rhs && noFreeJumps (label :: boundLabels) body
  | .jump label args =>
    boundLabels.contains label && noFreeJumpsList args
  | .tuple elems => noFreeJumpsList elems
  | .proj tup _ => noFreeJumps [] tup
  | .ctor _ _ args => noFreeJumpsList args
  | .prim _ args => noFreeJumpsList args
  | .rel plan => noFreeJumpsPlan plan
  | .host _ args => noFreeJumpsList args
  | .stop _ detail =>
    match detail with
    | none => true
    | some d => noFreeJumps [] d
  | .fail msg => noFreeJumps [] msg

def noFreeJumpsList : List Expr → Bool
  | [] => true
  | e :: es => noFreeJumps [] e && noFreeJumpsList es

def noFreeJumpsArms (boundLabels : List Ident) : List CaseArm → Bool
  | [] => true
  | .mk _ _ body :: rest =>
    noFreeJumps boundLabels body && noFreeJumpsArms boundLabels rest

def noFreeJumpsPlan : Plan → Bool
  | .sourceExpr e => noFreeJumps [] e
  | .sourceDB cap _ _ => noFreeJumps [] cap
  | .select p _ | .drop p _ | .rename p _ | .derive p _ | .filter p _
  | .distinct p _ | .sort p _ | .limit p _ | .groupBy p _
  | .summarize p _ _ | .suppressSmallGroups p _ _ _ | .window p _
  | .fillGaps p _ _ _ _ | .pivotWider p _ _ _ _ | .crosstab p _ _ _ _
  | .redact p _ _ => noFreeJumpsPlan p
  | .join _ l r _ _ | .union l r => noFreeJumpsPlan l && noFreeJumpsPlan r
  | .pseudonymize p _ sec => noFreeJumpsPlan p && noFreeJumps [] sec
end

/-! ## Literal & Primitive Type Checking -/

def checkLiteral (prog : Program) (pc : TagSet) : Literal → Except String LTy
  | .unit => .ok (.mk .unit pc)
  | .bool _ => .ok (.mk .bool pc)
  | .int n =>
    if inInt64Range n then .ok (.mk .int pc)
    else .error "integer literal out of 64-bit signed range"
  | .decimal d =>
    if inDecimalRange d then .ok (.mk .decimal pc)
    else .error "decimal literal out of 128-bit range"
  | .float _ => .ok (.mk .float pc)
  | .text _ => .ok (.mk .text pc)
  | .bytes _ => .ok (.mk .bytes pc)
  | .date _ => .ok (.mk .date pc)
  | .timestamp _ => .ok (.mk .timestamp pc)
  | .duration _ => .ok (.mk .duration pc)
  | .noneLit inner =>
    if !inner.isOption && validTy prog inner then .ok (.mk (.option inner) pc)
    else .error "invalid Option inner type in none literal"

def checkRowLit (prog : Program) (cols : List ColSpec) (r : RowLit) : Bool :=
  let rec go : List ColSpec → List Literal → Bool
    | [], [] => true
    | c :: cs, l :: ls =>
      match checkLiteral prog TagSet.empty l with
      | .ok lty => decide (lty.ty = c.ty.toTy) && go cs ls
      | .error _ => false
    | _, _ => false
  go cols r.cells

def checkPrimOp (prog : Program) (pc : TagSet) (op : PrimOp) (args : List LTy) :
    Except String LTy :=
  match op, args with
  | .someVal inner, [a] =>
    if !inner.isOption && validTy prog inner && decide (a.ty = inner) then
      .ok (.mk (.option inner) (a.tags.union pc))
    else .error "someVal type mismatch"
  | .isSome, [.mk (.option _) ts] => .ok (.mk .bool (ts.union pc))
  | .isNone, [.mk (.option _) ts] => .ok (.mk .bool (ts.union pc))
  | .unwrapOr, [.mk (.option inner) ts1, .mk ty2 ts2] =>
    if decide (inner = ty2) then
      .ok (.mk inner ((ts1.union ts2).union pc))
    else .error "unwrapOr branch type mismatch"
  | .unwrapBang, [.mk (.option inner) ts] =>
    .ok (.mk inner (ts.union pc))
  | .okVal errTy, [a] =>
    if validTy prog errTy then .ok (.mk (.result a.ty errTy) (a.tags.union pc))
    else .error "invalid errTy in okVal"
  | .errVal okTy, [a] =>
    if validTy prog okTy then .ok (.mk (.result okTy a.ty) (a.tags.union pc))
    else .error "invalid okTy in errVal"
  | .addInt, [.mk .int t1, .mk .int t2]
  | .subInt, [.mk .int t1, .mk .int t2]
  | .mulInt, [.mk .int t1, .mk .int t2]
  | .divInt, [.mk .int t1, .mk .int t2]
  | .modInt, [.mk .int t1, .mk .int t2] =>
    .ok (.mk .int ((t1.union t2).union pc))
  | .negInt, [.mk .int t1] =>
    .ok (.mk .int (t1.union pc))
  | .addDec, [.mk .decimal t1, .mk .decimal t2]
  | .subDec, [.mk .decimal t1, .mk .decimal t2]
  | .mulDec, [.mk .decimal t1, .mk .decimal t2]
  | .divDec, [.mk .decimal t1, .mk .decimal t2] =>
    .ok (.mk .decimal ((t1.union t2).union pc))
  | .negDec, [.mk .decimal t1] =>
    .ok (.mk .decimal (t1.union pc))
  | .intToDec, [.mk .int t1] =>
    .ok (.mk .decimal (t1.union pc))
  | .boolToDec, [.mk .bool t1] =>
    .ok (.mk .decimal (t1.union pc))
  | .eq, [a1, a2]
  | .ne, [a1, a2] =>
    if decide (a1.ty = a2.ty) && isEquatableTy a1.ty then
      .ok (.mk .bool ((a1.effectiveTags.union a2.effectiveTags).union pc))
    else .error "eq/ne requires matching equatable types"
  | .lt, [a1, a2]
  | .le, [a1, a2]
  | .gt, [a1, a2]
  | .ge, [a1, a2] =>
    if decide (a1.ty = a2.ty) && isOrderedScalarTy a1.ty then
      .ok (.mk .bool ((a1.effectiveTags.union a2.effectiveTags).union pc))
    else .error "comparison requires matching ordered scalar types"
  | .notBool, [.mk .bool t1] =>
    .ok (.mk .bool (t1.union pc))
  | .andBool, [.mk .bool t1, .mk .bool t2]
  | .orBool, [.mk .bool t1, .mk .bool t2] =>
    .ok (.mk .bool ((t1.union t2).union pc))
  | .concatText, [.mk .text t1, .mk .text t2] =>
    .ok (.mk .text ((t1.union t2).union pc))
  | .containsText, [.mk .text t1, .mk .text t2] =>
    .ok (.mk .bool ((t1.union t2).union pc))
  | .trimText, [.mk .text t1]
  | .lowerAsciiText, [.mk .text t1] =>
    .ok (.mk .text (t1.union pc))
  | .emptyText, [.mk .text t1] =>
    .ok (.mk .bool (t1.union pc))
  | .intToText, [.mk .int t1] =>
    .ok (.mk .text (t1.union pc))
  | .decToText, [.mk .decimal t1] =>
    .ok (.mk .text (t1.union pc))
  | .dateTruncMonth, [.mk .date t1] =>
    .ok (.mk .date (t1.union pc))
  | .addDuration, [.mk .timestamp t1, .mk .duration t2] =>
    .ok (.mk .timestamp ((t1.union t2).union pc))
  | .diffTimestamp, [.mk .timestamp t1, .mk .timestamp t2] =>
    .ok (.mk .duration ((t1.union t2).union pc))
  | .listLit elemLTy, elems =>
    if validLTy prog elemLTy && elems.all (fun a => ltySubtype a elemLTy) then
      .ok (.mk (.list elemLTy) pc)
    else .error "listLit element type/tag mismatch"
  | .listLen, [.mk (.list _) ts] =>
    .ok (.mk .int (ts.union pc))
  | .listEmpty, [.mk (.list _) ts] =>
    .ok (.mk .bool (ts.union pc))
  | .listAppend, [.mk (.list elemLTy) tsL, item] =>
    if ltySubtype item elemLTy then
      .ok (.mk (.list elemLTy) (tsL.union pc))
    else .error "listAppend element mismatch"
  | .listConcat, [.mk (.list (.mk (.list elemLTy) innerTs)) outerTs] =>
    .ok (.mk (.list (elemLTy.addTags innerTs)) ((outerTs.union innerTs).union pc))
  | .mapLit kLTy vLTy, kvArgs =>
    let rec checkPairs : List LTy → Bool
      | [] => true
      | k :: v :: rest => ltySubtype k kLTy && ltySubtype v vLTy && checkPairs rest
      | [_] => false
    if validLTy prog kLTy && validLTy prog vLTy && isEquatableTy kLTy.ty && checkPairs kvArgs then
      .ok (.mk (.map kLTy vLTy) pc)
    else .error "mapLit key/value type mismatch"
  | .mapGet, [.mk (.map kLTy vLTy) mapTs, .mk qTy qTs] =>
    if decide (qTy = kLTy.ty) && isEquatableTy qTy && !vLTy.ty.isOption then
      let resTags := (((mapTs.union kLTy.effectiveTags).union vLTy.tags).union qTs).union pc
      .ok (.mk (.option vLTy.ty) resTags)
    else .error "mapGet key type mismatch"
  | .tableCount, [.mk (.table tt) tTs] =>
    .ok (.mk .int ((tt.rowTags.union tTs).union pc))
  | .tableConcat schema, [.mk (.list (.mk (.table tt) elemTs)) listTs] =>
    if decide (schema = tt) && validTableTy prog schema then
      let extra := (elemTs.union listTs).union pc
      let outTT : TableTy := {
        cols := tt.cols.map (fun c => { c with aggKind := .raw })
        rowTags := tt.rowTags.union extra
        orderTags := tt.orderTags.union extra
        groupedBy := none
        summarized := false
        distinctBy := none
      }
      .ok (.mk (.table outTT) pc)
    else .error "tableConcat schema annotation mismatch"
  | .tableProfile, [.mk (.table tt) tTs] =>
    .ok (.mk (.profile ((tt.totalTags.union tTs).union pc)) pc)
  | .statsCorr colX colY, [.mk (.table tt) tTs] =>
    match tt.findCol? colX, tt.findCol? colY with
    | some cX, some cY =>
      if (numericCoreOfScalar? cX.ty).isSome && (numericCoreOfScalar? cY.ty).isSome then
        let sTags := (((tt.rowTags.union tTs).union cX.tags).union cY.tags).union pc
        .ok (.mk (.option .float) sTags)
      else .error "statsCorr requires numeric columns"
    | _, _ => .error "statsCorr missing column"
  | .statsLinReg colX colY, [.mk (.table tt) tTs] =>
    match tt.findCol? colX, tt.findCol? colY with
    | some cX, some cY =>
      if (numericCoreOfScalar? cX.ty).isSome && (numericCoreOfScalar? cY.ty).isSome then
        let sTags := (((tt.rowTags.union tTs).union cX.tags).union cY.tags).union pc
        .ok (.mk .linearModel sTags)
      else .error "statsLinReg requires numeric columns"
    | _, _ => .error "statsLinReg missing column"
  | .statsTTest colX colY, [.mk (.table tt) tTs] =>
    match tt.findCol? colX, tt.findCol? colY with
    | some cX, some cY =>
      if (numericCoreOfScalar? cX.ty).isSome && (numericCoreOfScalar? cY.ty).isSome then
        let sTags := (((tt.rowTags.union tTs).union cX.tags).union cY.tags).union pc
        .ok (.mk .statTest sTags)
      else .error "statsTTest requires numeric columns"
    | _, _ => .error "statsTTest missing column"
  | .chartMake _ cols _, [.mk (.table tt) tTs] =>
    if !cols.isEmpty && cols.all (fun cn => (tt.findCol? cn).isSome) then
      let colTags := TagSet.unionList (cols.filterMap (fun cn => (tt.findCol? cn).map ColSpec.tags))
      let cTags := (((tt.rowTags.union tt.orderTags).union tTs).union colTags).union pc
      .ok (.mk (.chart cTags) pc)
    else .error "chartMake references unknown or empty columns"
  | .reportNew, [.mk .text tTs] =>
    .ok (.mk (.report (tTs.union pc)) pc)
  | .reportAddSummary, [.mk (.report rTs) roTs, .mk .text sTs] =>
    .ok (.mk (.report (((rTs.union roTs).union sTs).union pc)) pc)
  | .reportAddChart, [.mk (.report rTs) roTs, .mk (.chart cTs) coTs] =>
    .ok (.mk (.report ((((rTs.union roTs).union cTs).union coTs).union pc)) pc)
  | .reportAddTable, [.mk (.report rTs) roTs, .mk (.table tt) toTs] =>
    .ok (.mk (.report ((((rTs.union roTs).union tt.totalTags).union toTs).union pc)) pc)
  | _, _ => .error "ill-typed primitive operation"

/-! ## `RowExpr` Static Checker -/

mutual
def checkRowExpr (prog : Program) (env : TyEnv) (cols : List ColSpec) (re : RowExpr) :
    Except String (ScalarTy × TagSet) :=
  match re with
  | .lit v => do
    let lty ← checkLiteral prog TagSet.empty v
    match lty.ty.toScalarTy? with
    | some sTy =>
      if validScalarTy prog sTy then .ok (sTy, TagSet.empty)
      else .error "invalid scalar literal type in RowExpr"
    | none => .error "non-scalar literal in RowExpr"
  | .col name =>
    match cols.find? (fun c => c.name == name) with
    | some c => .ok (c.ty, c.tags)
    | none => .error s!"missing column '{name}' in RowExpr"
  | .outerVar name =>
    match lookupTyEnv env name with
    | some lty =>
      match lty.ty.toScalarTy? with
      | some sTy =>
        if validScalarTy prog sTy then .ok (sTy, lty.effectiveTags)
        else .error s!"outer variable '{name}' in RowExpr has invalid scalar type"
      | none => .error s!"outer variable '{name}' in RowExpr is not a scalar type"
    | none => .error s!"unbound outer variable '{name}' in RowExpr"
  | .constRef name =>
    match prog.findConst? name with
    | some cDecl =>
      match cDecl.lty.ty.toScalarTy? with
      | some sTy =>
        if validScalarTy prog sTy then .ok (sTy, cDecl.lty.effectiveTags)
        else .error s!"constant '{name}' has invalid scalar type"
      | none => .error s!"constant '{name}' is not scalar"
    | none => .error s!"unknown constant '{name}'"
  | .prim op args => do
    let argPairs ← checkRowExprList prog env cols args
    let argLTys := argPairs.map (fun (sTy, ts) => LTy.mk sTy.toTy ts)
    let resLTy ← checkPrimOp prog TagSet.empty op argLTys
    match resLTy.ty.toScalarTy? with
    | some sTy =>
      if validScalarTy prog sTy then .ok (sTy, resLTy.effectiveTags)
      else .error "PrimOp in RowExpr produced nested Option or invalid scalar type"
    | none => .error "PrimOp in RowExpr did not produce a scalar column type"
  | .ifE cond tBr eBr => do
    let (cTy, cTags) ← checkRowExpr prog env cols cond
    let (tTy, tTags) ← checkRowExpr prog env cols tBr
    let (eTy, eTags) ← checkRowExpr prog env cols eBr
    if decide (cTy = .bool) && decide (tTy = eTy) then
      .ok (tTy, (cTags.union tTags).union eTags)
    else .error "RowExpr ifE requires Bool condition and matching branch types"
  | .coalesce optE defE => do
    let (oTy, oTags) ← checkRowExpr prog env cols optE
    let (dTy, dTags) ← checkRowExpr prog env cols defE
    match oTy with
    | .option inner =>
      if decide (inner = dTy) then .ok (dTy, oTags.union dTags)
      else .error "RowExpr coalesce type mismatch"
    | _ => .error "RowExpr coalesce requires Option left operand"
  | .callPure fnName args => do
    let argPairs ← checkRowExprList prog env cols args
    match prog.findFun? fnName with
    | some fDecl =>
      if !fDecl.isPure || fDecl.kind.isSpec then
        .error s!"function '{fnName}' called in RowExpr must be a pure non-spec function"
      else if fDecl.params.length != argPairs.length then
        .error s!"arity mismatch in RowExpr call to '{fnName}'"
      else
        let rec checkArgs : List (ScalarTy × TagSet) → List (Ident × LTy) → Bool
          | [], [] => true
          | (sTy, _) :: restA, (_, pLTy) :: restP =>
            decide (sTy.toTy = pLTy.ty) && pLTy.tags.isEmpty && checkArgs restA restP
          | _, _ => false
        if !fDecl.pc.isEmpty || !checkArgs argPairs fDecl.params then
          .error s!"pure function '{fnName}' in RowExpr must have public signature"
        else
          match fDecl.ret.ty.toScalarTy? with
          | some retSTy =>
            if validScalarTy prog retSTy then
              let argUnion := TagSet.unionList (argPairs.map Prod.snd)
              .ok (retSTy, fDecl.ret.effectiveTags.union argUnion)
            else .error s!"pure function '{fnName}' returns invalid scalar type"
          | none => .error s!"pure function '{fnName}' does not return a scalar type"
    | none => .error s!"unknown function '{fnName}' in RowExpr"
  termination_by structural re

def checkRowExprList (prog : Program) (env : TyEnv) (cols : List ColSpec)
    (rs : List RowExpr) : Except String (List (ScalarTy × TagSet)) :=
  match rs with
  | [] => .ok []
  | r :: rest => do
    let hd ← checkRowExpr prog env cols r
    let tl ← checkRowExprList prog env cols rest
    .ok (hd :: tl)
  termination_by structural rs
end

/-! ## Host Capability Operations & `dana.policy` Enforcement -/

def quarantineBadRowTableTy (s : TableTy) : TableTy :=
  let valTags := s.allColTags
  let lineTags := s.rowTags.union valTags
  { cols := [
      { name := "line", ty := .int, tags := TagSet.empty },
      { name := "column", ty := .text, tags := TagSet.empty },
      { name := "error_kind", ty := .text, tags := TagSet.empty },
      { name := "raw_value", ty := .text, tags := valTags },
      { name := "raw_line", ty := .text, tags := lineTags }
    ]
    rowTags := s.rowTags
    orderTags := s.orderTags }

def isSafeRelativePath (path : String) : Bool :=
  !path.isEmpty &&
  !path.startsWith "/" &&
  !path.contains '\\' &&
  !(path.splitOn "/").any (fun seg => seg == "..")

def joinConfinedPath (root relPath : String) : String :=
  if root.isEmpty then relPath
  else if root.endsWith "/" then root ++ relPath
  else root ++ "/" ++ relPath

def pathMatchesExportPrefix (policyRoot reqRoot : String) : Bool :=
  isSafeRelativePath reqRoot &&
  (reqRoot == policyRoot ||
    (policyRoot.endsWith "/" && reqRoot.startsWith policyRoot) ||
    (!policyRoot.endsWith "/" && reqRoot.startsWith (policyRoot ++ "/")))

def policyAllowsExport (p : Policy) (root : String) (allows : TagSet) : Bool :=
  allows.isEmpty ||
  (isSafeRelativePath root &&
    p.allowExport.any (fun (r, polTags) => pathMatchesExportPrefix r root && allows.subset polTags))

def policyAllowsHttps (p : Policy) (host : String) (allows : TagSet) : Bool :=
  allows.isEmpty ||
  p.allowHttps.any (fun (h, polTags) => h == host && allows.subset polTags)

def policyAllowsWrite (p : Policy) (db : Ident) (tbl : Ident) (allows : TagSet) : Bool :=
  allows.isEmpty ||
  p.allowWrite.any (fun r => r.db == db && r.table == tbl && allows.subset r.tags)

/-- Verify a capability type against optional repository `dana.policy` upper bound. -/
def checkCapAgainstPolicy (pol? : Option Policy) (ty : Ty) : Except String Unit :=
  match pol? with
  | none => .ok ()
  | some p =>
    match ty with
    | .declassify _ =>
      if p.forbidManualDeclassify then
        .error "dana.policy forbids manual Declassify capabilities"
      else .ok ()
    | .console allows =>
      if allows.isEmpty || allows.subset p.allowConsole then .ok ()
      else .error "Console capability exceeds dana.policy allowConsole"
    | .writeFiles root allows =>
      if policyAllowsExport p root allows then .ok ()
      else .error s!"WriteFiles(\"{root}\") capability exceeds dana.policy"
    | .httpsAllow host allows =>
      if policyAllowsHttps p host allows then .ok ()
      else .error s!"HttpsAllow(\"{host}\") capability exceeds dana.policy"
    | .writeTable db tbl _ _ allows =>
      if policyAllowsWrite p db tbl allows then .ok ()
      else .error s!"WriteTable({db}.{tbl}) capability exceeds dana.policy"
    | _ => .ok ()

def checkWriteTableCols (srcCols destCols : List ColSpec) (effRowTags destRowTags : TagSet) : Bool :=
  destCols.all (fun dc => effRowTags.subset (destRowTags.union dc.tags)) &&
  let rec go : List ColSpec → List ColSpec → Bool
    | [], [] => true
    | sc :: scs, dc :: dcs =>
      decide (sc.name = dc.name) &&
      decide (sc.ty = dc.ty) &&
      sc.tags.subset dc.tags &&
      go scs dcs
    | _, _ => false
  go srcCols destCols

def checkHostOp (prog : Program) (pc : TagSet) (inSpec : Bool) (op : HostOp) (args : List LTy) :
    Except String LTy :=
  match op, args with
  | .argsGet, [.mk .args capTs] =>
    .ok (.mk (.list (.mk .text TagSet.empty)) (capTs.union pc))
  | .clockNow, [.mk .clock capTs] =>
    .ok (.mk .timestamp (capTs.union pc))
  | .consolePrint, [.mk (.console allows) capTs, .mk .text mTs]
  | .consoleError, [.mk (.console allows) capTs, .mk .text mTs] => do
    checkCapAgainstPolicy prog.policy (.console allows)
    let eff := (pc.union capTs).union mTs
    if eff.subset allows then .ok (.mk .unit pc)
    else .error "Console sink unauthorized for value or pc sensitivity tags"
  | .consolePrintTable, [.mk (.console allows) capTs, .mk (.table tt) tTs] => do
    checkCapAgainstPolicy prog.policy (.console allows)
    let eff := ((pc.union capTs).union tTs).union tt.totalTags
    if eff.subset allows then .ok (.mk .unit pc)
    else .error "Console.printTable unauthorized for table sensitivity tags"
  | .readCsv schemaName, [.mk .readFiles capTs, .mk .text pathTs] =>
    match prog.findSchema? schemaName with
    | some sDecl =>
      let ctxTs := (pc.union capTs).union pathTs
      let goodTT : TableTy := {
        sDecl.schema with
        rowTags := sDecl.schema.rowTags.union ctxTs
        orderTags := sDecl.schema.orderTags.union ctxTs
      }
      let baseBad := quarantineBadRowTableTy sDecl.schema
      let badTT : TableTy := {
        baseBad with
        rowTags := baseBad.rowTags.union ctxTs
        orderTags := baseBad.orderTags.union ctxTs
      }
      let tupTy : Ty := .tuple [.mk (.table goodTT) TagSet.empty, .mk (.table badTT) TagSet.empty]
      .ok (.mk (.result tupTy .text) ctxTs)
    | none => .error s!"unknown schema '{schemaName}' in readCsv"
  | .writeFile, [.mk (.writeFiles root allows) capTs, .mk .text pTs, .mk .text cTs] => do
    checkCapAgainstPolicy prog.policy (.writeFiles root allows)
    let eff := ((pc.union capTs).union pTs).union cTs
    if eff.subset allows then .ok (.mk (.result .unit .text) eff)
    else .error s!"WriteFiles(\"{root}\") unauthorized for sensitivity tags"
  | .writeReportHtml, [.mk (.writeFiles root allows) capTs, .mk .text pTs, .mk (.report rTs) roTs] => do
    checkCapAgainstPolicy prog.policy (.writeFiles root allows)
    let eff := (((pc.union capTs).union pTs).union rTs).union roTs
    if eff.subset allows then .ok (.mk (.result .unit .text) eff)
    else .error s!"WriteFiles(\"{root}\") unauthorized for Report sensitivity tags"
  | .writeTable, [.mk (.writeTable db tbl destCols destRowTags allows) capTs, .mk (.table srcTT) srcTs] => do
    checkCapAgainstPolicy prog.policy (.writeTable db tbl destCols destRowTags allows)
    let effRow := ((pc.union capTs).union srcTs).union (srcTT.rowTags.union srcTT.orderTags)
    let effAll := effRow.union srcTT.allColTags
    if !effAll.subset allows then
      .error s!"WriteTable({db}.{tbl}) allows set does not cover source sensitivity tags"
    else if !checkWriteTableCols srcTT.cols destCols effRow destRowTags then
      .error s!"WriteTable({db}.{tbl}) column-by-column schema or tag mismatch"
    else
      .ok (.mk (.result .int .text) effRow)
  | .declassifyApprove clearTags, [.mk (.declassify allows) capTs, valLTy, .mk .text reasonTs] => do
    checkCapAgainstPolicy prog.policy (.declassify allows)
    if !validTagSet prog clearTags then
      .error "invalid tag in declassifyApprove"
    else if !clearTags.subset allows then
      .error "declassifyApprove clearTags exceeds Declassify capability allows"
    else if !reasonTs.isEmpty then
      .error "declassifyApprove audit reason must be public"
    else
      let baseTags := (valLTy.tags.union capTs).union pc
      -- Only allowed on scalar/non-table values so column tags cannot be bypassed without clearing
      match valLTy.ty with
      | .table _ => .error "declassifyApprove operates on scalar/composite values, not raw Tables"
      | _ => .ok (.mk valLTy.ty ((baseTags.diff clearTags).union pc))
  -- Outside boundary ops (type-checked & capability-checked identically to local ops)
  | .rawSqlQuery reqDb outSchema, [.mk (.rawReadDB capDb) capTs, .mk .text sqlTs] =>
    if decide (reqDb = capDb) && validTableTy prog outSchema && sqlTs.isEmpty then
      let ctxTs := capTs.union pc
      let outTT := { outSchema with
        rowTags := outSchema.rowTags.union ctxTs
        orderTags := outSchema.orderTags.union ctxTs }
      .ok (.mk (.result (.table outTT) .text) ctxTs)
    else .error "rawSqlQuery DB mismatch, invalid schema, or non-public SQL string"
  | .httpsGetJson, [.mk (.httpsAllow host allows) capTs, .mk .text urlTs] => do
    checkCapAgainstPolicy prog.policy (.httpsAllow host allows)
    let eff := (pc.union capTs).union urlTs
    if eff.subset allows then .ok (.mk (.result .text .text) eff)
    else .error s!"HttpsAllow(\"{host}\") unauthorized for URL/pc sensitivity tags"
  | .readParquet outSchema, [.mk .readFiles capTs, .mk .text pathTs] =>
    if validTableTy prog outSchema then
      let ctxTs := (pc.union capTs).union pathTs
      let outTT := { outSchema with
        rowTags := outSchema.rowTags.union ctxTs
        orderTags := outSchema.orderTags.union ctxTs }
      .ok (.mk (.result (.table outTT) .text) ctxTs)
    else .error "invalid schema in readParquet"
  | .writeParquet, [.mk (.writeFiles root allows) capTs, .mk .text pTs, .mk (.table srcTT) srcTs]
  | .writeXlsx, [.mk (.writeFiles root allows) capTs, .mk .text pTs, .mk (.table srcTT) srcTs] => do
    checkCapAgainstPolicy prog.policy (.writeFiles root allows)
    let eff := (((pc.union capTs).union pTs).union srcTs).union srcTT.totalTags
    if eff.subset allows then .ok (.mk (.result .unit .text) eff)
    else .error s!"WriteFiles(\"{root}\") unauthorized for Parquet/XLSX table tags"
  -- Spec-only fake constructors
  | .fakeConsole allows, [] =>
    if inSpec && validTagSet prog allows then .ok (.mk (.console allows) pc)
    else .error "fakeConsole is only permitted in spec functions (test/example/promise)"
  | .fakeFiles allows, [] =>
    if inSpec && validTagSet prog allows then .ok (.mk (.writeFiles "mem://" allows) pc)
    else .error "fakeFiles is only permitted in spec functions"
  | .fakeDB db, [] =>
    if inSpec then .ok (.mk (.readDB db) pc)
    else .error "fakeDB is only permitted in spec functions"
  | .fakeHttps host allows, [] =>
    if inSpec && validTagSet prog allows then .ok (.mk (.httpsAllow host allows) pc)
    else .error "fakeHttps is only permitted in spec functions"
  | .fakeSecret name, [.mk .text valTs] =>
    if inSpec && valTs.isEmpty then .ok (.mk (.secret name) (pc.union (TagSet.singleton "secret")))
    else .error "fakeSecret is only permitted in spec functions with public fixture text"
  | _, _ => .error "ill-typed HostOp"

/-! ## Relational Plan Helper Functions -/

def resolveJoinPairs (lTT rTT : TableTy) (on : JoinOn) : Except String (List (ColSpec × ColSpec)) :=
  let rawPairs : List (Ident × Ident) :=
    match on with
    | .sameKeys ks => ks.map (fun k => (k, k))
    | .pairs ps => ps
  if rawPairs.isEmpty then
    .error "join requires at least one key pair"
  else
    let rec go : List (Ident × Ident) → Except String (List (ColSpec × ColSpec))
      | [] => .ok []
      | (lk, rk) :: rest =>
        match lTT.findCol? lk, rTT.findCol? rk with
        | some lc, some rc =>
          if decide (lc.ty = rc.ty) && isEquatableTy lc.ty.toTy then do
            let tl ← go rest
            .ok ((lc, rc) :: tl)
          else .error s!"join key type mismatch between '{lk}' and '{rk}'"
        | _, _ => .error s!"missing join key '{lk}' or '{rk}'"
    go rawPairs

def buildJoinedCols (kind : JoinKind) (lCols rCols : List ColSpec) (on : JoinOn)
    (suffixes : Suffixes) : Except String (List ColSpec) :=
  match kind with
  | .semi | .anti =>
    .ok (lCols.map (fun c => { c with aggKind := .raw }))
  | _ =>
    let sameKeyNames : List Ident :=
      match on with
      | .sameKeys ks => ks
      | .pairs _ => []
    let rFiltered := rCols.filter (fun rc => !sameKeyNames.contains rc.name)
    let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
    -- Merge sensitivity tags on shared `sameKeys` columns
    let lUpdated := lCols.map (fun lc =>
      if sameKeyNames.contains lc.name then
        match rCols.find? (fun rc => rc.name == lc.name) with
        | some rc => { lc with tags := lc.tags.union rc.tags, bucketed := false, aggKind := .raw }
        | none => { lc with aggKind := .raw }
      else { lc with aggKind := .raw })
    let rPrepared := rFiltered.map (fun rc =>
      { rc with
        ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty
        bucketed := if isLeftOuter then false else rc.bucketed
        aggKind := .raw })
    let lNames := lUpdated.map ColSpec.name
    let rNames := rPrepared.map ColSpec.name
    let hasCollision := lNames.any (fun n => rNames.contains n)
    if !hasCollision then
      .ok (lUpdated ++ rPrepared)
    else
      match suffixes with
      | none => .error "overlapping non-key join columns require explicit suffixes"
      | some (sL, sR) =>
        if sL == sR || (sL.isEmpty && sR.isEmpty) then
          .error "join suffixes must be distinct"
        else
          let lRenamed := lUpdated.map (fun c =>
            if rNames.contains c.name then { c with name := c.name ++ sL } else c)
          let rRenamed := rPrepared.map (fun c =>
            if lNames.contains c.name then { c with name := c.name ++ sR } else c)
          let combined := lRenamed ++ rRenamed
          if distinctIdents (combined.map ColSpec.name) then .ok combined
          else .error "join suffixes still produced duplicate column names"

def checkBucketCuts (prog : Program) (srcTy : ScalarTy) (cuts : List Literal)
    (labels : List String) : Bool :=
  !cuts.isEmpty &&
  labels.length == cuts.length + 1 &&
  isOrderedScalarTy srcTy.toTy &&
  cuts.all (fun lit =>
    match checkLiteral prog TagSet.empty lit with
    | .ok lty => decide (lty.ty = srcTy.toTy)
    | .error _ => false)

def checkAggItem (prog : Program) (env : TyEnv) (inTT : TableTy) (item : AggItem) :
    Except String ColSpec :=
  let kind : AggKind := if item.op.isBlending then .blending else .nonBlending
  let ordTags := if item.op.isOrderSensitive then inTT.orderTags else TagSet.empty
  let baseCtx := inTT.rowTags.union ordTags
  match item.op, item.arg with
  | .count, none =>
    .ok { name := item.name, ty := .int, tags := baseCtx, bucketed := false, aggKind := kind }
  | .countDistinct, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    if isEquatableTy sTy.toTy then
      .ok { name := item.name, ty := .int, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    else .error "countDistinct requires equatable argument"
  | .sum, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    match numericCoreOfScalar? sTy with
    | some numTy =>
      .ok { name := item.name, ty := numTy, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    | none => .error "sum requires numeric argument"
  | .mean, some re
  | .median, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    match numericCoreOfScalar? sTy with
    | some .int =>
      .ok { name := item.name, ty := .option .float, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    | some numTy =>
      .ok { name := item.name, ty := .option numTy, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    | none => .error "mean/median requires numeric argument"
  | .stddev, some re
  | .variance, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    if (numericCoreOfScalar? sTy).isSome then
      .ok { name := item.name, ty := .option .float, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    else .error "stddev/variance requires numeric argument"
  | .percentile p, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    let pf := Float.ofBits p.bits
    if pf.isNaN || pf < 0.0 || pf > 1.0 then
      .error "percentile parameter p must be finite in [0.0, 1.0]"
    else if (numericCoreOfScalar? sTy).isSome then
      .ok { name := item.name, ty := .option .float, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    else .error "percentile requires numeric argument"
  | .min, some re
  | .max, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    let bTy := baseOfScalar sTy
    if isOrderedScalarTy bTy.toTy then
      .ok { name := item.name, ty := .option bTy, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
    else .error "min/max requires ordered scalar argument"
  | .first, some re
  | .last, some re => do
    let (sTy, rTags) ← checkRowExpr prog env inTT.cols re
    .ok { name := item.name, ty := ensureOptionScalar sTy, tags := rTags.union baseCtx, bucketed := false, aggKind := kind }
  | _, _ => .error s!"invalid argument arity for aggregate '{item.name}'"

def applyDeriveItem (prog : Program) (env : TyEnv) (cols : List ColSpec) (item : DeriveItem) :
    Except String (List ColSpec) :=
  match item with
  | .colExpr name expr => do
    let (sTy, rTags) ← checkRowExpr prog env cols expr
    let newCol : ColSpec := { name := name, ty := sTy, tags := rTags, bucketed := false, aggKind := .raw }
    if (cols.find? (fun c => c.name == name)).isSome then
      .ok (cols.map (fun c => if c.name == name then newCol else c))
    else
      .ok (cols ++ [newCol])
  | .bucketCol name src cuts labels =>
    match cols.find? (fun c => c.name == src) with
    | some srcCol =>
      if checkBucketCuts prog srcCol.ty cuts labels then
        let newCol : ColSpec := {
          name := name
          ty := .text
          tags := srcCol.tags
          bucketed := true
          aggKind := .raw
        }
        if (cols.find? (fun c => c.name == name)).isSome then
          .ok (cols.map (fun c => if c.name == name then newCol else c))
        else
          .ok (cols ++ [newCol])
      else .error s!"invalid cuts/labels in bucketCol '{name}'"
    | none => .error s!"unknown source column '{src}' in bucketCol"

def applyWindowItem (cols : List ColSpec) (orderTags : TagSet) (item : WindowItem) :
    Except String (List ColSpec) :=
  if !item.over.all (fun k => (cols.find? (fun c => c.name == k)).isSome) ||
     !item.order.all (fun (k, _) =>
        match cols.find? (fun c => c.name == k) with
        | some c => isOrderedScalarTy (baseOfScalar c.ty).toTy
        | none => false) then
    .error s!"window item '{item.name}' references invalid partition/order columns"
  else
    let overTags := TagSet.unionList (item.over.filterMap (fun k => (cols.find? (·.name == k)).map ColSpec.tags))
    let ordKeyTags := TagSet.unionList (item.order.filterMap (fun (k, _) => (cols.find? (·.name == k)).map ColSpec.tags))
    let ctxTags := (overTags.union ordKeyTags).union orderTags
    let fnSpec? : Option (ScalarTy × TagSet) :=
      match item.fn with
      | .rowNumber => some (.int, ctxTags)
      | .rank col =>
        match cols.find? (·.name == col) with
        | some c => if isOrderedScalarTy (baseOfScalar c.ty).toTy then some (.int, c.tags.union ctxTags) else none
        | none => none
      | .lag col _ | .lead col _ =>
        match cols.find? (·.name == col) with
        | some c => some (ensureOptionScalar c.ty, c.tags.union ctxTags)
        | none => none
      | .runningSum col =>
        match cols.find? (·.name == col) with
        | some c => (numericCoreOfScalar? c.ty).map (fun nTy => (nTy, c.tags.union ctxTags))
        | none => none
      | .rollingMean col wSz =>
        if wSz == 0 then none
        else
          match cols.find? (·.name == col) with
          | some c =>
            if (numericCoreOfScalar? c.ty).isSome then some (.option .float, c.tags.union ctxTags)
            else none
          | none => none
    match fnSpec? with
    | none => .error s!"ill-typed window function in '{item.name}'"
    | some (wTy, wTags) =>
      let newCol : ColSpec := { name := item.name, ty := wTy, tags := wTags, bucketed := false, aggKind := .raw }
      if (cols.find? (·.name == item.name)).isSome then
        .ok (cols.map (fun c => if c.name == item.name then newCol else c))
      else
        .ok (cols ++ [newCol])

/-! ## Case Arm Exhaustiveness & Typing Helpers -/

def expectedCaseSpecs (prog : Program) (scrutTy : Ty) (scrutTags : TagSet) :
    Except String (List (Ident × List LTy)) :=
  match scrutTy with
  | .bool => .ok [("true", []), ("false", [])]
  | .option inner => .ok [("None", []), ("Some", [.mk inner scrutTags])]
  | .result okTy errTy =>
    .ok [("Ok", [.mk okTy scrutTags]), ("Error", [.mk errTy scrutTags])]
  | .data dName =>
    match prog.findData? dName with
    | some dDecl =>
      .ok (dDecl.ctors.map (fun c => (c.name, c.fields.map (fun f => f.addTags scrutTags))))
    | none => .error s!"unknown data type '{dName}' in Case"
  | _ => .error "Case scrutinee must be Bool, Option, Result, or Data"

/-! ## Heuristic Jump-`pc` Collector for `Join` Inference -/

/- Conservatively collects an upper bound of `pc` tags at every `Jump(target, ...)`
   reachable in `e`, used solely to propose `joinPc` before `checkExpr` verifies it. -/
mutual
def inferJumpPc (prog : Program) (target : Ident) (env : TyEnv) (curPc : TagSet) : Expr → TagSet
  | .lit _ | .var _ | .constRef _ | .tableLit _ _ | .lam _ _ _ _ => TagSet.empty
  | .letE x xLTy bnd body =>
    (inferJumpPc prog target env curPc bnd).union
      (inferJumpPc prog target ((x, xLTy) :: env) curPc body)
  | .ifE cond tBr eBr =>
    let condGuess := exprQuickTags prog env cond
    let brPc := curPc.union condGuess
    (inferJumpPc prog target env brPc tBr).union (inferJumpPc prog target env brPc eBr)
  | .caseE scrut arms =>
    let scrutGuess := exprQuickTags prog env scrut
    let armPc := curPc.union scrutGuess
    inferJumpPcArms prog target env armPc arms
  | .join lbl params rhs body =>
    if lbl == target then TagSet.empty
    else
      let subPc := inferJumpPc prog lbl env curPc body
      let rhsEnv := extendTyEnv env params
      (inferJumpPc prog target env curPc body).union
        (inferJumpPc prog target rhsEnv (curPc.union subPc) rhs)
  | .jump lbl _ =>
    if lbl == target then curPc else TagSet.empty
  | .app _ _ | .call _ _ | .tuple _ | .proj _ _ | .ctor _ _ _
  | .prim _ _ | .rel _ | .host _ _ | .stop _ _ | .fail _ => TagSet.empty

def inferJumpPcArms (prog : Program) (target : Ident) (env : TyEnv) (armPc : TagSet) :
    List CaseArm → TagSet
  | [] => TagSet.empty
  | .mk _ _ body :: rest =>
    (inferJumpPc prog target env armPc body).union
      (inferJumpPcArms prog target env armPc rest)

def exprQuickTags (prog : Program) (env : TyEnv) : Expr → TagSet
  | .lit _ | .tableLit _ _ | .lam _ _ _ _ => TagSet.empty
  | .var x => match lookupTyEnv env x with | some l => l.effectiveTags | none => TagSet.empty
  | .constRef c => match prog.findConst? c with | some d => d.lty.effectiveTags | none => TagSet.empty
  | .letE x xLTy bnd body => (exprQuickTags prog env bnd).union (exprQuickTags prog ((x, xLTy) :: env) body)
  | .ifE c t e => (exprQuickTags prog env c).union ((exprQuickTags prog env t).union (exprQuickTags prog env e))
  | .caseE s _ => exprQuickTags prog env s
  | .app f as1 => (exprQuickTags prog env f).union (exprQuickTagsList prog env as1)
  | .call fn as1 =>
    let fTags := match prog.findFun? fn with | some d => d.ret.effectiveTags | none => TagSet.empty
    fTags.union (exprQuickTagsList prog env as1)
  | .join _ _ r b => (exprQuickTags prog env r).union (exprQuickTags prog env b)
  | .jump _ as1 => exprQuickTagsList prog env as1
  | .tuple es | .ctor _ _ es | .prim _ es | .host _ es => exprQuickTagsList prog env es
  | .proj e _ => exprQuickTags prog env e
  | .rel _ | .stop _ _ | .fail _ => TagSet.empty

def exprQuickTagsList (prog : Program) (env : TyEnv) : List Expr → TagSet
  | [] => TagSet.empty
  | e :: es => (exprQuickTags prog env e).union (exprQuickTagsList prog env es)
end

/-! ## Mutual Static Checker for `Expr` and `Plan` -/

/-- Outcome of checking `Plan`: either a typed `Table(TableTy)` or a `DynamicTable(TagSet)`
    (produced exclusively by `Crosstab`). -/
inductive PlanTy where
  | table (tt : TableTy)
  | dynamic (tags : TagSet)
  deriving DecidableEq, Repr

namespace PlanTy
def toLTy (pc : TagSet) : PlanTy → LTy
  | .table tt =>
    let tt' := { tt with
      rowTags := tt.rowTags.union pc
      orderTags := tt.orderTags.union pc }
    .mk (.table tt') pc
  | .dynamic ts => .mk (.dynamicTable (ts.union pc)) pc
end PlanTy

def applyDeriveItems (prog : Program) (env : TyEnv) :
    List ColSpec → List DeriveItem → Except String (List ColSpec)
  | cols, [] => .ok cols
  | cols, item :: rest => do
    let nextCols ← applyDeriveItem prog env cols item
    applyDeriveItems prog env nextCols rest

def applyWindowItems (orderTags : TagSet) :
    List ColSpec → List WindowItem → Except String (List ColSpec)
  | cols, [] => .ok cols
  | cols, it :: rest => do
    let nextCols ← applyWindowItem cols orderTags it
    applyWindowItems orderTags nextCols rest

def checkAggItemList (prog : Program) (env : TyEnv) (inTT : TableTy) :
    List AggItem → Except String (List ColSpec)
  | [] => .ok []
  | a :: rest => do
    let hd ← checkAggItem prog env inTT a
    let tl ← checkAggItemList prog env inTT rest
    .ok (hd :: tl)

def mergeUnionCols : List ColSpec → List ColSpec → Option (List ColSpec)
  | [], [] => some []
  | lc :: lcs, rc :: rcs =>
    if decide (lc.name = rc.name) && decide (lc.ty = rc.ty) then
      (mergeUnionCols lcs rcs).map (fun rest =>
        { name := lc.name
          ty := lc.ty
          tags := lc.tags.union rc.tags
          bucketed := lc.bucketed && rc.bucketed
          aggKind := .raw } :: rest)
    else none
  | _, _ => none

/- Structural non-jumping branch inspector to propose a `Join`'s return `LTy`
   before full verification by `checkExpr`. -/
mutual
def inferBranchLTy (prog : Program) (env : TyEnv) (jenv : JoinEnv) (curPc : TagSet)
    (skipLabels : List Ident) : Expr → Option LTy
  | .lit v => (checkLiteral prog curPc v).toOption
  | .var x => (lookupTyEnv env x).map (·.addTags curPc)
  | .constRef c => (prog.findConst? c).map (·.lty.addTags curPc)
  | .letE x dLTy _ body =>
    inferBranchLTy prog ((x, dLTy.addTags curPc) :: env) jenv curPc skipLabels body
  | .ifE cond tBr eBr =>
    let brPc := curPc.union (exprQuickTags prog env cond)
    match inferBranchLTy prog env jenv brPc skipLabels tBr,
          inferBranchLTy prog env jenv brPc skipLabels eBr with
    | some l1, some l2 => some (.mk l1.ty ((l1.tags.union l2.tags).union brPc))
    | some l1, none => some (l1.addTags brPc)
    | none, some l2 => some (l2.addTags brPc)
    | none, none => none
  | .caseE scrut arms =>
    let armPc := curPc.union (exprQuickTags prog env scrut)
    inferBranchArms prog env jenv armPc skipLabels arms
  | .lam params fnPc retLTy _ => some (.mk (.fn (params.map Prod.snd) fnPc retLTy) curPc)
  | .call fn _ => (prog.findFun? fn).map (·.ret.addTags curPc)
  | .app fnE _ =>
    match inferBranchLTy prog env jenv curPc skipLabels fnE with
    | some (.mk (.fn _ _ ret) fTs) => some (ret.addTags (curPc.union fTs))
    | _ => none
  | .join lbl params subRhs subBody =>
    let subEnv := extendTyEnv env params
    match inferBranchLTy prog subEnv jenv curPc (lbl :: skipLabels) subRhs with
    | some l => some l
    | none => inferBranchLTy prog env jenv curPc (lbl :: skipLabels) subBody
  | .jump lbl _ =>
    if skipLabels.contains lbl then none
    else (lookupJoinEnv jenv lbl).map (·.retLTy)
  | .tuple es =>
    (inferBranchList prog env jenv curPc skipLabels es).map (fun ls => .mk (.tuple ls) curPc)
  | .proj e idx =>
    match inferBranchLTy prog env jenv curPc skipLabels e with
    | some (.mk (.tuple ls) tTs) => ls[idx]?.map (·.addTags (tTs.union curPc))
    | _ => none
  | .ctor tName _ as1 =>
    some (.mk (.data tName) ((exprQuickTagsList prog env as1).union curPc))
  | .tableLit s _ => some (.mk (.table s) curPc)
  | .prim op as1 =>
    match inferBranchList prog env jenv curPc skipLabels as1 with
    | some ltys => (checkPrimOp prog curPc op ltys).toOption
    | none => none
  | .rel p => inferQuickPlanLTy prog env curPc skipLabels p
  | .host op as1 =>
    match inferBranchList prog env jenv curPc skipLabels as1 with
    | some ltys => (checkHostOp prog curPc true op ltys).toOption
    | none => none
  | .stop _ _ | .fail _ => some (.mk .unit curPc)

def inferBranchList (prog : Program) (env : TyEnv) (jenv : JoinEnv) (curPc : TagSet)
    (skipLabels : List Ident) : List Expr → Option (List LTy)
  | [] => some []
  | e :: rest => do
    let h ← inferBranchLTy prog env jenv curPc skipLabels e
    let t ← inferBranchList prog env jenv curPc skipLabels rest
    some (h :: t)

def inferBranchArms (prog : Program) (env : TyEnv) (jenv : JoinEnv) (armPc : TagSet)
    (skipLabels : List Ident) : List CaseArm → Option LTy
  | [] => none
  | .mk _ _ body :: rest =>
    match inferBranchLTy prog env jenv armPc skipLabels body,
          inferBranchArms prog env jenv armPc skipLabels rest with
    | some l1, some l2 => some (.mk l1.ty ((l1.tags.union l2.tags).union armPc))
    | some l1, none => some (l1.addTags armPc)
    | none, some l2 => some (l2.addTags armPc)
    | none, none => none

def inferQuickPlanLTy (prog : Program) (env : TyEnv) (curPc : TagSet)
    (skipLabels : List Ident) : Plan → Option LTy
  | .sourceExpr e =>
    match inferBranchLTy prog env [] curPc skipLabels e with
    | some (.mk (.table tt) eTs) =>
      let extra := eTs.union curPc
      some (PlanTy.toLTy curPc (.table { tt with
        rowTags := tt.rowTags.union extra
        orderTags := tt.orderTags.union extra }))
    | _ => none
  | .sourceDB cap _ s =>
    let extra := match inferBranchLTy prog env [] curPc skipLabels cap with
      | some l => l.tags.union curPc
      | none => curPc
    some (PlanTy.toLTy curPc (.table { s with
      rowTags := s.rowTags.union extra
      orderTags := s.orderTags.union extra }))
  | .select p selCols =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let outCols := selCols.filterMap (fun n => (tt.findCol? n).map (fun c => { c with aggKind := .raw }))
      some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
    | _ => none
  | .drop p dropCols =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let outCols := (tt.cols.filter (fun c => !dropCols.contains c.name)).map (fun c => { c with aggKind := .raw })
      some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
    | _ => none
  | .rename p pairs =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let outCols := tt.cols.map (fun c =>
        match pairs.find? (fun (_, oldN) => oldN == c.name) with
        | some (newN, _) => { c with name := newN, aggKind := .raw }
        | none => { c with aggKind := .raw })
      some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
    | _ => none
  | .derive p items =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      match applyDeriveItems prog env (tt.cols.map (fun c => { c with aggKind := .raw })) items with
      | .ok outCols =>
        some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
      | .error _ => none
    | _ => none
  | .filter p pred =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let pTags := match checkRowExpr prog env tt.cols pred with | .ok (_, ts) => ts | .error _ => TagSet.empty
      some (PlanTy.toLTy curPc (.table {
        cols := tt.cols.map (fun c => { c with aggKind := .raw })
        rowTags := tt.rowTags.union pTags
        orderTags := tt.orderTags }))
    | _ => none
  | .distinct p cols =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let keyNames := if cols.isEmpty then tt.cols.map ColSpec.name else cols
      let keyTags := TagSet.unionList (keyNames.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
      let ordDep := if keyNames.length == tt.cols.length then TagSet.empty else tt.orderTags
      some (PlanTy.toLTy curPc (.table {
        cols := tt.cols.map (fun c => { c with aggKind := .raw })
        rowTags := (tt.rowTags.union keyTags).union ordDep
        orderTags := tt.orderTags }))
    | _ => none
  | .sort p keys =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let sortKeyTags := TagSet.unionList ((keys.map Prod.fst).filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
      some (PlanTy.toLTy curPc (.table {
        cols := tt.cols.map (fun c => { c with aggKind := .raw })
        rowTags := tt.rowTags
        orderTags := tt.orderTags.union sortKeyTags }))
    | _ => none
  | .limit p _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      some (PlanTy.toLTy curPc (.table {
        cols := tt.cols.map (fun c => { c with aggKind := .raw })
        rowTags := tt.rowTags.union tt.orderTags
        orderTags := tt.orderTags }))
    | _ => none
  | .join kind l r on suffixes =>
    match inferQuickPlanLTy prog env curPc skipLabels l,
          inferQuickPlanLTy prog env curPc skipLabels r with
    | some (.mk (.table lTT) _), some (.mk (.table rTT) _) =>
      match resolveJoinPairs lTT rTT on, buildJoinedCols kind lTT.cols rTT.cols on suffixes with
      | .ok keyPairs, .ok joinedCols =>
        let onTags := TagSet.unionList (keyPairs.map (fun (lc, rc) => lc.tags.union rc.tags))
        let newOrderTags := match kind with | .semi | .anti => lTT.orderTags | _ => lTT.orderTags.union rTT.orderTags
        some (PlanTy.toLTy curPc (.table {
          cols := joinedCols
          rowTags := (lTT.rowTags.union rTT.rowTags).union onTags
          orderTags := newOrderTags }))
      | _, _ => none
    | _, _ => none
  | .union l r =>
    match inferQuickPlanLTy prog env curPc skipLabels l,
          inferQuickPlanLTy prog env curPc skipLabels r with
    | some (.mk (.table lTT) _), some (.mk (.table rTT) _) =>
      (mergeUnionCols lTT.cols rTT.cols).map (fun outCols =>
        PlanTy.toLTy curPc (.table {
          cols := outCols
          rowTags := lTT.rowTags.union rTT.rowTags
          orderTags := lTT.orderTags.union rTT.orderTags }))
    | _, _ => none
  | .groupBy p keys =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let keyTags := TagSet.unionList (keys.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
      let outCols := tt.cols.map (fun c =>
        if keys.contains c.name then { c with aggKind := .groupKey } else { c with aggKind := .raw })
      some (PlanTy.toLTy curPc (.table {
        cols := outCols, rowTags := tt.rowTags.union keyTags, orderTags := tt.orderTags, groupedBy := some keys }))
    | _ => none
  | .summarize p aggs distinctKey =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let groupKeys := tt.groupedBy.getD []
      let dkTags := match distinctKey with
        | none => TagSet.empty
        | some dk => match tt.findCol? dk with | some c => c.tags | none => TagSet.empty
      let keyCols := (tt.cols.filter (fun c => groupKeys.contains c.name)).map (fun c => { c with aggKind := .groupKey })
      match checkAggItemList prog env tt aggs with
      | .ok aggCols =>
        some (PlanTy.toLTy curPc (.table {
          cols := keyCols ++ aggCols
          rowTags := tt.rowTags.union dkTags
          orderTags := TagSet.empty
          groupedBy := some groupKeys
          summarized := true
          distinctBy := distinctKey }))
      | .error _ => none
    | _ => none
  | .suppressSmallGroups p _ _ _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let rawKeyTags := TagSet.unionList
        ((tt.cols.filter (fun c => decide (c.aggKind = .groupKey) && !c.bucketed)).map ColSpec.tags)
      let outCols := tt.cols.map (fun c =>
        match c.aggKind with
        | .groupKey => if c.bucketed then { c with tags := curPc, aggKind := .raw } else { c with aggKind := .raw }
        | .blending => { c with tags := curPc, aggKind := .raw }
        | .nonBlending | .raw => { c with aggKind := .raw })
      some (PlanTy.toLTy curPc (.table {
        cols := outCols, rowTags := rawKeyTags.union curPc, orderTags := tt.orderTags }))
    | _ => none
  | .window p items =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      match applyWindowItems tt.orderTags (tt.cols.map (fun c => { c with aggKind := .raw })) items with
      | .ok outCols =>
        some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
      | .error _ => none
    | _ => none
  | .fillGaps p col _ over _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      match tt.findCol? col with
      | some tCol =>
        let overTags := TagSet.unionList (over.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
        let newRowTags := (tt.rowTags.union tCol.tags).union overTags
        let outCols := tt.cols.map (fun c =>
          if c.name == col || over.contains c.name then { c with aggKind := .raw, bucketed := false }
          else { c with tags := (c.tags.union newRowTags).union tt.orderTags, aggKind := .raw, bucketed := false })
        some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := newRowTags, orderTags := TagSet.empty }))
      | none => none
    | _ => none
  | .pivotWider p namesFrom valuesFrom staticCols _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      match tt.findCol? namesFrom, tt.findCol? valuesFrom with
      | some nCol, some vCol =>
        let idCols := (tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map
          (fun c => { c with aggKind := .raw })
        let idTags := TagSet.unionList (idCols.map ColSpec.tags)
        let newRowTags := (tt.rowTags.union nCol.tags).union idTags
        let cellTags := ((nCol.tags.union vCol.tags).union newRowTags).union tt.orderTags
        let pivotedCols := staticCols.map (fun sc =>
          { name := sc, ty := vCol.ty, tags := cellTags, bucketed := false, aggKind := .raw })
        some (PlanTy.toLTy curPc (.table {
          cols := idCols ++ pivotedCols, rowTags := newRowTags, orderTags := TagSet.empty }))
      | _, _ => none
    | _ => none
  | .crosstab p rowsCol colsCol valuesCol _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      match tt.findCol? rowsCol, tt.findCol? colsCol, tt.findCol? valuesCol with
      | some rCol, some cCol, some vCol =>
        let dtTags := ((((tt.rowTags.union tt.orderTags).union rCol.tags).union cCol.tags).union vCol.tags).union curPc
        some (PlanTy.toLTy curPc (.dynamic dtTags))
      | _, _, _ => none
    | _ => none
  | .redact p col _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let outCols := tt.cols.map (fun c =>
        if c.name == col then { c with ty := .text, tags := curPc, bucketed := false, aggKind := .raw }
        else { c with aggKind := .raw })
      some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
    | _ => none
  | .pseudonymize p col _ =>
    match inferQuickPlanLTy prog env curPc skipLabels p with
    | some (.mk (.table tt) _) =>
      let outCols := tt.cols.map (fun c =>
        if c.name == col then
          { c with ty := .text, tags := (c.tags.remove "pii").union curPc, bucketed := false, aggKind := .raw }
        else { c with aggKind := .raw })
      some (PlanTy.toLTy curPc (.table { cols := outCols, rowTags := tt.rowTags, orderTags := tt.orderTags }))
    | _ => none
end

def inferJoinRetLTy (prog : Program) (env : TyEnv) (jenv : JoinEnv) (curPc : TagSet)
    (skipLabel : Ident) (rhs : Expr) (body : Expr) : Option LTy :=
  match inferBranchLTy prog env jenv curPc [skipLabel] rhs with
  | some lty => some lty
  | none => inferBranchLTy prog env jenv curPc [skipLabel] body

mutual
def checkExpr (prog : Program) (env : TyEnv) (jenv : JoinEnv) (pc : TagSet) (inSpec : Bool)
    (expr : Expr) : Except String LTy :=
  match expr with
  | .lit v => checkLiteral prog pc v
  | .var name =>
    match lookupTyEnv env name with
    | some lty => .ok (lty.addTags pc)
    | none => .error s!"unbound variable '{name}'"
  | .constRef name =>
    match prog.findConst? name with
    | some cDecl => .ok (cDecl.lty.addTags pc)
    | none => .error s!"unknown constant '{name}'"
  | .letE name declLTy bound body => do
    if !validLTy prog declLTy then
      .error s!"invalid type annotation on let '{name}'"
    else if !noFreeJumps [] bound then
      .error s!"non-tail jump inside bound expression of let '{name}'"
    else do
      let bLTy ← checkExpr prog env [] pc inSpec bound
      if !ltySubtype bLTy declLTy then
        .error s!"let '{name}' bound type mismatch"
      else
        checkExpr prog ((name, declLTy.addTags pc) :: env) jenv pc inSpec body
  | .ifE cond tBr eBr => do
    if !noFreeJumps [] cond then
      .error "non-tail jump inside if condition"
    else do
      let condLTy ← checkExpr prog env [] pc inSpec cond
      if decide (condLTy.ty = .bool) then
        let brPc := pc.union condLTy.tags
        let tLTy ← checkExpr prog env jenv brPc inSpec tBr
        let eLTy ← checkExpr prog env jenv brPc inSpec eBr
        if decide (tLTy.ty = eLTy.ty) then
          .ok (.mk tLTy.ty ((tLTy.tags.union eLTy.tags).union brPc))
        else .error "if branches have mismatched structural types"
      else .error "if condition must have type Bool"
  | .caseE scrut arms => do
    if !noFreeJumps [] scrut then
      .error "non-tail jump inside case scrutinee"
    else do
      let scrutLTy ← checkExpr prog env [] pc inSpec scrut
      let scrutTags := scrutLTy.effectiveTags
      let armPc := pc.union scrutTags
      let specs ← expectedCaseSpecs prog scrutLTy.ty scrutTags
      if !distinctIdents (arms.map (fun (.mk c _ _) => c)) || arms.length != specs.length then
        .error "case arms must be exhaustive and duplicate-free"
      else do
        let armLTys ← checkCaseArms prog env jenv armPc inSpec specs arms
        match armLTys with
        | [] => .error "empty case arms"
        | firstLTy :: restLTys =>
          if restLTys.all (fun l => decide (l.ty = firstLTy.ty)) then
            let unionArmTags := TagSet.unionList (armLTys.map LTy.tags)
            .ok (.mk firstLTy.ty (unionArmTags.union armPc))
          else .error "case arms have mismatched return types"
  | .lam params fnPc retLTy body => do
    if !distinctIdents (params.map Prod.fst) ||
       !params.all (fun (_, l) => validLTy prog l) ||
       !validTagSet prog fnPc ||
       !validLTy prog retLTy then
      .error "invalid lambda parameter or return types"
    else if !noFreeJumps [] body then
      .error "lambda cannot jump to enclosing outer join point"
    else if !fnPc.subset retLTy.effectiveTags then
      .error "lambda caller pc bound must be reflected in return type tags"
    else do
      let bodyEnv := extendTyEnv env params
      let bodyLTy ← checkExpr prog bodyEnv [] fnPc inSpec body
      if ltySubtype bodyLTy retLTy then
        .ok (.mk (.fn (params.map Prod.snd) fnPc retLTy) pc)
      else .error "lambda body type/tags do not match declared return LTy"
  | .app fnExpr args => do
    if !noFreeJumps [] fnExpr || !noFreeJumpsList args then
      .error "non-tail jump in function application"
    else do
      let fnLTy ← checkExpr prog env [] pc inSpec fnExpr
      let argLTys ← checkExprList prog env pc inSpec args
      match fnLTy.ty with
      | .fn paramLTys fnPc retLTy =>
        let callPc := pc.union fnLTy.tags
        if !callPc.subset fnPc then
          .error "caller pc / closure taint exceeds function pc bound"
        else if argLTys.length != paramLTys.length then
          .error "closure call arity mismatch"
        else if !(List.zip argLTys paramLTys).all (fun (a, p) => ltySubtype a p) then
          .error "closure call argument type/tag mismatch"
        else
          .ok (retLTy.addTags callPc)
      | _ => .error "application target is not a function"
  | .call fnName args => do
    if !noFreeJumpsList args then
      .error "non-tail jump in call arguments"
    else do
      let argLTys ← checkExprList prog env pc inSpec args
      match prog.findFun? fnName with
      | some fDecl =>
        if fDecl.kind.isSpec && !inSpec then
          .error s!"ordinary function cannot call spec function '{fnName}'"
        else if !pc.subset fDecl.pc then
          .error s!"caller pc exceeds function '{fnName}' pc bound"
        else if argLTys.length != fDecl.params.length then
          .error s!"call to '{fnName}' arity mismatch"
        else if !(List.zip argLTys (fDecl.params.map Prod.snd)).all (fun (a, p) => ltySubtype a p) then
          .error s!"call to '{fnName}' argument type/tag mismatch"
        else
          .ok (fDecl.ret.addTags pc)
      | none => .error s!"unknown function '{fnName}'"
  | .join label params rhs body => do
    if !distinctIdents (params.map Prod.fst) || !params.all (fun (_, l) => validLTy prog l) then
      .error s!"invalid parameters on join point '{label}'"
    else
      let guess1 := pc.union (inferJumpPc prog label env pc body)
      let rhsEnv := extendTyEnv env params
      let joinPc := guess1.union (inferJumpPc prog label rhsEnv guess1 rhs)
      match inferJoinRetLTy prog rhsEnv jenv joinPc label rhs body with
      | none => .error s!"could not determine return type of join point '{label}'"
      | some candRetLTy => do
        let retLTy := candRetLTy.addTags joinPc
        if !validLTy prog retLTy then
          .error s!"invalid inferred return type for join '{label}'"
        else do
          let sig : JoinSig := { params := params, joinPc := joinPc, retLTy := retLTy }
          let jenv' := (label, sig) :: jenv
          let rhsLTy ← checkExpr prog rhsEnv jenv' joinPc inSpec rhs
          let bodyLTy ← checkExpr prog env jenv' pc inSpec body
          if decide (rhsLTy.ty = retLTy.ty) && decide (bodyLTy.ty = retLTy.ty) then
            let finalTags := (retLTy.tags.union rhsLTy.tags).union (bodyLTy.tags.union pc)
            -- Ensure all jumps' `joinPc` is contained in `retLTy.tags` (already `joinPc ⊆ retLTy.tags`)
            if finalTags.subset retLTy.tags then
              .ok retLTy
            else do
              -- Re-verify at widened `finalRet` so `Jump` returns the exact unified `LTy`
              let finalRet : LTy := .mk retLTy.ty finalTags
              let sig2 : JoinSig := { params := params, joinPc := joinPc, retLTy := finalRet }
              let jenv2 := (label, sig2) :: jenv
              let rhsLTy2 ← checkExpr prog rhsEnv jenv2 joinPc inSpec rhs
              let bodyLTy2 ← checkExpr prog env jenv2 pc inSpec body
              if ltySubtype rhsLTy2 finalRet && ltySubtype bodyLTy2 finalRet then
                .ok finalRet
              else .error s!"join point '{label}' return label mismatch"
          else .error s!"join point '{label}' body and rhs types differ"
  | .jump label args => do
    if !noFreeJumpsList args then
      .error "non-tail jump inside jump arguments"
    else do
      let argLTys ← checkExprList prog env pc inSpec args
      match lookupJoinEnv jenv label with
      | some sig =>
        if !pc.subset sig.joinPc then
          .error s!"jump to '{label}' from pc exceeding joinPc"
        else if !pc.subset sig.retLTy.effectiveTags then
          .error s!"jump to '{label}' pc not reflected in join return tags"
        else if argLTys.length != sig.params.length then
          .error s!"jump to '{label}' arity mismatch"
        else if !(List.zip argLTys (sig.params.map Prod.snd)).all (fun (a, p) =>
            ltySubtype (a.addTags pc) p && pc.subset p.tags) then
          .error s!"jump to '{label}' argument type or pc-taint mismatch"
        else
          .ok sig.retLTy
      | none => .error s!"jump to unbound or non-tail label '{label}'"
  | .tuple elems => do
    if !noFreeJumpsList elems then
      .error "non-tail jump inside tuple"
    else do
      let elemLTys ← checkExprList prog env pc inSpec elems
      .ok (.mk (.tuple elemLTys) pc)
  | .proj tup idx => do
    if !noFreeJumps [] tup then
      .error "non-tail jump inside tuple projection"
    else do
      let tupLTy ← checkExpr prog env [] pc inSpec tup
      match tupLTy.ty with
      | .tuple elemLTys =>
        match elemLTys[idx]? with
        | some eLTy => .ok (eLTy.addTags (tupLTy.tags.union pc))
        | none => .error s!"tuple projection index {idx} out of bounds"
      | _ => .error "projection requires Tuple operand"
  | .ctor typeName ctorName args => do
    if !noFreeJumpsList args then
      .error "non-tail jump inside constructor arguments"
    else do
      let argLTys ← checkExprList prog env pc inSpec args
      match prog.findData? typeName with
      | some dDecl =>
        match dDecl.ctors.find? (fun c => c.name == ctorName) with
        | some cDecl =>
          if argLTys.length != cDecl.fields.length then
            .error s!"constructor '{ctorName}' arity mismatch"
          else if !(List.zip argLTys cDecl.fields).all (fun (a, f) =>
              decide (a.ty = f.ty)) then
            .error s!"constructor '{ctorName}' field type mismatch"
          else
            -- Propagate any excess argument sensitivity tags onto the enclosing Data value
            -- and enforce declared field tag bounds when argument tags fit
            let extraArgTags := TagSet.unionList (argLTys.map LTy.effectiveTags)
            .ok (.mk (.data typeName) (extraArgTags.union pc))
        | none => .error s!"unknown constructor '{ctorName}' for '{typeName}'"
      | none => .error s!"unknown data type '{typeName}'"
  | .tableLit schema rows =>
    if !validTableTy prog schema || schema.summarized || schema.groupedBy.isSome || schema.distinctBy.isSome then
      .error "invalid TableTy in tableLit"
    else if !schema.cols.all (fun c => !c.bucketed && decide (c.aggKind = .raw)) then
      .error "tableLit columns must have bucketed = false and aggKind = raw"
    else if !rows.all (checkRowLit prog schema.cols) then
      .error "tableLit row cells do not match declared TableTy"
    else
      let outSchema := { schema with
        rowTags := schema.rowTags.union pc
        orderTags := schema.orderTags.union pc }
      .ok (.mk (.table outSchema) pc)
  | .prim op args => do
    if !noFreeJumpsList args then
      .error "non-tail jump inside primitive arguments"
    else do
      let argLTys ← checkExprList prog env pc inSpec args
      checkPrimOp prog pc op argLTys
  | .rel plan => do
    if !noFreeJumpsPlan plan then
      .error "non-tail jump inside relational plan"
    else do
      let pTy ← checkPlan prog env pc inSpec plan
      .ok (pTy.toLTy pc)
  | .host op args => do
    if !noFreeJumpsList args then
      .error "non-tail jump inside host arguments"
    else do
      let argLTys ← checkExprList prog env pc inSpec args
      checkHostOp prog pc inSpec op argLTys
  | .stop _ detail => do
    match detail with
    | none => .ok (.mk .unit pc)
    | some d =>
      if !noFreeJumps [] d then
        .error "non-tail jump inside stop detail"
      else do
        let dLTy ← checkExpr prog env [] pc inSpec d
        if isEquatableTy dLTy.ty then .ok (.mk .unit pc)
        else .error "stop detail must be a printable/redacted value type"
  | .fail msg => do
    if !inSpec then
      .error "Fail is only permitted inside spec functions (test/example/promise)"
    else if !noFreeJumps [] msg then
      .error "non-tail jump inside fail message"
    else do
      let mLTy ← checkExpr prog env [] pc inSpec msg
      if decide (mLTy.ty = .text) && mLTy.tags.subset pc then
        .ok (.mk .unit pc)
      else .error "Fail message must be Text with tags bounded by pc"
  termination_by structural expr

def checkExprList (prog : Program) (env : TyEnv) (pc : TagSet) (inSpec : Bool)
    (exprs : List Expr) : Except String (List LTy) :=
  match exprs with
  | [] => .ok []
  | e :: es => do
    let hd ← checkExpr prog env [] pc inSpec e
    let tl ← checkExprList prog env pc inSpec es
    .ok (hd :: tl)
  termination_by structural exprs

def checkCaseArms (prog : Program) (env : TyEnv) (jenv : JoinEnv) (armPc : TagSet)
    (inSpec : Bool) (specs : List (Ident × List LTy))
    (arms : List CaseArm) : Except String (List LTy) :=
  match arms with
  | [] => .ok []
  | .mk cName binders body :: rest =>
    match specs.find? (fun (sn, _) => sn == cName) with
    | some (_, fieldLTys) =>
      if !distinctIdents binders || binders.length != fieldLTys.length then
        .error s!"case arm '{cName}' binder count or duplicate mismatch"
      else do
        let armBindings := List.zip binders (fieldLTys.map (fun f => f.addTags armPc))
        let hd ← checkExpr prog (extendTyEnv env armBindings) jenv armPc inSpec body
        let tl ← checkCaseArms prog env jenv armPc inSpec specs rest
        .ok (hd :: tl)
    | none => .error s!"unexpected constructor '{cName}' in Case"
  termination_by structural arms

/- Static schema & privacy checker for pure relational `Plan`s. -/
def checkPlan (prog : Program) (env : TyEnv) (pc : TagSet) (inSpec : Bool)
    (plan : Plan) : Except String PlanTy :=
  match plan with
  | .sourceExpr e => do
    let lty ← checkExpr prog env [] pc inSpec e
    match lty.ty with
    | .table tt =>
      let extra := lty.tags.union pc
      .ok (.table { tt with
        rowTags := tt.rowTags.union extra
        orderTags := tt.orderTags.union extra })
    | _ => .error "SourceExpr requires Table expression"
  | .sourceDB cap _ schema => do
    let capLTy ← checkExpr prog env [] pc inSpec cap
    match capLTy.ty with
    | .readDB _ =>
      if validTableTy prog schema && !schema.summarized && schema.groupedBy.isNone &&
         schema.distinctBy.isNone &&
         schema.cols.all (fun c => !c.bucketed && decide (c.aggKind = .raw)) then
        let extra := capLTy.tags.union pc
        .ok (.table { schema with
          rowTags := schema.rowTags.union extra
          orderTags := schema.orderTags.union extra })
      else .error "invalid initial schema in SourceDB"
    | _ => .error "SourceDB requires ReadDB capability"
  | .select input selCols => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      if selCols.isEmpty || !distinctIdents selCols then
        .error "Select requires non-empty distinct column list"
      else if !selCols.all (fun n => (tt.findCol? n).isSome) then
        .error "Select references missing column"
      else
        let outCols := selCols.filterMap (fun n =>
          (tt.findCol? n).map (fun c => { c with aggKind := .raw }))
        .ok (.table {
          cols := outCols
          rowTags := tt.rowTags
          orderTags := tt.orderTags
          groupedBy := none
          summarized := false
          distinctBy := none })
    | .dynamic _ => .error "cannot Select on DynamicTable"
  | .drop input dropCols => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      if !distinctIdents dropCols || !dropCols.all (fun n => (tt.findCol? n).isSome) then
        .error "Drop references unknown or duplicate columns"
      else
        let outCols := (tt.cols.filter (fun c => !dropCols.contains c.name)).map
          (fun c => { c with aggKind := .raw })
        if outCols.isEmpty then .error "Drop cannot remove every column of a Table"
        else
          .ok (.table {
            cols := outCols
            rowTags := tt.rowTags
            orderTags := tt.orderTags
            groupedBy := none
            summarized := false
            distinctBy := none })
    | .dynamic _ => .error "cannot Drop on DynamicTable"
  | .rename input pairs => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      let newNames := pairs.map Prod.fst
      let oldNames := pairs.map Prod.snd
      if !distinctIdents newNames || !distinctIdents oldNames ||
         !oldNames.all (fun oldN => (tt.findCol? oldN).isSome) then
        .error "Rename has duplicate or missing columns"
      else
        let outCols := tt.cols.map (fun c =>
          match pairs.find? (fun (_, oldN) => oldN == c.name) with
          | some (newN, _) => { c with name := newN, aggKind := .raw }
          | none => { c with aggKind := .raw })
        if distinctIdents (outCols.map ColSpec.name) then
          .ok (.table {
            cols := outCols
            rowTags := tt.rowTags
            orderTags := tt.orderTags
            groupedBy := none
            summarized := false
            distinctBy := none })
        else .error "Rename produced colliding column names"
    | .dynamic _ => .error "cannot Rename on DynamicTable"
  | .derive input items => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      let outCols ← applyDeriveItems prog env (tt.cols.map (fun c => { c with aggKind := .raw })) items
      if distinctIdents (outCols.map ColSpec.name) then
        .ok (.table {
          cols := outCols
          rowTags := tt.rowTags
          orderTags := tt.orderTags
          groupedBy := none
          summarized := false
          distinctBy := none })
      else .error "Derive produced duplicate column names"
    | .dynamic _ => .error "cannot Derive on DynamicTable"
  | .filter input pred => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt => do
      let (pTy, pTags) ← checkRowExpr prog env tt.cols pred
      if decide (pTy = .bool) then
        .ok (.table {
          cols := tt.cols.map (fun c => { c with aggKind := .raw })
          rowTags := tt.rowTags.union pTags
          orderTags := tt.orderTags
          groupedBy := none
          summarized := false
          distinctBy := none })
      else .error "Filter predicate must return Bool"
    | .dynamic _ => .error "cannot Filter on DynamicTable"
  | .distinct input cols => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      let keyNames := if cols.isEmpty then tt.cols.map ColSpec.name else cols
      if !distinctIdents keyNames || !keyNames.all (fun k =>
          match tt.findCol? k with
          | some c => isEquatableTy c.ty.toTy
          | none => false) then
        .error "Distinct references missing or non-equatable columns"
      else
        let keyTags := TagSet.unionList (keyNames.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
        -- If `cols` is a strict subset of `tt.cols`, which duplicate row survives depends on `orderTags`
        let ordDep := if keyNames.length == tt.cols.length then TagSet.empty else tt.orderTags
        .ok (.table {
          cols := tt.cols.map (fun c => { c with aggKind := .raw })
          rowTags := (tt.rowTags.union keyTags).union ordDep
          orderTags := tt.orderTags
          groupedBy := none
          summarized := false
          distinctBy := none })
    | .dynamic _ => .error "cannot Distinct on DynamicTable"
  | .sort input keys => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      let keyNames := keys.map Prod.fst
      if keys.isEmpty || !distinctIdents keyNames ||
         !keyNames.all (fun k =>
            match tt.findCol? k with
            | some c => isOrderedScalarTy (baseOfScalar c.ty).toTy
            | none => false) then
        .error "Sort requires non-empty distinct ordered columns"
      else
        let sortKeyTags := TagSet.unionList (keyNames.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
        -- Stable sort preserves prior relative tie order, so `orderTags` accumulates `tt.orderTags`
        .ok (.table {
          cols := tt.cols.map (fun c => { c with aggKind := .raw })
          rowTags := tt.rowTags
          orderTags := tt.orderTags.union sortKeyTags
          groupedBy := none
          summarized := false
          distinctBy := none })
    | .dynamic _ => .error "cannot Sort on DynamicTable"
  | .limit input _ => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      .ok (.table {
        cols := tt.cols.map (fun c => { c with aggKind := .raw })
        rowTags := tt.rowTags.union tt.orderTags
        orderTags := tt.orderTags
        groupedBy := none
        summarized := false
        distinctBy := none })
    | .dynamic _ => .error "cannot Limit on DynamicTable"
  | .join kind leftP rightP on suffixes => do
    let lPlan ← checkPlan prog env pc inSpec leftP
    let rPlan ← checkPlan prog env pc inSpec rightP
    match lPlan, rPlan with
    | .table lTT, .table rTT => do
      let keyPairs ← resolveJoinPairs lTT rTT on
      let onTags := TagSet.unionList (keyPairs.map (fun (lc, rc) => lc.tags.union rc.tags))
      let joinedCols ← buildJoinedCols kind lTT.cols rTT.cols on suffixes
      let newRowTags := (lTT.rowTags.union rTT.rowTags).union onTags
      let newOrderTags :=
        match kind with
        | .semi | .anti => lTT.orderTags
        | _ => lTT.orderTags.union rTT.orderTags
      .ok (.table {
        cols := joinedCols
        rowTags := newRowTags
        orderTags := newOrderTags
        groupedBy := none
        summarized := false
        distinctBy := none })
    | _, _ => .error "Join inputs must be statically typed Tables"
  | .union leftP rightP => do
    let lPlan ← checkPlan prog env pc inSpec leftP
    let rPlan ← checkPlan prog env pc inSpec rightP
    match lPlan, rPlan with
    | .table lTT, .table rTT =>
      match mergeUnionCols lTT.cols rTT.cols with
      | some outCols =>
        .ok (.table {
          cols := outCols
          rowTags := lTT.rowTags.union rTT.rowTags
          orderTags := lTT.orderTags.union rTT.orderTags
          groupedBy := none
          summarized := false
          distinctBy := none })
      | none => .error "Union requires matching column names and types"
    | _, _ => .error "Union inputs must be statically typed Tables"
  | .groupBy input keys => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      if !distinctIdents keys || !keys.all (fun k =>
          match tt.findCol? k with
          | some c => isOrderedScalarTy (baseOfScalar c.ty).toTy || isEquatableTy c.ty.toTy
          | none => false) then
        .error "GroupBy references duplicate, missing, or non-equatable key columns"
      else
        let keyTags := TagSet.unionList (keys.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
        let outCols := tt.cols.map (fun c =>
          if keys.contains c.name then { c with aggKind := .groupKey }
          else { c with aggKind := .raw })
        .ok (.table {
          cols := outCols
          rowTags := tt.rowTags.union keyTags
          orderTags := tt.orderTags
          groupedBy := some keys
          summarized := false
          distinctBy := none })
    | .dynamic _ => .error "cannot GroupBy on DynamicTable"
  | .summarize input aggs distinctKey => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      let groupKeys := tt.groupedBy.getD []
      if aggs.isEmpty then
        .error "Summarize requires at least one aggregate"
      else do
        let dkTags ← match distinctKey with
          | none => .ok TagSet.empty
          | some dk =>
            match tt.findCol? dk with
            | some c =>
              if isEquatableTy c.ty.toTy then .ok c.tags
              else .error s!"distinctKey '{dk}' must be equatable"
            | none => .error s!"unknown distinctKey '{dk}' in Summarize"
        let keyCols := (tt.cols.filter (fun c => groupKeys.contains c.name)).map
          (fun c => { c with aggKind := .groupKey })
        let aggCols ← checkAggItemList prog env tt aggs
        let outCols := keyCols ++ aggCols
        if !distinctIdents (outCols.map ColSpec.name) then
          .error "Summarize output column names must be strictly unique"
        else
          -- Canonical group-key ordering clears prior `orderTags`
          .ok (.table {
            cols := outCols
            rowTags := tt.rowTags.union dkTags
            orderTags := TagSet.empty
            groupedBy := some groupKeys
            summarized := true
            distinctBy := distinctKey })
    | .dynamic _ => .error "cannot Summarize on DynamicTable"
  | .suppressSmallGroups input minK distinctBy mode => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      let floor := prog.minGroupFloor
      if !tt.summarized then
        .error "SuppressSmallGroups requires immediately summarized input table (summarized = true)"
      else if minK < floor then
        .error s!"SuppressSmallGroups min_k ({minK}) is below required minimum floor ({floor})"
      else if distinctBy.isSome && decide (distinctBy ≠ tt.distinctBy) then
        .error "SuppressSmallGroups distinct_by must match Summarize distinct_key"
      else
        -- Audited declassification rules (`docs/design/privacy.md` §3.1.4):
        -- 1. Bucketed group-by keys clear tags to []
        -- 2. Blending aggregates (`count`, `count_distinct`, `sum`, `mean`, `stddev`, `variance`) clear tags to []
        -- 3. Non-bucketed group-by keys NEVER clear their tags
        -- 4. Non-blending extremes & order statistics (`median`, `percentile`, `min`, `max`, `first`, `last`) NEVER clear their tags
        -- 5. `rowTags` clears to the union of remaining non-bucketed group-by key tags (plus outer `pc`)
        -- 6. In `maskComplementary` mode, aggregate columns become optional (`T?`) so suppressed cells mask to `none`
        let rawKeyTags := TagSet.unionList
          ((tt.cols.filter (fun c => decide (c.aggKind = .groupKey) && !c.bucketed)).map ColSpec.tags)
        let newRowTags := rawKeyTags.union pc
        let outCols := tt.cols.map (fun c =>
          let base :=
            match c.aggKind with
            | .groupKey =>
              if c.bucketed then { c with tags := pc, aggKind := .raw }
              else { c with aggKind := .raw }
            | .blending => { c with tags := pc, aggKind := .raw }
            | .nonBlending | .raw => { c with aggKind := .raw }
          match mode, c.aggKind with
          | .maskComplementary, .blending | .maskComplementary, .nonBlending =>
            { base with ty := ensureOptionScalar base.ty, bucketed := false }
          | _, _ => base)
        .ok (.table {
          cols := outCols
          rowTags := newRowTags
          orderTags := tt.orderTags
          groupedBy := none
          summarized := false
          distinctBy := none })
    | .dynamic _ => .error "cannot SuppressSmallGroups on DynamicTable"
  | .window input items => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      if items.isEmpty then .error "Window requires at least one WindowItem"
      else
        let outCols ← applyWindowItems tt.orderTags (tt.cols.map (fun c => { c with aggKind := .raw })) items
        if distinctIdents (outCols.map ColSpec.name) then
          .ok (.table {
            cols := outCols
            rowTags := tt.rowTags
            orderTags := tt.orderTags
            groupedBy := none
            summarized := false
            distinctBy := none })
        else .error "Window produced duplicate column names"
    | .dynamic _ => .error "cannot Window on DynamicTable"
  | .fillGaps input col stepMicros over fill => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      if stepMicros <= 0 || !distinctIdents over then
        .error "FillGaps requires positive step and distinct partition keys"
      else
        match tt.findCol? col with
        | none => .error s!"missing time column '{col}' in FillGaps"
        | some tCol =>
          if !(decide (tCol.ty = .date) || decide (tCol.ty = .timestamp) || decide (tCol.ty = .int)) then
            .error "FillGaps column must be Date, Timestamp, or Int"
          else if !over.all (fun k => k != col && (tt.findCol? k).isSome) then
            .error "FillGaps partition keys must exist and exclude the time column"
          else
            let nonKeyCols := tt.cols.filter (fun c => c.name != col && !over.contains c.name)
            let fillOk := nonKeyCols.all (fun c =>
              match fill.find? (fun (fn, _) => fn == c.name) with
              | some (_, lit) =>
                match checkLiteral prog TagSet.empty lit with
                | .ok lty => decide (lty.ty = c.ty.toTy)
                | .error _ => false
              | none => decide (c.ty = ensureOptionScalar c.ty))
            if !fillOk then
              .error "FillGaps requires type-matching fill literals for non-nullable non-key columns"
            else
              let overTags := TagSet.unionList (over.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
              let newRowTags := (tt.rowTags.union tCol.tags).union overTags
              -- Duplicate timestamps within a partition pick the first row, reflecting `orderTags`
              let outCols := tt.cols.map (fun c =>
                if c.name == col || over.contains c.name then
                  { c with aggKind := .raw, bucketed := false }
                else
                  { c with tags := (c.tags.union newRowTags).union tt.orderTags, aggKind := .raw, bucketed := false })
              .ok (.table {
                cols := outCols
                rowTags := newRowTags
                orderTags := TagSet.empty
                groupedBy := none
                summarized := false
                distinctBy := none })
    | .dynamic _ => .error "cannot FillGaps on DynamicTable"
  | .pivotWider input namesFrom valuesFrom staticCols fill => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      if staticCols.isEmpty || !distinctIdents staticCols || namesFrom == valuesFrom then
        .error "PivotWider requires distinct non-empty staticCols and distinct namesFrom/valuesFrom"
      else
        match tt.findCol? namesFrom, tt.findCol? valuesFrom with
        | some nCol, some vCol =>
          if !decide (nCol.ty = .text) then
            .error "PivotWider namesFrom column must have type Text"
          else
            match checkLiteral prog TagSet.empty fill with
            | .error e => .error e
            | .ok fillLTy =>
              if !decide (fillLTy.ty = vCol.ty.toTy) then
                .error "PivotWider fill literal must match valuesFrom type"
              else
                let idCols := (tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map
                  (fun c => { c with aggKind := .raw })
                let idTags := TagSet.unionList (idCols.map ColSpec.tags)
                let newRowTags := (tt.rowTags.union nCol.tags).union idTags
                let cellTags := ((nCol.tags.union vCol.tags).union newRowTags).union tt.orderTags
                let pivotedCols := staticCols.map (fun sc => {
                  name := sc
                  ty := vCol.ty
                  tags := cellTags
                  bucketed := false
                  aggKind := .raw })
                let outCols := idCols ++ pivotedCols
                if distinctIdents (outCols.map ColSpec.name) then
                  .ok (.table {
                    cols := outCols
                    rowTags := newRowTags
                    orderTags := TagSet.empty
                    groupedBy := none
                    summarized := false
                    distinctBy := none })
                else .error "PivotWider staticCols collide with remaining id columns"
        | _, _ => .error "PivotWider missing namesFrom or valuesFrom column"
    | .dynamic _ => .error "cannot PivotWider on DynamicTable"
  | .crosstab input rowsCol colsCol valuesCol fill => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      match tt.findCol? rowsCol, tt.findCol? colsCol, tt.findCol? valuesCol with
      | some rCol, some cCol, some vCol =>
        match checkLiteral prog TagSet.empty fill with
        | .ok fillLTy =>
          if isEquatableTy rCol.ty.toTy && isEquatableTy cCol.ty.toTy &&
             decide (fillLTy.ty = vCol.ty.toTy) then
            let dtTags := ((((tt.rowTags.union tt.orderTags).union rCol.tags).union cCol.tags).union vCol.tags).union pc
            .ok (.dynamic dtTags)
          else .error "Crosstab column or fill type mismatch"
        | .error e => .error e
      | _, _, _ => .error "Crosstab missing column"
    | .dynamic _ => .error "cannot Crosstab on DynamicTable"
  | .redact input col _ => do
    let inPlan ← checkPlan prog env pc inSpec input
    match inPlan with
    | .table tt =>
      match tt.findCol? col with
      | some targetCol =>
        if decide (targetCol.ty = .text) || decide (targetCol.ty = .option .text) then
          let outCols := tt.cols.map (fun c =>
            if c.name == col then
              { c with ty := .text, tags := pc, bucketed := false, aggKind := .raw }
            else { c with aggKind := .raw })
          .ok (.table {
            cols := outCols
            rowTags := tt.rowTags
            orderTags := tt.orderTags
            groupedBy := none
            summarized := false
            distinctBy := none })
        else .error s!"Redact column '{col}' must be Text or Text?"
      | none => .error s!"unknown column '{col}' in Redact"
    | .dynamic _ => .error "cannot Redact on DynamicTable"
  | .pseudonymize input col secretExpr => do
    let inPlan ← checkPlan prog env pc inSpec input
    let secLTy ← checkExpr prog env [] pc inSpec secretExpr
    match inPlan, secLTy.ty with
    | .table tt, .secret _ =>
      match tt.findCol? col with
      | some targetCol =>
        if isEquatableTy targetCol.ty.toTy &&
           secLTy.tags.subset ((TagSet.singleton "secret").union pc) then
          -- Audited declassifier: replaces `.col` with keyed deterministic HMAC token (`Text`),
          -- clearing `[pii]` while preserving any non-PII domain tags (e.g. `[ferpa]`) + `pc`.
          let clearedTags := (targetCol.tags.remove "pii").union pc
          let outCols := tt.cols.map (fun c =>
            if c.name == col then
              { c with ty := .text, tags := clearedTags, bucketed := false, aggKind := .raw }
            else { c with aggKind := .raw })
          .ok (.table {
            cols := outCols
            rowTags := tt.rowTags
            orderTags := tt.orderTags
            groupedBy := none
            summarized := false
            distinctBy := none })
        else .error s!"Pseudonymize column '{col}' must be equatable"
      | none => .error s!"unknown column '{col}' in Pseudonymize"
    | .dynamic _, _ => .error "cannot Pseudonymize on DynamicTable"
    | _, _ => .error "Pseudonymize requires a Secret capability key (hardcoded strings forbidden)"
  termination_by structural plan
end

/-! ## Whole-Program & Policy Verification (`checkProgram`) -/

def checkDataDecls (prog : Program) : Except String Unit :=
  if !distinctIdents (prog.datas.map DataDecl.name) then
    .error "duplicate data type names"
  else
    let ok := prog.datas.all (fun d =>
      !d.ctors.isEmpty &&
      distinctIdents (d.ctors.map CtorDecl.name) &&
      d.ctors.all (fun c =>
        c.fields.all (fun f => validLTy prog f && isEquatableTy f.ty)))
    if ok then .ok ()
    else .error "invalid DataDecl constructors or non-data fields"

def checkSchemaDecls (prog : Program) : Except String Unit :=
  if !distinctIdents (prog.schemas.map SchemaDecl.name) then
    .error "duplicate schema names"
  else if prog.schemas.all (fun s =>
      validTableTy prog s.schema &&
      !s.schema.summarized &&
      s.schema.groupedBy.isNone &&
      s.schema.distinctBy.isNone &&
      s.schema.cols.all (fun c => !c.bucketed && decide (c.aggKind = .raw))) then
    .ok ()
  else .error "invalid SchemaDecl"

def checkConstDecls (prog : Program) : Except String Unit :=
  if !distinctIdents (prog.consts.map ConstDecl.name) then
    .error "duplicate constant names"
  else
    let rec go : List ConstDecl → Except String Unit
      | [] => .ok ()
      | c :: cs => do
        if !validLTy prog c.lty then
          .error s!"invalid type on constant '{c.name}'"
        else do
          let vLTy ← checkLiteral prog TagSet.empty c.value
          if ltySubtype vLTy c.lty then go cs
          else .error s!"constant '{c.name}' value does not match declared LTy"
    go prog.consts

/- Check syntactic purity (`exprIsPure`). -/
mutual
def exprIsPure : Expr → Bool
  | .lit _ | .var _ | .constRef _ | .tableLit _ _ => true
  | .letE _ _ b1 b2 => exprIsPure b1 && exprIsPure b2
  | .ifE c t e => exprIsPure c && exprIsPure t && exprIsPure e
  | .caseE s arms => exprIsPure s && exprIsPureArms arms
  | .lam _ _ _ b => exprIsPure b
  | .app f as1 => exprIsPure f && exprIsPureList as1
  | .call _ as1 => exprIsPureList as1
  | .join _ _ r b => exprIsPure r && exprIsPure b
  | .jump _ as1 | .tuple as1 | .ctor _ _ as1 | .prim _ as1 => exprIsPureList as1
  | .proj e _ => exprIsPure e
  | .rel p => planIsPure p
  | .host _ _ | .fail _ => false
  | .stop _ d => match d with | none => true | some e => exprIsPure e

def exprIsPureList : List Expr → Bool
  | [] => true
  | e :: es => exprIsPure e && exprIsPureList es

def exprIsPureArms : List CaseArm → Bool
  | [] => true
  | .mk _ _ b :: rest => exprIsPure b && exprIsPureArms rest

def planIsPure : Plan → Bool
  | .sourceExpr e => exprIsPure e
  | .sourceDB _ _ _ | .pseudonymize _ _ _ => false
  | .select p _ | .drop p _ | .rename p _ | .derive p _ | .filter p _
  | .distinct p _ | .sort p _ | .limit p _ | .groupBy p _
  | .summarize p _ _ | .suppressSmallGroups p _ _ _ | .window p _
  | .fillGaps p _ _ _ _ | .pivotWider p _ _ _ _ | .crosstab p _ _ _ _
  | .redact p _ _ => planIsPure p
  | .join _ l r _ _ | .union l r => planIsPure l && planIsPure r
end

def isCapabilityTy : Ty → Bool
  | .args | .clock | .console _ | .readFiles | .writeFiles _ _
  | .readDB _ | .writeTable _ _ _ _ _ | .rawReadDB _ | .httpsAllow _ _
  | .secret _ | .declassify _ => true
  | _ => false

def checkParamsPolicy (pol? : Option Policy) : List (Ident × LTy) → Except String Unit
  | [] => .ok ()
  | (_, pLTy) :: rest => do
    checkCapAgainstPolicy pol? pLTy.ty
    checkParamsPolicy pol? rest

def checkFunDecl (prog : Program) (f : FunDecl) : Except String Unit := do
  if !distinctIdents (f.params.map Prod.fst) then
    .error s!"duplicate parameter names in function '{f.name}'"
  else if !f.params.all (fun (_, l) => validLTy prog l) ||
          !validTagSet prog f.pc ||
          !validLTy prog f.ret then
    .error s!"invalid types or undeclared sensitivity tags in function '{f.name}'"
  else if !f.pc.subset f.ret.effectiveTags then
    .error s!"function '{f.name}' caller pc bound must be reflected in return LTy"
  else if !noFreeJumps [] f.body then
    .error s!"function '{f.name}' contains jump to unbound label"
  else if f.isPure && (f.params.any (fun (_, l) => isCapabilityTy l.ty) || !exprIsPure f.body) then
    .error s!"function '{f.name}' marked pure contains host effects or capabilities"
  else do
    -- Enforce optional `dana.policy` upper bound on every declared parameter capability
    checkParamsPolicy prog.policy f.params
    let bodyEnv : TyEnv := f.params.reverse
    let bodyLTy ← checkExpr prog bodyEnv [] f.pc f.kind.isSpec f.body
    if ltySubtype bodyLTy f.ret then .ok ()
    else .error s!"function '{f.name}' body return LTy mismatch"

def checkFunDecls (prog : Program) : List FunDecl → Except String Unit
  | [] => .ok ()
  | f :: fs => do
    checkFunDecl prog f
    checkFunDecls prog fs

def checkPolicyWf (prog : Program) : Except String Unit :=
  match prog.policy with
  | none => .ok ()
  | some p =>
    if p.minGroupSize >= 1 &&
       validTagSet prog p.allowConsole &&
       p.allowExport.all (fun (_, ts) => validTagSet prog ts) &&
       p.allowHttps.all (fun (_, ts) => validTagSet prog ts) &&
       p.allowWrite.all (fun r => validTagSet prog r.tags) then
      .ok ()
    else .error "invalid tags or min_group_size in Policy"

/-- Complete decidable static checker for Dana Core IR v0.1 programs.
    Note: `prog.metadata` is intentionally never inspected. -/
def checkProgram (prog : Program) : Except String Unit := do
  if prog.version != { major := 0, minor := 1 } then
    .error s!"unsupported Dana Core version {prog.version.major}.{prog.version.minor}"
  else if !distinctIdents prog.tags || prog.tags.any (fun t => builtInTags.contains t) then
    .error "duplicate or built-in-shadowing custom tag declarations"
  else do
    checkPolicyWf prog
    checkDataDecls prog
    checkSchemaDecls prog
    checkConstDecls prog
    if !distinctIdents (prog.funs.map FunDecl.name) then
      .error "duplicate function names"
    else do
      checkFunDecls prog prog.funs
      match prog.entry with
      | none => .ok ()
      | some mainName =>
        match prog.findFun? mainName with
        | some mainFn =>
          if mainFn.kind.isSpec then
            .error "program entry cannot be a spec function"
          else if !mainFn.pc.isEmpty then
            .error "program entry must have public caller pc = []"
          else if !mainFn.params.all (fun (_, l) => isCapabilityTy l.ty &&
              match l.ty with
              | .secret _ => l.tags.subset (TagSet.singleton "secret")
              | _ => l.tags.isEmpty) then
            .error "program entry parameters must be top-level capabilities"
          else .ok ()
        | none => .error s!"declared entry '{mainName}' not found"

def isWellTypedProgram (prog : Program) : Bool :=
  (checkProgram prog).isOk

end DanaCore
