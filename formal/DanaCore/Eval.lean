/-
  DanaCore/Eval.lean
  Fuel-indexed deterministic big-step operational semantics, strict total value
  ordering, capability/fake World state, automatic sensitive diagnostic redaction,
  and canonical observable Report extraction for Dana Core IR v0.1.
-/
import DanaCore.Syntax
import DanaCore.Check

namespace DanaCore

/-! ## Runtime Values, Capability Handles, Tables, Charts, Reports & Profiles -/

inductive CapHandle where
  | real
  | fake (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Hidden group cardinality metadata tracked across `Summarize -> SuppressSmallGroups`. -/
structure GroupMeta where
  rowCount      : Nat
  distinctCount : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

structure ProfileColSummary where
  colName       : Ident
  tyName        : String
  rowCount      : Nat
  nullCount     : Nat
  distinctCount : Nat
  minDisplay    : Option String
  maxDisplay    : Option String
  deriving DecidableEq, Repr, Inhabited

structure ProfileVal where
  cols : List ProfileColSummary
  deriving DecidableEq, Repr, Inhabited

mutual
structure TableRow where
  cells     : List Val
  groupMeta : Option GroupMeta := none
  deriving Repr

structure TableVal where
  cols : List ColSpec
  rows : List TableRow
  deriving Repr

structure ChartVal where
  kind    : ChartKind
  title   : String
  colNames : List Ident
  series  : List (List Val)
  deriving Repr

structure ReportVal where
  title     : String
  summaries : List String
  charts    : List ChartVal
  tables    : List (List Ident × List (List Val))
  deriving Repr

structure EnvEntry where
  name : Ident
  lty  : LTy
  val  : Val
  deriving Repr

inductive Val where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | decimal (scaled : Int)
  | float (f : Float64)
  | text (s : String)
  | bytes (bs : List UInt8)
  | date (days : Int)
  | timestamp (micros : Int)
  | duration (micros : Int)
  | optNone
  | optSome (v : Val)
  | resOk (v : Val)
  | resErr (e : Val)
  | tuple (elems : List Val)
  | list (elems : List Val)
  | map (entries : List (Val × Val))
  | ctor (typeName : Ident) (ctorName : Ident) (fields : List Val)
  | table (tv : TableVal)
  | dynTable (headers : List String) (rows : List (List Val))
  | chart (cv : ChartVal)
  | report (rv : ReportVal)
  | profile (pv : ProfileVal)
  | linearModel (slope : Float64) (intercept : Float64) (r2 : Float64)
  | statTest (stat : Float64) (pValue : Float64)
  | closure (params : List (Ident × LTy)) (fnPc : TagSet) (retLTy : LTy)
      (body : Expr) (capturedEnv : List EnvEntry)
  -- First-class capability values
  | capArgs
  | capClock
  | capConsole (h : CapHandle) (allows : TagSet)
  | capReadFiles (h : CapHandle)
  | capWriteFiles (h : CapHandle) (root : String) (allows : TagSet)
  | capReadDB (h : CapHandle) (db : Ident)
  | capWriteTable (h : CapHandle) (db : Ident) (tableName : Ident)
  | capRawReadDB (db : Ident)
  | capHttpsAllow (h : CapHandle) (host : String) (allows : TagSet)
  | capSecret (h : CapHandle) (name : String)
  | capDeclassify (allows : TagSet)
  deriving Repr
end

instance : Inhabited Val := ⟨.unit⟩
instance : Inhabited TableRow := ⟨{ cells := [] }⟩
instance : Inhabited TableVal := ⟨{ cols := [], rows := [] }⟩

abbrev Env := List EnvEntry

def lookupEnv (env : Env) (name : Ident) : Option (LTy × Val) :=
  match env with
  | [] => none
  | e :: rest => if e.name = name then some (e.lty, e.val) else lookupEnv rest name

def envToTyEnv (env : Env) : TyEnv :=
  env.map (fun e => (e.name, e.lty))

/-! ## Structural Value Equality & Strict Total Ordering on Data Values -/

/-- IEEE-754 totalOrder key mapping binary64 bits to `[0, 2^64)` injectively. -/
def floatOrderKey (f : Float64) : Nat :=
  let n := f.bits.toNat
  let signBit := 2 ^ 63
  if n ≥ signBit then (2 ^ 64 - 1) - n
  else n + signBit

theorem floatOrderKey_inj {f1 f2 : Float64} (h : floatOrderKey f1 = floatOrderKey f2) :
    f1 = f2 := by
  cases f1 with | mk b1 =>
  cases f2 with | mk b2 =>
  congr 1
  have hb1 : b1.toNat < 2 ^ 64 := b1.toBitVec.isLt
  have hb2 : b2.toNat < 2 ^ 64 := b2.toBitVec.isLt
  unfold floatOrderKey at h
  simp only at h
  have hnat : b1.toNat = b2.toNat := by
    by_cases h1 : b1.toNat ≥ 2 ^ 63 <;> by_cases h2 : b2.toNat ≥ 2 ^ 63
    · simp only [h1, h2, ↓reduceIte] at h; omega
    · simp only [h1, h2, ↓reduceIte] at h; omega
    · simp only [h1, h2, ↓reduceIte] at h; omega
    · simp only [h1, h2, ↓reduceIte] at h; omega
  exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hnat)

/-- Deterministic IEEE-754 binary64 conversions via Lean core `Float`. -/
def f64ToFloat (f : Float64) : Float := Float.ofBits f.bits

def floatToF64 (x : Float) : Float64 := ⟨x.toBits⟩

def valToFloat : Val → Option Float
  | .float f => some (f64ToFloat f)
  | .int n => some (Float.ofInt n)
  | .decimal d => some (Float.ofInt d / Float.ofInt decScale)
  | _ => none

def unwrapNumericFloat : Val → Option Float
  | .optNone => none
  | .optSome inner => valToFloat inner
  | other => valToFloat other

def byteListLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | b1 :: r1, b2 :: r2 =>
    if b1.toNat < b2.toNat then true
    else if b2.toNat < b1.toNat then false
    else byteListLt r1 r2

def valRank : Val → Nat
  | .optNone => 0
  | .unit => 1
  | .bool _ => 2
  | .int _ => 3
  | .decimal _ => 4
  | .float _ => 5
  | .text _ => 6
  | .bytes _ => 7
  | .date _ => 8
  | .timestamp _ => 9
  | .duration _ => 10
  | .optSome _ => 11
  | .resOk _ => 12
  | .resErr _ => 13
  | .tuple _ => 14
  | .list _ => 15
  | .map _ => 16
  | .ctor _ _ _ => 17
  | .table _ => 18
  | .dynTable _ _ => 19
  | .chart _ => 20
  | .report _ => 21
  | .profile _ => 22
  | .linearModel _ _ _ => 23
  | .statTest _ _ => 24
  | _ => 25

/- Structural equality on observable runtime data values (table equality compares
   ordered column cells, ignoring transient hidden `Summarize` group metadata). -/
mutual
def valEq (v1 v2 : Val) : Bool :=
  match v1, v2 with
  | .unit, .unit => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .decimal a, .decimal b => a == b
  | .float a, .float b => a == b
  | .text a, .text b => a == b
  | .bytes a, .bytes b => a == b
  | .date a, .date b => a == b
  | .timestamp a, .timestamp b => a == b
  | .duration a, .duration b => a == b
  | .optNone, .optNone => true
  | .optSome a, .optSome b => valEq a b
  | .resOk a, .resOk b => valEq a b
  | .resErr a, .resErr b => valEq a b
  | .tuple as1, .tuple bs1 => valListEq as1 bs1
  | .list as1, .list bs1 => valListEq as1 bs1
  | .map as1, .map bs1 => valPairsEq as1 bs1
  | .ctor tn1 cn1 fs1, .ctor tn2 cn2 fs2 =>
    tn1 == tn2 && cn1 == cn2 && valListEq fs1 fs2
  | .table (.mk cols1 rows1), .table (.mk cols2 rows2) =>
    decide (cols1.map ColSpec.name = cols2.map ColSpec.name) &&
    valTableRowsEq rows1 rows2
  | .dynTable h1 r1, .dynTable h2 r2 =>
    h1 == h2 && valRowsEq r1 r2
  | .linearModel s1 i1 r1, .linearModel s2 i2 r2 =>
    s1 == s2 && i1 == i2 && r1 == r2
  | .statTest s1 p1, .statTest s2 p2 =>
    s1 == s2 && p1 == p2
  | .profile p1, .profile p2 => decide (p1 = p2)
  | _, _ => false
  termination_by structural v1

def valListEq (xs ys : List Val) : Bool :=
  match xs, ys with
  | [], [] => true
  | a :: as1, b :: bs1 => valEq a b && valListEq as1 bs1
  | _, _ => false
  termination_by structural xs

def valPairsEq (xs ys : List (Val × Val)) : Bool :=
  match xs, ys with
  | [], [] => true
  | (k1, v1) :: r1, (k2, v2) :: r2 => valEq k1 k2 && valEq v1 v2 && valPairsEq r1 r2
  | _, _ => false
  termination_by structural xs

def valTableRowsEq (xs ys : List TableRow) : Bool :=
  match xs, ys with
  | [], [] => true
  | .mk c1 _ :: rs1, .mk c2 _ :: rs2 => valListEq c1 c2 && valTableRowsEq rs1 rs2
  | _, _ => false
  termination_by structural xs

def valRowsEq (xs ys : List (List Val)) : Bool :=
  match xs, ys with
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 => valListEq r1 r2 && valRowsEq rs1 rs2
  | _, _ => false
  termination_by structural xs
end

def cmpInt (a b : Int) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

def cmpNat (a b : Nat) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

def cmpTag (a b : String) : Ordering :=
  if charListLt a.toList b.toList then .lt
  else if charListLt b.toList a.toList then .gt
  else .eq

def cmpBytes (a b : List UInt8) : Ordering :=
  if byteListLt a b then .lt
  else if byteListLt b a then .gt
  else .eq

/- Three-way structural comparator on runtime values (`None < Some x`, numeric `<`,
   lexicographic strings/tuples), structurally recursive on its first argument. -/
mutual
def valCmp (v1 v2 : Val) : Ordering :=
  match v1, v2 with
  | .optNone, .optNone => .eq
  | .unit, .unit => .eq
  | .bool false, .bool true => .lt
  | .bool true, .bool false => .gt
  | .bool _, .bool _ => .eq
  | .int a, .int b => cmpInt a b
  | .decimal a, .decimal b => cmpInt a b
  | .float a, .float b => cmpNat (floatOrderKey a) (floatOrderKey b)
  | .text a, .text b => cmpTag a b
  | .bytes a, .bytes b => cmpBytes a b
  | .date a, .date b => cmpInt a b
  | .timestamp a, .timestamp b => cmpInt a b
  | .duration a, .duration b => cmpInt a b
  | .optSome a, .optSome b => valCmp a b
  | .resOk a, .resOk b => valCmp a b
  | .resErr a, .resErr b => valCmp a b
  | .tuple as1, .tuple bs1 => valListCmp as1 bs1
  | .list as1, .list bs1 => valListCmp as1 bs1
  | .map as1, .map bs1 => valPairsCmp as1 bs1
  | .ctor tn1 cn1 fs1, .ctor tn2 cn2 fs2 =>
    match cmpTag tn1 tn2 with
    | .lt => .lt
    | .gt => .gt
    | .eq =>
      match cmpTag cn1 cn2 with
      | .lt => .lt
      | .gt => .gt
      | .eq => valListCmp fs1 fs2
  | .profile p1, .profile p2 => cmpTag (reprStr p1) (reprStr p2)
  | .linearModel s1 i1 r1, .linearModel s2 i2 r2 =>
    match cmpNat (floatOrderKey s1) (floatOrderKey s2) with
    | .eq =>
      match cmpNat (floatOrderKey i1) (floatOrderKey i2) with
      | .eq => cmpNat (floatOrderKey r1) (floatOrderKey r2)
      | other => other
    | other => other
  | .statTest s1 p1, .statTest s2 p2 =>
    match cmpNat (floatOrderKey s1) (floatOrderKey s2) with
    | .eq => cmpNat (floatOrderKey p1) (floatOrderKey p2)
    | other => other
  | a, b => cmpNat (valRank a) (valRank b)
  termination_by structural v1

def valListCmp (xs ys : List Val) : Ordering :=
  match xs, ys with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as1, b :: bs1 =>
    match valCmp a b with
    | .lt => .lt
    | .gt => .gt
    | .eq => valListCmp as1 bs1
  termination_by structural xs

def valPairsCmp (xs ys : List (Val × Val)) : Ordering :=
  match xs, ys with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (k1, v1) :: r1, (k2, v2) :: r2 =>
    match valCmp k1 k2 with
    | .lt => .lt
    | .gt => .gt
    | .eq =>
      match valCmp v1 v2 with
      | .lt => .lt
      | .gt => .gt
      | .eq => valPairsCmp r1 r2
  termination_by structural xs
end

def valLt (a b : Val) : Bool := decide (valCmp a b = .lt)
def valListLt (as1 bs1 : List Val) : Bool := decide (valListCmp as1 bs1 = .lt)

/-! ### Canonical Insertion Sort & Deduplication Helpers -/

def insertSortedBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt y x then y :: insertSortedBy lt x ys else x :: y :: ys

def insertionSortBy {α : Type} (lt : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertSortedBy lt x (insertionSortBy lt xs)

def dedupEqBy {α : Type} (eq : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    let rest := dedupEqBy eq xs
    if rest.any (fun y => eq x y) then rest else x :: rest

/-- Deduplicate an already canonically sorted list by dropping adjacent duplicates. -/
def dedupAdjacentBy {α : Type} (eq : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    if eq x y then dedupAdjacentBy eq (y :: rest)
    else x :: dedupAdjacentBy eq (y :: rest)

/-! ## Safe-by-Default Runtime Redaction & Diagnostics -/

/-- Canonical redaction marker for non-empty sensitivity tag sets (`[REDACTED:tag]`). -/
def redactTags (ts : TagSet) : String :=
  "[REDACTED:" ++ String.intercalate "," ts.elems ++ "]"

def renderDecimal (scaled : Int) : String :=
  let sign := if scaled < 0 then "-" else ""
  let absVal : Nat := scaled.natAbs
  let scaleNat : Nat := 1000000000000000000
  let whole := absVal / scaleNat
  let frac := absVal % scaleNat
  if frac == 0 then
    s!"{sign}{whole}.0"
  else
    let fracStr := toString frac
    let padLen := 18 - fracStr.length
    let padded := String.ofList (List.replicate padLen '0') ++ fracStr
    let trimmed := String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse
    s!"{sign}{whole}.{trimmed}"

/-- Format a runtime value purely when `tags` is public (`[]`); otherwise emit `[REDACTED:...]`. -/
def renderPublicVal : Val → String
  | .unit => "Unit"
  | .bool true => "true"
  | .bool false => "false"
  | .int n => toString n
  | .decimal d => renderDecimal d
  | .float f => s!"float64({f.bits})"
  | .text s => s
  | .bytes bs => s!"bytes({bs.length})"
  | .date d => s!"date({d})"
  | .timestamp ts => s!"timestamp({ts})"
  | .duration dur => s!"duration({dur})"
  | .optNone => "none"
  | .optSome v => s!"some({renderPublicVal v})"
  | .resOk v => s!"Ok({renderPublicVal v})"
  | .resErr e => s!"Error({renderPublicVal e})"
  | .tuple vs => "(" ++ String.intercalate ", " (vs.map renderPublicVal) ++ ")"
  | .list vs => "[" ++ String.intercalate ", " (vs.map renderPublicVal) ++ "]"
  | .ctor _ cn vs =>
    if vs.isEmpty then cn
    else cn ++ "(" ++ String.intercalate ", " (vs.map renderPublicVal) ++ ")"
  | .table tv => s!"Table(rows={tv.rows.length})"
  | .dynTable hs rs => s!"DynamicTable(cols={hs.length}, rows={rs.length})"
  | _ => "<value>"

/-- Privacy-preserving diagnostic formatter: NEVER inspects `v` whenever `ts` is non-empty! -/
def formatDiagDetail (ts : TagSet) (v : Val) : String :=
  if ts.isEmpty then renderPublicVal v else redactTags ts

theorem formatDiagDetail_redacted {ts : TagSet} (hne : ts.isEmpty = false) (v1 v2 : Val) :
    formatDiagDetail ts v1 = formatDiagDetail ts v2 := by
  simp [formatDiagDetail, hne]

structure Bug where
  kind    : BugKind
  message : String
  deriving DecidableEq, Repr, Inhabited

/-! ## Host `World`, Fake Capability Stores, Outcomes & Observable `Report` -/

structure FakeConsoleState where
  stdout : List String := []
  stderr : List String := []
  deriving DecidableEq, Repr, Inhabited

structure FakeFilesState where
  files : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited

structure StoredTable where
  db        : Ident
  tableName : Ident
  schema    : TableTy
  rows      : List (List Val)
  deriving Repr

structure FakeDBState where
  db     : Ident
  tables : List StoredTable := []
  deriving Repr, Inhabited

structure FakeHttpsState where
  host      : String
  responses : List (String × String) := []
  requests  : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- Execution world holding real host state and isolated per-handle fake states. -/
structure World where
  args               : List String := []
  clockMicros        : Int := 0
  stdout             : List String := []
  stderr             : List String := []
  realCsvFixtures    : List (String × TableVal × TableVal) := []
  writtenFiles       : List (String × String) := []
  realDBTables       : List StoredTable := []
  writtenTables      : List (Ident × Ident × List Ident × List (List Val)) := []
  realSecrets        : List (String × String) := []
  runtimeAllowExport : TagSet := TagSet.empty
  -- Independent fake capability heaps for `spec` (`test` / `example` / `promise`)
  fakeConsoles       : List FakeConsoleState := []
  fakeFiles          : List FakeFilesState := []
  fakeDBs            : List FakeDBState := []
  fakeHttps          : List FakeHttpsState := []
  fakeSecrets        : List String := []
  deriving Repr, Inhabited

inductive Outcome where
  | ok (val : Val) (world : World)
  | stopped (bug : Bug) (world : World)
  | failed (assertionMsg : String) (world : World)
  | jumped (label : Ident) (args : List Val) (world : World)
  | wrong
  | outOfFuel
  deriving Repr

inductive ExitStatus where
  | ok
  | stopped
  | failed
  deriving DecidableEq, Repr, Inhabited

/-- Canonical observable execution report shared across `danacore` (Lean),
    the naive Rust oracle (`src/oracle/`), and the vectorized VM (`src/vm/`). -/
structure ExecReport where
  status        : ExitStatus
  diagnostic    : Option String
  stdout        : List String
  stderr        : List String
  writtenFiles  : List (String × String)
  writtenTables : List (Ident × Ident × List Ident × List (List String))
  fakeConsoles  : List FakeConsoleState
  fakeFiles     : List FakeFilesState
  deriving DecidableEq, Repr, Inhabited

def extractReport (out : Outcome) : Option ExecReport :=
  let renderTables (wts : List (Ident × Ident × List Ident × List (List Val))) :
      List (Ident × Ident × List Ident × List (List String)) :=
    wts.map (fun (db, tbl, cols, rows) =>
      (db, tbl, cols, rows.map (fun r => r.map renderPublicVal)))
  match out with
  | .ok _ w =>
    some {
      status := .ok
      diagnostic := none
      stdout := w.stdout
      stderr := w.stderr
      writtenFiles := w.writtenFiles
      writtenTables := renderTables w.writtenTables
      fakeConsoles := w.fakeConsoles
      fakeFiles := w.fakeFiles
    }
  | .stopped bug w =>
    some {
      status := .stopped
      diagnostic := some bug.message
      stdout := w.stdout
      stderr := w.stderr
      writtenFiles := w.writtenFiles
      writtenTables := renderTables w.writtenTables
      fakeConsoles := w.fakeConsoles
      fakeFiles := w.fakeFiles
    }
  | .failed msg w =>
    some {
      status := .failed
      diagnostic := some msg
      stdout := w.stdout
      stderr := w.stderr
      writtenFiles := w.writtenFiles
      writtenTables := renderTables w.writtenTables
      fakeConsoles := w.fakeConsoles
      fakeFiles := w.fakeFiles
    }
  | .jumped _ _ _ | .wrong | .outOfFuel => none

/-! ## Pure Literal, Scalar & Primitive Evaluation -/

def evalLiteral : Literal → Val
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .decimal d => .decimal d
  | .float f => .float f
  | .text s => .text s
  | .bytes bs => .bytes bs
  | .date d => .date d
  | .timestamp ts => .timestamp ts
  | .duration dur => .duration dur
  | .noneLit _ => .optNone

inductive PrimResult where
  | ok (v : Val)
  | stopped (b : Bug)
  | outOfFuel
  | wrong
  deriving Repr

def checkedInt (n : Int) : PrimResult :=
  if inInt64Range n then .ok (.int n)
  else .stopped { kind := .intOverflow, message := "Int64 arithmetic overflow" }

def checkedDecimal (d : Int) : PrimResult :=
  if inDecimalRange d then .ok (.decimal d)
  else .stopped { kind := .decimalOverflow, message := "Decimal arithmetic overflow" }

def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

def trimAsciiString (s : String) : String :=
  let cs := s.toList.dropWhile isAsciiSpace
  let cs' := (cs.reverse.dropWhile isAsciiSpace).reverse
  String.ofList cs'

def lowerAsciiChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def containsSubstr (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs => n.isPrefixOf (c :: cs) || go cs
    go h

/-- Truncate proleptic Gregorian days since `1970-01-01` to the 1st of its month
    (civil-from-days algorithm by Howard Hinnant). -/
def dateTruncMonthDays (days : Int) : Int :=
  let z := days + 719468
  let era := if z ≥ 0 then z / 146097 else (z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  -- First day of month is simply `days - day_of_month_0_indexed`
  let mp := (5 * doy + 2) / 153
  let dom0 := doy - (153 * mp + 2) / 5
  days - dom0

def buildPairs : List Val → Option (List (Val × Val))
  | [] => some []
  | k :: v :: rest => (buildPairs rest).map (fun tl => (k, v) :: tl)
  | [_] => none

def lookupColIdx? (cols : List ColSpec) (name : Ident) : Option (Nat × ColSpec) :=
  let rec go (i : Nat) : List ColSpec → Option (Nat × ColSpec)
    | [] => none
    | c :: cs => if c.name == name then some (i, c) else go (i + 1) cs
  go 0 cols

def projectColCells (tv : TableVal) (colName : Ident) : Option (ColSpec × List Val) := do
  let (idx, cSpec) ← lookupColIdx? tv.cols colName
  let rec gather : List TableRow → Option (List Val)
    | [] => some []
    | r :: rs => do
      let cell ← r.cells[idx]?
      let tl ← gather rs
      some (cell :: tl)
  let vals ← gather tv.rows
  some (cSpec, vals)

def buildProfileCol (tv : TableVal) (idx : Nat) (c : ColSpec) : Option ProfileColSummary := do
  let rec gather : List TableRow → Option (List Val)
    | [] => some []
    | r :: rs => do
      let cell ← r.cells[idx]?
      let tl ← gather rs
      some (cell :: tl)
  let cells ← gather tv.rows
  let nonNull := cells.filterMap (fun v =>
    match v with
    | .optNone => none
    | .optSome inner => some inner
    | other => some other)
  let nullCount := cells.length - nonNull.length
  let sorted := insertionSortBy valLt nonNull
  let distinctVals := dedupAdjacentBy valEq sorted
  -- Safe-by-default runtime redaction (`docs/design/privacy.md` §5):
  -- Tagged columns omit concrete min/max/sample values!
  let (minDisp, maxDisp) :=
    if !c.tags.isEmpty then
      (some (redactTags c.tags), some (redactTags c.tags))
    else
      match sorted.head?, sorted.getLast? with
      | some mn, some mx => (some (renderPublicVal mn), some (renderPublicVal mx))
      | _, _ => (none, none)
  some {
    colName := c.name
    tyName := reprStr c.ty
    rowCount := cells.length
    nullCount := nullCount
    distinctCount := distinctVals.length
    minDisplay := minDisp
    maxDisplay := maxDisp
  }

def buildProfileCols (tv : TableVal) (idx : Nat) : List ColSpec → Option (List ProfileColSummary)
  | [] => some []
  | c :: cs => do
    let hd ← buildProfileCol tv idx c
    let tl ← buildProfileCols tv (idx + 1) cs
    some (hd :: tl)

def flattenValLists : List Val → Option (List Val)
  | [] => some []
  | .list xs :: rest => (flattenValLists rest).map (fun tl => xs ++ tl)
  | _ => none

def gatherConcatRows : List Val → Option (List TableRow)
  | [] => some []
  | .table tv :: tl =>
    (gatherConcatRows tl).map (fun r => tv.rows.map (fun row => { row with groupMeta := none }) ++ r)
  | _ => none

def gatherChartSeries (tv : TableVal) : List Ident → Option (List (List Val))
  | [] => some []
  | cn :: cns => do
    let (_, vals) ← projectColCells tv cn
    let tl ← gatherChartSeries tv cns
    some (vals :: tl)

def extractPairVals (cols : List ColSpec) (colX colY : Ident) (rows : List TableRow) :
    Option (List (List Val)) := do
  let (idxX, _) ← lookupColIdx? cols colX
  let (idxY, _) ← lookupColIdx? cols colY
  some (rows.filterMap (fun r =>
    match r.cells[idxX]?, r.cells[idxY]? with
    | some vx, some vy =>
      match vx, vy with
      | .optNone, _ => none
      | _, .optNone => none
      | .optSome ux, .optSome uy => some [ux, uy]
      | .optSome ux, uy => some [ux, uy]
      | ux, .optSome uy => some [ux, uy]
      | ux, uy => some [ux, uy]
    | _, _ => none))

def pairsToFloats (sortedPairs : List (List Val)) : List (Float × Float) :=
  sortedPairs.filterMap (fun pair =>
    match pair with
    | [vx, vy] =>
      match valToFloat vx, valToFloat vy with
      | some x, some y => some (x, y)
      | _, _ => none
    | _ => none)

def meanOfFloats (xs : List Float) : Float :=
  let n := Float.ofNat xs.length
  let total := xs.foldl (· + ·) 0.0
  if total.isInf then xs.foldl (fun acc x => acc + x / n) 0.0
  else total / n

def computeStatsCorr (sortedPairs : List (List Val)) : Option Float64 :=
  let pts := pairsToFloats sortedPairs
  if pts.length < 2 || pts.any (fun p => p.1.isNaN || p.1.isInf || p.2.isNaN || p.2.isInf) then
    none
  else
    let meanX := meanOfFloats (pts.map Prod.fst)
    let meanY := meanOfFloats (pts.map Prod.snd)
    if meanX.isNaN || meanX.isInf || meanY.isNaN || meanY.isInf then
      none
    else
      let scaleX := pts.foldl (fun acc p => let a := Float.abs (p.1 - meanX); if a > acc then a else acc) 0.0
      let scaleY := pts.foldl (fun acc p => let a := Float.abs (p.2 - meanY); if a > acc then a else acc) 0.0
      if scaleX == 0.0 || scaleY == 0.0 || scaleX.isInf || scaleY.isInf then
        none
      else
        let uSxx := pts.foldl (fun acc p => let u := (p.1 - meanX) / scaleX; acc + u * u) 0.0
        let uSyy := pts.foldl (fun acc p => let u := (p.2 - meanY) / scaleY; acc + u * u) 0.0
        let uSxy := pts.foldl (fun acc p => acc + ((p.1 - meanX) / scaleX) * ((p.2 - meanY) / scaleY)) 0.0
        let denom := Float.sqrt uSxx * Float.sqrt uSyy
        if denom == 0.0 || denom.isNaN then none
        else some (floatToF64 (uSxy / denom))

def computeStatsLinReg (sortedPairs : List (List Val)) : Option (Float64 × Float64 × Float64) :=
  let pts := pairsToFloats sortedPairs
  if pts.length < 2 || pts.any (fun p => p.1.isNaN || p.1.isInf || p.2.isNaN || p.2.isInf) then
    none
  else
    let meanX := meanOfFloats (pts.map Prod.fst)
    let meanY := meanOfFloats (pts.map Prod.snd)
    if meanX.isNaN || meanX.isInf || meanY.isNaN || meanY.isInf then
      none
    else
      let scaleX := pts.foldl (fun acc p => let a := Float.abs (p.1 - meanX); if a > acc then a else acc) 0.0
      let scaleY := pts.foldl (fun acc p => let a := Float.abs (p.2 - meanY); if a > acc then a else acc) 0.0
      if scaleX == 0.0 || scaleX.isInf then
        none
      else if scaleY == 0.0 then
        some (Float64.zero, floatToF64 meanY, floatToF64 1.0)
      else if scaleY.isInf then
        none
      else
        let uSxx := pts.foldl (fun acc p => let u := (p.1 - meanX) / scaleX; acc + u * u) 0.0
        let uSyy := pts.foldl (fun acc p => let u := (p.2 - meanY) / scaleY; acc + u * u) 0.0
        let uSxy := pts.foldl (fun acc p => acc + ((p.1 - meanX) / scaleX) * ((p.2 - meanY) / scaleY)) 0.0
        if uSxx == 0.0 then none
        else
          let slope := (uSxy / uSxx) * (scaleY / scaleX)
          let intercept := meanY - slope * meanX
          let r2 := if uSyy == 0.0 then 1.0 else (uSxy * uSxy) / (uSxx * uSyy)
          some (floatToF64 slope, floatToF64 intercept, floatToF64 r2)

def evalPrimOp (op : PrimOp) (args : List Val) : PrimResult :=
  match op, args with
  | .someVal _, [v] => .ok (.optSome v)
  | .isSome, [.optNone] => .ok (.bool false)
  | .isSome, [.optSome _] => .ok (.bool true)
  | .isNone, [.optNone] => .ok (.bool true)
  | .isNone, [.optSome _] => .ok (.bool false)
  | .unwrapOr, [.optNone, defV] => .ok defV
  | .unwrapOr, [.optSome v, _] => .ok v
  | .unwrapBang, [.optSome v] => .ok v
  | .unwrapBang, [.optNone] =>
    .stopped { kind := .unwrapNone, message := "unwrapped none value" }
  | .okVal _, [v] => .ok (.resOk v)
  | .errVal _, [e] => .ok (.resErr e)
  | .addInt, [.int a, .int b] => checkedInt (a + b)
  | .subInt, [.int a, .int b] => checkedInt (a - b)
  | .mulInt, [.int a, .int b] => checkedInt (a * b)
  | .divInt, [.int a, .int b] =>
    if b == 0 then .stopped { kind := .divByZero, message := "integer division by zero" }
    else checkedInt (a / b)
  | .modInt, [.int a, .int b] =>
    if b == 0 then .stopped { kind := .divByZero, message := "integer modulo by zero" }
    else checkedInt (a % b)
  | .negInt, [.int a] => checkedInt (-a)
  | .addDec, [.decimal a, .decimal b] => checkedDecimal (a + b)
  | .subDec, [.decimal a, .decimal b] => checkedDecimal (a - b)
  | .mulDec, [.decimal a, .decimal b] => checkedDecimal ((a * b) / decScale)
  | .divDec, [.decimal a, .decimal b] =>
    if b == 0 then .stopped { kind := .divByZero, message := "decimal division by zero" }
    else checkedDecimal ((a * decScale) / b)
  | .negDec, [.decimal a] => checkedDecimal (-a)
  | .intToDec, [.int n] => checkedDecimal (n * decScale)
  | .boolToDec, [.bool b] => .ok (.decimal (if b then decScale else 0))
  | .eq, [a, b] => .ok (.bool (valEq a b))
  | .ne, [a, b] => .ok (.bool (!valEq a b))
  | .lt, [a, b] => .ok (.bool (valLt a b))
  | .le, [a, b] => .ok (.bool (valLt a b || valEq a b))
  | .gt, [a, b] => .ok (.bool (valLt b a))
  | .ge, [a, b] => .ok (.bool (valLt b a || valEq a b))
  | .notBool, [.bool a] => .ok (.bool (!a))
  | .andBool, [.bool a, .bool b] => .ok (.bool (a && b))
  | .orBool, [.bool a, .bool b] => .ok (.bool (a || b))
  | .concatText, [.text a, .text b] => .ok (.text (a ++ b))
  | .containsText, [.text a, .text b] => .ok (.bool (containsSubstr a b))
  | .trimText, [.text a] => .ok (.text (trimAsciiString a))
  | .lowerAsciiText, [.text a] => .ok (.text (String.ofList (a.toList.map lowerAsciiChar)))
  | .emptyText, [.text a] => .ok (.bool a.isEmpty)
  | .intToText, [.int n] => .ok (.text (toString n))
  | .decToText, [.decimal d] => .ok (.text (renderDecimal d))
  | .dateTruncMonth, [.date d] => .ok (.date (dateTruncMonthDays d))
  | .addDuration, [.timestamp ts, .duration dur] => .ok (.timestamp (ts + dur))
  | .diffTimestamp, [.timestamp t1, .timestamp t2] => .ok (.duration (t1 - t2))
  | .listLit _, elems => .ok (.list elems)
  | .listLen, [.list elems] => checkedInt (Int.ofNat elems.length)
  | .listEmpty, [.list elems] => .ok (.bool elems.isEmpty)
  | .listAppend, [.list elems, item] => .ok (.list (elems ++ [item]))
  | .listConcat, [.list nested] =>
    match flattenValLists nested with
    | some flat => .ok (.list flat)
    | none => .wrong
  | .mapLit _ _, kvArgs =>
    match buildPairs kvArgs with
    | some pairs => .ok (.map pairs)
    | none => .wrong
  | .mapGet, [.map pairs, qKey] =>
    match pairs.find? (fun (k, _) => valEq k qKey) with
    | some (_, v) => .ok (.optSome v)
    | none => .ok .optNone
  | .tableCount, [.table tv] => checkedInt (Int.ofNat tv.rows.length)
  | .tableConcat schema, [.list tbls] =>
    let outCols := schema.cols.map (fun c => { c with aggKind := .raw })
    match gatherConcatRows tbls with
    | some allRows => .ok (.table { cols := outCols, rows := allRows })
    | none => .wrong
  | .tableProfile, [.table tv] =>
    match buildProfileCols tv 0 tv.cols with
    | some summaries => .ok (.profile { cols := summaries })
    | none => .wrong
  | .statsCorr colX colY, [.table tv] =>
    match extractPairVals tv.cols colX colY tv.rows with
    | some rawPairs =>
      let sortedPairs := insertionSortBy valListLt rawPairs
      match computeStatsCorr sortedPairs with
      | none => .ok .optNone
      | some r => .ok (.optSome (.float r))
    | none => .wrong
  | .statsLinReg colX colY, [.table tv] =>
    match extractPairVals tv.cols colX colY tv.rows with
    | some rawPairs =>
      let sortedPairs := insertionSortBy valListLt rawPairs
      match computeStatsLinReg sortedPairs with
      | some (slope, intercept, r2) => .ok (.linearModel slope intercept r2)
      | none =>
        .stopped { kind := .divByZero, message := "degenerate linear regression: fewer than 2 points, non-finite inputs, or zero variance in x" }
    | none => .wrong
  | .statsTTest colX colY, [.table tv] =>
    match lookupColIdx? tv.cols colX, lookupColIdx? tv.cols colY with
    | some _, some _ =>
      .stopped { kind := .outsideBoundary, message := "outside boundary: statsTTest is outside the Lean Core oracle" }
    | _, _ => .wrong
  | .chartMake kind cols title, [.table tv] =>
    match gatherChartSeries tv cols with
    | some series => .ok (.chart { kind := kind, title := title, colNames := cols, series := series })
    | none => .wrong
  | .reportNew, [.text title] =>
    .ok (.report { title := title, summaries := [], charts := [], tables := [] })
  | .reportAddSummary, [.report rv, .text s] =>
    .ok (.report { rv with summaries := rv.summaries ++ [s] })
  | .reportAddChart, [.report rv, .chart cv] =>
    .ok (.report { rv with charts := rv.charts ++ [cv] })
  | .reportAddTable, [.report rv, .table tv] =>
    let headers := tv.cols.map ColSpec.name
    let rawRows := tv.rows.map TableRow.cells
    .ok (.report { rv with tables := rv.tables ++ [(headers, rawRows)] })
  | _, _ => .wrong

/-! ## Pseudonymization & Host Capability Execution -/

/-- Deterministic keyed token (`ps_<16-hex>`) modeling HMAC-SHA256 pseudonymization
    via FNV-1a 64-bit mixing of `(secretKey, serializedVal)`. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toList.foldl (fun hash c =>
    (hash ^^^ c.toNat.toUInt64) * 1099511628211) 14695981039346656037

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

def uint64ToHex16 (x : UInt64) : String :=
  let rec go (rem : Nat) (acc : List Char) (v : Nat) : List Char :=
    match rem with
    | 0 => acc
    | k + 1 => go k (hexDigit (v % 16) :: acc) (v / 16)
  String.ofList (go 16 [] x.toNat)

def pseudonymizeToken (secretMaterial : String) (v : Val) : String :=
  let h := fnv1a64 (secretMaterial ++ ":" ++ renderPublicVal v)
  "ps_" ++ uint64ToHex16 h

def checkRuntimeExportGate (h : CapHandle) (allows : TagSet) (w : World) : Option Bug :=
  match h with
  | .fake _ => none
  | .real =>
    if allows.isEmpty || allows.subset w.runtimeAllowExport then none
    else
      some {
        kind := .exportGateDenied
        message := "runtime --allow-export authorization required for sensitive external sink"
      }

def renderTableText (tv : TableVal) : String :=
  let hdr := String.intercalate " | " (tv.cols.map ColSpec.name)
  let body := tv.rows.map (fun r => String.intercalate " | " (r.cells.map renderPublicVal))
  String.intercalate "\n" (hdr :: body)

def renderReportHtml (rv : ReportVal) : String :=
  "<html><h1>" ++ rv.title ++ "</h1><p>" ++
    String.intercalate "</p><p>" rv.summaries ++
    s!"</p><!-- charts:{rv.charts.length} tables:{rv.tables.length} --></html>"

def evalHostOp (prog : Program) (op : HostOp) (args : List Val) (w : World) : Outcome :=
  match op, args with
  | .argsGet, [.capArgs] =>
    .ok (.list (w.args.map Val.text)) w
  | .clockNow, [.capClock] =>
    .ok (.timestamp w.clockMicros) w
  | .consolePrint, [.capConsole h allows, .text msg] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      match h with
      | .real => .ok .unit { w with stdout := w.stdout ++ [msg] }
      | .fake id =>
        match w.fakeConsoles[id]? with
        | some fc =>
          let fc' := { fc with stdout := fc.stdout ++ [msg] }
          .ok .unit { w with fakeConsoles := w.fakeConsoles.set id fc' }
        | none => .ok .unit w
  | .consoleError, [.capConsole h allows, .text msg] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      match h with
      | .real => .ok .unit { w with stderr := w.stderr ++ [msg] }
      | .fake id =>
        match w.fakeConsoles[id]? with
        | some fc =>
          let fc' := { fc with stderr := fc.stderr ++ [msg] }
          .ok .unit { w with fakeConsoles := w.fakeConsoles.set id fc' }
        | none => .ok .unit w
  | .consolePrintTable, [.capConsole h allows, .table tv] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      let line := renderTableText tv
      match h with
      | .real => .ok .unit { w with stdout := w.stdout ++ [line] }
      | .fake id =>
        match w.fakeConsoles[id]? with
        | some fc =>
          let fc' := { fc with stdout := fc.stdout ++ [line] }
          .ok .unit { w with fakeConsoles := w.fakeConsoles.set id fc' }
        | none => .ok .unit w
  | .readCsv schemaName, [.capReadFiles _, .text path] =>
    match prog.findSchema? schemaName with
    | none => .wrong
    | some sDecl =>
      let badTT := quarantineBadRowTableTy sDecl.schema
      match w.realCsvFixtures.find? (fun (p, _, _) => p == path) with
      | some (_, goodTV, badTV) =>
        if decide (goodTV.cols.map ColSpec.ty = sDecl.schema.cols.map ColSpec.ty) &&
           decide (badTV.cols.map ColSpec.ty = badTT.cols.map ColSpec.ty) then
          let gTV := { cols := sDecl.schema.cols, rows := goodTV.rows }
          let bTV := { cols := badTT.cols, rows := badTV.rows }
          .ok (.resOk (.tuple [.table gTV, .table bTV])) w
        else
          .ok (.resErr (.text s!"CSV fixture schema mismatch at '{path}'")) w
      | none =>
        let emptyGood : TableVal := { cols := sDecl.schema.cols, rows := [] }
        let emptyBad : TableVal := { cols := badTT.cols, rows := [] }
        .ok (.resOk (.tuple [.table emptyGood, .table emptyBad])) w
  | .writeFile, [.capWriteFiles h root allows, .text relPath, .text content] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      if !isSafeRelativePath relPath then
        .ok (.resErr (.text s!"invalid relative export path '{relPath}'")) w
      else
        let fullPath := joinConfinedPath root relPath
        match h with
        | .real =>
          .ok (.resOk .unit) { w with writtenFiles := w.writtenFiles ++ [(fullPath, content)] }
        | .fake id =>
          match w.fakeFiles[id]? with
          | some ff =>
            let ff' := { files := ff.files ++ [(fullPath, content)] }
            .ok (.resOk .unit) { w with fakeFiles := w.fakeFiles.set id ff' }
          | none => .ok (.resOk .unit) w
  | .writeReportHtml, [.capWriteFiles h root allows, .text relPath, .report rv] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      if !isSafeRelativePath relPath then
        .ok (.resErr (.text s!"invalid relative export path '{relPath}'")) w
      else
        let fullPath := joinConfinedPath root relPath
        let html := renderReportHtml rv
        match h with
        | .real =>
          .ok (.resOk .unit) { w with writtenFiles := w.writtenFiles ++ [(fullPath, html)] }
        | .fake id =>
          match w.fakeFiles[id]? with
          | some ff =>
            let ff' := { files := ff.files ++ [(fullPath, html)] }
            .ok (.resOk .unit) { w with fakeFiles := w.fakeFiles.set id ff' }
          | none => .ok (.resOk .unit) w
  | .writeTable, [.capWriteTable h db tbl, .table srcTV] =>
    let colNames := srcTV.cols.map ColSpec.name
    let rawRows := srcTV.rows.map TableRow.cells
    match checkedInt (Int.ofNat rawRows.length) with
    | .ok cntVal =>
      match h with
      | .real =>
        let w' := { w with writtenTables := w.writtenTables ++ [(db, tbl, colNames, rawRows)] }
        .ok (.resOk cntVal) w'
      | .fake _ =>
        .ok (.resOk cntVal) w
    | .stopped bug => .stopped bug w
    | _ => .wrong
  | .declassifyApprove _, [.capDeclassify _, v, .text _] =>
    .ok v w
  -- Documented `outside` host boundary operations (`docs/design/core-ir.md` §1)
  | .rawSqlQuery _ _, [.capRawReadDB _, .text _] =>
    .stopped { kind := .outsideBoundary, message := "outside boundary: live SQL wire query" } w
  | .httpsGetJson, [.capHttpsAllow h _ allows, .text url] =>
    match h with
    | .real =>
      .stopped { kind := .outsideBoundary, message := "outside boundary: live HTTPS socket" } w
    | .fake id =>
      match checkRuntimeExportGate h allows w with
      | some bug => .stopped bug w
      | none =>
        match w.fakeHttps[id]? with
        | some fh =>
          let fh' := { fh with requests := fh.requests ++ [url] }
          let w' := { w with fakeHttps := w.fakeHttps.set id fh' }
          match fh.responses.find? (fun (u, _) => u == url) with
          | some (_, body) => .ok (.resOk (.text body)) w'
          | none => .ok (.resErr (.text "404 Not Found")) w'
        | none => .ok (.resErr (.text "invalid fake https handle")) w
  | .readParquet _, [.capReadFiles h, .text _] =>
    match h with
    | .real =>
      .stopped { kind := .outsideBoundary, message := "outside boundary: binary Parquet decoder" } w
    | .fake _ =>
      .ok (.resErr (.text "in-memory Parquet fixture not found")) w
  | .writeParquet, [.capWriteFiles h root allows, .text relPath, .table srcTV] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      if !isSafeRelativePath relPath then
        .ok (.resErr (.text s!"invalid relative export path '{relPath}'")) w
      else
        match h with
        | .real =>
          .stopped { kind := .outsideBoundary, message := "outside boundary: binary Parquet encoder" } w
        | .fake id =>
          let fullPath := joinConfinedPath root relPath
          let reprContent := renderTableText srcTV
          match w.fakeFiles[id]? with
          | some ff =>
            let ff' := { files := ff.files ++ [(fullPath, reprContent)] }
            .ok (.resOk .unit) { w with fakeFiles := w.fakeFiles.set id ff' }
          | none => .ok (.resOk .unit) w
  | .writeXlsx, [.capWriteFiles h root allows, .text relPath, .table srcTV] =>
    match checkRuntimeExportGate h allows w with
    | some bug => .stopped bug w
    | none =>
      if !isSafeRelativePath relPath then
        .ok (.resErr (.text s!"invalid relative export path '{relPath}'")) w
      else
        match h with
        | .real =>
          .stopped { kind := .outsideBoundary, message := "outside boundary: binary XLSX encoder" } w
        | .fake id =>
          let fullPath := joinConfinedPath root relPath
          let reprContent := renderTableText srcTV
          match w.fakeFiles[id]? with
          | some ff =>
            let ff' := { files := ff.files ++ [(fullPath, reprContent)] }
            .ok (.resOk .unit) { w with fakeFiles := w.fakeFiles.set id ff' }
          | none => .ok (.resOk .unit) w
  -- Spec-only fake capability constructors
  | .fakeConsole allows, [] =>
    let id := w.fakeConsoles.length
    .ok (.capConsole (.fake id) allows) { w with fakeConsoles := w.fakeConsoles ++ [{}] }
  | .fakeFiles allows, [] =>
    let id := w.fakeFiles.length
    .ok (.capWriteFiles (.fake id) "mem://" allows) { w with fakeFiles := w.fakeFiles ++ [{}] }
  | .fakeDB db, [] =>
    let id := w.fakeDBs.length
    .ok (.capReadDB (.fake id) db) { w with fakeDBs := w.fakeDBs ++ [{ db := db }] }
  | .fakeHttps host allows, [] =>
    let id := w.fakeHttps.length
    .ok (.capHttpsAllow (.fake id) host allows) { w with fakeHttps := w.fakeHttps ++ [{ host := host }] }
  | .fakeSecret name, [.text secretVal] =>
    let id := w.fakeSecrets.length
    .ok (.capSecret (.fake id) name) { w with fakeSecrets := w.fakeSecrets ++ [secretVal] }
  | _, _ => .wrong

/-! ## Pure Relational Operators Evaluation Helpers -/

def defaultValForScalar : ScalarTy → Val
  | .unit => .unit
  | .bool => .bool false
  | .int => .int 0
  | .decimal => .decimal 0
  | .float => .float Float64.zero
  | .text => .text ""
  | .bytes => .bytes []
  | .date => .date 0
  | .timestamp => .timestamp 0
  | .duration => .duration 0
  | .data name => .ctor name "" []
  | .option _ => .optNone

def wrapIntoOptionVal (sTy : ScalarTy) (v : Val) : Val :=
  match sTy with
  | .option _ => v
  | _ => .optSome v

def evalBucketCell (v : Val) (cuts : List Val) (labels : List String) : Option Val :=
  let rec pick : List Val → List String → Option String
    | [], [lastLbl] => some lastLbl
    | cut :: restCuts, lbl :: restLbls =>
      if valLt v cut then some lbl
      else pick restCuts restLbls
    | _, _ => none
  (pick cuts labels).map Val.text

def sumSortedInts : List Val → PrimResult
  | [] => .ok (.int 0)
  | .int x :: xs =>
    match sumSortedInts xs with
    | .ok (.int rest) => checkedInt (x + rest)
    | .ok _ => .wrong
    | other => other
  | _ => .wrong

def sumSortedDecimals : List Val → PrimResult
  | [] => .ok (.decimal 0)
  | .decimal x :: xs =>
    match sumSortedDecimals xs with
    | .ok (.decimal rest) => checkedDecimal (x + rest)
    | .ok _ => .wrong
    | other => other
  | _ => .wrong

def sumSortedFloats (sorted : List Val) : Float64 :=
  let total := sorted.foldl (fun acc v =>
    match valToFloat v with
    | some x => acc + x
    | none => acc) 0.0
  floatToF64 total

def meanSortedFloats (sorted : List Val) : Float64 :=
  let xs := sorted.filterMap valToFloat
  if xs.isEmpty then Float64.zero
  else floatToF64 (meanOfFloats xs)

def medianSortedFloats (sorted : List Val) : Float64 :=
  let xs := sorted.filterMap valToFloat
  if xs.isEmpty then Float64.zero
  else
    let n := xs.length
    let mid := n / 2
    if n % 2 == 1 then
      floatToF64 (xs[mid]?.getD 0.0)
    else
      let lo := xs[mid - 1]?.getD 0.0
      let hi := xs[mid]?.getD 0.0
      floatToF64 ((lo / 2.0) + (hi / 2.0))

def varianceSortedFloats (sorted : List Val) : Float64 :=
  let xs := sorted.filterMap valToFloat
  if xs.isEmpty then Float64.zero
  else
    let n := Float.ofNat xs.length
    let mean := meanOfFloats xs
    let sumSq := xs.foldl (fun acc x => let d := x - mean; acc + d * d) 0.0
    floatToF64 (sumSq / n)

def stddevSortedFloats (sorted : List Val) : Float64 :=
  let xs := sorted.filterMap valToFloat
  if xs.isEmpty then Float64.zero
  else if xs.any (fun x => x.isNaN || x.isInf) then
    floatToF64 (Float.sqrt (f64ToFloat (varianceSortedFloats sorted)))
  else
    let n := Float.ofNat xs.length
    let mean := meanOfFloats xs
    if mean.isNaN || mean.isInf then
      floatToF64 (Float.sqrt (f64ToFloat (varianceSortedFloats sorted)))
    else
      let scale := xs.foldl (fun acc x => let a := Float.abs (x - mean); if a > acc then a else acc) 0.0
      if scale == 0.0 then Float64.zero
      else if scale.isInf then
        floatToF64 (Float.sqrt (f64ToFloat (varianceSortedFloats sorted)))
      else
        let uSumSq := xs.foldl (fun acc x => let u := (x - mean) / scale; acc + u * u) 0.0
        floatToF64 (scale * Float.sqrt (uSumSq / n))

def percentileSortedFloats (p : Float64) (sorted : List Val) : Float64 :=
  let xs := sorted.filterMap valToFloat
  if xs.isEmpty then Float64.zero
  else
    let n := xs.length
    let pVal := f64ToFloat p
    if pVal ≤ 0.0 || n == 1 then
      floatToF64 (xs[0]?.getD 0.0)
    else if pVal ≥ 1.0 then
      floatToF64 (xs[n - 1]?.getD 0.0)
    else
      let pos := pVal * Float.ofNat (n - 1)
      let lo := min (pos.toUInt64.toNat) (n - 1)
      let hi := min (lo + 1) (n - 1)
      let frac := pos - Float.ofNat lo
      let vlo := xs[lo]?.getD 0.0
      let vhi := xs[hi]?.getD 0.0
      if vlo == vhi then floatToF64 vlo
      else floatToF64 ((1.0 - frac) * vlo + frac * vhi)

def evalAggClean (op : AggOp) (outTy : ScalarTy) (rawVals : List Val) : PrimResult :=
  let nonNull : List Val := rawVals.filterMap (fun v =>
    match v with
    | .optNone => none
    | .optSome inner => some inner
    | other => some other)
  let sorted := insertionSortBy valLt nonNull
  match op with
  | .count => checkedInt (Int.ofNat rawVals.length)
  | .countDistinct =>
    let dedup := dedupAdjacentBy valEq sorted
    checkedInt (Int.ofNat dedup.length)
  | .sum =>
    match outTy with
    | .int => sumSortedInts sorted
    | .decimal => sumSortedDecimals sorted
    | .float => .ok (.float (sumSortedFloats sorted))
    | _ => .wrong
  | .mean =>
    if sorted.isEmpty then .ok .optNone
    else
      match outTy with
      | .option .decimal =>
        match sumSortedDecimals sorted with
        | .ok (.decimal total) =>
          let avg := total / Int.ofNat sorted.length
          if inDecimalRange avg then .ok (.optSome (.decimal avg))
          else .stopped { kind := .decimalOverflow, message := "Decimal overflow in mean" }
        | .ok _ => .wrong
        | .stopped b => .stopped b
        | .outOfFuel => .outOfFuel
        | .wrong => .wrong
      | .option .float => .ok (.optSome (.float (meanSortedFloats sorted)))
      | _ => .wrong
  | .median =>
    if sorted.isEmpty then .ok .optNone
    else
      match outTy with
      | .option .decimal =>
        let mid := sorted.length / 2
        if sorted.length % 2 == 1 then
          match sorted[mid]? with
          | some (.decimal d) => .ok (.optSome (.decimal d))
          | _ => .wrong
        else
          match sorted[mid - 1]?, sorted[mid]? with
          | some (.decimal lo), some (.decimal hi) =>
            let avg := (lo + hi) / 2
            if inDecimalRange avg then .ok (.optSome (.decimal avg))
            else .stopped { kind := .decimalOverflow, message := "Decimal overflow in median" }
          | _, _ => .wrong
      | .option .float => .ok (.optSome (.float (medianSortedFloats sorted)))
      | _ => .wrong
  | .variance =>
    if sorted.isEmpty then .ok .optNone
    else .ok (.optSome (.float (varianceSortedFloats sorted)))
  | .stddev =>
    if sorted.isEmpty then .ok .optNone
    else .ok (.optSome (.float (stddevSortedFloats sorted)))
  | .percentile p =>
    if sorted.isEmpty then .ok .optNone
    else .ok (.optSome (.float (percentileSortedFloats p sorted)))
  | .min =>
    match sorted.head? with
    | none => .ok .optNone
    | some v => .ok (.optSome v)
  | .max =>
    match sorted.getLast? with
    | none => .ok .optNone
    | some v => .ok (.optSome v)
  | .first =>
    match nonNull.head? with
    | none => .ok .optNone
    | some v => .ok (.optSome v)
  | .last =>
    match nonNull.getLast? with
    | none => .ok .optNone
    | some v => .ok (.optSome v)

def extractKeyVals (cols : List ColSpec) (keyNames : List Ident) (row : TableRow) :
    Option (List Val) :=
  let rec go : List Ident → Option (List Val)
    | [] => some []
    | k :: ks => do
      let (idx, _) ← lookupColIdx? cols k
      let cell ← row.cells[idx]?
      let tl ← go ks
      some (cell :: tl)
  go keyNames

def extractAllRowsKeyVals (cols : List ColSpec) (keyNames : List Ident) :
    List TableRow → Option (List (List Val))
  | [] => some []
  | r :: rs => do
    let kv ← extractKeyVals cols keyNames r
    let tl ← extractAllRowsKeyVals cols keyNames rs
    some (kv :: tl)

def projectRowsByIndices (idxs : List Nat) : List TableRow → Option (List TableRow)
  | [] => some []
  | r :: rs => do
    let rec pick : List Nat → Option (List Val)
      | [] => some []
      | i :: rest => do
        let cell ← r.cells[i]?
        let tl ← pick rest
        some (cell :: tl)
    let cells ← pick idxs
    let tl ← projectRowsByIndices idxs rs
    some ({ cells := cells, groupMeta := none } :: tl)

def rowLtByKeys (cols : List ColSpec) (keys : List (Ident × SortDir)) (r1 r2 : TableRow) : Bool :=
  let rec go : List (Ident × SortDir) → Bool
    | [] => false
    | (k, dir) :: rest =>
      match lookupColIdx? cols k with
      | none => false
      | some (idx, _) =>
        match r1.cells[idx]?, r2.cells[idx]? with
        | some v1, some v2 =>
          match dir with
          | .asc =>
            if valLt v1 v2 then true
            else if valLt v2 v1 then false
            else go rest
          | .desc =>
            if valLt v2 v1 then true
            else if valLt v1 v2 then false
            else go rest
        | _, _ => false
  go keys

/-- Detect duplicate join keys in `rows` and construct a privacy-redacted `Bug` diagnostic. -/
def checkUniqueJoinKeys (cols : List ColSpec) (keyNames : List Ident) (keyTags : TagSet)
    (rows : List TableRow) : Option Bug :=
  let indexed := rows.zipIdx
  let rec findDup : List (TableRow × Nat) → Option Bug
    | [] => none
    | (r1, i1) :: rest =>
      match extractKeyVals cols keyNames r1 with
      | none => none
      | some kv1 =>
        match rest.find? (fun (r2, _) =>
          match extractKeyVals cols keyNames r2 with
          | some kv2 => valListEq kv1 kv2
          | none => false) with
        | some (_, i2) =>
          let keyVal : Val := match kv1 with | [single] => single | _ => .tuple kv1
          let renderedKey := formatDiagDetail keyTags keyVal
          some {
            kind := .joinCardinality
            message := s!"duplicate key {renderedKey} (2 rows: {i1}, {i2})"
          }
        | none => findDup rest
  findDup indexed

def clampInt64Nat (n : Nat) : Int :=
  let i := Int.ofNat n
  if inInt64Range i then i else int64Max

def windowPartIndexed (cols : List ColSpec) (over : List Ident)
    (sortedIndexed : List (TableRow × Nat)) (myKey : List Val) : List (TableRow × Nat) :=
  sortedIndexed.filter (fun (r2, _) =>
    match extractKeyVals cols over r2 with
    | some k2 => valListEq myKey k2
    | none => false)

def evalWindowComputeCell (cols : List ColSpec) (item : WindowItem) (targetTy : ScalarTy)
    (partRows : List TableRow) (posInPart : Nat) : Option Val :=
  match item.fn with
  | .rowNumber => some (.int (clampInt64Nat (posInPart + 1)))
  | .rank col => do
    let (cIdx, _) ← lookupColIdx? cols col
    match partRows[posInPart]? with
    | none => some (.int 1)
    | some curRow =>
      match curRow.cells[cIdx]? with
      | none => some (.int 1)
      | some curVal =>
        let strictlyLess := (partRows.take posInPart).filter (fun pr =>
          match pr.cells[cIdx]? with
          | some pv => valLt pv curVal
          | none => false)
        some (.int (clampInt64Nat (strictlyLess.length + 1)))
  | .lag col offset => do
    let (cIdx, cSpec) ← lookupColIdx? cols col
    if posInPart < offset then some .optNone
    else
      match partRows[posInPart - offset]? with
      | none => some .optNone
      | some prevRow =>
        match prevRow.cells[cIdx]? with
        | none => some .optNone
        | some prevVal => some (wrapIntoOptionVal cSpec.ty prevVal)
  | .lead col offset => do
    let (cIdx, cSpec) ← lookupColIdx? cols col
    match partRows[posInPart + offset]? with
    | none => some .optNone
    | some nextRow =>
      match nextRow.cells[cIdx]? with
      | none => some .optNone
      | some nextVal => some (wrapIntoOptionVal cSpec.ty nextVal)
  | .runningSum col => do
    let (cIdx, _) ← lookupColIdx? cols col
    let prefixRows := partRows.take (posInPart + 1)
    let vals := prefixRows.filterMap (fun pr => pr.cells[cIdx]?)
    match evalAggClean .sum targetTy vals with
    | .ok v => some v
    | _ => some (defaultValForScalar targetTy)
  | .rollingMean col wSz => do
    let (cIdx, _) ← lookupColIdx? cols col
    let startIdx := if posInPart + 1 ≥ wSz then (posInPart + 1) - wSz else 0
    let winRows := (partRows.take (posInPart + 1)).drop startIdx
    let vals := winRows.filterMap (fun pr => pr.cells[cIdx]?)
    let floats := vals.filterMap unwrapNumericFloat
    if floats.isEmpty then some .optNone
    else
      let total := floats.foldl (· + ·) 0.0
      some (.optSome (.float (floatToF64 (total / Float.ofNat floats.length))))

def evalWindowOnTable (tv : TableVal) (item : WindowItem) (outCols : List ColSpec) :
    Option TableVal := do
  -- Sort indexed rows within each partition if `item.order` is non-empty, while
  -- emitting rows in `tv.rows`'s original order so `orderTags` never leaks `item.order`.
  let targetColSpec ← outCols.find? (fun c => c.name == item.name)
  let existingIdx? := lookupColIdx? tv.cols item.name
  let indexedRows := tv.rows.zipIdx
  let sortedIndexed :=
    if item.order.isEmpty then indexedRows
    else insertionSortBy (fun a b => rowLtByKeys tv.cols item.order a.1 b.1) indexedRows
  let computeCell := evalWindowComputeCell tv.cols item targetColSpec.ty
  let newRows ← buildWindowRows tv.cols item.over sortedIndexed existingIdx? computeCell indexedRows
  some { cols := outCols, rows := newRows }
where
  buildWindowRows (cols : List ColSpec) (over : List Ident) (sortedIndexed : List (TableRow × Nat))
      (existingIdx? : Option (Nat × ColSpec))
      (computeCell : List TableRow → Nat → Option Val) :
      List (TableRow × Nat) → Option (List TableRow)
    | [] => some []
    | (row, origIdx) :: rest => do
      let myKey ← extractKeyVals cols over row
      let partIndexed := windowPartIndexed cols over sortedIndexed myKey
      let posInPart := (partIndexed.findIdx? (fun (_, i2) => i2 == origIdx)).getD 0
      let wVal ← computeCell (partIndexed.map Prod.fst) posInPart
      let newCells :=
        match existingIdx? with
        | some (idx, _) => row.cells.set idx wVal
        | none => row.cells ++ [wVal]
      let tl ← buildWindowRows cols over sortedIndexed existingIdx? computeCell rest
      some ({ cells := newCells, groupMeta := none } :: tl)

def evalWindowItems : TableVal → List WindowItem → Option TableVal
  | curTV, [] => some curTV
  | curTV, it :: rest => do
    let nextCols ← (applyWindowItem curTV.cols TagSet.empty it).toOption
    let nextTV ← evalWindowOnTable curTV it nextCols
    evalWindowItems nextTV rest

def dedupTableRows (cols : List ColSpec) (keyNames : List Ident)
    (seen : List (List Val)) : List TableRow → Option (List TableRow)
  | [] => some []
  | r :: rs => do
    let kv ← extractKeyVals cols keyNames r
    if seen.any (fun sk => valListEq sk kv) then
      dedupTableRows cols keyNames seen rs
    else do
      let tl ← dedupTableRows cols keyNames (kv :: seen) rs
      some ({ r with groupMeta := none } :: tl)

def extractRightJoinCells (isLeftOuter : Bool) (rRow : TableRow) :
    List (ColSpec × Nat) → Option (List Val)
  | [] => some []
  | (rc, idx) :: rest => do
    let cell ← rRow.cells[idx]?
    let wrapped := if isLeftOuter then wrapIntoOptionVal rc.ty cell else cell
    let tl ← extractRightJoinCells isLeftOuter rRow rest
    some (wrapped :: tl)

def combineJoinMatches (isLeftOuter : Bool) (rKeepIdxs : List (ColSpec × Nat))
    (lCells : List Val) : List TableRow → Option (List TableRow)
  | [] => some []
  | mr :: mrs => do
    let rCells ← extractRightJoinCells isLeftOuter mr rKeepIdxs
    let tl ← combineJoinMatches isLeftOuter rKeepIdxs lCells mrs
    some ({ cells := lCells ++ rCells, groupMeta := none } :: tl)

def joinTableRows (kind : JoinKind) (lCols rCols : List ColSpec)
    (lKeyNames rKeyNames : List Ident) (rKeepIdxs : List (ColSpec × Nat))
    (isLeftOuter : Bool) (nullRightCells : List Val) (rRows : List TableRow) :
    List TableRow → Option (List TableRow)
  | [] => some []
  | lRow :: lRest => do
    let lkv ← extractKeyVals lCols lKeyNames lRow
    let matchingR := rRows.filter (fun rRow =>
      match extractKeyVals rCols rKeyNames rRow with
      | some rkv => valListEq lkv rkv
      | none => false)
    let restJoined ← joinTableRows kind lCols rCols lKeyNames rKeyNames
      rKeepIdxs isLeftOuter nullRightCells rRows lRest
    match kind with
    | .semi =>
      if !matchingR.isEmpty then
        some ({ cells := lRow.cells, groupMeta := none } :: restJoined)
      else some restJoined
    | .anti =>
      if matchingR.isEmpty then
        some ({ cells := lRow.cells, groupMeta := none } :: restJoined)
      else some restJoined
    | _ =>
      if matchingR.isEmpty then
        if isLeftOuter then
          some ({ cells := lRow.cells ++ nullRightCells, groupMeta := none } :: restJoined)
        else some restJoined
      else do
        let curJoined ← combineJoinMatches isLeftOuter rKeepIdxs lRow.cells matchingR
        some (curJoined ++ restJoined)

def mapPseudonymizeRows (keyMat : String) (cIdx : Nat) :
    List TableRow → Option (List TableRow)
  | [] => some []
  | r :: rs => do
    let origVal ← r.cells[cIdx]?
    let tok := Val.text (pseudonymizeToken keyMat origVal)
    let tl ← mapPseudonymizeRows keyMat cIdx rs
    some ({ cells := r.cells.set cIdx tok, groupMeta := none } :: tl)

/-! ## Case Matching Helper -/

def matchCaseVal (prog : Program) (scrutVal : Val) (scrutLTy : LTy) (armPc : TagSet) :
    Option (Ident × List (LTy × Val)) :=
  let sTags := scrutLTy.effectiveTags.union armPc
  match scrutLTy.ty, scrutVal with
  | .bool, .bool true => some ("true", [])
  | .bool, .bool false => some ("false", [])
  | .option _, .optNone => some ("None", [])
  | .option inner, .optSome u => some ("Some", [(.mk inner sTags, u)])
  | .result okTy _, .resOk u => some ("Ok", [(.mk okTy sTags, u)])
  | .result _ errTy, .resErr e => some ("Error", [(.mk errTy sTags, e)])
  | .data dName, .ctor vType cName fields =>
    if dName != vType then none
    else
      match prog.findData? dName with
      | none => none
      | some dDecl =>
        match dDecl.ctors.find? (fun c => c.name == cName) with
        | none => none
        | some cDecl =>
          if fields.length == cDecl.fields.length then
            some (cName, List.zip (cDecl.fields.map (fun f => f.addTags sTags)) fields)
          else none
  | _, _ => none

/-! ## Sequential Evaluation Helper for Argument Lists -/

inductive ArgOutcome where
  | ok (vals : List Val) (world : World)
  | aborted (out : Outcome)

def evalSeq (step : World → Expr → Outcome) (w : World) : List Expr → ArgOutcome
  | [] => .ok [] w
  | e :: es =>
    match step w e with
    | .ok v w1 =>
      match evalSeq step w1 es with
      | .ok vs w2 => .ok (v :: vs) w2
      | .aborted out => .aborted out
    | other => .aborted other

/-! ## Fuel-Indexed Mutual Big-Step Evaluator (`eval`, `evalPlan`, `evalRowExpr`) -/

inductive RowListResult where
  | ok (vs : List Val)
  | stopped (b : Bug)
  | outOfFuel
  | wrong
  deriving Repr

def deriveItemTargetName : DeriveItem → Ident
  | .colExpr n _ | .bucketCol n _ _ _ => n

def evalDeriveCell (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (curCols : List ColSpec) (r : TableRow) (item : DeriveItem) : PrimResult :=
  match item with
  | .colExpr _ re => evalRE curCols r re
  | .bucketCol _ src cuts labels =>
    match lookupColIdx? curCols src with
    | none => .wrong
    | some (sIdx, _) =>
      match r.cells[sIdx]? with
      | none => .wrong
      | some sVal =>
        match evalBucketCell sVal (cuts.map evalLiteral) labels with
        | some bVal => .ok bVal
        | none => .wrong

def evalDeriveMapRows (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (curCols : List ColSpec) (item : DeriveItem) (existingIdx? : Option (Nat × ColSpec)) :
    List TableRow → RowListResult
  | [] => .ok []
  | r :: rs =>
    match evalDeriveCell evalRE curCols r item with
    | .ok newCell =>
      let newCells :=
        match existingIdx? with
        | some (idx, _) => r.cells.set idx newCell
        | none => r.cells ++ [newCell]
      match evalDeriveMapRows evalRE curCols item existingIdx? rs with
      | .ok restVals => .ok (.tuple newCells :: restVals)
      | other => other
    | .stopped b => .stopped b
    | .outOfFuel => .outOfFuel
    | .wrong => .wrong

def evalDeriveItems (prog : Program) (tEnv : TyEnv)
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (w : World) (curTV : TableVal) : List DeriveItem → Outcome
  | [] => .ok (.table curTV) w
  | item :: rest =>
    match applyDeriveItem prog tEnv curTV.cols item with
    | .error _ => .wrong
    | .ok nextCols =>
      let existingIdx? := lookupColIdx? curTV.cols (deriveItemTargetName item)
      match evalDeriveMapRows evalRE curTV.cols item existingIdx? curTV.rows with
      | .ok rowTuples =>
        let nextRows : List TableRow := rowTuples.filterMap (fun
          | .tuple cs => some { cells := cs, groupMeta := none }
          | _ => none)
        evalDeriveItems prog tEnv evalRE w { cols := nextCols, rows := nextRows } rest
      | .stopped b => .stopped b w
      | .outOfFuel => .outOfFuel
      | .wrong => .wrong

def evalFilterRows (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (inCols outCols : List ColSpec) (pred : RowExpr) (w : World) : List TableRow → Outcome
  | [] => .ok (.table { cols := outCols, rows := [] }) w
  | r :: rs =>
    match evalRE inCols r pred with
    | .ok (.bool keep) =>
      match evalFilterRows evalRE inCols outCols pred w rs with
      | .ok (.table restTV) _ =>
        let r' : TableRow := { r with groupMeta := none }
        let rows' := if keep then r' :: restTV.rows else restTV.rows
        .ok (.table { cols := outCols, rows := rows' }) w
      | other => other
    | .ok _ => .wrong
    | .stopped b => .stopped b w
    | .outOfFuel => .outOfFuel
    | .wrong => .wrong

def evalArgOnGroupRows (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (cols : List ColSpec) (re : RowExpr) : List TableRow → RowListResult
  | [] => .ok []
  | gr :: grs =>
    match evalRE cols gr re with
    | .ok cv =>
      match evalArgOnGroupRows evalRE cols re grs with
      | .ok cvs => .ok (cv :: cvs)
      | other => other
    | .stopped b => .stopped b
    | .outOfFuel => .outOfFuel
    | .wrong => .wrong

def evalGroupAggItems (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (cols : List ColSpec) (gRows : List TableRow) : List (AggItem × ColSpec) → RowListResult
  | [] => .ok []
  | (aItem, aSpec) :: rest =>
    let valsRes : RowListResult :=
      match aItem.arg with
      | none => .ok (gRows.map (fun _ => Val.unit))
      | some re => evalArgOnGroupRows evalRE cols re gRows
    match valsRes with
    | .ok argVals =>
      match evalAggClean aItem.op aSpec.ty argVals with
      | .ok aggCell =>
        match evalGroupAggItems evalRE cols gRows rest with
        | .ok restCells => .ok (aggCell :: restCells)
        | other => other
      | .stopped b => .stopped b
      | .outOfFuel => .outOfFuel
      | .wrong => .wrong
    | other => other

def evalSummarizeGroups (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (tv : TableVal) (groupKeys : List Ident) (distinctKey : Option Ident)
    (dkIdx? : Option (Nat × ColSpec)) (aggs : List AggItem) (aggCols outCols : List ColSpec)
    (w : World) : List (List Val) → Outcome
  | [] => .ok (.table { cols := outCols, rows := [] }) w
  | gKey :: gks =>
    let gRows :=
      if groupKeys.isEmpty then tv.rows
      else tv.rows.filter (fun r =>
        match extractKeyVals tv.cols groupKeys r with
        | some kv => valListEq kv gKey
        | none => false)
    let distCount? : Option Nat :=
      match distinctKey, dkIdx? with
      | none, _ => none
      | some _, none => none
      | some _, some (dIdx, _) =>
        let dVals := gRows.filterMap (fun r =>
          match (r.cells[dIdx]? : Option Val) with
          | some Val.optNone | none => none
          | some (Val.optSome inner) => some inner
          | some v => some v)
        some (dedupAdjacentBy valEq (insertionSortBy valLt dVals)).length
    match evalGroupAggItems evalRE tv.cols gRows (List.zip aggs aggCols) with
    | .ok aggCells =>
      let gm : GroupMeta := { rowCount := gRows.length, distinctCount := distCount? }
      let curRow : TableRow := { cells := gKey ++ aggCells, groupMeta := some gm }
      match evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w gks with
      | .ok (.table restTV) _ =>
        .ok (.table { cols := outCols, rows := curRow :: restTV.rows }) w
      | other => other
    | .stopped b => .stopped b w
    | .outOfFuel => .outOfFuel
    | .wrong => .wrong

/-! ### `SuppressSmallGroups` Cell Masking & Complementary-Suppression Helpers -/

def suppressGroupSize (distinctBy : Option Ident) (r : TableRow) : Nat :=
  match r.groupMeta with
  | none => 0
  | some gm =>
    match distinctBy with
    | none => gm.rowCount
    | some _ => gm.distinctCount.getD 0

def extractGroupKeyCells : List ColSpec → List Val → List Val
  | [], _ => []
  | _, [] => []
  | c :: cs, v :: vs =>
    if decide (c.aggKind = .groupKey) then v :: extractGroupKeyCells cs vs
    else extractGroupKeyCells cs vs

def suppressRowLt (cols : List ColSpec) (distinctBy : Option Ident) (a b : TableRow) : Bool :=
  let sa := suppressGroupSize distinctBy a
  let sb := suppressGroupSize distinctBy b
  if sa < sb then true
  else if sb < sa then false
  else valListLt (extractGroupKeyCells cols a.cells) (extractGroupKeyCells cols b.cells)

def maskAggCells : List ColSpec → List Val → List Val
  | [], _ => []
  | _, [] => []
  | c :: cs, v :: vs =>
    let cell :=
      match c.aggKind with
      | .blending | .nonBlending => Val.optNone
      | .groupKey | .raw => v
    cell :: maskAggCells cs vs

def wrapAggCells : List ColSpec → List Val → List Val
  | [], _ => []
  | _, [] => []
  | c :: cs, v :: vs =>
    let cell :=
      match c.aggKind with
      | .blending | .nonBlending => wrapIntoOptionVal c.ty v
      | .groupKey | .raw => v
    cell :: wrapAggCells cs vs

def isMaskedAggRow (cols : List ColSpec) (r : TableRow) : Bool :=
  let rec go : List ColSpec → List Val → Bool
    | [], [] => true
    | c :: cs, v :: vs =>
      (match c.aggKind with
       | .blending | .nonBlending => match v with | .optNone => true | _ => false
       | .groupKey | .raw => true) && go cs vs
    | _, _ => false
  go cols r.cells

mutual
def evalRowExpr (fuel : Nat) (prog : Program) (env : Env) (cols : List ColSpec)
    (row : TableRow) (re : RowExpr) : PrimResult :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match re with
    | .lit v => .ok (evalLiteral v)
    | .col name =>
      match lookupColIdx? cols name with
      | some (idx, _) =>
        match row.cells[idx]? with
        | some cell => .ok cell
        | none => .wrong
      | none => .wrong
    | .outerVar name =>
      match lookupEnv env name with
      | some (_, v) => .ok v
      | none => .wrong
    | .constRef name =>
      match prog.findConst? name with
      | some cDecl => .ok (evalLiteral cDecl.value)
      | none => .wrong
    | .prim op args =>
      match evalRowExprList fuel' prog env cols row args with
      | .ok vs => evalPrimOp op vs
      | .stopped b => .stopped b
      | .outOfFuel => .outOfFuel
      | .wrong => .wrong
    | .ifE cond tBr eBr =>
      match evalRowExpr fuel' prog env cols row cond with
      | .ok (.bool true) => evalRowExpr fuel' prog env cols row tBr
      | .ok (.bool false) => evalRowExpr fuel' prog env cols row eBr
      | .ok _ => .wrong
      | other => other
    | .coalesce optE defE =>
      match evalRowExpr fuel' prog env cols row optE with
      | .ok .optNone => evalRowExpr fuel' prog env cols row defE
      | .ok (.optSome v) => .ok v
      | .ok _ => .wrong
      | other => other
    | .callPure fnName args =>
      match evalRowExprList fuel' prog env cols row args with
      | .stopped b => .stopped b
      | .outOfFuel => .outOfFuel
      | .wrong => .wrong
      | .ok vs =>
        match prog.findFun? fnName with
        | none => .wrong
        | some fDecl =>
          if vs.length != fDecl.params.length then .wrong
          else
            let callEnv : Env := (List.zip fDecl.params vs).reverse.map
              (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v })
            match eval fuel' prog callEnv TagSet.empty {} fDecl.body with
            | .ok v _ => .ok v
            | .stopped b _ => .stopped b
            | .failed m _ => .stopped { kind := .promiseViolation, message := m }
            | .outOfFuel => .outOfFuel
            | _ => .wrong
  termination_by fuel

def evalRowExprList (fuel : Nat) (prog : Program) (env : Env) (cols : List ColSpec)
    (row : TableRow) : List RowExpr → RowListResult
  | [] => .ok []
  | r :: rs =>
    match fuel with
    | 0 => .outOfFuel
    | fuel' + 1 =>
      match evalRowExpr fuel' prog env cols row r with
      | .ok v =>
        match evalRowExprList fuel' prog env cols row rs with
        | .ok vs => .ok (v :: vs)
        | other => other
      | .stopped b => .stopped b
      | .outOfFuel => .outOfFuel
      | .wrong => .wrong
  termination_by fuel

/- Deterministic fuel-indexed big-step evaluator for Dana Core IR v0.1 expressions. -/
def eval (fuel : Nat) (prog : Program) (env : Env) (pc : TagSet) (world : World)
    (expr : Expr) : Outcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match expr with
    | .lit v => .ok (evalLiteral v) world
    | .var name =>
      match lookupEnv env name with
      | some (_, v) => .ok v world
      | none => .wrong
    | .constRef name =>
      match prog.findConst? name with
      | some cDecl => .ok (evalLiteral cDecl.value) world
      | none => .wrong
    | .letE name declLTy bound body =>
      match eval fuel' prog env pc world bound with
      | .ok bVal w1 =>
        let entry : EnvEntry := { name := name, lty := declLTy.addTags pc, val := bVal }
        eval fuel' prog (entry :: env) pc w1 body
      | other => other
    | .ifE cond tBr eBr =>
      let condTags :=
        match checkExpr prog (envToTyEnv env) [] pc true cond with
        | .ok cLTy => cLTy.tags
        | .error _ => TagSet.empty
      match eval fuel' prog env pc world cond with
      | .ok (.bool true) w1 => eval fuel' prog env (pc.union condTags) w1 tBr
      | .ok (.bool false) w1 => eval fuel' prog env (pc.union condTags) w1 eBr
      | .ok _ _ => .wrong
      | other => other
    | .caseE scrut arms =>
      match checkExpr prog (envToTyEnv env) [] pc true scrut with
      | .error _ => .wrong
      | .ok scrutLTy =>
        let armPc := pc.union scrutLTy.effectiveTags
        match eval fuel' prog env pc world scrut with
        | .ok sVal w1 =>
          match matchCaseVal prog sVal scrutLTy armPc with
          | none => .wrong
          | some (cName, typedVals) =>
            match arms.find? (fun (.mk ac _ _) => ac == cName) with
            | none => .wrong
            | some (.mk _ binders armBody) =>
              if binders.length != typedVals.length then .wrong
              else
                let armEntries : Env := (List.zip binders typedVals).map
                  (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })
                eval fuel' prog (armEntries ++ env) armPc w1 armBody
        | other => other
    | .lam params fnPc retLTy body =>
      .ok (.closure params fnPc retLTy body env) world
    | .app fnExpr args =>
      match eval fuel' prog env pc world fnExpr with
      | .ok (.closure params fnPc _ body capEnv) w1 =>
        match evalSeq (eval fuel' prog env pc) w1 args with
        | .aborted out => out
        | .ok argVals w2 =>
          if argVals.length != params.length then .wrong
          else
            let paramEntries : Env := (List.zip params argVals).map
              (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })
            match eval fuel' prog (paramEntries ++ capEnv) fnPc w2 body with
            | .jumped _ _ _ => .wrong
            | other => other
      | .ok _ _ => .wrong
      | other => other
    | .call fnName args =>
      match evalSeq (eval fuel' prog env pc) world args with
      | .aborted out => out
      | .ok argVals w1 =>
        match prog.findFun? fnName with
        | none => .wrong
        | some fDecl =>
          if argVals.length != fDecl.params.length then .wrong
          else
            let callEnv : Env := (List.zip fDecl.params argVals).reverse.map
              (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })
            match eval fuel' prog callEnv fDecl.pc w1 fDecl.body with
            | .jumped _ _ _ => .wrong
            | other => other
    | .join label params rhs body =>
      let tEnv := envToTyEnv env
      let guess1 := pc.union (inferJumpPc prog label tEnv pc body)
      let rhsTEnv := extendTyEnv tEnv params
      let joinPc := guess1.union (inferJumpPc prog label rhsTEnv guess1 rhs)
      match eval fuel' prog env pc world body with
      | .jumped lbl jVals w1 =>
        if lbl == label then
          if jVals.length != params.length then .wrong
          else
            let jEntries : Env := (List.zip params jVals).map
              (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal })
            evalJoinLoop fuel' prog env label params joinPc rhs (jEntries ++ env) w1
        else
          .jumped lbl jVals w1
      | other => other
    | .jump label args =>
      match evalSeq (eval fuel' prog env pc) world args with
      | .aborted out => out
      | .ok argVals w1 => .jumped label argVals w1
    | .tuple elems =>
      match evalSeq (eval fuel' prog env pc) world elems with
      | .aborted out => out
      | .ok vs w1 => .ok (.tuple vs) w1
    | .proj tup idx =>
      match eval fuel' prog env pc world tup with
      | .ok (.tuple vs) w1 =>
        match vs[idx]? with
        | some v => .ok v w1
        | none => .wrong
      | .ok _ _ => .wrong
      | other => other
    | .ctor typeName ctorName args =>
      match evalSeq (eval fuel' prog env pc) world args with
      | .aborted out => out
      | .ok vs w1 => .ok (.ctor typeName ctorName vs) w1
    | .tableLit schema rows =>
      let tvRows : List TableRow := rows.map (fun rl =>
        { cells := rl.cells.map evalLiteral, groupMeta := none })
      .ok (.table { cols := schema.cols, rows := tvRows }) world
    | .prim op args =>
      match evalSeq (eval fuel' prog env pc) world args with
      | .aborted out => out
      | .ok vs w1 =>
        match evalPrimOp op vs with
        | .ok v => .ok v w1
        | .stopped b => .stopped b w1
        | .outOfFuel => .outOfFuel
        | .wrong => .wrong
    | .rel plan =>
      evalPlan fuel' prog env pc world plan
    | .host op args =>
      match evalSeq (eval fuel' prog env pc) world args with
      | .aborted out => out
      | .ok vs w1 => evalHostOp prog op vs w1
    | .stop kind detail =>
      match detail with
      | none =>
        .stopped { kind := kind, message := reprStr kind } world
      | some dExpr =>
        match checkExpr prog (envToTyEnv env) [] pc true dExpr with
        | .error _ => .wrong
        | .ok dLTy =>
          match eval fuel' prog env pc world dExpr with
          | .ok dVal w1 =>
            let effTags := dLTy.effectiveTags.union pc
            let msg := reprStr kind ++ ": " ++ formatDiagDetail effTags dVal
            .stopped { kind := kind, message := msg } w1
          | other => other
    | .fail msgExpr =>
      match eval fuel' prog env pc world msgExpr with
      | .ok (.text s) w1 => .failed s w1
      | .ok _ _ => .wrong
      | other => other
  termination_by fuel

def evalJoinLoop (fuel : Nat) (prog : Program) (baseEnv : Env) (label : Ident)
    (params : List (Ident × LTy)) (joinPc : TagSet) (rhs : Expr)
    (curEnv : Env) (world : World) : Outcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match eval fuel' prog curEnv joinPc world rhs with
    | .jumped lbl jVals w1 =>
      if lbl == label then
        if jVals.length != params.length then .wrong
        else
          let jEntries : Env := (List.zip params jVals).map
            (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal })
          evalJoinLoop fuel' prog baseEnv label params joinPc rhs (jEntries ++ baseEnv) w1
      else
        .jumped lbl jVals w1
    | other => other
  termination_by fuel

/-- Pure relational `Plan` evaluator (strictly free of output side-effects). -/
def evalPlan (fuel : Nat) (prog : Program) (env : Env) (pc : TagSet) (world : World)
    (plan : Plan) : Outcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match plan with
    | .sourceExpr e =>
      match eval fuel' prog env pc world e with
      | .ok (.table tv) w1 => .ok (.table tv) w1
      | .ok _ _ => .wrong
      | other => other
    | .sourceDB cap tableName schema =>
      match eval fuel' prog env pc world cap with
      | .ok (.capReadDB h db) w1 =>
        let stored? : Option StoredTable :=
          match h with
          | .real => w1.realDBTables.find? (fun st => st.db == db && st.tableName == tableName)
          | .fake id =>
            match w1.fakeDBs[id]? with
            | some fdb => fdb.tables.find? (fun st => st.tableName == tableName)
            | none => none
        match stored? with
        | some st =>
          if decide (st.schema.cols.map ColSpec.ty = schema.cols.map ColSpec.ty) then
            let rows : List TableRow := st.rows.map (fun cs => { cells := cs, groupMeta := none })
            .ok (.table { cols := schema.cols, rows := rows }) w1
          else
            .stopped { kind := .schemaConstraint, message := s!"schema drift on table '{tableName}'" } w1
        | none =>
          .ok (.table { cols := schema.cols, rows := [] }) w1
      | .ok _ _ => .wrong
      | other => other
    | .select input selCols =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let idxSpecs := selCols.filterMap (lookupColIdx? tv.cols)
        if idxSpecs.length != selCols.length then .wrong
        else
          let outCols := idxSpecs.map (fun (_, c) => { c with aggKind := .raw })
          match projectRowsByIndices (idxSpecs.map Prod.fst) tv.rows with
          | some outRows => .ok (.table { cols := outCols, rows := outRows }) w1
          | none => .wrong
      | .ok _ _ => .wrong
      | other => other
    | .drop input dropCols =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let keepIdxs := tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)
        let outCols := keepIdxs.map (fun (c, _) => { c with aggKind := .raw })
        match projectRowsByIndices (keepIdxs.map Prod.snd) tv.rows with
        | some outRows => .ok (.table { cols := outCols, rows := outRows }) w1
        | none => .wrong
      | .ok _ _ => .wrong
      | other => other
    | .rename input pairs =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let outCols := tv.cols.map (fun c =>
          match pairs.find? (fun (_, oldN) => oldN == c.name) with
          | some (newN, _) => { c with name := newN, aggKind := .raw }
          | none => { c with aggKind := .raw })
        let outRows := tv.rows.map (fun r => { r with groupMeta := none })
        .ok (.table { cols := outCols, rows := outRows }) w1
      | .ok _ _ => .wrong
      | other => other
    | .derive input items =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let initTV : TableVal := {
          cols := tv.cols.map (fun c => { c with aggKind := .raw })
          rows := tv.rows.map (fun r => { r with groupMeta := none })
        }
        evalDeriveItems prog (envToTyEnv env) (evalRowExpr fuel' prog env) w1 initTV items
      | .ok _ _ => .wrong
      | other => other
    | .filter input pred =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let outCols := tv.cols.map (fun c => { c with aggKind := .raw })
        evalFilterRows (evalRowExpr fuel' prog env) tv.cols outCols pred w1 tv.rows
      | .ok _ _ => .wrong
      | other => other
    | .distinct input cols =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let keyNames := if cols.isEmpty then tv.cols.map ColSpec.name else cols
        let outCols := tv.cols.map (fun c => { c with aggKind := .raw })
        match dedupTableRows tv.cols keyNames [] tv.rows with
        | some outRows => .ok (.table { cols := outCols, rows := outRows }) w1
        | none => .wrong
      | .ok _ _ => .wrong
      | other => other
    | .sort input keys =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let outCols := tv.cols.map (fun c => { c with aggKind := .raw })
        let sorted := insertionSortBy (rowLtByKeys tv.cols keys)
          (tv.rows.map (fun r => { r with groupMeta := none }))
        .ok (.table { cols := outCols, rows := sorted }) w1
      | .ok _ _ => .wrong
      | other => other
    | .limit input n =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let outCols := tv.cols.map (fun c => { c with aggKind := .raw })
        let taken := (tv.rows.take n).map (fun r => { r with groupMeta := none })
        .ok (.table { cols := outCols, rows := taken }) w1
      | .ok _ _ => .wrong
      | other => other
    | .join kind leftP rightP on suffixes =>
      match evalPlan fuel' prog env pc world leftP with
      | .ok (.table lTV) w1 =>
        match evalPlan fuel' prog env pc w1 rightP with
        | .ok (.table rTV) w2 =>
          match resolveJoinPairs { cols := lTV.cols } { cols := rTV.cols } on,
                buildJoinedCols kind lTV.cols rTV.cols on suffixes with
          | .ok keyPairs, .ok joinedCols =>
            let lKeyNames := keyPairs.map (fun (lc, _) => lc.name)
            let rKeyNames := keyPairs.map (fun (_, rc) => rc.name)
            let keyTags := (TagSet.unionList (keyPairs.map (fun (lc, rc) => lc.tags.union rc.tags))).union pc
            -- Enforce explicit join cardinality on right side (and left side for `One` joins)
            let rightDupBug? : Option Bug :=
              match kind with
              | .innerOne | .leftOne | .innerManyToOne | .leftManyToOne =>
                checkUniqueJoinKeys rTV.cols rKeyNames keyTags rTV.rows
              | .innerMany | .semi | .anti => none
            let leftDupBug? : Option Bug :=
              match kind with
              | .innerOne | .leftOne =>
                checkUniqueJoinKeys lTV.cols lKeyNames keyTags lTV.rows
              | _ => none
            match leftDupBug?.orElse (fun _ => rightDupBug?) with
            | some bug => .stopped bug w2
            | none =>
              let sameKeyNames : List Ident := match on with | .sameKeys ks => ks | .pairs _ => []
              let rKeepIdxs := rTV.cols.zipIdx.filter (fun (rc, _) => !sameKeyNames.contains rc.name)
              let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
              let nullRightCells : List Val := rKeepIdxs.map (fun _ => Val.optNone)
              match joinTableRows kind lTV.cols rTV.cols lKeyNames rKeyNames
                      rKeepIdxs isLeftOuter nullRightCells rTV.rows lTV.rows with
              | some outRows => .ok (.table { cols := joinedCols, rows := outRows }) w2
              | none => .wrong
          | _, _ => .wrong
        | .ok _ _ => .wrong
        | other => other
      | .ok _ _ => .wrong
      | other => other
    | .union leftP rightP =>
      match evalPlan fuel' prog env pc world leftP with
      | .ok (.table lTV) w1 =>
        match evalPlan fuel' prog env pc w1 rightP with
        | .ok (.table rTV) w2 =>
          match mergeUnionCols lTV.cols rTV.cols with
          | some outCols =>
            let outRows := (lTV.rows ++ rTV.rows).map (fun r => { r with groupMeta := none })
            .ok (.table { cols := outCols, rows := outRows }) w2
          | none => .wrong
        | .ok _ _ => .wrong
        | other => other
      | .ok _ _ => .wrong
      | other => other
    | .groupBy input keys =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let outCols := tv.cols.map (fun c =>
          if keys.contains c.name then { c with aggKind := .groupKey }
          else { c with aggKind := .raw })
        let outRows := tv.rows.map (fun r => { r with groupMeta := none })
        .ok (.table { cols := outCols, rows := outRows }) w1
      | .ok _ _ => .wrong
      | other => other
    | .summarize input aggs distinctKey =>
      match checkPlan prog (envToTyEnv env) pc true (.summarize input aggs distinctKey) with
      | .error _ => .wrong
      | .ok (.dynamic _) => .wrong
      | .ok (.table outTT) =>
        match evalPlan fuel' prog env pc world input with
        | .ok (.table tv) w1 =>
          let groupKeys := (tv.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name
          let keyCols := (tv.cols.filter (fun c => groupKeys.contains c.name)).map
            (fun c => { c with aggKind := .groupKey })
          let aggCols := outTT.cols.drop keyCols.length
          if aggCols.length != aggs.length then .wrong
          else
            match extractAllRowsKeyVals tv.cols groupKeys tv.rows with
            | none => .wrong
            | some rawKeys =>
              let sortedKeys :=
                if groupKeys.isEmpty && tv.rows.isEmpty then [[]]
                else dedupAdjacentBy valListEq (insertionSortBy valListLt rawKeys)
              let dkIdx? := distinctKey.bind (lookupColIdx? tv.cols)
              evalSummarizeGroups (evalRowExpr fuel' prog env) tv groupKeys distinctKey dkIdx?
                aggs aggCols outTT.cols w1 sortedKeys
        | .ok _ _ => .wrong
        | other => other
    | .suppressSmallGroups input minK distinctBy mode =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        let outCols := tv.cols.map (fun c =>
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
        match mode with
        | .drop =>
          let kept := (tv.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map
            (fun r => { r with groupMeta := none })
          .ok (.table { cols := outCols, rows := kept }) w1
        | .maskComplementary =>
          -- Mask all aggregate cells for groups with `size < minK`. Whenever any groups
          -- are suppressed and the total count across all suppressed groups is `< minK`,
          -- also mask the smallest surviving `>= minK` group (tie-broken by group-key cells
          -- only) so that whenever any groups remain unmasked, the combined suppressed
          -- count is at least `minK` (preventing exact single-cell recovery from a grand total).
          let smallRows := tv.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))
          let smallSum := smallRows.foldl (fun acc r => acc + suppressGroupSize distinctBy r) 0
          let validRows := tv.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))
          let compKey? : Option (List Val) :=
            if !smallRows.isEmpty && smallSum < minK then
              let sortedValid := insertionSortBy (suppressRowLt tv.cols distinctBy) validRows
              sortedValid.head?.map (fun r => extractGroupKeyCells tv.cols r.cells)
            else none
          let outRows := tv.rows.map (fun r =>
            let shouldMask :=
              decide (suppressGroupSize distinctBy r < minK) ||
              match compKey? with
              | none => false
              | some ck => valListEq (extractGroupKeyCells tv.cols r.cells) ck
            if shouldMask then
              { cells := maskAggCells tv.cols r.cells, groupMeta := none }
            else
              { cells := wrapAggCells tv.cols r.cells, groupMeta := none })
          .ok (.table { cols := outCols, rows := outRows }) w1
      | .ok _ _ => .wrong
      | other => other
    | .window input items =>
      match checkPlan prog (envToTyEnv env) pc true (.window input items) with
      | .error _ => .wrong
      | .ok (.dynamic _) => .wrong
      | .ok (.table outTT) =>
        match evalPlan fuel' prog env pc world input with
        | .ok (.table tv) w1 =>
          let initTV : TableVal := {
            cols := tv.cols.map (fun c => { c with aggKind := .raw })
            rows := tv.rows.map (fun r => { r with groupMeta := none })
          }
          match evalWindowItems initTV items with
          | some winTV => .ok (.table { cols := outTT.cols, rows := winTV.rows }) w1
          | none => .wrong
        | .ok _ _ => .wrong
        | other => other
    | .fillGaps input col stepMicros over fill =>
      match checkPlan prog (envToTyEnv env) pc true (.fillGaps input col stepMicros over fill) with
      | .error _ => .wrong
      | .ok (.dynamic _) => .wrong
      | .ok (.table outTT) =>
        match evalPlan fuel' prog env pc world input with
        | .ok (.table tv) w1 =>
          let sortSpec : List (Ident × SortDir) := (over ++ [col]).map (fun k => (k, .asc))
          let sorted := insertionSortBy (rowLtByKeys tv.cols sortSpec)
            (tv.rows.map (fun r => { r with groupMeta := none }))
          .ok (.table { cols := outTT.cols, rows := sorted }) w1
        | .ok _ _ => .wrong
        | other => other
    | .pivotWider input namesFrom valuesFrom staticCols fill =>
      match checkPlan prog (envToTyEnv env) pc true (.pivotWider input namesFrom valuesFrom staticCols fill) with
      | .error _ => .wrong
      | .ok (.dynamic _) => .wrong
      | .ok (.table outTT) =>
        match evalPlan fuel' prog env pc world input with
        | .ok (.table tv) w1 =>
          match lookupColIdx? tv.cols namesFrom, lookupColIdx? tv.cols valuesFrom with
          | some (nIdx, _), some (vIdx, _) =>
            let idCols := (tv.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map
              (fun c => { c with aggKind := .raw })
            let idNames := idCols.map ColSpec.name
            let fillVal := evalLiteral fill
            match extractAllRowsKeyVals tv.cols idNames tv.rows with
            | none => .wrong
            | some rawIds =>
              let uniqueIds := dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds)
              let outRows := uniqueIds.map (fun idKey =>
                let pRows := tv.rows.filter (fun r =>
                  match extractKeyVals tv.cols idNames r with
                  | some kv => valListEq kv idKey
                  | none => false)
                let pivCells := staticCols.map (fun sc =>
                  match pRows.find? (fun r =>
                    match (r.cells[nIdx]? : Option Val) with
                    | some (Val.text cellStr) => cellStr == sc
                    | _ => false) with
                  | some matchRow => matchRow.cells[vIdx]?.getD fillVal
                  | none => fillVal)
                { cells := idKey ++ pivCells, groupMeta := none })
              .ok (.table { cols := outTT.cols, rows := outRows }) w1
          | _, _ => .wrong
        | .ok _ _ => .wrong
        | other => other
    | .crosstab input rowsCol colsCol valuesCol fill =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        match lookupColIdx? tv.cols rowsCol, lookupColIdx? tv.cols colsCol,
              lookupColIdx? tv.cols valuesCol with
        | some (rIdx, _), some (cIdx, _), some (vIdx, _) =>
          let fillVal := evalLiteral fill
          let rKeys := dedupAdjacentBy valEq
            (insertionSortBy valLt (tv.rows.filterMap (fun r => r.cells[rIdx]?)))
          let cKeys := dedupAdjacentBy valEq
            (insertionSortBy valLt (tv.rows.filterMap (fun r => r.cells[cIdx]?)))
          let headers := rowsCol :: cKeys.map renderPublicVal
          let matrix := rKeys.map (fun rk =>
            rk :: cKeys.map (fun ck =>
              match tv.rows.find? (fun r =>
                match r.cells[rIdx]?, r.cells[cIdx]? with
                | some rv, some cv => valEq rv rk && valEq cv ck
                | _, _ => false) with
              | some mr => mr.cells[vIdx]?.getD fillVal
              | none => fillVal))
          .ok (.dynTable headers matrix) w1
        | _, _, _ => .wrong
      | .ok _ _ => .wrong
      | other => other
    | .redact input col replacement =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        match lookupColIdx? tv.cols col with
        | none => .wrong
        | some (cIdx, _) =>
          let outCols := tv.cols.map (fun c =>
            if c.name == col then
              { c with ty := .text, tags := pc, bucketed := false, aggKind := .raw }
            else { c with aggKind := .raw })
          let outRows := tv.rows.map (fun r =>
            { cells := r.cells.set cIdx (.text replacement), groupMeta := none })
          .ok (.table { cols := outCols, rows := outRows }) w1
      | .ok _ _ => .wrong
      | other => other
    | .pseudonymize input col secretExpr =>
      match evalPlan fuel' prog env pc world input with
      | .ok (.table tv) w1 =>
        match eval fuel' prog env pc w1 secretExpr with
        | .ok (.capSecret h sName) w2 =>
          match lookupColIdx? tv.cols col with
          | none => .wrong
          | some (cIdx, _) =>
            let keyMat : String :=
              match h with
              | .real =>
                match w2.realSecrets.find? (fun (n, _) => n == sName) with
                | some (_, sv) => sv
                | none => sName
              | .fake id => w2.fakeSecrets[id]?.getD sName
            let outCols := tv.cols.map (fun c =>
              if c.name == col then
                { c with ty := .text, tags := (c.tags.remove "pii").union pc, bucketed := false, aggKind := .raw }
              else { c with aggKind := .raw })
            match mapPseudonymizeRows keyMat cIdx tv.rows with
            | some outRows => .ok (.table { cols := outCols, rows := outRows }) w2
            | none => .wrong
        | .ok _ _ => .wrong
        | other => other
      | .ok _ _ => .wrong
      | other => other
  termination_by fuel
end

/-! ## Top-Level Entry Runner -/

def buildEntryCapVal (prog : Program) (ty : Ty) : Option Val :=
  match ty with
  | .args => some .capArgs
  | .clock => some .capClock
  | .console allows => some (.capConsole .real allows)
  | .readFiles => some (.capReadFiles .real)
  | .writeFiles root allows => some (.capWriteFiles .real root allows)
  | .readDB db => some (.capReadDB .real db)
  | .writeTable db tbl _ _ _ => some (.capWriteTable .real db tbl)
  | .rawReadDB db => some (.capRawReadDB db)
  | .httpsAllow host allows => some (.capHttpsAllow .real host allows)
  | .secret name => some (.capSecret .real name)
  | .declassify allows => some (.capDeclassify allows)
  | _ =>
    let _ := prog
    none

def mkEntryEnv (prog : Program) : List (Ident × LTy) → Option Env
  | [] => some []
  | (pName, pLTy) :: rest => do
    let capVal ← buildEntryCapVal prog pLTy.ty
    let tl ← mkEntryEnv prog rest
    some ({ name := pName, lty := pLTy, val := capVal } :: tl)

def entryCapRequiredExportTags (ty : Ty) : TagSet :=
  match ty with
  | .console allows
  | .writeFiles _ allows
  | .httpsAllow _ allows => allows
  | _ => TagSet.empty

def checkEntryExportGate (params : List (Ident × LTy)) (w : World) : Option Bug :=
  let req := TagSet.unionList (params.map (fun (_, l) => entryCapRequiredExportTags l.ty))
  if req.isEmpty || req.subset w.runtimeAllowExport then none
  else
    some {
      kind := .exportGateDenied
      message := "runtime --allow-export authorization required for sensitive external sink"
    }

/-- Typecheck and evaluate `prog.entry` (or return ok unit report if `entry = none`). -/
def runProgram (fuel : Nat) (prog : Program) (initWorld : World := {}) :
    Except String ExecReport := do
  checkProgram prog
  match prog.entry with
  | none =>
    match extractReport (.ok .unit initWorld) with
    | some rep => .ok rep
    | none => .error "internal error extracting empty report"
  | some mainName =>
    match prog.findFun? mainName with
    | none => .error s!"entry '{mainName}' not found"
    | some mainFn =>
      match mkEntryEnv prog mainFn.params.reverse with
      | none => .error "entry has non-capability parameters"
      | some initEnv =>
        match checkEntryExportGate mainFn.params initWorld with
        | some bug =>
          match extractReport (.stopped bug initWorld) with
          | some rep => .ok rep
          | none => .error "unable to extract report"
        | none =>
          let out := eval fuel prog initEnv TagSet.empty initWorld mainFn.body
          match out with
          | .outOfFuel => .error "execution exhausted fuel"
          | .wrong => .error "internal soundness violation: stuck state"
          | .jumped lbl _ _ => .error s!"internal soundness violation: uncaught jump '{lbl}'"
          | _ =>
            match extractReport out with
            | some rep => .ok rep
            | none => .error "unable to extract report"

end DanaCore
