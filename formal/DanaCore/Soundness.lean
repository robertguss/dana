/-
  DanaCore/Soundness.lean
  Theorem 1 — Schema & Type Soundness for Dana Core IR v0.1.

  Proves with zero unproved obligations and zero custom axioms that well-typed Dana Core
  expressions, relational plans, and programs never evaluate to `Outcome.wrong`,
  closed evaluations never escape with `Outcome.jumped`, and every normal outcome
  `Outcome.ok v w'` strictly preserves `ValWf` (including exact `TableTy` column
  schemas, unified `Option` invariants, and `SuppressSmallGroups` group-size floors)
  and `WorldWf`.
-/
import DanaCore.Syntax
import DanaCore.Check
import DanaCore.Eval

namespace DanaCore

/-! ## Structural Table Schema Invariant (Tag-Set Agnostic) -/

/-- Structural schema well-formedness on `TableTy` (column uniqueness, non-nested
    unified `Option` column types, `bucketed -> Text`, and `groupKey <-> groupedBy`). -/
def TableSchemaWf (prog : Program) (tt : TableTy) : Bool :=
  let gks := tt.groupedBy.getD []
  distinctIdents (tt.cols.map ColSpec.name) &&
  tt.cols.all (fun c =>
    validScalarTy prog c.ty &&
    (if c.bucketed then decide (c.ty = .text) else true) &&
    decide (decide (c.aggKind = .groupKey) = gks.contains c.name)) &&
  match tt.groupedBy with
  | none => true
  | some ks => distinctIdents ks && ks.all (fun k => (tt.findCol? k).isSome)

theorem validTableTy_imp_schemaWf {prog : Program} {tt : TableTy}
    (h : validTableTy prog tt = true) : TableSchemaWf prog tt = true := by
  simp only [validTableTy, TableSchemaWf, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨h.1.1.1.1, ?_⟩, h.2⟩
  intro c hc
  have hc0 := h.1.1.1.2 c hc
  simp only [validColSpec, Bool.and_eq_true] at hc0
  exact ⟨⟨hc0.1.1.1, hc0.1.2⟩, hc0.2⟩

@[simp] theorem tableSchemaWf_with_tags {prog : Program} (tt : TableTy) (rt ot : TagSet) :
    TableSchemaWf prog { tt with rowTags := rt, orderTags := ot } = TableSchemaWf prog tt := rfl

@[simp] theorem LTy.addTags_ty (l : LTy) (ts : TagSet) : (l.addTags ts).ty = l.ty := by
  cases l; rfl

/-! ## Runtime Value, Table, Environment, World, and Outcome Well-Formedness -/

mutual
inductive ValWf (prog : Program) : Val → Ty → Prop where
  | unit : ValWf prog .unit .unit
  | bool (b : Bool) : ValWf prog (.bool b) .bool
  | int {n : Int} (hr : inInt64Range n = true) : ValWf prog (.int n) .int
  | decimal {d : Int} (hr : inDecimalRange d = true) : ValWf prog (.decimal d) .decimal
  | float (f : Float64) : ValWf prog (.float f) .float
  | text (s : String) : ValWf prog (.text s) .text
  | bytes (bs : List UInt8) : ValWf prog (.bytes bs) .bytes
  | date (d : Int) : ValWf prog (.date d) .date
  | timestamp (ts : Int) : ValWf prog (.timestamp ts) .timestamp
  | duration (dur : Int) : ValWf prog (.duration dur) .duration
  | optNone (inner : Ty) : ValWf prog .optNone (.option inner)
  | optSome {v : Val} {inner : Ty} (hv : ValWf prog v inner) :
      ValWf prog (.optSome v) (.option inner)
  | resOk {v : Val} {okTy errTy : Ty} (hv : ValWf prog v okTy) :
      ValWf prog (.resOk v) (.result okTy errTy)
  | resErr {e : Val} {okTy errTy : Ty} (he : ValWf prog e errTy) :
      ValWf prog (.resErr e) (.result okTy errTy)
  | tuple {vs : List Val} {ltys : List LTy}
      (hvs : ValListWf prog vs ltys) :
      ValWf prog (.tuple vs) (.tuple ltys)
  | list {vs : List Val} {elem : LTy}
      (hvs : ValAllWf prog vs elem.ty) :
      ValWf prog (.list vs) (.list elem)
  | map {kvs : List (Val × Val)} {kLTy vLTy : LTy}
      (hkvs : ValPairsWf prog kvs kLTy.ty vLTy.ty) :
      ValWf prog (.map kvs) (.map kLTy vLTy)
  | ctor {dName cName : Ident} {vs : List Val} {dDecl : DataDecl} {cDecl : CtorDecl}
      (hd : prog.findData? dName = some dDecl)
      (hc : dDecl.ctors.find? (fun c => c.name == cName) = some cDecl)
      (hvs : ValListWf prog vs cDecl.fields) :
      ValWf prog (.ctor dName cName vs) (.data dName)
  | table {tv : TableVal} {tt : TableTy}
      (hcols : tv.cols = tt.cols)
      (hschema : TableSchemaWf prog tt = true)
      (hrows : RowsWf prog tv.rows tt.cols tt.summarized tt.distinctBy.isSome) :
      ValWf prog (.table tv) (.table tt)
  | dynTable (hs : List String) (rs : List (List Val)) (ts : TagSet) :
      ValWf prog (.dynTable hs rs) (.dynamicTable ts)
  | chart (cv : ChartVal) (ts : TagSet) :
      ValWf prog (.chart cv) (.chart ts)
  | report (rv : ReportVal) (ts : TagSet) :
      ValWf prog (.report rv) (.report ts)
  | profile (pv : ProfileVal) (ts : TagSet) :
      ValWf prog (.profile pv) (.profile ts)
  | linearModel (s i r2 : Float64) :
      ValWf prog (.linearModel s i r2) .linearModel
  | statTest (s p : Float64) :
      ValWf prog (.statTest s p) .statTest
  | closure {params : List (Ident × LTy)} {fnPc : TagSet} {retLTy bodyLTy : LTy}
      {body : Expr} {capEnv : Env}
      (henv : EnvWf prog capEnv)
      (hchk : checkExpr prog (extendTyEnv (envToTyEnv capEnv) params) [] fnPc true body = .ok bodyLTy)
      (hsub : ltySubtype bodyLTy retLTy = true) :
      ValWf prog (.closure params fnPc retLTy body capEnv) (.fn (params.map Prod.snd) fnPc retLTy)
  | capArgs : ValWf prog .capArgs .args
  | capClock : ValWf prog .capClock .clock
  | capConsole (h : CapHandle) (allows : TagSet) :
      ValWf prog (.capConsole h allows) (.console allows)
  | capReadFiles (h : CapHandle) :
      ValWf prog (.capReadFiles h) .readFiles
  | capWriteFiles (h : CapHandle) (root : String) (allows : TagSet) :
      ValWf prog (.capWriteFiles h root allows) (.writeFiles root allows)
  | capReadDB (h : CapHandle) (db : Ident) :
      ValWf prog (.capReadDB h db) (.readDB db)
  | capWriteTable (h : CapHandle) (db tbl : Ident) (cols : List ColSpec) (rt allows : TagSet) :
      ValWf prog (.capWriteTable h db tbl) (.writeTable db tbl cols rt allows)
  | capRawReadDB (db : Ident) :
      ValWf prog (.capRawReadDB db) (.rawReadDB db)
  | capHttpsAllow (h : CapHandle) (host : String) (allows : TagSet) :
      ValWf prog (.capHttpsAllow h host allows) (.httpsAllow host allows)
  | capSecret (h : CapHandle) (name : String) :
      ValWf prog (.capSecret h name) (.secret name)
  | capDeclassify (allows : TagSet) :
      ValWf prog (.capDeclassify allows) (.declassify allows)

inductive ValListWf (prog : Program) : List Val → List LTy → Prop where
  | nil : ValListWf prog [] []
  | cons {v vs l ls} (hv : ValWf prog v l.ty) (htl : ValListWf prog vs ls) :
      ValListWf prog (v :: vs) (l :: ls)

inductive ValAllWf (prog : Program) : List Val → Ty → Prop where
  | nil (ty : Ty) : ValAllWf prog [] ty
  | cons {v vs ty} (hv : ValWf prog v ty) (htl : ValAllWf prog vs ty) :
      ValAllWf prog (v :: vs) ty

inductive ValPairsWf (prog : Program) : List (Val × Val) → Ty → Ty → Prop where
  | nil (kt vt : Ty) : ValPairsWf prog [] kt vt
  | cons {k v rest kt vt} (hk : ValWf prog k kt) (hv : ValWf prog v vt)
      (htl : ValPairsWf prog rest kt vt) :
      ValPairsWf prog ((k, v) :: rest) kt vt

inductive CellsWf (prog : Program) : List Val → List ColSpec → Prop where
  | nil : CellsWf prog [] []
  | cons {v vs c cs} (hv : ValWf prog v c.ty.toTy) (htl : CellsWf prog vs cs) :
      CellsWf prog (v :: vs) (c :: cs)

inductive RowsWf (prog : Program) : List TableRow → List ColSpec → Bool → Bool → Prop where
  | nil (cols : List ColSpec) (sumB dkB : Bool) : RowsWf prog [] cols sumB dkB
  | cons {r rs cols sumB dkB}
      (hcells : CellsWf prog r.cells cols)
      (hmeta : sumB = true → ∃ gm, r.groupMeta = some gm ∧ (dkB = true → gm.distinctCount.isSome = true))
      (htl : RowsWf prog rs cols sumB dkB) :
      RowsWf prog (r :: rs) cols sumB dkB

inductive EnvWf (prog : Program) : Env → Prop where
  | nil : EnvWf prog []
  | cons {e : EnvEntry} {rest : Env}
      (hv : ValWf prog e.val e.lty.ty)
      (htl : EnvWf prog rest) :
      EnvWf prog (e :: rest)
end

structure WorldWf (prog : Program) (w : World) : Prop where
  csvWf : ∀ path gTV bTV, (path, gTV, bTV) ∈ w.realCsvFixtures →
    RowsWf prog gTV.rows gTV.cols false false ∧
    RowsWf prog bTV.rows bTV.cols false false
  realDbWf : ∀ st, st ∈ w.realDBTables →
    ∀ cs, cs ∈ st.rows → CellsWf prog cs st.schema.cols
  fakeDbWf : ∀ fdb, fdb ∈ w.fakeDBs → ∀ st, st ∈ fdb.tables →
    ∀ cs, cs ∈ st.rows → CellsWf prog cs st.schema.cols

theorem worldWf_empty (prog : Program) : WorldWf prog {} :=
  { csvWf := fun _ _ _ h => by cases h
    realDbWf := fun _ h => by cases h
    fakeDbWf := fun _ h => by cases h }

inductive PrimResultWf (prog : Program) (expectedTy : Ty) : PrimResult → Prop where
  | ok {v : Val} (hv : ValWf prog v expectedTy) : PrimResultWf prog expectedTy (.ok v)
  | stopped (b : Bug) : PrimResultWf prog expectedTy (.stopped b)
  | outOfFuel : PrimResultWf prog expectedTy .outOfFuel

inductive RowListResultWf (prog : Program) : List LTy → RowListResult → Prop where
  | ok {vs : List Val} {ltys : List LTy} (hvs : ValListWf prog vs ltys) :
      RowListResultWf prog ltys (.ok vs)
  | stopped (ltys : List LTy) (b : Bug) : RowListResultWf prog ltys (.stopped b)
  | outOfFuel (ltys : List LTy) : RowListResultWf prog ltys .outOfFuel

inductive OutcomeWf (prog : Program) (jenv : JoinEnv) (expectedTy : Ty) : Outcome → Prop where
  | ok {v : Val} {w : World} (hv : ValWf prog v expectedTy) (hw : WorldWf prog w) :
      OutcomeWf prog jenv expectedTy (.ok v w)
  | stopped (b : Bug) {w : World} (hw : WorldWf prog w) :
      OutcomeWf prog jenv expectedTy (.stopped b w)
  | failed (m : String) {w : World} (hw : WorldWf prog w) :
      OutcomeWf prog jenv expectedTy (.failed m w)
  | outOfFuel :
      OutcomeWf prog jenv expectedTy .outOfFuel
  | jumped {lbl : Ident} {vs : List Val} {w : World} {sig : JoinSig}
      (hlook : lookupJoinEnv jenv lbl = some sig)
      (hvs : ValListWf prog vs (sig.params.map Prod.snd))
      (hw : WorldWf prog w) :
      OutcomeWf prog jenv expectedTy (.jumped lbl vs w)

theorem OutcomeWf.not_wrong {prog jenv ty out} (h : OutcomeWf prog jenv ty out) :
    out ≠ .wrong := by
  intro heq; subst heq; nomatch h

theorem OutcomeWf.not_jumped_nil {prog ty out lbl vs w}
    (h : OutcomeWf prog [] ty out) :
    out ≠ .jumped lbl vs w := by
  intro heq; subst heq
  cases h with
  | jumped hlook _ _ => simp [lookupJoinEnv] at hlook

theorem OutcomeWf.cast_ty {prog jenv t1 t2 out} (heq : t1 = t2)
    (h : OutcomeWf prog jenv t1 out) : OutcomeWf prog jenv t2 out := by
  subst heq; exact h

theorem OutcomeWf.weaken_nil {prog jenv t out}
    (h : OutcomeWf prog [] t out) : OutcomeWf prog jenv t out := by
  cases h with
  | ok hv hw => exact .ok hv hw
  | stopped b hw => exact .stopped b hw
  | failed m hw => exact .failed m hw
  | outOfFuel => exact .outOfFuel
  | jumped hlook _ _ => simp [lookupJoinEnv] at hlook

theorem OutcomeWf.abort_non_ok {prog jenv t1 t2 out}
    (h : OutcomeWf prog jenv t1 out)
    (hnotok : ∀ v w, out ≠ .ok v w) :
    OutcomeWf prog jenv t2 out := by
  cases h with
  | ok hv hw => exact absurd rfl (hnotok _ _)
  | stopped b hw => exact .stopped b hw
  | failed m hw => exact .failed m hw
  | outOfFuel => exact .outOfFuel
  | jumped hlook hvs hw => exact .jumped hlook hvs hw

/-! ## Structural & List Lemmas on `distinctIdents`, `ValWf`, `CellsWf`, `RowsWf`, `EnvWf` -/

theorem distinctIdents_not_mem {x : Ident} {xs : List Ident}
    (h : distinctIdents (x :: xs) = true) : x ∉ xs ∧ distinctIdents xs = true := by
  simp only [distinctIdents, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hm => ?_, h.2⟩
  have hc : xs.contains x = true := List.contains_iff_mem.mpr hm
  rw [hc] at h
  exact absurd h.1 (by decide)

theorem filter_mem_not_mem {α : Type} (p : α → Bool) {x : α} {xs : List α}
    (h : x ∉ xs) : x ∉ xs.filter p :=
  fun hm => h (List.mem_filter.mp hm).1

theorem distinctIdents_filter (p : ColSpec → Bool) :
    ∀ {cols : List ColSpec},
      distinctIdents (cols.map ColSpec.name) = true →
      distinctIdents ((cols.filter p).map ColSpec.name) = true
  | [], _ => rfl
  | c :: cs, hd => by
    rcases distinctIdents_not_mem hd with ⟨hnot, htl⟩
    simp only [List.filter_cons]
    by_cases hp : p c = true
    · simp only [hp, ↓reduceIte, List.map_cons, distinctIdents, Bool.and_eq_true]
      refine ⟨?_, distinctIdents_filter p htl⟩
      cases hc : ((cs.filter p).map ColSpec.name).contains c.name with
      | false => rfl
      | true =>
        exfalso
        rw [List.contains_iff_mem, List.mem_map] at hc
        rcases hc with ⟨c', hc', hname⟩
        exact hnot (hname ▸ List.mem_map_of_mem (List.mem_filter.mp hc').1)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact distinctIdents_filter p htl

theorem resetRawTableSchemaWf {prog : Program} {cols : List ColSpec}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text))
    (rt ot : TagSet) :
    TableSchemaWf prog {
      cols := cols.map (fun c => { c with aggKind := .raw })
      rowTags := rt, orderTags := ot, groupedBy := none, summarized := false, distinctBy := none
    } = true := by
  have hnames : (cols.map (fun c => { c with aggKind := .raw })).map ColSpec.name = cols.map ColSpec.name := by
    induction cols <;> simp [*]
  simp only [TableSchemaWf, Option.getD_none, hnames, huniq, Bool.true_and, Bool.and_true, List.all_eq_true]
  intro c' hc'
  rw [List.mem_map] at hc'
  rcases hc' with ⟨c, hc, rfl⟩
  rcases hcols c hc with ⟨hv, hb⟩
  simp only [hv, Bool.true_and, Bool.and_eq_true]
  constructor
  · by_cases hbk : c.bucketed = true <;> simp [hbk, hb]
  · simp

theorem tableSchemaWf_cols_props {prog : Program} {tt : TableTy}
    (h : TableSchemaWf prog tt = true) :
    distinctIdents (tt.cols.map ColSpec.name) = true ∧
    ∀ c ∈ tt.cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) := by
  simp only [TableSchemaWf, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1.1, fun c hc => ?_⟩
  have h1 := h.1.2 c hc
  refine ⟨h1.1.1, fun hb => ?_⟩
  have hb0 := h1.1.2
  simp [hb] at hb0
  exact hb0

theorem ValListWf.length_eq {prog : Program} :
    ∀ {vs : List Val} {ltys : List LTy}, ValListWf prog vs ltys → vs.length = ltys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ htl => congrArg (· + 1) htl.length_eq

theorem ValListWf.getElem?_wf {prog : Program} :
    ∀ {vs : List Val} {ltys : List LTy} {idx : Nat} {lty : LTy},
      ValListWf prog vs ltys → ltys[idx]? = some lty →
      ∃ v, vs[idx]? = some v ∧ ValWf prog v lty.ty
  | _ :: _, _ :: _, 0, _, .cons hv _, hget => by
    simp at hget; subst hget; exact ⟨_, rfl, hv⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ htl, hget =>
    htl.getElem?_wf hget
  | [], [], _, _, .nil, hget => by simp at hget

theorem CellsWf.length_eq {prog : Program} :
    ∀ {vs : List Val} {cs : List ColSpec}, CellsWf prog vs cs → vs.length = cs.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ htl => congrArg (· + 1) htl.length_eq

theorem CellsWf.append {prog : Program} :
    ∀ {v1 v2 : List Val} {c1 c2 : List ColSpec},
      CellsWf prog v1 c1 → CellsWf prog v2 c2 → CellsWf prog (v1 ++ v2) (c1 ++ c2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, _, _ :: _, _, .cons hv htl, h2 => .cons hv (htl.append h2)

theorem CellsWf.congr_ty {prog : Program} :
    ∀ {vs : List Val} {c1 c2 : List ColSpec},
      c1.map ColSpec.ty = c2.map ColSpec.ty →
      CellsWf prog vs c1 → CellsWf prog vs c2
  | [], [], [], _, .nil => .nil
  | _ :: _, c :: cs1, d :: cs2, hmap, .cons hv htl => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    exact .cons (hmap.1 ▸ hv) (htl.congr_ty hmap.2)
  | _ :: _, _ :: _, [], hmap, _ => by simp at hmap
  | [], [], _ :: _, hmap, _ => by simp at hmap

theorem CellsWf.getElem?_wf {prog : Program} :
    ∀ {vs : List Val} {cs : List ColSpec} {idx : Nat} {c : ColSpec},
      CellsWf prog vs cs → cs[idx]? = some c →
      ∃ v, vs[idx]? = some v ∧ ValWf prog v c.ty.toTy
  | _ :: _, _ :: _, 0, _, .cons hv _, hget => by
    simp at hget; subst hget; exact ⟨_, rfl, hv⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ htl, hget =>
    htl.getElem?_wf hget
  | [], [], _, _, .nil, hget => by simp at hget

theorem RowsWf.to_forall {prog : Program} :
    ∀ {rs : List TableRow} {cols : List ColSpec} {s d : Bool},
      RowsWf prog rs cols s d → ∀ r ∈ rs, CellsWf prog r.cells cols
  | [], _, _, _, .nil _ _ _, _, hmem => nomatch hmem
  | _ :: _, _, _, _, .cons hcells _ htl, _, hmem => by
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact hcells
    · exact htl.to_forall _ hrest

theorem RowsWf.of_forall_raw {prog : Program} {cols : List ColSpec} :
    ∀ {rs : List TableRow}, (∀ r ∈ rs, CellsWf prog r.cells cols) → RowsWf prog rs cols false false
  | [], _ => .nil cols false false
  | r :: rs, hall =>
    .cons (hall r (.head _)) (fun h => by simp at h)
      (RowsWf.of_forall_raw (fun r' hr' => hall r' (.tail _ hr')))

theorem RowsWf.congr_ty_raw {prog : Program} {c1 c2 : List ColSpec}
    (hty : c1.map ColSpec.ty = c2.map ColSpec.ty) {rs : List TableRow} {s d : Bool}
    (hr : RowsWf prog rs c1 s d) :
    RowsWf prog (rs.map (fun r => { r with groupMeta := none })) c2 false false := by
  apply RowsWf.of_forall_raw
  intro r' hr'
  rw [List.mem_map] at hr'
  rcases hr' with ⟨r, hrmem, rfl⟩
  exact (hr.to_forall r hrmem).congr_ty hty

theorem ValAllWf.of_forall {prog : Program} {ty : Ty} :
    ∀ {vs : List Val}, (∀ v ∈ vs, ValWf prog v ty) → ValAllWf prog vs ty
  | [], _ => .nil ty
  | v :: _, h => .cons (h v (.head _)) (ValAllWf.of_forall (fun u hu => h u (.tail _ hu)))

theorem ValAllWf.to_forall {prog : Program} {ty : Ty} :
    ∀ {vs : List Val}, ValAllWf prog vs ty → ∀ v ∈ vs, ValWf prog v ty
  | [], .nil _, _, hm => nomatch hm
  | _ :: _, .cons hv htl, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hr
    · exact hv
    · exact htl.to_forall _ hr

theorem mem_insertSortedBy {α : Type} (lt : α → α → Bool) (x y : α) :
    ∀ (ys : List α), y ∈ insertSortedBy lt x ys → y = x ∨ y ∈ ys
  | [], hm => by simp [insertSortedBy] at hm; exact Or.inl hm
  | z :: zs, hm => by
    simp only [insertSortedBy] at hm
    by_cases h : lt z x = true
    · simp only [h, ↓reduceIte, List.mem_cons] at hm
      rcases hm with rfl | hrest
      · exact Or.inr (.head _)
      · rcases mem_insertSortedBy lt x y zs hrest with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (.tail _ hz)
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hm
      rcases hm with rfl | hm'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr hm')

theorem mem_insertionSortBy {α : Type} (lt : α → α → Bool) (y : α) :
    ∀ (xs : List α), y ∈ insertionSortBy lt xs → y ∈ xs
  | [], hm => nomatch hm
  | x :: xs, hm => by
    simp only [insertionSortBy] at hm
    rcases mem_insertSortedBy lt x y _ hm with rfl | hrest
    · exact .head _
    · exact .tail _ (mem_insertionSortBy lt y xs hrest)

theorem mem_dedupAdjacentBy {α : Type} (eq : α → α → Bool) (y : α) :
    ∀ (xs : List α), y ∈ dedupAdjacentBy eq xs → y ∈ xs
  | [], hm => nomatch hm
  | [x], hm => hm
  | x1 :: x2 :: rest, hm => by
    simp only [dedupAdjacentBy] at hm
    by_cases h : eq x1 x2 = true
    · simp only [h, ↓reduceIte] at hm
      exact .tail _ (mem_dedupAdjacentBy eq y (x2 :: rest) hm)
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hm
      rcases hm with rfl | hrest
      · exact .head _
      · exact .tail _ (mem_dedupAdjacentBy eq y (x2 :: rest) hrest)

theorem lookupEnv_of_envWf {prog : Program} :
    ∀ {env : Env} {name : Ident} {lty : LTy},
      EnvWf prog env →
      lookupTyEnv (envToTyEnv env) name = some lty →
      ∃ v, lookupEnv env name = some (lty, v) ∧ ValWf prog v lty.ty
  | [], _, _, .nil, hlook => by simp [envToTyEnv, lookupTyEnv] at hlook
  | e :: rest, name, lty, .cons hv htl, hlook => by
    simp only [envToTyEnv, List.map_cons, lookupTyEnv, lookupEnv] at hlook ⊢
    by_cases h : e.name = name
    · simp only [h, ↓reduceIte, Option.some.injEq] at hlook ⊢
      subst hlook
      exact ⟨e.val, rfl, hv⟩
    · simp only [h, ↓reduceIte] at hlook ⊢
      exact lookupEnv_of_envWf htl hlook

theorem extendEnv_wf {prog : Program} :
    ∀ {params : List (Ident × LTy)} {vs : List Val} {base : Env},
      ValListWf prog vs (params.map Prod.snd) →
      EnvWf prog base →
      EnvWf prog ((List.zip params vs).map (fun ((n, l), v) => { name := n, lty := l, val := v }) ++ base)
  | [], [], _, .nil, hbase => hbase
  | (_, _) :: _, _ :: _, _, .cons hv htl, hbase =>
    .cons hv (extendEnv_wf htl hbase)

theorem envToTyEnv_zip_params :
    ∀ (params : List (Ident × LTy)) (vs : List Val),
      vs.length = params.length →
      envToTyEnv ((List.zip params vs).map (fun ((n, l), v) => { name := n, lty := l, val := v })) = params
  | [], [], _ => rfl
  | (n, l) :: ps, v :: vs, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [envToTyEnv, List.zip_cons_cons, List.map_cons]
    exact congrArg ((n, l) :: ·) (envToTyEnv_zip_params ps vs hlen)

theorem envToTyEnv_append (e1 e2 : Env) :
    envToTyEnv (e1 ++ e2) = envToTyEnv e1 ++ envToTyEnv e2 := by
  simp [envToTyEnv, List.map_append]

theorem envToTyEnv_reverse (e : Env) :
    envToTyEnv e.reverse = (envToTyEnv e).reverse := by
  simp [envToTyEnv, List.map_reverse]

/-! ## Monotonicity of `inSpec` (`false → true`) in `checkExpr` and `checkPlan` -/

theorem checkHostOp_inSpec_mono {prog : Program} {pc : TagSet} {inSpec : Bool}
    {op : HostOp} {args : List LTy} {lty : LTy}
    (h : checkHostOp prog pc inSpec op args = .ok lty) :
    checkHostOp prog pc true op args = .ok lty := by
  cases inSpec
  · unfold checkHostOp at h ⊢
    split at h <;> simp_all
  · exact h

mutual
theorem checkExpr_inSpec_true {prog : Program} :
    ∀ {env : TyEnv} {jenv : JoinEnv} {pc : TagSet} {inSpec : Bool} {e : Expr} {lty : LTy},
      checkExpr prog env jenv pc inSpec e = .ok lty →
      checkExpr prog env jenv pc true e = .ok lty
  | _, _, _, true, _, _, h => h
  | env, jenv, pc, false, e, lty, h => by
    cases e with
    | lit _ | var _ | constRef _ | tableLit _ _ => exact h
    | letE n dLTy bnd body =>
      unfold checkExpr at h ⊢
      cases hv : validLTy prog dLTy <;> simp only [hv, Bool.not_false, Bool.not_true, ↓reduceIte] at h ⊢
      · contradiction
      · cases hj : noFreeJumps [] bnd <;> simp only [hj, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
        · contradiction
        · cases hb : checkExpr prog env [] pc false bnd with
          | error _ => simp [hb] at h
          | ok bLTy =>
            rw [checkExpr_inSpec_true hb]; simp only [hb] at h
            cases hs : ltySubtype bLTy dLTy <;> simp only [hs, Bool.not_false, Bool.not_true, ↓reduceIte] at h ⊢
            · contradiction
            · exact checkExpr_inSpec_true h
    | ifE cond tBr eBr =>
      unfold checkExpr at h ⊢
      cases hj : noFreeJumps [] cond <;> simp only [hj, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases hc : checkExpr prog env [] pc false cond with
        | error _ => simp [hc] at h
        | ok cLTy =>
          rw [checkExpr_inSpec_true hc]; simp only [hc] at h
          cases h2 : decide (cLTy.ty = .bool) <;> simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
          · contradiction
          · cases ht : checkExpr prog env jenv (pc.union cLTy.tags) false tBr with
            | error _ => simp [ht] at h
            | ok tLTy =>
              rw [checkExpr_inSpec_true ht]; simp only [ht] at h
              cases he : checkExpr prog env jenv (pc.union cLTy.tags) false eBr with
              | error _ => simp [he] at h
              | ok eLTy =>
                rw [checkExpr_inSpec_true he]; simpa [he] using h
    | caseE scrut arms =>
      unfold checkExpr at h ⊢
      cases hj : noFreeJumps [] scrut <;> simp only [hj, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases hs : checkExpr prog env [] pc false scrut with
        | error _ => simp [hs] at h
        | ok sLTy =>
          rw [checkExpr_inSpec_true hs]; simp only [hs] at h ⊢
          cases hsp : expectedCaseSpecs prog sLTy.ty sLTy.effectiveTags with
          | error _ => simp [hsp] at h
          | ok specs =>
            simp only [hsp] at h ⊢
            split at h
            · contradiction
            · rename_i hgood
              simp only [hgood, Bool.false_eq_true, ↓reduceIte]
              cases ha : checkCaseArms prog env jenv (pc.union sLTy.effectiveTags) false specs arms with
              | error _ => rw [ha] at h; contradiction
              | ok armLTys =>
                rw [checkCaseArms_inSpec_true ha]
                rw [ha] at h
                simpa using h
    | lam params fnPc retLTy body =>
      unfold checkExpr at h ⊢
      cases h1 : (!distinctIdents (params.map Prod.fst) || !params.all (fun x => validLTy prog x.2) || !validTagSet prog fnPc || !validLTy prog retLTy) <;>
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
      · cases h2 : noFreeJumps [] body <;> simp only [h2, Bool.not_false, Bool.not_true, ↓reduceIte] at h ⊢
        · contradiction
        · cases h3 : fnPc.subset retLTy.effectiveTags <;>
            simp only [h3, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
          · contradiction
          · cases hb : checkExpr prog (extendTyEnv env params) [] fnPc false body with
            | error _ => simp [hb] at h
            | ok bLTy => rw [checkExpr_inSpec_true hb]; simpa [hb] using h
      · contradiction
    | app fnE args =>
      unfold checkExpr at h ⊢
      cases h1 : (!noFreeJumps [] fnE || !noFreeJumpsList args) <;>
        simp only [h1, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · cases hf : checkExpr prog env [] pc false fnE with
        | error _ => simp [hf] at h
        | ok fLTy =>
          rw [checkExpr_inSpec_true hf]; simp only [hf] at h
          cases ha : checkExprList prog env pc false args with
          | error _ => simp [ha] at h
          | ok aLTys => rw [checkExprList_inSpec_true ha]; simpa [ha] using h
      · contradiction
    | call fnName args =>
      unfold checkExpr at h ⊢
      cases h1 : noFreeJumpsList args <;>
        simp only [h1, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases ha : checkExprList prog env pc false args with
        | error _ => simp [ha] at h
        | ok aLTys =>
          rw [checkExprList_inSpec_true ha]; simp only [ha] at h
          cases hf : prog.findFun? fnName with
          | none => simp [hf] at h
          | some fDecl =>
            simp only [hf] at h ⊢
            cases hsp : fDecl.kind.isSpec
            · simp only [hsp, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h
            · simp [hsp] at h
    | join label params rhs body =>
      unfold checkExpr at h ⊢
      cases h1 : (!distinctIdents (params.map Prod.fst) || !params.all (fun x => validLTy prog x.2)) <;>
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
      · cases hc0 : inferJoinRetLTy prog (extendTyEnv env params) jenv
            ((pc.union (inferJumpPc prog label env pc body)).union
              (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))
            label rhs body with
        | none => simp only [hc0] at h; contradiction
        | some candRetLTy =>
          simp only [hc0, bind, Except.bind] at h ⊢
          cases hv : (!validLTy prog (candRetLTy.addTags
              ((pc.union (inferJumpPc prog label env pc body)).union
                (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)))) <;>
            simp only [hv, Bool.false_eq_true, ↓reduceIte] at h ⊢
          · cases hr1 : checkExpr prog (extendTyEnv env params)
                ((label, { params := params
                           joinPc := (pc.union (inferJumpPc prog label env pc body)).union
                             (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)
                           retLTy := candRetLTy.addTags ((pc.union (inferJumpPc prog label env pc body)).union
                             (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)) }) :: jenv)
                ((pc.union (inferJumpPc prog label env pc body)).union
                  (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))
                false rhs with
            | error _ => simp only [hr1] at h; contradiction
            | ok rLTy1 =>
              rw [checkExpr_inSpec_true hr1]; simp only [hr1] at h ⊢
              cases hb1 : checkExpr prog env
                  ((label, { params := params
                             joinPc := (pc.union (inferJumpPc prog label env pc body)).union
                               (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)
                             retLTy := candRetLTy.addTags ((pc.union (inferJumpPc prog label env pc body)).union
                               (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)) }) :: jenv)
                  pc false body with
              | error _ => simp only [hb1] at h; contradiction
              | ok bLTy1 =>
                rw [checkExpr_inSpec_true hb1]; simp only [hb1] at h ⊢
                cases hty : (decide (rLTy1.ty = (candRetLTy.addTags
                    ((pc.union (inferJumpPc prog label env pc body)).union
                      (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))).ty) &&
                  decide (bLTy1.ty = (candRetLTy.addTags
                    ((pc.union (inferJumpPc prog label env pc body)).union
                      (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))).ty)) <;>
                  simp only [hty, Bool.false_eq_true, ↓reduceIte] at h ⊢
                · contradiction
                · cases hsub : (((candRetLTy.addTags
                      ((pc.union (inferJumpPc prog label env pc body)).union
                        (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))).tags.union rLTy1.tags).union
                    (bLTy1.tags.union pc)).subset
                    (candRetLTy.addTags
                      ((pc.union (inferJumpPc prog label env pc body)).union
                        (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))).tags <;>
                    simp only [hsub, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  · generalize hj2 :
                      ((label, ({ params := params
                                  joinPc := (pc.union (inferJumpPc prog label env pc body)).union
                                    (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)
                                  retLTy := LTy.mk (candRetLTy.addTags
                                    ((pc.union (inferJumpPc prog label env pc body)).union
                                      (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))).ty
                                    ((((candRetLTy.addTags
                                      ((pc.union (inferJumpPc prog label env pc body)).union
                                        (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs))).tags.union rLTy1.tags).union
                                      (bLTy1.tags.union pc))) } : JoinSig)) :: jenv) = jenv2 at h ⊢
                    generalize hpc2 :
                      ((pc.union (inferJumpPc prog label env pc body)).union
                        (inferJumpPc prog label (extendTyEnv env params) (pc.union (inferJumpPc prog label env pc body)) rhs)) = joinPc2 at h ⊢
                    cases hr2 : checkExpr prog (extendTyEnv env params) jenv2 joinPc2 false rhs with
                    | error _ => simp only [hr2] at h; contradiction
                    | ok rLTy2 =>
                      rw [checkExpr_inSpec_true hr2]; simp only [hr2] at h ⊢
                      cases hb2 : checkExpr prog env jenv2 pc false body with
                      | error _ => simp only [hb2] at h; contradiction
                      | ok bLTy2 =>
                        rw [checkExpr_inSpec_true hb2]; simp only [hb2] at h ⊢; exact h
                  · exact h
          · contradiction
      · contradiction
    | jump _ args | tuple args | ctor _ _ args | prim _ args =>
      unfold checkExpr at h ⊢
      cases h1 : noFreeJumpsList args <;>
        simp only [h1, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases ha : checkExprList prog env pc false args with
        | error _ => simp [ha] at h
        | ok aLTys => rw [checkExprList_inSpec_true ha]; simpa [ha] using h
    | proj tup _ =>
      unfold checkExpr at h ⊢
      cases h1 : noFreeJumps [] tup <;>
        simp only [h1, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases ht : checkExpr prog env [] pc false tup with
        | error _ => simp [ht] at h
        | ok tLTy => rw [checkExpr_inSpec_true ht]; simpa [ht] using h
    | rel plan =>
      unfold checkExpr at h ⊢
      cases h1 : noFreeJumpsPlan plan <;>
        simp only [h1, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases hp : checkPlan prog env pc false plan with
        | error _ => simp [hp] at h
        | ok pTy => rw [checkPlan_inSpec_true hp]; simpa [hp] using h
    | host op args =>
      unfold checkExpr at h ⊢
      cases h1 : noFreeJumpsList args <;>
        simp only [h1, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · contradiction
      · cases ha : checkExprList prog env pc false args with
        | error _ => simp [ha] at h
        | ok aLTys =>
          rw [checkExprList_inSpec_true ha]; simp only [ha] at h
          exact checkHostOp_inSpec_mono h
    | stop _ d =>
      cases d with
      | none => exact h
      | some dE =>
        unfold checkExpr at h ⊢
        cases h1 : noFreeJumps [] dE <;>
          simp only [h1, Bool.not_false, Bool.not_true, ↓reduceIte, bind, Except.bind] at h ⊢
        · contradiction
        · cases hd : checkExpr prog env [] pc false dE with
          | error _ => simp [hd] at h
          | ok dLTy => rw [checkExpr_inSpec_true hd]; simpa [hd] using h
    | fail _ => unfold checkExpr at h; simp at h

theorem checkExprList_inSpec_true {prog : Program} :
    ∀ {env : TyEnv} {pc : TagSet} {inSpec : Bool} {es : List Expr} {ltys : List LTy},
      checkExprList prog env pc inSpec es = .ok ltys →
      checkExprList prog env pc true es = .ok ltys
  | _, _, true, _, _, h => h
  | _, _, false, [], _, h => h
  | env, pc, false, e :: es, ltys, h => by
    unfold checkExprList at h ⊢
    simp only [bind, Except.bind] at h ⊢
    cases he : checkExpr prog env [] pc false e with
    | error _ => simp [he] at h
    | ok hd =>
      rw [checkExpr_inSpec_true he]; simp only [he] at h
      cases hes : checkExprList prog env pc false es with
      | error _ => simp [hes] at h
      | ok tl => rw [checkExprList_inSpec_true hes]; simpa [hes] using h

theorem checkCaseArms_inSpec_true {prog : Program} :
    ∀ {env : TyEnv} {jenv : JoinEnv} {armPc : TagSet} {inSpec : Bool}
      {specs : List (Ident × List LTy)} {arms : List CaseArm} {ltys : List LTy},
      checkCaseArms prog env jenv armPc inSpec specs arms = .ok ltys →
      checkCaseArms prog env jenv armPc true specs arms = .ok ltys
  | _, _, _, true, _, _, _, h => h
  | _, _, _, false, _, [], _, h => h
  | env, jenv, armPc, false, specs, .mk cn bs body :: rest, ltys, h => by
    unfold checkCaseArms at h ⊢
    cases hsp : specs.find? (fun x => x.1 == cn) with
    | none => simp [hsp] at h
    | some pair =>
      rcases pair with ⟨_, fieldLTys⟩
      simp only [hsp] at h ⊢
      cases h1 : (!distinctIdents bs || bs.length != fieldLTys.length) <;>
        simp only [h1, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h ⊢
      · cases hb : checkExpr prog (extendTyEnv env (List.zip bs (fieldLTys.map (·.addTags armPc)))) jenv armPc false body with
        | error _ => simp [hb] at h
        | ok hd =>
          rw [checkExpr_inSpec_true hb]; simp only [hb] at h
          cases hr : checkCaseArms prog env jenv armPc false specs rest with
          | error _ => simp [hr] at h
          | ok tl => rw [checkCaseArms_inSpec_true hr]; simpa [hr] using h
      · contradiction

theorem checkPlan_inSpec_true {prog : Program} :
    ∀ {env : TyEnv} {pc : TagSet} {inSpec : Bool} {p : Plan} {pTy : PlanTy},
      checkPlan prog env pc inSpec p = .ok pTy →
      checkPlan prog env pc true p = .ok pTy
  | _, _, true, _, _, h => h
  | env, pc, false, p, pTy, h => by
    cases p with
    | sourceExpr e =>
      unfold checkPlan at h ⊢; simp only [bind, Except.bind] at h ⊢
      cases he : checkExpr prog env [] pc false e with
      | error _ => simp [he] at h
      | ok lty => rw [checkExpr_inSpec_true he]; simpa [he] using h
    | sourceDB cap _ _ =>
      unfold checkPlan at h ⊢; simp only [bind, Except.bind] at h ⊢
      cases hc : checkExpr prog env [] pc false cap with
      | error _ => simp [hc] at h
      | ok lty => rw [checkExpr_inSpec_true hc]; simpa [hc] using h
    | join _ l r _ _ | union l r =>
      unfold checkPlan at h ⊢; simp only [bind, Except.bind] at h ⊢
      cases hl : checkPlan prog env pc false l with
      | error _ => simp [hl] at h
      | ok lP =>
        rw [checkPlan_inSpec_true hl]; simp only [hl] at h
        cases hr : checkPlan prog env pc false r with
        | error _ => simp [hr] at h
        | ok rP => rw [checkPlan_inSpec_true hr]; simpa [hr] using h
    | pseudonymize inp _ sec =>
      unfold checkPlan at h ⊢; simp only [bind, Except.bind] at h ⊢
      cases hi : checkPlan prog env pc false inp with
      | error _ => simp [hi] at h
      | ok inP =>
        rw [checkPlan_inSpec_true hi]; simp only [hi] at h
        cases hs : checkExpr prog env [] pc false sec with
        | error _ => simp [hs] at h
        | ok sLTy => rw [checkExpr_inSpec_true hs]; simpa [hs] using h
    | select inp _ | drop inp _ | rename inp _ | derive inp _ | filter inp _
    | distinct inp _ | sort inp _ | limit inp _ | groupBy inp _
    | summarize inp _ _ | suppressSmallGroups inp _ _ _ | window inp _
    | fillGaps inp _ _ _ _ | pivotWider inp _ _ _ _ | crosstab inp _ _ _ _
    | redact inp _ _ =>
      unfold checkPlan at h ⊢; simp only [bind, Except.bind] at h ⊢
      cases hi : checkPlan prog env pc false inp with
      | error _ => simp [hi] at h
      | ok inP => rw [checkPlan_inSpec_true hi]; simpa [hi] using h
end

/-! ## Literal, Constant, Primitive & Host Operation Soundness -/

theorem checkLiteral_sound {prog : Program} {pc : TagSet} {lit : Literal} {lty : LTy}
    (h : checkLiteral prog pc lit = .ok lty) :
    ValWf prog (evalLiteral lit) lty.ty := by
  cases lit with
  | unit => injection h with h'; subst h'; exact .unit
  | bool b => injection h with h'; subst h'; exact .bool b
  | int n =>
    simp only [checkLiteral] at h
    by_cases hr : inInt64Range n = true
    · simp only [hr, ↓reduceIte, Except.ok.injEq] at h; subst h; exact .int hr
    · simp [hr] at h
  | decimal d =>
    simp only [checkLiteral] at h
    by_cases hr : inDecimalRange d = true
    · simp only [hr, ↓reduceIte, Except.ok.injEq] at h; subst h; exact .decimal hr
    · simp [hr] at h
  | float f => injection h with h'; subst h'; exact .float f
  | text s => injection h with h'; subst h'; exact .text s
  | bytes bs => injection h with h'; subst h'; exact .bytes bs
  | date d => injection h with h'; subst h'; exact .date d
  | timestamp ts => injection h with h'; subst h'; exact .timestamp ts
  | duration dur => injection h with h'; subst h'; exact .duration dur
  | noneLit inner =>
    simp only [checkLiteral] at h
    split at h <;> simp_all
    subst h; exact .optNone inner

theorem checkConst_sound {prog : Program} {name : Ident} {cDecl : ConstDecl}
    (hprog : checkProgram prog = .ok ())
    (hfind : prog.findConst? name = some cDecl) :
    ValWf prog (evalLiteral cDecl.value) cDecl.lty.ty := by
  have hmem := List.mem_of_find?_eq_some hfind
  simp only [checkProgram, bind, Except.bind] at hprog
  split at hprog <;> try simp at hprog
  split at hprog <;> try simp at hprog
  cases hp : checkPolicyWf prog <;> simp [hp] at hprog
  cases hd : checkDataDecls prog <;> simp [hd] at hprog
  cases hs : checkSchemaDecls prog <;> simp [hs] at hprog
  cases hc : checkConstDecls prog <;> simp [hc] at hprog
  unfold checkConstDecls at hc
  split at hc <;> try simp at hc
  have go_ok : ∀ (cs : List ConstDecl), checkConstDecls.go prog cs = .ok () →
      ∀ c ∈ cs, ValWf prog (evalLiteral c.value) c.lty.ty := by
    intro cs hgo c hcm
    induction cs with
    | nil => nomatch hcm
    | cons hdC tlC ih =>
      simp only [checkConstDecls.go, bind, Except.bind] at hgo
      split at hgo <;> try simp at hgo
      cases hv : checkLiteral prog TagSet.empty hdC.value with
      | error _ => simp [hv] at hgo
      | ok vLTy =>
        simp only [hv] at hgo
        split at hgo <;> try simp at hgo
        case isTrue hsub =>
          rcases List.mem_cons.mp hcm with rfl | hrest
          · simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
            rw [← hsub.1]; exact checkLiteral_sound hv
          · exact ih hgo hrest
  exact go_ok prog.consts hc cDecl hmem

theorem clampInt64Nat_inRange (n : Nat) : inInt64Range (clampInt64Nat n) = true := by
  unfold clampInt64Nat
  by_cases h : inInt64Range (Int.ofNat n) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; decide

theorem checkedInt_sound (n : Int) : PrimResultWf prog .int (checkedInt n) := by
  unfold checkedInt
  by_cases h : inInt64Range n = true
  · simp [h]; exact .ok (.int h)
  · simp [h]; exact .stopped _

theorem checkedDecimal_sound (d : Int) : PrimResultWf prog .decimal (checkedDecimal d) := by
  unfold checkedDecimal
  by_cases h : inDecimalRange d = true
  · simp [h]; exact .ok (.decimal h)
  · simp [h]; exact .stopped _

theorem lookupColIdx?_of_find? {cols : List ColSpec} {name : Ident} {c : ColSpec}
    (h : cols.find? (fun x => x.name == name) = some c) :
    ∃ idx, lookupColIdx? cols name = some (idx, c) ∧ cols[idx]? = some c := by
  unfold lookupColIdx?
  have aux : ∀ (k : Nat) (cs : List ColSpec),
      cs.find? (fun x => x.name == name) = some c →
      ∃ idx, lookupColIdx?.go name k cs = some (k + idx, c) ∧ cs[idx]? = some c := by
    intro k cs hfind
    induction cs generalizing k with
    | nil => simp at hfind
    | cons hd tl ih =>
      simp only [List.find?] at hfind
      unfold lookupColIdx?.go
      by_cases hn : (hd.name == name) = true
      · simp only [hn, Option.some.injEq] at hfind
        subst hfind; simp only [hn, ↓reduceIte]
        exact ⟨0, rfl, rfl⟩
      · simp only [hn] at hfind
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
        rcases ih (k + 1) hfind with ⟨subIdx, hgo, hget⟩
        refine ⟨subIdx + 1, ?_, hget⟩
        have hadd : k + 1 + subIdx = k + (subIdx + 1) := by omega
        rw [← hadd]; exact hgo
  rcases aux 0 cols h with ⟨idx, hgo, hget⟩
  simp only [Nat.zero_add] at hgo
  exact ⟨idx, hgo, hget⟩

theorem projectColCells_sound {prog : Program} {tv : TableVal} {tt : TableTy} {colName : Ident} {c : ColSpec}
    (hcols : tv.cols = tt.cols)
    (hrows : RowsWf prog tv.rows tt.cols tt.summarized tt.distinctBy.isSome)
    (hfind : tt.findCol? colName = some c) :
    ∃ vals, projectColCells tv colName = some (c, vals) ∧ ∀ v ∈ vals, ValWf prog v c.ty.toTy := by
  unfold TableTy.findCol? at hfind
  rw [← hcols] at hfind
  rcases lookupColIdx?_of_find? hfind with ⟨idx, hlook, hcolGet⟩
  unfold projectColCells
  simp only [hlook, bind, Option.bind]
  have hgather : ∀ (rs : List TableRow),
      (∀ r ∈ rs, CellsWf prog r.cells tv.cols) →
      ∃ vals, projectColCells.gather idx rs = some vals ∧ ∀ v ∈ vals, ValWf prog v c.ty.toTy := by
    intro rs hrs
    induction rs with
    | nil => exact ⟨[], rfl, fun _ hm => nomatch hm⟩
    | cons r rest ih =>
      rcases (hrs r (.head _)).getElem?_wf hcolGet with ⟨cell, hcellGet, hcellWf⟩
      rcases ih (fun r' hr' => hrs r' (.tail _ hr')) with ⟨tlVals, htl, htlWf⟩
      refine ⟨cell :: tlVals, by simp [projectColCells.gather, hcellGet, htl], ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hrest
      · exact hcellWf
      · exact htlWf v hrest
  have hallRows : ∀ r ∈ tv.rows, CellsWf prog r.cells tv.cols := by
    rw [hcols]; exact hrows.to_forall
  rcases hgather tv.rows hallRows with ⟨vals, hg, hv⟩
  simp only [hg]
  exact ⟨vals, rfl, hv⟩

theorem buildProfileCols_some {prog : Program} {tv : TableVal}
    (hallRows : ∀ r ∈ tv.rows, CellsWf prog r.cells tv.cols) :
    ∃ summaries, buildProfileCols tv 0 tv.cols = some summaries := by
  have aux : ∀ (k : Nat) (rem : List ColSpec),
      (∀ i c, rem[i]? = some c → tv.cols[k + i]? = some c) →
      ∃ s, buildProfileCols tv k rem = some s := by
    intro k rem hidx
    induction rem generalizing k with
    | nil => exact ⟨[], rfl⟩
    | cons c cs ih =>
      have hc0 : tv.cols[k]? = some c := by simpa using hidx 0 c rfl
      have hbc : ∃ summary, buildProfileCol tv k c = some summary := by
        unfold buildProfileCol
        have hg : ∀ (rs : List TableRow), (∀ r ∈ rs, CellsWf prog r.cells tv.cols) →
            ∃ cells, buildProfileCol.gather k rs = some cells := by
          intro rs hrs
          induction rs with
          | nil => exact ⟨[], rfl⟩
          | cons r rest ihr =>
            rcases (hrs r (.head _)).getElem?_wf hc0 with ⟨cell, hget, _⟩
            rcases ihr (fun r' hr' => hrs r' (.tail _ hr')) with ⟨tl, htl⟩
            exact ⟨cell :: tl, by simp [buildProfileCol.gather, hget, htl]⟩
        rcases hg tv.rows hallRows with ⟨cells, hcells⟩
        simp [hcells]
      rcases hbc with ⟨hd, hhd⟩
      rcases ih (k + 1) (fun i c' hi => by
        have := hidx (i + 1) c' hi
        have heq : k + (i + 1) = k + 1 + i := by omega
        rw [← heq]; exact this) with ⟨tl, htl⟩
      exact ⟨hd :: tl, by simp [buildProfileCols, hhd, htl]⟩
  exact aux 0 tv.cols (fun i c h => by simpa using h)

theorem valListWf_zero {prog : Program} {vs : List Val}
    (h : ValListWf prog vs []) : vs = [] := by
  cases h; rfl

theorem valListWf_one {prog : Program} {vs : List Val} {l1 : LTy}
    (h : ValListWf prog vs [l1]) :
    ∃ v1, vs = [v1] ∧ ValWf prog v1 l1.ty := by
  cases h with
  | cons hv1 hnil =>
    cases hnil
    exact ⟨_, rfl, hv1⟩

theorem valListWf_two {prog : Program} {vs : List Val} {l1 l2 : LTy}
    (h : ValListWf prog vs [l1, l2]) :
    ∃ v1 v2, vs = [v1, v2] ∧ ValWf prog v1 l1.ty ∧ ValWf prog v2 l2.ty := by
  cases h with
  | cons hv1 h2 =>
    cases h2 with
    | cons hv2 hnil =>
      cases hnil
      exact ⟨_, _, rfl, hv1, hv2⟩

theorem valListWf_three {prog : Program} {vs : List Val} {l1 l2 l3 : LTy}
    (h : ValListWf prog vs [l1, l2, l3]) :
    ∃ v1 v2 v3, vs = [v1, v2, v3] ∧ ValWf prog v1 l1.ty ∧ ValWf prog v2 l2.ty ∧ ValWf prog v3 l3.ty := by
  cases h with
  | cons hv1 h2 =>
    cases h2 with
    | cons hv2 h3 =>
      cases h3 with
      | cons hv3 hnil =>
        cases hnil
        exact ⟨_, _, _, rfl, hv1, hv2, hv3⟩

theorem valAllWf_of_ltySubtype {prog : Program} {elemLTy : LTy} :
    ∀ {vs : List Val} {ls : List LTy},
      ValListWf prog vs ls →
      (∀ a ∈ ls, ltySubtype a elemLTy = true) →
      ∀ v ∈ vs, ValWf prog v elemLTy.ty
  | [], [], .nil, _, _, hv => nomatch hv
  | _ :: _, _ :: _, .cons hhd htl, hsub, _, hv => by
    rcases List.mem_cons.mp hv with rfl | hrest
    · have hs := hsub _ (.head _)
      simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hs
      rw [← hs.1]; exact hhd
    · exact valAllWf_of_ltySubtype htl (fun a ha => hsub a (.tail _ ha)) _ hrest

theorem flattenValLists_wf {prog : Program} {elemLTy : LTy} :
    ∀ (ns : List Val),
      ValAllWf prog ns (.list elemLTy) →
      ∃ flat, flattenValLists ns = some flat ∧ ∀ u ∈ flat, ValWf prog u elemLTy.ty
  | [], .nil _ => ⟨[], rfl, fun _ hm => nomatch hm⟩
  | _ :: rest, .cons (.list (vs := elems) hxs) htl => by
    rcases flattenValLists_wf rest htl with ⟨tl, htlEq, htlWf⟩
    refine ⟨elems ++ tl, by simp [flattenValLists, htlEq], ?_⟩
    intro u hu; rw [List.mem_append] at hu
    rcases hu with hl | hr
    · exact hxs.to_forall u hl
    · exact htlWf u hr

theorem buildPairs_wf {prog : Program} {kLTy vLTy : LTy} :
    ∀ (ls : List LTy) (vs : List Val),
      ValListWf prog vs ls →
      checkPrimOp.checkPairs kLTy vLTy ls = true →
      ∃ ps, buildPairs vs = some ps ∧ ValPairsWf prog ps kLTy.ty vLTy.ty
  | [], [], .nil, _ => ⟨[], rfl, .nil _ _⟩
  | [_], [_], .cons _ .nil, hcp => by simp [checkPrimOp.checkPairs] at hcp
  | _ :: _ :: restL, _ :: _ :: restV, .cons hk (.cons hv htl), hcp => by
    simp only [checkPrimOp.checkPairs, Bool.and_eq_true, ltySubtype, decide_eq_true_eq] at hcp
    rcases buildPairs_wf restL restV htl hcp.2 with ⟨tlPs, hbp, htlWf⟩
    exact ⟨_ :: tlPs, by simp [buildPairs, hbp], .cons (hcp.1.1.1 ▸ hk) (hcp.1.2.1 ▸ hv) htlWf⟩

theorem valPairsWf_snd {prog : Program} {kt vt : Ty} :
    ∀ {ps : List (Val × Val)}, ValPairsWf prog ps kt vt → ∀ p ∈ ps, ValWf prog p.2 vt
  | [], .nil _ _, _, hp => nomatch hp
  | _ :: _, .cons _ hv htl, _, hp => by
    rcases List.mem_cons.mp hp with rfl | hr
    · exact hv
    · exact valPairsWf_snd htl _ hr

theorem mapGet_wf {prog : Program} {kLTy vLTy : LTy} (kvs : List (Val × Val)) (qVal : Val)
    (hkvs : ValPairsWf prog kvs kLTy.ty vLTy.ty) :
    PrimResultWf prog (.option vLTy.ty)
      (match kvs.find? (fun kv => valEq kv.1 qVal) with
       | some (_, v) => .ok (.optSome v)
       | none => .ok .optNone) := by
  cases hfind : kvs.find? (fun kv => valEq kv.1 qVal) with
  | none => exact .ok (.optNone _)
  | some kv =>
    rcases kv with ⟨k, v⟩
    exact .ok (.optSome (valPairsWf_snd hkvs (k, v) (List.mem_of_find?_eq_some hfind)))

theorem map_ty_with_aggKind (cols : List ColSpec) (ak : AggKind) :
    (cols.map (fun c => { c with aggKind := ak })).map ColSpec.ty = cols.map ColSpec.ty := by
  induction cols <;> simp [*]

theorem gatherConcatRows_wf {prog : Program} {schema : TableTy} :
    ∀ (vs : List Val),
      ValAllWf prog vs (.table schema) →
      ∃ rows, gatherConcatRows vs = some rows ∧
        ∀ r ∈ rows, CellsWf prog r.cells (schema.cols.map (fun c => { c with aggKind := .raw }))
  | [], .nil _ => ⟨[], rfl, fun _ hm => nomatch hm⟩
  | _ :: rest, .cons (.table (tv := tv) _ _ hrows) htl => by
    rcases gatherConcatRows_wf rest htl with ⟨tlR, htlEq, htlWf⟩
    refine ⟨tv.rows.map (fun r => { r with groupMeta := none }) ++ tlR, by simp [gatherConcatRows, htlEq], ?_⟩
    intro r hr; rw [List.mem_append] at hr
    rcases hr with hl | hr'
    · rw [List.mem_map] at hl; rcases hl with ⟨origR, horigMem, rfl⟩
      exact (hrows.to_forall origR horigMem).congr_ty (map_ty_with_aggKind schema.cols .raw).symm
    · exact htlWf r hr'

theorem gatherChartSeries_some {prog : Program} {tv : TableVal} {tt : TableTy}
    (hcols : tv.cols = tt.cols)
    (hrows : RowsWf prog tv.rows tt.cols tt.summarized tt.distinctBy.isSome) :
    ∀ (cns : List Ident), (∀ cn ∈ cns, ∃ c, TableTy.findCol? tt cn = some c) →
      ∃ s, gatherChartSeries tv cns = some s
  | [], _ => ⟨[], rfl⟩
  | cn :: rest, hcns => by
    rcases hcns cn (.head _) with ⟨cSpec, hfind⟩
    rcases projectColCells_sound hcols hrows hfind with ⟨vals, hp, _⟩
    rcases gatherChartSeries_some hcols hrows rest (fun x hx => hcns x (.tail _ hx)) with ⟨tl, htl⟩
    exact ⟨vals :: tl, by simp [gatherChartSeries, hp, htl]⟩

theorem evalPrimOp_sound {prog : Program} {pc : TagSet} {op : PrimOp}
    {argLTys : List LTy} {argVals : List Val} {retLTy : LTy}
    (hchk : checkPrimOp prog pc op argLTys = .ok retLTy)
    (hargs : ValListWf prog argVals argLTys) :
    PrimResultWf prog retLTy.ty (evalPrimOp op argVals) := by
  unfold checkPrimOp at hchk
  split at hchk
  -- 1. someVal
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases valListWf_one hargs with ⟨_, rfl, hv⟩
      rw [← hc.2]; exact .ok (.optSome hv)
  -- 2. isSome
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv⟩; cases hv <;> exact .ok (.bool _)
  -- 3. isNone
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv⟩; cases hv <;> exact .ok (.bool _)
  -- 4. unwrapOr
  · split at hchk <;> try contradiction
    case isTrue heq =>
      injection hchk with hret; subst hret
      have hty := of_decide_eq_true heq; subst hty
      rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
      cases hv1 with | optNone => exact .ok hv2 | optSome hu => exact .ok hu
  -- 5. unwrapBang
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv⟩; cases hv with
    | optNone => exact .stopped _
    | optSome hu => exact .ok hu
  -- 6. okVal
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, ha⟩; exact .ok (.resOk ha)
  -- 7. errVal
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, ha⟩; exact .ok (.resErr ha)
  -- 8..12. addInt, subInt, mulInt, divInt, modInt
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact checkedInt_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact checkedInt_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact checkedInt_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; simp only [evalPrimOp]; split; exact .stopped _; exact checkedInt_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; simp only [evalPrimOp]; split; exact .stopped _; exact checkedInt_sound _
  -- 13. negInt
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact checkedInt_sound _
  -- 14..17. addDec, subDec, mulDec, divDec
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact checkedDecimal_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact checkedDecimal_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact checkedDecimal_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; simp only [evalPrimOp]; split; exact .stopped _; exact checkedDecimal_sound _
  -- 18..20. negDec, intToDec, boolToDec
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact checkedDecimal_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact checkedDecimal_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1 with | bool b =>
    simp only [evalPrimOp]; apply PrimResultWf.ok; apply ValWf.decimal; cases b <;> decide
  -- 21..26. eq, ne, lt, le, gt, ge
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, _, _⟩; exact .ok (.bool _)
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, _, _⟩; exact .ok (.bool _)
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, _, _⟩; exact .ok (.bool _)
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, _, _⟩; exact .ok (.bool _)
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, _, _⟩; exact .ok (.bool _)
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, _, _⟩; exact .ok (.bool _)
  -- 27..29. notBool, andBool, orBool
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.bool _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.bool _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.bool _)
  -- 30..36. concatText, containsText, trimText, lowerAsciiText, emptyText, intToText, decToText
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.text _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.bool _)
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.text _)
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.text _)
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.bool _)
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.text _)
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.text _)
  -- 37..39. dateTruncMonth, addDuration, diffTimestamp
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.date _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.timestamp _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.duration _)
  -- 40. listLit
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, List.all_eq_true] at hc
      exact .ok (.list (ValAllWf.of_forall (valAllWf_of_ltySubtype hargs hc.2)))
  -- 41..42. listLen, listEmpty
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact checkedInt_sound _
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.bool _)
  -- 43. listAppend
  · split at hchk <;> try contradiction
    case isTrue hsub =>
      injection hchk with hret; subst hret
      simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
      rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
      cases hv1 with | list hvs =>
      apply PrimResultWf.ok; apply ValWf.list; apply ValAllWf.of_forall
      intro u hu; rw [List.mem_append] at hu
      rcases hu with hl | hr
      · exact hvs.to_forall u hl
      · simp at hr; subst hr; rw [← hsub.1]; exact hv2
  -- 44. listConcat
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
    cases hv1 with | list hnested =>
    rcases flattenValLists_wf _ hnested with ⟨flat, hfEq, hfWf⟩
    simp only [evalPrimOp, hfEq]
    apply PrimResultWf.ok; apply ValWf.list
    have htyEq : ∀ (l : LTy) (ts : TagSet), (l.addTags ts).ty = l.ty := by intro ⟨_, _⟩ _; rfl
    rw [htyEq]
    exact ValAllWf.of_forall hfWf
  -- 45. mapLit
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true] at hc
      rcases buildPairs_wf _ argVals hargs hc.2 with ⟨ps, hbp, hpsWf⟩
      simp only [evalPrimOp, hbp]; exact .ok (.map hpsWf)
  -- 46. mapGet
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, qVal, rfl, hv1, _⟩
    cases hv1 with | map hkvs =>
    dsimp only [evalPrimOp, LTy.ty]
    exact mapGet_wf _ qVal hkvs
  -- 47. tableCount
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact checkedInt_sound _
  -- 48. tableConcat
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, hvalSchema⟩
      rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
      cases hv1 with | list htbls =>
      rcases gatherConcatRows_wf _ htbls with ⟨allRows, hgEq, hgWf⟩
      simp only [evalPrimOp, hgEq]
      rcases tableSchemaWf_cols_props (validTableTy_imp_schemaWf hvalSchema) with ⟨huniq, hcProps⟩
      exact .ok (.table rfl (resetRawTableSchemaWf huniq hcProps _ _) (RowsWf.of_forall_raw hgWf))
  -- 49. tableProfile
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
    cases hv1 with | @table tv _ hcols _ hrows =>
    have hall : ∀ r ∈ tv.rows, CellsWf prog r.cells tv.cols := by rw [hcols]; exact hrows.to_forall
    rcases buildProfileCols_some hall with ⟨summaries, hsEq⟩
    simp only [evalPrimOp, hsEq]; exact .ok (.profile _ _)
  -- 50..52. statsCorr, statsLinReg, statsTTest
  · rename_i colX colY tt tTs
    cases hx : tt.findCol? colX <;> cases hy : tt.findCol? colY <;> simp [hx, hy] at hchk
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
    cases hv1 with | table hcols _ _ =>
    unfold TableTy.findCol? at hx hy
    rcases lookupColIdx?_of_find? (hcols.symm ▸ hx) with ⟨ix, hix, _⟩
    rcases lookupColIdx?_of_find? (hcols.symm ▸ hy) with ⟨iy, hiy, _⟩
    simp only [evalPrimOp, extractPairVals, hix, hiy, bind, Option.bind]
    cases computeStatsCorr _
    · exact .ok (.optNone _)
    · exact .ok (.optSome (.float _))
  · rename_i colX colY tt tTs
    cases hx : tt.findCol? colX <;> cases hy : tt.findCol? colY <;> simp [hx, hy] at hchk
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
    cases hv1 with | table hcols _ _ =>
    unfold TableTy.findCol? at hx hy
    rcases lookupColIdx?_of_find? (hcols.symm ▸ hx) with ⟨ix, hix, _⟩
    rcases lookupColIdx?_of_find? (hcols.symm ▸ hy) with ⟨iy, hiy, _⟩
    simp only [evalPrimOp, extractPairVals, hix, hiy, bind, Option.bind]
    cases computeStatsLinReg _
    · exact .stopped _
    · exact .ok (.linearModel _ _ _)
  · rename_i colX colY tt tTs
    cases hx : tt.findCol? colX <;> cases hy : tt.findCol? colY <;> simp [hx, hy] at hchk
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
    cases hv1 with | table hcols _ _ =>
    unfold TableTy.findCol? at hx hy
    rcases lookupColIdx?_of_find? (hcols.symm ▸ hx) with ⟨ix, hix, _⟩
    rcases lookupColIdx?_of_find? (hcols.symm ▸ hy) with ⟨iy, hiy, _⟩
    simp only [evalPrimOp, hix, hiy]
    exact .stopped _
  -- 53. chartMake
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, List.all_eq_true, Option.isSome_iff_exists] at hc
      rcases valListWf_one hargs with ⟨_, rfl, hv1⟩
      cases hv1 with | table hcols _ hrows =>
      rcases gatherChartSeries_some hcols hrows _ hc.2 with ⟨series, hsEq⟩
      simp only [evalPrimOp, hsEq]; exact .ok (.chart _ _)
  -- 54..57. reportNew, reportAddSummary, reportAddChart, reportAddTable
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1; exact .ok (.report _ _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.report _ _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.report _ _)
  · injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩; cases hv1; cases hv2; exact .ok (.report _ _)
  -- 58. catch-all error
  · contradiction

/-! ## Host Capability Soundness -/

theorem checkSchema_valid {prog : Program} {sName : Ident} {sDecl : SchemaDecl}
    (hprog : checkProgram prog = .ok ())
    (hfind : prog.findSchema? sName = some sDecl) :
    TableSchemaWf prog sDecl.schema = true ∧ sDecl.schema.summarized = false ∧ sDecl.schema.distinctBy = none := by
  have hmem := List.mem_of_find?_eq_some hfind
  simp only [checkProgram, bind, Except.bind] at hprog
  split at hprog <;> try simp at hprog
  split at hprog <;> try simp at hprog
  cases hp : checkPolicyWf prog <;> simp [hp] at hprog
  cases hd : checkDataDecls prog <;> simp [hd] at hprog
  cases hs : checkSchemaDecls prog <;> simp [hs] at hprog
  unfold checkSchemaDecls at hs
  split at hs
  · contradiction
  · split at hs
    · rename_i hall
      have h1 := (List.all_eq_true.mp hall) sDecl hmem
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h1
      exact ⟨validTableTy_imp_schemaWf h1.1.1.1.1, h1.1.1.1.2, h1.1.2⟩
    · contradiction

theorem quarantineBadRow_schemaWf {prog : Program} (s : TableTy) :
    TableSchemaWf prog (quarantineBadRowTableTy s) = true := by
  simp [quarantineBadRowTableTy, TableSchemaWf, distinctIdents, validScalarTy]

theorem evalHostOp_sound {prog : Program} {pc : TagSet} {inSpec : Bool}
    {op : HostOp} {argLTys : List LTy} {argVals : List Val} {retLTy : LTy} {w : World}
    (hprog : checkProgram prog = .ok ())
    (hchk : checkHostOp prog pc inSpec op argLTys = .ok retLTy)
    (hargs : ValListWf prog argVals argLTys)
    (hw : WorldWf prog w) :
    OutcomeWf prog [] retLTy.ty (evalHostOp prog op argVals w) := by
  unfold checkHostOp at hchk
  split at hchk
  -- 1. argsGet
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1
    apply OutcomeWf.ok _ hw
    apply ValWf.list; apply ValAllWf.of_forall
    intro v hv; rw [List.mem_map] at hv; rcases hv with ⟨s, _, rfl⟩; exact .text s
  -- 2. clockNow
  · injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1
    exact .ok (.timestamp _) hw
  -- 3..4. consolePrint, consoleError
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1 with | capConsole h _ => cases hv2 with | text _ =>
    cases h with
    | real =>
      dsimp only [evalHostOp]
      split; exact .stopped _ hw; exact .ok .unit ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
    | fake id =>
      dsimp only [evalHostOp, checkRuntimeExportGate]
      cases w.fakeConsoles[id]? <;> exact .ok .unit ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1 with | capConsole h _ => cases hv2 with | text _ =>
    cases h with
    | real =>
      dsimp only [evalHostOp]
      split; exact .stopped _ hw; exact .ok .unit ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
    | fake id =>
      dsimp only [evalHostOp, checkRuntimeExportGate]
      cases w.fakeConsoles[id]? <;> exact .ok .unit ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 5. consolePrintTable
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1 with | capConsole h _ => cases hv2 with | table _ _ _ =>
    cases h with
    | real =>
      dsimp only [evalHostOp]
      split; exact .stopped _ hw; exact .ok .unit ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
    | fake id =>
      dsimp only [evalHostOp, checkRuntimeExportGate]
      cases w.fakeConsoles[id]? <;> exact .ok .unit ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 6. readCsv
  · rename_i schemaName capTs pathTs
    cases hfs : prog.findSchema? schemaName with
    | none => simp [hfs] at hchk
    | some sDecl =>
      simp only [hfs, Except.ok.injEq] at hchk; subst hchk
      rcases checkSchema_valid hprog hfs with ⟨hsWf, hsumF, hdkN⟩
      rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
      cases hv1 with | capReadFiles _ => cases hv2 with | text path =>
      simp only [evalHostOp, hfs]
      have hbadWf : TableSchemaWf prog (quarantineBadRowTableTy sDecl.schema) = true :=
        quarantineBadRow_schemaWf sDecl.schema
      cases hfix : w.realCsvFixtures.find? (fun x => x.1 == path) with
      | none =>
        apply OutcomeWf.ok _ hw
        apply ValWf.resOk; apply ValWf.tuple
        refine .cons ?_ (.cons ?_ .nil)
        · apply ValWf.table rfl (by simpa using hsWf)
          simp [hsumF, hdkN]; exact .nil _ _ _
        · apply ValWf.table rfl (by simpa using hbadWf)
          exact .nil _ _ _
      | some triple =>
        rcases triple with ⟨p, gTV, bTV⟩
        have hmem := List.mem_of_find?_eq_some hfix
        rcases hw.csvWf p gTV bTV hmem with ⟨hgR, hbR⟩
        simp only
        split
        · case isTrue htyEq =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at htyEq
          apply OutcomeWf.ok _ hw
          apply ValWf.resOk; apply ValWf.tuple
          refine .cons ?_ (.cons ?_ .nil)
          · apply ValWf.table rfl (by simpa using hsWf)
            simp only [hsumF, hdkN, Option.isSome_none]
            exact RowsWf.of_forall_raw (fun r hr => (hgR.to_forall r hr).congr_ty htyEq.1)
          · apply ValWf.table rfl (by simpa using hbadWf)
            exact RowsWf.of_forall_raw (fun r hr => (hbR.to_forall r hr).congr_ty htyEq.2)
        · exact .ok (.resErr (.text _)) hw
  -- 7. writeFile
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_three hargs with ⟨_, _, _, rfl, hv1, hv2, hv3⟩
    cases hv1 with | capWriteFiles h _ _ => cases hv2 with | text _ => cases hv3 with | text _ =>
    dsimp only [evalHostOp]
    split
    · exact .stopped _ hw
    · split
      · exact .ok (.resErr (.text _)) hw
      · cases h with
        | real => exact .ok (.resOk .unit) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
        | fake id =>
          dsimp only
          cases w.fakeFiles[id]? <;> exact .ok (.resOk .unit) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 8. writeReportHtml
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_three hargs with ⟨_, _, _, rfl, hv1, hv2, hv3⟩
    cases hv1 with | capWriteFiles h _ _ => cases hv2 with | text _ => cases hv3 with | report _ _ =>
    dsimp only [evalHostOp]
    split
    · exact .stopped _ hw
    · split
      · exact .ok (.resErr (.text _)) hw
      · cases h with
        | real => exact .ok (.resOk .unit) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
        | fake id =>
          dsimp only
          cases w.fakeFiles[id]? <;> exact .ok (.resOk .unit) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 9. writeTable
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1 with | capWriteTable h _ _ => cases hv2 with | @table srcTV _ _ _ _ =>
    simp only [evalHostOp]
    unfold checkedInt
    cases hrng : inInt64Range (Int.ofNat (srcTV.rows.map TableRow.cells).length)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact .stopped _ hw
    · simp only [↓reduceIte]
      cases h <;> exact .ok (.resOk (.int hrng)) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 10. declassifyApprove
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    split at hchk
    · contradiction
    · injection hchk with hret; subst hret
      rcases valListWf_three hargs with ⟨_, _, _, rfl, hv1, hv2, hv3⟩
      cases hv1; cases hv3
      exact .ok hv2 hw
  -- 11. rawSqlQuery
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1; cases hv2; exact .stopped _ hw
  -- 12. httpsGetJson
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1 with | capHttpsAllow h _ _ => cases hv2 with | text url =>
    cases h with
    | real => exact .stopped _ hw
    | fake id =>
      dsimp only [evalHostOp, checkRuntimeExportGate]
      cases hwfh : w.fakeHttps[id]? with
      | none => exact .ok (.resErr (.text _)) hw
      | some fh =>
        dsimp only
        cases hfind : fh.responses.find? (fun x => x.1 == url) with
        | none => exact .ok (.resErr (.text _)) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
        | some pair =>
          rcases pair with ⟨_, body⟩
          exact .ok (.resOk (.text body)) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 13. readParquet
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_two hargs with ⟨_, _, rfl, hv1, hv2⟩
    cases hv1 with | capReadFiles h => cases hv2 with | text _ =>
    cases h with
    | real => exact .stopped _ hw
    | fake _ => exact .ok (.resErr (.text _)) hw
  -- 14..15. writeParquet, writeXlsx
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_three hargs with ⟨_, _, _, rfl, hv1, hv2, hv3⟩
    cases hv1 with | capWriteFiles h _ _ => cases hv2 with | text _ => cases hv3 with | table _ _ _ =>
    dsimp only [evalHostOp]
    split
    · exact .stopped _ hw
    · split
      · exact .ok (.resErr (.text _)) hw
      · cases h with
        | real => exact .stopped _ hw
        | fake id =>
          dsimp only
          cases w.fakeFiles[id]? <;> exact .ok (.resOk .unit) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_three hargs with ⟨_, _, _, rfl, hv1, hv2, hv3⟩
    cases hv1 with | capWriteFiles h _ _ => cases hv2 with | text _ => cases hv3 with | table _ _ _ =>
    dsimp only [evalHostOp]
    split
    · exact .stopped _ hw
    · split
      · exact .ok (.resErr (.text _)) hw
      · cases h with
        | real => exact .stopped _ hw
        | fake id =>
          dsimp only
          cases w.fakeFiles[id]? <;> exact .ok (.resOk .unit) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 16..20. fakeConsole, fakeFiles, fakeDB, fakeHttps, fakeSecret
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    have hz := valListWf_zero hargs; subst hz
    exact .ok (.capConsole _ _) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    have hz := valListWf_zero hargs; subst hz
    exact .ok (.capWriteFiles _ _ _) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    have hz := valListWf_zero hargs; subst hz
    refine .ok (.capReadDB _ _) ⟨hw.csvWf, hw.realDbWf, ?_⟩
    intro fdb hfdb st hst
    rw [List.mem_append] at hfdb
    rcases hfdb with hl | hr
    · exact hw.fakeDbWf fdb hl st hst
    · simp at hr; subst hr; nomatch hst
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    have hz := valListWf_zero hargs; subst hz
    exact .ok (.capHttpsAllow _ _ _) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListWf_one hargs with ⟨_, rfl, hv1⟩; cases hv1
    exact .ok (.capSecret _ _) ⟨hw.csvWf, hw.realDbWf, hw.fakeDbWf⟩
  -- 21. catch-all error
  · contradiction

/-! ## Whole-Program Declaration Extraction & Pigeonhole Exhaustiveness -/

theorem checkProgram_parts {prog : Program} (hprog : checkProgram prog = .ok ()) :
    checkDataDecls prog = .ok () ∧
    checkSchemaDecls prog = .ok () ∧
    checkConstDecls prog = .ok () ∧
    checkFunDecls prog prog.funs = .ok () := by
  simp only [checkProgram, bind, Except.bind] at hprog
  split at hprog <;> try contradiction
  split at hprog <;> try contradiction
  cases hp : checkPolicyWf prog <;> simp only [hp] at hprog <;> try contradiction
  cases hd : checkDataDecls prog <;> simp only [hd] at hprog <;> try contradiction
  cases hs : checkSchemaDecls prog <;> simp only [hs] at hprog <;> try contradiction
  cases hc : checkConstDecls prog <;> simp only [hc] at hprog <;> try contradiction
  split at hprog <;> try contradiction
  cases hf : checkFunDecls prog prog.funs <;> simp only [hf] at hprog <;> try contradiction
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem list_find?_pred {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    simp only [List.find?] at h
    cases hp : p y
    · simp only [hp] at h; exact list_find?_pred h
    · simp only [hp, Option.some.injEq] at h; subst h; exact hp

theorem checkDataDecls_valid {prog : Program} {dName : Ident} {dDecl : DataDecl}
    (hprog : checkProgram prog = .ok ())
    (hfind : prog.findData? dName = some dDecl) :
    distinctIdents (dDecl.ctors.map CtorDecl.name) = true := by
  have hd := (checkProgram_parts hprog).1
  have hmem := List.mem_of_find?_eq_some hfind
  unfold checkDataDecls at hd
  split at hd <;> try contradiction
  simp only at hd
  split at hd
  · rename_i hall
    have h1 := (List.all_eq_true.mp hall) dDecl hmem
    simp only [Bool.and_eq_true] at h1
    exact h1.1.2
  · contradiction

theorem checkFunDecls_mem {prog : Program} :
    ∀ {fs : List FunDecl} {f : FunDecl},
      checkFunDecls prog fs = .ok () → f ∈ fs → checkFunDecl prog f = .ok ()
  | [], _, _, hm => nomatch hm
  | hd :: tl, f, hchk, hm => by
    simp only [checkFunDecls, bind, Except.bind] at hchk
    cases hhd : checkFunDecl prog hd with
    | error _ => simp [hhd] at hchk
    | ok _ =>
      simp only [hhd] at hchk
      rcases List.mem_cons.mp hm with rfl | hrest
      · exact hhd
      · exact checkFunDecls_mem hchk hrest

theorem checkFunDecl_valid {prog : Program} {fnName : Ident} {fDecl : FunDecl}
    (hprog : checkProgram prog = .ok ())
    (hfind : prog.findFun? fnName = some fDecl) :
    ∃ bodyLTy,
      checkExpr prog fDecl.params.reverse [] fDecl.pc fDecl.kind.isSpec fDecl.body = .ok bodyLTy ∧
      bodyLTy.ty = fDecl.ret.ty := by
  have hfs := (checkProgram_parts hprog).2.2.2
  have hf := checkFunDecls_mem hfs (List.mem_of_find?_eq_some hfind)
  unfold checkFunDecl at hf
  split at hf <;> try contradiction
  split at hf <;> try contradiction
  split at hf <;> try contradiction
  split at hf <;> try contradiction
  split at hf <;> try contradiction
  simp only [bind, Except.bind] at hf
  cases hpol : checkParamsPolicy prog.policy fDecl.params with
  | error _ => simp [hpol] at hf
  | ok _ =>
    simp only [hpol] at hf
    cases hb : checkExpr prog fDecl.params.reverse [] fDecl.pc fDecl.kind.isSpec fDecl.body with
    | error _ => simp [hb] at hf
    | ok bodyLTy =>
      simp only [hb] at hf
      split at hf <;> try contradiction
      rename_i hsub
      simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
      exact ⟨bodyLTy, rfl, hsub.1⟩

theorem distinctIdents_filter_str (p : Ident → Bool) :
    ∀ {xs : List Ident}, distinctIdents xs = true → distinctIdents (xs.filter p) = true
  | [], _ => rfl
  | x :: xs, hd => by
    rcases distinctIdents_not_mem hd with ⟨hnot, htl⟩
    simp only [List.filter_cons]
    cases hp : p x
    · exact distinctIdents_filter_str p htl
    · simp only [↓reduceIte, distinctIdents, Bool.and_eq_true]
      refine ⟨?_, distinctIdents_filter_str p htl⟩
      cases hc : (xs.filter p).contains x with
      | false => rfl
      | true =>
        exfalso
        exact hnot (List.mem_filter.mp (List.contains_iff_mem.mp hc)).1

theorem filter_ne_eq_self {y : Ident} :
    ∀ {xs : List Ident}, y ∉ xs → xs.filter (fun z => z != y) = xs
  | [], _ => rfl
  | x :: xs, hnot => by
    have hxy : (x != y) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro heq; subst heq; exact hnot (.head _)
    simp only [List.filter_cons, hxy, ↓reduceIte]
    exact congrArg (x :: ·) (filter_ne_eq_self (fun hm => hnot (.tail _ hm)))

theorem filter_ne_length {y : Ident} :
    ∀ {xs : List Ident}, distinctIdents xs = true → y ∈ xs →
      (xs.filter (fun z => z != y)).length + 1 = xs.length
  | [], _, hm => nomatch hm
  | x :: xs, hd, hm => by
    rcases distinctIdents_not_mem hd with ⟨hnot, htl⟩
    by_cases hxy : x = y
    · subst hxy
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        filter_ne_eq_self hnot, List.length_cons]
    · have hmem' : y ∈ xs := by
        rcases List.mem_cons.mp hm with rfl | hr
        · exact absurd rfl hxy
        · exact hr
      have hneB : (x != y) = true := bne_iff_ne.mpr hxy
      simp only [List.filter_cons, hneB, ↓reduceIte, List.length_cons]
      have ih := filter_ne_length htl hmem'
      omega

theorem filter_ne_length_le (y : Ident) :
    ∀ (ys : List Ident), y ∈ ys → (ys.filter (fun z => z != y)).length < ys.length
  | [], hm => nomatch hm
  | x :: ys, hm => by
    by_cases hxy : x = y
    · subst hxy
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hle := List.length_filter_le (fun z => z != x) ys
      omega
    · have hmem' : y ∈ ys := by
        rcases List.mem_cons.mp hm with rfl | hr
        · exact absurd rfl hxy
        · exact hr
      have hneB : (x != y) = true := bne_iff_ne.mpr hxy
      simp only [List.filter_cons, hneB, ↓reduceIte, List.length_cons]
      have ih := filter_ne_length_le y ys hmem'
      omega

theorem distinctIdents_length_le :
    ∀ {xs ys : List Ident}, distinctIdents xs = true → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hd, hsub => by
    rcases distinctIdents_not_mem hd with ⟨hnot, htl⟩
    have hx : x ∈ ys := hsub x (.head _)
    have hlt := filter_ne_length_le x ys hx
    have hsub' : ∀ z ∈ xs, z ∈ ys.filter (fun z => z != x) := by
      intro z hz
      rw [List.mem_filter]
      refine ⟨hsub z (.tail _ hz), bne_iff_ne.mpr ?_⟩
      intro heq; subst heq; exact hnot hz
    have ih := distinctIdents_length_le htl hsub'
    simp only [List.length_cons]
    omega

theorem pigeonhole_distinct_idents :
    ∀ {ys xs : List Ident},
      distinctIdents xs = true →
      distinctIdents ys = true →
      (∀ x ∈ xs, x ∈ ys) →
      xs.length = ys.length →
      ∀ y ∈ ys, y ∈ xs
  | [], _, _, _, _, _, _, hy => nomatch hy
  | y :: ys, xs, hdx, hdy, hsub, hlen, q, hq => by
    rcases distinctIdents_not_mem hdy with ⟨hyNot, hdyTl⟩
    by_cases hyIn : y ∈ xs
    · rcases List.mem_cons.mp hq with rfl | hqTl
      · exact hyIn
      · let xs' := xs.filter (fun z => z != y)
        have hdx' : distinctIdents xs' = true := distinctIdents_filter_str _ hdx
        have hlen' : xs'.length = ys.length := by
          have h1 := filter_ne_length hdx hyIn
          dsimp only [xs']
          simp only [List.length_cons] at hlen
          omega
        have hsub' : ∀ z ∈ xs', z ∈ ys := by
          intro z hz
          rcases List.mem_filter.mp hz with ⟨hzxs, hzny⟩
          rcases List.mem_cons.mp (hsub z hzxs) with rfl | hzys
          · simp at hzny
          · exact hzys
        have hqIn' := pigeonhole_distinct_idents hdx' hdyTl hsub' hlen' q hqTl
        exact (List.mem_filter.mp hqIn').1
    · exfalso
      have hsubTl : ∀ z ∈ xs, z ∈ ys := by
        intro z hz
        rcases List.mem_cons.mp (hsub z hz) with rfl | hzys
        · exact absurd hz hyIn
        · exact hzys
      have hle := distinctIdents_length_le hdx hsubTl
      simp only [List.length_cons] at hlen
      omega

theorem expectedCaseSpecs_distinct {prog : Program} {sTy : Ty} {sTags : TagSet}
    {specs : List (Ident × List LTy)}
    (hprog : checkProgram prog = .ok ())
    (hsp : expectedCaseSpecs prog sTy sTags = .ok specs) :
    distinctIdents (specs.map Prod.fst) = true := by
  cases sTy <;> try contradiction
  case bool => injection hsp with hs; subst hs; decide
  case option _ => injection hsp with hs; subst hs; simp [distinctIdents]
  case result _ _ => injection hsp with hs; subst hs; simp [distinctIdents]
  case data dName =>
    simp only [expectedCaseSpecs] at hsp
    cases hd : prog.findData? dName with
    | none => simp [hd] at hsp
    | some dDecl =>
      simp only [hd, Except.ok.injEq] at hsp; subst hsp
      have hmap : (dDecl.ctors.map (fun c => (c.name, c.fields.map (fun f => f.addTags sTags)))).map Prod.fst =
          dDecl.ctors.map CtorDecl.name := by
        induction dDecl.ctors <;> simp [*]
      rw [hmap]
      exact checkDataDecls_valid hprog hd

theorem addTags_addTags (f : LTy) (s1 s2 : TagSet) :
    (f.addTags s1).addTags s2 = f.addTags (s1.union s2) := by
  cases f with | mk ty ts =>
  simp only [LTy.addTags, LTy.mk.injEq, true_and]
  apply TagSet.ext; intro t
  simp only [TagSet.mem_union]
  cases ts.mem t <;> cases s1.mem t <;> cases s2.mem t <;> rfl

theorem zip_addTags_wf {prog : Program} (extra : TagSet) :
    ∀ {fields : List LTy} {vs : List Val},
      ValListWf prog vs fields →
      (List.zip (fields.map (fun f => f.addTags extra)) vs).map Prod.fst =
        fields.map (fun f => f.addTags extra) ∧
      ValListWf prog
        ((List.zip (fields.map (fun f => f.addTags extra)) vs).map Prod.snd)
        (fields.map (fun f => f.addTags extra))
  | [], [], .nil => ⟨rfl, .nil⟩
  | f :: fs, v :: vs, .cons hv htl => by
    rcases zip_addTags_wf extra htl with ⟨hfst, hsnd⟩
    have hty : (f.addTags extra).ty = f.ty := by cases f; rfl
    simp only [List.map_cons, List.zip_cons_cons]
    exact ⟨congrArg (f.addTags extra :: ·) hfst, .cons (hty.symm ▸ hv) hsnd⟩

theorem find_data_ctor_in_specs {sTags : TagSet} :
    ∀ (ctors : List CtorDecl) {cName : Ident} {cDecl : CtorDecl},
      ctors.find? (fun c => c.name == cName) = some cDecl →
      (ctors.map (fun c => (c.name, c.fields.map (fun f => f.addTags sTags)))).find?
        (fun p => p.1 == cName) = some (cName, cDecl.fields.map (fun f => f.addTags sTags))
  | [], _, _, hf => nomatch hf
  | c :: cs, cName, cDecl, hf => by
    simp only [List.find?, List.map_cons] at hf ⊢
    cases hc : (c.name == cName)
    · simp only [hc] at hf ⊢
      exact find_data_ctor_in_specs cs hf
    · simp only [hc, Option.some.injEq] at hf
      subst hf
      have hname : c.name = cName := beq_iff_eq.mp hc
      subst hname
      simp

theorem matchCaseVal_sound {prog : Program} {sVal : Val} {scrutLTy : LTy} {armPc : TagSet}
    {specs : List (Ident × List LTy)}
    (hv : ValWf prog sVal scrutLTy.ty)
    (hsp : expectedCaseSpecs prog scrutLTy.ty scrutLTy.effectiveTags = .ok specs) :
    ∃ cName fieldLTys typedVals,
      matchCaseVal prog sVal scrutLTy armPc = some (cName, typedVals) ∧
      specs.find? (fun p => p.1 == cName) = some (cName, fieldLTys) ∧
      typedVals.map Prod.fst = fieldLTys.map (fun f => f.addTags armPc) ∧
      ValListWf prog (typedVals.map Prod.snd) (fieldLTys.map (fun f => f.addTags armPc)) := by
  cases scrutLTy with | mk sTy sOuter =>
  dsimp only [LTy.ty] at hv hsp
  cases hv with
  | bool b =>
    injection hsp with hs; subst hs
    cases b
    · exact ⟨"false", [], [], rfl, rfl, rfl, .nil⟩
    · exact ⟨"true", [], [], rfl, rfl, rfl, .nil⟩
  | optNone inner =>
    injection hsp with hs; subst hs
    exact ⟨"None", [], [], rfl, rfl, rfl, .nil⟩
  | optSome hu =>
    injection hsp with hs; subst hs
    exact ⟨"Some", [_], [(_, _)], rfl, rfl, rfl, .cons hu .nil⟩
  | resOk hu =>
    injection hsp with hs; subst hs
    exact ⟨"Ok", [_], [(_, _)], rfl, rfl, rfl, .cons hu .nil⟩
  | resErr he =>
    injection hsp with hs; subst hs
    exact ⟨"Error", [_], [(_, _)], rfl, rfl, rfl, .cons he .nil⟩
  | @ctor dName cName vs dDecl cDecl hd hc hvs =>
    simp only [expectedCaseSpecs, hd, Except.ok.injEq] at hsp; subst hsp
    have hlenEq : (vs.length == cDecl.fields.length) = true := beq_iff_eq.mpr hvs.length_eq
    have hbne : (dName != dName) = false := by simp
    have hmatchEq : matchCaseVal prog (.ctor dName cName vs) (.mk (.data dName) sOuter) armPc =
        some (cName, List.zip (cDecl.fields.map (fun f => f.addTags ((LTy.mk (.data dName) sOuter).effectiveTags.union armPc))) vs) := by
      unfold matchCaseVal
      simp only [LTy.ty, hbne, Bool.false_eq_true, ↓reduceIte, hd, hc, hlenEq]
    have hfindSpec := find_data_ctor_in_specs dDecl.ctors hc
      (sTags := (LTy.mk (.data dName) sOuter).effectiveTags)
    rcases zip_addTags_wf ((LTy.mk (.data dName) sOuter).effectiveTags.union armPc) hvs with ⟨hfst, hsnd⟩
    have hmapEq : (cDecl.fields.map (fun f => f.addTags (LTy.mk (.data dName) sOuter).effectiveTags)).map
        (fun f => f.addTags armPc) =
        cDecl.fields.map (fun f => f.addTags ((LTy.mk (.data dName) sOuter).effectiveTags.union armPc)) := by
      induction cDecl.fields with
      | nil => rfl
      | cons f fs ih => simp [addTags_addTags, ih]
    refine ⟨cName, _, _, hmatchEq, hfindSpec, ?_, ?_⟩
    · rw [hmapEq]; exact hfst
    · rw [hmapEq]; exact hsnd
  | _ => simp [expectedCaseSpecs] at hsp

theorem find?_some_of_mem_ctor :
    ∀ (arms : List CaseArm) {cName : Ident},
      cName ∈ arms.map (fun (.mk c _ _) => c) →
      ∃ b body, arms.find? (fun (.mk ac _ _) => ac == cName) = some (.mk cName b body)
  | [], _, hm => nomatch hm
  | .mk ac bs body :: rest, cName, hm => by
    simp only [List.find?]
    cases h : (ac == cName)
    · rcases List.mem_cons.mp hm with rfl | htl
      · simp at h
      · exact find?_some_of_mem_ctor rest htl
    · have heq := beq_iff_eq.mp h; subst heq
      exact ⟨bs, body, rfl⟩

theorem find?_name_eq {α : Type} (f : α → Ident) :
    ∀ {xs : List α} {k : Ident} {x : α},
      xs.find? (fun c => f c == k) = some x → f x = k
  | [], _, _, h => nomatch h
  | y :: _, k, _, h => by
    simp only [List.find?] at h
    cases hy : (f y == k)
    · simp only [hy] at h; exact find?_name_eq f h
    · simp only [hy, Option.some.injEq] at h; subst h; exact beq_iff_eq.mp hy

theorem checkCaseArms_props {prog : Program} {env : TyEnv} {jenv : JoinEnv} {armPc : TagSet}
    {inSpec : Bool} {specs : List (Ident × List LTy)} :
    ∀ {arms : List CaseArm} {armLTys : List LTy},
      checkCaseArms prog env jenv armPc inSpec specs arms = .ok armLTys →
      (∀ c ∈ arms.map (fun (.mk ac _ _) => ac), c ∈ specs.map Prod.fst) ∧
      (∀ cName bs body fieldLTys,
        arms.find? (fun (.mk ac _ _) => ac == cName) = some (.mk cName bs body) →
        specs.find? (fun p => p.1 == cName) = some (cName, fieldLTys) →
        bs.length = fieldLTys.length ∧
        ∃ aLTy, aLTy ∈ armLTys ∧
          checkExpr prog (extendTyEnv env (List.zip bs (fieldLTys.map (fun f => f.addTags armPc))))
            jenv armPc inSpec body = .ok aLTy)
  | [], _, hchk => by
    unfold checkCaseArms at hchk; injection hchk with h'; subst h'
    exact ⟨(fun _ hm => nomatch hm), (fun _ _ _ _ hf _ => nomatch hf)⟩
  | .mk ac bs body :: rest, armLTys, hchk => by
    unfold checkCaseArms at hchk
    cases hsp : specs.find? (fun p => p.1 == ac) with
    | none => simp [hsp] at hchk
    | some pair =>
      rcases pair with ⟨sn, fLTys⟩
      simp only [hsp] at hchk
      cases hbad : (!distinctIdents bs || bs.length != fLTys.length) <;>
        simp only [hbad, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at hchk
      · cases hb : checkExpr prog (extendTyEnv env (List.zip bs (fLTys.map (fun f => f.addTags armPc)))) jenv armPc inSpec body with
        | error _ => simp [hb] at hchk
        | ok hd =>
          simp only [hb] at hchk
          cases hr : checkCaseArms prog env jenv armPc inSpec specs rest with
          | error _ => simp [hr] at hchk
          | ok tl =>
            simp only [hr, Except.ok.injEq] at hchk; subst hchk
            rcases checkCaseArms_props hr with ⟨hmemTl, hfindTl⟩
            refine ⟨?_, ?_⟩
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hrest
              · have hsn : sn = c := find?_name_eq Prod.fst hsp
                subst hsn
                exact List.mem_map_of_mem (List.mem_of_find?_eq_some hsp)
              · exact hmemTl c hrest
            · intro cName bs' body' fieldLTys hfa hfs
              simp only [List.find?] at hfa
              cases hac : (ac == cName)
              · simp only [hac] at hfa
                rcases hfindTl cName bs' body' fieldLTys hfa hfs with ⟨hlen, aLTy, haMem, haChk⟩
                exact ⟨hlen, aLTy, .tail _ haMem, haChk⟩
              · have heq := beq_iff_eq.mp hac; subst heq
                simp only [hac, Option.some.injEq, CaseArm.mk.injEq] at hfa
                rcases hfa with ⟨_, rfl, rfl⟩
                rw [hsp] at hfs; injection hfs with hp; injection hp with _ hfeq; subst hfeq
                simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hbad
                exact ⟨hbad.2, hd, .head _, hb⟩
      · contradiction

theorem envWf_armEntries {prog : Program} :
    ∀ (binders : List Ident) (fLTys : List LTy) (vs : List Val) (typedVals : List (LTy × Val)) (base : Env),
      binders.length = fLTys.length →
      typedVals.map Prod.fst = fLTys →
      typedVals.map Prod.snd = vs →
      ValListWf prog vs fLTys →
      EnvWf prog base →
      let entries : Env := (List.zip binders typedVals).map
        (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })
      EnvWf prog (entries ++ base) ∧ envToTyEnv (entries ++ base) = List.zip binders fLTys ++ envToTyEnv base
  | [], [], [], [], base, _, _, _, .nil, hbase => ⟨hbase, rfl⟩
  | b :: bs, _ :: ls, _ :: vs, (tl, tv) :: tvs, base, hblen, hfst, hsnd, .cons hv htl, hbase => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hblen
    simp only [List.map_cons, List.cons.injEq] at hfst hsnd
    rcases hfst with ⟨rfl, hfstTl⟩
    rcases hsnd with ⟨rfl, hsndTl⟩
    rcases envWf_armEntries bs ls vs tvs base hblen hfstTl hsndTl htl hbase with ⟨heWf, htyEq⟩
    exact ⟨.cons hv heWf, congrArg ((b, tl) :: ·) htyEq⟩
  | _ :: _, _ :: _, _, [], _, _, hfst, _, _, _ => by simp at hfst
  | [], [], _ :: _, _, _, _, _, _, hwf, _ => nomatch hwf
  | _ :: _, [], _, _, _, hblen, _, _, _, _ => by simp at hblen
  | [], _ :: _, _, _, _, hblen, _, _, _, _ => by simp at hblen

/-! ## Pure Relational Operator Soundness Lemmas -/

theorem lookupColIdx?_shift (name : Ident) :
    ∀ (k : Nat) (cs : List ColSpec),
      lookupColIdx?.go name (k + 1) cs = (lookupColIdx?.go name k cs).map (fun (i, c) => (i + 1, c))
  | _, [] => rfl
  | k, c :: cs => by
    unfold lookupColIdx?.go
    cases hc : (c.name == name)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact lookupColIdx?_shift name (k + 1) cs
    · simp [↓reduceIte]

theorem lookupColIdx?_cons (c : ColSpec) (cs : List ColSpec) (name : Ident) :
  lookupColIdx? (c :: cs) name =
    if c.name == name then some (0, c)
    else (lookupColIdx? cs name).map (fun (i, x) => (i + 1, x)) := by
  simp only [lookupColIdx?]
  conv => lhs; unfold lookupColIdx?.go
  cases hc : (c.name == name)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact lookupColIdx?_shift name 0 cs
  · simp [↓reduceIte]

theorem lookupColIdx?_props {cols : List ColSpec} {name : Ident} {idx : Nat} {c : ColSpec}
    (h : lookupColIdx? cols name = some (idx, c)) :
    cols[idx]? = some c ∧ c.name = name := by
  induction cols generalizing idx with
  | nil => simp [lookupColIdx?, lookupColIdx?.go] at h
  | cons hd tl ih =>
    rw [lookupColIdx?_cons] at h
    cases hn : (hd.name == name)
    · simp only [hn, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨⟨subIdx, subC⟩, hsub, hinj⟩
      injection hinj with hi hc; subst hi; subst hc
      exact ih hsub
    · simp only [hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, beq_iff_eq.mp hn⟩

theorem cellsWf_set_by_name {prog : Program} {targetName : Ident} {newVal : Val}
    (f : ColSpec → ColSpec) :
    ∀ {cols : List ColSpec} {cells : List Val} {idx : Nat} {origCol : ColSpec},
      distinctIdents (cols.map ColSpec.name) = true →
      lookupColIdx? cols targetName = some (idx, origCol) →
      CellsWf prog cells cols →
      (∀ c ∈ cols, if c.name == targetName then ValWf prog newVal (f c).ty.toTy else (f c).ty = c.ty) →
      CellsWf prog (cells.set idx newVal) (cols.map f)
  | [], _, _, _, _, hlook, _, _ => by simp [lookupColIdx?, lookupColIdx?.go] at hlook
  | c :: cs, _ :: vs, idx, origCol, huniq, hlook, .cons hv htl, hall => by
    rcases distinctIdents_not_mem huniq with ⟨hnot, huniqTl⟩
    rw [lookupColIdx?_cons] at hlook
    cases hc : (c.name == targetName)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hlook
      rcases hlook with ⟨⟨subIdx, subCol⟩, hsub, hinj⟩
      injection hinj with hi _; subst hi
      have hfc : (f c).ty = c.ty := by
        have h0 := hall c (.head _)
        simpa [hc] using h0
      simp only [List.set_cons_succ, List.map_cons]
      exact .cons (hfc.symm ▸ hv)
        (cellsWf_set_by_name f huniqTl hsub htl (fun x hx => hall x (.tail _ hx)))
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hlook
      rcases hlook with ⟨rfl, _⟩
      have hnew : ValWf prog newVal (f c).ty.toTy := by
        have h0 := hall c (.head _)
        simpa [hc] using h0
      have htyRest : cs.map ColSpec.ty = (cs.map f).map ColSpec.ty := by
        have hmem : ∀ x ∈ cs, (f x).ty = x.ty := by
          intro x hx
          have hne : (x.name == targetName) = false := by
            cases hxn : (x.name == targetName)
            · rfl
            · exfalso
              have heq : x.name = c.name := (beq_iff_eq.mp hxn).trans (beq_iff_eq.mp hc).symm
              exact hnot (heq ▸ List.mem_map_of_mem hx)
          have h0 := hall x (.tail _ hx)
          simpa [hne] using h0
        clear huniq hnot huniqTl htl hall hc hv hnew
        induction cs with
        | nil => rfl
        | cons d ds ihd =>
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨(hmem d (.head _)).symm, ihd (fun x hx => hmem x (.tail _ hx))⟩
      simp only [List.set_cons_zero, List.map_cons]
      exact .cons hnew (htl.congr_ty htyRest)

theorem checkRowLit_go_sound {prog : Program} :
    ∀ (cols : List ColSpec) (lits : List Literal),
      checkRowLit.go prog cols lits = true →
      CellsWf prog (lits.map evalLiteral) cols
  | [], [], _ => .nil
  | c :: cs, l :: ls, h => by
    unfold checkRowLit.go at h
    cases hl : checkLiteral prog TagSet.empty l with
    | error _ => simp [hl] at h
    | ok lty =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .cons (h.1 ▸ checkLiteral_sound hl) (checkRowLit_go_sound cs ls h.2)
  | _ :: _, [], h => by simp [checkRowLit.go] at h
  | [], _ :: _, h => by simp [checkRowLit.go] at h

theorem checkRowExpr_validScalarTy {prog : Program} {env : TyEnv} {cols : List ColSpec}
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true) :
    ∀ {re : RowExpr} {sTy : ScalarTy} {rTags : TagSet},
      checkRowExpr prog env cols re = .ok (sTy, rTags) →
      validScalarTy prog sTy = true
  | .lit v, sTy, _, h => by
    unfold checkRowExpr at h; simp only [bind, Except.bind] at h
    cases hl : checkLiteral prog TagSet.empty v with
    | error _ => simp [hl] at h
    | ok lty =>
      simp only [hl] at h
      cases hs : lty.ty.toScalarTy? with
      | none => simp [hs] at h
      | some st =>
        simp only [hs] at h
        cases hv : validScalarTy prog st <;> simp [hv] at h
        rcases h with ⟨rfl, _⟩; exact hv
  | .col name, sTy, _, h => by
    unfold checkRowExpr at h
    cases hf : cols.find? (fun c => c.name == name) with
    | none => simp [hf] at h
    | some c =>
      simp only [hf, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact hcols c (List.mem_of_find?_eq_some hf)
  | .outerVar name, sTy, _, h => by
    unfold checkRowExpr at h
    cases hl : lookupTyEnv env name with
    | none => simp [hl] at h
    | some lty =>
      simp only [hl] at h
      cases hs : lty.ty.toScalarTy? with
      | none => simp [hs] at h
      | some st =>
        simp only [hs] at h
        cases hv : validScalarTy prog st <;> simp [hv] at h
        rcases h with ⟨rfl, _⟩; exact hv
  | .constRef name, sTy, _, h => by
    unfold checkRowExpr at h
    cases hc : prog.findConst? name with
    | none => simp [hc] at h
    | some cDecl =>
      simp only [hc] at h
      cases hs : cDecl.lty.ty.toScalarTy? with
      | none => simp [hs] at h
      | some st =>
        simp only [hs] at h
        cases hv : validScalarTy prog st <;> simp [hv] at h
        rcases h with ⟨rfl, _⟩; exact hv
  | .prim op args, sTy, _, h => by
    unfold checkRowExpr at h; simp only [bind, Except.bind] at h
    cases ha : checkRowExprList prog env cols args with
    | error _ => simp [ha] at h
    | ok pairs =>
      simp only [ha] at h
      cases hp : checkPrimOp prog TagSet.empty op (pairs.map (fun (st, ts) => LTy.mk st.toTy ts)) with
      | error _ => simp [hp] at h
      | ok resLTy =>
        simp only [hp] at h
        cases hs : resLTy.ty.toScalarTy? with
        | none => simp [hs] at h
        | some st =>
          simp only [hs] at h
          cases hv : validScalarTy prog st <;> simp [hv] at h
          rcases h with ⟨rfl, _⟩; exact hv
  | .ifE cond tBr eBr, sTy, _, h => by
    unfold checkRowExpr at h; simp only [bind, Except.bind] at h
    cases hc : checkRowExpr prog env cols cond with
    | error _ => simp [hc] at h
    | ok cp =>
      simp only [hc] at h
      cases ht : checkRowExpr prog env cols tBr with
      | error _ => simp [ht] at h
      | ok tp =>
        simp only [ht] at h
        cases he : checkRowExpr prog env cols eBr with
        | error _ => simp [he] at h
        | ok ep =>
          simp only [he] at h
          split at h <;> try contradiction
          injection h with hp; injection hp with hs _; subst hs
          exact checkRowExpr_validScalarTy hcols ht
  | .coalesce optE defE, sTy, _, h => by
    unfold checkRowExpr at h; simp only [bind, Except.bind] at h
    cases ho : checkRowExpr prog env cols optE with
    | error _ => simp [ho] at h
    | ok op =>
      rcases op with ⟨oTy, oTags⟩
      simp only [ho] at h
      cases hd : checkRowExpr prog env cols defE with
      | error _ => simp [hd] at h
      | ok dp =>
        rcases dp with ⟨dTy, dTags⟩
        simp only [hd] at h
        cases oTy <;> try contradiction
        dsimp only at h
        split at h <;> try contradiction
        injection h with hp; injection hp with hs _; subst hs
        exact checkRowExpr_validScalarTy hcols hd
  | .callPure fnName args, sTy, _, h => by
    unfold checkRowExpr at h; simp only [bind, Except.bind] at h
    cases ha : checkRowExprList prog env cols args with
    | error _ => simp [ha] at h
    | ok pairs =>
      simp only [ha] at h
      cases hf : prog.findFun? fnName with
      | none => simp [hf] at h
      | some fDecl =>
        simp only [hf] at h
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        cases hs : fDecl.ret.ty.toScalarTy? with
        | none => simp [hs] at h
        | some st =>
          simp only [hs] at h
          cases hv : validScalarTy prog st <;> simp [hv] at h
          rcases h with ⟨rfl, _⟩; exact hv

theorem evalBucketCell_pick_some (v : Val) :
    ∀ (cs : List Val) (ls : List String),
      ls.length = cs.length + 1 →
      ∃ s, evalBucketCell.pick v cs ls = some s
  | [], [lastLbl], _ => ⟨lastLbl, rfl⟩
  | [], [] , h => by simp at h
  | [], _ :: _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | cut :: restCuts, lbl :: restLbls, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    unfold evalBucketCell.pick
    cases valLt v cut
    · exact evalBucketCell_pick_some v restCuts restLbls h
    · exact ⟨lbl, rfl⟩

theorem evalBucketCell_sound {prog : Program} {srcTy : ScalarTy} {cuts : List Literal}
    {labels : List String} (sVal : Val)
    (hchk : checkBucketCuts prog srcTy cuts labels = true) :
    ∃ bVal, evalBucketCell sVal (cuts.map evalLiteral) labels = some bVal ∧ ValWf prog bVal .text := by
  simp only [checkBucketCuts, Bool.and_eq_true, beq_iff_eq] at hchk
  have hlen : labels.length = (cuts.map evalLiteral).length + 1 := by simp [hchk.1.1.2]
  rcases evalBucketCell_pick_some sVal (cuts.map evalLiteral) labels hlen with ⟨s, hs⟩
  exact ⟨.text s, by simp [evalBucketCell, hs], .text s⟩

theorem distinctIdents_replace_or_append (newCol : ColSpec) :
    ∀ (cols : List ColSpec),
      distinctIdents (cols.map ColSpec.name) = true →
      distinctIdents ((if (cols.find? (fun c => c.name == newCol.name)).isSome then
          cols.map (fun c => if c.name == newCol.name then newCol else c)
        else cols ++ [newCol]).map ColSpec.name) = true := by
  intro cols huniq
  cases hf : cols.find? (fun c => c.name == newCol.name) with
  | some found =>
    simp only [Option.isSome_some, ↓reduceIte]
    have hnames : ∀ (cs : List ColSpec),
        (cs.map (fun c => if c.name == newCol.name then newCol else c)).map ColSpec.name =
        cs.map ColSpec.name := by
      intro cs; induction cs with
      | nil => rfl
      | cons c csTl ih =>
        simp only [List.map_cons]
        cases hc : (c.name == newCol.name)
        · simp only [Bool.false_eq_true, ↓reduceIte, ih]
        · simp only [↓reduceIte, beq_iff_eq.mp hc, ih]
    rw [hnames cols]; exact huniq
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
    have hnot : newCol.name ∉ cols.map ColSpec.name := by
      intro hm
      rw [List.mem_map] at hm
      rcases hm with ⟨c, hc, hname⟩
      have hnone := List.find?_eq_none.mp hf c hc
      simp [hname] at hnone
    clear hf
    induction cols with
    | nil => rfl
    | cons c cs ih =>
      rcases distinctIdents_not_mem huniq with ⟨hcnot, htl⟩
      have hnotTl : newCol.name ∉ cs.map ColSpec.name := fun hm => hnot (.tail _ hm)
      have hcne : c.name ≠ newCol.name := fun heq => hnot (heq ▸ .head _)
      simp only [List.map_cons, List.cons_append, distinctIdents, Bool.and_eq_true]
      refine ⟨?_, ih htl hnotTl⟩
      cases hmem : (cs.map ColSpec.name ++ [newCol.name]).contains c.name with
      | false => rfl
      | true =>
        exfalso
        rw [List.contains_iff_mem, List.mem_append] at hmem
        rcases hmem with hl | hr
        · exact hcnot hl
        · simp at hr; exact hcne hr

theorem colProps_replace_or_append {prog : Program} {cols : List ColSpec} {newCol : ColSpec}
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text))
    (hnew : validScalarTy prog newCol.ty = true ∧ (newCol.bucketed = true → newCol.ty = .text)) :
    ∀ c ∈ (if (cols.find? (fun x => x.name == newCol.name)).isSome then
        cols.map (fun x => if x.name == newCol.name then newCol else x)
      else cols ++ [newCol]),
      validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) := by
  intro c hc
  split at hc
  · rw [List.mem_map] at hc
    rcases hc with ⟨orig, horig, rfl⟩
    split
    · exact hnew
    · exact hcols orig horig
  · rw [List.mem_append] at hc
    rcases hc with hl | hr
    · exact hcols c hl
    · simp at hr; subst hr; exact hnew

theorem lookupColIdx?_none_iff_find?_none (cols : List ColSpec) (name : Ident) :
    lookupColIdx? cols name = none ↔ cols.find? (fun c => c.name == name) = none := by
  induction cols with
  | nil => simp [lookupColIdx?, lookupColIdx?.go]
  | cons c cs ih =>
    rw [lookupColIdx?_cons]
    simp only [List.find?]
    cases hc : (c.name == name)
    · simp [ih]
    · simp

theorem applyDeriveItem_props {prog : Program} {tEnv : TyEnv} {cols nextCols : List ColSpec}
    {item : DeriveItem}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text))
    (happly : applyDeriveItem prog tEnv cols item = .ok nextCols) :
    distinctIdents (nextCols.map ColSpec.name) = true ∧
    (∀ c ∈ nextCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text)) := by
  cases item with
  | colExpr name re =>
    unfold applyDeriveItem at happly; simp only [bind, Except.bind] at happly
    cases hre : checkRowExpr prog tEnv cols re with
    | error _ => simp [hre] at happly
    | ok pair =>
      rcases pair with ⟨sTy, rTags⟩
      simp only [hre] at happly
      have hsv : validScalarTy prog sTy = true :=
        checkRowExpr_validScalarTy (fun c hc => (hcols c hc).1) hre
      let nc : ColSpec := { name := name, ty := sTy, tags := rTags, bucketed := false, aggKind := .raw }
      have heq : nextCols = (if (cols.find? (fun c => c.name == nc.name)).isSome then
          cols.map (fun c => if c.name == nc.name then nc else c)
        else cols ++ [nc]) := by
        dsimp only [nc]
        cases hex : (cols.find? (fun c => c.name == name)).isSome <;>
          (simp only [hex, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happly ⊢; exact happly.symm)
      rw [heq]
      exact ⟨distinctIdents_replace_or_append nc cols huniq,
        colProps_replace_or_append hcols ⟨hsv, fun hb => by simp [nc] at hb⟩⟩
  | bucketCol name src cuts labels =>
    unfold applyDeriveItem at happly
    cases hs : cols.find? (fun c => c.name == src) with
    | none => simp [hs] at happly
    | some srcCol =>
      simp only [hs] at happly
      cases hb : checkBucketCuts prog srcCol.ty cuts labels
      · simp [hb] at happly
      · simp only [hb, ↓reduceIte] at happly
        let nc : ColSpec := { name := name, ty := .text, tags := srcCol.tags, bucketed := true, aggKind := .raw }
        have heq : nextCols = (if (cols.find? (fun c => c.name == nc.name)).isSome then
            cols.map (fun c => if c.name == nc.name then nc else c)
          else cols ++ [nc]) := by
          dsimp only [nc]
          cases hex : (cols.find? (fun c => c.name == name)).isSome <;>
            (simp only [hex, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happly ⊢; exact happly.symm)
        rw [heq]
        exact ⟨distinctIdents_replace_or_append nc cols huniq,
          colProps_replace_or_append hcols ⟨rfl, fun _ => rfl⟩⟩

def deriveItemName : DeriveItem → Ident
  | .colExpr n _ => n
  | .bucketCol n _ _ _ => n

theorem evalDeriveMapRows_sound {prog : Program} {tEnv : TyEnv}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    {cols nextCols : List ColSpec} {item : DeriveItem}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (happly : applyDeriveItem prog tEnv cols item = .ok nextCols)
    (hreSound : ∀ r re sTy rTags, CellsWf prog r.cells cols →
      checkRowExpr prog tEnv cols re = .ok (sTy, rTags) →
      PrimResultWf prog sTy.toTy (evalRE cols r re)) :
    ∀ (rs : List TableRow),
      (∀ r ∈ rs, CellsWf prog r.cells cols) →
      match evalDeriveMapRows evalRE cols item (lookupColIdx? cols (deriveItemName item)) rs with
      | .ok rowTuples =>
        ∀ nr ∈ rowTuples.filterMap (fun | .tuple cs => some ({ cells := cs, groupMeta := none } : TableRow) | _ => none),
          CellsWf prog nr.cells nextCols
      | .stopped _ => True
      | .outOfFuel => True
      | .wrong => False := by
  intro rs hrs
  let itemName := deriveItemName item
  have hCell : ∀ r, CellsWf prog r.cells cols →
      ∃ newCol : ColSpec,
        newCol.name = itemName ∧
        nextCols = (if (cols.find? (fun c => c.name == itemName)).isSome then
            cols.map (fun c => if c.name == itemName then newCol else c)
          else cols ++ [newCol]) ∧
        PrimResultWf prog newCol.ty.toTy (evalDeriveCell evalRE cols r item) := by
    intro r hrCells
    cases item with
    | colExpr name re =>
      unfold applyDeriveItem at happly; simp only [bind, Except.bind] at happly
      cases hre : checkRowExpr prog tEnv cols re with
      | error _ => simp [hre] at happly
      | ok pair =>
        rcases pair with ⟨sTy, rTags⟩
        simp only [hre] at happly
        refine ⟨{ name := name, ty := sTy, tags := rTags, bucketed := false, aggKind := .raw }, rfl, ?_, ?_⟩
        · dsimp only [itemName, deriveItemName]
          split at happly <;> simp_all
        · exact hreSound r re sTy rTags hrCells hre
    | bucketCol name src cuts labels =>
      unfold applyDeriveItem at happly
      cases hs : cols.find? (fun c => c.name == src) with
      | none => simp [hs] at happly
      | some srcCol =>
        simp only [hs] at happly
        cases hb : checkBucketCuts prog srcCol.ty cuts labels
        · simp [hb] at happly
        · simp only [hb, ↓reduceIte] at happly
          rcases lookupColIdx?_of_find? hs with ⟨sIdx, hlookSrc, hgetSrc⟩
          rcases hrCells.getElem?_wf hgetSrc with ⟨sVal, hsVal, _⟩
          rcases evalBucketCell_sound sVal hb with ⟨bVal, hbVal, hbWf⟩
          refine ⟨{ name := name, ty := .text, tags := srcCol.tags, bucketed := true, aggKind := .raw }, rfl, ?_, ?_⟩
          · dsimp only [itemName, deriveItemName]
            split at happly <;> simp_all
          · simp only [evalDeriveCell, hlookSrc, hsVal, hbVal]; exact .ok hbWf
  induction rs with
  | nil => intro _ hm; nomatch hm
  | cons r rest ih =>
    have hrCells := hrs r (.head _)
    rcases hCell r hrCells with ⟨newCol, hnameEq, hnextEq, hprimWf⟩
    unfold evalDeriveMapRows
    cases hcr : evalDeriveCell evalRE cols r item with
    | stopped _ => trivial
    | outOfFuel => trivial
    | wrong => rw [hcr] at hprimWf; nomatch hprimWf
    | ok newCell =>
      rw [hcr] at hprimWf
      dsimp only
      cases hprimWf with | ok hcellWf =>
      have hUpdated : CellsWf prog
          (match lookupColIdx? cols (deriveItemName item) with
           | some (idx, _) => r.cells.set idx newCell
           | none => r.cells ++ [newCell]) nextCols := by
        change CellsWf prog
          (match lookupColIdx? cols itemName with
           | some (idx, _) => r.cells.set idx newCell
           | none => r.cells ++ [newCell]) nextCols
        rw [hnextEq, ← hnameEq]
        cases hlook : lookupColIdx? cols newCol.name with
        | none =>
          have hfNone := (lookupColIdx?_none_iff_find?_none cols newCol.name).mp hlook
          simp only [hfNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          exact hrCells.append (.cons hcellWf .nil)
        | some pair =>
          rcases pair with ⟨idx, origC⟩
          have hfSome : (cols.find? (fun c => c.name == newCol.name)).isSome = true := by
            cases hf : cols.find? (fun c => c.name == newCol.name) with
            | some _ => rfl
            | none =>
              have := (lookupColIdx?_none_iff_find?_none cols newCol.name).mpr hf
              rw [hlook] at this; nomatch this
          simp only [hfSome, ↓reduceIte]
          apply cellsWf_set_by_name (fun c => if c.name == newCol.name then newCol else c) huniq hlook hrCells
          intro c _
          split
          · exact hcellWf
          · rfl
      have ihRest := ih (fun r' hr' => hrs r' (.tail _ hr'))
      cases hrec : evalDeriveMapRows evalRE cols item (lookupColIdx? cols (deriveItemName item)) rest with
      | stopped _ => trivial
      | outOfFuel => trivial
      | wrong => rw [hrec] at ihRest; exact ihRest
      | ok restTuples =>
        rw [hrec] at ihRest
        dsimp only at ihRest ⊢
        intro nr hnr
        simp only [List.filterMap_cons, List.mem_cons] at hnr
        rcases hnr with rfl | htl
        · exact hUpdated
        · exact ihRest nr htl

theorem rawTableSchemaWf_of_props {prog : Program} {cols : List ColSpec} (rt ot : TagSet)
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) :
    TableSchemaWf prog {
      cols := cols, rowTags := rt, orderTags := ot,
      groupedBy := none, summarized := false, distinctBy := none
    } = true := by
  simp only [TableSchemaWf, Option.getD_none, huniq, Bool.true_and, Bool.and_true, List.all_eq_true]
  intro c hc
  rcases hcols c hc with ⟨hv, hb, hraw⟩
  simp only [hv, hraw, Bool.true_and, Bool.and_eq_true]
  refine ⟨?_, by simp⟩
  cases hbk : c.bucketed <;> simp [hbk, hb]

theorem applyDeriveItem_raw {prog : Program} {tEnv : TyEnv} {cols nextCols : List ColSpec}
    {item : DeriveItem}
    (hraw : ∀ c ∈ cols, c.aggKind = .raw)
    (happly : applyDeriveItem prog tEnv cols item = .ok nextCols) :
    ∀ c ∈ nextCols, c.aggKind = .raw := by
  intro c hc
  cases item with
  | colExpr name re =>
    unfold applyDeriveItem at happly; simp only [bind, Except.bind] at happly
    cases hre : checkRowExpr prog tEnv cols re with
    | error _ => simp [hre] at happly
    | ok pair =>
      simp only [hre] at happly
      cases ex : (cols.find? (fun x => x.name == name)).isSome
      · simp only [ex, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happly
        subst happly
        rw [List.mem_append] at hc; rcases hc with hl | hr
        · exact hraw c hl
        · simp at hr; subst hr; rfl
      · simp only [ex, ↓reduceIte, Except.ok.injEq] at happly
        subst happly
        rw [List.mem_map] at hc; rcases hc with ⟨orig, horig, rfl⟩
        split; rfl; exact hraw orig horig
  | bucketCol name src cuts labels =>
    unfold applyDeriveItem at happly
    cases hs : cols.find? (fun x => x.name == src) with
    | none => simp [hs] at happly
    | some srcCol =>
      simp only [hs] at happly
      cases hb : checkBucketCuts prog srcCol.ty cuts labels
      · simp [hb] at happly
      · simp only [hb, ↓reduceIte] at happly
        cases ex : (cols.find? (fun x => x.name == name)).isSome
        · simp only [ex, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happly
          subst happly
          rw [List.mem_append] at hc; rcases hc with hl | hr
          · exact hraw c hl
          · simp at hr; subst hr; rfl
        · simp only [ex, ↓reduceIte, Except.ok.injEq] at happly
          subst happly
          rw [List.mem_map] at hc; rcases hc with ⟨orig, horig, rfl⟩
          split; rfl; exact hraw orig horig

theorem evalDeriveItems_sound {prog : Program} {tEnv : TyEnv}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (w : World) (hw : WorldWf prog w)
    (hreSound : ∀ cols r re sTy rTags,
      distinctIdents (cols.map ColSpec.name) = true →
      (∀ c ∈ cols, validScalarTy prog c.ty = true) →
      CellsWf prog r.cells cols →
      checkRowExpr prog tEnv cols re = .ok (sTy, rTags) →
      PrimResultWf prog sTy.toTy (evalRE cols r re)) :
    ∀ (items : List DeriveItem) (curTV : TableVal) (outCols : List ColSpec) (rt ot : TagSet),
      distinctIdents (curTV.cols.map ColSpec.name) = true →
      (∀ c ∈ curTV.cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
      RowsWf prog curTV.rows curTV.cols false false →
      applyDeriveItems prog tEnv curTV.cols items = .ok outCols →
      OutcomeWf prog [] (.table {
        cols := outCols, rowTags := rt, orderTags := ot,
        groupedBy := none, summarized := false, distinctBy := none
      }) (evalDeriveItems prog tEnv evalRE w curTV items)
  | [], curTV, outCols, rt, ot, huniq, hcols, hrows, happly => by
    unfold applyDeriveItems at happly; injection happly with heq; subst heq
    exact .ok (.table rfl (rawTableSchemaWf_of_props rt ot huniq hcols) hrows) hw
  | item :: rest, curTV, outCols, rt, ot, huniq, hcols, hrows, happly => by
    unfold applyDeriveItems at happly; simp only [bind, Except.bind] at happly
    unfold evalDeriveItems
    cases hstep : applyDeriveItem prog tEnv curTV.cols item with
    | error _ => simp [hstep] at happly
    | ok nextCols =>
      simp only [hstep] at happly ⊢
      have hlookEq : deriveItemTargetName item = deriveItemName item := by
        cases item <;> rfl
      rw [hlookEq]
      rcases applyDeriveItem_props huniq (fun c hc => ⟨(hcols c hc).1, (hcols c hc).2.1⟩) hstep with ⟨hnextUniq, hnextProps⟩
      have hnextRaw := applyDeriveItem_raw (fun c hc => (hcols c hc).2.2) hstep
      have hmap := evalDeriveMapRows_sound evalRE huniq hstep
        (fun r re sTy rTags hr hre => hreSound curTV.cols r re sTy rTags huniq (fun c hc => (hcols c hc).1) hr hre)
        curTV.rows hrows.to_forall
      cases hm : evalDeriveMapRows evalRE curTV.cols item
          (lookupColIdx? curTV.cols (deriveItemName item)) curTV.rows with
      | stopped b => exact .stopped b hw
      | outOfFuel => exact .outOfFuel
      | wrong => rw [hm] at hmap; nomatch hmap
      | ok rowTuples =>
        rw [hm] at hmap
        dsimp only at hmap ⊢
        exact evalDeriveItems_sound evalRE w hw hreSound rest _ outCols rt ot hnextUniq
          (fun c hc => ⟨(hnextProps c hc).1, (hnextProps c hc).2, hnextRaw c hc⟩)
          (RowsWf.of_forall_raw hmap) happly

theorem evalFilterRows_sound {prog : Program} {tEnv : TyEnv}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    {inCols : List ColSpec} {pred : RowExpr} {pTags : TagSet} (rt ot : TagSet)
    (w : World) (hw : WorldWf prog w)
    (huniq : distinctIdents (inCols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ inCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text))
    (hpred : checkRowExpr prog tEnv inCols pred = .ok (.bool, pTags))
    (hreSound : ∀ r, CellsWf prog r.cells inCols → PrimResultWf prog .bool (evalRE inCols r pred)) :
    ∀ (rs : List TableRow),
      (∀ r ∈ rs, CellsWf prog r.cells inCols) →
      OutcomeWf prog [] (.table {
        cols := inCols.map (fun c => { c with aggKind := .raw }),
        rowTags := rt, orderTags := ot, groupedBy := none, summarized := false, distinctBy := none
      }) (evalFilterRows evalRE inCols (inCols.map (fun c => { c with aggKind := .raw })) pred w rs)
  | [], _ =>
    .ok (.table rfl (resetRawTableSchemaWf huniq hcols rt ot) (.nil _ false false)) hw
  | r :: rs, hrs => by
    unfold evalFilterRows
    have hrWf := hreSound r (hrs r (.head _))
    cases hre : evalRE inCols r pred with
    | stopped b => exact .stopped b hw
    | outOfFuel => exact .outOfFuel
    | wrong => rw [hre] at hrWf; nomatch hrWf
    | ok pv =>
      rw [hre] at hrWf
      cases hrWf with | ok hpv =>
      cases hpv with | bool keep =>
      have ih := evalFilterRows_sound evalRE rt ot w hw huniq hcols hpred hreSound rs
        (fun r' hr' => hrs r' (.tail _ hr'))
      cases hrec : evalFilterRows evalRE inCols (inCols.map (fun c => { c with aggKind := .raw })) pred w rs with
      | stopped b w' => rw [hrec] at ih; exact ih
      | failed m w' => rw [hrec] at ih; exact ih
      | outOfFuel => exact .outOfFuel
      | jumped _ _ _ => rw [hrec] at ih; exact ih
      | wrong => rw [hrec] at ih; nomatch ih
      | ok resVal w' =>
        rw [hrec] at ih
        cases ih with | ok hresWf _ =>
        cases hresWf with | @table restTV _ hrestCols hschema hrestRows =>
        apply OutcomeWf.ok _ hw
        apply ValWf.table rfl hschema
        have hrOut : CellsWf prog r.cells (inCols.map (fun c => { c with aggKind := .raw })) :=
          (hrs r (.head _)).congr_ty (map_ty_with_aggKind inCols .raw).symm
        cases keep
        · exact hrestRows
        · exact .cons hrOut (fun h => by simp at h) hrestRows

theorem lookupColIdx?_snd_eq_find? (cols : List ColSpec) (name : Ident) :
    (lookupColIdx? cols name).map Prod.snd = cols.find? (fun c => c.name == name) := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    rw [lookupColIdx?_cons]
    simp only [List.find?]
    cases hc : (c.name == name)
    · simp only [Bool.false_eq_true, ↓reduceIte, ← ih]
      cases lookupColIdx? cs name <;> rfl
    · simp [↓reduceIte]

theorem projectRowsByIndices_pick_sound {prog : Program} {inCols : List ColSpec} {r : TableRow}
    (hr : CellsWf prog r.cells inCols) :
    ∀ (idxCols : List (Nat × ColSpec)),
      (∀ ic ∈ idxCols, inCols[ic.1]? = some ic.2) →
      ∃ cs, projectRowsByIndices.pick r (idxCols.map Prod.fst) = some cs ∧
        CellsWf prog cs (idxCols.map (fun (_, c) => { c with aggKind := .raw }))
  | [], _ => ⟨[], rfl, .nil⟩
  | (idx, cSpec) :: rest, hall => by
    rcases hr.getElem?_wf (hall (idx, cSpec) (.head _)) with ⟨cell, hget, hcellWf⟩
    rcases projectRowsByIndices_pick_sound hr rest (fun x hx => hall x (.tail _ hx)) with ⟨tlCs, htlPick, htlWf⟩
    exact ⟨cell :: tlCs, by simp [projectRowsByIndices.pick, hget, htlPick], .cons hcellWf htlWf⟩

theorem projectRowsByIndices_sound {prog : Program} {inCols : List ColSpec}
    (idxCols : List (Nat × ColSpec))
    (hallIdx : ∀ ic ∈ idxCols, inCols[ic.1]? = some ic.2) :
    ∀ (rows : List TableRow),
      (∀ r ∈ rows, CellsWf prog r.cells inCols) →
      ∃ outRows, projectRowsByIndices (idxCols.map Prod.fst) rows = some outRows ∧
        RowsWf prog outRows (idxCols.map (fun (_, c) => { c with aggKind := .raw })) false false
  | [], _ => ⟨[], rfl, .nil _ false false⟩
  | r :: rs, hrs => by
    rcases projectRowsByIndices_pick_sound (hrs r (.head _)) idxCols hallIdx with ⟨cs, hpick, hcsWf⟩
    rcases projectRowsByIndices_sound idxCols hallIdx rs (fun r' hr' => hrs r' (.tail _ hr')) with ⟨tlRows, htlProj, htlRowsWf⟩
    refine ⟨{ cells := cs, groupMeta := none } :: tlRows,
      by simp [projectRowsByIndices, hpick, htlProj],
      .cons hcsWf (fun h => by simp at h) htlRowsWf⟩

theorem select_idxSpecs_props {cols : List ColSpec} :
    ∀ (selCols : List Ident),
      (∀ n ∈ selCols, (cols.find? (fun c => c.name == n)).isSome = true) →
      let idxSpecs := selCols.filterMap (lookupColIdx? cols)
      idxSpecs.length = selCols.length ∧
      (∀ ic ∈ idxSpecs, cols[ic.1]? = some ic.2) ∧
      idxSpecs.map (fun (_, c) => { c with aggKind := .raw }) =
        selCols.filterMap (fun n => (cols.find? (fun c => c.name == n)).map (fun c => { c with aggKind := .raw })) ∧
      (idxSpecs.map (fun (_, c) => { c with aggKind := .raw })).map ColSpec.name = selCols
  | [], _ => ⟨rfl, (fun _ hm => nomatch hm), rfl, rfl⟩
  | n :: ns, hex => by
    have hnSome := hex n (.head _)
    rw [Option.isSome_iff_exists] at hnSome
    rcases hnSome with ⟨cSpec, hfind⟩
    have hsnd := lookupColIdx?_snd_eq_find? cols n
    rw [hfind] at hsnd
    cases hlook : lookupColIdx? cols n with
    | none => rw [hlook] at hsnd; nomatch hsnd
    | some pair =>
      rcases pair with ⟨idx, cFound⟩
      rw [hlook] at hsnd; simp only [Option.map_some, Option.some.injEq] at hsnd; subst hsnd
      rcases lookupColIdx?_props hlook with ⟨hget, hname⟩
      rcases select_idxSpecs_props ns (fun m hm => hex m (.tail _ hm)) with ⟨hlen, hall, hcolsEq, hnamesEq⟩
      simp only [List.filterMap_cons, hlook, hfind, Option.map_some, List.length_cons, List.map_cons]
      refine ⟨congrArg (· + 1) hlen, ?_, congrArg (_ :: ·) hcolsEq, ?_⟩
      · intro ic hic
        rcases List.mem_cons.mp hic with rfl | hrest
        · exact hget
        · exact hall ic hrest
      · rw [hname, hnamesEq]

theorem zipIdx_props_aux :
    ∀ (k : Nat) (cs : List ColSpec),
      (cs.zipIdx k).map Prod.fst = cs ∧
      ∀ p ∈ cs.zipIdx k, k ≤ p.2 ∧ cs[p.2 - k]? = some p.1
  | _, [] => ⟨rfl, fun _ hm => nomatch hm⟩
  | k, c :: cs => by
    rcases zipIdx_props_aux (k + 1) cs with ⟨hfst, hget⟩
    simp only [List.zipIdx_cons, List.map_cons]
    refine ⟨congrArg (c :: ·) hfst, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | htl
    · simp
    · rcases hget p htl with ⟨hle, hsub⟩
      refine ⟨by omega, ?_⟩
      have heq : p.2 - k = (p.2 - (k + 1)) + 1 := by omega
      rw [heq]; simpa using hsub

theorem zipIdx_filter_props (p : ColSpec → Bool) (cols : List ColSpec) :
    let kept := cols.zipIdx.filter (fun (c, _) => p c)
    kept.map (fun (c, _) => c) = cols.filter p ∧
    ∀ pair ∈ kept, cols[pair.2]? = some pair.1 := by
  have h0 := zipIdx_props_aux 0 cols
  refine ⟨?_, ?_⟩
  · have haux : ∀ (k : Nat) (cs : List ColSpec),
        ((cs.zipIdx k).filter (fun (c, _) => p c)).map Prod.fst = cs.filter p := by
      intro k cs
      induction cs generalizing k with
      | nil => rfl
      | cons c rest ih =>
        simp only [List.zipIdx_cons, List.filter_cons]
        cases p c <;> simp [ih (k + 1)]
    exact haux 0 cols
  · intro pair hpair
    have hmem := (List.mem_filter.mp hpair).1
    rcases h0.2 pair hmem with ⟨_, hget⟩
    simpa using hget

theorem extractKeyVals_some {prog : Program} {cols : List ColSpec} {r : TableRow}
    (hr : CellsWf prog r.cells cols) :
    ∀ (keyNames : List Ident),
      (∀ k ∈ keyNames, (cols.find? (fun c => c.name == k)).isSome = true) →
      ∃ kv, extractKeyVals cols keyNames r = some kv
  | [], _ => ⟨[], rfl⟩
  | k :: ks, hall => by
    have hk := hall k (.head _)
    rw [Option.isSome_iff_exists] at hk
    rcases hk with ⟨c, hfind⟩
    rcases lookupColIdx?_of_find? hfind with ⟨idx, hlook, hgetCol⟩
    rcases hr.getElem?_wf hgetCol with ⟨cell, hgetCell, _⟩
    rcases extractKeyVals_some hr ks (fun m hm => hall m (.tail _ hm)) with ⟨tl, htl⟩
    refine ⟨cell :: tl, ?_⟩
    unfold extractKeyVals at htl ⊢
    unfold extractKeyVals.go
    simp only [hlook, hgetCell, htl, bind, Option.bind]

theorem extractKeyVals_typed {prog : Program} {cols : List ColSpec} {r : TableRow}
    (hr : CellsWf prog r.cells cols) :
    ∀ (keyCols : List ColSpec),
      (∀ kc ∈ keyCols, ∃ origC, cols.find? (fun c => c.name == kc.name) = some origC ∧ origC.ty = kc.ty) →
      ∃ kv, extractKeyVals cols (keyCols.map ColSpec.name) r = some kv ∧ CellsWf prog kv keyCols
  | [], _ => ⟨[], rfl, .nil⟩
  | kc :: kcs, hall => by
    rcases hall kc (.head _) with ⟨origC, hfind, htyEq⟩
    have hsnd := lookupColIdx?_snd_eq_find? cols kc.name
    rw [hfind] at hsnd
    cases hlook : lookupColIdx? cols kc.name with
    | none => rw [hlook] at hsnd; nomatch hsnd
    | some pair =>
      rcases pair with ⟨idx, cFound⟩
      rw [hlook] at hsnd; simp only [Option.map_some, Option.some.injEq] at hsnd; subst hsnd
      rcases lookupColIdx?_props hlook with ⟨hgetCol, _⟩
      rcases hr.getElem?_wf hgetCol with ⟨cell, hgetCell, hcellWf⟩
      rcases extractKeyVals_typed hr kcs (fun x hx => hall x (.tail _ hx)) with ⟨tl, htlEq, htlWf⟩
      refine ⟨cell :: tl, ?_, .cons (htyEq ▸ hcellWf) htlWf⟩
      unfold extractKeyVals at htlEq ⊢
      simp only [List.map_cons]
      unfold extractKeyVals.go
      simp only [hlook, hgetCell, htlEq, bind, Option.bind]

theorem extractAllRowsKeyVals_typed {prog : Program} {cols keyCols : List ColSpec}
    (hallKey : ∀ kc ∈ keyCols, ∃ origC, cols.find? (fun c => c.name == kc.name) = some origC ∧ origC.ty = kc.ty) :
    ∀ (rows : List TableRow),
      (∀ r ∈ rows, CellsWf prog r.cells cols) →
      ∃ kvs, extractAllRowsKeyVals cols (keyCols.map ColSpec.name) rows = some kvs ∧
        ∀ kv ∈ kvs, CellsWf prog kv keyCols
  | [], _ => ⟨[], rfl, fun _ hm => nomatch hm⟩
  | r :: rs, hrs => by
    rcases extractKeyVals_typed (hrs r (.head _)) keyCols hallKey with ⟨kv, hkv, hkvWf⟩
    rcases extractAllRowsKeyVals_typed hallKey rs (fun r' hr' => hrs r' (.tail _ hr')) with ⟨tl, htl, htlWf⟩
    refine ⟨kv :: tl, by simp [extractAllRowsKeyVals, hkv, htl], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact hkvWf
    · exact htlWf x hrest

theorem dedupTableRows_sound {prog : Program} {cols outCols : List ColSpec} {keyNames : List Ident}
    (hty : cols.map ColSpec.ty = outCols.map ColSpec.ty)
    (hkeys : ∀ k ∈ keyNames, (cols.find? (fun c => c.name == k)).isSome = true) :
    ∀ (seen : List (List Val)) (rows : List TableRow),
      (∀ r ∈ rows, CellsWf prog r.cells cols) →
      ∃ outRows, dedupTableRows cols keyNames seen rows = some outRows ∧
        RowsWf prog outRows outCols false false
  | _, [], _ => ⟨[], rfl, .nil _ false false⟩
  | seen, r :: rs, hrs => by
    rcases extractKeyVals_some (hrs r (.head _)) keyNames hkeys with ⟨kv, hkv⟩
    unfold dedupTableRows
    simp only [hkv, bind, Option.bind]
    cases seen.any (fun sk => valListEq sk kv)
    · rcases dedupTableRows_sound hty hkeys (kv :: seen) rs (fun r' hr' => hrs r' (.tail _ hr')) with ⟨tl, htl, htlWf⟩
      refine ⟨{ r with groupMeta := none } :: tl, by simp [htl],
        .cons ((hrs r (.head _)).congr_ty hty) (fun h => by simp at h) htlWf⟩
    · exact dedupTableRows_sound hty hkeys seen rs (fun r' hr' => hrs r' (.tail _ hr'))

theorem nonNull_wf {prog : Program} {sTy : ScalarTy} {rawVals : List Val}
    (hval : validScalarTy prog sTy = true)
    (hraw : ∀ v ∈ rawVals, ValWf prog v sTy.toTy) :
    ∀ u ∈ rawVals.filterMap (fun v =>
      match v with
      | .optNone => none
      | .optSome inner => some inner
      | other => some other),
      ValWf prog u (baseOfScalar sTy).toTy := by
  intro u hu
  rw [List.mem_filterMap] at hu
  rcases hu with ⟨v, hvMem, hvMap⟩
  have hvWf := hraw v hvMem
  cases sTy with
  | option inner =>
    simp only [validScalarTy, Bool.and_eq_true, Bool.not_eq_true'] at hval
    dsimp only [ScalarTy.toTy, baseOfScalar] at hvWf ⊢
    cases hvWf with
    | optNone => simp at hvMap
    | optSome hinner => injection hvMap with heq; subst heq; exact hinner
  | unit | bool | int | decimal | float | text | bytes | date | timestamp | duration | data _ =>
    dsimp only [ScalarTy.toTy, baseOfScalar] at hvWf ⊢
    cases hvWf <;> (injection hvMap with heq; subst heq; constructor <;> assumption)

theorem sumSortedInts_sound {prog : Program} :
    ∀ (xs : List Val), (∀ u ∈ xs, ValWf prog u .int) → PrimResultWf prog .int (sumSortedInts xs)
  | [], _ => .ok (.int (by decide))
  | x :: xs, hxs => by
    have hx := hxs x (.head _)
    cases hx with | int _ =>
    have ih := sumSortedInts_sound xs (fun u hu => hxs u (.tail _ hu))
    unfold sumSortedInts
    cases hs : sumSortedInts xs with
    | stopped b => exact .stopped b
    | outOfFuel => exact .outOfFuel
    | wrong => rw [hs] at ih; nomatch ih
    | ok rv =>
      rw [hs] at ih
      cases ih with | ok hrv =>
      cases hrv with | int _ =>
      exact checkedInt_sound _

theorem sumSortedDecimals_sound {prog : Program} :
    ∀ (xs : List Val), (∀ u ∈ xs, ValWf prog u .decimal) → PrimResultWf prog .decimal (sumSortedDecimals xs)
  | [], _ => .ok (.decimal (by decide))
  | x :: xs, hxs => by
    have hx := hxs x (.head _)
    cases hx with | decimal _ =>
    have ih := sumSortedDecimals_sound xs (fun u hu => hxs u (.tail _ hu))
    unfold sumSortedDecimals
    cases hs : sumSortedDecimals xs with
    | stopped b => exact .stopped b
    | outOfFuel => exact .outOfFuel
    | wrong => rw [hs] at ih; nomatch ih
    | ok rv =>
      rw [hs] at ih
      cases ih with | ok hrv =>
      cases hrv with | decimal _ =>
      exact checkedDecimal_sound _

theorem ensureOptionScalar_eq_option_base {prog : Program} {sTy : ScalarTy}
    (h : validScalarTy prog sTy = true) :
    ensureOptionScalar sTy = .option (baseOfScalar sTy) ∧
    validScalarTy prog (ensureOptionScalar sTy) = true := by
  cases sTy with
  | option inner =>
    exact ⟨rfl, h⟩
  | data name =>
    exact ⟨rfl, h⟩
  | _ =>
    exact ⟨rfl, rfl⟩

theorem wrapIntoOptionVal_sound {prog : Program} {sTy : ScalarTy} {v : Val}
    (hs : validScalarTy prog sTy = true)
    (hv : ValWf prog v sTy.toTy) :
    ValWf prog (wrapIntoOptionVal sTy v) (ensureOptionScalar sTy).toTy := by
  cases sTy with
  | option inner => exact hv
  | _ =>
    have _ := hs
    exact .optSome hv

theorem optNone_ensureOption_sound {prog : Program} (sTy : ScalarTy) :
    ValWf prog .optNone (ensureOptionScalar sTy).toTy := by
  cases sTy <;> exact .optNone _

theorem numericCoreOfScalar?_props {sTy nTy : ScalarTy}
    (hn : numericCoreOfScalar? sTy = some nTy) :
    baseOfScalar sTy = nTy ∧ (nTy = .int ∨ nTy = .decimal ∨ nTy = .float) := by
  cases sTy <;> try contradiction
  case int => injection hn with h; subst h; exact ⟨rfl, Or.inl rfl⟩
  case decimal => injection hn with h; subst h; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  case float => injection hn with h; subst h; exact ⟨rfl, Or.inr (Or.inr rfl)⟩
  case option inner =>
    cases inner <;> try contradiction
    case int => injection hn with h; subst h; exact ⟨rfl, Or.inl rfl⟩
    case decimal => injection hn with h; subst h; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    case float => injection hn with h; subst h; exact ⟨rfl, Or.inr (Or.inr rfl)⟩

theorem checkAggItem_props {prog : Program} {tEnv : TyEnv} {inTT : TableTy}
    {item : AggItem} {cSpec : ColSpec}
    (hcols : ∀ c ∈ inTT.cols, validScalarTy prog c.ty = true)
    (hchk : checkAggItem prog tEnv inTT item = .ok cSpec) :
    validScalarTy prog cSpec.ty = true ∧ cSpec.bucketed = false ∧ cSpec.aggKind ≠ .groupKey := by
  unfold checkAggItem at hchk
  cases hop : item.op <;> cases harg : item.arg <;> simp only [hop, harg, bind, Except.bind] at hchk <;> try contradiction
  · -- count, none
    injection hchk with hc; subst hc; exact ⟨rfl, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- countDistinct, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p => simp only [hre] at hchk; split at hchk <;> try contradiction
              injection hchk with hc; subst hc; exact ⟨rfl, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- sum, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre] at hchk
      cases hn : numericCoreOfScalar? p.1 with
      | none => simp [hn] at hchk
      | some numTy =>
        simp only [hn, Except.ok.injEq] at hchk; subst hchk
        refine ⟨?_, rfl, by dsimp only [AggOp.isBlending]; decide⟩
        rcases (numericCoreOfScalar?_props hn).2 with rfl | rfl | rfl <;> rfl
  · -- mean, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre] at hchk
      cases hn : numericCoreOfScalar? p.1 with
      | none => simp [hn] at hchk
      | some numTy =>
        simp only [hn] at hchk
        rcases (numericCoreOfScalar?_props hn).2 with rfl | rfl | rfl <;>
          (injection hchk with hc; subst hc; exact ⟨rfl, rfl, by dsimp only [AggOp.isBlending]; decide⟩)
  · -- stddev, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p => simp only [hre] at hchk; split at hchk <;> try contradiction
              injection hchk with hc; subst hc; exact ⟨rfl, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- variance, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p => simp only [hre] at hchk; split at hchk <;> try contradiction
              injection hchk with hc; subst hc; exact ⟨rfl, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- median, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre] at hchk
      cases hn : numericCoreOfScalar? p.1 with
      | none => simp [hn] at hchk
      | some numTy =>
        simp only [hn] at hchk
        rcases (numericCoreOfScalar?_props hn).2 with rfl | rfl | rfl <;>
          (injection hchk with hc; subst hc; exact ⟨rfl, rfl, by dsimp only [AggOp.isBlending]; decide⟩)
  · -- percentile, some re
    rename_i _ re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre] at hchk
      split at hchk <;> try contradiction
      split at hchk <;> try contradiction
      injection hchk with hc; subst hc; exact ⟨rfl, rfl, by simp [AggOp.isBlending]⟩
  · -- min, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      have hsv := checkRowExpr_validScalarTy hcols hre
      exact ⟨(ensureOptionScalar_eq_option_base hsv).1 ▸ (ensureOptionScalar_eq_option_base hsv).2, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- max, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      have hsv := checkRowExpr_validScalarTy hcols hre
      exact ⟨(ensureOptionScalar_eq_option_base hsv).1 ▸ (ensureOptionScalar_eq_option_base hsv).2, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- first, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre, Except.ok.injEq] at hchk; subst hchk
      have hsv := checkRowExpr_validScalarTy hcols hre
      exact ⟨(ensureOptionScalar_eq_option_base hsv).2, rfl, by dsimp only [AggOp.isBlending]; decide⟩
  · -- last, some re
    rename_i re
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      simp only [hre, Except.ok.injEq] at hchk; subst hchk
      have hsv := checkRowExpr_validScalarTy hcols hre
      exact ⟨(ensureOptionScalar_eq_option_base hsv).2, rfl, by dsimp only [AggOp.isBlending]; decide⟩

theorem mem_of_head?_eq_some {α : Type} : ∀ {xs : List α} {x : α}, xs.head? = some x → x ∈ xs
  | _ :: _, _, h => by injection h with h'; subst h'; exact .head _

theorem mem_of_getLast?_eq_some {α : Type} : ∀ {xs : List α} {x : α}, xs.getLast? = some x → x ∈ xs
  | [a], _, h => by injection h with h'; subst h'; exact .head _
  | _ :: b :: bs, _, h => .tail _ (mem_of_getLast?_eq_some (xs := b :: bs) h)

theorem evalAggClean_sound {prog : Program} {op : AggOp} {sTy outTy : ScalarTy} {rawVals : List Val}
    (hval : validScalarTy prog sTy = true)
    (hraw : ∀ v ∈ rawVals, ValWf prog v sTy.toTy)
    (hop :
      (op = .count ∧ outTy = .int) ∨
      (op = .countDistinct ∧ outTy = .int) ∨
      (op = .sum ∧ numericCoreOfScalar? sTy = some outTy) ∨
      ((op = .mean ∨ op = .median) ∧
        match numericCoreOfScalar? sTy with
        | some .int => outTy = .option .float
        | some nTy => outTy = .option nTy
        | none => False) ∨
      ((op = .stddev ∨ op = .variance ∨ ∃ p, op = .percentile p) ∧ outTy = .option .float) ∨
      ((op = .min ∨ op = .max) ∧ outTy = .option (baseOfScalar sTy)) ∨
      ((op = .first ∨ op = .last) ∧ outTy = ensureOptionScalar sTy)) :
    PrimResultWf prog outTy.toTy (evalAggClean op outTy rawVals) := by
  have hnn := nonNull_wf hval hraw
  have hsorted : ∀ u ∈ insertionSortBy valLt (rawVals.filterMap (fun v =>
      match v with | .optNone => none | .optSome inner => some inner | other => some other)),
      ValWf prog u (baseOfScalar sTy).toTy :=
    fun u hu => hnn u (mem_insertionSortBy valLt u _ hu)
  have hCore : ∀ {nTy : ScalarTy}, numericCoreOfScalar? sTy = some nTy → baseOfScalar sTy = nTy ∧
      (nTy = .int ∨ nTy = .decimal ∨ nTy = .float) := fun hn => numericCoreOfScalar?_props hn
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hsum⟩ | ⟨hmed, hmmTy⟩ | ⟨hstat, rfl⟩ | ⟨hminMax, rfl⟩ | ⟨hfirstLast, rfl⟩
  · exact checkedInt_sound _
  · exact checkedInt_sound _
  · rcases hCore hsum with ⟨hbase, hcases⟩
    rw [hbase] at hsorted
    unfold evalAggClean
    rcases hcases with rfl | rfl | rfl
    · exact sumSortedInts_sound _ hsorted
    · exact sumSortedDecimals_sound _ hsorted
    · exact .ok (.float _)
  · cases hn : numericCoreOfScalar? sTy with
    | none => rw [hn] at hmmTy; exact False.elim hmmTy
    | some nTy =>
      rw [hn] at hmmTy
      rcases hCore hn with ⟨hbase, hcases⟩
      rw [hbase] at hsorted
      rcases hmed with rfl | rfl
      · -- mean
        unfold evalAggClean
        simp only
        generalize hsortEq : insertionSortBy valLt (rawVals.filterMap (fun v =>
          match v with | .optNone => none | .optSome inner => some inner | other => some other)) = sorted at hsorted ⊢
        split
        · rcases hcases with rfl | rfl | rfl <;> (subst hmmTy; exact .ok (.optNone _))
        · rcases hcases with rfl | rfl | rfl
          · subst hmmTy; exact .ok (.optSome (.float _))
          · subst hmmTy
            have hds := sumSortedDecimals_sound sorted hsorted
            cases hs : sumSortedDecimals sorted with
            | stopped b => exact .stopped b
            | outOfFuel => exact .outOfFuel
            | wrong => rw [hs] at hds; nomatch hds
            | ok tv =>
              rw [hs] at hds; cases hds with | ok htv => cases htv with | decimal _ =>
              simp only
              cases havg : inDecimalRange _
              · simp only [Bool.false_eq_true, ↓reduceIte]; exact .stopped _
              · simp only [↓reduceIte]; exact .ok (.optSome (.decimal havg))
          · subst hmmTy; exact .ok (.optSome (.float _))
      · -- median
        unfold evalAggClean
        simp only
        generalize hsortEq : insertionSortBy valLt (rawVals.filterMap (fun v =>
          match v with | .optNone => none | .optSome inner => some inner | other => some other)) = sorted at hsorted ⊢
        cases hemp : sorted.isEmpty
        · have hne : sorted.length > 0 := by
            cases sorted with
            | nil => simp at hemp
            | cons _ _ => simp
          have hdivLt : sorted.length / 2 < sorted.length := Nat.div_lt_self hne (by decide)
          have hgetEx : ∃ midV, sorted[sorted.length / 2]? = some midV :=
            ⟨sorted[sorted.length / 2], List.getElem?_eq_getElem hdivLt⟩
          rcases hgetEx with ⟨midV, hmidEq⟩
          have hmMem : midV ∈ sorted := List.mem_of_getElem? hmidEq
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hcases with rfl | rfl | rfl
          · subst hmmTy; exact .ok (.optSome (.float _))
          · subst hmmTy
            cases hmod : (sorted.length % 2 == 1)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hge2 : sorted.length ≥ 2 := by
                have hne1 : sorted.length % 2 ≠ 1 := by simpa using hmod
                omega
              have hloLt : sorted.length / 2 - 1 < sorted.length := by omega
              have hloEq : ∃ loV, sorted[sorted.length / 2 - 1]? = some loV :=
                ⟨sorted[sorted.length / 2 - 1], List.getElem?_eq_getElem hloLt⟩
              rcases hloEq with ⟨loV, hloEq⟩
              have hloMem : loV ∈ sorted := List.mem_of_getElem? hloEq
              have hloWf := hsorted loV hloMem
              have hmidWf := hsorted midV hmMem
              cases hloWf with | decimal _ =>
              cases hmidWf with | decimal _ =>
              rw [hloEq, hmidEq]
              simp only
              cases havg : inDecimalRange _
              · simp only [Bool.false_eq_true, ↓reduceIte]; exact .stopped _
              · simp only [↓reduceIte]; exact .ok (.optSome (.decimal havg))
            · simp only [↓reduceIte, hmidEq]
              cases hsorted midV hmMem with | decimal hr =>
              exact .ok (.optSome (.decimal hr))
          · subst hmmTy; exact .ok (.optSome (.float _))
        · simp only [↓reduceIte]
          rcases hcases with rfl | rfl | rfl <;> (subst hmmTy; exact .ok (.optNone _))
  · rcases hstat with rfl | rfl | ⟨p, rfl⟩
    · unfold evalAggClean; simp only; split
      · exact .ok (.optNone _)
      · exact .ok (.optSome (.float _))
    · unfold evalAggClean; simp only; split
      · exact .ok (.optNone _)
      · exact .ok (.optSome (.float _))
    · unfold evalAggClean; simp only; split
      · exact .ok (.optNone _)
      · exact .ok (.optSome (.float _))
  · rcases hminMax with rfl | rfl
    · unfold evalAggClean; simp only
      cases hh : (insertionSortBy valLt _).head? with
      | none => exact .ok (.optNone _)
      | some v => exact .ok (.optSome (hsorted v (mem_of_head?_eq_some hh)))
    · unfold evalAggClean; simp only
      cases hl : (insertionSortBy valLt _).getLast? with
      | none => exact .ok (.optNone _)
      | some v => exact .ok (.optSome (hsorted v (mem_of_getLast?_eq_some hl)))
  · have heqOpt := (ensureOptionScalar_eq_option_base hval).1
    rcases hfirstLast with rfl | rfl
    · unfold evalAggClean; simp only
      rw [heqOpt]
      cases hh : (rawVals.filterMap _).head? with
      | none => exact .ok (.optNone _)
      | some v => exact .ok (.optSome (hnn v (mem_of_head?_eq_some hh)))
    · unfold evalAggClean; simp only
      rw [heqOpt]
      cases hl : (rawVals.filterMap _).getLast? with
      | none => exact .ok (.optNone _)
      | some v => exact .ok (.optSome (hnn v (mem_of_getLast?_eq_some hl)))

theorem evalArgOnGroupRows_sound {prog : Program}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    {cols : List ColSpec} {re : RowExpr} {sTy : ScalarTy}
    (hreSound : ∀ r, CellsWf prog r.cells cols → PrimResultWf prog sTy.toTy (evalRE cols r re)) :
    ∀ (gRows : List TableRow),
      (∀ r ∈ gRows, CellsWf prog r.cells cols) →
      match evalArgOnGroupRows evalRE cols re gRows with
      | .ok cvs => ∀ v ∈ cvs, ValWf prog v sTy.toTy
      | .stopped _ => True
      | .outOfFuel => True
      | .wrong => False
  | [], _ => fun _ hm => nomatch hm
  | gr :: grs, hgrs => by
    unfold evalArgOnGroupRows
    have hhd := hreSound gr (hgrs gr (.head _))
    cases he : evalRE cols gr re with
    | stopped _ => trivial
    | outOfFuel => trivial
    | wrong => rw [he] at hhd; nomatch hhd
    | ok cv =>
      rw [he] at hhd; cases hhd with | ok hcv =>
      have ih := evalArgOnGroupRows_sound evalRE hreSound grs (fun r hr => hgrs r (.tail _ hr))
      cases htl : evalArgOnGroupRows evalRE cols re grs with
      | stopped _ => trivial
      | outOfFuel => trivial
      | wrong => rw [htl] at ih; exact ih
      | ok cvs =>
        rw [htl] at ih
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hrest
        · exact hcv
        · exact ih v hrest

theorem checkAggItem_op_spec {prog : Program} {tEnv : TyEnv} {inTT : TableTy}
    {aItem : AggItem} {aSpec : ColSpec}
    (hcols : ∀ c ∈ inTT.cols, validScalarTy prog c.ty = true)
    (hchk : checkAggItem prog tEnv inTT aItem = .ok aSpec) :
    (aItem.arg = none ∧ aItem.op = .count ∧ aSpec.ty = .int) ∨
    ∃ re sTy rTags,
      aItem.arg = some re ∧
      checkRowExpr prog tEnv inTT.cols re = .ok (sTy, rTags) ∧
      validScalarTy prog sTy = true ∧
      ((aItem.op = .countDistinct ∧ aSpec.ty = .int) ∨
       (aItem.op = .sum ∧ numericCoreOfScalar? sTy = some aSpec.ty) ∨
       ((aItem.op = .mean ∨ aItem.op = .median) ∧
         match numericCoreOfScalar? sTy with
         | some .int => aSpec.ty = .option .float
         | some nTy => aSpec.ty = .option nTy
         | none => False) ∨
       ((aItem.op = .stddev ∨ aItem.op = .variance ∨ ∃ p, aItem.op = .percentile p) ∧ aSpec.ty = .option .float) ∨
       ((aItem.op = .min ∨ aItem.op = .max) ∧ aSpec.ty = .option (baseOfScalar sTy)) ∨
       ((aItem.op = .first ∨ aItem.op = .last) ∧ aSpec.ty = ensureOptionScalar sTy)) := by
  cases ha : aItem with | mk aName op arg =>
  unfold checkAggItem at hchk
  simp only [ha] at hchk ⊢
  split at hchk
  · injection hchk with hc; subst hc; exact Or.inl ⟨rfl, rfl, rfl⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk
      cases hn : numericCoreOfScalar? sTy with
      | none => simp [hn] at hchk
      | some numTy =>
        simp only [hn, Except.ok.injEq] at hchk; subst hchk
        exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre, Or.inr (Or.inl ⟨rfl, hn⟩)⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk
      have hsv := checkRowExpr_validScalarTy hcols hre
      cases hn : numericCoreOfScalar? sTy with
      | none => simp [hn] at hchk
      | some numTy =>
        simp only [hn] at hchk
        refine Or.inr ⟨re, sTy, rTags, rfl, hre, hsv, Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, ?_⟩))⟩
        rw [hn]
        cases numTy <;> try (injection hchk with hc; subst hc; rfl)
        all_goals (exfalso; cases sTy <;> simp [numericCoreOfScalar?] at hn; case option inner => cases inner <;> simp [numericCoreOfScalar?] at hn)
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk
      have hsv := checkRowExpr_validScalarTy hcols hre
      cases hn : numericCoreOfScalar? sTy with
      | none => simp [hn] at hchk
      | some numTy =>
        simp only [hn] at hchk
        refine Or.inr ⟨re, sTy, rTags, rfl, hre, hsv, Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, ?_⟩))⟩
        rw [hn]
        cases numTy <;> try (injection hchk with hc; subst hc; rfl)
        all_goals (exfalso; cases sTy <;> simp [numericCoreOfScalar?] at hn; case option inner => cases inner <;> simp [numericCoreOfScalar?] at hn)
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), rfl⟩)))⟩
  · rename_i pct re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk
      split at hchk <;> try contradiction
      split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr ⟨pct, rfl⟩), rfl⟩)))⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩))))⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre] at hchk; split at hchk <;> try contradiction
      injection hchk with hc; subst hc
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl⟩))))⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre, Except.ok.injEq] at hchk; subst hchk
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, rfl⟩))))⟩
  · rename_i re
    simp only [bind, Except.bind] at hchk
    cases hre : checkRowExpr prog tEnv inTT.cols re with
    | error _ => simp [hre] at hchk
    | ok p =>
      rcases p with ⟨sTy, rTags⟩; simp only [hre, Except.ok.injEq] at hchk; subst hchk
      exact Or.inr ⟨re, sTy, rTags, rfl, hre, checkRowExpr_validScalarTy hcols hre,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, rfl⟩))))⟩
  · contradiction

theorem evalGroupAggItems_sound {prog : Program} {tEnv : TyEnv} {inTT : TableTy}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    {gRows : List TableRow}
    (hcols : ∀ c ∈ inTT.cols, validScalarTy prog c.ty = true)
    (hgRows : ∀ r ∈ gRows, CellsWf prog r.cells inTT.cols)
    (hreSound : ∀ r re sTy rTags, CellsWf prog r.cells inTT.cols →
      checkRowExpr prog tEnv inTT.cols re = .ok (sTy, rTags) →
      PrimResultWf prog sTy.toTy (evalRE inTT.cols r re)) :
    ∀ (aggs : List AggItem) (aggCols : List ColSpec),
      checkAggItemList prog tEnv inTT aggs = .ok aggCols →
      match evalGroupAggItems evalRE inTT.cols gRows (List.zip aggs aggCols) with
      | .ok aggCells => CellsWf prog aggCells aggCols
      | .stopped _ => True
      | .outOfFuel => True
      | .wrong => False
  | [], _, hchk => by
    unfold checkAggItemList at hchk; injection hchk with h'; subst h'
    exact .nil
  | aItem :: restA, aggCols, hchk => by
    unfold checkAggItemList at hchk; simp only [bind, Except.bind] at hchk
    cases hhd : checkAggItem prog tEnv inTT aItem with
    | error _ => simp [hhd] at hchk
    | ok aSpec =>
      simp only [hhd] at hchk
      cases htl : checkAggItemList prog tEnv inTT restA with
      | error _ => simp [htl] at hchk
      | ok tlSpecs =>
        simp only [htl, Except.ok.injEq] at hchk; subst hchk
        simp only [List.zip_cons_cons, evalGroupAggItems]
        have ih := evalGroupAggItems_sound evalRE hcols hgRows hreSound restA tlSpecs htl
        rcases checkAggItem_op_spec hcols hhd with ⟨hargNone, hopCnt, htyInt⟩ | ⟨re, sTy, rTags, hargSome, hreChk, hsv, hopRest⟩
        · simp only [hargNone]
          have hclean := evalAggClean_sound (prog := prog) (sTy := .unit) (outTy := aSpec.ty)
            (rawVals := gRows.map (fun _ => Val.unit)) rfl
            (fun v hv => by rw [List.mem_map] at hv; rcases hv with ⟨_, _, rfl⟩; exact .unit)
            (Or.inl ⟨hopCnt, htyInt⟩)
          cases hc : evalAggClean aItem.op aSpec.ty (gRows.map (fun _ => Val.unit)) with
          | stopped _ => trivial
          | outOfFuel => trivial
          | wrong => rw [hc] at hclean; nomatch hclean
          | ok aggCell =>
            rw [hc] at hclean; cases hclean with | ok hcellWf =>
            simp only
            cases hr : evalGroupAggItems evalRE inTT.cols gRows (List.zip restA tlSpecs) with
            | stopped _ => trivial
            | outOfFuel => trivial
            | wrong => rw [hr] at ih; exact ih
            | ok restCells => rw [hr] at ih; exact .cons hcellWf ih
        · simp only [hargSome]
          have hargWf := evalArgOnGroupRows_sound evalRE
            (fun r hr => hreSound r re sTy rTags hr hreChk) gRows hgRows
          cases harg : evalArgOnGroupRows evalRE inTT.cols re gRows with
          | stopped _ => trivial
          | outOfFuel => trivial
          | wrong => rw [harg] at hargWf; exact hargWf
          | ok argVals =>
            rw [harg] at hargWf
            simp only
            have hclean := evalAggClean_sound hsv hargWf (Or.inr hopRest)
            cases hc : evalAggClean aItem.op aSpec.ty argVals with
            | stopped _ => trivial
            | outOfFuel => trivial
            | wrong => rw [hc] at hclean; nomatch hclean
            | ok aggCell =>
              rw [hc] at hclean; cases hclean with | ok hcellWf =>
              simp only
              cases hr : evalGroupAggItems evalRE inTT.cols gRows (List.zip restA tlSpecs) with
              | stopped _ => trivial
              | outOfFuel => trivial
              | wrong => rw [hr] at ih; exact ih
              | ok restCells => rw [hr] at ih; exact .cons hcellWf ih

theorem checkAggItemList_props {prog : Program} {tEnv : TyEnv} {inTT : TableTy}
    (hcols : ∀ c ∈ inTT.cols, validScalarTy prog c.ty = true) :
    ∀ {aggs : List AggItem} {aggCols : List ColSpec},
      checkAggItemList prog tEnv inTT aggs = .ok aggCols →
      aggCols.length = aggs.length ∧
      ∀ c ∈ aggCols, validScalarTy prog c.ty = true ∧ c.bucketed = false ∧ c.aggKind ≠ .groupKey
  | [], _, hchk => by
    unfold checkAggItemList at hchk; injection hchk with h'; subst h'
    exact ⟨rfl, fun _ hm => nomatch hm⟩
  | a :: rest, _, hchk => by
    unfold checkAggItemList at hchk; simp only [bind, Except.bind] at hchk
    cases hhd : checkAggItem prog tEnv inTT a with
    | error _ => simp [hhd] at hchk
    | ok hd =>
      simp only [hhd] at hchk
      cases htl : checkAggItemList prog tEnv inTT rest with
      | error _ => simp [htl] at hchk
      | ok tl =>
        simp only [htl, Except.ok.injEq] at hchk; subst hchk
        rcases checkAggItemList_props hcols htl with ⟨hlen, htlProps⟩
        refine ⟨congrArg (· + 1) hlen, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hr
        · exact checkAggItem_props hcols hhd
        · exact htlProps c hr

theorem summarize_keyCols_props {prog : Program} {tv : TableVal} {tt : TableTy}
    (hcolsEq : tv.cols = tt.cols)
    (hschema : TableSchemaWf prog tt = true) :
    let gksChk := tt.groupedBy.getD []
    let groupKeysEval := (tv.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name
    let keyColsEval := (tv.cols.filter (fun c => groupKeysEval.contains c.name)).map
      (fun c => { c with aggKind := .groupKey })
    let keyColsChk := (tt.cols.filter (fun c => gksChk.contains c.name)).map
      (fun c => { c with aggKind := .groupKey })
    keyColsEval = keyColsChk ∧
    groupKeysEval = keyColsEval.map ColSpec.name ∧
    (∀ kc ∈ keyColsEval, ∃ origC, tv.cols.find? (fun c => c.name == kc.name) = some origC ∧ origC.ty = kc.ty) := by
  intro gksChk groupKeysEval keyColsEval keyColsChk
  simp only [TableSchemaWf, Bool.and_eq_true, List.all_eq_true] at hschema
  have huniq : distinctIdents (tv.cols.map ColSpec.name) = true := hcolsEq ▸ hschema.1.1
  have hgkIff : ∀ c ∈ tv.cols, decide (c.aggKind = .groupKey) = gksChk.contains c.name := by
    intro c hc
    rw [hcolsEq] at hc
    have h1 := (hschema.1.2 c hc).2
    exact of_decide_eq_true h1
  have hevalContains : ∀ c ∈ tv.cols, groupKeysEval.contains c.name = decide (c.aggKind = .groupKey) := by
    intro c hc
    cases hck : decide (c.aggKind = .groupKey)
    · cases hmem : groupKeysEval.contains c.name with
      | false => rfl
      | true =>
        exfalso
        rw [List.contains_iff_mem, List.mem_map] at hmem
        rcases hmem with ⟨c', hc', hnameEq⟩
        rcases List.mem_filter.mp hc' with ⟨hc'In, hc'Gk⟩
        have hceqc' : c = c' := by
          clear hgkIff keyColsEval keyColsChk groupKeysEval hc'
          generalize hcsEq : tv.cols = cs at huniq hc hc'In
          clear hcsEq
          induction cs with
          | nil => nomatch hc
          | cons d ds ih =>
            rcases distinctIdents_not_mem huniq with ⟨hdnot, hdtl⟩
            rcases List.mem_cons.mp hc with rfl | hctl
            · rcases List.mem_cons.mp hc'In with rfl | hc'tl
              · rfl
              · exfalso; exact hdnot (hnameEq ▸ List.mem_map_of_mem hc'tl)
            · rcases List.mem_cons.mp hc'In with rfl | hc'tl
              · exfalso; exact hdnot (hnameEq.symm ▸ List.mem_map_of_mem hctl)
              · exact ih hdtl hctl hc'tl
        subst hceqc'; rw [hck] at hc'Gk; nomatch hc'Gk
    · apply List.contains_iff_mem.mpr
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, hck⟩)
  have hfilterEq : tv.cols.filter (fun c => groupKeysEval.contains c.name) =
      tv.cols.filter (fun c => decide (c.aggKind = .groupKey)) := by
    apply List.filter_congr
    intro c hc; exact hevalContains c hc
  have hfilterChkEq : tv.cols.filter (fun c => decide (c.aggKind = .groupKey)) =
      tt.cols.filter (fun c => gksChk.contains c.name) := by
    rw [← hcolsEq]
    apply List.filter_congr
    intro c hc; exact hgkIff c hc
  have hkeyEq : keyColsEval = keyColsChk := by
    dsimp only [keyColsEval, keyColsChk]
    rw [hfilterEq, hfilterChkEq]
  have hgkNames : groupKeysEval = keyColsEval.map ColSpec.name := by
    dsimp only [keyColsEval, groupKeysEval]
    rw [hfilterEq]
    induction (tv.cols.filter (fun c => decide (c.aggKind = .groupKey))) <;> simp [*]
  refine ⟨hkeyEq, hgkNames, ?_⟩
  intro kc hkc
  dsimp only [keyColsEval] at hkc
  rw [hfilterEq, List.mem_map] at hkc
  rcases hkc with ⟨orig, horigFilter, rfl⟩
  have horigIn := (List.mem_filter.mp horigFilter).1
  have hfindUniq : ∀ (cs : List ColSpec), distinctIdents (cs.map ColSpec.name) = true →
      orig ∈ cs → cs.find? (fun x => x.name == orig.name) = some orig := by
    intro cs hcs horigCs
    induction cs with
    | nil => nomatch horigCs
    | cons d ds ih =>
      rcases distinctIdents_not_mem hcs with ⟨hdnot, hdtl⟩
      simp only [List.find?]
      rcases List.mem_cons.mp horigCs with rfl | htl
      · simp
      · have hne : (d.name == orig.name) = false := by
          cases hdo : (d.name == orig.name)
          · rfl
          · exfalso; exact hdnot ((beq_iff_eq.mp hdo) ▸ List.mem_map_of_mem htl)
        simp [hne, ih hdtl htl]
  exact ⟨orig, hfindUniq tv.cols huniq horigIn, rfl⟩

theorem summarize_schemaWf {prog : Program} {tt : TableTy} {aggCols : List ColSpec}
    {rt ot : TagSet} {distinctKey : Option Ident}
    (htt : TableSchemaWf prog tt = true)
    (haggProps : ∀ c ∈ aggCols, validScalarTy prog c.ty = true ∧ c.bucketed = false ∧ c.aggKind ≠ .groupKey)
    (houtUniq : distinctIdents (((tt.cols.filter (fun (c : ColSpec) => (tt.groupedBy.getD []).contains c.name)).map
        (fun (c : ColSpec) => { c with aggKind := .groupKey }) ++ aggCols).map ColSpec.name) = true) :
    TableSchemaWf prog {
      cols := (tt.cols.filter (fun (c : ColSpec) => (tt.groupedBy.getD []).contains c.name)).map
          (fun (c : ColSpec) => { c with aggKind := .groupKey }) ++ aggCols,
      rowTags := rt, orderTags := ot,
      groupedBy := some (tt.groupedBy.getD []),
      summarized := true,
      distinctBy := distinctKey
    } = true := by
  let gks := tt.groupedBy.getD []
  let keyCols := (tt.cols.filter (fun (c : ColSpec) => gks.contains c.name)).map (fun (c : ColSpec) => { c with aggKind := .groupKey })
  rcases tableSchemaWf_cols_props htt with ⟨_, httCols⟩
  have hgbProps : distinctIdents gks = true ∧ ∀ k ∈ gks, (tt.findCol? k).isSome = true := by
    unfold TableSchemaWf at htt
    simp only [Bool.and_eq_true] at htt
    cases hgb : tt.groupedBy with
    | none => simp [gks, hgb, distinctIdents]
    | some ks =>
      rw [hgb] at htt
      simp only [Bool.and_eq_true, List.all_eq_true] at htt
      simpa [gks, hgb] using htt.2
  unfold TableSchemaWf
  dsimp only
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨houtUniq, ?_⟩, hgbProps.1, ?_⟩
  · intro c hc
    rw [List.mem_append] at hc
    rcases hc with hkey | hagg
    · rw [List.mem_map] at hkey
      rcases hkey with ⟨orig, horigF, rfl⟩
      rcases List.mem_filter.mp horigF with ⟨horigIn, horigGk⟩
      rcases httCols orig horigIn with ⟨hv, hb⟩
      refine ⟨⟨hv, ?_⟩, ?_⟩
      · cases hbk : orig.bucketed <;> simp [hbk, hb]
      · simpa [gks] using horigGk.symm
    · rcases haggProps c hagg with ⟨hv, hb, hnotGk⟩
      have hgkF : decide (c.aggKind = .groupKey) = false := decide_eq_false hnotGk
      have hnotInGks : gks.contains c.name = false := by
        cases hmem : gks.contains c.name with
        | false => rfl
        | true =>
          exfalso
          have hkSome := hgbProps.2 c.name (List.contains_iff_mem.mp hmem)
          rw [Option.isSome_iff_exists] at hkSome
          rcases hkSome with ⟨kc, hkcFind⟩
          have hkcIn := List.mem_of_find?_eq_some hkcFind
          have hkcName : kc.name = c.name := find?_name_eq ColSpec.name hkcFind
          have hInKeyCols : c.name ∈ keyCols.map ColSpec.name := by
            rw [List.mem_map]
            refine ⟨{ kc with aggKind := .groupKey }, ?_, hkcName⟩
            exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hkcIn, hkcName ▸ hmem⟩)
          have hInAggCols : c.name ∈ aggCols.map ColSpec.name := List.mem_map_of_mem hagg
          have hdisj : ∀ {xs ys : List Ident}, distinctIdents (xs ++ ys) = true → ∀ z ∈ xs, z ∉ ys := by
            intro xs ys hd z hz
            induction xs with
            | nil => nomatch hz
            | cons x xtl ih =>
              simp only [List.cons_append] at hd
              rcases distinctIdents_not_mem hd with ⟨hxnot, hdtl⟩
              rcases List.mem_cons.mp hz with rfl | hztl
              · exact fun hy => hxnot (List.mem_append.mpr (Or.inr hy))
              · exact ih hdtl hztl
          have houtUniq' := houtUniq
          rw [List.map_append] at houtUniq'
          exact hdisj houtUniq' c.name hInKeyCols hInAggCols
      have hnotInGks' : (tt.groupedBy.getD []).contains c.name = false := hnotInGks
      refine ⟨⟨hv, by simp [hb]⟩, ?_⟩
      simp only [Option.getD_some, hgkF, hnotInGks', decide_true]
  · intro k hk
    have hkSome := hgbProps.2 k hk
    rw [Option.isSome_iff_exists] at hkSome ⊢
    rcases hkSome with ⟨kc, hkcFind⟩
    have hkcIn := List.mem_of_find?_eq_some hkcFind
    have hkcName : kc.name = k := find?_name_eq ColSpec.name hkcFind
    have hInOut : { kc with aggKind := .groupKey } ∈ keyCols ++ aggCols := by
      apply List.mem_append.mpr; apply Or.inl
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hkcIn, hkcName ▸ List.contains_iff_mem.mpr hk⟩)
    unfold TableTy.findCol?
    cases hf : (keyCols ++ aggCols).find? (fun c => c.name == k) with
    | some found => exact ⟨found, rfl⟩
    | none =>
      exfalso
      have hnone := List.find?_eq_none.mp hf { kc with aggKind := .groupKey } hInOut
      simp [hkcName] at hnone

theorem evalSummarizeGroups_sound {prog : Program} {tEnv : TyEnv} {inTT outTT : TableTy}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    {tv : TableVal} (groupKeys : List Ident) {keyCols aggCols : List ColSpec}
    {distinctKey : Option Ident} {dkIdx? : Option (Nat × ColSpec)} {aggs : List AggItem}
    (w : World) (hw : WorldWf prog w)
    (htvCols : tv.cols = inTT.cols)
    (hinCols : ∀ c ∈ inTT.cols, validScalarTy prog c.ty = true)
    (htvRows : ∀ r ∈ tv.rows, CellsWf prog r.cells inTT.cols)
    (houtCols : outTT.cols = keyCols ++ aggCols)
    (houtSum : outTT.summarized = true)
    (houtDk : outTT.distinctBy = distinctKey)
    (houtSchema : TableSchemaWf prog outTT = true)
    (hdkSome : distinctKey.isSome = true → dkIdx?.isSome = true)
    (haggChk : checkAggItemList prog tEnv inTT aggs = .ok aggCols)
    (hreSound : ∀ r re sTy rTags, CellsWf prog r.cells inTT.cols →
      checkRowExpr prog tEnv inTT.cols re = .ok (sTy, rTags) →
      PrimResultWf prog sTy.toTy (evalRE inTT.cols r re)) :
    ∀ (gks : List (List Val)),
      (∀ gk ∈ gks, CellsWf prog gk keyCols) →
      OutcomeWf prog [] (.table outTT)
        (evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outTT.cols w gks)
  | [], _ =>
    .ok (.table rfl houtSchema (by rw [houtSum, houtDk]; exact .nil _ true _)) hw
  | gKey :: gks, hgks => by
    unfold evalSummarizeGroups
    simp only
    let gRows :=
      if groupKeys.isEmpty then tv.rows
      else tv.rows.filter (fun r =>
        match extractKeyVals tv.cols groupKeys r with
        | some kv => valListEq kv gKey
        | none => false)
    have hgRowsWf : ∀ r ∈ gRows, CellsWf prog r.cells inTT.cols := by
      intro r hr
      dsimp only [gRows] at hr
      split at hr
      · exact htvRows r hr
      · exact htvRows r (List.mem_filter.mp hr).1
    have haggRes := evalGroupAggItems_sound evalRE hinCols hgRowsWf hreSound aggs aggCols haggChk
    rw [← htvCols] at haggRes
    cases hga : evalGroupAggItems evalRE tv.cols gRows (List.zip aggs aggCols) with
    | stopped b => exact .stopped b hw
    | outOfFuel => exact .outOfFuel
    | wrong => rw [hga] at haggRes; nomatch haggRes
    | ok aggCells =>
      rw [hga] at haggRes
      simp only
      have ih := evalSummarizeGroups_sound evalRE groupKeys w hw htvCols hinCols htvRows houtCols houtSum
        houtDk houtSchema hdkSome haggChk hreSound gks (fun gk hgk => hgks gk (.tail _ hgk))
      cases hrec : evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outTT.cols w gks with
      | stopped b w' => rw [hrec] at ih; exact ih
      | failed m w' => rw [hrec] at ih; exact ih
      | outOfFuel => exact .outOfFuel
      | jumped _ _ _ => rw [hrec] at ih; exact ih
      | wrong => rw [hrec] at ih; nomatch ih
      | ok resVal w' =>
        rw [hrec] at ih
        cases ih with | ok hresWf _ =>
        cases hresWf with | @table restTV _ _ _ hrestRows =>
        apply OutcomeWf.ok _ hw
        apply ValWf.table rfl houtSchema
        have hcurCells : CellsWf prog (gKey ++ aggCells) outTT.cols := by
          rw [houtCols]
          exact (hgks gKey (.head _)).append haggRes
        refine .cons hcurCells ?_ hrestRows
        intro _
        refine ⟨_, rfl, ?_⟩
        intro hdkB
        rw [houtDk] at hdkB
        have hdki := hdkSome hdkB
        cases distinctKey with
        | none => simp at hdkB
        | some _ =>
          cases dkIdx? with
          | none => simp at hdki
          | some pair => rcases pair with ⟨_, _⟩; rfl

theorem resolveJoinPairs_keys_exist {lTT rTT : TableTy} {on : JoinOn}
    {keyPairs : List (ColSpec × ColSpec)}
    (h : resolveJoinPairs lTT rTT on = .ok keyPairs) :
    ∀ k ∈ keyPairs.map (fun p => p.1.name), (lTT.cols.find? (fun c => c.name == k)).isSome = true := by
  have aux : ∀ (ps : List (Ident × Ident)) (kps : List (ColSpec × ColSpec)),
      resolveJoinPairs.go lTT rTT ps = .ok kps →
      ∀ k ∈ kps.map (fun p => p.1.name), (lTT.cols.find? (fun c => c.name == k)).isSome = true := by
    intro ps kps hgo
    induction ps generalizing kps with
    | nil =>
      unfold resolveJoinPairs.go at hgo; injection hgo with h'; subst h'
      intro _ hm; nomatch hm
    | cons pair rest ih =>
      rcases pair with ⟨lk, rk⟩
      unfold resolveJoinPairs.go at hgo
      cases hl : lTT.findCol? lk <;> cases hr : rTT.findCol? rk <;> simp [hl, hr] at hgo
      split at hgo <;> try contradiction
      simp only [bind, Except.bind] at hgo
      cases htl : resolveJoinPairs.go lTT rTT rest with
      | error _ => simp [htl] at hgo
      | ok tlKps =>
        simp only [htl, Except.ok.injEq] at hgo; subst hgo
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hrest
        · unfold TableTy.findCol? at hl
          dsimp only
          have hln : _ = lk := find?_name_eq ColSpec.name hl
          rw [hln, hl]; rfl
        · exact ih tlKps htl k hrest
  unfold resolveJoinPairs at h
  cases on <;> simp only at h <;> (split at h; contradiction; exact aux _ keyPairs h)

theorem distinctIdents_append_disjoint :
    ∀ {xs ys : List Ident},
      distinctIdents xs = true →
      distinctIdents ys = true →
      xs.any (fun n => ys.contains n) = false →
      distinctIdents (xs ++ ys) = true
  | [], _, _, hdy, _ => hdy
  | x :: xs, ys, hdx, hdy, hany => by
    rcases distinctIdents_not_mem hdx with ⟨hxnot, hdxTl⟩
    simp only [List.any_cons, Bool.or_eq_false_iff] at hany
    simp only [List.cons_append, distinctIdents, Bool.and_eq_true]
    refine ⟨?_, distinctIdents_append_disjoint hdxTl hdy hany.2⟩
    cases hm : (xs ++ ys).contains x with
    | false => rfl
    | true =>
      exfalso
      rw [List.contains_iff_mem, List.mem_append] at hm
      rcases hm with hl | hr
      · exact hxnot hl
      · have hyc := List.contains_iff_mem.mpr hr
        rw [hyc] at hany; nomatch hany.1

def buildJoinedColsCore (lUpdated rPrepared : List ColSpec) (suffixes : Suffixes) :
    Except String (List ColSpec) :=
  let lNames := lUpdated.map ColSpec.name
  let rNames := rPrepared.map ColSpec.name
  if !(lNames.any (fun n => rNames.contains n)) then
    .ok (lUpdated ++ rPrepared)
  else
    match suffixes with
    | none => .error "overlapping non-key join columns require explicit suffixes"
    | some (sL, sR) =>
      if sL == sR || (sL.isEmpty && sR.isEmpty) then
        .error "join suffixes must be distinct"
      else
        let lRenamed := lUpdated.map (fun c => if rNames.contains c.name then { c with name := c.name ++ sL } else c)
        let rRenamed := rPrepared.map (fun c => if lNames.contains c.name then { c with name := c.name ++ sR } else c)
        let combined := lRenamed ++ rRenamed
        if distinctIdents (combined.map ColSpec.name) then .ok combined
        else .error "join suffixes still produced duplicate column names"

theorem buildJoinedColsCore_props {prog : Program} {lUpdated rPrepared joinedCols : List ColSpec}
    {suffixes : Suffixes}
    (hlUniq : distinctIdents (lUpdated.map ColSpec.name) = true)
    (hrUniq : distinctIdents (rPrepared.map ColSpec.name) = true)
    (hlCProps : ∀ c ∈ lUpdated, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
    (hrCProps : ∀ c ∈ rPrepared, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
    (hb : buildJoinedColsCore lUpdated rPrepared suffixes = .ok joinedCols) :
    distinctIdents (joinedCols.map ColSpec.name) = true ∧
    (∀ c ∈ joinedCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) ∧
    joinedCols.map ColSpec.ty = lUpdated.map ColSpec.ty ++ rPrepared.map ColSpec.ty := by
  unfold buildJoinedColsCore at hb
  dsimp only at hb
  cases hcoll : ((lUpdated.map ColSpec.name).any (fun n => (rPrepared.map ColSpec.name).contains n))
  · simp only [hcoll, Bool.not_false, ↓reduceIte] at hb
    injection hb with h'; subst h'
    rw [List.map_append, List.map_append]
    refine ⟨distinctIdents_append_disjoint hlUniq hrUniq hcoll, ?_, rfl⟩
    intro c hc; rw [List.mem_append] at hc
    rcases hc with hl | hr; exact hlCProps c hl; exact hrCProps c hr
  · simp only [hcoll, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb
    cases suffixes with
    | none => simp at hb
    | some sf =>
      rcases sf with ⟨sL, sR⟩
      dsimp only at hb
      cases hsufBad : (sL == sR || (sL.isEmpty && sR.isEmpty))
      · simp only [hsufBad, Bool.false_eq_true, ↓reduceIte] at hb
        split at hb
        · rename_i hcombDist
          injection hb with h'; subst h'
          refine ⟨hcombDist, ?_, ?_⟩
          · intro c hc; rw [List.mem_append] at hc
            rcases hc with hl | hr
            · rw [List.mem_map] at hl; rcases hl with ⟨lc, hlc, rfl⟩
              rcases hlCProps lc hlc with ⟨p1, p2, p3⟩
              split <;> exact ⟨p1, p2, p3⟩
            · rw [List.mem_map] at hr; rcases hr with ⟨rc, hrc, rfl⟩
              rcases hrCProps rc hrc with ⟨p1, p2, p3⟩
              split <;> exact ⟨p1, p2, p3⟩
          · rw [List.map_append]
            have hrenTy : ∀ (ns : List Ident) (suf : String) (cs : List ColSpec),
                (cs.map (fun c => if ns.contains c.name then { c with name := c.name ++ suf } else c)).map ColSpec.ty =
                  cs.map ColSpec.ty := by
              intro ns suf cs; induction cs with
              | nil => rfl
              | cons d ds ih => simp only [List.map_cons, ih]; cases ns.contains d.name <;> simp
            rw [hrenTy, hrenTy]
        · contradiction
      · rw [hsufBad] at hb; simp at hb

theorem buildJoinedCols_props {prog : Program} {kind : JoinKind} {lCols rCols joinedCols : List ColSpec}
    {on : JoinOn} {suffixes : Suffixes}
    (hlUniq : distinctIdents (lCols.map ColSpec.name) = true)
    (hrUniq : distinctIdents (rCols.map ColSpec.name) = true)
    (hlProps : ∀ c ∈ lCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text))
    (hrProps : ∀ c ∈ rCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text))
    (hb : buildJoinedCols kind lCols rCols on suffixes = .ok joinedCols) :
    distinctIdents (joinedCols.map ColSpec.name) = true ∧
    (∀ c ∈ joinedCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) ∧
    (match kind with
     | .semi | .anti => joinedCols.map ColSpec.ty = lCols.map ColSpec.ty
     | _ =>
       let sameKeyNames := match on with | .sameKeys ks => ks | .pairs _ => []
       let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
       joinedCols.map ColSpec.ty =
         lCols.map ColSpec.ty ++
           (rCols.filter (fun rc => !sameKeyNames.contains rc.name)).map
             (fun rc => if isLeftOuter then ensureOptionScalar rc.ty else rc.ty)) := by
  have hlUpdProps : ∀ (sks : List Ident),
      let lUpdated := lCols.map (fun lc =>
        if sks.contains lc.name then
          match rCols.find? (fun rc => rc.name == lc.name) with
          | some rc => { lc with tags := lc.tags.union rc.tags, bucketed := false, aggKind := .raw }
          | none => { lc with aggKind := .raw }
        else { lc with aggKind := .raw })
      lUpdated.map ColSpec.name = lCols.map ColSpec.name ∧
      lUpdated.map ColSpec.ty = lCols.map ColSpec.ty ∧
      ∀ c ∈ lUpdated, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
    intro sks
    have hnt : ∀ (cs : List ColSpec),
        (cs.map (fun lc =>
          if sks.contains lc.name then
            match rCols.find? (fun rc => rc.name == lc.name) with
            | some rc => { lc with tags := lc.tags.union rc.tags, bucketed := false, aggKind := .raw }
            | none => { lc with aggKind := .raw }
          else { lc with aggKind := .raw })).map ColSpec.name = cs.map ColSpec.name ∧
        (cs.map (fun lc =>
          if sks.contains lc.name then
            match rCols.find? (fun rc => rc.name == lc.name) with
            | some rc => { lc with tags := lc.tags.union rc.tags, bucketed := false, aggKind := .raw }
            | none => { lc with aggKind := .raw }
          else { lc with aggKind := .raw })).map ColSpec.ty = cs.map ColSpec.ty := by
      intro cs; induction cs with
      | nil => exact ⟨rfl, rfl⟩
      | cons lc lcs ih =>
        simp only [List.map_cons]; split
        · cases rCols.find? (fun rc => rc.name == lc.name) <;> exact ⟨congrArg _ ih.1, congrArg _ ih.2⟩
        · exact ⟨congrArg _ ih.1, congrArg _ ih.2⟩
    refine ⟨(hnt lCols).1, (hnt lCols).2, ?_⟩
    intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨lc, hlc, rfl⟩
    rcases hlProps lc hlc with ⟨hv, hb0⟩
    split
    · cases rCols.find? (fun rc => rc.name == lc.name)
      · exact ⟨hv, hb0, rfl⟩
      · exact ⟨hv, fun h => by simp at h, rfl⟩
    · exact ⟨hv, hb0, rfl⟩
  have hrPrepProps : ∀ (sks : List Ident) (isLO : Bool),
      let rFiltered := rCols.filter (fun rc => !sks.contains rc.name)
      let rPrepared := rFiltered.map (fun rc =>
        { rc with
          ty := if isLO then ensureOptionScalar rc.ty else rc.ty
          bucketed := if isLO then false else rc.bucketed
          aggKind := .raw })
      distinctIdents (rPrepared.map ColSpec.name) = true ∧
      rPrepared.map ColSpec.ty = rFiltered.map (fun rc => if isLO then ensureOptionScalar rc.ty else rc.ty) ∧
      ∀ c ∈ rPrepared, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
    intro sks isLO rFiltered rPrepared
    have hnames : rPrepared.map ColSpec.name = rFiltered.map ColSpec.name := by
      dsimp only [rPrepared]; induction rFiltered <;> simp [*]
    refine ⟨hnames ▸ distinctIdents_filter _ hrUniq, ?_, ?_⟩
    · dsimp only [rPrepared]; induction rFiltered <;> simp [*]
    · intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨rc, hrcF, rfl⟩
      rcases hrProps rc (List.mem_filter.mp hrcF).1 with ⟨hv, hb0⟩
      cases isLO
      · exact ⟨hv, hb0, rfl⟩
      · exact ⟨(ensureOptionScalar_eq_option_base hv).2, fun h => by simp at h, rfl⟩
  cases kind with
  | semi | anti =>
    unfold buildJoinedCols at hb; injection hb with h'; subst h'
    have hnames : (lCols.map (fun c => { c with aggKind := .raw })).map ColSpec.name = lCols.map ColSpec.name := by
      induction lCols <;> simp [*]
    refine ⟨hnames ▸ hlUniq, ?_, map_ty_with_aggKind lCols .raw⟩
    intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨lc, hlc, rfl⟩
    exact ⟨(hlProps lc hlc).1, (hlProps lc hlc).2, rfl⟩
  | innerOne | innerManyToOne | innerMany =>
    let sks := match on with | .sameKeys ks => ks | .pairs _ => []
    rcases hlUpdProps sks with ⟨hlNames, hlTys, hlCProps⟩
    rcases hrPrepProps sks false with ⟨hrDist, hrTys, hrCProps⟩
    rcases buildJoinedColsCore_props (hlNames ▸ hlUniq) hrDist hlCProps hrCProps hb with ⟨hd, hp, ht⟩
    exact ⟨hd, hp, by rw [ht, hlTys, hrTys]⟩
  | leftOne | leftManyToOne =>
    let sks := match on with | .sameKeys ks => ks | .pairs _ => []
    rcases hlUpdProps sks with ⟨hlNames, hlTys, hlCProps⟩
    rcases hrPrepProps sks true with ⟨hrDist, hrTys, hrCProps⟩
    rcases buildJoinedColsCore_props (hlNames ▸ hlUniq) hrDist hlCProps hrCProps hb with ⟨hd, hp, ht⟩
    exact ⟨hd, hp, by rw [ht, hlTys, hrTys]⟩

theorem extractRightJoinCells_sound {prog : Program} (isLeftOuter : Bool) {rCols : List ColSpec}
    {rRow : TableRow}
    (hrCols : ∀ c ∈ rCols, validScalarTy prog c.ty = true)
    (hrCells : CellsWf prog rRow.cells rCols) :
    ∀ (rKeepIdxs : List (ColSpec × Nat)),
      (∀ p ∈ rKeepIdxs, rCols[p.2]? = some p.1) →
      ∃ rCells, extractRightJoinCells isLeftOuter rRow rKeepIdxs = some rCells ∧
        CellsWf prog rCells (rKeepIdxs.map (fun (rc, _) =>
          { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty }))
  | [], _ => ⟨[], rfl, .nil⟩
  | (rc, idx) :: rest, hall => by
    have hgetCol := hall (rc, idx) (.head _)
    have hrcMem : rc ∈ rCols := List.mem_of_getElem? hgetCol
    rcases hrCells.getElem?_wf hgetCol with ⟨cell, hgetCell, hcellWf⟩
    rcases extractRightJoinCells_sound isLeftOuter hrCols hrCells rest (fun p hp => hall p (.tail _ hp)) with ⟨tlCells, htlEq, htlWf⟩
    refine ⟨(if isLeftOuter then wrapIntoOptionVal rc.ty cell else cell) :: tlCells,
      by simp [extractRightJoinCells, hgetCell, htlEq], .cons ?_ htlWf⟩
    cases isLeftOuter
    · exact hcellWf
    · exact wrapIntoOptionVal_sound (hrCols rc hrcMem) hcellWf

theorem combineJoinMatches_sound {prog : Program} (isLeftOuter : Bool)
    {lCols rCols : List ColSpec} {rKeepIdxs : List (ColSpec × Nat)} {lCells : List Val}
    (hrCols : ∀ c ∈ rCols, validScalarTy prog c.ty = true)
    (hlCells : CellsWf prog lCells lCols)
    (hallIdx : ∀ p ∈ rKeepIdxs, rCols[p.2]? = some p.1) :
    ∀ (mrs : List TableRow),
      (∀ mr ∈ mrs, CellsWf prog mr.cells rCols) →
      ∃ joined, combineJoinMatches isLeftOuter rKeepIdxs lCells mrs = some joined ∧
        ∀ jr ∈ joined, CellsWf prog jr.cells
          (lCols ++ rKeepIdxs.map (fun (rc, _) =>
            { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty }))
  | [], _ => ⟨[], rfl, fun _ hm => nomatch hm⟩
  | mr :: mrs, hmrs => by
    rcases extractRightJoinCells_sound isLeftOuter hrCols (hmrs mr (.head _)) rKeepIdxs hallIdx with ⟨rCells, hrEq, hrWf⟩
    rcases combineJoinMatches_sound isLeftOuter hrCols hlCells hallIdx mrs (fun x hx => hmrs x (.tail _ hx)) with ⟨tlJ, htlEq, htlWf⟩
    refine ⟨{ cells := lCells ++ rCells, groupMeta := none } :: tlJ,
      by simp [combineJoinMatches, hrEq, htlEq], ?_⟩
    intro jr hjr
    rcases List.mem_cons.mp hjr with rfl | hrest
    · exact hlCells.append hrWf
    · exact htlWf jr hrest

theorem nullRightCells_wf {prog : Program} :
    ∀ (rKeepIdxs : List (ColSpec × Nat)),
      CellsWf prog (rKeepIdxs.map (fun _ => Val.optNone))
        (rKeepIdxs.map (fun (rc, _) => { rc with ty := ensureOptionScalar rc.ty }))
  | [] => .nil
  | (rc, _) :: rest => .cons (optNone_ensureOption_sound rc.ty) (nullRightCells_wf rest)

theorem joinTableRows_sound {prog : Program} (kind : JoinKind)
    {lCols rCols joinedCols : List ColSpec}
    {lKeyNames rKeyNames : List Ident} {rKeepIdxs : List (ColSpec × Nat)}
    {rRows : List TableRow}
    (hrCols : ∀ c ∈ rCols, validScalarTy prog c.ty = true)
    (hlKeys : ∀ k ∈ lKeyNames, (lCols.find? (fun c => c.name == k)).isSome = true)
    (hallIdx : ∀ p ∈ rKeepIdxs, rCols[p.2]? = some p.1)
    (hrRows : ∀ rr ∈ rRows, CellsWf prog rr.cells rCols)
    (htyMatch :
      match kind with
      | .semi | .anti => joinedCols.map ColSpec.ty = lCols.map ColSpec.ty
      | _ =>
        let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
        joinedCols.map ColSpec.ty =
          lCols.map ColSpec.ty ++
            (rKeepIdxs.map (fun (rc, _) => { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty) :
    let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
    let nullRightCells := rKeepIdxs.map (fun _ => Val.optNone)
    ∀ (lRows : List TableRow),
      (∀ lr ∈ lRows, CellsWf prog lr.cells lCols) →
      ∃ outRows, joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows lRows = some outRows ∧
        RowsWf prog outRows joinedCols false false := by
  intro isLeftOuter nullRightCells lRows hlRows
  induction lRows with
  | nil => exact ⟨[], rfl, .nil _ false false⟩
  | cons lRow lRest ih =>
    have hlRowWf := hlRows lRow (.head _)
    rcases extractKeyVals_some hlRowWf lKeyNames hlKeys with ⟨lkv, hlkv⟩
    rcases ih (fun lr hlr => hlRows lr (.tail _ hlr)) with ⟨restJoined, hrestEq, hrestWf⟩
    unfold joinTableRows
    rw [hlkv]; dsimp only [bind, Option.bind]
    rw [hrestEq]; dsimp only [bind, Option.bind]
    let matchingR := rRows.filter (fun rRow =>
      match extractKeyVals rCols rKeyNames rRow with
      | some rkv => valListEq lkv rkv
      | none => false)
    have hmatchWf : ∀ mr ∈ matchingR, CellsWf prog mr.cells rCols :=
      fun mr hmr => hrRows mr (List.mem_filter.mp hmr).1
    cases kind with
    | semi =>
      dsimp only
      split
      · exact ⟨_, rfl, .cons (hlRowWf.congr_ty htyMatch.symm) (fun h => by simp at h) hrestWf⟩
      · exact ⟨restJoined, rfl, hrestWf⟩
    | anti =>
      dsimp only
      split
      · exact ⟨_, rfl, .cons (hlRowWf.congr_ty htyMatch.symm) (fun h => by simp at h) hrestWf⟩
      · exact ⟨restJoined, rfl, hrestWf⟩
    | innerOne | innerManyToOne | innerMany =>
      dsimp only [isLeftOuter] at htyMatch ⊢
      have hcombEq : (lCols ++ rKeepIdxs.map (fun (p : ColSpec × Nat) => { p.1 with ty := p.1.ty })).map ColSpec.ty =
          joinedCols.map ColSpec.ty := by
        rw [List.map_append]; exact htyMatch.symm
      split
      · exact ⟨restJoined, rfl, hrestWf⟩
      · rcases combineJoinMatches_sound false hrCols hlRowWf hallIdx matchingR hmatchWf with ⟨curJ, hcurEq, hcurWf⟩
        dsimp only [matchingR] at hcurEq
        erw [hcurEq]
        refine ⟨curJ ++ restJoined, rfl, RowsWf.of_forall_raw ?_⟩
        intro r hr; rw [List.mem_append] at hr
        rcases hr with hl | hr'
        · exact (hcurWf r hl).congr_ty hcombEq
        · exact hrestWf.to_forall r hr'
    | leftOne | leftManyToOne =>
      dsimp only [isLeftOuter] at htyMatch ⊢
      have hcombEq : (lCols ++ rKeepIdxs.map (fun (p : ColSpec × Nat) => { p.1 with ty := ensureOptionScalar p.1.ty })).map ColSpec.ty =
          joinedCols.map ColSpec.ty := by
        rw [List.map_append]; exact htyMatch.symm
      split
      · refine ⟨_, rfl, .cons ((hlRowWf.append (nullRightCells_wf rKeepIdxs)).congr_ty hcombEq)
          (fun h => by simp at h) hrestWf⟩
      · rcases combineJoinMatches_sound true hrCols hlRowWf hallIdx matchingR hmatchWf with ⟨curJ, hcurEq, hcurWf⟩
        dsimp only [matchingR] at hcurEq
        erw [hcurEq]
        refine ⟨curJ ++ restJoined, rfl, RowsWf.of_forall_raw ?_⟩
        intro r hr; rw [List.mem_append] at hr
        rcases hr with hl | hr'
        · exact (hcurWf r hl).congr_ty hcombEq
        · exact hrestWf.to_forall r hr'

theorem mergeUnionCols_props {prog : Program} :
    ∀ {lCols rCols outCols : List ColSpec},
      distinctIdents (lCols.map ColSpec.name) = true →
      (∀ c ∈ lCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text)) →
      mergeUnionCols lCols rCols = some outCols →
      outCols.map ColSpec.name = lCols.map ColSpec.name ∧
      outCols.map ColSpec.ty = lCols.map ColSpec.ty ∧
      distinctIdents (outCols.map ColSpec.name) = true ∧
      (∀ c ∈ outCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) ∧
      rCols.map ColSpec.ty = outCols.map ColSpec.ty
  | [], [], _, _, _, hm => by
    unfold mergeUnionCols at hm; injection hm with h'; subst h'
    exact ⟨rfl, rfl, rfl, (fun _ h => nomatch h), rfl⟩
  | lc :: lcs, rc :: rcs, _, hlUniq, hlProps, hm => by
    unfold mergeUnionCols at hm
    split at hm <;> try contradiction
    rename_i hmatch
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.map_eq_some_iff] at hmatch hm
    rcases hm with ⟨tlOut, htlM, rfl⟩
    rcases distinctIdents_not_mem hlUniq with ⟨_, htlUniq⟩
    rcases mergeUnionCols_props htlUniq (fun c hc => hlProps c (.tail _ hc)) htlM with
      ⟨hnTl, htTl, _, hpTl, hrTl⟩
    let headCol : ColSpec := {
      name := lc.name, ty := lc.ty, tags := lc.tags.union rc.tags,
      bucketed := lc.bucketed && rc.bucketed, aggKind := .raw
    }
    have hnEq : (headCol :: tlOut).map ColSpec.name = (lc :: lcs).map ColSpec.name :=
      congrArg (lc.name :: ·) hnTl
    refine ⟨hnEq, congrArg (lc.ty :: ·) htTl, hnEq ▸ hlUniq, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hrest
      · rcases hlProps lc (.head _) with ⟨hv, hb⟩
        exact ⟨hv, fun hbk => hb (by dsimp only [headCol] at hbk; revert hbk; cases lc.bucketed <;> simp), rfl⟩
      · exact hpTl c hrest
    · simp only [List.map_cons, ← hmatch.2, hrTl]
  | _ :: _, [], _, _, _, hm => by simp [mergeUnionCols] at hm
  | [], _ :: _, _, _, _, hm => by simp [mergeUnionCols] at hm

def windowFnSpec? (cols : List ColSpec) (orderTags : TagSet) (item : WindowItem) :
    Option (ScalarTy × TagSet) :=
  let overTags := TagSet.unionList (item.over.filterMap (fun k => (cols.find? (fun c => c.name == k)).map ColSpec.tags))
  let ordKeyTags := TagSet.unionList (item.order.filterMap (fun (k, _) => (cols.find? (fun c => c.name == k)).map ColSpec.tags))
  let ctxTags := (overTags.union ordKeyTags).union orderTags
  match item.fn with
  | .rowNumber => some (.int, ctxTags)
  | .rank col =>
    match cols.find? (fun c => c.name == col) with
    | some c => if isOrderedScalarTy (baseOfScalar c.ty).toTy then some (.int, c.tags.union ctxTags) else none
    | none => none
  | .lag col _ | .lead col _ =>
    match cols.find? (fun c => c.name == col) with
    | some c => some (ensureOptionScalar c.ty, c.tags.union ctxTags)
    | none => none
  | .runningSum col =>
    match cols.find? (fun c => c.name == col) with
    | some c => (numericCoreOfScalar? c.ty).map (fun nTy => (nTy, c.tags.union ctxTags))
    | none => none
  | .rollingMean col wSz =>
    if wSz == 0 then none
    else
      match cols.find? (fun c => c.name == col) with
      | some c =>
        if (numericCoreOfScalar? c.ty).isSome then some (.option .float, c.tags.union ctxTags)
        else none
      | none => none

theorem applyWindowItem_eq (cols : List ColSpec) (orderTags : TagSet) (item : WindowItem) :
    applyWindowItem cols orderTags item =
      if !item.over.all (fun k => (cols.find? (fun c => c.name == k)).isSome) ||
         !item.order.all (fun (k, _) =>
            match cols.find? (fun c => c.name == k) with
            | some c => isOrderedScalarTy (baseOfScalar c.ty).toTy
            | none => false) then
        .error s!"window item '{item.name}' references invalid partition/order columns"
      else
        match windowFnSpec? cols orderTags item with
        | none => .error s!"ill-typed window function in '{item.name}'"
        | some (wTy, wTags) =>
          let newCol : ColSpec := { name := item.name, ty := wTy, tags := wTags, bucketed := false, aggKind := .raw }
          if (cols.find? (fun c => c.name == item.name)).isSome then
            .ok (cols.map (fun c => if c.name == item.name then newCol else c))
          else
            .ok (cols ++ [newCol]) := rfl

theorem windowFnSpec?_ot_congr {prog : Program} {cols : List ColSpec} {ot1 : TagSet} (ot2 : TagSet)
    {item : WindowItem} {wTy : ScalarTy} {ts1 : TagSet}
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true)
    (hf1 : windowFnSpec? cols ot1 item = some (wTy, ts1)) :
    (∃ ts2, windowFnSpec? cols ot2 item = some (wTy, ts2)) ∧ validScalarTy prog wTy = true := by
  unfold windowFnSpec? at hf1 ⊢
  dsimp only at hf1 ⊢
  cases hfn : item.fn <;> simp only [hfn] at hf1 ⊢
  case rowNumber =>
    injection hf1 with hp; injection hp with hw _; subst hw; exact ⟨⟨_, rfl⟩, rfl⟩
  case rank col =>
    cases hc : cols.find? (fun c => c.name == col) with
    | none => simp [hc] at hf1
    | some c =>
      simp only [hc] at hf1 ⊢
      cases ho : isOrderedScalarTy (baseOfScalar c.ty).toTy <;> simp only [ho, Bool.false_eq_true, ↓reduceIte] at hf1 ⊢
      · contradiction
      · injection hf1 with hp; injection hp with hw _; subst hw; exact ⟨⟨_, rfl⟩, rfl⟩
  case lag col _ =>
    cases hc : cols.find? (fun c => c.name == col) with
    | none => simp [hc] at hf1
    | some c =>
      simp only [hc] at hf1 ⊢
      injection hf1 with hp; injection hp with hw _; subst hw
      exact ⟨⟨_, rfl⟩, (ensureOptionScalar_eq_option_base (hcols c (List.mem_of_find?_eq_some hc))).2⟩
  case lead col _ =>
    cases hc : cols.find? (fun c => c.name == col) with
    | none => simp [hc] at hf1
    | some c =>
      simp only [hc] at hf1 ⊢
      injection hf1 with hp; injection hp with hw _; subst hw
      exact ⟨⟨_, rfl⟩, (ensureOptionScalar_eq_option_base (hcols c (List.mem_of_find?_eq_some hc))).2⟩
  case runningSum col =>
    cases hc : cols.find? (fun c => c.name == col) with
    | none => simp [hc] at hf1
    | some c =>
      simp only [hc] at hf1 ⊢
      cases hn : numericCoreOfScalar? c.ty with
      | none => simp [hn] at hf1
      | some nTy =>
        simp only [hn, Option.map_some] at hf1 ⊢
        injection hf1 with hp; injection hp with hw _; subst hw
        refine ⟨⟨_, rfl⟩, ?_⟩
        rcases (numericCoreOfScalar?_props hn).2 with rfl | rfl | rfl <;> rfl
  case rollingMean col wSz =>
    cases hw0 : (wSz == 0) <;> simp only [hw0, Bool.false_eq_true, ↓reduceIte] at hf1 ⊢
    · cases hc : cols.find? (fun c => c.name == col) with
      | none => simp [hc] at hf1
      | some c =>
        simp only [hc] at hf1 ⊢
        cases hn : (numericCoreOfScalar? c.ty).isSome <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at hf1 ⊢
        · contradiction
        · injection hf1 with hp; injection hp with hw _; subst hw; exact ⟨⟨_, rfl⟩, rfl⟩
    · contradiction

theorem applyWindowItem_props {prog : Program} {cols next1 : List ColSpec}
    {ot1 : TagSet} (ot2 : TagSet) {item : WindowItem}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
    (happly1 : applyWindowItem cols ot1 item = .ok next1) :
    ∃ next2,
      applyWindowItem cols ot2 item = .ok next2 ∧
      next2.map ColSpec.name = next1.map ColSpec.name ∧
      next2.map ColSpec.ty = next1.map ColSpec.ty ∧
      distinctIdents (next1.map ColSpec.name) = true ∧
      (∀ c ∈ next1, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) ∧
      (∀ c ∈ next2, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) := by
  rw [applyWindowItem_eq] at happly1 ⊢
  split at happly1
  · contradiction
  · rename_i hoverOrdOk
    simp only [hoverOrdOk, Bool.false_eq_true, ↓reduceIte]
    cases hf1 : windowFnSpec? cols ot1 item with
    | none => rw [hf1] at happly1; simp at happly1
    | some pair =>
      rcases pair with ⟨wTy, ts1⟩
      rw [hf1] at happly1; dsimp only at happly1
      rcases windowFnSpec?_ot_congr ot2 (fun c hc => (hcols c hc).1) hf1 with ⟨⟨ts2, hf2⟩, hwVal⟩
      rw [hf2]; dsimp only
      let nc1 : ColSpec := { name := item.name, ty := wTy, tags := ts1, bucketed := false, aggKind := .raw }
      let nc2 : ColSpec := { name := item.name, ty := wTy, tags := ts2, bucketed := false, aggKind := .raw }
      have hncProps1 : ∀ c ∈ (if (cols.find? (fun c => c.name == item.name)).isSome then cols.map (fun c => if c.name == item.name then nc1 else c) else cols ++ [nc1]),
          validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
        intro c hc; split at hc
        · rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
          split; exact ⟨hwVal, fun h => by simp at h, rfl⟩; exact hcols o ho
        · rw [List.mem_append] at hc; rcases hc with hl | hr
          · exact hcols c hl
          · simp at hr; subst hr; exact ⟨hwVal, fun h => by simp at h, rfl⟩
      have hncProps2 : ∀ c ∈ (if (cols.find? (fun c => c.name == item.name)).isSome then cols.map (fun c => if c.name == item.name then nc2 else c) else cols ++ [nc2]),
          validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
        intro c hc; split at hc
        · rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
          split; exact ⟨hwVal, fun h => by simp at h, rfl⟩; exact hcols o ho
        · rw [List.mem_append] at hc; rcases hc with hl | hr
          · exact hcols c hl
          · simp at hr; subst hr; exact ⟨hwVal, fun h => by simp at h, rfl⟩
      have hdist1 := distinctIdents_replace_or_append nc1 cols huniq
      dsimp only [nc1] at hdist1
      cases hex : (cols.find? (fun c => c.name == item.name)).isSome
      · simp only [hex, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happly1 hdist1 hncProps1 hncProps2 ⊢
        subst happly1
        exact ⟨cols ++ [nc2], rfl, by simp [nc2], by simp [nc2], hdist1, hncProps1, hncProps2⟩
      · simp only [hex, ↓reduceIte, Except.ok.injEq] at happly1 hdist1 hncProps1 hncProps2 ⊢
        subst happly1
        have hmapN : (cols.map (fun c => if c.name == item.name then nc2 else c)).map ColSpec.name =
            (cols.map (fun c => if c.name == item.name then nc1 else c)).map ColSpec.name := by
          generalize cols = l
          induction l with
          | nil => rfl
          | cons c cs ih => rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ih]; cases (c.name == item.name) <;> simp [nc1, nc2]
        have hmapT : (cols.map (fun c => if c.name == item.name then nc2 else c)).map ColSpec.ty =
            (cols.map (fun c => if c.name == item.name then nc1 else c)).map ColSpec.ty := by
          generalize cols = l
          induction l with
          | nil => rfl
          | cons c cs ih => rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ih]; cases (c.name == item.name) <;> simp [nc1, nc2]
        exact ⟨_, rfl, hmapN, hmapT, hdist1, hncProps1, hncProps2⟩

theorem evalWindowOnTable_sound {prog : Program} {tv : TableVal} {item : WindowItem}
    {nextCols : List ColSpec}
    (huniq : distinctIdents (tv.cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ tv.cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
    (hrows : RowsWf prog tv.rows tv.cols false false)
    (happly : applyWindowItem tv.cols TagSet.empty item = .ok nextCols) :
    ∃ nextTV, evalWindowOnTable tv item nextCols = some nextTV ∧
      nextTV.cols = nextCols ∧
      RowsWf prog nextTV.rows nextCols false false := by
  rw [applyWindowItem_eq] at happly
  split at happly <;> try contradiction
  rename_i hoverOrdNotBad
  rw [Bool.not_eq_true] at hoverOrdNotBad
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.all_eq_true] at hoverOrdNotBad
  have hoverOk := hoverOrdNotBad.1
  cases hfnSpec : windowFnSpec? tv.cols TagSet.empty item with
  | none => rw [hfnSpec] at happly; simp at happly
  | some pair =>
    rcases pair with ⟨wTy, wTags⟩
    rw [hfnSpec] at happly; dsimp only at happly
    let newCol : ColSpec := { name := item.name, ty := wTy, tags := wTags, bucketed := false, aggKind := .raw }
    have hnextEq : nextCols = (if (tv.cols.find? (fun c => c.name == item.name)).isSome then
        tv.cols.map (fun c => if c.name == item.name then newCol else c)
      else tv.cols ++ [newCol]) := by
      cases hex : (tv.cols.find? (fun c => c.name == item.name)).isSome <;>
        simp only [hex, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happly ⊢ <;>
        exact happly.symm
    have hnextUniq : distinctIdents (nextCols.map ColSpec.name) = true := by
      rw [hnextEq]; exact distinctIdents_replace_or_append newCol tv.cols huniq
    have hnewColMem : newCol ∈ nextCols := by
      rw [hnextEq]
      cases hf : tv.cols.find? (fun c => c.name == item.name) with
      | none => simp
      | some orig =>
        simp only [Option.isSome_some, ↓reduceIte, List.mem_map]
        have hnameEq : orig.name = item.name := find?_name_eq ColSpec.name hf
        exact ⟨orig, List.mem_of_find?_eq_some hf, by simp [hnameEq]⟩
    have hfindTarget : nextCols.find? (fun c => c.name == item.name) = some newCol := by
      have haux : ∀ (cs : List ColSpec), distinctIdents (cs.map ColSpec.name) = true →
          newCol ∈ cs → cs.find? (fun c => c.name == item.name) = some newCol := by
        intro cs hcs hmem
        induction cs with
        | nil => nomatch hmem
        | cons d ds ih =>
          rcases distinctIdents_not_mem hcs with ⟨hdnot, hdtl⟩
          simp only [List.find?]
          rcases List.mem_cons.mp hmem with rfl | htl
          · simp [newCol]
          · have hne : (d.name == item.name) = false := by
              cases hdn : (d.name == item.name)
              · rfl
              · exfalso; exact hdnot ((beq_iff_eq.mp hdn) ▸ List.mem_map_of_mem htl)
            simp [hne, ih hdtl htl]
      exact haux nextCols hnextUniq hnewColMem
    have hmemZip : ∀ (k : Nat) (rs : List TableRow) (p : TableRow × Nat),
        p ∈ rs.zipIdx k → p.1 ∈ rs := by
      intro k rs
      induction rs generalizing k with
      | nil => intro _ hm; nomatch hm
      | cons hd tl ihz =>
        intro p hp
        simp only [List.zipIdx_cons] at hp
        rcases List.mem_cons.mp hp with rfl | htl
        · exact .head _
        · exact .tail _ (ihz (k + 1) p htl)
    let indexedRows := tv.rows.zipIdx
    have hindexedWf : ∀ p ∈ indexedRows, CellsWf prog p.1.cells tv.cols :=
      fun p hp => hrows.to_forall p.1 (hmemZip 0 tv.rows p hp)
    let sortedIndexed :=
      if item.order.isEmpty then indexedRows
      else insertionSortBy (fun a b => rowLtByKeys tv.cols item.order a.1 b.1) indexedRows
    have hsortedWf : ∀ p ∈ sortedIndexed, CellsWf prog p.1.cells tv.cols := by
      intro p hp; dsimp only [sortedIndexed] at hp
      split at hp
      · exact hindexedWf p hp
      · exact hindexedWf p (mem_insertionSortBy _ p _ hp)
    have hcompute : ∀ (partRows : List TableRow) (pos : Nat),
        (∀ pr ∈ partRows, CellsWf prog pr.cells tv.cols) →
        ∃ wVal, evalWindowComputeCell tv.cols item newCol.ty partRows pos = some wVal ∧ ValWf prog wVal wTy.toTy := by
      intro partRows pos hpartWf
      unfold evalWindowComputeCell
      unfold windowFnSpec? at hfnSpec; dsimp only [newCol] at hfnSpec ⊢
      cases hfn : item.fn <;> (rw [hfn] at hfnSpec; dsimp only at hfnSpec ⊢)
      case rowNumber =>
        injection hfnSpec with hp; injection hp with hw _; subst hw
        exact ⟨_, rfl, .int (clampInt64Nat_inRange _)⟩
      case rank col =>
        cases hc : tv.cols.find? (fun c => c.name == col) with
        | none => simp [hc] at hfnSpec
        | some c =>
          rw [hc] at hfnSpec; dsimp only at hfnSpec; split at hfnSpec <;> try contradiction
          injection hfnSpec with hp; injection hp with hw _; subst hw
          rcases lookupColIdx?_of_find? hc with ⟨cIdx, hlook, _⟩
          simp only [hlook, bind, Option.bind]
          cases hpr : partRows[pos]? with
          | none => exact ⟨.int 1, rfl, .int (by decide)⟩
          | some curRow =>
            dsimp only
            cases hcell : curRow.cells[cIdx]? with
            | none => exact ⟨.int 1, rfl, .int (by decide)⟩
            | some _ => exact ⟨_, rfl, .int (clampInt64Nat_inRange _)⟩
      case lag col offset =>
        cases hc : tv.cols.find? (fun c => c.name == col) with
        | none => simp [hc] at hfnSpec
        | some c =>
          rw [hc] at hfnSpec; dsimp only at hfnSpec; injection hfnSpec with hp; injection hp with hw _; subst hw
          have hsnd := lookupColIdx?_snd_eq_find? tv.cols col; rw [hc] at hsnd
          cases hlook : lookupColIdx? tv.cols col with
          | none => rw [hlook] at hsnd; nomatch hsnd
          | some pair =>
            rcases pair with ⟨cIdx, cSpec⟩
            rw [hlook] at hsnd; dsimp only [Option.map] at hsnd; injection hsnd with hcs; subst cSpec
            rcases lookupColIdx?_props hlook with ⟨hgetCol, _⟩
            have hcVal := (hcols c (List.mem_of_find?_eq_some hc)).1
            simp only [bind, Option.bind]
            split
            · exact ⟨.optNone, rfl, optNone_ensureOption_sound c.ty⟩
            · cases hpr : partRows[pos - offset]? with
              | none => exact ⟨.optNone, rfl, optNone_ensureOption_sound c.ty⟩
              | some prevRow =>
                dsimp only
                have hprevWf := hpartWf prevRow (List.mem_of_getElem? hpr)
                rcases hprevWf.getElem?_wf hgetCol with ⟨pv, hpv, hpvWf⟩
                simp only [hpv]
                exact ⟨_, rfl, wrapIntoOptionVal_sound hcVal hpvWf⟩
      case lead col offset =>
        cases hc : tv.cols.find? (fun c => c.name == col) with
        | none => simp [hc] at hfnSpec
        | some c =>
          rw [hc] at hfnSpec; dsimp only at hfnSpec; injection hfnSpec with hp; injection hp with hw _; subst hw
          have hsnd := lookupColIdx?_snd_eq_find? tv.cols col; rw [hc] at hsnd
          cases hlook : lookupColIdx? tv.cols col with
          | none => rw [hlook] at hsnd; nomatch hsnd
          | some pair =>
            rcases pair with ⟨cIdx, cSpec⟩
            rw [hlook] at hsnd; dsimp only [Option.map] at hsnd; injection hsnd with hcs; subst cSpec
            rcases lookupColIdx?_props hlook with ⟨hgetCol, _⟩
            have hcVal := (hcols c (List.mem_of_find?_eq_some hc)).1
            simp only [bind, Option.bind]
            cases hnr : partRows[pos + offset]? with
            | none => exact ⟨.optNone, rfl, optNone_ensureOption_sound c.ty⟩
            | some nextRow =>
              dsimp only
              have hnextWf := hpartWf nextRow (List.mem_of_getElem? hnr)
              rcases hnextWf.getElem?_wf hgetCol with ⟨nv, hnv, hnvWf⟩
              simp only [hnv]
              exact ⟨_, rfl, wrapIntoOptionVal_sound hcVal hnvWf⟩
      case runningSum col =>
        cases hc : tv.cols.find? (fun c => c.name == col) with
        | none => simp [hc] at hfnSpec
        | some c =>
          rw [hc] at hfnSpec; dsimp only at hfnSpec
          cases hn : numericCoreOfScalar? c.ty with
          | none => simp [hn] at hfnSpec
          | some nTy =>
            rw [hn] at hfnSpec; dsimp only [Option.map] at hfnSpec; injection hfnSpec with hp; injection hp with hw _; subst hw
            rcases lookupColIdx?_of_find? hc with ⟨cIdx, hlook, hgetCol⟩
            have hcVal := (hcols c (List.mem_of_find?_eq_some hc)).1
            simp only [hlook, bind, Option.bind]
            let vals := (partRows.take (pos + 1)).filterMap (fun pr => pr.cells[cIdx]?)
            have hvalsWf : ∀ v ∈ vals, ValWf prog v c.ty.toTy := by
              intro v hv; rw [List.mem_filterMap] at hv
              rcases hv with ⟨pr, hprTake, hprCell⟩
              have hprMem := List.mem_of_mem_take hprTake
              rcases (hpartWf pr hprMem).getElem?_wf hgetCol with ⟨cell, hcell, hcellWf⟩
              rw [hcell] at hprCell; injection hprCell with hvEq; subst hvEq; exact hcellWf
            have hdefWf : ValWf prog (defaultValForScalar nTy) nTy.toTy := by
              rcases (numericCoreOfScalar?_props hn).2 with rfl | rfl | rfl
              · exact .int (by decide)
              · exact .decimal (by decide)
              · exact .float _
            have hagg := evalAggClean_sound hcVal hvalsWf (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩)))
            cases he : evalAggClean .sum nTy vals with
            | ok v => rw [he] at hagg; cases hagg with | ok hv => exact ⟨v, rfl, hv⟩
            | stopped _ | outOfFuel | wrong => exact ⟨_, rfl, hdefWf⟩
      case rollingMean col wSz =>
        cases hw0 : (wSz == 0) <;> simp only [hw0, Bool.false_eq_true, ↓reduceIte] at hfnSpec
        · cases hc : tv.cols.find? (fun c => c.name == col) with
          | none => simp [hc] at hfnSpec
          | some c =>
            rw [hc] at hfnSpec; dsimp only at hfnSpec; split at hfnSpec <;> try contradiction
            injection hfnSpec with hp; injection hp with hw _; subst hw
            rcases lookupColIdx?_of_find? hc with ⟨cIdx, hlook, _⟩
            simp only [hlook, bind, Option.bind]
            cases hemp : ((((partRows.take (pos + 1)).drop (if pos + 1 ≥ wSz then (pos + 1) - wSz else 0)).filterMap (fun pr => pr.cells[cIdx]?)).filterMap unwrapNumericFloat).isEmpty <;>
              simp only [Bool.false_eq_true, ↓reduceIte]
            · exact ⟨_, rfl, .optSome (.float _)⟩
            · exact ⟨.optNone, rfl, .optNone .float⟩
        · contradiction
    unfold evalWindowOnTable
    rw [hfindTarget]; dsimp only [bind, Option.bind]
    have hbuild : ∀ (rem : List (TableRow × Nat)),
        (∀ p ∈ rem, CellsWf prog p.1.cells tv.cols) →
        ∃ newRows,
          evalWindowOnTable.buildWindowRows tv.cols item.over sortedIndexed
            (lookupColIdx? tv.cols item.name)
            (evalWindowComputeCell tv.cols item newCol.ty) rem = some newRows ∧
          RowsWf prog newRows nextCols false false := by
      intro rem hrem
      induction rem with
      | nil => exact ⟨[], rfl, .nil _ false false⟩
      | cons pair rest ih =>
        rcases pair with ⟨row, origIdx⟩
        have hrowWf : CellsWf prog row.cells tv.cols := hrem (row, origIdx) (.head _)
        rcases extractKeyVals_some hrowWf item.over hoverOk with ⟨myKey, hmyKey⟩
        let partIndexed := windowPartIndexed tv.cols item.over sortedIndexed myKey
        let partRows := partIndexed.map Prod.fst
        have hpartWf : ∀ pr ∈ partRows, CellsWf prog pr.cells tv.cols := by
          intro pr hpr
          rw [List.mem_map] at hpr
          rcases hpr with ⟨p2, hp2, rfl⟩
          exact hsortedWf p2 (List.mem_filter.mp hp2).1
        let posInPart := (partIndexed.findIdx? (fun (_, i2) => i2 == origIdx)).getD 0
        rcases hcompute partRows posInPart hpartWf with ⟨wVal, hwEq, hwWf⟩
        rcases ih (fun p' hp' => hrem p' (.tail _ hp')) with ⟨tlRows, htlEq, htlWf⟩
        have hcellsUpd : CellsWf prog
            (match lookupColIdx? tv.cols item.name with
             | some (idx, _) => row.cells.set idx wVal
             | none => row.cells ++ [wVal]) nextCols := by
          rw [hnextEq]
          cases hlook : lookupColIdx? tv.cols item.name with
          | none =>
            have hfNone := (lookupColIdx?_none_iff_find?_none tv.cols item.name).mp hlook
            simp only [hfNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            exact hrowWf.append (.cons hwWf .nil)
          | some p =>
            rcases p with ⟨idx, _⟩
            have hfSome : (tv.cols.find? (fun c => c.name == item.name)).isSome = true := by
              cases hf : tv.cols.find? (fun c => c.name == item.name) with
              | some _ => rfl
              | none =>
                have := (lookupColIdx?_none_iff_find?_none tv.cols item.name).mpr hf
                rw [hlook] at this; nomatch this
            simp only [hfSome, ↓reduceIte]
            apply cellsWf_set_by_name (fun c => if c.name == item.name then newCol else c) huniq hlook hrowWf
            intro c _
            split
            · exact hwWf
            · rfl
        unfold evalWindowOnTable.buildWindowRows
        rw [hmyKey]; dsimp only [bind, Option.bind]
        dsimp only [partRows, partIndexed, posInPart] at hwEq
        rw [hwEq]; dsimp only [bind, Option.bind]
        rw [htlEq]; dsimp only [bind, Option.bind]
        exact ⟨_, rfl, .cons hcellsUpd (fun h => by simp at h) htlWf⟩
    rcases hbuild indexedRows hindexedWf with ⟨newRows, hbEq, hbWf⟩
    dsimp only [sortedIndexed, indexedRows, newCol] at hbEq ⊢
    rw [hbEq]; dsimp only [bind, Option.bind]
    exact ⟨{ cols := nextCols, rows := newRows }, rfl, rfl, hbWf⟩

theorem windowFnSpec?_cols_congr {c1 c2 : List ColSpec} {ot : TagSet} {w : WindowItem}
    {wTy : ScalarTy} {ts1 : TagSet}
    (hfindEq : ∀ (k : Ident),
      (c2.find? (fun c => c.name == k)).map (fun c => (c.name, c.ty)) =
        (c1.find? (fun c => c.name == k)).map (fun c => (c.name, c.ty)))
    (hfs1 : windowFnSpec? c1 ot w = some (wTy, ts1)) :
    ∃ ts2, windowFnSpec? c2 ot w = some (wTy, ts2) := by
  unfold windowFnSpec? at hfs1 ⊢
  dsimp only at hfs1 ⊢
  cases hwfn : w.fn <;> simp only [hwfn] at hfs1 ⊢
  case rowNumber =>
    injection hfs1 with hp; injection hp with hwt _; subst hwt; exact ⟨_, rfl⟩
  case rank col =>
    have hf := hfindEq col
    cases hc1 : c1.find? (fun c => c.name == col) <;> cases hc2 : c2.find? (fun c => c.name == col) <;> simp [hc1, hc2] at hf hfs1 ⊢
    rw [hf.2]; simp [hfs1.1, hfs1.2.1]
  case lag col _ =>
    have hf := hfindEq col
    cases hc1 : c1.find? (fun c => c.name == col) <;> cases hc2 : c2.find? (fun c => c.name == col) <;> simp [hc1, hc2] at hf hfs1 ⊢
    rw [hf.2]; exact hfs1.1
  case lead col _ =>
    have hf := hfindEq col
    cases hc1 : c1.find? (fun c => c.name == col) <;> cases hc2 : c2.find? (fun c => c.name == col) <;> simp [hc1, hc2] at hf hfs1 ⊢
    rw [hf.2]; exact hfs1.1
  case runningSum col =>
    have hf := hfindEq col
    cases hc1 : c1.find? (fun c => c.name == col) <;> cases hc2 : c2.find? (fun c => c.name == col) <;> simp [hc1, hc2] at hf hfs1 ⊢
    rw [hf.2]; cases hn : numericCoreOfScalar? _ <;> simp [hn] at hfs1 ⊢
    exact hfs1.1
  case rollingMean col wSz =>
    have hf := hfindEq col
    cases hwz : (wSz == 0) <;> simp [hwz] at hfs1 ⊢
    cases hc1 : c1.find? (fun c => c.name == col) <;> cases hc2 : c2.find? (fun c => c.name == col) <;> simp [hc1, hc2] at hf hfs1 ⊢
    rw [hf.2]; simp [hfs1.1, hfs1.2.1]

theorem evalWindowItems_sound {prog : Program} {ot : TagSet} :
    ∀ (items : List WindowItem) (curTV : TableVal) (outCols : List ColSpec),
      distinctIdents (curTV.cols.map ColSpec.name) = true →
      (∀ c ∈ curTV.cols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
      RowsWf prog curTV.rows curTV.cols false false →
      applyWindowItems ot curTV.cols items = .ok outCols →
      ∃ winTV, evalWindowItems curTV items = some winTV ∧
        RowsWf prog winTV.rows outCols false false ∧
        (∀ c ∈ outCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
  | [], curTV, outCols, _, hcols, hrows, happly => by
    unfold applyWindowItems at happly; injection happly with h'; subst h'
    exact ⟨curTV, rfl, hrows, hcols⟩
  | it :: rest, curTV, outCols, huniq, hcols, hrows, happly => by
    unfold applyWindowItems at happly; simp only [bind, Except.bind] at happly
    cases hstep : applyWindowItem curTV.cols ot it with
    | error _ => simp [hstep] at happly
    | ok next1 =>
      simp only [hstep] at happly
      rcases applyWindowItem_props TagSet.empty huniq hcols hstep with
        ⟨next2, hstepEmpty, hnamesEq, htysEq, huniq1, hprops1, hprops2⟩
      rcases evalWindowOnTable_sound huniq hcols hrows hstepEmpty with ⟨nextTV, hevWin, hnextTVCols, hnextRows⟩
      have hItemsCongr : ∀ (rem : List WindowItem) (c1 c2 oc1 : List ColSpec),
          c2.map ColSpec.name = c1.map ColSpec.name →
          c2.map ColSpec.ty = c1.map ColSpec.ty →
          distinctIdents (c1.map ColSpec.name) = true →
          (∀ c ∈ c1, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
          (∀ c ∈ c2, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
          applyWindowItems ot c1 rem = .ok oc1 →
          ∃ oc2, applyWindowItems ot c2 rem = .ok oc2 ∧ oc2.map ColSpec.ty = oc1.map ColSpec.ty ∧
            (∀ c ∈ oc1, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) := by
        intro rem
        induction rem with
        | nil =>
          intro c1 c2 oc1 _ htEq _ hp1 _ ha1
          unfold applyWindowItems at ha1; injection ha1 with h'; subst h'
          exact ⟨c2, rfl, htEq, hp1⟩
        | cons w wRest ihw =>
          intro c1 c2 oc1 hnEq htEq hu1 hp1 hp2 ha1
          unfold applyWindowItems at ha1 ⊢; simp only [bind, Except.bind] at ha1 ⊢
          cases hs1 : applyWindowItem c1 ot w with
          | error _ => simp [hs1] at ha1
          | ok m1 =>
            simp only [hs1] at ha1
            have hfindEq : ∀ (k : Ident),
                (c2.find? (fun c => c.name == k)).map (fun c => (c.name, c.ty)) =
                  (c1.find? (fun c => c.name == k)).map (fun c => (c.name, c.ty)) := by
              intro k
              clear ha1 hs1 hp1 hp2 hu1
              induction c1 generalizing c2 with
              | nil =>
                cases c2 with
                | nil => rfl
                | cons _ _ => simp at hnEq
              | cons d1 ds1 ihc =>
                cases c2 with
                | nil => simp at hnEq
                | cons d2 ds2 =>
                  simp only [List.map_cons, List.cons.injEq] at hnEq htEq
                  simp only [List.find?, hnEq.1]
                  cases hdk : (d1.name == k)
                  · dsimp only; exact ihc ds2 hnEq.2 htEq.2
                  · simp only [Option.map_some, hnEq.1, htEq.1]
            have hstep2 : ∃ m2, applyWindowItem c2 ot w = .ok m2 ∧
                m2.map ColSpec.name = m1.map ColSpec.name ∧ m2.map ColSpec.ty = m1.map ColSpec.ty := by
              have hs1Save := hs1
              rw [applyWindowItem_eq] at hs1Save ⊢
              have hoverEq : w.over.all (fun k => (c2.find? (fun c => c.name == k)).isSome) =
                  w.over.all (fun k => (c1.find? (fun c => c.name == k)).isSome) := by
                apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
                constructor
                · intro hall k hk
                  have h0 := hall k hk
                  have hf := hfindEq k
                  cases hc2 : c2.find? (fun c => c.name == k) <;> cases hc1 : c1.find? (fun c => c.name == k) <;> simp [hc1, hc2] at hf h0 ⊢
                · intro hall k hk
                  have h0 := hall k hk
                  have hf := hfindEq k
                  cases hc2 : c2.find? (fun c => c.name == k) <;> cases hc1 : c1.find? (fun c => c.name == k) <;> simp [hc1, hc2] at hf h0 ⊢
              have hordEq : w.order.all (fun (k, _) => match c2.find? (fun c => c.name == k) with | some c => isOrderedScalarTy (baseOfScalar c.ty).toTy | none => false) =
                  w.order.all (fun (k, _) => match c1.find? (fun c => c.name == k) with | some c => isOrderedScalarTy (baseOfScalar c.ty).toTy | none => false) := by
                apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
                constructor
                · intro hall p hp
                  rcases p with ⟨k, dir⟩
                  have h0 := hall (k, dir) hp
                  have hf := hfindEq k
                  cases hc2 : c2.find? (fun c => c.name == k) <;> cases hc1 : c1.find? (fun c => c.name == k) <;> simp [hc1, hc2] at hf h0 ⊢
                  rw [← hf.2]; exact h0
                · intro hall p hp
                  rcases p with ⟨k, dir⟩
                  have h0 := hall (k, dir) hp
                  have hf := hfindEq k
                  cases hc2 : c2.find? (fun c => c.name == k) <;> cases hc1 : c1.find? (fun c => c.name == k) <;> simp [hc1, hc2] at hf h0 ⊢
                  rw [hf.2]; exact h0
              rw [hoverEq, hordEq]
              split at hs1Save
              · contradiction
              · rename_i hnotBad
                simp only [hnotBad, Bool.false_eq_true, ↓reduceIte]
                cases hfs1 : windowFnSpec? c1 ot w with
                | none => rw [hfs1] at hs1Save; simp at hs1Save
                | some p1 =>
                  rcases p1 with ⟨wTy, ts1⟩
                  rw [hfs1] at hs1Save; dsimp only at hs1Save
                  rcases windowFnSpec?_cols_congr hfindEq hfs1 with ⟨ts2, hfs2⟩
                  rw [hfs2]; dsimp only
                  have hisSomeEq : (c2.find? (fun c => c.name == w.name)).isSome = (c1.find? (fun c => c.name == w.name)).isSome := by
                    have hf := hfindEq w.name
                    cases hc2 : c2.find? (fun c => c.name == w.name) <;> cases hc1 : c1.find? (fun c => c.name == w.name) <;> simp [hc1, hc2] at hf ⊢
                  rw [hisSomeEq]
                  cases his : (c1.find? (fun c => c.name == w.name)).isSome
                  · simp only [his, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hs1Save ⊢
                    subst hs1Save
                    exact ⟨_, rfl, by simp [hnEq], by simp [htEq]⟩
                  · simp only [his, ↓reduceIte, Except.ok.injEq] at hs1Save ⊢
                    subst hs1Save
                    refine ⟨_, rfl, ?_, ?_⟩
                    · clear ha1 hs1 hfs1 hfs2 hoverEq hordEq his hisSomeEq hfindEq hnotBad hp1 hp2 hu1
                      induction c1 generalizing c2 with
                      | nil =>
                        cases c2 with
                        | nil => rfl
                        | cons _ _ => simp at hnEq
                      | cons d1 ds1 ihc =>
                        cases c2 with
                        | nil => simp at hnEq
                        | cons d2 ds2 =>
                          simp only [List.map_cons, List.cons.injEq] at hnEq htEq
                          rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ihc ds2 hnEq.2 htEq.2]
                          simp only [hnEq.1]
                          cases (d1.name == w.name)
                          · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; exact hnEq.1
                          · rfl
                    · clear ha1 hs1 hfs1 hfs2 hoverEq hordEq his hisSomeEq hfindEq hnotBad hp1 hp2 hu1
                      induction c1 generalizing c2 with
                      | nil =>
                        cases c2 with
                        | nil => rfl
                        | cons _ _ => simp at hnEq
                      | cons d1 ds1 ihc =>
                        cases c2 with
                        | nil => simp at hnEq
                        | cons d2 ds2 =>
                          simp only [List.map_cons, List.cons.injEq] at hnEq htEq
                          rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ihc ds2 hnEq.2 htEq.2]
                          simp only [hnEq.1]
                          cases (d1.name == w.name)
                          · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; exact htEq.1
                          · rfl
            rcases hstep2 with ⟨m2, hs2, hmNames, hmTys⟩
            rw [hs2]; dsimp only
            have hu2 : distinctIdents (c2.map ColSpec.name) = true := by rw [hnEq]; exact hu1
            rcases applyWindowItem_props ot hu1 hp1 hs1 with ⟨_, _, _, _, hmu1, hmp1, _⟩
            rcases applyWindowItem_props ot hu2 hp2 hs2 with ⟨_, _, _, _, _, hmp2, _⟩
            exact ihw m1 m2 oc1 hmNames hmTys hmu1 hmp1 hmp2 ha1
      rcases hItemsCongr rest next1 next2 outCols hnamesEq htysEq huniq1 hprops1 hprops2 happly with
        ⟨outCols2, happly2, houtTysEq, houtProps⟩
      rw [← hnextTVCols] at hnextRows hprops2 happly2
      have huniqNextTV : distinctIdents (nextTV.cols.map ColSpec.name) = true := by
        rw [hnextTVCols, hnamesEq]; exact huniq1
      rcases evalWindowItems_sound rest nextTV outCols2 huniqNextTV hprops2 hnextRows happly2 with
        ⟨winTV, hevRest, hwinRows2, _⟩
      unfold evalWindowItems
      have htoOpt : (applyWindowItem curTV.cols TagSet.empty it).toOption = some next2 := by
        simp [hstepEmpty, Except.toOption]
      simp only [htoOpt, hevWin, hevRest, bind, Option.bind]
      have hrowsCast : RowsWf prog winTV.rows outCols false false :=
        RowsWf.of_forall_raw (fun r hr => (hwinRows2.to_forall r hr).congr_ty houtTysEq)
      exact ⟨winTV, rfl, hrowsCast, houtProps⟩

theorem mapPseudonymizeRows_sound {prog : Program} {pc : TagSet} (keyMat : String) {cols outCols : List ColSpec}
    {cIdx : Nat} {origCol : ColSpec} {col : Ident}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hlook : lookupColIdx? cols col = some (cIdx, origCol))
    (houtCols : outCols = cols.map (fun c =>
      if c.name == col then { c with ty := .text, tags := (c.tags.remove "pii").union pc, bucketed := false, aggKind := .raw }
      else { c with aggKind := .raw })) :
    ∀ (rows : List TableRow),
      (∀ r ∈ rows, CellsWf prog r.cells cols) →
      ∃ outRows, mapPseudonymizeRows keyMat cIdx rows = some outRows ∧
        RowsWf prog outRows outCols false false
  | [], _ => ⟨[], rfl, .nil _ false false⟩
  | r :: rs, hrs => by
    have hrWf := hrs r (.head _)
    rcases lookupColIdx?_props hlook with ⟨hgetCol, _⟩
    rcases hrWf.getElem?_wf hgetCol with ⟨origVal, hgetCell, _⟩
    rcases mapPseudonymizeRows_sound (pc := pc) keyMat huniq hlook houtCols rs
      (fun r' hr' => hrs r' (.tail _ hr')) with ⟨tlRows, htlEq, htlWf⟩
    unfold mapPseudonymizeRows
    simp only [hgetCell, htlEq, bind, Option.bind]
    have hsetWf : CellsWf prog (r.cells.set cIdx (.text (pseudonymizeToken keyMat origVal))) outCols := by
      rw [houtCols]
      apply cellsWf_set_by_name _ huniq hlook hrWf
      intro c _
      split
      · exact .text _
      · rfl
    exact ⟨_, rfl, .cons hsetWf (fun h => by simp at h) htlWf⟩

/-! ## Sequential Evaluation Soundness & Mutual Fuel Induction -/

theorem evalSeq_sound {prog : Program} {tEnv : TyEnv} {pc : TagSet} {inSpec : Bool}
    (step : World → Expr → Outcome)
    (hstep : ∀ w e eLTy, WorldWf prog w →
      checkExpr prog tEnv [] pc inSpec e = .ok eLTy →
      OutcomeWf prog [] eLTy.ty (step w e)) :
    ∀ {args : List Expr} {argLTys : List LTy} {w : World},
      WorldWf prog w →
      checkExprList prog tEnv pc inSpec args = .ok argLTys →
      match evalSeq step w args with
      | .ok vs w1 => ValListWf prog vs argLTys ∧ WorldWf prog w1
      | .aborted out => ∀ jenv anyTy, OutcomeWf prog jenv anyTy out
  | [], _, w, hw, hchk => by
    unfold checkExprList at hchk; injection hchk with h'; subst h'
    exact ⟨.nil, hw⟩
  | e :: es, _, w, hw, hchk => by
    unfold checkExprList at hchk; simp only [bind, Except.bind] at hchk
    cases he : checkExpr prog tEnv [] pc inSpec e with
    | error _ => simp [he] at hchk
    | ok hdLTy =>
      simp only [he] at hchk
      cases hes : checkExprList prog tEnv pc inSpec es with
      | error _ => simp [hes] at hchk
      | ok tlLTys =>
        simp only [hes, Except.ok.injEq] at hchk; subst hchk
        unfold evalSeq
        have hhdOut := hstep w e hdLTy hw he
        cases hs1 : step w e with
        | stopped b w1 => dsimp only; rw [hs1] at hhdOut; cases hhdOut with | stopped _ hw1 => intro _ _; exact .stopped b hw1
        | failed m w1 => dsimp only; rw [hs1] at hhdOut; cases hhdOut with | failed _ hw1 => intro _ _; exact .failed m hw1
        | outOfFuel => dsimp only; intro _ _; exact .outOfFuel
        | jumped _ _ _ => exact absurd hs1 hhdOut.not_jumped_nil
        | wrong => rw [hs1] at hhdOut; nomatch hhdOut
        | ok v w1 =>
          dsimp only
          rw [hs1] at hhdOut; cases hhdOut with | ok hv hw1 =>
          have ih := evalSeq_sound step hstep hw1 hes
          cases hs2 : evalSeq step w1 es with
          | aborted out => dsimp only; rw [hs2] at ih; exact ih
          | ok vs w2 =>
            dsimp only
            rw [hs2] at ih
            exact ⟨.cons hv ih.1, ih.2⟩

theorem EnvWf.append {prog : Program} :
    ∀ {e1 e2 : Env}, EnvWf prog e1 → EnvWf prog e2 → EnvWf prog (e1 ++ e2)
  | [], _, .nil, h2 => h2
  | _ :: _, _, .cons hv htl, h2 => .cons hv (htl.append h2)

theorem EnvWf.reverse {prog : Program} :
    ∀ {e : Env}, EnvWf prog e → EnvWf prog e.reverse
  | [], .nil => .nil
  | _ :: _, .cons hv htl => by
    rw [List.reverse_cons]
    exact htl.reverse.append (.cons hv .nil)

theorem extendEnv_rev_wf {prog : Program} {params : List (Ident × LTy)} {vs : List Val}
    (hvs : ValListWf prog vs (params.map Prod.snd)) :
    let callEnv : Env := (List.zip params vs).reverse.map
      (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v })
    EnvWf prog callEnv ∧ envToTyEnv callEnv = params.reverse := by
  have hlen : vs.length = params.length := by
    have h0 := hvs.length_eq
    simpa using h0
  have hewd := extendEnv_wf hvs (.nil : EnvWf prog [])
  rw [List.append_nil] at hewd
  have hmapRev : (List.zip params vs).reverse.map (fun ((pName, pLTy), v) => ({ name := pName, lty := pLTy, val := v } : EnvEntry)) =
      ((List.zip params vs).map (fun ((pName, pLTy), v) => ({ name := pName, lty := pLTy, val := v } : EnvEntry))).reverse := by
    simp [List.map_reverse]
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [hmapRev]
    exact hewd.reverse
  · dsimp only
    rw [hmapRev, envToTyEnv_reverse, envToTyEnv_zip_params params vs hlen]

theorem valListWf_of_zip_tyEq {prog : Program} :
    ∀ {vs : List Val} {as1 bs1 : List LTy},
      ValListWf prog vs as1 →
      as1.length = bs1.length →
      (∀ p ∈ List.zip as1 bs1, p.1.ty = p.2.ty) →
      ValListWf prog vs bs1
  | [], [], [], .nil, _, _ => .nil
  | _ :: _, _ :: asTl, _ :: bsTl, .cons hv htl, hlen, hall => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hhd : _ = _ := hall (_, _) (.head _)
    exact .cons (hhd ▸ hv) (valListWf_of_zip_tyEq htl hlen (fun p hp => hall p (.tail _ hp)))
  | _, _ :: _, [], _, hlen, _ => by simp at hlen
  | _, [], _ :: _, _, hlen, _ => by simp at hlen

def RowExprSoundAt (fuel : Nat) (prog : Program) : Prop :=
  checkProgram prog = .ok () →
  ∀ env cols row re sTy rTags,
    EnvWf prog env →
    (∀ c ∈ cols, validScalarTy prog c.ty = true) →
    CellsWf prog row.cells cols →
    checkRowExpr prog (envToTyEnv env) cols re = .ok (sTy, rTags) →
    PrimResultWf prog sTy.toTy (evalRowExpr fuel prog env cols row re)

def RowExprListSoundAt (fuel : Nat) (prog : Program) : Prop :=
  checkProgram prog = .ok () →
  ∀ env cols row rs pairs,
    EnvWf prog env →
    (∀ c ∈ cols, validScalarTy prog c.ty = true) →
    CellsWf prog row.cells cols →
    checkRowExprList prog (envToTyEnv env) cols rs = .ok pairs →
    RowListResultWf prog (pairs.map (fun (st, ts) => LTy.mk st.toTy ts))
      (evalRowExprList fuel prog env cols row rs)

def ExprSoundAt (fuel : Nat) (prog : Program) : Prop :=
  checkProgram prog = .ok () →
  ∀ env jenv pc inSpec w e lty,
    EnvWf prog env →
    WorldWf prog w →
    checkExpr prog (envToTyEnv env) jenv pc inSpec e = .ok lty →
    OutcomeWf prog jenv lty.ty (eval fuel prog env pc w e)

def JoinLoopSoundAt (fuel : Nat) (prog : Program) : Prop :=
  checkProgram prog = .ok () →
  ∀ baseEnv curEnv jenv label params joinPc retLTy rLTy inSpec rhs w,
    EnvWf prog baseEnv →
    EnvWf prog curEnv →
    envToTyEnv curEnv = extendTyEnv (envToTyEnv baseEnv) params →
    WorldWf prog w →
    checkExpr prog (extendTyEnv (envToTyEnv baseEnv) params)
      ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
      joinPc inSpec rhs = .ok rLTy →
    rLTy.ty = retLTy.ty →
    OutcomeWf prog jenv retLTy.ty
      (evalJoinLoop fuel prog baseEnv label params joinPc rhs curEnv w)

def PlanSoundAt (fuel : Nat) (prog : Program) : Prop :=
  checkProgram prog = .ok () →
  ∀ env pc inSpec w plan pTy,
    EnvWf prog env →
    WorldWf prog w →
    checkPlan prog (envToTyEnv env) pc inSpec plan = .ok pTy →
    OutcomeWf prog [] (pTy.toLTy pc).ty (evalPlan fuel prog env pc w plan)

theorem eval_fuel_sound (prog : Program) :
    ∀ (fuel : Nat),
      RowExprSoundAt fuel prog ∧
      RowExprListSoundAt fuel prog ∧
      ExprSoundAt fuel prog ∧
      JoinLoopSoundAt fuel prog ∧
      PlanSoundAt fuel prog
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ _ _ _ _; unfold evalRowExpr; exact .outOfFuel
    · intro _ _ _ _ rs pairs _ _ _ hchk
      cases rs with
      | nil =>
        unfold checkRowExprList at hchk; injection hchk with h'; subst h'
        unfold evalRowExprList; exact .ok .nil
      | cons _ _ => unfold evalRowExprList; exact .outOfFuel _
    · intro _ _ _ _ _ _ _ _ _ _ _; unfold eval; exact .outOfFuel
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; unfold evalJoinLoop; exact .outOfFuel
    · intro _ _ _ _ _ _ _ _ _ _; unfold evalPlan; exact .outOfFuel
  | fuel' + 1 => by
    rcases eval_fuel_sound prog fuel' with ⟨ihRE, ihREL, ihE, ihJL, ihP⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- Part A: RowExprSoundAt (fuel' + 1)
    · intro hprog env cols row re sTy rTags henv hcols hrow hchk
      unfold evalRowExpr
      cases re with
      | lit v =>
        dsimp only
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases hl : checkLiteral prog TagSet.empty v with
        | error _ => simp [hl] at hchk
        | ok lty =>
          simp only [hl] at hchk
          cases hs : lty.ty.toScalarTy? with
          | none => simp [hs] at hchk
          | some st =>
            simp only [hs] at hchk; split at hchk <;> try contradiction
            injection hchk with hp; injection hp with hst _; subst hst
            rw [Ty.toScalarTy?_some_imp hs]
            exact .ok (checkLiteral_sound hl)
      | col name =>
        dsimp only
        unfold checkRowExpr at hchk
        cases hf : cols.find? (fun c => c.name == name) with
        | none => simp [hf] at hchk
        | some c =>
          simp only [hf] at hchk
          injection hchk with hp; injection hp with hst _; subst hst
          rcases lookupColIdx?_of_find? hf with ⟨idx, hlook, hgetCol⟩
          rcases hrow.getElem?_wf hgetCol with ⟨cell, hgetCell, hcellWf⟩
          simp only [hlook, hgetCell]; exact .ok hcellWf
      | outerVar name =>
        dsimp only
        unfold checkRowExpr at hchk
        cases hl : lookupTyEnv (envToTyEnv env) name with
        | none => simp [hl] at hchk
        | some lty =>
          simp only [hl] at hchk
          cases hs : lty.ty.toScalarTy? with
          | none => simp [hs] at hchk
          | some st =>
            simp only [hs] at hchk; split at hchk <;> try contradiction
            injection hchk with hp; injection hp with hst _; subst hst
            rcases lookupEnv_of_envWf henv hl with ⟨v, hlookEnv, hvWf⟩
            simp only [hlookEnv]
            rw [Ty.toScalarTy?_some_imp hs]; exact .ok hvWf
      | constRef name =>
        dsimp only
        unfold checkRowExpr at hchk
        cases hc : prog.findConst? name with
        | none => simp [hc] at hchk
        | some cDecl =>
          simp only [hc] at hchk
          cases hs : cDecl.lty.ty.toScalarTy? with
          | none => simp [hs] at hchk
          | some st =>
            simp only [hs] at hchk; split at hchk <;> try contradiction
            injection hchk with hp; injection hp with hst _; subst hst
            dsimp only
            rw [Ty.toScalarTy?_some_imp hs]
            exact .ok (checkConst_sound hprog hc)
      | prim op args =>
        dsimp only
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases ha : checkRowExprList prog (envToTyEnv env) cols args with
        | error _ => simp [ha] at hchk
        | ok pairs =>
          simp only [ha] at hchk
          cases hp : checkPrimOp prog TagSet.empty op (pairs.map (fun (st, ts) => LTy.mk st.toTy ts)) with
          | error _ => simp [hp] at hchk
          | ok resLTy =>
            simp only [hp] at hchk
            cases hs : resLTy.ty.toScalarTy? with
            | none => simp [hs] at hchk
            | some st =>
              simp only [hs] at hchk; split at hchk <;> try contradiction
              injection hchk with hpair; injection hpair with hst _; subst hst
              have hargsWf := ihREL hprog env cols row args pairs henv hcols hrow ha
              cases hrl : evalRowExprList fuel' prog env cols row args with
              | stopped b => exact .stopped b
              | outOfFuel => exact .outOfFuel
              | wrong => rw [hrl] at hargsWf; nomatch hargsWf
              | ok vs =>
                rw [hrl] at hargsWf; cases hargsWf with | ok hvs =>
                rw [Ty.toScalarTy?_some_imp hs]
                exact evalPrimOp_sound hp hvs
      | ifE cond tBr eBr =>
        dsimp only
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases hc : checkRowExpr prog (envToTyEnv env) cols cond with
        | error _ => simp [hc] at hchk
        | ok cp =>
          simp only [hc] at hchk
          cases ht : checkRowExpr prog (envToTyEnv env) cols tBr with
          | error _ => simp [ht] at hchk
          | ok tp =>
            simp only [ht] at hchk
            cases he : checkRowExpr prog (envToTyEnv env) cols eBr with
            | error _ => simp [he] at hchk
            | ok ep =>
              simp only [he] at hchk
              split at hchk <;> try contradiction
              rename_i htypes
              simp only [Bool.and_eq_true, decide_eq_true_eq] at htypes
              injection hchk with hp; injection hp with hst _; subst hst
              have hcWf := ihRE hprog env cols row cond cp.1 cp.2 henv hcols hrow hc
              rw [htypes.1] at hcWf
              cases hcv : evalRowExpr fuel' prog env cols row cond with
              | stopped b => exact .stopped b
              | outOfFuel => exact .outOfFuel
              | wrong => rw [hcv] at hcWf; nomatch hcWf
              | ok v =>
                rw [hcv] at hcWf; cases hcWf with | ok hvb =>
                cases hvb with | bool b =>
                cases b
                · rw [htypes.2]; exact ihRE hprog env cols row eBr ep.1 ep.2 henv hcols hrow he
                · exact ihRE hprog env cols row tBr tp.1 tp.2 henv hcols hrow ht
      | coalesce optE defE =>
        dsimp only
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases ho : checkRowExpr prog (envToTyEnv env) cols optE with
        | error _ => simp [ho] at hchk
        | ok op =>
          rcases op with ⟨oTy, oTags⟩
          simp only [ho] at hchk
          cases hd : checkRowExpr prog (envToTyEnv env) cols defE with
          | error _ => simp [hd] at hchk
          | ok dp =>
            rcases dp with ⟨dTy, dTags⟩
            simp only [hd] at hchk
            cases oTy <;> try contradiction
            case option inner =>
              dsimp only at hchk
              split at hchk <;> try contradiction
              rename_i hinnerEq
              have heq := of_decide_eq_true hinnerEq; subst inner
              injection hchk with hp; injection hp with hst _; subst hst
              have hoWf := ihRE hprog env cols row optE (.option dTy) oTags henv hcols hrow ho
              cases hov : evalRowExpr fuel' prog env cols row optE with
              | stopped b => exact .stopped b
              | outOfFuel => exact .outOfFuel
              | wrong => rw [hov] at hoWf; nomatch hoWf
              | ok v =>
                rw [hov] at hoWf; cases hoWf with | ok hvo =>
                cases hvo with
                | optNone => exact ihRE hprog env cols row defE dTy dTags henv hcols hrow hd
                | optSome hu => exact .ok hu
      | callPure fnName args =>
        dsimp only
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases ha : checkRowExprList prog (envToTyEnv env) cols args with
        | error _ => simp [ha] at hchk
        | ok pairs =>
          simp only [ha] at hchk
          cases hf : prog.findFun? fnName with
          | none => simp [hf] at hchk
          | some fDecl =>
            simp only [hf] at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i harityOk
            split at hchk <;> try contradiction
            rename_i hsigOk
            cases hs : fDecl.ret.ty.toScalarTy? with
            | none => simp [hs] at hchk
            | some retSTy =>
              simp only [hs] at hchk; split at hchk <;> try contradiction
              injection hchk with hp; injection hp with hst _; subst hst
              have hargsWf := ihREL hprog env cols row args pairs henv hcols hrow ha
              cases hrl : evalRowExprList fuel' prog env cols row args with
              | stopped b => exact .stopped b
              | outOfFuel => exact .outOfFuel
              | wrong => rw [hrl] at hargsWf; nomatch hargsWf
              | ok vs =>
                rw [hrl] at hargsWf; cases hargsWf with | ok hvs =>
                dsimp only
                simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harityOk
                have hvsLen : vs.length = fDecl.params.length := by
                  have hl := hvs.length_eq
                  simp only [List.length_map] at hl
                  omega
                have hlenNeF : (vs.length != fDecl.params.length) = false := bne_eq_false_iff_eq.mpr hvsLen
                simp only [hlenNeF, Bool.false_eq_true, ↓reduceIte]
                simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hsigOk
                -- Convert `ValListWf prog vs (pairs.map ...)` to `ValListWf prog vs (fDecl.params.map Prod.snd)`
                have hconv : ∀ {vs1 : List Val} {ps1 : List (ScalarTy × TagSet)} {fps : List (Ident × LTy)},
                    ValListWf prog vs1 (ps1.map (fun (st, ts) => LTy.mk st.toTy ts)) →
                    checkRowExpr.checkArgs ps1 fps = true →
                    ValListWf prog vs1 (fps.map Prod.snd) := by
                  intro vs1 ps1 fps hw hca
                  induction ps1 generalizing vs1 fps with
                  | nil =>
                    cases fps with
                    | nil => cases hw; exact .nil
                    | cons _ _ => simp [checkRowExpr.checkArgs] at hca
                  | cons pa pas ihp =>
                    cases fps with
                    | nil => simp [checkRowExpr.checkArgs] at hca
                    | cons fp fpsTl =>
                      cases hw with | cons hv hwtl =>
                      simp only [checkRowExpr.checkArgs, Bool.and_eq_true, decide_eq_true_eq] at hca
                      exact .cons (hca.1.1 ▸ hv) (ihp hwtl hca.2)
                have hvsParams := hconv hvs hsigOk.2
                rcases extendEnv_rev_wf hvsParams with ⟨hcallEnvWf, hcallTyEq⟩
                rcases checkFunDecl_valid hprog hf with ⟨bodyLTy, hbodyChk, hbodyTy⟩
                have hpcEmpty : fDecl.pc = TagSet.empty := by
                  have hem := hsigOk.1
                  cases hpcMk : fDecl.pc with | mk elems inv =>
                  simp only [TagSet.isEmpty, hpcMk, List.isEmpty_iff] at hem
                  subst hem; rfl
                rw [hpcEmpty, ← hcallTyEq] at hbodyChk
                have hevBody := ihE hprog _ [] TagSet.empty fDecl.kind.isSpec {} fDecl.body bodyLTy
                  hcallEnvWf (worldWf_empty prog) hbodyChk
                cases hout : eval fuel' prog _ TagSet.empty {} fDecl.body with
                | stopped b _ => exact .stopped b
                | failed m _ => exact .stopped _
                | outOfFuel => exact .outOfFuel
                | jumped _ _ _ => exact absurd hout hevBody.not_jumped_nil
                | wrong => rw [hout] at hevBody; nomatch hevBody
                | ok v _ =>
                  rw [hout] at hevBody; cases hevBody with | ok hv _ =>
                  rw [Ty.toScalarTy?_some_imp hs, ← hbodyTy]
                  exact .ok hv
    -- Part B: RowExprListSoundAt (fuel' + 1)
    · intro hprog env cols row rs pairs henv hcols hrow hchk
      cases rs with
      | nil =>
        unfold checkRowExprList at hchk; injection hchk with h'; subst h'
        unfold evalRowExprList; exact .ok .nil
      | cons r rest =>
        unfold checkRowExprList at hchk; simp only [bind, Except.bind] at hchk
        unfold evalRowExprList; dsimp only
        cases hr : checkRowExpr prog (envToTyEnv env) cols r with
        | error _ => simp [hr] at hchk
        | ok hdPair =>
          simp only [hr] at hchk
          cases hrest : checkRowExprList prog (envToTyEnv env) cols rest with
          | error _ => simp [hrest] at hchk
          | ok tlPairs =>
            simp only [hrest, Except.ok.injEq] at hchk; subst hchk
            have hhdWf := ihRE hprog env cols row r hdPair.1 hdPair.2 henv hcols hrow hr
            cases he1 : evalRowExpr fuel' prog env cols row r with
            | stopped b => exact .stopped _ b
            | outOfFuel => exact .outOfFuel _
            | wrong => rw [he1] at hhdWf; nomatch hhdWf
            | ok v =>
              rw [he1] at hhdWf; cases hhdWf with | ok hv =>
              have htlWf := ihREL hprog env cols row rest tlPairs henv hcols hrow hrest
              cases he2 : evalRowExprList fuel' prog env cols row rest with
              | stopped b => exact .stopped _ b
              | outOfFuel => exact .outOfFuel _
              | wrong => rw [he2] at htlWf; nomatch htlWf
              | ok vs =>
                rw [he2] at htlWf; cases htlWf with | ok hvs =>
                exact .ok (.cons hv hvs)
    -- Part C: ExprSoundAt (fuel' + 1)
    · intro hprog env jenv pc inSpec w e lty henv hw hchk
      unfold eval
      cases e with
      | lit v =>
        dsimp only
        unfold checkExpr at hchk
        exact .ok (checkLiteral_sound hchk) hw
      | var name =>
        dsimp only
        unfold checkExpr at hchk
        cases hl : lookupTyEnv (envToTyEnv env) name with
        | none => simp [hl] at hchk
        | some vLTy =>
          simp only [hl, Except.ok.injEq] at hchk; subst hchk
          rcases lookupEnv_of_envWf henv hl with ⟨v, hlook, hvWf⟩
          have hty : (vLTy.addTags pc).ty = vLTy.ty := by cases vLTy; rfl
          simp only [hlook, hty]; exact .ok hvWf hw
      | constRef name =>
        dsimp only
        unfold checkExpr at hchk
        cases hc : prog.findConst? name with
        | none => simp [hc] at hchk
        | some cDecl =>
          simp only [hc, Except.ok.injEq] at hchk; subst hchk
          have hty : (cDecl.lty.addTags pc).ty = cDecl.lty.ty := by cases cDecl.lty; rfl
          simp only [hty]; exact .ok (checkConst_sound hprog hc) hw
      | letE name declLTy bound body =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hb : checkExpr prog (envToTyEnv env) [] pc inSpec bound with
        | error _ => simp [hb] at hchk
        | ok bLTy =>
          simp only [hb] at hchk
          split at hchk <;> try contradiction
          rename_i hnotSub
          simp only [Bool.not_eq_true', Bool.not_eq_false, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hnotSub
          have hevB := ihE hprog env [] pc inSpec w bound bLTy henv hw hb
          cases houtB : eval fuel' prog env pc w bound with
          | stopped b w1 => rw [houtB] at hevB; exact hevB.weaken_nil.abort_non_ok (by simp)
          | failed m w1 => rw [houtB] at hevB; exact hevB.weaken_nil.abort_non_ok (by simp)
          | outOfFuel => exact .outOfFuel
          | jumped _ _ _ => exact absurd houtB hevB.not_jumped_nil
          | wrong => rw [houtB] at hevB; nomatch hevB
          | ok bVal w1 =>
            rw [houtB] at hevB; cases hevB with | ok hbWf hw1 =>
            have hdeclTy : (declLTy.addTags pc).ty = bLTy.ty := by
              cases declLTy; exact hnotSub.1.symm
            have henv' : EnvWf prog ({ name := name, lty := declLTy.addTags pc, val := bVal } :: env) :=
              .cons (hdeclTy ▸ hbWf) henv
            exact ihE hprog _ jenv pc inSpec w1 body lty henv' hw1 hchk
      | ifE cond tBr eBr =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hc : checkExpr prog (envToTyEnv env) [] pc inSpec cond with
        | error _ => simp [hc] at hchk
        | ok cLTy =>
          simp only [hc] at hchk
          split at hchk <;> try contradiction
          rename_i hcBool
          have hcTy : cLTy.ty = .bool := of_decide_eq_true hcBool
          cases ht : checkExpr prog (envToTyEnv env) jenv (pc.union cLTy.tags) inSpec tBr with
          | error _ => simp [ht] at hchk
          | ok tLTy =>
            simp only [ht] at hchk
            cases he : checkExpr prog (envToTyEnv env) jenv (pc.union cLTy.tags) inSpec eBr with
            | error _ => simp [he] at hchk
            | ok eLTy =>
              simp only [he] at hchk
              split at hchk <;> try contradiction
              rename_i hteEq
              have hbrEq : tLTy.ty = eLTy.ty := of_decide_eq_true hteEq
              injection hchk with hlty; subst hlty
              have hcTrue := checkExpr_inSpec_true hc
              simp only [hcTrue]
              have hevC := ihE hprog env [] pc inSpec w cond cLTy henv hw hc
              rw [hcTy] at hevC
              cases houtC : eval fuel' prog env pc w cond with
              | stopped b w1 => rw [houtC] at hevC; exact hevC.weaken_nil.abort_non_ok (by simp)
              | failed m w1 => rw [houtC] at hevC; exact hevC.weaken_nil.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtC hevC.not_jumped_nil
              | wrong => rw [houtC] at hevC; nomatch hevC
              | ok cv w1 =>
                rw [houtC] at hevC; cases hevC with | ok hcv hw1 =>
                cases hcv with | bool b =>
                cases b
                · exact (ihE hprog env jenv (pc.union cLTy.tags) inSpec w1 eBr eLTy henv hw1 he).cast_ty hbrEq.symm
                · exact ihE hprog env jenv (pc.union cLTy.tags) inSpec w1 tBr tLTy henv hw1 ht
      | caseE scrut arms =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hs : checkExpr prog (envToTyEnv env) [] pc inSpec scrut with
        | error _ => simp [hs] at hchk
        | ok scrutLTy =>
          simp only [hs] at hchk
          cases hsp : expectedCaseSpecs prog scrutLTy.ty scrutLTy.effectiveTags with
          | error _ => simp [hsp] at hchk
          | ok specs =>
            simp only [hsp] at hchk
            split at hchk <;> try contradiction
            rename_i harmsExhaust
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at harmsExhaust
            cases ha : checkCaseArms prog (envToTyEnv env) jenv (pc.union scrutLTy.effectiveTags) inSpec specs arms with
            | error _ => simp [ha] at hchk
            | ok armLTys =>
              simp only [ha] at hchk
              cases armLTys with
              | nil => simp at hchk
              | cons firstLTy restLTys =>
                dsimp only at hchk
                split at hchk <;> try contradiction
                rename_i hallSameTy
                injection hchk with hlty; subst hlty
                rw [checkExpr_inSpec_true hs]; dsimp only
                have hevS := ihE hprog env [] pc inSpec w scrut scrutLTy henv hw hs
                cases houtS : eval fuel' prog env pc w scrut with
                | stopped b w1 => rw [houtS] at hevS; exact hevS.weaken_nil.abort_non_ok (by simp)
                | failed m w1 => rw [houtS] at hevS; exact hevS.weaken_nil.abort_non_ok (by simp)
                | outOfFuel => exact .outOfFuel
                | jumped _ _ _ => exact absurd houtS hevS.not_jumped_nil
                | wrong => rw [houtS] at hevS; nomatch hevS
                | ok sVal w1 =>
                  dsimp only
                  rw [houtS] at hevS; cases hevS with | ok hsWf hw1 =>
                  rcases matchCaseVal_sound hsWf hsp (armPc := pc.union scrutLTy.effectiveTags) with
                    ⟨cName, fieldLTys, typedVals, hmatch, hspecFind, htvFst, htvWf⟩
                  rw [hmatch]; dsimp only
                  rcases checkCaseArms_props ha with ⟨harmsInSpecs, harmFindProp⟩
                  have hspecsDist := expectedCaseSpecs_distinct hprog hsp
                  have hcInSpecs : cName ∈ specs.map Prod.fst := by
                    have hm := List.mem_of_find?_eq_some hspecFind
                    exact List.mem_map_of_mem hm
                  have hcInArms := pigeonhole_distinct_idents harmsExhaust.1 hspecsDist harmsInSpecs
                    (by simp [harmsExhaust.2]) cName hcInSpecs
                  rcases find?_some_of_mem_ctor arms hcInArms with ⟨binders, armBody, harmFind⟩
                  erw [harmFind]; dsimp only
                  rcases harmFindProp cName binders armBody fieldLTys harmFind hspecFind with
                    ⟨hbindLen, aLTy, haMem, haChk⟩
                  have htvLen : typedVals.length = fieldLTys.length := by
                    have hl := congrArg List.length htvFst
                    simpa using hl
                  have hneF : (binders.length != typedVals.length) = false :=
                    bne_eq_false_iff_eq.mpr (hbindLen.trans htvLen.symm)
                  simp only [hneF, Bool.false_eq_true, ↓reduceIte]
                  rcases envWf_armEntries binders (fieldLTys.map (fun f => f.addTags (pc.union scrutLTy.effectiveTags)))
                    (typedVals.map Prod.snd) typedVals env (by simp [hbindLen]) htvFst rfl htvWf henv with
                    ⟨harmEnvWf, harmTyEq⟩
                  have haTyEq : aLTy.ty = firstLTy.ty := by
                    rcases List.mem_cons.mp haMem with rfl | hrest
                    · rfl
                    · exact of_decide_eq_true ((List.all_eq_true.mp hallSameTy) aLTy hrest)
                  rw [extendTyEnv, ← harmTyEq] at haChk
                  exact (ihE hprog _ jenv (pc.union scrutLTy.effectiveTags) inSpec w1 armBody aLTy
                    harmEnvWf hw1 haChk).cast_ty haTyEq
      | lam params fnPc retLTy body =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hb : checkExpr prog (extendTyEnv (envToTyEnv env) params) [] fnPc inSpec body with
        | error _ => simp [hb] at hchk
        | ok bodyLTy =>
          simp only [hb] at hchk
          split at hchk <;> try contradiction
          rename_i hsub
          injection hchk with hlty; subst hlty
          exact .ok (.closure henv (checkExpr_inSpec_true hb) hsub) hw
      | app fnExpr args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hf : checkExpr prog (envToTyEnv env) [] pc inSpec fnExpr with
        | error _ => simp [hf] at hchk
        | ok fnLTy =>
          simp only [hf] at hchk
          cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
          | error _ => simp [ha] at hchk
          | ok argLTys =>
            simp only [ha] at hchk
            cases hfty : fnLTy.ty <;> simp only [hfty] at hchk <;> try contradiction
            case fn paramLTys fnPc retLTy =>
              split at hchk <;> try contradiction
              split at hchk <;> try contradiction
              rename_i harityOk
              split at hchk <;> try contradiction
              rename_i hargsSub
              injection hchk with hlty; subst hlty
              have hevF := ihE hprog env [] pc inSpec w fnExpr fnLTy henv hw hf
              rw [hfty] at hevF
              cases houtF : eval fuel' prog env pc w fnExpr with
              | stopped b w1 => rw [houtF] at hevF; exact hevF.weaken_nil.abort_non_ok (by simp)
              | failed m w1 => rw [houtF] at hevF; exact hevF.weaken_nil.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtF hevF.not_jumped_nil
              | wrong => rw [houtF] at hevF; nomatch hevF
              | ok fv w1 =>
                rw [houtF] at hevF; cases hevF with | ok hfv hw1 =>
                cases hfv with | @closure params _ _ bodyLTy body capEnv hcapEnv hbodyChk hsub =>
                dsimp only
                have hseq := evalSeq_sound (eval fuel' prog env pc)
                  (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw1 ha
                cases hseqOut : evalSeq (eval fuel' prog env pc) w1 args with
                | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
                | ok argVals w2 =>
                  dsimp only
                  rw [hseqOut] at hseq; rcases hseq with ⟨hargValsWf, hw2⟩
                  simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harityOk
                  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hargsSub
                  have hvsParams := valListWf_of_zip_tyEq hargValsWf harityOk (fun p hp => (hargsSub p hp).1)
                  have hlenEq : argVals.length = params.length := by
                    have hl := hvsParams.length_eq; simpa using hl
                  have hneF : (argVals.length != params.length) = false := bne_eq_false_iff_eq.mpr hlenEq
                  simp only [hneF, Bool.false_eq_true, ↓reduceIte]
                  have hcallEnvWf := extendEnv_wf hvsParams hcapEnv
                  have htyEnvEq : envToTyEnv ((List.zip params argVals).map
                      (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv) =
                      extendTyEnv (envToTyEnv capEnv) params := by
                    rw [envToTyEnv_append, envToTyEnv_zip_params params argVals hlenEq, extendTyEnv]
                  rw [← htyEnvEq] at hbodyChk
                  have hevBody := ihE hprog _ [] fnPc true w2 body bodyLTy hcallEnvWf hw2 hbodyChk
                  simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
                  have hretAddTy : (retLTy.addTags (pc.union fnLTy.tags)).ty = bodyLTy.ty := by
                    simp [hsub.1]
                  cases houtB : eval fuel' prog _ fnPc w2 body with
                  | stopped b w3 => dsimp only; rw [houtB] at hevBody; exact hevBody.weaken_nil.abort_non_ok (by simp)
                  | failed m w3 => dsimp only; rw [houtB] at hevBody; exact hevBody.weaken_nil.abort_non_ok (by simp)
                  | outOfFuel => dsimp only; exact .outOfFuel
                  | jumped _ _ _ => exact absurd houtB hevBody.not_jumped_nil
                  | wrong => rw [houtB] at hevBody; nomatch hevBody
                  | ok bv w3 =>
                    dsimp only; rw [houtB] at hevBody; cases hevBody with | ok hbv hw3 =>
                    exact .ok (hretAddTy ▸ hbv) hw3
      | call fnName args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          simp only [ha] at hchk
          cases hf : prog.findFun? fnName with
          | none => simp [hf] at hchk
          | some fDecl =>
            simp only [hf] at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i harityOk
            split at hchk <;> try contradiction
            rename_i hargsSub
            injection hchk with hlty; subst hlty
            have hseq := evalSeq_sound (eval fuel' prog env pc)
              (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw ha
            cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
            | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
            | ok argVals w1 =>
              dsimp only
              rw [hseqOut] at hseq; rcases hseq with ⟨hargValsWf, hw1⟩
              simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harityOk
              simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hargsSub
              have hvsParams := valListWf_of_zip_tyEq hargValsWf (by simp [harityOk]) (fun p hp => (hargsSub p hp).1)
              have hlenEq : argVals.length = fDecl.params.length := by
                have hl := hvsParams.length_eq; simpa using hl
              have hneF : (argVals.length != fDecl.params.length) = false := bne_eq_false_iff_eq.mpr hlenEq
              simp only [hneF, Bool.false_eq_true, ↓reduceIte]
              rcases extendEnv_rev_wf hvsParams with ⟨hcallEnvWf, hcallTyEq⟩
              rcases checkFunDecl_valid hprog hf with ⟨bodyLTy, hbodyChk, hbodyTy⟩
              rw [← hcallTyEq] at hbodyChk
              have hevBody := ihE hprog _ [] fDecl.pc fDecl.kind.isSpec w1 fDecl.body bodyLTy hcallEnvWf hw1 hbodyChk
              have hretAddTy : (fDecl.ret.addTags pc).ty = bodyLTy.ty := by
                simp [hbodyTy]
              cases houtB : eval fuel' prog _ fDecl.pc w1 fDecl.body with
              | stopped b w2 => dsimp only; rw [houtB] at hevBody; exact hevBody.weaken_nil.abort_non_ok (by simp)
              | failed m w2 => dsimp only; rw [houtB] at hevBody; exact hevBody.weaken_nil.abort_non_ok (by simp)
              | outOfFuel => dsimp only; exact .outOfFuel
              | jumped _ _ _ => exact absurd houtB hevBody.not_jumped_nil
              | wrong => rw [houtB] at hevBody; nomatch hevBody
              | ok bv w2 =>
                dsimp only; rw [houtB] at hevBody; cases hevBody with | ok hbv hw2 =>
                exact .ok (hretAddTy ▸ hbv) hw2
      | join label params rhs body =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        dsimp only at hchk
        let tEnv := envToTyEnv env
        let guess1 := pc.union (inferJumpPc prog label tEnv pc body)
        let rhsTEnv := extendTyEnv tEnv params
        let joinPc := guess1.union (inferJumpPc prog label rhsTEnv guess1 rhs)
        have hexSig : ∃ retLTy rLTy bLTy,
            retLTy.ty = lty.ty ∧
            rLTy.ty = retLTy.ty ∧
            bLTy.ty = retLTy.ty ∧
            checkExpr prog rhsTEnv ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv) joinPc inSpec rhs = .ok rLTy ∧
            checkExpr prog tEnv ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv) pc inSpec body = .ok bLTy := by
          change (match inferJoinRetLTy prog rhsTEnv jenv joinPc label rhs body with
            | none => Except.error s!"could not determine return type of join point '{label}'"
            | some candRetLTy => _) = Except.ok lty at hchk
          cases hc0 : inferJoinRetLTy prog rhsTEnv jenv joinPc label rhs body with
          | none => rw [hc0] at hchk; contradiction
          | some candRetLTy =>
            rw [hc0] at hchk; dsimp only [bind, Except.bind] at hchk
            split at hchk <;> try contradiction
            cases hr1 : checkExpr prog rhsTEnv ((label, { params := params, joinPc := joinPc, retLTy := candRetLTy.addTags joinPc }) :: jenv) joinPc inSpec rhs with
            | error _ => rw [hr1] at hchk; contradiction
            | ok rLTy1 =>
              rw [hr1] at hchk; dsimp only at hchk
              cases hb1 : checkExpr prog tEnv ((label, { params := params, joinPc := joinPc, retLTy := candRetLTy.addTags joinPc }) :: jenv) pc inSpec body with
              | error _ => rw [hb1] at hchk; contradiction
              | ok bLTy1 =>
                rw [hb1] at hchk; dsimp only at hchk
                split at hchk <;> try contradiction
                rename_i htyOk1
                simp only [Bool.and_eq_true, decide_eq_true_eq] at htyOk1
                split at hchk
                · injection hchk with hlty; subst hlty
                  exact ⟨_, rLTy1, bLTy1, rfl, htyOk1.1, htyOk1.2, hr1, hb1⟩
                · cases hr2 : checkExpr prog rhsTEnv _ joinPc inSpec rhs with
                  | error _ => rw [hr2] at hchk; contradiction
                  | ok rLTy2 =>
                    rw [hr2] at hchk; dsimp only at hchk
                    cases hb2 : checkExpr prog tEnv _ pc inSpec body with
                    | error _ => rw [hb2] at hchk; contradiction
                    | ok bLTy2 =>
                      rw [hb2] at hchk; dsimp only at hchk
                      split at hchk <;> try contradiction
                      rename_i hsub2
                      simp only [Bool.and_eq_true, ltySubtype, decide_eq_true_eq] at hsub2
                      injection hchk with hlty; subst hlty
                      exact ⟨_, rLTy2, bLTy2, rfl, hsub2.1.1, hsub2.2.1, hr2, hb2⟩
        rcases hexSig with ⟨retLTy, rLTy, bLTy, hretEqLty, hrTyEq, hbTyEq, hrChk, hbChk⟩
        have hevBody := ihE hprog env ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
          pc inSpec w body bLTy henv hw hbChk
        cases houtB : eval fuel' prog env pc w body with
        | ok bv w1 =>
          rw [houtB] at hevBody; cases hevBody with | ok hbv hw1 =>
          exact .ok ((hbTyEq.trans hretEqLty) ▸ hbv) hw1
        | stopped b w1 =>
          rw [houtB] at hevBody; cases hevBody with | stopped _ hw1 => exact .stopped b hw1
        | failed m w1 =>
          rw [houtB] at hevBody; cases hevBody with | failed _ hw1 => exact .failed m hw1
        | outOfFuel => exact .outOfFuel
        | wrong => rw [houtB] at hevBody; nomatch hevBody
        | jumped lbl jVals w1 =>
          rw [houtB] at hevBody
          cases hevBody with | @jumped _ _ _ otherSig hlookJ hjValsWf hw1 =>
          cases hlbl : (lbl == label)
          · simp only [hlbl, Bool.false_eq_true, ↓reduceIte]
            have hne : label ≠ lbl := fun heq => by subst heq; simp at hlbl
            simp only [lookupJoinEnv, hne, ↓reduceIte] at hlookJ
            exact .jumped hlookJ hjValsWf hw1
          · simp only [hlbl, ↓reduceIte]
            have heq : label = lbl := (beq_iff_eq.mp hlbl).symm
            simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlookJ
            subst hlookJ
            have hjLen : jVals.length = params.length := by
              have hl := hjValsWf.length_eq; simpa using hl
            have hneF : (jVals.length != params.length) = false := bne_eq_false_iff_eq.mpr hjLen
            simp only [hneF, Bool.false_eq_true, ↓reduceIte]
            have hjEnvWf := extendEnv_wf hjValsWf henv
            have hjTyEq : envToTyEnv ((List.zip params jVals).map
                (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env) =
                extendTyEnv (envToTyEnv env) params := by
              rw [envToTyEnv_append, envToTyEnv_zip_params params jVals hjLen, extendTyEnv]
            exact (ihJL hprog env _ jenv label params joinPc retLTy rLTy inSpec rhs w1
              henv hjEnvWf hjTyEq hw1 hrChk hrTyEq).cast_ty hretEqLty
      | jump label args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          simp only [ha] at hchk
          cases hj : lookupJoinEnv jenv label with
          | none => simp [hj] at hchk
          | some sig =>
            simp only [hj] at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i harityOk
            split at hchk <;> try contradiction
            rename_i hargsSub
            injection hchk with hlty; subst hlty
            have hseq := evalSeq_sound (eval fuel' prog env pc)
              (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw ha
            cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
            | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
            | ok argVals w1 =>
              dsimp only
              rw [hseqOut] at hseq; rcases hseq with ⟨hargValsWf, hw1⟩
              simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harityOk
              simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true, ltySubtype, decide_eq_true_eq] at hargsSub
              have hvsSig := valListWf_of_zip_tyEq (bs1 := sig.params.map Prod.snd) hargValsWf (by simp [harityOk]) (fun p hp => by
                have h0 := (hargsSub p hp).1.1
                rwa [LTy.addTags_ty] at h0)
              exact .jumped hj hvsSig hw1
      | tuple elems =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec elems with
        | error _ => simp [ha] at hchk
        | ok elemLTys =>
          simp only [ha, Except.ok.injEq] at hchk; subst hchk
          have hseq := evalSeq_sound (eval fuel' prog env pc)
            (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w elems with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
          | ok vs w1 =>
            dsimp only
            rw [hseqOut] at hseq; exact .ok (.tuple hseq.1) hseq.2
      | proj tup idx =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ht : checkExpr prog (envToTyEnv env) [] pc inSpec tup with
        | error _ => simp [ht] at hchk
        | ok tupLTy =>
          simp only [ht] at hchk
          cases htty : tupLTy.ty <;> simp only [htty] at hchk <;> try contradiction
          case tuple elemLTys =>
            cases hg : elemLTys[idx]? with
            | none => simp [hg] at hchk
            | some eLTy =>
              simp only [hg, Except.ok.injEq] at hchk; subst hchk
              have hevT := ihE hprog env [] pc inSpec w tup tupLTy henv hw ht
              rw [htty] at hevT
              cases houtT : eval fuel' prog env pc w tup with
              | stopped b w1 => rw [houtT] at hevT; exact hevT.weaken_nil.abort_non_ok (by simp)
              | failed m w1 => rw [houtT] at hevT; exact hevT.weaken_nil.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtT hevT.not_jumped_nil
              | wrong => rw [houtT] at hevT; nomatch hevT
              | ok tv w1 =>
                rw [houtT] at hevT; cases hevT with | ok htv hw1 =>
                cases htv with | tuple hvs =>
                rcases hvs.getElem?_wf hg with ⟨v, hvGet, hvWf⟩
                have haddTy : (eLTy.addTags (tupLTy.tags.union pc)).ty = eLTy.ty := by cases eLTy; rfl
                simp only [hvGet, haddTy]; exact .ok hvWf hw1
      | ctor typeName ctorName args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          simp only [ha] at hchk
          cases hd : prog.findData? typeName with
          | none => simp [hd] at hchk
          | some dDecl =>
            simp only [hd] at hchk
            cases hc : dDecl.ctors.find? (fun c => c.name == ctorName) with
            | none => simp [hc] at hchk
            | some cDecl =>
              simp only [hc] at hchk
              split at hchk <;> try contradiction
              rename_i harityOk
              split at hchk <;> try contradiction
              rename_i hfieldsEq
              injection hchk with hlty; subst hlty
              have hseq := evalSeq_sound (eval fuel' prog env pc)
                (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw ha
              cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
              | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
              | ok vs w1 =>
                dsimp only
                rw [hseqOut] at hseq; rcases hseq with ⟨hvsWf, hw1⟩
                simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harityOk
                simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, decide_eq_true_eq] at hfieldsEq
                have hvsFields := valListWf_of_zip_tyEq hvsWf harityOk (fun p hp => hfieldsEq p hp)
                exact .ok (.ctor hd hc hvsFields) hw1
      | tableLit schema rows =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        rename_i hvalS
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        rename_i hrowsOk
        injection hchk with hlty; subst hlty
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hvalS
        simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hrowsOk
        apply OutcomeWf.ok _ hw
        apply ValWf.table rfl (by simpa using validTableTy_imp_schemaWf hvalS.1.1.1)
        simp only [hvalS.1.1.2, hvalS.2, Option.isSome_none]
        apply RowsWf.of_forall_raw
        intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨rl, hrlMem, rfl⟩
        exact checkRowLit_go_sound schema.cols rl.cells (hrowsOk rl hrlMem)
      | prim op args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          simp only [ha] at hchk
          have hseq := evalSeq_sound (eval fuel' prog env pc)
            (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
          | ok vs w1 =>
            dsimp only
            rw [hseqOut] at hseq; rcases hseq with ⟨hvsWf, hw1⟩
            have hprim := evalPrimOp_sound hchk hvsWf
            cases hp : evalPrimOp op vs with
            | ok v => dsimp only; rw [hp] at hprim; cases hprim with | ok hv => exact .ok hv hw1
            | stopped b => dsimp only; exact .stopped b hw1
            | outOfFuel => dsimp only; exact .outOfFuel
            | wrong => rw [hp] at hprim; nomatch hprim
      | rel plan =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hp : checkPlan prog (envToTyEnv env) pc inSpec plan with
        | error _ => simp [hp] at hchk
        | ok pTy =>
          simp only [hp, Except.ok.injEq] at hchk; subst hchk
          exact (ihP hprog env pc inSpec w plan pTy henv hw hp).weaken_nil
      | host op args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          simp only [ha] at hchk
          have hseq := evalSeq_sound (eval fuel' prog env pc)
            (fun w' e' eLTy hw' he' => ihE hprog env [] pc inSpec w' e' eLTy henv hw' he') hw ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq jenv _
          | ok vs w1 =>
            dsimp only
            rw [hseqOut] at hseq; rcases hseq with ⟨hvsWf, hw1⟩
            exact (evalHostOp_sound hprog hchk hvsWf hw1).weaken_nil
      | stop kind detail =>
        dsimp only
        unfold checkExpr at hchk
        cases detail with
        | none => dsimp only; exact .stopped _ hw
        | some dExpr =>
          dsimp only at hchk ⊢
          split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hd : checkExpr prog (envToTyEnv env) [] pc inSpec dExpr with
          | error _ => simp [hd] at hchk
          | ok dLTy =>
            simp only [hd] at hchk
            split at hchk <;> try contradiction
            rw [checkExpr_inSpec_true hd]; dsimp only
            have hevD := ihE hprog env [] pc inSpec w dExpr dLTy henv hw hd
            cases houtD : eval fuel' prog env pc w dExpr with
            | stopped b w1 => dsimp only; rw [houtD] at hevD; exact hevD.weaken_nil.abort_non_ok (by simp)
            | failed m w1 => dsimp only; rw [houtD] at hevD; exact hevD.weaken_nil.abort_non_ok (by simp)
            | outOfFuel => dsimp only; exact .outOfFuel
            | jumped _ _ _ => exact absurd houtD hevD.not_jumped_nil
            | wrong => rw [houtD] at hevD; nomatch hevD
            | ok _ w1 => dsimp only; rw [houtD] at hevD; cases hevD with | ok _ hw1 => exact .stopped _ hw1
      | fail msgExpr =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hm : checkExpr prog (envToTyEnv env) [] pc inSpec msgExpr with
        | error _ => simp [hm] at hchk
        | ok mLTy =>
          simp only [hm] at hchk
          split at hchk <;> try contradiction
          rename_i hmText
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hmText
          have hevM := ihE hprog env [] pc inSpec w msgExpr mLTy henv hw hm
          rw [hmText.1] at hevM
          cases houtM : eval fuel' prog env pc w msgExpr with
          | stopped b w1 => rw [houtM] at hevM; exact hevM.weaken_nil.abort_non_ok (by simp)
          | failed m w1 => rw [houtM] at hevM; exact hevM.weaken_nil.abort_non_ok (by simp)
          | outOfFuel => exact .outOfFuel
          | jumped _ _ _ => exact absurd houtM hevM.not_jumped_nil
          | wrong => rw [houtM] at hevM; nomatch hevM
          | ok mv w1 =>
            rw [houtM] at hevM; cases hevM with | ok hmv hw1 =>
            cases hmv with | text s => exact .failed s hw1
    -- Part D: JoinLoopSoundAt (fuel' + 1)
    · intro hprog baseEnv curEnv jenv label params joinPc retLTy rLTy inSpec rhs w hbase hcur hcurTy hw hrChk hrTyEq
      unfold evalJoinLoop; dsimp only
      have hrChk' := hrChk; rw [← hcurTy] at hrChk'
      have hevR := ihE hprog curEnv ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
        joinPc inSpec w rhs rLTy hcur hw hrChk'
      cases houtR : eval fuel' prog curEnv joinPc w rhs with
      | ok rv w1 =>
        rw [houtR] at hevR; cases hevR with | ok hrv hw1 =>
        exact .ok (hrTyEq ▸ hrv) hw1
      | stopped b w1 =>
        rw [houtR] at hevR; cases hevR with | stopped _ hw1 => exact .stopped b hw1
      | failed m w1 =>
        rw [houtR] at hevR; cases hevR with | failed _ hw1 => exact .failed m hw1
      | outOfFuel => exact .outOfFuel
      | wrong => rw [houtR] at hevR; nomatch hevR
      | jumped lbl jVals w1 =>
        rw [houtR] at hevR
        cases hevR with | @jumped _ _ _ otherSig hlookJ hjValsWf hw1 =>
        cases hlbl : (lbl == label)
        · simp only [hlbl, Bool.false_eq_true, ↓reduceIte]
          have hne : label ≠ lbl := fun heq => by subst heq; simp at hlbl
          simp only [lookupJoinEnv, hne, ↓reduceIte] at hlookJ
          exact .jumped hlookJ hjValsWf hw1
        · simp only [hlbl, ↓reduceIte]
          have heq : label = lbl := (beq_iff_eq.mp hlbl).symm
          simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlookJ
          subst hlookJ
          have hjLen : jVals.length = params.length := by
            have hl := hjValsWf.length_eq; simpa using hl
          have hneF : (jVals.length != params.length) = false := bne_eq_false_iff_eq.mpr hjLen
          simp only [hneF, Bool.false_eq_true, ↓reduceIte]
          have hjEnvWf := extendEnv_wf hjValsWf hbase
          have hjTyEq : envToTyEnv ((List.zip params jVals).map
              (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ baseEnv) =
              extendTyEnv (envToTyEnv baseEnv) params := by
            rw [envToTyEnv_append, envToTyEnv_zip_params params jVals hjLen, extendTyEnv]
          exact ihJL hprog baseEnv _ jenv label params joinPc retLTy rLTy inSpec rhs w1
            hbase hjEnvWf hjTyEq hw1 hrChk hrTyEq
    -- Part E: PlanSoundAt (fuel' + 1)
    · intro hprog env pc inSpec w plan pTy henv hw hchk
      unfold evalPlan
      cases plan with
      | sourceExpr e =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases he : checkExpr prog (envToTyEnv env) [] pc inSpec e with
        | error _ => simp [he] at hchk
        | ok eLTy =>
          simp only [he] at hchk
          cases hety : eLTy.ty <;> simp only [hety] at hchk <;> try contradiction
          case table tt =>
            injection hchk with hp; subst hp
            have hevE := ihE hprog env [] pc inSpec w e eLTy henv hw he
            rw [hety] at hevE
            cases houtE : eval fuel' prog env pc w e with
            | stopped b w1 => rw [houtE] at hevE; exact hevE.abort_non_ok (by simp)
            | failed m w1 => rw [houtE] at hevE; exact hevE.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtE hevE.not_jumped_nil
            | wrong => rw [houtE] at hevE; nomatch hevE
            | ok ev w1 =>
              rw [houtE] at hevE; cases hevE with | ok hevWf hw1 =>
              cases hevWf with | table hcols hschema hrows =>
              exact .ok (.table hcols (by simpa [PlanTy.toLTy] using hschema) hrows) hw1
      | sourceDB cap tableName schema =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hc : checkExpr prog (envToTyEnv env) [] pc inSpec cap with
        | error _ => simp [hc] at hchk
        | ok capLTy =>
          simp only [hc] at hchk
          cases hcty : capLTy.ty <;> simp only [hcty] at hchk <;> try contradiction
          case readDB dbName =>
            split at hchk <;> try contradiction
            rename_i hvalS
            injection hchk with hp; subst hp
            simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hvalS
            have hsWf := validTableTy_imp_schemaWf hvalS.1.1.1.1
            have hsumF := hvalS.1.1.1.2
            have hdkN := hvalS.1.2
            have hevC := ihE hprog env [] pc inSpec w cap capLTy henv hw hc
            rw [hcty] at hevC
            cases houtC : eval fuel' prog env pc w cap with
            | stopped b w1 => rw [houtC] at hevC; exact hevC.abort_non_ok (by simp)
            | failed m w1 => rw [houtC] at hevC; exact hevC.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtC hevC.not_jumped_nil
            | wrong => rw [houtC] at hevC; nomatch hevC
            | ok cv w1 =>
              rw [houtC] at hevC; cases hevC with | ok hcv hw1 =>
              cases hcv with | capReadDB h =>
              cases h with
              | real =>
                dsimp only
                cases hst : w1.realDBTables.find? (fun (st : StoredTable) => st.db == dbName && st.tableName == tableName) with
                | none =>
                  dsimp only
                  apply OutcomeWf.ok _ hw1
                  apply ValWf.table rfl (by simpa [PlanTy.toLTy] using hsWf)
                  simp only [hsumF, hdkN, Option.isSome_none]; exact .nil _ _ _
                | some st =>
                  dsimp only
                  split
                  · rename_i htyEq
                    have hty := of_decide_eq_true htyEq
                    apply OutcomeWf.ok _ hw1
                    apply ValWf.table rfl (by simpa [PlanTy.toLTy] using hsWf)
                    simp only [hsumF, hdkN, Option.isSome_none]
                    apply RowsWf.of_forall_raw
                    intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨cs, hcs, rfl⟩
                    exact (hw1.realDbWf st (List.mem_of_find?_eq_some hst) cs hcs).congr_ty hty
                  · exact .stopped _ hw1
              | fake id =>
                dsimp only
                cases hfdb : w1.fakeDBs[id]? with
                | none =>
                  dsimp only
                  apply OutcomeWf.ok _ hw1
                  apply ValWf.table rfl (by simpa [PlanTy.toLTy] using hsWf)
                  simp only [hsumF, hdkN, Option.isSome_none]; exact .nil _ _ _
                | some fdb =>
                  dsimp only
                  cases hst : fdb.tables.find? (fun (st : StoredTable) => st.tableName == tableName) with
                  | none =>
                    dsimp only
                    apply OutcomeWf.ok _ hw1
                    apply ValWf.table rfl (by simpa [PlanTy.toLTy] using hsWf)
                    simp only [hsumF, hdkN, Option.isSome_none]; exact .nil _ _ _
                  | some st =>
                    dsimp only
                    split
                    · rename_i htyEq
                      have hty := of_decide_eq_true htyEq
                      apply OutcomeWf.ok _ hw1
                      apply ValWf.table rfl (by simpa [PlanTy.toLTy] using hsWf)
                      simp only [hsumF, hdkN, Option.isSome_none]
                      apply RowsWf.of_forall_raw
                      intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨cs, hcs, rfl⟩
                      exact (hw1.fakeDbWf fdb (List.mem_of_getElem? hfdb) st (List.mem_of_find?_eq_some hst) cs hcs).congr_ty hty
                    · exact .stopped _ hw1
      | select inp selCols =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            rename_i hselDist
            split at hchk <;> try contradiction
            rename_i hselEx
            injection hchk with hp; subst hp
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hselDist hselEx
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              have hselExTv : ∀ n ∈ selCols, (tv.cols.find? (fun c => c.name == n)).isSome = true := by
                rw [hcolsEq]; exact hselEx
              rcases select_idxSpecs_props selCols hselExTv with ⟨hlen, hallIdx, houtColsEq, houtNames⟩
              have hneF : ((selCols.filterMap (lookupColIdx? tv.cols)).length != selCols.length) = false :=
                bne_eq_false_iff_eq.mpr hlen
              simp only [hneF, Bool.false_eq_true, ↓reduceIte]
              rcases projectRowsByIndices_sound (selCols.filterMap (lookupColIdx? tv.cols)) hallIdx
                tv.rows (hcolsEq ▸ hrows.to_forall) with ⟨outRows, hproj, houtRowsWf⟩
              simp only [hproj]
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨_, httProps⟩
              have houtColsEqTt : (selCols.filterMap (lookupColIdx? tv.cols)).map (fun (_, c) => { c with aggKind := .raw }) =
                  selCols.filterMap (fun n => (tt.findCol? n).map (fun c => { c with aggKind := .raw })) := by
                rw [houtColsEq, hcolsEq]; rfl
              apply OutcomeWf.ok _ hw1
              refine .table houtColsEqTt (rawTableSchemaWf_of_props _ _ ?_ ?_) (houtColsEqTt ▸ houtRowsWf)
              · rw [← houtColsEqTt, houtNames]
                cases hd : distinctIdents selCols <;> simp [hd] at hselDist ⊢
              · intro c hc; rw [List.mem_filterMap] at hc; rcases hc with ⟨n, _, hmap⟩
                cases hf : tt.findCol? n with
                | none => simp [hf] at hmap
                | some orig =>
                  rw [hf] at hmap; injection hmap with hcEq; subst hcEq
                  have horig := httProps orig (List.mem_of_find?_eq_some hf)
                  exact ⟨horig.1, horig.2, rfl⟩
      | drop inp dropCols =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            injection hchk with hp; subst hp
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases zipIdx_filter_props (fun c => !dropCols.contains c.name) tv.cols with ⟨hkeptFst, hkeptIdx⟩
              let keepSwapped := (tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)).map (fun (c, idx) => (idx, c))
              have hmapIdx : keepSwapped.map Prod.fst =
                  (tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)).map Prod.snd := by
                dsimp only [keepSwapped]
                induction (tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)) <;> simp [*]
              have hmapCols : keepSwapped.map (fun (_, c) => { c with aggKind := .raw }) =
                  (tt.cols.filter (fun c => !dropCols.contains c.name)).map (fun c => { c with aggKind := .raw }) := by
                have h1 : keepSwapped.map (fun (_, c) => { c with aggKind := .raw }) =
                    ((tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)).map Prod.fst).map
                      (fun c => { c with aggKind := .raw }) := by
                  dsimp only [keepSwapped]
                  induction (tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)) <;> simp [*]
                rw [h1, hkeptFst, hcolsEq]
              have hallSwapped : ∀ ic ∈ keepSwapped, tv.cols[ic.1]? = some ic.2 := by
                intro ic hic; rw [List.mem_map] at hic; rcases hic with ⟨⟨c, i⟩, hci, rfl⟩
                exact hkeptIdx (c, i) hci
              rcases projectRowsByIndices_sound keepSwapped hallSwapped tv.rows (hcolsEq ▸ hrows.to_forall) with
                ⟨outRows, hproj, houtRowsWf⟩
              rw [hmapIdx] at hproj
              simp only [hproj]
              have htvOutEq : (tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)).map (fun (c, _) => { c with aggKind := .raw }) =
                  (tt.cols.filter (fun c => !dropCols.contains c.name)).map (fun c => { c with aggKind := .raw }) := by
                rw [← hmapCols]; dsimp only [keepSwapped]
                induction (tv.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)) <;> simp [*]
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
              exact .ok (.table htvOutEq
                (resetRawTableSchemaWf (distinctIdents_filter _ httUniq)
                  (fun c hc => httProps c (List.mem_filter.mp hc).1) _ _)
                (hmapCols ▸ houtRowsWf)) hw1
      | rename inp pairs =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i houtUniq
            injection hchk with hp; subst hp
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨_, httProps⟩
              have hrenTy : tt.cols.map ColSpec.ty =
                  (tt.cols.map (fun c => match pairs.find? (fun (_, oldN) => oldN == c.name) with
                    | some (newN, _) => { c with name := newN, aggKind := .raw }
                    | none => { c with aggKind := .raw })).map ColSpec.ty := by
                induction tt.cols with
                | nil => rfl
                | cons c cs ih =>
                  simp only [List.map_cons]
                  cases pairs.find? (fun (_, oldN) => oldN == c.name) <;> simp [ih]
              apply OutcomeWf.ok _ hw1
              refine .table (by
                rw [hcolsEq]; dsimp only [PlanTy.toLTy]
                apply List.map_congr_left
                intro c _
                cases pairs.find? (fun (_, oldN) => oldN == c.name) <;> rfl)
                (rawTableSchemaWf_of_props _ _ houtUniq ?_) (hrows.congr_ty_raw hrenTy)
              intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨orig, horig, rfl⟩
              rcases httProps orig horig with ⟨hv, hb⟩
              cases pairs.find? (fun (_, oldN) => oldN == orig.name) <;> exact ⟨hv, hb, rfl⟩
      | derive inp items =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            cases ha : applyDeriveItems prog (envToTyEnv env) (tt.cols.map (fun c => { c with aggKind := .raw })) items with
            | error _ => simp [ha] at hchk
            | ok outCols =>
              simp only [ha] at hchk
              split at hchk <;> try contradiction
              injection hchk with hp; subst hp
              have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
              cases houtI : evalPlan fuel' prog env pc w inp with
              | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
              | wrong => rw [houtI] at hevI; nomatch hevI
              | ok iv w1 =>
                rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                cases hiv with | @table tv _ hcols hschema hrows =>
                have hcolsEq : tv.cols = tt.cols := hcols
                rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                have hinitUniq : distinctIdents ((tv.cols.map (fun c => { c with aggKind := .raw })).map ColSpec.name) = true := by
                  rw [hcolsEq]
                  have hn : (tt.cols.map (fun c => { c with aggKind := .raw })).map ColSpec.name = tt.cols.map ColSpec.name := by
                    induction tt.cols <;> simp [*]
                  rw [hn]; exact httUniq
                have hinitProps : ∀ c ∈ tv.cols.map (fun c => { c with aggKind := .raw }),
                    validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                  rw [hcolsEq]; intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
                  exact ⟨(httProps o ho).1, (httProps o ho).2, rfl⟩
                have hinitRows : RowsWf prog (tv.rows.map (fun r => { r with groupMeta := none }))
                    (tv.cols.map (fun c => { c with aggKind := .raw })) false false := by
                  rw [hcolsEq]; exact hrows.congr_ty_raw (map_ty_with_aggKind tt.cols .raw).symm
                exact evalDeriveItems_sound (evalRowExpr fuel' prog env) w1 hw1
                  (fun cols r re sTy rTags _ hcV hrC hre => ihRE hprog env cols r re sTy rTags henv hcV hrC hre)
                  items _ outCols _ _ hinitUniq hinitProps hinitRows (by simpa [hcolsEq] using ha)
      | filter inp pred =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            cases hp : checkRowExpr prog (envToTyEnv env) tt.cols pred with
            | error _ => simp [hp] at hchk
            | ok pr =>
              simp only [hp] at hchk
              split at hchk <;> try contradiction
              rename_i hpBool
              have hpTy : pr.1 = .bool := of_decide_eq_true hpBool
              injection hchk with hpOut; subst hpOut
              have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
              cases houtI : evalPlan fuel' prog env pc w inp with
              | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
              | wrong => rw [houtI] at hevI; nomatch hevI
              | ok iv w1 =>
                rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                cases hiv with | @table tv _ hcols hschema hrows =>
                have hcolsEq : tv.cols = tt.cols := hcols
                rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                cases pr with | mk pTy pTags =>
                dsimp only at hpTy; subst hpTy
                dsimp only [PlanTy.toLTy]
                rw [hcolsEq]
                exact evalFilterRows_sound (evalRowExpr fuel' prog env)
                  ((tt.rowTags.union pTags).union pc) (tt.orderTags.union pc) w1 hw1 httUniq httProps hp
                  (fun r hr => ihRE hprog env tt.cols r pred .bool pTags henv (fun c hc => (httProps c hc).1) hr hp)
                  tv.rows (hcolsEq ▸ hrows.to_forall)
      | distinct inp cols =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            generalize hkn : (if cols.isEmpty then tt.cols.map ColSpec.name else cols) = keyNames at hchk
            split at hchk <;> try contradiction
            rename_i hkeysOk
            injection hchk with hp; subst hp
            rw [← hkn] at hkeysOk
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', List.all_eq_true] at hkeysOk
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
              have hkeysExist : ∀ k ∈ (if cols.isEmpty then tv.cols.map ColSpec.name else cols),
                  (tv.cols.find? (fun c => c.name == k)).isSome = true := by
                rw [hcolsEq]; intro k hk
                have hk0 := hkeysOk.2 k hk
                unfold TableTy.findCol? at hk0
                cases hfk : tt.cols.find? (fun c => c.name == k)
                · rw [hfk] at hk0; simp at hk0
                · rfl
              rcases dedupTableRows_sound (outCols := tt.cols.map (fun c => { c with aggKind := .raw }))
                (by rw [hcolsEq]; exact (map_ty_with_aggKind tt.cols .raw).symm) hkeysExist [] tv.rows
                (hcolsEq ▸ hrows.to_forall) with ⟨outRows, hdedup, houtRowsWf⟩
              simp only [hdedup]
              exact .ok (.table (by rw [hcolsEq]) (resetRawTableSchemaWf httUniq httProps _ _) houtRowsWf) hw1
      | sort inp keys =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            injection hchk with hp; subst hp
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
              apply OutcomeWf.ok _ hw1
              refine .table (by rw [hcolsEq]) (resetRawTableSchemaWf httUniq httProps _ _) (RowsWf.of_forall_raw ?_)
              intro r hr
              have hmem := mem_insertionSortBy _ r _ hr
              rw [List.mem_map] at hmem; rcases hmem with ⟨orig, horig, rfl⟩
              exact (hrows.to_forall orig horig).congr_ty (map_ty_with_aggKind tt.cols .raw).symm
      | limit inp n =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            injection hchk with hp; subst hp
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
              apply OutcomeWf.ok _ hw1
              refine .table (by rw [hcolsEq]) (resetRawTableSchemaWf httUniq httProps _ _) (RowsWf.of_forall_raw ?_)
              intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨orig, horig, rfl⟩
              exact (hrows.to_forall orig (List.mem_of_mem_take horig)).congr_ty (map_ty_with_aggKind tt.cols .raw).symm
      | join kind leftP rightP on suffixes =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hl : checkPlan prog (envToTyEnv env) pc inSpec leftP with
        | error _ => simp [hl] at hchk
        | ok lP =>
          simp only [hl] at hchk
          cases hr : checkPlan prog (envToTyEnv env) pc inSpec rightP with
          | error _ => simp [hr] at hchk
          | ok rP =>
            simp only [hr] at hchk
            cases lP <;> cases rP <;> try contradiction
            case table.table lTT rTT =>
              cases hkp : resolveJoinPairs lTT rTT on with
              | error _ => simp [hkp] at hchk
              | ok keyPairs =>
                simp only [hkp] at hchk
                cases hbj : buildJoinedCols kind lTT.cols rTT.cols on suffixes with
                | error _ => simp [hbj] at hchk
                | ok joinedCols =>
                  simp only [hbj, Except.ok.injEq] at hchk; subst hchk
                  have hevL := ihP hprog env pc inSpec w leftP (.table lTT) henv hw hl
                  cases houtL : evalPlan fuel' prog env pc w leftP with
                  | stopped b w1 => rw [houtL] at hevL; exact hevL.abort_non_ok (by simp)
                  | failed m w1 => rw [houtL] at hevL; exact hevL.abort_non_ok (by simp)
                  | outOfFuel => exact .outOfFuel
                  | jumped _ _ _ => exact absurd houtL hevL.not_jumped_nil
                  | wrong => rw [houtL] at hevL; nomatch hevL
                  | ok lv w1 =>
                    rw [houtL] at hevL; cases hevL with | ok hlv hw1 =>
                    cases hlv with | @table lTV _ hlCols hlSchema hlRows =>
                    dsimp only
                    have hlColsEq : lTV.cols = lTT.cols := hlCols
                    have hevR := ihP hprog env pc inSpec w1 rightP (.table rTT) henv hw1 hr
                    cases houtR : evalPlan fuel' prog env pc w1 rightP with
                    | stopped b w2 => dsimp only; rw [houtR] at hevR; exact hevR.abort_non_ok (by simp)
                    | failed m w2 => dsimp only; rw [houtR] at hevR; exact hevR.abort_non_ok (by simp)
                    | outOfFuel => dsimp only; exact .outOfFuel
                    | jumped _ _ _ => exact absurd houtR hevR.not_jumped_nil
                    | wrong => rw [houtR] at hevR; nomatch hevR
                    | ok rv w2 =>
                      rw [houtR] at hevR; cases hevR with | ok hrv hw2 =>
                      cases hrv with | @table rTV _ hrCols hrSchema hrRows =>
                      dsimp only
                      have hrColsEq : rTV.cols = rTT.cols := hrCols
                      have hresSame : resolveJoinPairs { cols := lTV.cols } { cols := rTV.cols } on =
                          resolveJoinPairs lTT rTT on := by
                        rw [hlColsEq, hrColsEq]
                        have hg : ∀ (ps : List (Ident × Ident)),
                            resolveJoinPairs.go { cols := lTT.cols } { cols := rTT.cols } ps = resolveJoinPairs.go lTT rTT ps := by
                          intro ps; induction ps with
                          | nil => rfl
                          | cons p psTl ih =>
                            rcases p with ⟨lk, rk⟩
                            unfold resolveJoinPairs.go
                            have hfl : TableTy.findCol? { cols := lTT.cols } lk = lTT.findCol? lk := rfl
                            have hfr : TableTy.findCol? { cols := rTT.cols } rk = rTT.findCol? rk := rfl
                            rw [hfl, hfr, ih]
                        cases on <;> unfold resolveJoinPairs <;> dsimp only <;> (split; rfl; exact hg _)
                      rw [hresSame, hkp]; rw [hlColsEq, hrColsEq]; simp only [hbj]
                      rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hlSchema) with ⟨hlUniq, hlProps⟩
                      rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hrSchema) with ⟨hrUniq, hrProps⟩
                      have hlKeysEx0 := resolveJoinPairs_keys_exist hkp
                      have hlKeyMapEq : keyPairs.map (fun (lc, _) => lc.name) = keyPairs.map (fun p => p.1.name) := by
                        induction keyPairs <;> simp [*]
                      have hlKeysEx : ∀ k ∈ keyPairs.map (fun (lc, _) => lc.name),
                          (lTT.cols.find? (fun c => c.name == k)).isSome = true := by
                        rw [hlKeyMapEq]; exact hlKeysEx0
                      let sks := match on with | .sameKeys ks => ks | .pairs _ => []
                      rcases zipIdx_filter_props (fun rc => !sks.contains rc.name) rTT.cols with ⟨hrKeepFst, hrKeepIdx⟩
                      cases kind with
                      | semi =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        rcases joinTableRows_sound .semi (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTys lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
                      | anti =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        rcases joinTableRows_sound .anti (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTys lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
                      | innerOne =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        dsimp only at hjTys
                        have hjTysIdx : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                            ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if false then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty := by
                          rw [hjTys]; congr 1
                          have h1 : ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if false then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty =
                              ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map Prod.fst).map
                                (fun rc => if false then ensureOptionScalar rc.ty else rc.ty) := by
                            generalize (rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)) = z
                            induction z <;> simp [*]
                          rw [h1, hrKeepFst]
                        rcases joinTableRows_sound .innerOne (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTysIdx lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
                      | innerManyToOne =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        dsimp only at hjTys
                        have hjTysIdx : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                            ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if false then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty := by
                          rw [hjTys]; congr 1
                          have h1 : ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if false then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty =
                              ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map Prod.fst).map
                                (fun rc => if false then ensureOptionScalar rc.ty else rc.ty) := by
                            generalize (rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)) = z
                            induction z <;> simp [*]
                          rw [h1, hrKeepFst]
                        rcases joinTableRows_sound .innerManyToOne (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTysIdx lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
                      | innerMany =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        dsimp only at hjTys
                        have hjTysIdx : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                            ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if false then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty := by
                          rw [hjTys]; congr 1
                          have h1 : ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if false then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty =
                              ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map Prod.fst).map
                                (fun rc => if false then ensureOptionScalar rc.ty else rc.ty) := by
                            generalize (rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)) = z
                            induction z <;> simp [*]
                          rw [h1, hrKeepFst]
                        rcases joinTableRows_sound .innerMany (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTysIdx lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
                      | leftOne =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        dsimp only at hjTys
                        have hjTysIdx : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                            ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if true then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty := by
                          rw [hjTys]; congr 1
                          have h1 : ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if true then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty =
                              ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map Prod.fst).map
                                (fun rc => if true then ensureOptionScalar rc.ty else rc.ty) := by
                            generalize (rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)) = z
                            induction z <;> simp [*]
                          rw [h1, hrKeepFst]
                        rcases joinTableRows_sound .leftOne (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTysIdx lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
                      | leftManyToOne =>
                        rcases buildJoinedCols_props hlUniq hrUniq hlProps hrProps hbj with ⟨hjUniq, hjProps, hjTys⟩
                        dsimp only at hjTys
                        have hjTysIdx : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                            ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if true then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty := by
                          rw [hjTys]; congr 1
                          have h1 : ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map
                              (fun (p : ColSpec × Nat) => { p.1 with ty := if true then ensureOptionScalar p.1.ty else p.1.ty })).map ColSpec.ty =
                              ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map Prod.fst).map
                                (fun rc => if true then ensureOptionScalar rc.ty else rc.ty) := by
                            generalize (rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)) = z
                            induction z <;> simp [*]
                          rw [h1, hrKeepFst]
                        rcases joinTableRows_sound .leftManyToOne (joinedCols := joinedCols)
                          (rKeyNames := keyPairs.map (fun (_, rc) => rc.name)) (rRows := rTV.rows)
                          (fun c hc => (hrProps c hc).1) hlKeysEx hrKeepIdx
                          hrRows.to_forall hjTysIdx lTV.rows hlRows.to_forall with
                          ⟨outRows, hjEq, houtRowsWf⟩
                        dsimp only
                        split
                        · exact .stopped _ hw2
                        · erw [hjEq]; dsimp only
                          exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ hjUniq hjProps)
                            (by simpa [PlanTy.toLTy] using houtRowsWf)) hw2
      | union leftP rightP =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hl : checkPlan prog (envToTyEnv env) pc inSpec leftP with
        | error _ => simp [hl] at hchk
        | ok lP =>
          simp only [hl] at hchk
          cases hr : checkPlan prog (envToTyEnv env) pc inSpec rightP with
          | error _ => simp [hr] at hchk
          | ok rP =>
            simp only [hr] at hchk
            cases lP <;> cases rP <;> try contradiction
            case table.table lTT rTT =>
              cases hm : mergeUnionCols lTT.cols rTT.cols with
              | none => simp [hm] at hchk
              | some outCols =>
                simp only [hm, Except.ok.injEq] at hchk; subst hchk
                have hevL := ihP hprog env pc inSpec w leftP (.table lTT) henv hw hl
                cases houtL : evalPlan fuel' prog env pc w leftP with
                | stopped b w1 => rw [houtL] at hevL; exact hevL.abort_non_ok (by simp)
                | failed m w1 => rw [houtL] at hevL; exact hevL.abort_non_ok (by simp)
                | outOfFuel => exact .outOfFuel
                | jumped _ _ _ => exact absurd houtL hevL.not_jumped_nil
                | wrong => rw [houtL] at hevL; nomatch hevL
                | ok lv w1 =>
                  rw [houtL] at hevL; cases hevL with | ok hlv hw1 =>
                  cases hlv with | @table lTV _ hlCols hlSchema hlRows =>
                  dsimp only
                  have hevR := ihP hprog env pc inSpec w1 rightP (.table rTT) henv hw1 hr
                  cases houtR : evalPlan fuel' prog env pc w1 rightP with
                  | stopped b w2 => dsimp only; rw [houtR] at hevR; exact hevR.abort_non_ok (by simp)
                  | failed m w2 => dsimp only; rw [houtR] at hevR; exact hevR.abort_non_ok (by simp)
                  | outOfFuel => dsimp only; exact .outOfFuel
                  | jumped _ _ _ => exact absurd houtR hevR.not_jumped_nil
                  | wrong => rw [houtR] at hevR; nomatch hevR
                  | ok rv w2 =>
                    rw [houtR] at hevR; cases hevR with | ok hrv hw2 =>
                    cases hrv with | @table rTV _ hrCols _ hrRows =>
                    dsimp only
                    have hlColsEq : lTV.cols = lTT.cols := hlCols
                    have hrColsEq : rTV.cols = rTT.cols := hrCols
                    rw [hlColsEq, hrColsEq]; simp only [hm]
                    rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hlSchema) with ⟨hlUniq, hlProps⟩
                    rcases mergeUnionCols_props hlUniq hlProps hm with ⟨_, houtL, houtUniq, houtProps, hrTysEq⟩
                    apply OutcomeWf.ok _ hw2
                    refine .table rfl (rawTableSchemaWf_of_props _ _ houtUniq houtProps) (RowsWf.of_forall_raw ?_)
                    intro r hr0; rw [List.mem_map] at hr0; rcases hr0 with ⟨orig, horig, rfl⟩
                    rw [List.mem_append] at horig
                    rcases horig with hlM | hrM
                    · exact (hlRows.to_forall orig hlM).congr_ty houtL.symm
                    · exact (hrRows.to_forall orig hrM).congr_ty hrTysEq
      | groupBy inp keys =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            rename_i hkeysOk
            injection hchk with hp; subst hp
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hkeysOk
            rw [List.all_eq_true] at hkeysOk
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
              have houtNames : (tt.cols.map (fun c => if keys.contains c.name then { c with aggKind := .groupKey } else { c with aggKind := .raw })).map ColSpec.name =
                  tt.cols.map ColSpec.name := by
                induction tt.cols with
                | nil => rfl
                | cons c cs ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; split <;> simp
              have houtTy : tt.cols.map ColSpec.ty =
                  (tt.cols.map (fun c => if keys.contains c.name then { c with aggKind := .raw } else { c with aggKind := .raw })).map ColSpec.ty := by
                induction tt.cols with
                | nil => rfl
                | cons c cs ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; split <;> simp
              have houtTy' : tt.cols.map ColSpec.ty =
                  (tt.cols.map (fun c => if keys.contains c.name then { c with aggKind := .groupKey } else { c with aggKind := .raw })).map ColSpec.ty := by
                induction tt.cols with
                | nil => rfl
                | cons c cs ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; split <;> simp
              apply OutcomeWf.ok _ hw1
              refine .table (by rw [hcolsEq]) ?_ (hrows.congr_ty_raw houtTy')
              unfold TableSchemaWf; dsimp only [PlanTy.toLTy]
              simp only [houtNames, httUniq, hkeysOk.1, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
              refine ⟨?_, ?_⟩
              · intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨orig, horig, rfl⟩
                rcases httProps orig horig with ⟨hv, hb⟩
                cases hk : keys.contains orig.name
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  refine ⟨⟨hv, ?_⟩, by simp only [Option.getD_some, hk]; decide⟩
                  cases hbk : orig.bucketed <;> simp [hbk, hb]
                · simp only [↓reduceIte]
                  refine ⟨⟨hv, ?_⟩, by simp only [Option.getD_some, hk]; decide⟩
                  cases hbk : orig.bucketed <;> simp [hbk, hb]
              · intro k hk
                have hk0 := hkeysOk.2 k hk
                unfold TableTy.findCol? at hk0 ⊢
                cases hf : tt.cols.find? (fun c => c.name == k) with
                | none => rw [hf] at hk0; simp at hk0
                | some orig =>
                  have horigMem := List.mem_of_find?_eq_some hf
                  have horigName : orig.name = k := find?_name_eq ColSpec.name hf
                  rw [Option.isSome_iff_exists]
                  cases hfOut : (tt.cols.map (fun c => if keys.contains c.name then { c with aggKind := .groupKey } else { c with aggKind := .raw })).find? (fun c => c.name == k) with
                  | some f => exact ⟨f, rfl⟩
                  | none =>
                    exfalso
                    have hIn : (if keys.contains orig.name then { orig with aggKind := .groupKey } else { orig with aggKind := .raw }) ∈
                        tt.cols.map (fun c => if keys.contains c.name then { c with aggKind := .groupKey } else { c with aggKind := .raw }) :=
                      List.mem_map_of_mem horigMem
                    have hn := List.find?_eq_none.mp hfOut _ hIn
                    split at hn <;> simp [horigName] at hn
      | summarize inp aggs distinctKey =>
        have hchkTrue := checkPlan_inSpec_true hchk
        dsimp only
        unfold checkPlan at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi, bind, Except.bind] at hchk
        | ok inP =>
          rw [hi] at hchk; dsimp only [bind, Except.bind] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            have hsumExtract : ∃ aggCols dkTags,
                checkAggItemList prog (envToTyEnv env) tt aggs = .ok aggCols ∧
                distinctIdents (((tt.cols.filter (fun (c : ColSpec) => (tt.groupedBy.getD []).contains c.name)).map
                  (fun (c : ColSpec) => { c with aggKind := .groupKey }) ++ aggCols).map ColSpec.name) = true ∧
                pTy = .table {
                  cols := (tt.cols.filter (fun (c : ColSpec) => (tt.groupedBy.getD []).contains c.name)).map
                    (fun (c : ColSpec) => { c with aggKind := .groupKey }) ++ aggCols
                  rowTags := tt.rowTags.union dkTags
                  orderTags := TagSet.empty
                  groupedBy := some (tt.groupedBy.getD [])
                  summarized := true
                  distinctBy := distinctKey } ∧
                (distinctKey.isSome = true → ∃ dk, distinctKey = some dk ∧ (tt.findCol? dk).isSome = true) := by
              cases distinctKey with
              | none =>
                dsimp only at hchk
                cases hagg : checkAggItemList prog (envToTyEnv env) tt aggs with
                | error _ => rw [hagg] at hchk; simp at hchk
                | ok aggCols =>
                  rw [hagg] at hchk; dsimp only at hchk
                  split at hchk <;> try contradiction
                  rename_i hd; simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
                  injection hchk with hp
                  exact ⟨aggCols, TagSet.empty, rfl, hd, hp.symm, fun h => by simp at h⟩
              | some dk =>
                dsimp only at hchk
                cases hfc : tt.findCol? dk with
                | none => rw [hfc] at hchk; simp at hchk
                | some c =>
                  rw [hfc] at hchk; dsimp only at hchk
                  split at hchk <;> try contradiction
                  cases hagg : checkAggItemList prog (envToTyEnv env) tt aggs with
                  | error _ => rw [hagg] at hchk; simp at hchk
                  | ok aggCols =>
                    rw [hagg] at hchk; dsimp only at hchk
                    split at hchk <;> try contradiction
                    rename_i hd; simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
                    injection hchk with hp
                    exact ⟨aggCols, c.tags, rfl, hd, hp.symm, fun _ => ⟨dk, rfl, by simp [hfc]⟩⟩
            rcases hsumExtract with ⟨aggCols, dkTags, hagg, houtDist, hp, hdkSomeProp⟩
            subst hp
            rw [hchkTrue]; dsimp only
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              dsimp only
              have hcolsEq : tv.cols = tt.cols := hcols
              have httWf : TableSchemaWf prog tt = true := by simpa [PlanTy.toLTy] using hschema
              rcases tableSchemaWf_cols_props httWf with ⟨_, httProps⟩
              rcases checkAggItemList_props (fun c hc => (httProps c hc).1) hagg with ⟨haggLen, haggProps⟩
              rcases summarize_keyCols_props hcolsEq httWf with ⟨hkeyColsEq, hgkNames, hkeyFind⟩
              let keyColsEval := (tv.cols.filter (fun c => ((tv.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name).contains c.name)).map
                (fun c => { c with aggKind := .groupKey })
              rw [← hkeyColsEq]
              rw [List.drop_left]
              have hneF : (aggCols.length != aggs.length) = false := bne_eq_false_iff_eq.mpr haggLen
              simp only [hneF, Bool.false_eq_true, ↓reduceIte]
              rcases extractAllRowsKeyVals_typed hkeyFind tv.rows (hcolsEq ▸ hrows.to_forall) with
                ⟨rawKeys, hrawEq, hrawWf⟩
              rw [← hgkNames] at hrawEq
              simp only [hrawEq]
              have hsortedGksWf : ∀ gk ∈ (if ((tv.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name).isEmpty && tv.rows.isEmpty
                  then [[]] else dedupAdjacentBy valListEq (insertionSortBy valListLt rawKeys)),
                  CellsWf prog gk keyColsEval := by
                intro gk hgk
                split at hgk
                · rename_i hempBoth
                  simp only [Bool.and_eq_true] at hempBoth
                  simp only [List.mem_singleton] at hgk; subst hgk
                  have hkcNil : keyColsEval = [] := by
                    dsimp only [keyColsEval]
                    rw [List.isEmpty_iff.mp hempBoth.1]
                    simp
                  rw [hkcNil]; exact .nil
                · exact hrawWf gk (mem_insertionSortBy _ gk _ (mem_dedupAdjacentBy _ gk _ hgk))
              have hdkIdxSome : distinctKey.isSome = true → (distinctKey.bind (lookupColIdx? tv.cols)).isSome = true := by
                intro hdkS
                rcases hdkSomeProp hdkS with ⟨dk, rfl, hfcSome⟩
                simp only [Option.bind_some]
                rw [Option.isSome_iff_exists] at hfcSome
                rcases hfcSome with ⟨dkCol, hfc⟩
                unfold TableTy.findCol? at hfc
                rw [← hcolsEq] at hfc
                rcases lookupColIdx?_of_find? hfc with ⟨idx, hlook, _⟩
                rw [hlook]; rfl
              have houtSchemaWf := summarize_schemaWf httWf haggProps (hkeyColsEq ▸ houtDist)
                (rt := (tt.rowTags.union dkTags).union pc) (ot := TagSet.empty.union pc) (distinctKey := distinctKey)
              rw [← hkeyColsEq] at houtSchemaWf
              exact evalSummarizeGroups_sound (evalRowExpr fuel' prog env) _ w1 hw1 hcolsEq
                (fun c hc => (httProps c hc).1) hrows.to_forall rfl rfl rfl houtSchemaWf hdkIdxSome hagg
                (fun r re sTy rTags hrC hre => ihRE hprog env tt.cols r re sTy rTags henv (fun c hc => (httProps c hc).1) hrC hre)
                _ hsortedGksWf
      | suppressSmallGroups inp minK distinctBy mode =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            injection hchk with hp; subst hp
            have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
            | outOfFuel => exact .outOfFuel
            | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
            | wrong => rw [houtI] at hevI; nomatch hevI
            | ok iv w1 =>
              rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
              cases hiv with | @table tv _ hcols hschema hrows =>
              have hcolsEq : tv.cols = tt.cols := hcols
              rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
              let supF (m : SuppressMode) (c : ColSpec) : ColSpec :=
                let base :=
                  match c.aggKind with
                  | .groupKey => if c.bucketed then { c with tags := pc, aggKind := .raw } else { c with aggKind := .raw }
                  | .blending => { c with tags := pc, aggKind := .raw }
                  | .nonBlending | .raw => { c with aggKind := .raw }
                match m, c.aggKind with
                | .maskComplementary, .blending | .maskComplementary, .nonBlending =>
                  { base with ty := ensureOptionScalar base.ty, bucketed := false }
                | _, _ => base
              have hsupNames : (tt.cols.map (supF mode)).map ColSpec.name = tt.cols.map ColSpec.name := by
                induction tt.cols with
                | nil => rfl
                | cons c cs ih =>
                  simp only [List.map_cons, ih, supF]
                  cases mode <;> cases c.aggKind <;> try simp
                  all_goals (cases c.bucketed <;> simp)
              have hsupProps : ∀ c ∈ tt.cols.map (supF mode),
                  validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
                rcases httProps o ho with ⟨hv, hb⟩
                dsimp only [supF]
                cases mode
                · cases hoA : o.aggKind
                  · exact ⟨hv, hb, rfl⟩
                  · cases hoB : o.bucketed
                    · dsimp only; exact ⟨hv, fun h => by simp at h, rfl⟩
                    · dsimp only; exact ⟨hv, fun _ => hb hoB, rfl⟩
                  · exact ⟨hv, hb, rfl⟩
                  · exact ⟨hv, hb, rfl⟩
                · cases hoA : o.aggKind
                  · exact ⟨hv, hb, rfl⟩
                  · cases hoB : o.bucketed
                    · dsimp only; exact ⟨hv, fun h => by simp at h, rfl⟩
                    · dsimp only; exact ⟨hv, fun _ => hb hoB, rfl⟩
                  · exact ⟨(ensureOptionScalar_eq_option_base hv).2, fun h => by simp at h, rfl⟩
                  · exact ⟨(ensureOptionScalar_eq_option_base hv).2, fun h => by simp at h, rfl⟩
              have houtSchema := rawTableSchemaWf_of_props
                ((TagSet.unionList ((tt.cols.filter (fun c => decide (c.aggKind = .groupKey) && !c.bucketed)).map ColSpec.tags)).union pc |>.union pc)
                (tt.orderTags.union pc) (hsupNames ▸ httUniq) hsupProps
              have hsupColsEq : tv.cols.map (supF mode) = tt.cols.map (supF mode) := by
                rw [hcolsEq]
              cases mode with
              | drop =>
                have hsupTys : tt.cols.map ColSpec.ty = (tt.cols.map (supF .drop)).map ColSpec.ty := by
                  induction tt.cols with
                  | nil => rfl
                  | cons c cs ih =>
                    simp only [List.map_cons, ih, supF]
                    cases c.aggKind <;> try simp
                    cases c.bucketed <;> simp
                apply OutcomeWf.ok _ hw1
                refine .table hsupColsEq houtSchema (RowsWf.of_forall_raw ?_)
                intro r hr; dsimp only at hr; rw [List.mem_map] at hr; rcases hr with ⟨orig, horigF, rfl⟩
                exact (hrows.to_forall orig (List.mem_filter.mp horigF).1).congr_ty hsupTys
              | maskComplementary =>
                let rec maskWf : ∀ {cs : List ColSpec} {vs : List Val},
                    (∀ c ∈ cs, validScalarTy prog c.ty = true) →
                    CellsWf prog vs cs →
                    CellsWf prog (maskAggCells cs vs) (cs.map (supF .maskComplementary))
                  | [], [], _, .nil => .nil
                  | { name := cn, ty := cty, tags := ctags, bucketed := cbuck, aggKind := cagg } :: cs, v :: vs, hcs, .cons hv htl => by
                    dsimp only [maskAggCells, List.map_cons, supF]
                    cases cagg
                    · exact .cons hv (maskWf (fun d hd => hcs d (.tail _ hd)) htl)
                    · cases cbuck <;> exact .cons hv (maskWf (fun d hd => hcs d (.tail _ hd)) htl)
                    · exact .cons (optNone_ensureOption_sound cty) (maskWf (fun d hd => hcs d (.tail _ hd)) htl)
                    · exact .cons (optNone_ensureOption_sound cty) (maskWf (fun d hd => hcs d (.tail _ hd)) htl)
                let rec wrapWf : ∀ {cs : List ColSpec} {vs : List Val},
                    (∀ c ∈ cs, validScalarTy prog c.ty = true) →
                    CellsWf prog vs cs →
                    CellsWf prog (wrapAggCells cs vs) (cs.map (supF .maskComplementary))
                  | [], [], _, .nil => .nil
                  | { name := cn, ty := cty, tags := ctags, bucketed := cbuck, aggKind := cagg } :: cs, v :: vs, hcs, .cons hv htl => by
                    dsimp only [wrapAggCells, List.map_cons, supF]
                    cases cagg
                    · exact .cons hv (wrapWf (fun d hd => hcs d (.tail _ hd)) htl)
                    · cases cbuck <;> exact .cons hv (wrapWf (fun d hd => hcs d (.tail _ hd)) htl)
                    · exact .cons (wrapIntoOptionVal_sound (hcs _ (.head _)) hv) (wrapWf (fun d hd => hcs d (.tail _ hd)) htl)
                    · exact .cons (wrapIntoOptionVal_sound (hcs _ (.head _)) hv) (wrapWf (fun d hd => hcs d (.tail _ hd)) htl)
                apply OutcomeWf.ok _ hw1
                refine .table hsupColsEq houtSchema (RowsWf.of_forall_raw ?_)
                intro r hr; dsimp only at hr; rw [List.mem_map] at hr; rcases hr with ⟨orig, horigMem, rfl⟩
                have horigWf := hrows.to_forall orig horigMem
                have hif : ∀ (b : Bool),
                    CellsWf prog (if b = true then ({ cells := maskAggCells tv.cols orig.cells, groupMeta := none } : TableRow) else ({ cells := wrapAggCells tv.cols orig.cells, groupMeta := none } : TableRow)).cells (tt.cols.map (supF .maskComplementary)) := by
                  intro b; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [hcolsEq]
                  · exact wrapWf (fun c hc => (httProps c hc).1) horigWf
                  · exact maskWf (fun c hc => (httProps c hc).1) horigWf
                exact hif _
      | window inp items =>
        have hchkTrue := checkPlan_inSpec_true hchk
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            cases ha : applyWindowItems tt.orderTags (tt.cols.map (fun c => { c with aggKind := .raw })) items with
            | error _ => rw [ha] at hchk; contradiction
            | ok outCols =>
              rw [ha] at hchk; dsimp only at hchk
              split at hchk <;> try contradiction
              rename_i houtDist
              injection hchk with hp; subst hp
              rw [hchkTrue]; dsimp only
              have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
              cases houtI : evalPlan fuel' prog env pc w inp with
              | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
              | wrong => rw [houtI] at hevI; nomatch hevI
              | ok iv w1 =>
                rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                cases hiv with | @table tv _ hcols hschema hrows =>
                have hcolsEq : tv.cols = tt.cols := hcols
                rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                have hinitUniq : distinctIdents ((tv.cols.map (fun c => { c with aggKind := .raw })).map ColSpec.name) = true := by
                  rw [hcolsEq]
                  have hn : (tt.cols.map (fun c => { c with aggKind := .raw })).map ColSpec.name = tt.cols.map ColSpec.name := by
                    induction tt.cols <;> simp [*]
                  rw [hn]; exact httUniq
                have hinitProps : ∀ c ∈ tv.cols.map (fun c => { c with aggKind := .raw }),
                    validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                  rw [hcolsEq]; intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
                  exact ⟨(httProps o ho).1, (httProps o ho).2, rfl⟩
                have hinitRows : RowsWf prog (tv.rows.map (fun r => { r with groupMeta := none }))
                    (tv.cols.map (fun c => { c with aggKind := .raw })) false false := by
                  rw [hcolsEq]; exact hrows.congr_ty_raw (map_ty_with_aggKind tt.cols .raw).symm
                rcases evalWindowItems_sound (ot := tt.orderTags) items
                  { cols := tv.cols.map (fun c => { c with aggKind := .raw })
                    rows := tv.rows.map (fun r => { r with groupMeta := none }) }
                  outCols hinitUniq hinitProps hinitRows
                  (by dsimp only; rw [hcolsEq]; exact ha) with ⟨winTV, hwinEq, hwinRows, houtProps⟩
                simp only [hwinEq]
                exact .ok (.table rfl (rawTableSchemaWf_of_props _ _ houtDist houtProps) hwinRows) hw1
      | fillGaps inp col stepMicros over fill =>
        have hchkTrue := checkPlan_inSpec_true hchk
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            cases htc : tt.findCol? col with
            | none => rw [htc] at hchk; contradiction
            | some tCol =>
              rw [htc] at hchk; dsimp only at hchk
              split at hchk <;> try contradiction
              split at hchk <;> try contradiction
              split at hchk <;> try contradiction
              injection hchk with hp; subst hp
              rw [hchkTrue]; dsimp only
              have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
              cases houtI : evalPlan fuel' prog env pc w inp with
              | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
              | wrong => rw [houtI] at hevI; nomatch hevI
              | ok iv w1 =>
                rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                cases hiv with | @table tv _ _ hschema hrows =>
                rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                let fgF : ColSpec → ColSpec := fun c =>
                  if c.name == col || over.contains c.name then { c with aggKind := .raw, bucketed := false }
                  else { c with tags := (c.tags.union ((tt.rowTags.union tCol.tags).union (TagSet.unionList (over.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))))).union tt.orderTags, aggKind := .raw, bucketed := false }
                have hfgNames : (tt.cols.map fgF).map ColSpec.name = tt.cols.map ColSpec.name := by
                  induction tt.cols with
                  | nil => rfl
                  | cons c cs ih => simp only [List.map_cons, ih, fgF]; split <;> simp
                have hfgTys : tt.cols.map ColSpec.ty = (tt.cols.map fgF).map ColSpec.ty := by
                  induction tt.cols with
                  | nil => rfl
                  | cons c cs ih => simp only [List.map_cons, ih, fgF]; split <;> simp
                have hfgProps : ∀ c ∈ tt.cols.map fgF,
                    validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                  intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
                  dsimp only [fgF]; split <;> exact ⟨(httProps o ho).1, fun h => by simp at h, rfl⟩
                apply OutcomeWf.ok _ hw1
                refine .table rfl (rawTableSchemaWf_of_props _ _ (hfgNames ▸ httUniq) hfgProps) (RowsWf.of_forall_raw ?_)
                intro r hr
                have hmem := mem_insertionSortBy _ r _ hr
                rw [List.mem_map] at hmem; rcases hmem with ⟨orig, horig, rfl⟩
                exact (hrows.to_forall orig horig).congr_ty hfgTys
      | pivotWider inp namesFrom valuesFrom staticCols fill =>
        have hchkTrue := checkPlan_inSpec_true hchk
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            dsimp only at hchk
            split at hchk <;> try contradiction
            cases hnC : tt.findCol? namesFrom <;> cases hvC : tt.findCol? valuesFrom <;>
              simp only [hnC, hvC] at hchk <;> try contradiction
            case some.some nCol vCol =>
              split at hchk <;> try contradiction
              cases hfill : checkLiteral prog TagSet.empty fill with
              | error _ => rw [hfill] at hchk; contradiction
              | ok fillLTy =>
                rw [hfill] at hchk; dsimp only at hchk
                split at hchk <;> try contradiction
                rename_i hfillTy
                simp only [Bool.not_eq_true', Bool.not_eq_false, decide_eq_true_eq] at hfillTy
                split at hchk <;> try contradiction
                rename_i houtDist
                injection hchk with hp; subst hp
                rw [hchkTrue]; dsimp only
                have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
                cases houtI : evalPlan fuel' prog env pc w inp with
                | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
                | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
                | outOfFuel => exact .outOfFuel
                | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
                | wrong => rw [houtI] at hevI; nomatch hevI
                | ok iv w1 =>
                  rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                  cases hiv with | @table tv _ hcols hschema hrows =>
                  have hcolsEq : tv.cols = tt.cols := hcols
                  rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                  unfold TableTy.findCol? at hnC hvC
                  rw [← hcolsEq] at hnC hvC
                  rcases lookupColIdx?_of_find? hnC with ⟨nIdx, hlookN, _⟩
                  rcases lookupColIdx?_of_find? hvC with ⟨vIdx, hlookV, hgetVCol⟩
                  simp only [hlookN, hlookV]
                  let idCols := (tv.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map
                    (fun c => { c with aggKind := .raw })
                  have hidKeyFind : ∀ kc ∈ idCols, ∃ origC, tv.cols.find? (fun c => c.name == kc.name) = some origC ∧ origC.ty = kc.ty := by
                    intro kc hkc; rw [List.mem_map] at hkc; rcases hkc with ⟨orig, horigF, rfl⟩
                    have horigIn := (List.mem_filter.mp horigF).1
                    have huniqTv : distinctIdents (tv.cols.map ColSpec.name) = true := hcolsEq ▸ httUniq
                    have hfindU : ∀ (cs : List ColSpec), distinctIdents (cs.map ColSpec.name) = true →
                        orig ∈ cs → cs.find? (fun x => x.name == orig.name) = some orig := by
                      intro cs hcs horigCs
                      induction cs with
                      | nil => nomatch horigCs
                      | cons d ds ih =>
                        rcases distinctIdents_not_mem hcs with ⟨hdnot, hdtl⟩
                        simp only [List.find?]
                        rcases List.mem_cons.mp horigCs with rfl | htl
                        · simp
                        · have hne : (d.name == orig.name) = false := by
                            cases hdo : (d.name == orig.name)
                            · rfl
                            · exfalso; exact hdnot ((beq_iff_eq.mp hdo) ▸ List.mem_map_of_mem htl)
                          simp [hne, ih hdtl htl]
                    exact ⟨orig, hfindU tv.cols huniqTv horigIn, rfl⟩
                  rcases extractAllRowsKeyVals_typed hidKeyFind tv.rows (hcolsEq ▸ hrows.to_forall) with
                    ⟨rawIds, hrawIdsEq, hrawIdsWf⟩
                  erw [hrawIdsEq]; dsimp only
                  have hfillValWf : ValWf prog (evalLiteral fill) vCol.ty.toTy :=
                    hfillTy ▸ checkLiteral_sound hfill
                  have houtProps : ∀ c ∈ ((tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun c => { c with aggKind := .raw }) ++
                      staticCols.map (fun sc => { name := sc, ty := vCol.ty, tags := ((nCol.tags.union vCol.tags).union ((tt.rowTags.union nCol.tags).union (TagSet.unionList (((tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun c => { c with aggKind := .raw })).map ColSpec.tags)))).union tt.orderTags, bucketed := false, aggKind := .raw })),
                      validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                    intro c hc; rw [List.mem_append] at hc
                    rcases hc with hl | hr
                    · rw [List.mem_map] at hl; rcases hl with ⟨o, hoF, rfl⟩
                      rcases httProps o (List.mem_filter.mp hoF).1 with ⟨hv, hb⟩
                      exact ⟨hv, hb, rfl⟩
                    · rw [List.mem_map] at hr; rcases hr with ⟨_, _, rfl⟩
                      have hvIn : vCol ∈ tt.cols := hcolsEq ▸ List.mem_of_find?_eq_some hvC
                      exact ⟨(httProps vCol hvIn).1, fun h => by simp at h, rfl⟩
                  apply OutcomeWf.ok _ hw1
                  refine .table rfl (rawTableSchemaWf_of_props _ _ houtDist houtProps) (RowsWf.of_forall_raw ?_)
                  intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨idKey, hidMem, rfl⟩
                  have hidWf : CellsWf prog idKey ((tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun c => { c with aggKind := .raw })) := by
                    rw [← hcolsEq]
                    exact hrawIdsWf idKey (mem_insertionSortBy _ idKey _ (mem_dedupAdjacentBy _ idKey _ hidMem))
                  have hpivWf : ∀ (scs : List Ident) (ct : TagSet),
                      CellsWf prog (scs.map (fun sc =>
                        match (tv.rows.filter (fun (r : TableRow) => match extractKeyVals tv.cols (idCols.map ColSpec.name) r with | some kv => valListEq kv idKey | none => false)).find?
                          (fun (r : TableRow) => match (r.cells[nIdx]? : Option Val) with | some (Val.text cellStr) => cellStr == sc | _ => false) with
                        | some matchRow => matchRow.cells[vIdx]?.getD (evalLiteral fill)
                        | none => evalLiteral fill))
                        (scs.map (fun sc => ({ name := sc, ty := vCol.ty, tags := ct, bucketed := false, aggKind := .raw } : ColSpec))) := by
                    intro scs ct
                    induction scs with
                    | nil => exact .nil
                    | cons sc scTl ih =>
                      dsimp only [List.map]
                      refine .cons ?_ ih
                      split
                      · rename_i matchRow hmr
                        have hmIn := (List.mem_filter.mp (List.mem_of_find?_eq_some hmr)).1
                        have hmCells : CellsWf prog matchRow.cells tv.cols := hcolsEq ▸ hrows.to_forall matchRow hmIn
                        rcases hmCells.getElem?_wf hgetVCol with ⟨mv, hmvGet, hmvWf⟩
                        rw [hmvGet]; exact hmvWf
                      · exact hfillValWf
                  exact hidWf.append (hpivWf staticCols _)
      | crosstab inp rowsCol colsCol valuesCol fill =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            cases hrC : tt.findCol? rowsCol <;> cases hcC : tt.findCol? colsCol <;> cases hvC : tt.findCol? valuesCol <;>
              simp [hrC, hcC, hvC] at hchk
            cases hfill : checkLiteral prog TagSet.empty fill with
            | error _ => simp [hfill] at hchk
            | ok fillLTy =>
              simp only [hfill] at hchk
              split at hchk <;> try contradiction
              injection hchk with hp; subst hp
              have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
              cases houtI : evalPlan fuel' prog env pc w inp with
              | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
              | wrong => rw [houtI] at hevI; nomatch hevI
              | ok iv w1 =>
                rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                cases hiv with | @table tv _ hcols _ _ =>
                unfold TableTy.findCol? at hrC hcC hvC
                rw [← hcols] at hrC hcC hvC
                rcases lookupColIdx?_of_find? hrC with ⟨rIdx, hlookR, _⟩
                rcases lookupColIdx?_of_find? hcC with ⟨cIdx, hlookC, _⟩
                rcases lookupColIdx?_of_find? hvC with ⟨vIdx, hlookV, _⟩
                simp only [hlookR, hlookC, hlookV]
                exact .ok (.dynTable _ _ _) hw1
      | redact inp col replacement =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases inP <;> try contradiction
          case table tt =>
            cases hc : tt.findCol? col with
            | none => simp [hc] at hchk
            | some targetCol =>
              simp only [hc] at hchk
              split at hchk <;> try contradiction
              injection hchk with hp; subst hp
              have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
              cases houtI : evalPlan fuel' prog env pc w inp with
              | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
              | outOfFuel => exact .outOfFuel
              | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
              | wrong => rw [houtI] at hevI; nomatch hevI
              | ok iv w1 =>
                rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                cases hiv with | @table tv _ hcols hschema hrows =>
                have hcolsEq : tv.cols = tt.cols := hcols
                rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                unfold TableTy.findCol? at hc; rw [← hcolsEq] at hc
                rcases lookupColIdx?_of_find? hc with ⟨cIdx, hlook, _⟩
                simp only [hlook]
                let redF : ColSpec → ColSpec := fun c =>
                  if c.name == col then { c with ty := .text, tags := pc, bucketed := false, aggKind := .raw }
                  else { c with aggKind := .raw }
                have hredNames : (tt.cols.map redF).map ColSpec.name = tt.cols.map ColSpec.name := by
                  induction tt.cols with
                  | nil => rfl
                  | cons c cs ih => simp only [List.map_cons, ih, redF]; split <;> simp
                have hredProps : ∀ c ∈ tt.cols.map redF,
                    validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                  intro c hc0; rw [List.mem_map] at hc0; rcases hc0 with ⟨o, ho, rfl⟩
                  dsimp only [redF]; split
                  · exact ⟨rfl, fun h => by simp at h, rfl⟩
                  · exact ⟨(httProps o ho).1, (httProps o ho).2, rfl⟩
                apply OutcomeWf.ok _ hw1
                refine .table (by rw [hcolsEq]) (rawTableSchemaWf_of_props _ _ (hredNames ▸ httUniq) hredProps)
                  (RowsWf.of_forall_raw ?_)
                intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨orig, horig, rfl⟩
                rw [← hcolsEq]
                apply cellsWf_set_by_name redF (hcolsEq ▸ httUniq) hlook (hcolsEq ▸ hrows.to_forall orig horig)
                intro c _; dsimp only [redF]; split
                · exact .text _
                · rfl
      | pseudonymize inp col secretExpr =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases hs : checkExpr prog (envToTyEnv env) [] pc inSpec secretExpr with
          | error _ => simp [hs] at hchk
          | ok secLTy =>
            simp only [hs] at hchk
            cases inP <;> cases hsty : secLTy.ty <;> simp only [hsty] at hchk <;> try contradiction
            case table.secret tt _ =>
              cases hc : tt.findCol? col with
              | none => simp [hc] at hchk
              | some targetCol =>
                simp only [hc] at hchk
                split at hchk <;> try contradiction
                injection hchk with hp; subst hp
                have hevI := ihP hprog env pc inSpec w inp (.table tt) henv hw hi
                cases houtI : evalPlan fuel' prog env pc w inp with
                | stopped b w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
                | failed m w1 => rw [houtI] at hevI; exact hevI.abort_non_ok (by simp)
                | outOfFuel => exact .outOfFuel
                | jumped _ _ _ => exact absurd houtI hevI.not_jumped_nil
                | wrong => rw [houtI] at hevI; nomatch hevI
                | ok iv w1 =>
                  rw [houtI] at hevI; cases hevI with | ok hiv hw1 =>
                  cases hiv with | @table tv _ hcols hschema hrows =>
                  dsimp only
                  have hevS := ihE hprog env [] pc inSpec w1 secretExpr secLTy henv hw1 hs
                  rw [hsty] at hevS
                  cases houtS : eval fuel' prog env pc w1 secretExpr with
                  | stopped b w2 => dsimp only; rw [houtS] at hevS; exact hevS.abort_non_ok (by simp)
                  | failed m w2 => dsimp only; rw [houtS] at hevS; exact hevS.abort_non_ok (by simp)
                  | outOfFuel => dsimp only; exact .outOfFuel
                  | jumped _ _ _ => exact absurd houtS hevS.not_jumped_nil
                  | wrong => rw [houtS] at hevS; nomatch hevS
                  | ok sv w2 =>
                    rw [houtS] at hevS; cases hevS with | ok hsv hw2 =>
                    cases hsv with | capSecret h sName =>
                    dsimp only
                    have hcolsEq : tv.cols = tt.cols := hcols
                    rcases tableSchemaWf_cols_props (by simpa [PlanTy.toLTy] using hschema) with ⟨httUniq, httProps⟩
                    unfold TableTy.findCol? at hc; rw [← hcolsEq] at hc
                    rcases lookupColIdx?_of_find? hc with ⟨cIdx, hlook, _⟩
                    simp only [hlook]
                    have htargetEqCols : tv.cols.map (fun c =>
                        if c.name == col then { c with ty := .text, tags := (c.tags.remove "pii").union pc, bucketed := false, aggKind := .raw }
                        else { c with aggKind := .raw }) =
                        tt.cols.map (fun c =>
                          if c.name == col then { c with ty := .text, tags := (targetCol.tags.remove "pii").union pc, bucketed := false, aggKind := .raw }
                          else { c with aggKind := .raw }) := by
                      rw [hcolsEq]
                      have htIn : targetCol ∈ tt.cols := List.mem_of_find?_eq_some (hcolsEq ▸ hc)
                      have htName : targetCol.name = col := find?_name_eq ColSpec.name (hcolsEq ▸ hc)
                      have huniqEq : ∀ c ∈ tt.cols, (c.name == col) = true → c = targetCol := by
                        intro c hcIn hcn
                        have hceqt : c.name = targetCol.name := (beq_iff_eq.mp hcn).trans htName.symm
                        clear hc hlook httProps
                        generalize hcsEq : tt.cols = cs at httUniq htIn hcIn
                        clear hcsEq
                        induction cs with
                        | nil => nomatch hcIn
                        | cons d ds ih =>
                          rcases distinctIdents_not_mem httUniq with ⟨hdnot, hdtl⟩
                          rcases List.mem_cons.mp hcIn with rfl | hctl
                          · rcases List.mem_cons.mp htIn with rfl | httl
                            · rfl
                            · exfalso; exact hdnot (hceqt ▸ List.mem_map_of_mem httl)
                          · rcases List.mem_cons.mp htIn with rfl | httl
                            · exfalso; exact hdnot (hceqt.symm ▸ List.mem_map_of_mem hctl)
                            · exact ih hdtl httl hctl
                      have hmapCongr : ∀ (cs : List ColSpec), (∀ x ∈ cs, x ∈ tt.cols) →
                          cs.map (fun c => if c.name == col then { c with ty := .text, tags := (c.tags.remove "pii").union pc, bucketed := false, aggKind := .raw } else { c with aggKind := .raw }) =
                          cs.map (fun c => if c.name == col then { c with ty := .text, tags := (targetCol.tags.remove "pii").union pc, bucketed := false, aggKind := .raw } else { c with aggKind := .raw }) := by
                        intro cs hsub
                        induction cs with
                        | nil => rfl
                        | cons d ds ih =>
                          simp only [List.map_cons, ih (fun x hx => hsub x (.tail _ hx))]
                          cases hdn : (d.name == col)
                          · simp
                          · rw [huniqEq d (hsub d (.head _)) hdn]
                      exact hmapCongr tt.cols (fun _ h => h)
                    let psF : ColSpec → ColSpec := fun c =>
                      if c.name == col then { c with ty := .text, tags := (targetCol.tags.remove "pii").union pc, bucketed := false, aggKind := .raw }
                      else { c with aggKind := .raw }
                    have hpsNames : (tt.cols.map psF).map ColSpec.name = tt.cols.map ColSpec.name := by
                      induction tt.cols with
                      | nil => rfl
                      | cons c cs ih => simp only [List.map_cons, ih, psF]; split <;> simp
                    have hpsProps : ∀ c ∈ tt.cols.map psF,
                        validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
                      intro c hc0; rw [List.mem_map] at hc0; rcases hc0 with ⟨o, ho, rfl⟩
                      dsimp only [psF]; split
                      · exact ⟨rfl, fun h => by simp at h, rfl⟩
                      · exact ⟨(httProps o ho).1, (httProps o ho).2, rfl⟩
                    rcases mapPseudonymizeRows_sound (pc := pc) _ (hcolsEq ▸ httUniq) hlook rfl tv.rows
                      (hcolsEq ▸ hrows.to_forall) with ⟨outRows, hpsEq, houtRowsWf⟩
                    erw [hpsEq]
                    exact .ok (.table htargetEqCols
                      (rawTableSchemaWf_of_props _ _ (hpsNames ▸ httUniq) hpsProps)
                      (htargetEqCols ▸ houtRowsWf)) hw2

/-! ## Theorem 1 — Exported Top-Level Soundness Theorems -/

/-- **Theorem 1A (Expression Schema & Type Soundness):**
    In any well-typed Dana Core IR program (`checkProgram prog = .ok ()`), evaluating a
    well-typed expression `e` at any fuel budget never reaches `Outcome.wrong` (stuck state),
    closed evaluation (`jenv = []`) never escapes with an uncaught `Outcome.jumped`, and
    every `Outcome.ok v w'` strictly satisfies `ValWf prog v lty.ty` and `WorldWf prog w'`. -/
theorem theorem1_expr_soundness {prog : Program} {env : Env} {pc : TagSet} {inSpec : Bool}
    {w : World} {e : Expr} {lty : LTy} (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (henv : EnvWf prog env)
    (hw : WorldWf prog w)
    (hchk : checkExpr prog (envToTyEnv env) [] pc inSpec e = .ok lty) :
    let out := eval fuel prog env pc w e
    out ≠ .wrong ∧
    (∀ lbl vs w', out ≠ .jumped lbl vs w') ∧
    (∀ v w', out = .ok v w' → ValWf prog v lty.ty ∧ WorldWf prog w') := by
  have hout := (eval_fuel_sound prog fuel).2.2.1 hprog env [] pc inSpec w e lty henv hw hchk
  refine ⟨hout.not_wrong, fun lbl vs w' => hout.not_jumped_nil, ?_⟩
  intro v w' heq
  rw [heq] at hout
  cases hout with | ok hv hw' => exact ⟨hv, hw'⟩

/-- **Theorem 1B (Relational Plan Schema Soundness):**
    Well-typed pure relational `Plan`s never evaluate to `Outcome.wrong` or `Outcome.jumped`,
    and every `Outcome.ok v w'` produces a `TableVal` (or `DynamicTable` for `Crosstab`)
    matching the exact statically inferred `PlanTy` schema (`tv.cols = outTT.cols`,
    `TableSchemaWf`, unified `Option`, and row-cell typing `RowsWf`). -/
theorem theorem1_plan_soundness {prog : Program} {env : Env} {pc : TagSet} {inSpec : Bool}
    {w : World} {plan : Plan} {pTy : PlanTy} (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (henv : EnvWf prog env)
    (hw : WorldWf prog w)
    (hchk : checkPlan prog (envToTyEnv env) pc inSpec plan = .ok pTy) :
    let out := evalPlan fuel prog env pc w plan
    out ≠ .wrong ∧
    (∀ lbl vs w', out ≠ .jumped lbl vs w') ∧
    (∀ v w', out = .ok v w' → ValWf prog v (pTy.toLTy pc).ty ∧ WorldWf prog w') := by
  have hout := (eval_fuel_sound prog fuel).2.2.2.2 hprog env pc inSpec w plan pTy henv hw hchk
  refine ⟨hout.not_wrong, fun lbl vs w' => hout.not_jumped_nil, ?_⟩
  intro v w' heq
  rw [heq] at hout
  cases hout with | ok hv hw' => exact ⟨hv, hw'⟩

theorem mkEntryEnv_sound (prog : Program) :
    ∀ (params : List (Ident × LTy)),
      (∀ p ∈ params, isCapabilityTy p.2.ty = true) →
      ∃ initEnv, mkEntryEnv prog params = some initEnv ∧
        EnvWf prog initEnv ∧ envToTyEnv initEnv = params
  | [], _ => ⟨[], rfl, .nil, rfl⟩
  | (pName, pLTy) :: rest, hall => by
    have hcap := hall (pName, pLTy) (.head _)
    have hbuild : ∃ cv, buildEntryCapVal prog pLTy.ty = some cv ∧ ValWf prog cv pLTy.ty := by
      cases hty : pLTy.ty <;> rw [hty] at hcap <;> try simp [isCapabilityTy] at hcap
      · exact ⟨_, rfl, .capArgs⟩
      · exact ⟨_, rfl, .capClock⟩
      · exact ⟨_, rfl, .capConsole .real _⟩
      · exact ⟨_, rfl, .capReadFiles .real⟩
      · exact ⟨_, rfl, .capWriteFiles .real _ _⟩
      · exact ⟨_, rfl, .capReadDB .real _⟩
      · exact ⟨_, rfl, .capWriteTable .real _ _ _ _ _⟩
      · exact ⟨_, rfl, .capRawReadDB _⟩
      · exact ⟨_, rfl, .capHttpsAllow .real _ _⟩
      · exact ⟨_, rfl, .capSecret .real _⟩
      · exact ⟨_, rfl, .capDeclassify _⟩
    rcases hbuild with ⟨cv, hcvEq, hcvWf⟩
    rcases mkEntryEnv_sound prog rest (fun q hq => hall q (.tail _ hq)) with ⟨tlEnv, htlEq, htlWf, htlTy⟩
    refine ⟨{ name := pName, lty := pLTy, val := cv } :: tlEnv,
      by simp [mkEntryEnv, hcvEq, htlEq],
      .cons hcvWf htlWf,
      congrArg ((pName, pLTy) :: ·) htlTy⟩

/-- **Theorem 1C (Whole-Program Soundness):**
    For any well-typed Dana Core IR program (`checkProgram prog = .ok ()`) and well-formed
    initial `World`, running `prog` either exhausts fuel (`outOfFuel`) or succeeds with a
    canonical `ExecReport` (`runProgram fuel prog initWorld = .ok rep`) — never failing due
    to a runtime type/schema mismatch (`wrong`) or uncaught `Jump`. -/
theorem theorem1_program_soundness {prog : Program} {initWorld : World} (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (hw : WorldWf prog initWorld) :
    (∃ mainName mainFn initEnv,
      prog.entry = some mainName ∧
      prog.findFun? mainName = some mainFn ∧
      mkEntryEnv prog mainFn.params.reverse = some initEnv ∧
      eval fuel prog initEnv TagSet.empty initWorld mainFn.body = .outOfFuel) ∨
    (∃ rep, runProgram fuel prog initWorld = .ok rep) := by
  have hprogSave := hprog
  simp only [checkProgram, bind, Except.bind] at hprog
  split at hprog <;> try contradiction
  split at hprog <;> try contradiction
  cases hp : checkPolicyWf prog <;> simp only [hp] at hprog <;> try contradiction
  cases hd : checkDataDecls prog <;> simp only [hd] at hprog <;> try contradiction
  cases hs : checkSchemaDecls prog <;> simp only [hs] at hprog <;> try contradiction
  cases hc : checkConstDecls prog <;> simp only [hc] at hprog <;> try contradiction
  split at hprog <;> try contradiction
  cases hf : checkFunDecls prog prog.funs <;> simp only [hf] at hprog <;> try contradiction
  unfold runProgram
  simp only [hprogSave, bind, Except.bind]
  cases hent : prog.entry with
  | none =>
    exact Or.inr ⟨_, rfl⟩
  | some mainName =>
    rw [hent] at hprog; dsimp only at hprog
    cases hfind : prog.findFun? mainName with
    | none => rw [hfind] at hprog; simp at hprog
    | some mainFn =>
      rw [hfind] at hprog; dsimp only at hprog; simp only [hfind]
      split at hprog <;> try contradiction
      split at hprog <;> try contradiction
      rename_i hpcNotNonEmpty
      split at hprog <;> try contradiction
      rename_i hcapParams
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true] at hpcNotNonEmpty hcapParams
      have hrevCaps : ∀ p ∈ mainFn.params.reverse, isCapabilityTy p.2.ty = true := by
        intro p hpMem; exact (hcapParams p (List.mem_reverse.mp hpMem)).1
      rcases mkEntryEnv_sound prog mainFn.params.reverse hrevCaps with ⟨initEnv, hmkEq, hinitWf, hinitTy⟩
      simp only [hmkEq]
      cases checkEntryExportGate mainFn.params initWorld with
      | some bug => exact Or.inr ⟨_, rfl⟩
      | none =>
        rcases checkFunDecl_valid hprogSave hfind with ⟨bodyLTy, hbodyChk, _⟩
        have hpcEmpty : mainFn.pc = TagSet.empty := by
          cases hpcMk : mainFn.pc with | mk elems inv =>
          simp only [TagSet.isEmpty, hpcMk, List.isEmpty_iff] at hpcNotNonEmpty
          subst hpcNotNonEmpty; rfl
        rw [hpcEmpty, ← hinitTy] at hbodyChk
        rcases theorem1_expr_soundness fuel hprogSave hinitWf hw hbodyChk with ⟨hnotWrong, hnotJumped, _⟩
        cases hout : eval fuel prog initEnv TagSet.empty initWorld mainFn.body with
        | outOfFuel =>
          exact Or.inl ⟨mainName, mainFn, initEnv, rfl, hfind, hmkEq, hout⟩
        | wrong => exact absurd hout hnotWrong
        | jumped lbl vs w' => exact absurd hout (hnotJumped lbl vs w')
        | ok v w' => exact Or.inr ⟨_, rfl⟩
        | stopped b w' => exact Or.inr ⟨_, rfl⟩
        | failed m w' => exact Or.inr ⟨_, rfl⟩

/-- **Theorem 1D (`SuppressSmallGroups` Tracked Group-Size Floor Invariant):**
    For any well-typed `SuppressSmallGroups(input, minK, distinctBy, mode)` plan,
    `minK ≥ prog.minGroupFloor ≥ 5` (where `prog.minGroupFloor ≥ 5` holds by definition
    of `Program.minGroupFloor`), and every output row relates to an input row from
    `input` according to the evaluator's tracked `groupMeta` counters:
    - in `.drop` mode, every surviving row satisfies `suppressGroupSize distinctBy origRow ≥ minK`;
    - in `.maskComplementary` mode, every output row is either unmasked with
      `suppressGroupSize distinctBy origRow ≥ minK` (aggregate cells wrapped in `Option`),
      or masked via `maskAggCells` (all aggregate cells replaced by `Val.optNone`). -/
theorem theorem1_suppress_small_groups_invariant {prog : Program} {env : Env} {pc : TagSet}
    {inSpec : Bool} {w w' : World} {inp : Plan} {minK : Nat} {distinctBy : Option Ident}
    {mode : SuppressMode} {pTy : PlanTy} {outTV : TableVal} (fuel : Nat)
    (hchk : checkPlan prog (envToTyEnv env) pc inSpec (.suppressSmallGroups inp minK distinctBy mode) = .ok pTy)
    (heval : evalPlan (fuel + 1) prog env pc w (.suppressSmallGroups inp minK distinctBy mode) = .ok (.table outTV) w') :
    minK ≥ prog.minGroupFloor ∧
    prog.minGroupFloor ≥ 5 ∧
    ∃ inTV w1,
      evalPlan fuel prog env pc w inp = .ok (.table inTV) w1 ∧
      ∀ outRow ∈ outTV.rows, ∃ origRow ∈ inTV.rows,
        match mode with
        | .drop =>
          outRow.cells = origRow.cells ∧
          suppressGroupSize distinctBy origRow ≥ minK
        | .maskComplementary =>
          (outRow.cells = wrapAggCells inTV.cols origRow.cells ∧
            suppressGroupSize distinctBy origRow ≥ minK) ∨
          (outRow.cells = maskAggCells inTV.cols origRow.cells) := by
  have hfloor5 : prog.minGroupFloor ≥ 5 := by
    unfold Program.minGroupFloor
    cases prog.policy with
    | none => decide
    | some pol => exact Nat.le_max_left 5 pol.minGroupSize
  unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
  cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
  | error _ => simp [hi] at hchk
  | ok inP =>
    simp only [hi] at hchk
    cases inP <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i hminKNotLt
    have hminKGe : minK ≥ prog.minGroupFloor := Nat.not_lt.mp hminKNotLt
    refine ⟨hminKGe, hfloor5, ?_⟩
    unfold evalPlan at heval; dsimp only at heval
    cases houtI : evalPlan fuel prog env pc w inp with
    | stopped _ _ | failed _ _ | outOfFuel | jumped _ _ _ | wrong =>
      rw [houtI] at heval; simp at heval
    | ok iv w1 =>
      rw [houtI] at heval
      cases iv <;> try (simp at heval)
      case table inTV =>
        refine ⟨inTV, w1, rfl, ?_⟩
        cases mode with
        | drop =>
          dsimp only at heval
          injection heval with hvalEq _
          injection hvalEq with htvEq; subst htvEq
          clear hchk houtI hi
          intro outRow houtMem
          dsimp only at houtMem
          rw [List.mem_map] at houtMem
          rcases houtMem with ⟨origRow, horigFilter, rfl⟩
          rcases List.mem_filter.mp horigFilter with ⟨horigIn, hgeDec⟩
          exact ⟨origRow, horigIn, rfl, of_decide_eq_true hgeDec⟩
        | maskComplementary =>
          dsimp only at heval
          injection heval with hvalEq _
          injection hvalEq with htvEq; subst htvEq
          clear hchk houtI hi
          intro outRow houtMem
          dsimp only at houtMem
          rcases List.mem_map.mp houtMem with ⟨origRow, horigIn, rfl⟩
          refine ⟨origRow, horigIn, ?_⟩
          dsimp only
          by_cases hlt : suppressGroupSize distinctBy origRow < minK
          · exact Or.inr (by simp [hlt])
          · simp only [hlt, false_or]
            have hif : ∀ (b : Bool),
                ((if b = true then ({ cells := maskAggCells inTV.cols origRow.cells, groupMeta := none } : TableRow)
                  else ({ cells := wrapAggCells inTV.cols origRow.cells, groupMeta := none } : TableRow)).cells =
                  wrapAggCells inTV.cols origRow.cells ∧ suppressGroupSize distinctBy origRow ≥ minK) ∨
                (if b = true then ({ cells := maskAggCells inTV.cols origRow.cells, groupMeta := none } : TableRow)
                  else ({ cells := wrapAggCells inTV.cols origRow.cells, groupMeta := none } : TableRow)).cells =
                  maskAggCells inTV.cols origRow.cells := by
              intro b; cases b
              · exact Or.inl ⟨rfl, Nat.not_lt.mp hlt⟩
              · exact Or.inr rfl
            exact hif _

end DanaCore
