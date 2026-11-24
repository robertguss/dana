/-
  DanaCore/NonInterference.lean
  Theorem 2 — Termination- and Error-Insensitive Non-Interference (TEINI) and
  Automatic Redaction of Explicit `.stop` Diagnostics for Dana Core IR v0.1.

  Formalizes observer-clearance equivalence `≈_L` across scalars, algebraic data,
  closures, capability handles, relational `Table`s (accounting for `col_tags`,
  `row_tags`, and `order_tags` permutations), environments, and host `World`s,
  and proves with zero custom axioms:
  - Theorems 2A–2D (TEINI on `ok` runs): well-typed programs whose non-spec
    functions are free of audited declassifiers crossing `L`, whose sinks all
    satisfy `allows ⊆ L`, and whose stored DB tables satisfy `progRespectsDB`
    map `L`-equivalent inputs to identical observable `ExecReport`s whenever
    both runs complete normally (`status = .ok`).
  - Theorem 2E (Explicit `.stop` Redaction): explicit `.stop` nodes with
    sensitive payloads redact to identical `[REDACTED:tag]` diagnostics and
    observable `ExecReport`s. (Runtime trap divergence such as divide-by-zero
    or `Int64`/`Decimal` overflow lies outside the static proof.)
-/
import DanaCore.Syntax
import DanaCore.Check
import DanaCore.Eval
import DanaCore.Soundness

namespace DanaCore

/-! ## Strict Total Order Laws on `byteListLt`, `valCmp`, `valLt`, and `valEq` -/

private theorem uint8_eq_of_toNat_eq {b1 b2 : UInt8} (h : b1.toNat = b2.toNat) : b1 = b2 :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem byteListLt_irrefl : ∀ (bs : List UInt8), byteListLt bs bs = false
  | [] => rfl
  | b :: rest => by
    simp only [byteListLt, Nat.lt_irrefl, ↓reduceIte]
    exact byteListLt_irrefl rest

theorem byteListLt_trans :
    ∀ {l1 l2 l3 : List UInt8},
      byteListLt l1 l2 = true → byteListLt l2 l3 = true → byteListLt l1 l3 = true
  | [], [], _ :: _, h12, _ => by simp [byteListLt] at h12
  | [], _ :: _, [], _, h23 => by simp [byteListLt] at h23
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h12, _ => by simp [byteListLt] at h12
  | _ :: _, _ :: _, [], _, h23 => by simp [byteListLt] at h23
  | b1 :: r1, b2 :: r2, b3 :: r3, h12, h23 => by
    simp only [byteListLt] at h12 h23 ⊢
    by_cases h1 : b1.toNat < b2.toNat
    · simp only [h1, ↓reduceIte] at h12
      by_cases h2 : b2.toNat < b3.toNat
      · have h13 : b1.toNat < b3.toNat := Nat.lt_trans h1 h2
        simp [h13]
      · by_cases h2' : b3.toNat < b2.toNat
        · simp [h2, h2'] at h23
        · have h13 : b1.toNat < b3.toNat := by omega
          simp [h13]
    · by_cases h1' : b2.toNat < b1.toNat
      · simp [h1, h1'] at h12
      · simp only [h1, h1', ↓reduceIte] at h12
        by_cases h2 : b2.toNat < b3.toNat
        · have h13 : b1.toNat < b3.toNat := by omega
          simp [h13]
        · by_cases h2' : b3.toNat < b2.toNat
          · simp [h2, h2'] at h23
          · have hn13 : ¬ (b1.toNat < b3.toNat) := by omega
            have hn31 : ¬ (b3.toNat < b1.toNat) := by omega
            simp only [h2, h2', ↓reduceIte] at h23
            simp only [hn13, hn31, ↓reduceIte]
            exact byteListLt_trans h12 h23

theorem byteListLt_trichotomy :
    ∀ (l1 l2 : List UInt8),
      byteListLt l1 l2 = true ∨ l1 = l2 ∨ byteListLt l2 l1 = true
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl rfl
  | _ :: _, [] => Or.inr (Or.inr rfl)
  | b1 :: r1, b2 :: r2 => by
    simp only [byteListLt]
    by_cases h1 : b1.toNat < b2.toNat
    · exact Or.inl (by simp [h1])
    · by_cases h2 : b2.toNat < b1.toNat
      · exact Or.inr (Or.inr (by simp [h2]))
      · have heq : b1 = b2 := uint8_eq_of_toNat_eq (by omega)
        subst heq
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rcases byteListLt_trichotomy r1 r2 with hlt | rfl | hgt
        · exact Or.inl hlt
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hgt)

theorem cmpInt_eq_iff (a b : Int) : cmpInt a b = .eq ↔ a = b := by
  unfold cmpInt
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega

theorem cmpInt_lt_iff (a b : Int) : cmpInt a b = .lt ↔ a < b := by
  unfold cmpInt
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2]

theorem cmpInt_gt_iff (a b : Int) : cmpInt a b = .gt ↔ b < a := by
  unfold cmpInt
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega

theorem cmpNat_eq_iff (a b : Nat) : cmpNat a b = .eq ↔ a = b := by
  unfold cmpNat
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega

theorem cmpNat_lt_iff (a b : Nat) : cmpNat a b = .lt ↔ a < b := by
  unfold cmpNat
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2]

theorem cmpNat_gt_iff (a b : Nat) : cmpNat a b = .gt ↔ b < a := by
  unfold cmpNat
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega

theorem cmpTag_eq_iff (a b : String) : cmpTag a b = .eq ↔ a = b := by
  unfold cmpTag
  rcases charListLt_trichotomy a.toList b.toList with hlt | heq | hgt
  · have hne : a ≠ b := fun h => by rw [h, charListLt_irrefl] at hlt; contradiction
    simp [hlt, hne]
  · have hab : a = b := String.ext heq
    subst hab
    simp [charListLt_irrefl]
  · have hnot : charListLt a.toList b.toList = false := by
      cases h : charListLt a.toList b.toList
      · rfl
      · have := charListLt_trans h hgt; rw [charListLt_irrefl] at this; contradiction
    have hne : a ≠ b := fun h => by rw [h, charListLt_irrefl] at hgt; contradiction
    simp [hnot, hgt, hne]

theorem cmpTag_lt_iff (a b : String) : cmpTag a b = .lt ↔ charListLt a.toList b.toList = true := by
  unfold cmpTag
  cases h : charListLt a.toList b.toList
  · cases charListLt b.toList a.toList <;> simp
  · simp

theorem cmpTag_gt_iff (a b : String) : cmpTag a b = .gt ↔ charListLt b.toList a.toList = true := by
  unfold cmpTag
  cases h1 : charListLt a.toList b.toList
  · cases h2 : charListLt b.toList a.toList <;> simp
  · have h2 : charListLt b.toList a.toList = false := by
      cases hb : charListLt b.toList a.toList
      · rfl
      · have := charListLt_trans h1 hb; rw [charListLt_irrefl] at this; contradiction
    simp [h2]

theorem cmpBytes_eq_iff (a b : List UInt8) : cmpBytes a b = .eq ↔ a = b := by
  unfold cmpBytes
  rcases byteListLt_trichotomy a b with hlt | rfl | hgt
  · have hne : a ≠ b := fun h => by rw [h, byteListLt_irrefl] at hlt; contradiction
    simp [hlt, hne]
  · simp [byteListLt_irrefl]
  · have hnot : byteListLt a b = false := by
      cases h : byteListLt a b
      · rfl
      · have := byteListLt_trans h hgt; rw [byteListLt_irrefl] at this; contradiction
    have hne : a ≠ b := fun h => by rw [h, byteListLt_irrefl] at hgt; contradiction
    simp [hnot, hgt, hne]

theorem cmpBytes_lt_iff (a b : List UInt8) : cmpBytes a b = .lt ↔ byteListLt a b = true := by
  unfold cmpBytes
  cases h : byteListLt a b
  · cases byteListLt b a <;> simp
  · simp

theorem cmpBytes_gt_iff (a b : List UInt8) : cmpBytes a b = .gt ↔ byteListLt b a = true := by
  unfold cmpBytes
  cases h1 : byteListLt a b
  · cases h2 : byteListLt b a <;> simp
  · have h2 : byteListLt b a = false := by
      cases hb : byteListLt b a
      · rfl
      · have := byteListLt_trans h1 hb; rw [byteListLt_irrefl] at this; contradiction
    simp [h2]

/-! ## Pure Scalar / Algebraic Values Supporting Canonical Total Ordering -/

mutual
inductive SortableVal : Val → Prop where
  | optNone : SortableVal .optNone
  | unit : SortableVal .unit
  | bool (b : Bool) : SortableVal (.bool b)
  | int (n : Int) : SortableVal (.int n)
  | decimal (d : Int) : SortableVal (.decimal d)
  | float (f : Float64) : SortableVal (.float f)
  | text (s : String) : SortableVal (.text s)
  | bytes (bs : List UInt8) : SortableVal (.bytes bs)
  | date (d : Int) : SortableVal (.date d)
  | timestamp (ts : Int) : SortableVal (.timestamp ts)
  | duration (dur : Int) : SortableVal (.duration dur)
  | optSome {v : Val} (hv : SortableVal v) : SortableVal (.optSome v)
  | resOk {v : Val} (hv : SortableVal v) : SortableVal (.resOk v)
  | resErr {e : Val} (he : SortableVal e) : SortableVal (.resErr e)
  | tuple {vs : List Val} (hvs : SortableValList vs) : SortableVal (.tuple vs)
  | list {vs : List Val} (hvs : SortableValList vs) : SortableVal (.list vs)
  | ctor (tn cn : Ident) {fs : List Val} (hfs : SortableValList fs) :
      SortableVal (.ctor tn cn fs)
  | linearModel (s i r2 : Float64) : SortableVal (.linearModel s i r2)
  | statTest (s p : Float64) : SortableVal (.statTest s p)

inductive SortableValList : List Val → Prop where
  | nil : SortableValList []
  | cons {v : Val} {vs : List Val} (hv : SortableVal v) (hvs : SortableValList vs) :
      SortableValList (v :: vs)
end

theorem SortableValList.of_forall :
    ∀ {vs : List Val}, (∀ v ∈ vs, SortableVal v) → SortableValList vs
  | [], _ => .nil
  | v :: _, h => .cons (h v (.head _)) (SortableValList.of_forall fun u hu => h u (.tail _ hu))

theorem SortableValList.to_forall :
    ∀ {vs : List Val}, SortableValList vs → ∀ v ∈ vs, SortableVal v
  | [], .nil, _, hm => nomatch hm
  | _ :: _, .cons hv hvs, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hr
    · exact hv
    · exact hvs.to_forall _ hr

private theorem cmpNat_symm (a b : Nat) :
    cmpNat b a = (match cmpNat a b with | .lt => .gt | .eq => .eq | .gt => .lt) := by
  unfold cmpNat
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega

private theorem cmpTag_symm (a b : String) :
    cmpTag b a = (match cmpTag a b with | .lt => .gt | .eq => .eq | .gt => .lt) := by
  rcases charListLt_trichotomy a.toList b.toList with hlt | heq | hgt
  · have hnot : charListLt b.toList a.toList = false := by
      cases hb : charListLt b.toList a.toList
      · rfl
      · have := charListLt_trans hlt hb; rw [charListLt_irrefl] at this; contradiction
    simp [cmpTag, hlt, hnot]
  · simp [cmpTag, heq, charListLt_irrefl]
  · have hnot : charListLt a.toList b.toList = false := by
      cases ha : charListLt a.toList b.toList
      · rfl
      · have := charListLt_trans ha hgt; rw [charListLt_irrefl] at this; contradiction
    simp [cmpTag, hgt, hnot]

private theorem valCmp_of_rank_ne {v1 v2 : Val} (h : valRank v1 ≠ valRank v2) :
    valCmp v1 v2 = cmpNat (valRank v1) (valRank v2) := by
  cases v1 <;> cases v2 <;> simp only [valRank] at h <;> (try contradiction) <;>
    (try cases ‹Bool›) <;> simp [valCmp, valRank, cmpNat]

private theorem valEq_false_of_rank_ne {v1 v2 : Val} (h : valRank v1 ≠ valRank v2) :
    valEq v1 v2 = false := by
  cases v1 <;> cases v2 <;> simp only [valRank] at h <;> (try contradiction) <;>
    (try cases ‹TableVal›) <;> simp [valEq]

mutual
theorem valCmp_eq_iff :
    ∀ {v1 v2 : Val}, SortableVal v1 → SortableVal v2 → (valCmp v1 v2 = .eq ↔ v1 = v2)
  | v1, v2, h1, h2 => by
    by_cases hr : valRank v1 = valRank v2
    · cases h1 <;> cases h2 <;> simp only [valRank] at hr <;> try contradiction
      case optNone.optNone => simp [valCmp]
      case unit.unit => simp [valCmp]
      case bool.bool b1 b2 => cases b1 <;> cases b2 <;> simp [valCmp]
      case int.int a b => simp [valCmp, cmpInt_eq_iff]
      case decimal.decimal a b => simp [valCmp, cmpInt_eq_iff]
      case float.float a b =>
        simp only [valCmp, cmpNat_eq_iff, Val.float.injEq]
        exact ⟨floatOrderKey_inj, fun h => h ▸ rfl⟩
      case text.text a b => simp [valCmp, cmpTag_eq_iff]
      case bytes.bytes a b => simp [valCmp, cmpBytes_eq_iff]
      case date.date a b => simp [valCmp, cmpInt_eq_iff]
      case timestamp.timestamp a b => simp [valCmp, cmpInt_eq_iff]
      case duration.duration a b => simp [valCmp, cmpInt_eq_iff]
      case optSome.optSome _ hv1 _ hv2 => simp [valCmp, valCmp_eq_iff hv1 hv2]
      case resOk.resOk _ hv1 _ hv2 => simp [valCmp, valCmp_eq_iff hv1 hv2]
      case resErr.resErr _ he1 _ he2 => simp [valCmp, valCmp_eq_iff he1 he2]
      case tuple.tuple _ hvs1 _ hvs2 => simp [valCmp, valListCmp_eq_iff hvs1 hvs2]
      case list.list _ hvs1 _ hvs2 => simp [valCmp, valListCmp_eq_iff hvs1 hvs2]
      case ctor.ctor tn1 cn1 _ hfs1 tn2 cn2 _ hfs2 =>
        simp only [valCmp]
        cases ht : cmpTag tn1 tn2
        · have hne : tn1 ≠ tn2 := fun h => by rw [h, (cmpTag_eq_iff _ _).mpr rfl] at ht; nomatch ht
          simp [hne]
        · rw [cmpTag_eq_iff] at ht; subst ht
          cases hc : cmpTag cn1 cn2
          · have hne : cn1 ≠ cn2 := fun h => by rw [h, (cmpTag_eq_iff _ _).mpr rfl] at hc; nomatch hc
            simp [hne]
          · rw [cmpTag_eq_iff] at hc; subst hc
            simp [valListCmp_eq_iff hfs1 hfs2]
          · have hne : cn1 ≠ cn2 := fun h => by rw [h, (cmpTag_eq_iff _ _).mpr rfl] at hc; nomatch hc
            simp [hne]
        · have hne : tn1 ≠ tn2 := fun h => by rw [h, (cmpTag_eq_iff _ _).mpr rfl] at ht; nomatch ht
          simp [hne]
      case linearModel.linearModel s1 i1 r1 s2 i2 r2 =>
        simp only [valCmp]
        cases hs : cmpNat (floatOrderKey s1) (floatOrderKey s2)
        · have hne : s1 ≠ s2 := fun h => by rw [h, (cmpNat_eq_iff _ _).mpr rfl] at hs; nomatch hs
          simp [hne]
        · have hsEq := floatOrderKey_inj ((cmpNat_eq_iff _ _).mp hs); subst hsEq
          cases hi : cmpNat (floatOrderKey i1) (floatOrderKey i2)
          · have hne : i1 ≠ i2 := fun h => by rw [h, (cmpNat_eq_iff _ _).mpr rfl] at hi; nomatch hi
            simp [hne]
          · have hiEq := floatOrderKey_inj ((cmpNat_eq_iff _ _).mp hi); subst hiEq
            simp only [cmpNat_eq_iff, Val.linearModel.injEq, true_and]
            exact ⟨floatOrderKey_inj, fun h => h ▸ rfl⟩
          · have hne : i1 ≠ i2 := fun h => by rw [h, (cmpNat_eq_iff _ _).mpr rfl] at hi; nomatch hi
            simp [hne]
        · have hne : s1 ≠ s2 := fun h => by rw [h, (cmpNat_eq_iff _ _).mpr rfl] at hs; nomatch hs
          simp [hne]
      case statTest.statTest s1 p1 s2 p2 =>
        simp only [valCmp]
        cases hs : cmpNat (floatOrderKey s1) (floatOrderKey s2)
        · have hne : s1 ≠ s2 := fun h => by rw [h, (cmpNat_eq_iff _ _).mpr rfl] at hs; nomatch hs
          simp [hne]
        · have hsEq := floatOrderKey_inj ((cmpNat_eq_iff _ _).mp hs); subst hsEq
          simp only [cmpNat_eq_iff, Val.statTest.injEq, true_and]
          exact ⟨floatOrderKey_inj, fun h => h ▸ rfl⟩
        · have hne : s1 ≠ s2 := fun h => by rw [h, (cmpNat_eq_iff _ _).mpr rfl] at hs; nomatch hs
          simp [hne]
    · rw [valCmp_of_rank_ne hr, cmpNat_eq_iff]
      exact ⟨fun h => absurd h hr, fun h => absurd (congrArg valRank h) hr⟩

theorem valListCmp_eq_iff :
    ∀ {xs ys : List Val}, SortableValList xs → SortableValList ys → (valListCmp xs ys = .eq ↔ xs = ys)
  | [], [], .nil, .nil => by simp [valListCmp]
  | [], _ :: _, .nil, .cons _ _ => by simp [valListCmp]
  | _ :: _, [], .cons _ _, .nil => by simp [valListCmp]
  | a :: as1, b :: bs1, .cons ha has, .cons hb hbs => by
    simp only [valListCmp]
    cases hc : valCmp a b
    · have hne : a ≠ b := fun h => by rw [h, (valCmp_eq_iff hb hb).mpr rfl] at hc; nomatch hc
      simp [hne]
    · rw [valCmp_eq_iff ha hb] at hc; subst hc
      simp [valListCmp_eq_iff has hbs]
    · have hne : a ≠ b := fun h => by rw [h, (valCmp_eq_iff hb hb).mpr rfl] at hc; nomatch hc
      simp [hne]
end

mutual
theorem valCmp_gt_iff :
    ∀ {v1 v2 : Val}, SortableVal v1 → SortableVal v2 → (valCmp v1 v2 = .gt ↔ valCmp v2 v1 = .lt)
  | v1, v2, h1, h2 => by
    by_cases hr : valRank v1 = valRank v2
    · cases h1 <;> cases h2 <;> simp only [valRank] at hr <;> try contradiction
      case optNone.optNone => decide
      case unit.unit => decide
      case bool.bool b1 b2 => cases b1 <;> cases b2 <;> decide
      case int.int a b => simp [valCmp, cmpInt_gt_iff, cmpInt_lt_iff]
      case decimal.decimal a b => simp [valCmp, cmpInt_gt_iff, cmpInt_lt_iff]
      case float.float a b => simp [valCmp, cmpNat_gt_iff, cmpNat_lt_iff]
      case text.text a b => simp [valCmp, cmpTag_gt_iff, cmpTag_lt_iff]
      case bytes.bytes a b => simp [valCmp, cmpBytes_gt_iff, cmpBytes_lt_iff]
      case date.date a b => simp [valCmp, cmpInt_gt_iff, cmpInt_lt_iff]
      case timestamp.timestamp a b => simp [valCmp, cmpInt_gt_iff, cmpInt_lt_iff]
      case duration.duration a b => simp [valCmp, cmpInt_gt_iff, cmpInt_lt_iff]
      case optSome.optSome _ hv1 _ hv2 => simp only [valCmp]; exact valCmp_gt_iff hv1 hv2
      case resOk.resOk _ hv1 _ hv2 => simp only [valCmp]; exact valCmp_gt_iff hv1 hv2
      case resErr.resErr _ he1 _ he2 => simp only [valCmp]; exact valCmp_gt_iff he1 he2
      case tuple.tuple _ hvs1 _ hvs2 => simp only [valCmp]; exact valListCmp_gt_iff hvs1 hvs2
      case list.list _ hvs1 _ hvs2 => simp only [valCmp]; exact valListCmp_gt_iff hvs1 hvs2
      case ctor.ctor tn1 cn1 _ hfs1 tn2 cn2 _ hfs2 =>
        simp only [valCmp]
        rw [cmpTag_symm tn1 tn2, cmpTag_symm cn1 cn2]
        cases cmpTag tn1 tn2 <;> cases cmpTag cn1 cn2 <;> simp [valListCmp_gt_iff hfs1 hfs2]
      case linearModel.linearModel s1 i1 r1 s2 i2 r2 =>
        simp only [valCmp]
        rw [cmpNat_symm (floatOrderKey s1) (floatOrderKey s2),
            cmpNat_symm (floatOrderKey i1) (floatOrderKey i2),
            cmpNat_symm (floatOrderKey r1) (floatOrderKey r2)]
        cases cmpNat (floatOrderKey s1) (floatOrderKey s2) <;>
          cases cmpNat (floatOrderKey i1) (floatOrderKey i2) <;>
          cases cmpNat (floatOrderKey r1) (floatOrderKey r2) <;> decide
      case statTest.statTest s1 p1 s2 p2 =>
        simp only [valCmp]
        rw [cmpNat_symm (floatOrderKey s1) (floatOrderKey s2),
            cmpNat_symm (floatOrderKey p1) (floatOrderKey p2)]
        cases cmpNat (floatOrderKey s1) (floatOrderKey s2) <;>
          cases cmpNat (floatOrderKey p1) (floatOrderKey p2) <;> decide
    · rw [valCmp_of_rank_ne hr, valCmp_of_rank_ne (Ne.symm hr), cmpNat_gt_iff, cmpNat_lt_iff]
  termination_by v1 v2 => sizeOf v1 + sizeOf v2

theorem valListCmp_gt_iff :
    ∀ {xs ys : List Val}, SortableValList xs → SortableValList ys → (valListCmp xs ys = .gt ↔ valListCmp ys xs = .lt)
  | [], [], .nil, .nil => by simp [valListCmp]
  | [], _ :: _, .nil, .cons _ _ => by simp [valListCmp]
  | _ :: _, [], .cons _ _, .nil => by simp [valListCmp]
  | a :: as1, b :: bs1, .cons ha has, .cons hb hbs => by
    simp only [valListCmp]
    cases h12 : valCmp a b <;> cases h21 : valCmp b a
    · have := (valCmp_gt_iff hb ha).mpr h12; rw [this] at h21; nomatch h21
    · rw [valCmp_eq_iff hb ha] at h21; subst h21; rw [(valCmp_eq_iff ha ha).mpr rfl] at h12; nomatch h12
    · simp
    · rw [valCmp_eq_iff ha hb] at h12; subst h12; rw [(valCmp_eq_iff ha ha).mpr rfl] at h21; nomatch h21
    · exact valListCmp_gt_iff has hbs
    · rw [valCmp_eq_iff ha hb] at h12; subst h12; rw [(valCmp_eq_iff ha ha).mpr rfl] at h21; nomatch h21
    · simp
    · rw [valCmp_eq_iff hb ha] at h21; subst h21; rw [(valCmp_eq_iff ha ha).mpr rfl] at h12; nomatch h12
    · rw [valCmp_gt_iff ha hb] at h12; rw [h12] at h21; nomatch h21
  termination_by xs ys => sizeOf xs + sizeOf ys
end

private theorem same_ctor_or_rank_lt {v1 v2 : Val}
    (_ : SortableVal v1) (_ : SortableVal v2) :
    (valRank v1 ≠ valRank v2 → (valCmp v1 v2 = .lt ↔ valRank v1 < valRank v2)) := by
  intro hne
  rw [valCmp_of_rank_ne hne, cmpNat_lt_iff]

mutual
theorem valCmp_lt_trans :
    ∀ {v1 v2 v3 : Val},
      SortableVal v1 → SortableVal v2 → SortableVal v3 →
      valCmp v1 v2 = .lt → valCmp v2 v3 = .lt → valCmp v1 v3 = .lt
  | v1, v2, v3, h1, h2, h3, h12, h23 => by
    have hr12 : valRank v1 ≤ valRank v2 := by
      by_cases heq : valRank v1 = valRank v2
      · omega
      · have := (same_ctor_or_rank_lt h1 h2 heq).mp h12; omega
    have hr23 : valRank v2 ≤ valRank v3 := by
      by_cases heq : valRank v2 = valRank v3
      · omega
      · have := (same_ctor_or_rank_lt h2 h3 heq).mp h23; omega
    by_cases hlt13 : valRank v1 < valRank v3
    · exact (same_ctor_or_rank_lt h1 h3 (by omega)).mpr hlt13
    · have hrEq12 : valRank v1 = valRank v2 := by omega
      have hrEq23 : valRank v2 = valRank v3 := by omega
      exact (by
        cases h1 <;> cases h2 <;> simp only [valRank] at hrEq12 <;> try omega
        all_goals (cases h3 <;> simp only [valRank] at hrEq23 <;> try omega)
        all_goals try (simp [valCmp] at h12)
        case bool.bool.bool b1 b2 b3 =>
          cases b1 <;> cases b2 <;> cases b3 <;> simp [valCmp] at h12 h23 ⊢
        case int.int.int a b c =>
          simp only [valCmp, cmpInt_lt_iff] at h12 h23 ⊢; omega
        case decimal.decimal.decimal a b c =>
          simp only [valCmp, cmpInt_lt_iff] at h12 h23 ⊢; omega
        case float.float.float a b c =>
          simp only [valCmp, cmpNat_lt_iff] at h12 h23 ⊢; omega
        case text.text.text a b c =>
          simp only [valCmp, cmpTag_lt_iff] at h12 h23 ⊢
          exact charListLt_trans h12 h23
        case bytes.bytes.bytes a b c =>
          simp only [valCmp, cmpBytes_lt_iff] at h12 h23 ⊢
          exact byteListLt_trans h12 h23
        case date.date.date a b c =>
          simp only [valCmp, cmpInt_lt_iff] at h12 h23 ⊢; omega
        case timestamp.timestamp.timestamp a b c =>
          simp only [valCmp, cmpInt_lt_iff] at h12 h23 ⊢; omega
        case duration.duration.duration a b c =>
          simp only [valCmp, cmpInt_lt_iff] at h12 h23 ⊢; omega
        case optSome.optSome.optSome _ hv1 _ hv2 _ hv3 =>
          simp only [valCmp] at h12 h23 ⊢
          exact valCmp_lt_trans hv1 hv2 hv3 h12 h23
        case resOk.resOk.resOk _ hv1 _ hv2 _ hv3 =>
          simp only [valCmp] at h12 h23 ⊢
          exact valCmp_lt_trans hv1 hv2 hv3 h12 h23
        case resErr.resErr.resErr _ he1 _ he2 _ he3 =>
          simp only [valCmp] at h12 h23 ⊢
          exact valCmp_lt_trans he1 he2 he3 h12 h23
        case tuple.tuple.tuple _ hvs1 _ hvs2 _ hvs3 =>
          simp only [valCmp] at h12 h23 ⊢
          exact valListCmp_lt_trans hvs1 hvs2 hvs3 h12 h23
        case list.list.list _ hvs1 _ hvs2 _ hvs3 =>
          simp only [valCmp] at h12 h23 ⊢
          exact valListCmp_lt_trans hvs1 hvs2 hvs3 h12 h23
        case ctor.ctor.ctor tn1 cn1 _ hfs1 tn2 cn2 _ hfs2 tn3 cn3 _ hfs3 =>
          simp only [valCmp] at h12 h23 ⊢
          cases ht12 : cmpTag tn1 tn2 <;> simp only [ht12] at h12 <;> try contradiction
          · cases ht23 : cmpTag tn2 tn3 <;> simp only [ht23] at h23 <;> try contradiction
            · have ht13 : cmpTag tn1 tn3 = .lt := (cmpTag_lt_iff _ _).mpr
                (charListLt_trans ((cmpTag_lt_iff _ _).mp ht12) ((cmpTag_lt_iff _ _).mp ht23))
              simp [ht13]
            · rw [cmpTag_eq_iff] at ht23; subst ht23; simp [ht12]
          · rw [cmpTag_eq_iff] at ht12; subst ht12
            cases ht23 : cmpTag tn1 tn3 <;> simp only [ht23] at h23 ⊢ <;> try contradiction
            cases hc12 : cmpTag cn1 cn2 <;> simp only [hc12] at h12 <;> try contradiction
            · cases hc23 : cmpTag cn2 cn3 <;> simp only [hc23] at h23 <;> try contradiction
              · have hc13 : cmpTag cn1 cn3 = .lt := (cmpTag_lt_iff _ _).mpr
                  (charListLt_trans ((cmpTag_lt_iff _ _).mp hc12) ((cmpTag_lt_iff _ _).mp hc23))
                simp [hc13]
              · rw [cmpTag_eq_iff] at hc23; subst hc23; simp [hc12]
            · rw [cmpTag_eq_iff] at hc12; subst hc12
              cases hc23 : cmpTag cn1 cn3 <;> simp only [hc23] at h23 ⊢ <;> try contradiction
              exact valListCmp_lt_trans hfs1 hfs2 hfs3 h12 h23
        case linearModel.linearModel.linearModel s1 i1 r1 s2 i2 r2 s3 i3 r3 =>
          simp only [valCmp] at h12 h23 ⊢
          cases hs12 : cmpNat (floatOrderKey s1) (floatOrderKey s2) <;> simp [hs12] at h12
          · cases hs23 : cmpNat (floatOrderKey s2) (floatOrderKey s3) <;> simp [hs23] at h23
            · rw [cmpNat_lt_iff] at hs12 hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
              simp [hs13]
            · rw [cmpNat_lt_iff] at hs12; rw [cmpNat_eq_iff] at hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
              simp [hs13]
          · rw [cmpNat_eq_iff] at hs12
            cases hs23 : cmpNat (floatOrderKey s2) (floatOrderKey s3) <;> simp [hs23] at h23
            · rw [cmpNat_lt_iff] at hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
              simp [hs13]
            · rw [cmpNat_eq_iff] at hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .eq := (cmpNat_eq_iff _ _).mpr (by omega)
              simp only [hs13]
              cases hi12 : cmpNat (floatOrderKey i1) (floatOrderKey i2) <;> simp [hi12] at h12
              · cases hi23 : cmpNat (floatOrderKey i2) (floatOrderKey i3) <;> simp [hi23] at h23
                · rw [cmpNat_lt_iff] at hi12 hi23
                  have hi13 : cmpNat (floatOrderKey i1) (floatOrderKey i3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
                  simp [hi13]
                · rw [cmpNat_lt_iff] at hi12; rw [cmpNat_eq_iff] at hi23
                  have hi13 : cmpNat (floatOrderKey i1) (floatOrderKey i3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
                  simp [hi13]
              · rw [cmpNat_eq_iff] at hi12
                cases hi23 : cmpNat (floatOrderKey i2) (floatOrderKey i3) <;> simp [hi23] at h23
                · rw [cmpNat_lt_iff] at hi23
                  have hi13 : cmpNat (floatOrderKey i1) (floatOrderKey i3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
                  simp [hi13]
                · rw [cmpNat_eq_iff] at hi23
                  have hi13 : cmpNat (floatOrderKey i1) (floatOrderKey i3) = .eq := (cmpNat_eq_iff _ _).mpr (by omega)
                  simp only [hi13, cmpNat_lt_iff] at h12 h23 ⊢; omega
        case statTest.statTest.statTest s1 p1 s2 p2 s3 p3 =>
          simp only [valCmp] at h12 h23 ⊢
          cases hs12 : cmpNat (floatOrderKey s1) (floatOrderKey s2) <;> simp [hs12] at h12
          · cases hs23 : cmpNat (floatOrderKey s2) (floatOrderKey s3) <;> simp [hs23] at h23
            · rw [cmpNat_lt_iff] at hs12 hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
              simp [hs13]
            · rw [cmpNat_lt_iff] at hs12; rw [cmpNat_eq_iff] at hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
              simp [hs13]
          · rw [cmpNat_eq_iff] at hs12
            cases hs23 : cmpNat (floatOrderKey s2) (floatOrderKey s3) <;> simp [hs23] at h23
            · rw [cmpNat_lt_iff] at hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .lt := (cmpNat_lt_iff _ _).mpr (by omega)
              simp [hs13]
            · rw [cmpNat_eq_iff] at hs23
              have hs13 : cmpNat (floatOrderKey s1) (floatOrderKey s3) = .eq := (cmpNat_eq_iff _ _).mpr (by omega)
              simp only [hs13, cmpNat_lt_iff] at h12 h23 ⊢; omega)

theorem valListCmp_lt_trans :
    ∀ {xs ys zs : List Val},
      SortableValList xs → SortableValList ys → SortableValList zs →
      valListCmp xs ys = .lt → valListCmp ys zs = .lt → valListCmp xs zs = .lt
  | [], _ :: _, _ :: _, .nil, .cons _ _, .cons _ _, _, _ => rfl
  | [], _ :: _, [], .nil, .cons _ _, .nil, _, h23 => by simp [valListCmp] at h23
  | [], [], _, .nil, .nil, _, h12, _ => by simp [valListCmp] at h12
  | _ :: _, [], _, .cons _ _, .nil, _, h12, _ => by simp [valListCmp] at h12
  | _ :: _, _ :: _, [], .cons _ _, .cons _ _, .nil, _, h23 => by simp [valListCmp] at h23
  | a :: as1, b :: bs1, c :: cs1, .cons ha has, .cons hb hbs, .cons hc hcs, h12, h23 => by
    simp only [valListCmp] at h12 h23 ⊢
    cases hab : valCmp a b <;> simp only [hab] at h12 <;> try contradiction
    · cases hbc : valCmp b c <;> simp only [hbc] at h23 <;> try contradiction
      · simp [valCmp_lt_trans ha hb hc hab hbc]
      · rw [valCmp_eq_iff hb hc] at hbc; subst hbc; simp [hab]
    · rw [valCmp_eq_iff ha hb] at hab; subst hab
      cases hbc : valCmp a c <;> simp only [hbc] at h23 ⊢ <;> try contradiction
      exact valListCmp_lt_trans has hbs hcs h12 h23
end

theorem valLt_irrefl {v : Val} (hv : SortableVal v) : valLt v v = false := by
  simp [valLt, (valCmp_eq_iff hv hv).mpr rfl]

theorem valLt_trans {a b c : Val} (ha : SortableVal a) (hb : SortableVal b) (hc : SortableVal c)
    (h1 : valLt a b = true) (h2 : valLt b c = true) : valLt a c = true := by
  simp only [valLt, decide_eq_true_eq] at h1 h2 ⊢
  exact valCmp_lt_trans ha hb hc h1 h2

theorem valLt_trichotomy {a b : Val} (ha : SortableVal a) (hb : SortableVal b) :
    valLt a b = true ∨ a = b ∨ valLt b a = true := by
  unfold valLt
  cases hc : valCmp a b
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl ((valCmp_eq_iff ha hb).mp hc))
  · exact Or.inr (Or.inr (by simp [(valCmp_gt_iff ha hb).mp hc]))

theorem valListLt_irrefl {vs : List Val} (hvs : SortableValList vs) : valListLt vs vs = false := by
  simp [valListLt, (valListCmp_eq_iff hvs hvs).mpr rfl]

theorem valListLt_trans {a b c : List Val}
    (ha : SortableValList a) (hb : SortableValList b) (hc : SortableValList c)
    (h1 : valListLt a b = true) (h2 : valListLt b c = true) : valListLt a c = true := by
  simp only [valListLt, decide_eq_true_eq] at h1 h2 ⊢
  exact valListCmp_lt_trans ha hb hc h1 h2

theorem valListLt_trichotomy {a b : List Val} (ha : SortableValList a) (hb : SortableValList b) :
    valListLt a b = true ∨ a = b ∨ valListLt b a = true := by
  unfold valListLt
  cases hc : valListCmp a b
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl ((valListCmp_eq_iff ha hb).mp hc))
  · exact Or.inr (Or.inr (by simp [(valListCmp_gt_iff ha hb).mp hc]))

mutual
theorem valEq_iff_eq :
    ∀ {v1 v2 : Val}, SortableVal v1 → SortableVal v2 → (valEq v1 v2 = true ↔ v1 = v2)
  | v1, v2, h1, h2 => by
    by_cases hr : valRank v1 = valRank v2
    · cases h1 <;> cases h2 <;> simp only [valRank] at hr <;> try contradiction
      case optNone.optNone | unit.unit | bool.bool | int.int | decimal.decimal
         | float.float | text.text | bytes.bytes | date.date
         | timestamp.timestamp | duration.duration => simp [valEq]
      case optSome.optSome _ hv1 _ hv2 => simp [valEq, valEq_iff_eq hv1 hv2]
      case resOk.resOk _ hv1 _ hv2 => simp [valEq, valEq_iff_eq hv1 hv2]
      case resErr.resErr _ he1 _ he2 => simp [valEq, valEq_iff_eq he1 he2]
      case tuple.tuple _ hvs1 _ hvs2 => simp [valEq, valListEq_iff_eq hvs1 hvs2]
      case list.list _ hvs1 _ hvs2 => simp [valEq, valListEq_iff_eq hvs1 hvs2]
      case ctor.ctor tn1 cn1 _ hfs1 tn2 cn2 _ hfs2 =>
        simp [valEq, valListEq_iff_eq hfs1 hfs2, and_assoc]
      case linearModel.linearModel =>
        simp [valEq, and_assoc]
      case statTest.statTest =>
        simp [valEq]
    · rw [valEq_false_of_rank_ne hr]
      exact ⟨(fun h => nomatch h), fun h => absurd (congrArg valRank h) hr⟩

theorem valListEq_iff_eq :
    ∀ {xs ys : List Val}, SortableValList xs → SortableValList ys → (valListEq xs ys = true ↔ xs = ys)
  | [], [], .nil, .nil => by simp [valListEq]
  | [], _ :: _, .nil, .cons _ _ => by simp [valListEq]
  | _ :: _, [], .cons _ _, .nil => by simp [valListEq]
  | a :: as1, b :: bs1, .cons ha has, .cons hb hbs => by
    simp [valListEq, Bool.and_eq_true, valEq_iff_eq ha hb, valListEq_iff_eq has hbs]
end

/-! ## Generic Canonical Sorting (`insertionSortBy`) & Deduplication (`dedupAdjacentBy`) Lemmas -/

theorem insertSortedBy_perm {α : Type} (lt : α → α → Bool) (x : α) :
    ∀ (ys : List α), List.Perm (insertSortedBy lt x ys) (x :: ys)
  | [] => List.Perm.refl _
  | y :: ys => by
    simp only [insertSortedBy]
    split
    · exact ((insertSortedBy_perm lt x ys).cons y).trans (List.Perm.swap x y ys)
    · exact List.Perm.refl _

theorem insertionSortBy_perm {α : Type} (lt : α → α → Bool) :
    ∀ (xs : List α), List.Perm (insertionSortBy lt xs) xs
  | [] => List.Perm.nil
  | x :: xs =>
    (insertSortedBy_perm lt x (insertionSortBy lt xs)).trans ((insertionSortBy_perm lt xs).cons x)

theorem pairwise_insertSortedBy {α : Type} {P : α → Prop} {lt : α → α → Bool}
    (hirrefl : ∀ {a}, P a → lt a a = false)
    (htrans : ∀ {a b c}, P a → P b → P c → lt a b = true → lt b c = true → lt a c = true)
    (htrich : ∀ {a b}, P a → P b → lt a b = true ∨ a = b ∨ lt b a = true)
    {x : α} (hx : P x) :
    ∀ {ys : List α},
      (∀ y ∈ ys, P y) →
      ys.Pairwise (fun a b => ¬ lt b a = true) →
      (insertSortedBy lt x ys).Pairwise (fun a b => ¬ lt b a = true)
  | [], _, _ => List.Pairwise.cons (fun _ h => nomatch h) .nil
  | y :: ys, hysP, .cons hy hys => by
    have hyP := hysP y (.head _)
    have htlP : ∀ z ∈ ys, P z := fun z hz => hysP z (.tail _ hz)
    simp only [insertSortedBy]
    by_cases hlt : lt y x = true
    · simp only [hlt, ↓reduceIte]
      apply List.Pairwise.cons
      · intro z hz
        rcases mem_insertSortedBy lt x z ys hz with rfl | hmem
        · intro hxy
          have hyy := htrans hyP hx hyP hlt hxy
          rw [hirrefl hyP] at hyy
          contradiction
        · exact hy z hmem
      · exact pairwise_insertSortedBy hirrefl htrans htrich hx htlP hys
    · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
      apply List.Pairwise.cons
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hmem
        · exact hlt
        · intro hzx
          have hzP := htlP z hmem
          have hyzNot := hy z hmem
          rcases htrich hx hyP with hxy | rfl | hyx
          · exact hyzNot (htrans hzP hx hyP hzx hxy)
          · exact hyzNot hzx
          · exact hlt hyx
      · exact .cons hy hys

theorem pairwise_insertionSortBy {α : Type} {P : α → Prop} {lt : α → α → Bool}
    (hirrefl : ∀ {a}, P a → lt a a = false)
    (htrans : ∀ {a b c}, P a → P b → P c → lt a b = true → lt b c = true → lt a c = true)
    (htrich : ∀ {a b}, P a → P b → lt a b = true ∨ a = b ∨ lt b a = true) :
    ∀ {xs : List α},
      (∀ x ∈ xs, P x) →
      (insertionSortBy lt xs).Pairwise (fun a b => ¬ lt b a = true)
  | [], _ => .nil
  | x :: xs, hxsP => by
    simp only [insertionSortBy]
    apply pairwise_insertSortedBy hirrefl htrans htrich (hxsP x (.head _))
    · intro y hy
      exact hxsP y (.tail _ (mem_insertionSortBy lt y xs hy))
    · exact pairwise_insertionSortBy hirrefl htrans htrich (fun z hz => hxsP z (.tail _ hz))

theorem pairwise_perm_eq {α : Type} {P : α → Prop} {lt : α → α → Bool}
    (htrich : ∀ {a b}, P a → P b → lt a b = true ∨ a = b ∨ lt b a = true) :
    ∀ {l1 l2 : List α},
      (∀ x ∈ l1, P x) →
      l1.Pairwise (fun a b => ¬ lt b a = true) →
      l2.Pairwise (fun a b => ¬ lt b a = true) →
      List.Perm l1 l2 →
      l1 = l2
  | [], l2, _, _, _, hp => (List.perm_nil.mp hp.symm) ▸ rfl
  | x :: _, [], _, _, _, hp => nomatch (List.perm_nil.mp hp)
  | x :: xs, y :: ys, hP1, .cons hx hxs, .cons hy hys, hp => by
    have hxIn2 : x ∈ y :: ys := hp.subset (.head _)
    have hyIn1 : y ∈ x :: xs := hp.symm.subset (.head _)
    have hxP : P x := hP1 x (.head _)
    have hyP : P y := hP1 y hyIn1
    have hxy : x = y := by
      rcases List.mem_cons.mp hxIn2 with rfl | hxYs
      · rfl
      · rcases List.mem_cons.mp hyIn1 with rfl | hyXs
        · rfl
        · have hnotXY := hy x hxYs
          have hnotYX := hx y hyXs
          rcases htrich hxP hyP with hlt | heq | hgt
          · exact absurd hlt hnotXY
          · exact heq
          · exact absurd hgt hnotYX
    subst hxy
    congr 1
    exact pairwise_perm_eq htrich (fun z hz => hP1 z (.tail _ hz)) hxs hys ((List.perm_cons x).mp hp)

/-- Canonical sorting theorem: any two permutations of `P`-elements sort to the
    exact same list under `insertionSortBy lt`. -/
theorem insertionSortBy_perm_eq {α : Type} {P : α → Prop} {lt : α → α → Bool}
    (hirrefl : ∀ {a}, P a → lt a a = false)
    (htrans : ∀ {a b c}, P a → P b → P c → lt a b = true → lt b c = true → lt a c = true)
    (htrich : ∀ {a b}, P a → P b → lt a b = true ∨ a = b ∨ lt b a = true)
    {xs ys : List α} (hP : ∀ x ∈ xs, P x) (hperm : List.Perm xs ys) :
    insertionSortBy lt xs = insertionSortBy lt ys := by
  have hP2 : ∀ y ∈ ys, P y := fun y hy => hP y (hperm.symm.subset hy)
  have hp1 := pairwise_insertionSortBy hirrefl htrans htrich hP
  have hp2 := pairwise_insertionSortBy hirrefl htrans htrich hP2
  have hpermSort : List.Perm (insertionSortBy lt xs) (insertionSortBy lt ys) :=
    (insertionSortBy_perm lt xs).trans (hperm.trans (insertionSortBy_perm lt ys).symm)
  exact pairwise_perm_eq htrich
    (fun z hz => hP z (mem_insertionSortBy lt z xs hz)) hp1 hp2 hpermSort

inductive RelList {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : RelList R [] []
  | cons {a : α} {b : β} {as1 : List α} {bs1 : List β}
      (hd : R a b) (tl : RelList R as1 bs1) :
      RelList R (a :: as1) (b :: bs1)

theorem RelList.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ tl => congrArg (· + 1) tl.length_eq

theorem RelList.refl_of_forall {α : Type} {R : α → α → Prop} :
    ∀ {xs : List α}, (∀ x ∈ xs, R x x) → RelList R xs xs
  | [], _ => .nil
  | x :: _, h => .cons (h x (.head _)) (RelList.refl_of_forall fun y hy => h y (.tail _ hy))

theorem insertSortedBy_forall2 {α β : Type} {R : α → β → Prop}
    {lt1 : α → α → Bool} {lt2 : β → β → Bool}
    (hcong : ∀ a1 a2 b1 b2, R a1 b1 → R a2 b2 → lt1 a1 a2 = lt2 b1 b2)
    {x1 : α} {x2 : β} (hx : R x1 x2)
    {ys1 : List α} {ys2 : List β} (hys : RelList R ys1 ys2) :
    RelList R (insertSortedBy lt1 x1 ys1) (insertSortedBy lt2 x2 ys2) := by
  induction hys with
  | nil => exact .cons hx .nil
  | cons hy htl ih =>
    simp only [insertSortedBy, hcong _ _ _ _ hy hx]
    split
    · exact .cons hy ih
    · exact .cons hx (.cons hy htl)

theorem insertionSortBy_forall2 {α β : Type} {R : α → β → Prop}
    {lt1 : α → α → Bool} {lt2 : β → β → Bool}
    (hcong : ∀ a1 a2 b1 b2, R a1 b1 → R a2 b2 → lt1 a1 a2 = lt2 b1 b2)
    {xs1 : List α} {xs2 : List β} (hxs : RelList R xs1 xs2) :
    RelList R (insertionSortBy lt1 xs1) (insertionSortBy lt2 xs2) := by
  induction hxs with
  | nil => exact .nil
  | cons hx _ ih => exact insertSortedBy_forall2 hcong hx ih


/-! ## Sortable Types & Well-Formedness Bridge -/

mutual
def isSortableTy : Ty → Bool
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .data _ | .linearModel | .statTest => true
  | .option inner => isSortableTy inner
  | .result okTy errTy => isSortableTy okTy && isSortableTy errTy
  | .tuple elems => isSortableLTyList elems
  | .list elem => isSortableLTy elem
  | _ => false

def isSortableLTy : LTy → Bool
  | .mk ty _ => isSortableTy ty

def isSortableLTyList : List LTy → Bool
  | [] => true
  | l :: ls => isSortableLTy l && isSortableLTyList ls
end

@[simp] theorem ScalarTy.isSortable_toTy : ∀ (s : ScalarTy), isSortableTy s.toTy = true
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .data _ => rfl
  | .option inner => ScalarTy.isSortable_toTy inner

def progDatasSortableForNI (prog : Program) (_L : TagSet) : Bool :=
  prog.datas.all (fun d =>
    d.ctors.all (fun c =>
      c.fields.all (fun f => isSortableTy f.ty)))

theorem isSortableLTyList_of_forall :
    ∀ {ls : List LTy}, (∀ f ∈ ls, isSortableTy f.ty = true) → isSortableLTyList ls = true
  | [], _ => rfl
  | .mk ty ts :: rest, h => by
    simp only [isSortableLTyList, isSortableLTy, Bool.and_eq_true]
    exact ⟨h (.mk ty ts) (.head _), isSortableLTyList_of_forall fun f hf => h f (.tail _ hf)⟩

mutual
theorem valWf_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {v : Val} {ty : Ty}, ValWf prog v ty → isSortableTy ty = true → SortableVal v
  | _, _, hwf, hs => by
    cases hwf
    case unit => exact .unit
    case bool b => exact .bool b
    case int n _ => exact .int n
    case decimal d _ => exact .decimal d
    case float f => exact .float f
    case text s => exact .text s
    case bytes bs => exact .bytes bs
    case date d => exact .date d
    case timestamp ts => exact .timestamp ts
    case duration dur => exact .duration dur
    case optNone _ => exact .optNone
    case optSome _ _ hu => exact .optSome (valWf_sortable hd hu hs)
    case resOk _ _ _ hu =>
      simp only [isSortableTy, Bool.and_eq_true] at hs
      exact .resOk (valWf_sortable hd hu hs.1)
    case resErr _ _ _ he =>
      simp only [isSortableTy, Bool.and_eq_true] at hs
      exact .resErr (valWf_sortable hd he hs.2)
    case tuple _ _ hvs =>
      exact .tuple (valListWf_sortable hd hvs hs)
    case list _ elem hvs =>
      cases elem with | mk ety _ =>
      simp only [isSortableTy, isSortableLTy] at hs
      exact .list (valAllWf_sortable hd hvs hs)
    case ctor dName cName _ _ cDecl hfindD hfindC hvs =>
      have hdAll : ∀ d ∈ prog.datas, ∀ c ∈ d.ctors, ∀ f ∈ c.fields, isSortableTy f.ty = true := by
        unfold progDatasSortableForNI at hd
        simp only [List.all_eq_true] at hd
        intro d hdMem c hcMem f hfMem
        exact hd d hdMem c hcMem f hfMem
      have hfieldsS : isSortableLTyList cDecl.fields = true :=
        isSortableLTyList_of_forall (fun f hf =>
          hdAll _ (List.mem_of_find?_eq_some hfindD) _ (List.mem_of_find?_eq_some hfindC) f hf)
      exact .ctor dName cName (valListWf_sortable hd hvs hfieldsS)
    case linearModel s i r2 => exact .linearModel s i r2
    case statTest s p => exact .statTest s p
    all_goals contradiction

theorem valListWf_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {vs : List Val} {ltys : List LTy},
      ValListWf prog vs ltys → isSortableLTyList ltys = true → SortableValList vs
  | [], [], .nil, _ => .nil
  | _ :: _, .mk _ _ :: _, .cons hv htl, hs => by
    simp only [isSortableLTyList, isSortableLTy, Bool.and_eq_true] at hs
    exact .cons (valWf_sortable hd hv hs.1) (valListWf_sortable hd htl hs.2)

theorem valAllWf_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {vs : List Val} {ty : Ty},
      ValAllWf prog vs ty → isSortableTy ty = true → SortableValList vs
  | [], _, .nil _, _ => .nil
  | _ :: _, _, .cons hv htl, hs =>
    .cons (valWf_sortable hd hv hs) (valAllWf_sortable hd htl hs)
end


/-! ## Declassifier- & Sink-Safety Predicates for Non-Interference -/

mutual
def tySinksAllowed (L : TagSet) : Ty → Bool
  | .option inner => tySinksAllowed L inner
  | .result okTy errTy => tySinksAllowed L okTy && tySinksAllowed L errTy
  | .tuple elems => ltyListSinksAllowed L elems
  | .list elem => ltySinksAllowed L elem
  | .map k v => ltySinksAllowed L k && ltySinksAllowed L v
  | .fn params _ ret => ltyListSinksAllowed L params && ltySinksAllowed L ret
  | .console allows
  | .writeFiles _ allows
  | .writeTable _ _ _ _ allows
  | .httpsAllow _ allows => allows.subset L
  | _ => true

def ltySinksAllowed (L : TagSet) : LTy → Bool
  | .mk ty _ => tySinksAllowed L ty

def ltyListSinksAllowed (L : TagSet) : List LTy → Bool
  | [] => true
  | l :: ls => ltySinksAllowed L l && ltyListSinksAllowed L ls
end

@[simp] theorem ltySinksAllowed_addTags (L extra : TagSet) (l : LTy) :
    ltySinksAllowed L (l.addTags extra) = ltySinksAllowed L l := by
  cases l; rfl

@[simp] theorem ScalarTy.tySinksAllowed_toTy (L : TagSet) :
    ∀ (s : ScalarTy), tySinksAllowed L s.toTy = true
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .data _ => rfl
  | .option inner => ScalarTy.tySinksAllowed_toTy L inner

@[simp] theorem PlanTy.ltySinksAllowed_toLTy (L pc : TagSet) (pTy : PlanTy) :
    ltySinksAllowed L (pTy.toLTy pc) = true := by
  cases pTy <;> rfl

def litSafeForNI (L : TagSet) : Literal → Bool
  | .noneLit inner => tySinksAllowed L inner
  | _ => true

def primOpSafeForNI (L : TagSet) : PrimOp → Bool
  | .someVal inner | .okVal inner | .errVal inner => tySinksAllowed L inner
  | .listLit elem => ltySinksAllowed L elem
  | .mapLit k v => ltySinksAllowed L k && ltySinksAllowed L v
  | _ => true

def hostOpSafeForNI (L : TagSet) : HostOp → Bool
  | .declassifyApprove clearTags => clearTags.subset L
  | .fakeConsole _ | .fakeFiles _ | .fakeDB _ | .fakeHttps _ _ | .fakeSecret _ => false
  | _ => true

mutual
def rowExprSafeForNI (L : TagSet) : RowExpr → Bool
  | .lit v => litSafeForNI L v
  | .col _ | .outerVar _ | .constRef _ => true
  | .prim op args => primOpSafeForNI L op && rowExprListSafeForNI L args
  | .ifE c t e => rowExprSafeForNI L c && rowExprSafeForNI L t && rowExprSafeForNI L e
  | .coalesce o d => rowExprSafeForNI L o && rowExprSafeForNI L d
  | .callPure _ args => rowExprListSafeForNI L args

def rowExprListSafeForNI (L : TagSet) : List RowExpr → Bool
  | [] => true
  | r :: rs => rowExprSafeForNI L r && rowExprListSafeForNI L rs
end

def deriveItemSafeForNI (L : TagSet) : DeriveItem → Bool
  | .colExpr _ re => rowExprSafeForNI L re
  | .bucketCol _ _ _ _ => true

def aggItemSafeForNI (L : TagSet) (a : AggItem) : Bool :=
  match a.arg with
  | none => true
  | some re => rowExprSafeForNI L re

mutual
def exprSafeForNI (L : TagSet) : Expr → Bool
  | .lit v => litSafeForNI L v
  | .var _ | .constRef _ | .tableLit _ _ => true
  | .letE _ declLTy bnd body =>
    ltySinksAllowed L declLTy && exprSafeForNI L bnd && exprSafeForNI L body
  | .ifE c t e => exprSafeForNI L c && exprSafeForNI L t && exprSafeForNI L e
  | .caseE s arms => exprSafeForNI L s && caseArmsSafeForNI L arms
  | .lam params _ ret body =>
    ltyListSinksAllowed L (params.map Prod.snd) &&
    ltySinksAllowed L ret &&
    exprSafeForNI L body
  | .app f args => exprSafeForNI L f && exprListSafeForNI L args
  | .call _ args | .jump _ args | .tuple args | .ctor _ _ args =>
    exprListSafeForNI L args
  | .join _ params rhs body =>
    ltyListSinksAllowed L (params.map Prod.snd) &&
    exprSafeForNI L rhs &&
    exprSafeForNI L body
  | .proj e _ => exprSafeForNI L e
  | .prim op args => primOpSafeForNI L op && exprListSafeForNI L args
  | .rel p => planSafeForNI L p
  | .host op args => hostOpSafeForNI L op && exprListSafeForNI L args
  | .stop _ detail =>
    match detail with
    | none => true
    | some d => exprSafeForNI L d
  | .fail m => exprSafeForNI L m

def exprListSafeForNI (L : TagSet) : List Expr → Bool
  | [] => true
  | e :: es => exprSafeForNI L e && exprListSafeForNI L es

def caseArmsSafeForNI (L : TagSet) : List CaseArm → Bool
  | [] => true
  | .mk _ _ body :: rest => exprSafeForNI L body && caseArmsSafeForNI L rest

def planSafeForNI (L : TagSet) : Plan → Bool
  | .sourceExpr e => exprSafeForNI L e
  | .sourceDB cap _ _ => exprSafeForNI L cap
  | .select p _ | .drop p _ | .rename p _ | .distinct p _
  | .sort p _ | .limit p _ | .groupBy p _ | .window p _
  | .fillGaps p _ _ _ _ | .pivotWider p _ _ _ _ | .crosstab p _ _ _ _
  | .redact p _ _ => planSafeForNI L p
  | .derive p items => planSafeForNI L p && items.all (deriveItemSafeForNI L)
  | .filter p pred => planSafeForNI L p && rowExprSafeForNI L pred
  | .join _ l r _ _ | .union l r => planSafeForNI L l && planSafeForNI L r
  | .summarize p aggs _ => planSafeForNI L p && aggs.all (aggItemSafeForNI L)
  | .suppressSmallGroups p _ _ _ => planSafeForNI L p
  | .pseudonymize p _ sec =>
    L.mem "pii" && L.mem "secret" && planSafeForNI L p && exprSafeForNI L sec
end

mutual
def exprNoSpecCalls (prog : Program) : Expr → Bool
  | .lit _ | .var _ | .constRef _ | .tableLit _ _ => true
  | .letE _ _ bnd body => exprNoSpecCalls prog bnd && exprNoSpecCalls prog body
  | .ifE c t e => exprNoSpecCalls prog c && exprNoSpecCalls prog t && exprNoSpecCalls prog e
  | .caseE s arms => exprNoSpecCalls prog s && caseArmsNoSpecCalls prog arms
  | .lam _ _ _ body => exprNoSpecCalls prog body
  | .app f args => exprNoSpecCalls prog f && exprListNoSpecCalls prog args
  | .call fn args =>
    (match prog.findFun? fn with
     | some fd => !fd.kind.isSpec
     | none => true) && exprListNoSpecCalls prog args
  | .jump _ args | .tuple args | .ctor _ _ args | .prim _ args | .host _ args =>
    exprListNoSpecCalls prog args
  | .join _ _ rhs body => exprNoSpecCalls prog rhs && exprNoSpecCalls prog body
  | .proj e _ => exprNoSpecCalls prog e
  | .rel p => planNoSpecCalls prog p
  | .stop _ detail =>
    match detail with
    | none => true
    | some d => exprNoSpecCalls prog d
  | .fail m => exprNoSpecCalls prog m

def exprListNoSpecCalls (prog : Program) : List Expr → Bool
  | [] => true
  | e :: es => exprNoSpecCalls prog e && exprListNoSpecCalls prog es

def caseArmsNoSpecCalls (prog : Program) : List CaseArm → Bool
  | [] => true
  | .mk _ _ body :: rest => exprNoSpecCalls prog body && caseArmsNoSpecCalls prog rest

def planNoSpecCalls (prog : Program) : Plan → Bool
  | .sourceExpr e => exprNoSpecCalls prog e
  | .sourceDB cap _ _ => exprNoSpecCalls prog cap
  | .select p _ | .drop p _ | .rename p _ | .derive p _ | .filter p _
  | .distinct p _ | .sort p _ | .limit p _ | .groupBy p _ | .summarize p _ _
  | .suppressSmallGroups p _ _ _ | .window p _ | .fillGaps p _ _ _ _
  | .pivotWider p _ _ _ _ | .crosstab p _ _ _ _ | .redact p _ _ => planNoSpecCalls prog p
  | .join _ l r _ _ | .union l r => planNoSpecCalls prog l && planNoSpecCalls prog r
  | .pseudonymize p _ sec => planNoSpecCalls prog p && exprNoSpecCalls prog sec
end

/-- `SuppressSmallGroups` clears no sensitivity tag outside observer clearance `L`. -/
def suppressClearsOnlyL (L : TagSet) (tt : TableTy) : Bool :=
  tt.rowTags.subset L &&
  tt.cols.all (fun c =>
    if (decide (c.aggKind = .groupKey) && c.bucketed) || decide (c.aggKind = .blending) then
      c.tags.subset L
    else true)

mutual
def exprSuppressSafe (prog : Program) (L : TagSet) (env : TyEnv) (pc : TagSet) : Expr → Bool
  | .lit _ | .var _ | .constRef _ | .tableLit _ _ => true
  | .letE name declLTy bnd body =>
    exprSuppressSafe prog L env pc bnd &&
    exprSuppressSafe prog L ((name, declLTy.addTags pc) :: env) pc body
  | .ifE cond tBr eBr =>
    match checkExpr prog env [] pc false cond with
    | .ok cLTy =>
      let brPc := pc.union cLTy.tags
      exprSuppressSafe prog L env pc cond &&
      exprSuppressSafe prog L env brPc tBr &&
      exprSuppressSafe prog L env brPc eBr
    | .error _ => false
  | .caseE scrut arms =>
    match checkExpr prog env [] pc false scrut with
    | .ok sLTy =>
      let armPc := pc.union sLTy.effectiveTags
      match expectedCaseSpecs prog sLTy.ty sLTy.effectiveTags with
      | .ok specs =>
        exprSuppressSafe prog L env pc scrut &&
        caseArmsSuppressSafe prog L env armPc specs arms
      | .error _ => false
    | .error _ => false
  | .lam params fnPc _ body =>
    exprSuppressSafe prog L (extendTyEnv env params) fnPc body
  | .app fnE args =>
    exprSuppressSafe prog L env pc fnE && exprListSuppressSafe prog L env pc args
  | .call _ args | .jump _ args | .tuple args | .ctor _ _ args | .prim _ args | .host _ args =>
    exprListSuppressSafe prog L env pc args
  | .join label params rhs body =>
    let guess1 := pc.union (inferJumpPc prog label env pc body)
    let rhsEnv := extendTyEnv env params
    let joinPc := guess1.union (inferJumpPc prog label rhsEnv guess1 rhs)
    exprSuppressSafe prog L rhsEnv joinPc rhs &&
    exprSuppressSafe prog L env pc body
  | .proj e _ => exprSuppressSafe prog L env pc e
  | .rel p => planSuppressSafe prog L env pc p
  | .stop _ detail =>
    match detail with
    | none => true
    | some d => exprSuppressSafe prog L env pc d
  | .fail m => exprSuppressSafe prog L env pc m

def exprListSuppressSafe (prog : Program) (L : TagSet) (env : TyEnv) (pc : TagSet) :
    List Expr → Bool
  | [] => true
  | e :: es => exprSuppressSafe prog L env pc e && exprListSuppressSafe prog L env pc es

def caseArmsSuppressSafe (prog : Program) (L : TagSet) (env : TyEnv) (armPc : TagSet)
    (specs : List (Ident × List LTy)) : List CaseArm → Bool
  | [] => true
  | .mk cName binders body :: rest =>
    match specs.find? (fun (sn, _) => sn == cName) with
    | some (_, fieldLTys) =>
      let armBindings := List.zip binders (fieldLTys.map (fun f => f.addTags armPc))
      exprSuppressSafe prog L (extendTyEnv env armBindings) armPc body &&
      caseArmsSuppressSafe prog L env armPc specs rest
    | none => false

def planSuppressSafe (prog : Program) (L : TagSet) (env : TyEnv) (pc : TagSet) : Plan → Bool
  | .sourceExpr e => exprSuppressSafe prog L env pc e
  | .sourceDB cap _ _ => exprSuppressSafe prog L env pc cap
  | .select p _ | .drop p _ | .rename p _ | .derive p _ | .filter p _
  | .distinct p _ | .sort p _ | .limit p _ | .groupBy p _ | .summarize p _ _
  | .window p _ | .fillGaps p _ _ _ _ | .pivotWider p _ _ _ _ | .crosstab p _ _ _ _
  | .redact p _ _ => planSuppressSafe prog L env pc p
  | .join _ l r _ _ | .union l r =>
    planSuppressSafe prog L env pc l && planSuppressSafe prog L env pc r
  | .suppressSmallGroups inp _ _ _ =>
    planSuppressSafe prog L env pc inp &&
    match checkPlan prog env pc false inp with
    | .ok (.table tt) => suppressClearsOnlyL L tt
    | _ => false
  | .pseudonymize p _ sec =>
    planSuppressSafe prog L env pc p && exprSuppressSafe prog L env pc sec
end

def progSafeForNI (prog : Program) (L : TagSet) : Bool :=
  progDatasSortableForNI prog L &&
  prog.datas.all (fun d => d.ctors.all (fun c => ltyListSinksAllowed L c.fields)) &&
  prog.consts.all (fun c => ltySinksAllowed L c.lty && litSafeForNI L c.value) &&
  prog.funs.all (fun f =>
    f.kind.isSpec ||
    (ltyListSinksAllowed L (f.params.map Prod.snd) &&
     ltySinksAllowed L f.ret &&
     exprSafeForNI L f.body &&
     exprSuppressSafe prog L f.params.reverse f.pc f.body))

mutual
theorem checkExpr_noSpecCalls {prog : Program} :
    ∀ {env : TyEnv} {jenv : JoinEnv} {pc : TagSet} {e : Expr} {lty : LTy},
      checkExpr prog env jenv pc false e = .ok lty →
      exprNoSpecCalls prog e = true
  | _, _, _, .lit _, _, _ => rfl
  | _, _, _, .var _, _, _ => rfl
  | _, _, _, .constRef _, _, _ => rfl
  | _, _, _, .tableLit _ _, _, _ => rfl
  | _, _, _, .letE _ _ bnd body, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hb : checkExpr prog _ [] _ false bnd <;> rw [hb] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    simp [exprNoSpecCalls, checkExpr_noSpecCalls hb, checkExpr_noSpecCalls hchk]
  | _, _, _, .ifE c t e, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hc : checkExpr prog _ [] _ false c <;> rw [hc] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    cases ht : checkExpr prog _ _ _ false t <;> rw [ht] at hchk <;> try contradiction
    dsimp only at hchk
    cases he : checkExpr prog _ _ _ false e <;> rw [he] at hchk <;> try contradiction
    simp [exprNoSpecCalls, checkExpr_noSpecCalls hc, checkExpr_noSpecCalls ht, checkExpr_noSpecCalls he]
  | _, _, _, .caseE s arms, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hs : checkExpr prog _ [] _ false s <;> rw [hs] at hchk <;> try contradiction
    dsimp only at hchk
    cases hsp : expectedCaseSpecs prog _ _ <;> rw [hsp] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    cases ha : checkCaseArms prog _ _ _ false _ arms <;> rw [ha] at hchk <;> try contradiction
    simp [exprNoSpecCalls, checkExpr_noSpecCalls hs, checkCaseArms_noSpecCalls ha]
  | _, _, _, .lam _ _ _ body, _, hchk => by
    unfold checkExpr at hchk
    repeat (split at hchk <;> try contradiction)
    simp only [bind, Except.bind] at hchk
    cases hb : checkExpr prog _ [] _ false body <;> rw [hb] at hchk <;> try contradiction
    dsimp only [exprNoSpecCalls]
    exact checkExpr_noSpecCalls hb
  | _, _, _, .app f args, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hf : checkExpr prog _ [] _ false f <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk
    cases ha : checkExprList prog _ _ false args <;> rw [ha] at hchk <;> try contradiction
    simp [exprNoSpecCalls, checkExpr_noSpecCalls hf, checkExprList_noSpecCalls ha]
  | _, _, _, .call fn args, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog _ _ false args <;> rw [ha] at hchk <;> try contradiction
    dsimp only at hchk
    cases hf : prog.findFun? fn <;> rw [hf] at hchk <;> try contradiction
    rename_i fd; dsimp only at hchk; split at hchk <;> try contradiction
    rename_i hns
    have hns' : (!fd.kind.isSpec) = true := by
      cases h : fd.kind.isSpec <;> simp [h] at hns ⊢
    simp [exprNoSpecCalls, hf, hns', checkExprList_noSpecCalls ha]
  | _, _, _, .join _ _ rhs body, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    dsimp only at hchk
    cases hinf : inferJoinRetLTy prog _ _ _ _ rhs body <;> rw [hinf] at hchk <;> try contradiction
    dsimp only [bind, Except.bind] at hchk; split at hchk <;> try contradiction
    cases hr : checkExpr prog _ _ _ false rhs <;> rw [hr] at hchk <;> try contradiction
    dsimp only at hchk
    cases hb : checkExpr prog _ _ _ false body <;> rw [hb] at hchk <;> try contradiction
    simp [exprNoSpecCalls, checkExpr_noSpecCalls hr, checkExpr_noSpecCalls hb]
  | _, _, _, .jump _ args, _, hchk
  | _, _, _, .tuple args, _, hchk
  | _, _, _, .ctor _ _ args, _, hchk
  | _, _, _, .prim _ args, _, hchk
  | _, _, _, .host _ args, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog _ _ false args <;> rw [ha] at hchk <;> try contradiction
    exact checkExprList_noSpecCalls ha
  | _, _, _, .proj e _, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases he : checkExpr prog _ [] _ false e <;> rw [he] at hchk <;> try contradiction
    dsimp only [exprNoSpecCalls]
    exact checkExpr_noSpecCalls he
  | _, _, _, .rel p, _, hchk => by
    unfold checkExpr at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hp : checkPlan prog _ _ false p <;> rw [hp] at hchk <;> try contradiction
    exact checkPlan_noSpecCalls hp
  | _, _, _, .stop _ none, _, _ => rfl
  | _, _, _, .stop _ (some d), _, hchk => by
    unfold checkExpr at hchk; dsimp only at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hd : checkExpr prog _ [] _ false d <;> rw [hd] at hchk <;> try contradiction
    dsimp only [exprNoSpecCalls]
    exact checkExpr_noSpecCalls hd
  | _, _, _, .fail _, _, hchk => by
    unfold checkExpr at hchk; contradiction

theorem checkExprList_noSpecCalls {prog : Program} :
    ∀ {env : TyEnv} {pc : TagSet} {es : List Expr} {ltys : List LTy},
      checkExprList prog env pc false es = .ok ltys →
      exprListNoSpecCalls prog es = true
  | _, _, [], _, _ => rfl
  | _, _, e :: es, _, hchk => by
    unfold checkExprList at hchk; simp only [bind, Except.bind] at hchk
    cases hh : checkExpr prog _ [] _ false e <;> rw [hh] at hchk <;> try contradiction
    dsimp only at hchk
    cases ht : checkExprList prog _ _ false es <;> rw [ht] at hchk <;> try contradiction
    simp [exprListNoSpecCalls, checkExpr_noSpecCalls hh, checkExprList_noSpecCalls ht]

theorem checkCaseArms_noSpecCalls {prog : Program} :
    ∀ {env : TyEnv} {jenv : JoinEnv} {armPc : TagSet} {specs : List (Ident × List LTy)}
      {arms : List CaseArm} {ltys : List LTy},
      checkCaseArms prog env jenv armPc false specs arms = .ok ltys →
      caseArmsNoSpecCalls prog arms = true
  | _, _, _, _, [], _, _ => rfl
  | _, _, _, specs, .mk cName binders body :: rest, _, hchk => by
    unfold checkCaseArms at hchk
    cases hf : specs.find? (fun (sn, _) => sn == cName) <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hh : checkExpr prog _ _ _ false body <;> rw [hh] at hchk <;> try contradiction
    dsimp only at hchk
    cases ht : checkCaseArms prog _ _ _ false _ rest <;> rw [ht] at hchk <;> try contradiction
    simp [caseArmsNoSpecCalls, checkExpr_noSpecCalls hh, checkCaseArms_noSpecCalls ht]

theorem checkPlan_noSpecCalls {prog : Program} :
    ∀ {env : TyEnv} {pc : TagSet} {p : Plan} {pTy : PlanTy},
      checkPlan prog env pc false p = .ok pTy →
      planNoSpecCalls prog p = true
  | _, _, .sourceExpr e, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases he : checkExpr prog _ [] _ false e <;> rw [he] at hchk <;> try contradiction
    exact checkExpr_noSpecCalls he
  | _, _, .sourceDB cap _ _, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hc : checkExpr prog _ [] _ false cap <;> rw [hc] at hchk <;> try contradiction
    exact checkExpr_noSpecCalls hc
  | _, _, .select p _, _, hchk | _, _, .drop p _, _, hchk | _, _, .rename p _, _, hchk
  | _, _, .derive p _, _, hchk | _, _, .filter p _, _, hchk | _, _, .distinct p _, _, hchk
  | _, _, .sort p _, _, hchk | _, _, .limit p _, _, hchk | _, _, .groupBy p _, _, hchk
  | _, _, .summarize p _ _, _, hchk | _, _, .suppressSmallGroups p _ _ _, _, hchk
  | _, _, .window p _, _, hchk | _, _, .fillGaps p _ _ _ _, _, hchk
  | _, _, .pivotWider p _ _ _ _, _, hchk | _, _, .crosstab p _ _ _ _, _, hchk
  | _, _, .redact p _ _, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hp : checkPlan prog _ _ false p <;> rw [hp] at hchk <;> try contradiction
    dsimp only [planNoSpecCalls]
    exact checkPlan_noSpecCalls hp
  | _, _, .join _ l r _ _, _, hchk | _, _, .union l r, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hl : checkPlan prog _ _ false l <;> rw [hl] at hchk <;> try contradiction
    dsimp only at hchk
    cases hr : checkPlan prog _ _ false r <;> rw [hr] at hchk <;> try contradiction
    simp [planNoSpecCalls, checkPlan_noSpecCalls hl, checkPlan_noSpecCalls hr]
  | _, _, .pseudonymize p _ sec, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hp : checkPlan prog _ _ false p <;> rw [hp] at hchk <;> try contradiction
    dsimp only at hchk
    cases hs : checkExpr prog _ [] _ false sec <;> rw [hs] at hchk <;> try contradiction
    simp [planNoSpecCalls, checkPlan_noSpecCalls hp, checkExpr_noSpecCalls hs]
end

def tyEnvSinksAllowed (L : TagSet) (env : TyEnv) : Bool :=
  env.all (fun (_, l) => ltySinksAllowed L l)

def joinEnvSinksAllowed (L : TagSet) (jenv : JoinEnv) : Bool :=
  jenv.all (fun (_, sig) =>
    ltyListSinksAllowed L (sig.params.map Prod.snd) && ltySinksAllowed L sig.retLTy)

mutual
def valSafeForNI (L : TagSet) : Val → Bool
  | .optSome v | .resOk v | .resErr v => valSafeForNI L v
  | .tuple vs | .list vs | .ctor _ _ vs => valListSafeForNI L vs
  | .map kvs => valPairsSafeForNI L kvs
  | .closure params _ retLTy body capEnv =>
    ltyListSinksAllowed L (params.map Prod.snd) &&
    ltySinksAllowed L retLTy &&
    exprSafeForNI L body &&
    envSafeForNI L capEnv
  | _ => true
  termination_by structural v => v

def valListSafeForNI (L : TagSet) : List Val → Bool
  | [] => true
  | v :: vs => valSafeForNI L v && valListSafeForNI L vs
  termination_by structural vs => vs

def valPairsSafeForNI (L : TagSet) : List (Val × Val) → Bool
  | [] => true
  | (k, v) :: rest => valSafeForNI L k && valSafeForNI L v && valPairsSafeForNI L rest
  termination_by structural ps => ps

def envSafeForNI (L : TagSet) : List EnvEntry → Bool
  | [] => true
  | .mk _ lty v :: rest => ltySinksAllowed L lty && valSafeForNI L v && envSafeForNI L rest
  termination_by structural es => es
end

theorem ltyListSinksAllowed_iff {L : TagSet} {ls : List LTy} :
    ltyListSinksAllowed L ls = true ↔ ∀ l ∈ ls, ltySinksAllowed L l = true := by
  induction ls with
  | nil => simp [ltyListSinksAllowed]
  | cons l rest ih => simp [ltyListSinksAllowed, Bool.and_eq_true, ih]

theorem valListSafeForNI_iff {L : TagSet} {vs : List Val} :
    valListSafeForNI L vs = true ↔ ∀ v ∈ vs, valSafeForNI L v = true := by
  induction vs with
  | nil => simp [valListSafeForNI]
  | cons v rest ih => simp [valListSafeForNI, Bool.and_eq_true, ih]

theorem envSafeForNI_imp_tyEnv {L : TagSet} :
    ∀ {env : Env}, envSafeForNI L env = true → tyEnvSinksAllowed L (envToTyEnv env) = true
  | [], _ => rfl
  | .mk _ _ _ :: rest, h => by
    simp only [envSafeForNI, Bool.and_eq_true] at h
    simp only [envToTyEnv, List.map_cons, tyEnvSinksAllowed, List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.1, envSafeForNI_imp_tyEnv h.2⟩

theorem lookupTyEnv_sinksAllowed {L : TagSet} {env : TyEnv} {name : Ident} {lty : LTy}
    (henv : tyEnvSinksAllowed L env = true)
    (hlook : lookupTyEnv env name = some lty) :
    ltySinksAllowed L lty = true := by
  induction env with
  | nil => simp [lookupTyEnv] at hlook
  | cons hd tl ih =>
    simp only [tyEnvSinksAllowed, List.all_cons, Bool.and_eq_true] at henv
    simp only [lookupTyEnv] at hlook
    split at hlook
    · injection hlook with h; subst h; exact henv.1
    · exact ih henv.2 hlook

theorem lookupEnv_safeForNI {L : TagSet} {env : Env} {name : Ident} {lty : LTy} {v : Val}
    (henv : envSafeForNI L env = true)
    (hlook : lookupEnv env name = some (lty, v)) :
    ltySinksAllowed L lty = true ∧ valSafeForNI L v = true := by
  induction env with
  | nil => simp [lookupEnv] at hlook
  | cons hd tl ih =>
    cases hd
    simp only [envSafeForNI, Bool.and_eq_true] at henv
    simp only [lookupEnv] at hlook
    split at hlook
    · injection hlook with h; injection h with h1 h2; subst h1; subst h2
      exact ⟨henv.1.1, henv.1.2⟩
    · exact ih henv.2 hlook

theorem checkLiteral_sinksAllowed {prog : Program} {L pc : TagSet} {lit : Literal} {lty : LTy}
    (hsafe : litSafeForNI L lit = true)
    (hchk : checkLiteral prog pc lit = .ok lty) :
    ltySinksAllowed L lty = true := by
  cases lit <;> simp only [checkLiteral] at hchk
  all_goals try (injection hchk with h; subst h; rfl)
  case int | decimal =>
    split at hchk <;> try contradiction
    injection hchk with h; subst h; rfl
  case noneLit inner =>
    split at hchk <;> try contradiction
    injection hchk with h; subst h
    exact hsafe

@[simp] theorem tySinksAllowed_ty (L : TagSet) (l : LTy) :
    tySinksAllowed L l.ty = ltySinksAllowed L l := by
  cases l; rfl

theorem checkPrimOp_sinksAllowed {prog : Program} {L pc : TagSet} {op : PrimOp}
    {args : List LTy} {lty : LTy}
    (hsafe : primOpSafeForNI L op = true)
    (hargs : ltyListSinksAllowed L args = true)
    (hchk : checkPrimOp prog pc op args = .ok lty) :
    ltySinksAllowed L lty = true := by
  unfold checkPrimOp at hchk
  split at hchk
  all_goals (
    repeat (
      try dsimp only at hchk
      first
      | contradiction
      | (injection hchk with h; subst h)
      | (split at hchk <;> try contradiction)
    )
  )
  all_goals (
    try simp only [primOpSafeForNI, ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed,
      ltySinksAllowed_addTags, tySinksAllowed_ty, Bool.and_eq_true, and_self] at hsafe hargs ⊢
  )
  all_goals (
    first
    | rfl
    | trivial
    | exact hsafe
    | exact hargs.1
    | exact hargs.1.2
    | exact ⟨hargs.1, hsafe⟩
    | exact ⟨hsafe, hargs.1⟩
  )

theorem checkHostOp_sinksAllowed {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {op : HostOp} {args : List LTy} {lty : LTy}
    (hsafe : hostOpSafeForNI L op = true)
    (hargs : ltyListSinksAllowed L args = true)
    (hchk : checkHostOp prog pc inSpec op args = .ok lty) :
    ltySinksAllowed L lty = true := by
  unfold checkHostOp at hchk
  split at hchk
  all_goals (try (simp [hostOpSafeForNI] at hsafe))
  all_goals (
    repeat (
      try dsimp only at hchk
      first
      | contradiction
      | (injection hchk with h; subst h)
      | (simp only [bind, Except.bind] at hchk; split at hchk <;> try contradiction)
      | (split at hchk <;> try contradiction)
    )
  )
  all_goals (
    try simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed,
      tySinksAllowed_ty, Bool.and_eq_true, and_self] at hargs ⊢
  )
  all_goals (first | rfl | trivial | exact hargs.2.1)

theorem extendTyEnv_sinksAllowed {L : TagSet} {env : TyEnv} {bindings : List (Ident × LTy)}
    (henv : tyEnvSinksAllowed L env = true)
    (hb : ltyListSinksAllowed L (bindings.map Prod.snd) = true) :
    tyEnvSinksAllowed L (extendTyEnv env bindings) = true := by
  unfold extendTyEnv tyEnvSinksAllowed
  rw [List.all_append, Bool.and_eq_true]
  refine ⟨?_, henv⟩
  rw [List.all_eq_true]
  rw [ltyListSinksAllowed_iff] at hb
  intro p hp
  exact hb p.2 (List.mem_map_of_mem hp)

mutual
theorem inferBranchLTy_sinksAllowed {prog : Program} {L : TagSet}
    (hprog : progSafeForNI prog L = true) :
    ∀ {env : TyEnv} {jenv : JoinEnv} {curPc : TagSet} {skip : List Ident} {e : Expr} {lty : LTy},
      tyEnvSinksAllowed L env = true →
      joinEnvSinksAllowed L jenv = true →
      exprSafeForNI L e = true →
      exprNoSpecCalls prog e = true →
      inferBranchLTy prog env jenv curPc skip e = some lty →
      ltySinksAllowed L lty = true
  | env, _, curPc, _, .lit v, lty, _, _, hs, _, hinf => by
    simp only [inferBranchLTy, Except.toOption] at hinf
    cases hc : checkLiteral prog curPc v with
    | error _ => rw [hc] at hinf; nomatch hinf
    | ok l => rw [hc] at hinf; injection hinf with h; subst h; exact checkLiteral_sinksAllowed hs hc
  | env, _, curPc, _, .var x, lty, henv, _, _, _, hinf => by
    simp only [inferBranchLTy, Option.map_eq_some_iff] at hinf
    rcases hinf with ⟨l, hlook, rfl⟩
    simp [lookupTyEnv_sinksAllowed henv hlook]
  | _, _, curPc, _, .constRef c, lty, _, _, _, _, hinf => by
    simp only [inferBranchLTy, Option.map_eq_some_iff] at hinf
    rcases hinf with ⟨cd, hfind, rfl⟩
    simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hprog
    have hcd := (hprog.1.2 cd (List.mem_of_find?_eq_some hfind)).1
    simpa using hcd
  | env, jenv, curPc, skip, .letE x dLTy _ body, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    have henv' : tyEnvSinksAllowed L ((x, dLTy.addTags curPc) :: env) = true := by
      unfold tyEnvSinksAllowed at henv ⊢
      simp [hs.1.1, henv]
    exact inferBranchLTy_sinksAllowed hprog henv' hjenv hs.2 hns.2 hinf
  | env, jenv, curPc, skip, .ifE cond tBr eBr, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    simp only [inferBranchLTy] at hinf
    cases ht : inferBranchLTy prog env jenv (curPc.union (exprQuickTags prog env cond)) skip tBr <;>
      cases he : inferBranchLTy prog env jenv (curPc.union (exprQuickTags prog env cond)) skip eBr <;>
      simp only [ht, he] at hinf
    · nomatch hinf
    · injection hinf with h; subst h; simp [inferBranchLTy_sinksAllowed hprog henv hjenv hs.2 hns.2 he]
    · injection hinf with h; subst h; simp [inferBranchLTy_sinksAllowed hprog henv hjenv hs.1.2 hns.1.2 ht]
    · injection hinf with h; subst h
      have htOk := inferBranchLTy_sinksAllowed hprog henv hjenv hs.1.2 hns.1.2 ht
      rename_i l1 _
      cases l1; exact htOk
  | env, jenv, curPc, skip, .caseE scrut arms, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    exact inferBranchArms_sinksAllowed hprog henv hjenv hs.2 hns.2 hinf
  | _, _, _, _, .lam params _ retLTy _, lty, _, _, hs, _, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    injection hinf with h; subst h
    simp [ltySinksAllowed, tySinksAllowed, hs.1.1, hs.1.2]
  | _, _, curPc, _, .call fn _, lty, _, _, _, hns, hinf => by
    simp only [inferBranchLTy, Option.map_eq_some_iff] at hinf
    rcases hinf with ⟨fd, hfind, rfl⟩
    simp only [exprNoSpecCalls, hfind, Bool.and_eq_true, Bool.not_eq_true'] at hns
    simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hprog
    have hfd := hprog.2 fd (List.mem_of_find?_eq_some hfind)
    simp only [hns.1, Bool.false_or, Bool.and_eq_true] at hfd
    simpa using hfd.1.1.2
  | env, jenv, curPc, skip, .app fnE _, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    simp only [inferBranchLTy] at hinf
    cases hf : inferBranchLTy prog env jenv curPc skip fnE with
    | none => rw [hf] at hinf; nomatch hinf
    | some fl =>
      rw [hf] at hinf
      have hfl := inferBranchLTy_sinksAllowed hprog henv hjenv hs.1 hns.1 hf
      cases fl with | mk fty fts =>
      cases fty <;> simp at hinf
      subst hinf
      simp only [ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hfl
      simpa using hfl.2
  | env, jenv, curPc, skip, .join lbl params subRhs subBody, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    simp only [inferBranchLTy] at hinf
    have hsubEnv := extendTyEnv_sinksAllowed henv hs.1.1
    cases hr : inferBranchLTy prog (extendTyEnv env params) jenv curPc (lbl :: skip) subRhs with
    | some l =>
      rw [hr] at hinf; injection hinf with h; subst h
      exact inferBranchLTy_sinksAllowed hprog hsubEnv hjenv hs.1.2 hns.1 hr
    | none =>
      rw [hr] at hinf
      exact inferBranchLTy_sinksAllowed hprog henv hjenv hs.2 hns.2 hinf
  | _, jenv, _, skip, .jump lbl _, lty, _, hjenv, _, _, hinf => by
    simp only [inferBranchLTy] at hinf
    split at hinf
    · nomatch hinf
    · simp only [Option.map_eq_some_iff] at hinf
      rcases hinf with ⟨sig, hlook, rfl⟩
      induction jenv with
      | nil => simp [lookupJoinEnv] at hlook
      | cons hd tl ih =>
        simp only [joinEnvSinksAllowed, List.all_cons, Bool.and_eq_true] at hjenv
        simp only [lookupJoinEnv] at hlook
        split at hlook
        · injection hlook with h; subst h; exact hjenv.1.2
        · exact ih hjenv.2 hlook
  | env, jenv, curPc, skip, .tuple es, lty, henv, hjenv, hs, hns, hinf => by
    simp only [inferBranchLTy, Option.map_eq_some_iff] at hinf
    rcases hinf with ⟨ls, hls, rfl⟩
    exact inferBranchList_sinksAllowed hprog henv hjenv hs hns hls
  | env, jenv, curPc, skip, .proj e idx, lty, henv, hjenv, hs, hns, hinf => by
    have hsE : exprSafeForNI L e = true := hs
    have hnsE : exprNoSpecCalls prog e = true := hns
    simp only [inferBranchLTy] at hinf
    cases he : inferBranchLTy prog env jenv curPc skip e with
    | none => rw [he] at hinf; nomatch hinf
    | some el =>
      rw [he] at hinf
      have hel := inferBranchLTy_sinksAllowed hprog henv hjenv hsE hnsE he
      cases el with | mk ety ets =>
      cases ety <;> simp at hinf
      case tuple ls =>
        rcases hinf with ⟨item, hget, rfl⟩
        simp only [ltySinksAllowed, tySinksAllowed] at hel
        rw [ltyListSinksAllowed_iff] at hel
        simpa using hel item (List.mem_of_getElem? hget)
  | _, _, _, _, .ctor _ _ _, lty, _, _, _, _, hinf => by
    injection hinf with h; subst h; rfl
  | _, _, _, _, .tableLit _ _, lty, _, _, _, _, hinf => by
    injection hinf with h; subst h; rfl
  | env, jenv, curPc, skip, .prim op as1, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [inferBranchLTy, Except.toOption] at hinf
    cases hl : inferBranchList prog env jenv curPc skip as1 with
    | none => rw [hl] at hinf; nomatch hinf
    | some ltys =>
      rw [hl] at hinf; dsimp only at hinf
      have hltys := inferBranchList_sinksAllowed hprog henv hjenv hs.2 hns hl
      cases hc : checkPrimOp prog curPc op ltys with
      | error _ => rw [hc] at hinf; nomatch hinf
      | ok res => rw [hc] at hinf; injection hinf with h; subst h; exact checkPrimOp_sinksAllowed hs.1 hltys hc
  | _, _, curPc, skip, .rel p, lty, _, _, _, _, hinf => by
    clear hprog
    cases p <;> simp only [inferBranchLTy, inferQuickPlanLTy] at hinf
    all_goals (
      repeat (
        first
        | contradiction
        | (injection hinf with h; subst h; rfl)
        | (simp only [Option.map_eq_some_iff] at hinf; rcases hinf with ⟨_, _, rfl⟩; rfl)
        | split at hinf
      )
    )
  | env, jenv, curPc, skip, .host op as1, lty, henv, hjenv, hs, hns, hinf => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [inferBranchLTy, Except.toOption] at hinf
    cases hl : inferBranchList prog env jenv curPc skip as1 with
    | none => rw [hl] at hinf; nomatch hinf
    | some ltys =>
      rw [hl] at hinf; dsimp only at hinf
      have hltys := inferBranchList_sinksAllowed hprog henv hjenv hs.2 hns hl
      cases hc : checkHostOp prog curPc true op ltys with
      | error _ => rw [hc] at hinf; nomatch hinf
      | ok res => rw [hc] at hinf; injection hinf with h; subst h; exact checkHostOp_sinksAllowed hs.1 hltys hc
  | _, _, _, _, .stop _ _, lty, _, _, _, _, hinf => by
    injection hinf with h; subst h; rfl
  | _, _, _, _, .fail _, lty, _, _, _, _, hinf => by
    injection hinf with h; subst h; rfl

theorem inferBranchList_sinksAllowed {prog : Program} {L : TagSet}
    (hprog : progSafeForNI prog L = true) :
    ∀ {env : TyEnv} {jenv : JoinEnv} {curPc : TagSet} {skip : List Ident} {es : List Expr} {ltys : List LTy},
      tyEnvSinksAllowed L env = true →
      joinEnvSinksAllowed L jenv = true →
      exprListSafeForNI L es = true →
      exprListNoSpecCalls prog es = true →
      inferBranchList prog env jenv curPc skip es = some ltys →
      ltyListSinksAllowed L ltys = true
  | _, _, _, _, [], _, _, _, _, _, hinf => by
    injection hinf with h; subst h; rfl
  | env, jenv, curPc, skip, e :: rest, _, henv, hjenv, hs, hns, hinf => by
    simp only [exprListSafeForNI, Bool.and_eq_true] at hs
    simp only [exprListNoSpecCalls, Bool.and_eq_true] at hns
    simp only [inferBranchList, bind, Option.bind] at hinf
    cases hh : inferBranchLTy prog env jenv curPc skip e with
    | none => rw [hh] at hinf; nomatch hinf
    | some hd =>
      rw [hh] at hinf; dsimp only at hinf
      cases ht : inferBranchList prog env jenv curPc skip rest with
      | none => rw [ht] at hinf; nomatch hinf
      | some tl =>
        rw [ht] at hinf; injection hinf with h; subst h
        simp [ltyListSinksAllowed, inferBranchLTy_sinksAllowed hprog henv hjenv hs.1 hns.1 hh,
          inferBranchList_sinksAllowed hprog henv hjenv hs.2 hns.2 ht]

theorem inferBranchArms_sinksAllowed {prog : Program} {L : TagSet}
    (hprog : progSafeForNI prog L = true) :
    ∀ {env : TyEnv} {jenv : JoinEnv} {armPc : TagSet} {skip : List Ident} {arms : List CaseArm} {lty : LTy},
      tyEnvSinksAllowed L env = true →
      joinEnvSinksAllowed L jenv = true →
      caseArmsSafeForNI L arms = true →
      caseArmsNoSpecCalls prog arms = true →
      inferBranchArms prog env jenv armPc skip arms = some lty →
      ltySinksAllowed L lty = true
  | _, _, _, _, [], _, _, _, _, _, hinf => nomatch hinf
  | env, jenv, armPc, skip, .mk _ _ body :: rest, lty, henv, hjenv, hs, hns, hinf => by
    simp only [caseArmsSafeForNI, Bool.and_eq_true] at hs
    simp only [caseArmsNoSpecCalls, Bool.and_eq_true] at hns
    simp only [inferBranchArms] at hinf
    cases hb : inferBranchLTy prog env jenv armPc skip body <;>
      cases hr : inferBranchArms prog env jenv armPc skip rest <;>
      simp only [hb, hr] at hinf
    · nomatch hinf
    · injection hinf with h; subst h; simp [inferBranchArms_sinksAllowed hprog henv hjenv hs.2 hns.2 hr]
    · injection hinf with h; subst h; simp [inferBranchLTy_sinksAllowed hprog henv hjenv hs.1 hns.1 hb]
    · injection hinf with h; subst h
      have hbOk := inferBranchLTy_sinksAllowed hprog henv hjenv hs.1 hns.1 hb
      rename_i l1 _
      cases l1; exact hbOk
end

theorem expectedCaseSpecs_sinksAllowed {prog : Program} {L : TagSet} {scrutTy : Ty} {scrutTags : TagSet}
    {specs : List (Ident × List LTy)}
    (hprog : progSafeForNI prog L = true)
    (hscrut : tySinksAllowed L scrutTy = true)
    (hexp : expectedCaseSpecs prog scrutTy scrutTags = .ok specs) :
    ∀ p ∈ specs, ltyListSinksAllowed L p.2 = true := by
  cases scrutTy <;> simp only [expectedCaseSpecs] at hexp <;> try contradiction
  case bool =>
    injection hexp with h; subst h
    intro p hp; rcases List.mem_cons.mp hp with rfl | h2
    · rfl
    · rcases List.mem_cons.mp h2 with rfl | h3; rfl; nomatch h3
  case option inner =>
    unfold tySinksAllowed at hscrut
    injection hexp with h; subst h
    intro p hp; rcases List.mem_cons.mp hp with rfl | h2
    · rfl
    · rcases List.mem_cons.mp h2 with rfl | h3
      · simp [ltyListSinksAllowed, ltySinksAllowed, hscrut]
      · nomatch h3
  case result okTy errTy =>
    simp only [tySinksAllowed, Bool.and_eq_true] at hscrut
    injection hexp with h; subst h
    intro p hp; rcases List.mem_cons.mp hp with rfl | h2
    · simp [ltyListSinksAllowed, ltySinksAllowed, hscrut.1]
    · rcases List.mem_cons.mp h2 with rfl | h3
      · simp [ltyListSinksAllowed, ltySinksAllowed, hscrut.2]
      · nomatch h3
  case data dName =>
    cases hd : prog.findData? dName with
    | none => simp [hd] at hexp
    | some dDecl =>
      simp only [hd, Except.ok.injEq] at hexp; subst hexp
      simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hprog
      have hdOk := hprog.1.1.2 dDecl (List.mem_of_find?_eq_some hd)
      intro p hp
      rw [List.mem_map] at hp
      rcases hp with ⟨c, hcIn, rfl⟩
      have hcOk := hdOk c hcIn
      rw [ltyListSinksAllowed_iff] at hcOk ⊢
      intro l hl
      rw [List.mem_map] at hl
      rcases hl with ⟨f, hfIn, rfl⟩
      simpa using hcOk f hfIn

mutual
theorem checkExpr_sinksAllowed {prog : Program} {L : TagSet}
    (hprog : progSafeForNI prog L = true) :
    ∀ {env : TyEnv} {jenv : JoinEnv} {pc : TagSet} {inSpec : Bool} {e : Expr} {lty : LTy},
      tyEnvSinksAllowed L env = true →
      joinEnvSinksAllowed L jenv = true →
      exprSafeForNI L e = true →
      exprNoSpecCalls prog e = true →
      checkExpr prog env jenv pc inSpec e = .ok lty →
      ltySinksAllowed L lty = true
  | _, _, _, _, .lit v, _, _, _, hs, _, hchk =>
    checkLiteral_sinksAllowed hs hchk
  | env, _, _, _, .var name, _, henv, _, _, _, hchk => by
    unfold checkExpr at hchk
    cases hl : lookupTyEnv env name with
    | none => simp [hl] at hchk
    | some l => simp only [hl, Except.ok.injEq] at hchk; subst hchk; simp [lookupTyEnv_sinksAllowed henv hl]
  | _, _, _, _, .constRef name, _, _, _, _, _, hchk => by
    unfold checkExpr at hchk
    cases hc : prog.findConst? name with
    | none => simp [hc] at hchk
    | some cd =>
      simp only [hc, Except.ok.injEq] at hchk; subst hchk
      simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hprog
      simpa using (hprog.1.2 cd (List.mem_of_find?_eq_some hc)).1
  | env, jenv, pc, inSpec, .letE name declLTy bound body, _, henv, hjenv, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hb : checkExpr prog env [] pc inSpec bound with
    | error _ => simp [hb] at hchk
    | ok bLTy =>
      simp only [hb] at hchk
      split at hchk <;> try contradiction
      have henv' : tyEnvSinksAllowed L ((name, declLTy.addTags pc) :: env) = true := by
        unfold tyEnvSinksAllowed at henv ⊢
        simp [hs.1.1, henv]
      exact checkExpr_sinksAllowed hprog henv' hjenv hs.2 hns.2 hchk
  | env, jenv, pc, inSpec, .ifE cond tBr eBr, _, henv, hjenv, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hc : checkExpr prog env [] pc inSpec cond with
    | error _ => simp [hc] at hchk
    | ok cLTy =>
      simp only [hc] at hchk
      split at hchk <;> try contradiction
      cases ht : checkExpr prog env jenv (pc.union cLTy.tags) inSpec tBr with
      | error _ => simp [ht] at hchk
      | ok tLTy =>
        simp only [ht] at hchk
        cases he : checkExpr prog env jenv (pc.union cLTy.tags) inSpec eBr with
        | error _ => simp [he] at hchk
        | ok _ =>
          simp only [he] at hchk
          split at hchk <;> try contradiction
          injection hchk with h; subst h
          have htOk := checkExpr_sinksAllowed hprog henv hjenv hs.1.2 hns.1.2 ht
          cases tLTy; exact htOk
  | env, jenv, pc, inSpec, .caseE scrut arms, _, henv, hjenv, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hsc : checkExpr prog env [] pc inSpec scrut with
    | error _ => simp [hsc] at hchk
    | ok scrutLTy =>
      simp only [hsc] at hchk
      cases hsp : expectedCaseSpecs prog scrutLTy.ty scrutLTy.effectiveTags with
      | error _ => simp [hsp] at hchk
      | ok specs =>
        simp only [hsp] at hchk
        split at hchk <;> try contradiction
        cases ha : checkCaseArms prog env jenv (pc.union scrutLTy.effectiveTags) inSpec specs arms with
        | error _ => simp [ha] at hchk
        | ok armLTys =>
          simp only [ha] at hchk; try dsimp only at hchk
          cases armLTys with
          | nil => simp at hchk
          | cons firstLTy restLTys =>
            try dsimp only at hchk
            split at hchk <;> try contradiction
            injection hchk with h; subst h
            have hscrutOk := checkExpr_sinksAllowed (jenv := []) hprog henv rfl hs.1 hns.1 hsc
            have hspecsOk := expectedCaseSpecs_sinksAllowed hprog (by cases scrutLTy; exact hscrutOk) hsp
            have harmsOk := checkCaseArms_sinksAllowed hprog henv hjenv hspecsOk hs.2 hns.2 ha
            simp only [ltyListSinksAllowed, Bool.and_eq_true] at harmsOk
            cases firstLTy; exact harmsOk.1
  | _, _, _, _, .lam params _ retLTy _, _, _, _, hs, _, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    unfold checkExpr at hchk
    repeat (split at hchk <;> try contradiction)
    simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with h; subst h
    simp [ltySinksAllowed, tySinksAllowed, hs.1.1, hs.1.2]
  | env, _, pc, inSpec, .app fnExpr args, _, henv, _, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hf : checkExpr prog env [] pc inSpec fnExpr with
    | error _ => simp [hf] at hchk
    | ok fnLTy =>
      simp only [hf] at hchk
      cases ha : checkExprList prog env pc inSpec args with
      | error _ => simp [ha] at hchk
      | ok argLTys =>
        simp only [ha] at hchk
        have hfnOk := checkExpr_sinksAllowed (jenv := []) hprog henv rfl hs.1 hns.1 hf
        cases fnLTy with | mk fty fts =>
        dsimp only [LTy.ty, LTy.tags] at hchk
        cases fty <;> (try dsimp only at hchk) <;> try contradiction
        case fn paramLTys fnPc ret =>
          try simp only [] at hchk
          cases h1 : !(pc.union fts).subset fnPc <;>
            cases h2 : (argLTys.length != paramLTys.length) <;>
            cases h3 : !(argLTys.zip paramLTys).all (fun x => ltySubtype x.fst x.snd) <;>
            simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hchk <;>
            try contradiction
          rw [← hchk]
          simp only [ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hfnOk
          simpa using hfnOk.2
  | _, _, _, _, .call fnName _, _, _, _, _, hns, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    cases hf : prog.findFun? fnName with
    | none => simp [hf] at hchk
    | some fDecl =>
      simp only [hf] at hchk
      repeat (split at hchk <;> try contradiction)
      injection hchk with h; subst h
      simp only [exprNoSpecCalls, hf, Bool.and_eq_true, Bool.not_eq_true'] at hns
      simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hprog
      have hfd := hprog.2 fDecl (List.mem_of_find?_eq_some hf)
      simp only [hns.1, Bool.false_or, Bool.and_eq_true] at hfd
      simpa using hfd.1.1.2
  | env, jenv, pc, inSpec, .join label params rhs body, _, henv, hjenv, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    dsimp only at hchk
    let guess1 := pc.union (inferJumpPc prog label env pc body)
    let rhsEnv := extendTyEnv env params
    let joinPc := guess1.union (inferJumpPc prog label rhsEnv guess1 rhs)
    have hrhsEnvOk := extendTyEnv_sinksAllowed henv hs.1.1
    cases hinf : inferJoinRetLTy prog rhsEnv jenv joinPc label rhs body with
    | none => rw [hinf] at hchk; contradiction
    | some candRetLTy =>
      rw [hinf] at hchk
      have hcandOk : ltySinksAllowed L candRetLTy = true := by
        unfold inferJoinRetLTy at hinf
        cases h1 : inferBranchLTy prog rhsEnv jenv joinPc [label] rhs with
        | some l =>
          rw [h1] at hinf; injection hinf with h; subst h
          exact inferBranchLTy_sinksAllowed hprog hrhsEnvOk hjenv hs.1.2 hns.1 h1
        | none =>
          rw [h1] at hinf
          exact inferBranchLTy_sinksAllowed hprog hrhsEnvOk hjenv hs.2 hns.2 hinf
      dsimp only [bind, Except.bind] at hchk
      split at hchk <;> try contradiction
      cases hr : checkExpr prog rhsEnv _ joinPc inSpec rhs with
      | error _ => rw [hr] at hchk; contradiction
      | ok rLTy =>
        rw [hr] at hchk; dsimp only at hchk
        cases hb : checkExpr prog env _ pc inSpec body with
        | error _ => rw [hb] at hchk; contradiction
        | ok bLTy =>
          rw [hb] at hchk; dsimp only at hchk
          split at hchk <;> try contradiction
          split at hchk
          · injection hchk with h; subst h; simpa using hcandOk
          · cases hr2 : checkExpr prog rhsEnv _ joinPc inSpec rhs with
            | error _ => rw [hr2] at hchk; contradiction
            | ok _ =>
              rw [hr2] at hchk; dsimp only at hchk
              cases hb2 : checkExpr prog env _ pc inSpec body with
              | error _ => rw [hb2] at hchk; contradiction
              | ok _ =>
                rw [hb2] at hchk; dsimp only at hchk
                split at hchk <;> try contradiction
                injection hchk with h; subst h
                cases candRetLTy; exact hcandOk
  | _, jenv, _, _, .jump label _, _, _, hjenv, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    cases hj : lookupJoinEnv jenv label with
    | none => simp [hj] at hchk
    | some sig =>
      simp only [hj] at hchk
      repeat (split at hchk <;> try contradiction)
      injection hchk with h; subst h
      induction jenv with
      | nil => simp [lookupJoinEnv] at hj
      | cons hd tl ih =>
        simp only [joinEnvSinksAllowed, List.all_cons, Bool.and_eq_true] at hjenv
        simp only [lookupJoinEnv] at hj
        split at hj
        · injection hj with h; subst h; exact hjenv.1.2
        · exact ih hjenv.2 hj
  | env, _, pc, inSpec, .tuple elems, _, henv, _, hs, hns, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec elems with
    | error _ => simp [ha] at hchk
    | ok elemLTys =>
      simp only [ha, Except.ok.injEq] at hchk; subst hchk
      exact checkExprList_sinksAllowed hprog henv hs hns ha
  | env, _, pc, inSpec, .proj tup idx, _, henv, _, hs, hns, hchk => by
    have hsTup : exprSafeForNI L tup = true := hs
    have hnsTup : exprNoSpecCalls prog tup = true := hns
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ht : checkExpr prog env [] pc inSpec tup with
    | error _ => simp [ht] at hchk
    | ok tupLTy =>
      simp only [ht] at hchk
      have htOk := checkExpr_sinksAllowed (jenv := []) hprog henv rfl hsTup hnsTup ht
      cases tupLTy with | mk tty tts =>
      dsimp only [LTy.ty, LTy.tags] at hchk
      cases tty <;> (try dsimp only at hchk) <;> try contradiction
      case tuple elemLTys =>
        cases hg : elemLTys[idx]? with
        | none => rw [hg] at hchk; contradiction
        | some eLTy =>
          rw [hg] at hchk; injection hchk with h; subst h
          simp only [ltySinksAllowed, tySinksAllowed] at htOk
          rw [ltyListSinksAllowed_iff] at htOk
          simpa using htOk eLTy (List.mem_of_getElem? hg)
  | _, _, _, _, .ctor _ _ _, _, _, _, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h; rfl
  | _, _, _, _, .tableLit _ _, _, _, _, _, _, hchk => by
    unfold checkExpr at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h; rfl
  | env, _, pc, inSpec, .prim op args, _, henv, _, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args with
    | error _ => simp [ha] at hchk
    | ok argLTys =>
      simp only [ha] at hchk
      exact checkPrimOp_sinksAllowed hs.1 (checkExprList_sinksAllowed hprog henv hs.2 hns ha) hchk
  | env, _, pc, inSpec, .rel plan, _, _, _, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hp : checkPlan prog env pc inSpec plan with
    | error _ => simp [hp] at hchk
    | ok pTy =>
      simp only [hp, Except.ok.injEq] at hchk; subst hchk
      exact PlanTy.ltySinksAllowed_toLTy L pc pTy
  | env, _, pc, inSpec, .host op args, _, henv, _, hs, hns, hchk => by
    simp only [exprSafeForNI, Bool.and_eq_true] at hs
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args with
    | error _ => simp [ha] at hchk
    | ok argLTys =>
      simp only [ha] at hchk
      exact checkHostOp_sinksAllowed hs.1 (checkExprList_sinksAllowed hprog henv hs.2 hns ha) hchk
  | env, _, pc, inSpec, .stop _ detail, _, _, _, _, _, hchk => by
    unfold checkExpr at hchk
    cases detail with
    | none => injection hchk with h; subst h; rfl
    | some d =>
      dsimp only at hchk
      split at hchk <;> try contradiction
      simp only [bind, Except.bind] at hchk
      cases hd : checkExpr prog env [] pc inSpec d with
      | error _ => simp [hd] at hchk
      | ok _ =>
        simp only [hd] at hchk
        split at hchk <;> try contradiction
        injection hchk with h; subst h; rfl
  | env, _, pc, inSpec, .fail msg, _, _, _, _, _, hchk => by
    unfold checkExpr at hchk
    repeat (split at hchk <;> try contradiction)
    simp only [bind, Except.bind] at hchk
    cases hm : checkExpr prog env [] pc inSpec msg with
    | error _ => simp [hm] at hchk
    | ok _ =>
      simp only [hm] at hchk
      split at hchk <;> try contradiction
      injection hchk with h; subst h; rfl

theorem checkExprList_sinksAllowed {prog : Program} {L : TagSet}
    (hprog : progSafeForNI prog L = true) :
    ∀ {env : TyEnv} {pc : TagSet} {inSpec : Bool} {es : List Expr} {ltys : List LTy},
      tyEnvSinksAllowed L env = true →
      exprListSafeForNI L es = true →
      exprListNoSpecCalls prog es = true →
      checkExprList prog env pc inSpec es = .ok ltys →
      ltyListSinksAllowed L ltys = true
  | _, _, _, [], _, _, _, _, hchk => by
    injection hchk with h; subst h; rfl
  | env, pc, inSpec, e :: rest, _, henv, hs, hns, hchk => by
    simp only [exprListSafeForNI, Bool.and_eq_true] at hs
    simp only [exprListNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExprList at hchk; simp only [bind, Except.bind] at hchk
    cases hh : checkExpr prog env [] pc inSpec e with
    | error _ => simp [hh] at hchk
    | ok hd =>
      simp only [hh] at hchk
      cases ht : checkExprList prog env pc inSpec rest with
      | error _ => simp [ht] at hchk
      | ok tl =>
        simp only [ht, Except.ok.injEq] at hchk; subst hchk
        simp [ltyListSinksAllowed,
          checkExpr_sinksAllowed (jenv := []) hprog henv rfl hs.1 hns.1 hh,
          checkExprList_sinksAllowed hprog henv hs.2 hns.2 ht]

theorem checkCaseArms_sinksAllowed {prog : Program} {L : TagSet}
    (hprog : progSafeForNI prog L = true) :
    ∀ {env : TyEnv} {jenv : JoinEnv} {armPc : TagSet} {inSpec : Bool}
      {specs : List (Ident × List LTy)} {arms : List CaseArm} {ltys : List LTy},
      tyEnvSinksAllowed L env = true →
      joinEnvSinksAllowed L jenv = true →
      (∀ p ∈ specs, ltyListSinksAllowed L p.2 = true) →
      caseArmsSafeForNI L arms = true →
      caseArmsNoSpecCalls prog arms = true →
      checkCaseArms prog env jenv armPc inSpec specs arms = .ok ltys →
      ltyListSinksAllowed L ltys = true
  | _, _, _, _, _, [], _, _, _, _, _, _, hchk => by
    injection hchk with h; subst h; rfl
  | env, jenv, armPc, inSpec, specs, .mk cName binders body :: rest, _, henv, hjenv, hspecs, hs, hns, hchk => by
    simp only [caseArmsSafeForNI, Bool.and_eq_true] at hs
    simp only [caseArmsNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkCaseArms at hchk
    cases hf : specs.find? (fun (sn, _) => sn == cName) with
    | none => simp [hf] at hchk
    | some pair =>
      rcases pair with ⟨_, fieldLTys⟩
      simp only [hf] at hchk
      split at hchk <;> try contradiction
      simp only [bind, Except.bind] at hchk
      have hfOk := hspecs _ (List.mem_of_find?_eq_some hf)
      have harmBindOk : ltyListSinksAllowed L ((List.zip binders (fieldLTys.map (fun f => f.addTags armPc))).map Prod.snd) = true := by
        rw [ltyListSinksAllowed_iff] at hfOk ⊢
        intro l hl
        rw [List.mem_map] at hl; rcases hl with ⟨⟨_, l'⟩, hmemZ, rfl⟩
        have hmemMap := List.of_mem_zip hmemZ |>.2
        rw [List.mem_map] at hmemMap; rcases hmemMap with ⟨orig, horig, rfl⟩
        simpa using hfOk orig horig
      have harmEnvOk := extendTyEnv_sinksAllowed henv harmBindOk
      cases hh : checkExpr prog (extendTyEnv env (List.zip binders (fieldLTys.map (fun f => f.addTags armPc)))) jenv armPc inSpec body with
      | error _ => simp [hh] at hchk
      | ok hd =>
        simp only [hh] at hchk
        cases ht : checkCaseArms prog env jenv armPc inSpec specs rest with
        | error _ => simp [ht] at hchk
        | ok tl =>
          simp only [ht, Except.ok.injEq] at hchk; subst hchk
          simp [ltyListSinksAllowed,
            checkExpr_sinksAllowed hprog harmEnvOk hjenv hs.1 hns.1 hh,
            checkCaseArms_sinksAllowed hprog henv hjenv hspecs hs.2 hns.2 ht]
end

/-! ## Confinement Theorem (`pc ⊈ L → w' = w`) -/

mutual
theorem sortableVal_safeForNI (L : TagSet) :
    ∀ {v : Val}, SortableVal v → valSafeForNI L v = true
  | _, .optNone | _, .unit | _, .bool _ | _, .int _ | _, .decimal _ | _, .float _
  | _, .text _ | _, .bytes _ | _, .date _ | _, .timestamp _ | _, .duration _
  | _, .linearModel _ _ _ | _, .statTest _ _ => by simp [valSafeForNI]
  | _, .optSome hv => by simp [valSafeForNI, sortableVal_safeForNI L hv]
  | _, .resOk hv => by simp [valSafeForNI, sortableVal_safeForNI L hv]
  | _, .resErr hv => by simp [valSafeForNI, sortableVal_safeForNI L hv]
  | _, .tuple hvs => by simp [valSafeForNI, sortableValList_safeForNI L hvs]
  | _, .list hvs => by simp [valSafeForNI, sortableValList_safeForNI L hvs]
  | _, .ctor _ _ hfs => by simp [valSafeForNI, sortableValList_safeForNI L hfs]

theorem sortableValList_safeForNI (L : TagSet) :
    ∀ {vs : List Val}, SortableValList vs → valListSafeForNI L vs = true
  | [], .nil => by simp [valListSafeForNI]
  | _ :: _, .cons hv hvs => by
    simp [valListSafeForNI, sortableVal_safeForNI L hv, sortableValList_safeForNI L hvs]
end

theorem valWf_scalar_safeForNI {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) {sTy : ScalarTy} {v : Val}
    (hv : ValWf prog v sTy.toTy) : valSafeForNI L v = true :=
  sortableVal_safeForNI L (valWf_sortable hd hv (ScalarTy.isSortable_toTy sTy))


theorem flattenValLists_safeForNI {L : TagSet} :
    ∀ {nested flat : List Val},
      valListSafeForNI L nested = true →
      flattenValLists nested = some flat →
      valListSafeForNI L flat = true
  | [], _, _, hf => by injection hf with h; subst h; simp [valListSafeForNI]
  | .list xs :: rest, _, hsafe, hf => by
    simp only [valListSafeForNI, valSafeForNI, Bool.and_eq_true] at hsafe
    simp only [flattenValLists, Option.map_eq_some_iff] at hf
    rcases hf with ⟨tl, htl, rfl⟩
    have htlSafe := flattenValLists_safeForNI hsafe.2 htl
    rw [valListSafeForNI_iff] at hsafe htlSafe ⊢
    intro v hv
    rcases List.mem_append.mp hv with h1 | h2
    · exact hsafe.1 v h1
    · exact htlSafe v h2

theorem buildPairs_safeForNI {L : TagSet} :
    ∀ {kvArgs : List Val} {pairs : List (Val × Val)},
      valListSafeForNI L kvArgs = true →
      buildPairs kvArgs = some pairs →
      valPairsSafeForNI L pairs = true
  | [], _, _, hb => by injection hb with h; subst h; simp [valPairsSafeForNI]
  | [_], _, _, hb => nomatch hb
  | k :: v :: rest, _, hsafe, hb => by
    simp only [valListSafeForNI, Bool.and_eq_true] at hsafe
    simp only [buildPairs, Option.map_eq_some_iff] at hb
    rcases hb with ⟨tl, htl, rfl⟩
    simp [valPairsSafeForNI, hsafe.1, hsafe.2.1, buildPairs_safeForNI hsafe.2.2 htl]

private theorem valPairsSafeForNI_snd {L : TagSet} :
    ∀ {pairs : List (Val × Val)}, valPairsSafeForNI L pairs = true →
      ∀ p ∈ pairs, valSafeForNI L p.2 = true
  | [], _, _, hm => nomatch hm
  | _ :: tl, hp, p, hpMem => by
    simp only [valPairsSafeForNI, Bool.and_eq_true] at hp
    rcases List.mem_cons.mp hpMem with rfl | htl
    · exact hp.1.2
    · exact valPairsSafeForNI_snd hp.2 p htl

private theorem valListSafeForNI_append_one {L : TagSet} {elems : List Val} {item : Val}
    (he : valListSafeForNI L elems = true) (hi : valSafeForNI L item = true) :
    valListSafeForNI L (elems ++ [item]) = true := by
  rw [valListSafeForNI_iff] at he ⊢
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact he x h1
  · simp at h2; subst h2; exact hi

theorem evalPrimOp_safeForNI {L : TagSet} {op : PrimOp} {vs : List Val} {v : Val}
    (hsafe : valListSafeForNI L vs = true)
    (hev : evalPrimOp op vs = .ok v) :
    valSafeForNI L v = true := by
  unfold evalPrimOp at hev
  split at hev
  all_goals (try simp only [valListSafeForNI, valSafeForNI, Bool.and_eq_true] at hsafe)
  all_goals (
    repeat (
      (try simp only [] at hev)
      first
      | contradiction
      | (injection hev with h; rw [← h])
      | (simp only [checkedInt, checkedDecimal] at hev; split at hev <;> try contradiction)
      | (split at hev <;> try contradiction)
    )
  )
  all_goals ((try simp only [] at hev); try (injection hev with h; rw [← h]))
  all_goals (try simp only [valSafeForNI])
  all_goals (
    first
    | rfl
    | trivial
    | exact hsafe
    | exact hsafe.1
    | exact hsafe.2.1
    | exact valListSafeForNI_append_one hsafe.1 hsafe.2.1
    | exact flattenValLists_safeForNI hsafe.1 ‹flattenValLists _ = some _›
    | exact buildPairs_safeForNI hsafe ‹buildPairs _ = some _›
    | exact valPairsSafeForNI_snd hsafe.1 _ (List.mem_of_find?_eq_some ‹List.find? _ _ = some _›)
  )

def outcomeWorldEq (w : World) : Outcome → Prop
  | .ok _ w' | .stopped _ w' | .failed _ w' | .jumped _ _ w' => w' = w
  | .wrong | .outOfFuel => True

def outcomeValSafe (L : TagSet) : Outcome → Prop
  | .ok v _ => valSafeForNI L v = true
  | .jumped _ vs _ => valListSafeForNI L vs = true
  | _ => True

private theorem checkedInt_valSafe {L : TagSet} {n : Int} {v : Val}
    (h : checkedInt n = .ok v) : valSafeForNI L v = true := by
  unfold checkedInt at h
  split at h
  · injection h with h; rw [← h]; rfl
  · nomatch h

private theorem evalHostOp_valSafe {prog : Program} {L : TagSet} {op : HostOp}
    {args : List Val} {w : World}
    (hargSafe : valListSafeForNI L args = true) :
    outcomeValSafe L (evalHostOp prog op args w) := by
  unfold evalHostOp
  split
  · simp only [outcomeValSafe, valSafeForNI]
    rw [valListSafeForNI_iff]
    intro v hv; rw [List.mem_map] at hv; rcases hv with ⟨_, _, rfl⟩; rfl
  all_goals (try simp only [valListSafeForNI, Bool.and_eq_true] at hargSafe)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals (try simp only [outcomeValSafe, valSafeForNI])
  all_goals (first | rfl | trivial | exact hargSafe.2.1 | exact checkedInt_valSafe ‹_›)

private theorem pc_not_subset_allows {pc allows L : TagSet}
    (ha : allows.subset L = true) (hpcF : pc.subset L = false) :
    pc.subset allows = false := by
  cases h : pc.subset allows
  · rfl
  · have := TagSet.subset_trans h ha; rw [hpcF] at this; nomatch this

theorem evalHostOp_safe_and_confined {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {op : HostOp} {argLTys : List LTy} {args : List Val} {lty : LTy} {w : World}
    (hsafeOp : hostOpSafeForNI L op = true)
    (hargSinks : ltyListSinksAllowed L argLTys = true)
    (hargSafe : valListSafeForNI L args = true)
    (hchk : checkHostOp prog pc inSpec op argLTys = .ok lty) :
    outcomeValSafe L (evalHostOp prog op args w) ∧
    (pc.subset L = false → outcomeWorldEq w (evalHostOp prog op args w)) := by
  refine ⟨evalHostOp_valSafe hargSafe, ?_⟩
  intro hpcF
  unfold evalHostOp
  split
  all_goals (try (simp [hostOpSafeForNI] at hsafeOp))
  all_goals (
    first
    | rfl
    | trivial
    | (exfalso
       unfold checkHostOp at hchk
       split at hchk <;> try contradiction
       simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
       simp only [bind, Except.bind] at hchk
       (try (split at hchk <;> try contradiction))
       (try simp only [] at hchk)
       simp only [TagSet.union_subset_iff, pc_not_subset_allows hargSinks.1 hpcF,
         Bool.false_and, Bool.not_false] at hchk
       (try simp only [Bool.false_eq_true, ↓reduceIte] at hchk)
       (try (split at hchk <;> try contradiction))
       contradiction)
    | skip
  )
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals (first | rfl | trivial)

mutual
def valNoSpecCalls (prog : Program) : Val → Bool
  | .optSome v | .resOk v | .resErr v => valNoSpecCalls prog v
  | .tuple vs | .list vs | .ctor _ _ vs => valListNoSpecCalls prog vs
  | .map kvs => valPairsNoSpecCalls prog kvs
  | .closure _ _ _ body capEnv =>
    exprNoSpecCalls prog body && envNoSpecCalls prog capEnv
  | _ => true
  termination_by structural v => v

def valListNoSpecCalls (prog : Program) : List Val → Bool
  | [] => true
  | v :: vs => valNoSpecCalls prog v && valListNoSpecCalls prog vs
  termination_by structural vs => vs

def valPairsNoSpecCalls (prog : Program) : List (Val × Val) → Bool
  | [] => true
  | (k, v) :: rest => valNoSpecCalls prog k && valNoSpecCalls prog v && valPairsNoSpecCalls prog rest
  termination_by structural ps => ps

def envNoSpecCalls (prog : Program) : List EnvEntry → Bool
  | [] => true
  | .mk _ _ v :: rest => valNoSpecCalls prog v && envNoSpecCalls prog rest
  termination_by structural es => es
end

def outcomeNoSpecCalls (prog : Program) : Outcome → Prop
  | .ok v _ => valNoSpecCalls prog v = true
  | .jumped _ vs _ => valListNoSpecCalls prog vs = true
  | _ => True

private theorem valListNoSpecCalls_iff {prog : Program} {vs : List Val} :
    valListNoSpecCalls prog vs = true ↔ ∀ v ∈ vs, valNoSpecCalls prog v = true := by
  induction vs with
  | nil => simp [valListNoSpecCalls]
  | cons v rest ih => simp [valListNoSpecCalls, Bool.and_eq_true, ih]

private theorem valListNoSpecCalls_append {prog : Program} :
    ∀ {xs ys : List Val},
      valListNoSpecCalls prog xs = true → valListNoSpecCalls prog ys = true →
      valListNoSpecCalls prog (xs ++ ys) = true
  | [], _, _, hy => hy
  | _ :: _, _, hx, hy => by
    simp only [valListNoSpecCalls, Bool.and_eq_true] at hx
    simp [valListNoSpecCalls, hx.1, valListNoSpecCalls_append hx.2 hy]

private theorem envNoSpecCalls_append {prog : Program} :
    ∀ {a b : Env}, envNoSpecCalls prog a = true → envNoSpecCalls prog b = true →
      envNoSpecCalls prog (a ++ b) = true
  | [], _, _, hb => hb
  | .mk _ _ _ :: _, _, ha, hb => by
    simp only [envNoSpecCalls, Bool.and_eq_true] at ha
    simp [envNoSpecCalls, ha.1, envNoSpecCalls_append ha.2 hb]

private theorem envNoSpecCalls_reverse {prog : Program} :
    ∀ {env : Env}, envNoSpecCalls prog env = true → envNoSpecCalls prog env.reverse = true
  | [], _ => rfl
  | .mk _ _ _ :: _, h => by
    simp only [envNoSpecCalls, Bool.and_eq_true] at h
    rw [List.reverse_cons]
    exact envNoSpecCalls_append (envNoSpecCalls_reverse h.2) (by simp [envNoSpecCalls, h.1])

private theorem extendEnv_noSpecCalls {prog : Program} :
    ∀ {params : List (Ident × LTy)} {vs : List Val} {base : Env},
      valListNoSpecCalls prog vs = true → envNoSpecCalls prog base = true →
      envNoSpecCalls prog ((List.zip params vs).map (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v }) ++ base) = true
  | [], _, base, _, hbase => hbase
  | _ :: _, [], base, _, hbase => hbase
  | (_, _) :: ps, v :: vs, base, hv, hbase => by
    simp only [valListNoSpecCalls, Bool.and_eq_true] at hv
    simp [List.zip_cons_cons, envNoSpecCalls, hv.1, extendEnv_noSpecCalls hv.2 hbase]

private theorem lookupEnv_noSpecCalls {prog : Program} :
    ∀ {env : Env} {name : Ident} {lty : LTy} {v : Val},
      envNoSpecCalls prog env = true → lookupEnv env name = some (lty, v) →
      valNoSpecCalls prog v = true
  | [], _, _, _, _, hl => nomatch hl
  | .mk _ _ _ :: _, _, _, _, henv, hl => by
    simp only [envNoSpecCalls, Bool.and_eq_true] at henv
    simp only [lookupEnv] at hl
    split at hl
    · injection hl with h; injection h with _ h2; subst h2; exact henv.1
    · exact lookupEnv_noSpecCalls henv.2 hl

private theorem flattenValLists_noSpecCalls {prog : Program} :
    ∀ {nested flat : List Val},
      valListNoSpecCalls prog nested = true → flattenValLists nested = some flat →
      valListNoSpecCalls prog flat = true
  | [], _, _, hf => by injection hf with h; subst h; rfl
  | x :: _, _, hx, hf => by
    simp only [valListNoSpecCalls, Bool.and_eq_true] at hx
    cases x <;> try contradiction
    simp only [flattenValLists, Option.map_eq_some_iff] at hf
    rcases hf with ⟨tl, htl, rfl⟩
    exact valListNoSpecCalls_append hx.1 (flattenValLists_noSpecCalls hx.2 htl)

private theorem buildPairs_noSpecCalls {prog : Program} :
    ∀ {args : List Val} {ps : List (Val × Val)},
      valListNoSpecCalls prog args = true → buildPairs args = some ps →
      valPairsNoSpecCalls prog ps = true
  | [], _, _, hb => by injection hb with h; subst h; rfl
  | [_], _, _, hb => nomatch hb
  | _ :: _ :: _, _, h, hb => by
    simp only [valListNoSpecCalls, Bool.and_eq_true] at h
    simp only [buildPairs, Option.map_eq_some_iff] at hb
    rcases hb with ⟨tl, htl, rfl⟩
    simp [valPairsNoSpecCalls, h.1, h.2.1, buildPairs_noSpecCalls h.2.2 htl]

private theorem valPairsNoSpecCalls_snd {prog : Program} :
    ∀ {ps : List (Val × Val)}, valPairsNoSpecCalls prog ps = true →
      ∀ p ∈ ps, valNoSpecCalls prog p.2 = true
  | [], _, _, hm => nomatch hm
  | (_, _) :: _, h, _, hm => by
    simp only [valPairsNoSpecCalls, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | hrest
    · exact h.1.2
    · exact valPairsNoSpecCalls_snd h.2 _ hrest

private theorem evalPrimOp_noSpecCalls {prog : Program} {op : PrimOp} {vs : List Val} {v : Val}
    (hns : valListNoSpecCalls prog vs = true) (hev : evalPrimOp op vs = .ok v) :
    valNoSpecCalls prog v = true := by
  unfold evalPrimOp at hev
  split at hev
  all_goals (try simp only [valListNoSpecCalls, valNoSpecCalls, Bool.and_eq_true] at hns)
  all_goals (
    repeat (
      (try simp only [] at hev)
      first
      | contradiction
      | (injection hev with h; rw [← h])
      | (simp only [checkedInt, checkedDecimal] at hev; split at hev <;> try contradiction)
      | (split at hev <;> try contradiction)
    )
  )
  all_goals ((try simp only [] at hev); try (injection hev with h; rw [← h]))
  all_goals (try simp only [valNoSpecCalls])
  all_goals (
    first
    | rfl
    | trivial
    | exact hns
    | exact hns.1
    | exact hns.2.1
    | exact valListNoSpecCalls_append hns.1 (by simp [valListNoSpecCalls, hns.2.1])
    | exact flattenValLists_noSpecCalls hns.1 ‹flattenValLists _ = some _›
    | exact buildPairs_noSpecCalls hns ‹buildPairs _ = some _›
    | exact valPairsNoSpecCalls_snd hns.1 _ (List.mem_of_find?_eq_some ‹List.find? _ _ = some _›)
  )

private theorem checkedInt_noSpecCalls {prog : Program} {n : Int} {v : Val}
    (h : checkedInt n = .ok v) : valNoSpecCalls prog v = true := by
  unfold checkedInt at h; split at h
  · injection h with h; rw [← h]; rfl
  · nomatch h

private theorem evalHostOp_noSpecCalls {prog : Program} {op : HostOp}
    {args : List Val} {w : World}
    (hns : valListNoSpecCalls prog args = true) :
    outcomeNoSpecCalls prog (evalHostOp prog op args w) := by
  unfold evalHostOp
  split
  · simp only [outcomeNoSpecCalls, valNoSpecCalls]
    rw [valListNoSpecCalls_iff]
    intro v hv; rw [List.mem_map] at hv; rcases hv with ⟨_, _, rfl⟩; rfl
  all_goals (try simp only [valListNoSpecCalls, Bool.and_eq_true] at hns)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals ((try simp only []); try split)
  all_goals (try simp only [outcomeNoSpecCalls, valNoSpecCalls])
  all_goals (first | rfl | trivial | exact hns.2.1 | exact checkedInt_noSpecCalls ‹_›)

private theorem matchCaseVal_noSpecCalls {prog : Program} {armPc : TagSet}
    {sVal : Val} {scrutLTy : LTy} {cName : Ident} {typedVals : List (LTy × Val)}
    (hsNs : valNoSpecCalls prog sVal = true)
    (hm : matchCaseVal prog sVal scrutLTy armPc = some (cName, typedVals)) :
    ∀ tv ∈ typedVals, valNoSpecCalls prog tv.2 = true := by
  unfold matchCaseVal at hm
  cases scrutLTy with | mk sty sts =>
  dsimp only [LTy.ty] at hm
  cases sty <;> cases sVal <;> (try simp only at hm) <;> try contradiction
  case bool.bool b =>
    cases b <;> injection hm with h <;> injection h with _ h2 <;> subst h2 <;> intro _ hm0 <;> nomatch hm0
  case option.optNone =>
    injection hm with h; injection h with _ h2; subst h2; intro _ hm0; nomatch hm0
  case option.optSome inner u =>
    injection hm with h; injection h with _ h2; subst h2
    intro tv htv; simp only [List.mem_singleton] at htv; subst htv; exact hsNs
  case result.resOk okTy errTy u =>
    injection hm with h; injection h with _ h2; subst h2
    intro tv htv; simp only [List.mem_singleton] at htv; subst htv; exact hsNs
  case result.resErr okTy errTy e =>
    injection hm with h; injection h with _ h2; subst h2
    intro tv htv; simp only [List.mem_singleton] at htv; subst htv; exact hsNs
  case data.ctor dName vType cn fields =>
    split at hm; nomatch hm
    cases hd : prog.findData? dName with
    | none => rw [hd] at hm; nomatch hm
    | some dDecl =>
      rw [hd] at hm; dsimp only at hm
      cases hc : dDecl.ctors.find? (fun c => c.name == cn) with
      | none => rw [hc] at hm; nomatch hm
      | some cDecl =>
        rw [hc] at hm; dsimp only at hm
        split at hm <;> try contradiction
        injection hm with h; injection h with _ h2; subst h2
        simp only [valNoSpecCalls] at hsNs; rw [valListNoSpecCalls_iff] at hsNs
        intro tv htv; exact hsNs tv.2 (List.of_mem_zip htv).2

theorem evalSeq_safe_and_confined {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {env : Env} (step : World → Expr → Outcome)
    (hstep : ∀ w e lty,
      WorldWf prog w →
      exprSafeForNI L e = true →
      exprNoSpecCalls prog e = true →
      checkExpr prog (envToTyEnv env) [] pc inSpec e = .ok lty →
      OutcomeWf prog [] lty.ty (step w e) ∧
      outcomeValSafe L (step w e) ∧
      outcomeNoSpecCalls prog (step w e) ∧
      (pc.subset L = false → outcomeWorldEq w (step w e))) :
    ∀ {es : List Expr} {ltys : List LTy} {w : World},
      WorldWf prog w →
      exprListSafeForNI L es = true →
      exprListNoSpecCalls prog es = true →
      checkExprList prog (envToTyEnv env) pc inSpec es = .ok ltys →
      match evalSeq step w es with
      | .ok vs w' => valListSafeForNI L vs = true ∧ valListNoSpecCalls prog vs = true ∧ WorldWf prog w' ∧ (pc.subset L = false → w' = w)
      | .aborted out => outcomeValSafe L out ∧ outcomeNoSpecCalls prog out ∧ (pc.subset L = false → outcomeWorldEq w out)
  | [], _, w, hw, _, _, _ => ⟨rfl, rfl, hw, fun _ => rfl⟩
  | e :: rest, _, w, hw, hs, hns, hchk => by
    simp only [exprListSafeForNI, Bool.and_eq_true] at hs
    simp only [exprListNoSpecCalls, Bool.and_eq_true] at hns
    unfold checkExprList at hchk; simp only [bind, Except.bind] at hchk
    cases hh : checkExpr prog (envToTyEnv env) [] pc inSpec e with
    | error _ => simp [hh] at hchk
    | ok hdLTy =>
      simp only [hh] at hchk
      cases ht : checkExprList prog (envToTyEnv env) pc inSpec rest with
      | error _ => simp [ht] at hchk
      | ok tlLTys =>
        rcases hstep w e hdLTy hw hs.1 hns.1 hh with ⟨houtWf, houtSafe, houtNs, houtConf⟩
        simp only [evalSeq]
        cases hsOut : step w e with
        | stopped b w1 | failed b w1 | jumped b _ w1 | wrong | outOfFuel =>
          dsimp only
          rw [hsOut] at houtSafe houtNs houtConf
          exact ⟨houtSafe, houtNs, houtConf⟩
        | ok v w1 =>
          dsimp only
          rw [hsOut] at houtWf houtSafe houtNs houtConf
          dsimp only [outcomeValSafe, outcomeNoSpecCalls, outcomeWorldEq] at houtSafe houtNs houtConf
          cases houtWf with | ok _ hw1 =>
          have ih := evalSeq_safe_and_confined step hstep hw1 hs.2 hns.2 ht
          cases hrestOut : evalSeq step w1 rest with
          | aborted out =>
            dsimp only
            rw [hrestOut] at ih; dsimp only at ih
            refine ⟨ih.1, ih.2.1, fun hpcF => ?_⟩
            have hw1Eq : w1 = w := houtConf hpcF
            subst hw1Eq
            exact ih.2.2 hpcF
          | ok vs w2 =>
            dsimp only
            rw [hrestOut] at ih; dsimp only at ih
            refine ⟨by simp [valListSafeForNI, houtSafe, ih.1], by simp [valListNoSpecCalls, houtNs, ih.2.1], ih.2.2.1, fun hpcF => ?_⟩
            exact (ih.2.2.2 hpcF).trans (houtConf hpcF)

theorem extendEnv_safeForNI {L : TagSet} :
    ∀ {params : List (Ident × LTy)} {vs : List Val} {base : Env},
      ltyListSinksAllowed L (params.map Prod.snd) = true →
      valListSafeForNI L vs = true →
      envSafeForNI L base = true →
      envSafeForNI L ((List.zip params vs).map (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v }) ++ base) = true
  | [], _, base, _, _, hbase => hbase
  | _ :: _, [], base, _, _, hbase => hbase
  | (_, pLTy) :: ps, v :: vs, base, hp, hv, hbase => by
    simp only [List.map_cons, ltyListSinksAllowed, Bool.and_eq_true] at hp
    simp only [valListSafeForNI, Bool.and_eq_true] at hv
    simp [List.zip_cons_cons, envSafeForNI, hp.1, hv.1, extendEnv_safeForNI hp.2 hv.2 hbase]

theorem envSafeForNI_append {L : TagSet} :
    ∀ {a b : Env}, envSafeForNI L a = true → envSafeForNI L b = true → envSafeForNI L (a ++ b) = true
  | [], _, _, hb => hb
  | .mk _ _ _ :: _, _, ha, hb => by
    simp only [envSafeForNI, Bool.and_eq_true] at ha
    simp [envSafeForNI, ha.1.1, ha.1.2, envSafeForNI_append ha.2 hb]

theorem envSafeForNI_reverse {L : TagSet} :
    ∀ {env : Env}, envSafeForNI L env = true → envSafeForNI L env.reverse = true
  | [], _ => rfl
  | .mk _ _ _ :: _, h => by
    simp only [envSafeForNI, Bool.and_eq_true] at h
    rw [List.reverse_cons]
    exact envSafeForNI_append (envSafeForNI_reverse h.2) (by simp [envSafeForNI, h.1.1, h.1.2])

theorem callEnv_props {prog : Program} {L : TagSet} {params : List (Ident × LTy)} {vs : List Val}
    (hlen : vs.length = params.length)
    (hvs : ValListWf prog vs (params.map Prod.snd))
    (hpOk : ltyListSinksAllowed L (params.map Prod.snd) = true)
    (hvOk : valListSafeForNI L vs = true) :
    let callEnv : Env := (List.zip params vs).reverse.map
      (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })
    EnvWf prog callEnv ∧ envSafeForNI L callEnv = true ∧ envToTyEnv callEnv = params.reverse := by
  dsimp only
  have h1 : EnvWf prog ((List.zip params vs).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) := by
    simpa using extendEnv_wf hvs (.nil : EnvWf prog [])
  have h2 : envSafeForNI L ((List.zip params vs).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) = true := by
    simpa using extendEnv_safeForNI hpOk hvOk (rfl : envSafeForNI L [] = true)
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_reverse]; exact h1.reverse
  · rw [List.map_reverse]; exact envSafeForNI_reverse h2
  · have h3 := congrArg List.reverse (envToTyEnv_zip_params params vs hlen)
    simp only [envToTyEnv, ← List.map_reverse] at h3 ⊢
    exact h3

theorem matchCaseVal_safeForNI {prog : Program} {L armPc : TagSet} {sVal : Val} {scrutLTy : LTy}
    {cName : Ident} {typedVals : List (LTy × Val)}
    (hprog : progSafeForNI prog L = true)
    (hscrutSink : ltySinksAllowed L scrutLTy = true)
    (hsValSafe : valSafeForNI L sVal = true)
    (hm : matchCaseVal prog sVal scrutLTy armPc = some (cName, typedVals)) :
    ∀ tv ∈ typedVals, ltySinksAllowed L tv.1 = true ∧ valSafeForNI L tv.2 = true := by
  unfold matchCaseVal at hm
  cases scrutLTy with | mk sty sts =>
  dsimp only [LTy.ty] at hm
  cases sty <;> cases sVal <;> (try simp only at hm) <;> try contradiction
  case bool.bool b =>
    cases b <;> injection hm with h <;> injection h with _ h2 <;> subst h2 <;> intro _ hm0 <;> nomatch hm0
  case option.optNone =>
    injection hm with h; injection h with _ h2; subst h2; intro _ hm0; nomatch hm0
  case option.optSome inner u =>
    injection hm with h; injection h with _ h2; subst h2
    intro tv htv; simp only [List.mem_singleton] at htv; subst htv
    exact ⟨hscrutSink, hsValSafe⟩
  case result.resOk okTy errTy u =>
    simp only [ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hscrutSink
    injection hm with h; injection h with _ h2; subst h2
    intro tv htv; simp only [List.mem_singleton] at htv; subst htv
    exact ⟨hscrutSink.1, hsValSafe⟩
  case result.resErr okTy errTy e =>
    simp only [ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hscrutSink
    injection hm with h; injection h with _ h2; subst h2
    intro tv htv; simp only [List.mem_singleton] at htv; subst htv
    exact ⟨hscrutSink.2, hsValSafe⟩
  case data.ctor dName vType cn fields =>
    split at hm; nomatch hm
    cases hd : prog.findData? dName with
    | none => rw [hd] at hm; nomatch hm
    | some dDecl =>
      rw [hd] at hm; dsimp only at hm
      cases hc : dDecl.ctors.find? (fun c => c.name == cn) with
      | none => rw [hc] at hm; nomatch hm
      | some cDecl =>
        rw [hc] at hm; dsimp only at hm
        split at hm <;> try contradiction
        injection hm with h; injection h with _ h2; subst h2
        simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hprog
        have hcOk := hprog.1.1.2 dDecl (List.mem_of_find?_eq_some hd) cDecl (List.mem_of_find?_eq_some hc)
        rw [ltyListSinksAllowed_iff] at hcOk
        simp only [valSafeForNI] at hsValSafe
        rw [valListSafeForNI_iff] at hsValSafe
        intro tv htv
        have hpair := List.of_mem_zip htv
        rw [List.mem_map] at hpair
        rcases hpair.1 with ⟨f, hfIn, hfeq⟩
        exact ⟨hfeq ▸ by simpa using hcOk f hfIn, hsValSafe tv.2 hpair.2⟩

theorem not_subset_union_left {a b L : TagSet} (ha : a.subset L = false) :
    (a.union b).subset L = false := by
  rw [TagSet.union_subset_iff]
  simp [ha]

def ExprSafeAndConfinedAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ env jenv pc inSpec w e lty,
    EnvWf prog env →
    envSafeForNI L env = true →
    envNoSpecCalls prog env = true →
    joinEnvSinksAllowed L jenv = true →
    WorldWf prog w →
    exprSafeForNI L e = true →
    exprNoSpecCalls prog e = true →
    checkExpr prog (envToTyEnv env) jenv pc inSpec e = .ok lty →
    outcomeValSafe L (eval fuel prog env pc w e) ∧
    outcomeNoSpecCalls prog (eval fuel prog env pc w e) ∧
    (pc.subset L = false → outcomeWorldEq w (eval fuel prog env pc w e))

def JoinLoopSafeAndConfinedAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ baseEnv curEnv jenv label params joinPc retLTy rLTy inSpec rhs w,
    EnvWf prog baseEnv →
    envSafeForNI L baseEnv = true →
    envNoSpecCalls prog baseEnv = true →
    EnvWf prog curEnv →
    envSafeForNI L curEnv = true →
    envNoSpecCalls prog curEnv = true →
    envToTyEnv curEnv = extendTyEnv (envToTyEnv baseEnv) params →
    joinEnvSinksAllowed L jenv = true →
    ltyListSinksAllowed L (params.map Prod.snd) = true →
    ltySinksAllowed L retLTy = true →
    WorldWf prog w →
    exprSafeForNI L rhs = true →
    exprNoSpecCalls prog rhs = true →
    checkExpr prog (extendTyEnv (envToTyEnv baseEnv) params)
      ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
      joinPc inSpec rhs = .ok rLTy →
    rLTy.ty = retLTy.ty →
    outcomeValSafe L (evalJoinLoop fuel prog baseEnv label params joinPc rhs curEnv w) ∧
    outcomeNoSpecCalls prog (evalJoinLoop fuel prog baseEnv label params joinPc rhs curEnv w) ∧
    (joinPc.subset L = false →
      outcomeWorldEq w (evalJoinLoop fuel prog baseEnv label params joinPc rhs curEnv w))

def PlanSafeAndConfinedAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ env pc inSpec w plan pTy,
    EnvWf prog env →
    envSafeForNI L env = true →
    envNoSpecCalls prog env = true →
    WorldWf prog w →
    planSafeForNI L plan = true →
    planNoSpecCalls prog plan = true →
    checkPlan prog (envToTyEnv env) pc inSpec plan = .ok pTy →
    outcomeValSafe L (evalPlan fuel prog env pc w plan) ∧
    outcomeNoSpecCalls prog (evalPlan fuel prog env pc w plan) ∧
    (pc.subset L = false → outcomeWorldEq w (evalPlan fuel prog env pc w plan))

/-- Any relational helper over an already-evaluated input table `tv` at world `w1`
    produces only `.table _`, `.dynTable _ _`, `.stopped _ w1`, `.outOfFuel`, or `.wrong`
    at the exact same `w1`! -/
theorem evalDeriveItems_world_and_safe {prog : Program} {L : TagSet} {tEnv : TyEnv}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult) (w1 : World) :
    ∀ (curTV : TableVal) (items : List DeriveItem),
      outcomeValSafe L (evalDeriveItems prog tEnv evalRE w1 curTV items) ∧
      outcomeNoSpecCalls prog (evalDeriveItems prog tEnv evalRE w1 curTV items) ∧
      outcomeWorldEq w1 (evalDeriveItems prog tEnv evalRE w1 curTV items)
  | _, [] => ⟨rfl, rfl, rfl⟩
  | curTV, item :: rest => by
    unfold evalDeriveItems
    cases applyDeriveItem prog tEnv curTV.cols item with
    | error _ => exact ⟨trivial, trivial, trivial⟩
    | ok nextCols =>
      dsimp only
      cases evalDeriveMapRows evalRE curTV.cols item (lookupColIdx? curTV.cols (deriveItemTargetName item)) curTV.rows with
      | ok _ => exact evalDeriveItems_world_and_safe evalRE w1 _ rest
      | stopped _ => exact ⟨trivial, trivial, rfl⟩
      | outOfFuel | wrong => exact ⟨trivial, trivial, trivial⟩

theorem evalFilterRows_world_and_safe {prog : Program} {L : TagSet}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (inCols outCols : List ColSpec) (pred : RowExpr) (w1 : World) :
    ∀ (rows : List TableRow),
      outcomeValSafe L (evalFilterRows evalRE inCols outCols pred w1 rows) ∧
      outcomeNoSpecCalls prog (evalFilterRows evalRE inCols outCols pred w1 rows) ∧
      outcomeWorldEq w1 (evalFilterRows evalRE inCols outCols pred w1 rows)
  | [] => ⟨rfl, rfl, rfl⟩
  | r :: rs => by
    unfold evalFilterRows
    cases evalRE inCols r pred with
    | stopped _ => exact ⟨trivial, trivial, rfl⟩
    | outOfFuel | wrong => exact ⟨trivial, trivial, trivial⟩
    | ok pv =>
      cases pv <;> try exact ⟨trivial, trivial, trivial⟩
      have ih := evalFilterRows_world_and_safe (prog := prog) (L := L) evalRE inCols outCols pred w1 rs
      cases hrest : evalFilterRows evalRE inCols outCols pred w1 rs with
      | ok rv rw1 =>
        rw [hrest] at ih
        cases rv <;> try exact ih
        exact ⟨rfl, rfl, rfl⟩
      | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
        rw [hrest] at ih; exact ih

theorem evalSummarizeGroups_world_and_safe {prog : Program} {L : TagSet}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (tv : TableVal) (groupKeys : List Ident) (distinctKey : Option Ident)
    (dkIdx? : Option (Nat × ColSpec)) (aggs : List AggItem) (aggCols outCols : List ColSpec)
    (w1 : World) :
    ∀ (gks : List (List Val)),
      outcomeValSafe L (evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks) ∧
      outcomeNoSpecCalls prog (evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks) ∧
      outcomeWorldEq w1 (evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks)
  | [] => ⟨rfl, rfl, rfl⟩
  | gKey :: gks => by
    unfold evalSummarizeGroups
    dsimp only
    cases evalGroupAggItems evalRE tv.cols _ (List.zip aggs aggCols) with
    | stopped _ => exact ⟨trivial, trivial, rfl⟩
    | outOfFuel | wrong => exact ⟨trivial, trivial, trivial⟩
    | ok _ =>
      dsimp only
      have ih := evalSummarizeGroups_world_and_safe (prog := prog) (L := L) evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks
      cases hrest : evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks with
      | ok rv _ =>
        rw [hrest] at ih
        cases rv <;> try exact ih
        exact ⟨rfl, rfl, rfl⟩
      | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
        rw [hrest] at ih; exact ih

theorem eval_safe_and_confined_all (prog : Program) (L : TagSet) :
    ∀ (fuel : Nat),
      ExprSafeAndConfinedAt fuel prog L ∧
      JoinLoopSafeAndConfinedAt fuel prog L ∧
      PlanSafeAndConfinedAt fuel prog L
  | 0 => ⟨by unfold ExprSafeAndConfinedAt; intros; unfold eval; exact ⟨trivial, trivial, fun _ => trivial⟩,
          by unfold JoinLoopSafeAndConfinedAt; intros; unfold evalJoinLoop; exact ⟨trivial, trivial, fun _ => trivial⟩,
          by unfold PlanSafeAndConfinedAt; intros; unfold evalPlan; exact ⟨trivial, trivial, fun _ => trivial⟩⟩
  | fuel' + 1 => by
    rcases eval_safe_and_confined_all prog L fuel' with ⟨ihE, ihJL, ihP⟩
    have hsound := eval_fuel_sound prog fuel'
    refine ⟨?_, ?_, ?_⟩
    -- 1. ExprSafeAndConfinedAt (fuel' + 1)
    · intro hprog hsafeProg env jenv pc inSpec w expr lty henvWf henvSafe henvNs hjenvSafe hwWf hesafe hens hchk
      have htyEnvOk := envSafeForNI_imp_tyEnv henvSafe
      unfold eval
      cases expr with
      | lit v =>
        dsimp only
        exact ⟨by cases v <;> rfl, by cases v <;> rfl, fun _ => rfl⟩
      | var name =>
        dsimp only
        cases hl : lookupEnv env name with
        | none => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
        | some pair => dsimp only; exact ⟨(lookupEnv_safeForNI henvSafe hl).2, lookupEnv_noSpecCalls henvNs hl, fun _ => rfl⟩
      | constRef name =>
        dsimp only
        cases prog.findConst? name with
        | none => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
        | some cDecl => dsimp only; exact ⟨by cases cDecl.value <;> rfl, by cases cDecl.value <;> rfl, fun _ => rfl⟩
      | letE name declLTy bound body =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hb : checkExpr prog (envToTyEnv env) [] pc inSpec bound with
        | error _ => simp [hb] at hchk
        | ok bLTy =>
          simp only [hb] at hchk
          split at hchk <;> try contradiction
          rename_i hsub
          have hbWf := hsound.2.2.1 hprog env [] pc inSpec w bound bLTy henvWf hwWf hb
          rcases ihE hprog hsafeProg env [] pc inSpec w bound bLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe.1.2 hens.1 hb with ⟨hbSafe, hbNs, hbConf⟩
          cases houtB : eval fuel' prog env pc w bound with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only
            rw [houtB] at hbSafe hbNs hbConf; exact ⟨hbSafe, hbNs, hbConf⟩
          | ok bVal w1 =>
            dsimp only
            rw [houtB] at hbWf hbSafe hbNs hbConf
            dsimp only [outcomeValSafe, outcomeNoSpecCalls, outcomeWorldEq] at hbSafe hbNs hbConf
            cases hbWf with | ok hbValWf hw1 =>
            simp only [Bool.not_eq_true', Bool.not_eq_false, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
            have hentryWf : EnvWf prog ({ name := name, lty := declLTy.addTags pc, val := bVal } :: env) :=
              .cons (by simpa [hsub.1] using hbValWf) henvWf
            have hentrySafe : envSafeForNI L ({ name := name, lty := declLTy.addTags pc, val := bVal } :: env) = true := by
              simp [envSafeForNI, hesafe.1.1, hbSafe, henvSafe]
            have hentryNs : envNoSpecCalls prog ({ name := name, lty := declLTy.addTags pc, val := bVal } :: env) = true := by
              simp [envNoSpecCalls, hbNs, henvNs]
            rcases ihE hprog hsafeProg _ jenv pc inSpec w1 body lty hentryWf hentrySafe hentryNs hjenvSafe hw1 hesafe.2 hens.2 hchk with ⟨hbodySafe, hbodyNs, hbodyConf⟩
            refine ⟨hbodySafe, hbodyNs, fun hpcF => ?_⟩
            have hw1Eq : w1 = w := hbConf hpcF
            subst hw1Eq
            exact hbodyConf hpcF
      | ifE cond tBr eBr =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hc : checkExpr prog (envToTyEnv env) [] pc inSpec cond with
        | error _ => simp [hc] at hchk
        | ok cLTy =>
          simp only [hc] at hchk
          split at hchk <;> try contradiction
          cases ht : checkExpr prog (envToTyEnv env) jenv (pc.union cLTy.tags) inSpec tBr with
          | error _ => simp [ht] at hchk
          | ok tLTy =>
            simp only [ht] at hchk
            cases he : checkExpr prog (envToTyEnv env) jenv (pc.union cLTy.tags) inSpec eBr with
            | error _ => simp [he] at hchk
            | ok eLTy =>
              rw [checkExpr_inSpec_true hc]; dsimp only
              have hcWf := hsound.2.2.1 hprog env [] pc inSpec w cond cLTy henvWf hwWf hc
              rcases ihE hprog hsafeProg env [] pc inSpec w cond cLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe.1.1 hens.1.1 hc with ⟨hcSafe, hcNs, hcConf⟩
              cases houtC : eval fuel' prog env pc w cond with
              | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
                dsimp only
                rw [houtC] at hcSafe hcNs hcConf; exact ⟨hcSafe, hcNs, hcConf⟩
              | ok cv w1 =>
                try dsimp only
                rw [houtC] at hcWf hcSafe hcNs hcConf
                cases hcWf with | ok hcvWf hw1 =>
                cases cv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
                case bool b =>
                  cases b <;> try dsimp only
                  · rcases ihE hprog hsafeProg env jenv (pc.union cLTy.tags) inSpec w1 eBr eLTy henvWf henvSafe henvNs hjenvSafe hw1 hesafe.2 hens.2 he with ⟨heSafe, heNs, heConf⟩
                    refine ⟨heSafe, heNs, fun hpcF => ?_⟩
                    have hw1Eq : w1 = w := hcConf hpcF; subst hw1Eq
                    exact heConf (not_subset_union_left hpcF)
                  · rcases ihE hprog hsafeProg env jenv (pc.union cLTy.tags) inSpec w1 tBr tLTy henvWf henvSafe henvNs hjenvSafe hw1 hesafe.1.2 hens.1.2 ht with ⟨htSafe, htNs, htConf⟩
                    refine ⟨htSafe, htNs, fun hpcF => ?_⟩
                    have hw1Eq : w1 = w := hcConf hpcF; subst hw1Eq
                    exact htConf (not_subset_union_left hpcF)
      | caseE scrut arms =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hsc : checkExpr prog (envToTyEnv env) [] pc inSpec scrut with
        | error _ => simp [hsc] at hchk
        | ok scrutLTy =>
          simp only [hsc] at hchk
          cases hsp : expectedCaseSpecs prog scrutLTy.ty scrutLTy.effectiveTags with
          | error _ => simp [hsp] at hchk
          | ok specs =>
            simp only [hsp] at hchk
            split at hchk <;> try contradiction
            cases ha : checkCaseArms prog (envToTyEnv env) jenv (pc.union scrutLTy.effectiveTags) inSpec specs arms with
            | error _ => simp [ha] at hchk
            | ok _ =>
              rw [checkExpr_inSpec_true hsc]; dsimp only
              have hscWf := hsound.2.2.1 hprog env [] pc inSpec w scrut scrutLTy henvWf hwWf hsc
              have hscSink := checkExpr_sinksAllowed hsafeProg htyEnvOk (by rfl) hesafe.1 hens.1 hsc
              rcases ihE hprog hsafeProg env [] pc inSpec w scrut scrutLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe.1 hens.1 hsc with ⟨hscSafe, hscNs, hscConf⟩
              cases houtS : eval fuel' prog env pc w scrut with
              | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
                dsimp only
                rw [houtS] at hscSafe hscNs hscConf; exact ⟨hscSafe, hscNs, hscConf⟩
              | ok sVal w1 =>
                dsimp only
                rw [houtS] at hscWf hscSafe hscNs hscConf
                cases hscWf with | ok hsValWf hw1 =>
                cases hm : matchCaseVal prog sVal scrutLTy (pc.union scrutLTy.effectiveTags) with
                | none => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
                | some pair =>
                  rcases pair with ⟨cName, typedVals⟩
                  try dsimp only
                  cases hfindArm : arms.find? (fun (.mk ac _ _) => ac == cName) with
                  | none => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
                  | some arm =>
                    rcases arm with ⟨ac, binders, armBody⟩
                    try dsimp only
                    split
                    · exact ⟨trivial, trivial, fun _ => trivial⟩
                    · rename_i hlenOk
                      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                      have hbeq := List.find?_some hfindArm
                      dsimp only at hbeq
                      have hcEq : cName = ac := (beq_iff_eq.mp hbeq).symm
                      subst hcEq
                      rcases matchCaseVal_sound hsValWf hsp (armPc := pc.union scrutLTy.effectiveTags) with
                        ⟨cName2, fieldLTys, typedVals2, hm2, hspecFind, htvLTys, htvWf⟩
                      rw [hm] at hm2; injection hm2 with hpEq; injection hpEq with hc2 htv2; subst hc2; subst htv2
                      rcases checkCaseArms_props ha with ⟨_, harmFindProp⟩
                      rcases harmFindProp cName binders armBody fieldLTys hfindArm hspecFind with
                        ⟨hbindLen, armLTy, _, harmBodyChk⟩
                      have harmSafeNs : exprSafeForNI L armBody = true ∧ exprNoSpecCalls prog armBody = true := by
                        have hmem := List.mem_of_find?_eq_some hfindArm
                        have haux : ∀ (as1 : List CaseArm), CaseArm.mk cName binders armBody ∈ as1 →
                            caseArmsSafeForNI L as1 = true → caseArmsNoSpecCalls prog as1 = true →
                            exprSafeForNI L armBody = true ∧ exprNoSpecCalls prog armBody = true := by
                          intro as1 hm0 hc0 hn0
                          induction as1 with
                          | nil => nomatch hm0
                          | cons hd tl iha =>
                            cases hd
                            simp only [caseArmsSafeForNI, Bool.and_eq_true] at hc0
                            simp only [caseArmsNoSpecCalls, Bool.and_eq_true] at hn0
                            rcases List.mem_cons.mp hm0 with heq | htl
                            · injection heq with _ _ hb; subst hb; exact ⟨hc0.1, hn0.1⟩
                            · exact iha htl hc0.2 hn0.2
                        exact haux arms hmem hesafe.2 hens.2
                      have htvSafe := matchCaseVal_safeForNI hsafeProg hscSink hscSafe hm
                      have htvNs := matchCaseVal_noSpecCalls hscNs hm
                      rcases envWf_armEntries binders
                        (fieldLTys.map (fun f => f.addTags (pc.union scrutLTy.effectiveTags)))
                        (typedVals.map Prod.snd) typedVals env
                        (by simp [hbindLen]) htvLTys rfl htvWf henvWf with
                        ⟨harmEnvWf, harmTyEq⟩
                      let armEntries : Env := (List.zip binders typedVals).map
                        (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })
                      have harmEnvSafe : envSafeForNI L (armEntries ++ env) = true := by
                        dsimp only [armEntries]
                        clear harmEnvWf
                        have haux : ∀ (bs : List Ident) (tvs : List (LTy × Val)),
                            (∀ p ∈ tvs, ltySinksAllowed L p.1 = true ∧ valSafeForNI L p.2 = true) →
                            envSafeForNI L ((List.zip bs tvs).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ env) = true := by
                          intro bs tvs hp
                          induction bs generalizing tvs with
                          | nil => exact henvSafe
                          | cons b bsTl ihb =>
                            cases tvs with
                            | nil => exact henvSafe
                            | cons tv tvsTl =>
                              rcases hp tv (.head _) with ⟨h1, h2⟩
                              simp [List.zip_cons_cons, envSafeForNI, h1, h2, ihb tvsTl (fun q hq => hp q (.tail _ hq))]
                        exact haux binders typedVals htvSafe
                      have harmEnvNs : envNoSpecCalls prog (armEntries ++ env) = true := by
                        dsimp only [armEntries]
                        have haux : ∀ (bs : List Ident) (tvs : List (LTy × Val)),
                            (∀ p ∈ tvs, valNoSpecCalls prog p.2 = true) →
                            envNoSpecCalls prog ((List.zip bs tvs).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ env) = true := by
                          intro bs tvs hp
                          induction bs generalizing tvs with
                          | nil => exact henvNs
                          | cons _ bsTl ihb =>
                            cases tvs with
                            | nil => exact henvNs
                            | cons tv tvsTl =>
                              simp [List.zip_cons_cons, envNoSpecCalls, hp tv (.head _), ihb tvsTl (fun q hq => hp q (.tail _ hq))]
                        exact haux binders typedVals htvNs
                      rw [extendTyEnv, ← harmTyEq] at harmBodyChk
                      rcases ihE hprog hsafeProg (armEntries ++ env) jenv (pc.union scrutLTy.effectiveTags) inSpec w1 armBody armLTy
                        harmEnvWf harmEnvSafe harmEnvNs hjenvSafe hw1 harmSafeNs.1 harmSafeNs.2 harmBodyChk with ⟨hbSafe, hbNs, hbConf⟩
                      refine ⟨hbSafe, hbNs, fun hpcF => ?_⟩
                      have hw1Eq : w1 = w := hscConf hpcF; subst hw1Eq
                      exact hbConf (not_subset_union_left hpcF)
      | lam params fnPc retLTy body =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        exact ⟨by simp [outcomeValSafe, valSafeForNI, hesafe.1.1, hesafe.1.2, hesafe.2, henvSafe],
               by simp [outcomeNoSpecCalls, valNoSpecCalls, henvNs]; exact hens,
               fun _ => rfl⟩
      | app fnExpr args =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
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
              rename_i hcallPcSub
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hcallPcSub
              have hfWf := hsound.2.2.1 hprog env [] pc inSpec w fnExpr fnLTy henvWf hwWf hf
              rw [hfty] at hfWf
              rcases ihE hprog hsafeProg env [] pc inSpec w fnExpr fnLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe.1 hens.1 hf with ⟨hfSafe, hfNs, hfConf⟩
              cases houtF : eval fuel' prog env pc w fnExpr with
              | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
                dsimp only
                rw [houtF] at hfSafe hfNs hfConf; exact ⟨hfSafe, hfNs, hfConf⟩
              | ok fv w1 =>
                rw [houtF] at hfWf hfSafe hfNs hfConf
                cases hfWf with | ok hfvWf hw1 =>
                cases hfvWf with | @closure params _ _ bodyLTy body capEnv hcapWf hbodyChk _ =>
                dsimp only
                simp only [outcomeValSafe, valSafeForNI, Bool.and_eq_true] at hfSafe
                simp only [outcomeNoSpecCalls, valNoSpecCalls, Bool.and_eq_true] at hfNs
                have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
                  And.intro
                    (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
                    (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
                have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hw1 hesafe.2 hens.2 ha
                cases hseqOut : evalSeq (eval fuel' prog env pc) w1 args with
                | aborted out =>
                  rw [hseqOut] at hseq; dsimp only
                  refine ⟨hseq.1, hseq.2.1, fun hpcF => ?_⟩
                  have hw1Eq : w1 = w := hfConf hpcF; subst hw1Eq; exact hseq.2.2 hpcF
                | ok argVals w2 =>
                  rw [hseqOut] at hseq; dsimp only
                  split
                  · exact ⟨trivial, trivial, fun _ => trivial⟩
                  · rename_i hlenOk
                    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                    have haWf := evalSeq_sound (eval fuel' prog env pc)
                      (fun w' e' eLTy hw' he' => hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he') hw1 ha
                    rw [hseqOut] at haWf
                    split at hchk <;> try contradiction
                    split at hchk <;> try contradiction
                    rename_i hzipSub
                    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hzipSub
                    have hvsParamsWf := valListWf_of_zip_tyEq (bs1 := params.map Prod.snd) haWf.1
                      (by rw [← haWf.1.length_eq, hlenOk, List.length_map])
                      (fun p hp => (hzipSub p hp).1)
                    have hcallEnvWf := extendEnv_wf hvsParamsWf hcapWf
                    have hcallEnvSafe := extendEnv_safeForNI hfSafe.1.1.1 hseq.1 hfSafe.2
                    have hcallEnvNs := extendEnv_noSpecCalls (params := params) hseq.2.1 hfNs.2
                    have hcallTyEq : envToTyEnv ((List.zip params argVals).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv) =
                        extendTyEnv (envToTyEnv capEnv) params := by
                      rw [envToTyEnv_append, envToTyEnv_zip_params params argVals hlenOk, extendTyEnv]
                    rw [← hcallTyEq] at hbodyChk
                    rcases ihE hprog hsafeProg _ [] fnPc true w2 body bodyLTy hcallEnvWf hcallEnvSafe hcallEnvNs (by rfl) hseq.2.2.1 hfSafe.1.2 hfNs.1 hbodyChk with ⟨hbSafe, hbNs, hbConf⟩
                    have hfnPcF : pc.subset L = false → fnPc.subset L = false := by
                      intro hpcF
                      cases hfn : fnPc.subset L
                      · rfl
                      · have hpSub := TagSet.subset_trans (TagSet.subset_union_left pc fnLTy.tags) (TagSet.subset_trans hcallPcSub hfn)
                        rw [hpcF] at hpSub; nomatch hpSub
                    cases houtB : eval fuel' prog _ fnPc w2 body with
                    | jumped _ _ _ => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
                    | ok v w3 | stopped v w3 | failed v w3 =>
                      dsimp only
                      rw [houtB] at hbSafe hbNs hbConf
                      refine ⟨hbSafe, hbNs, fun hpcF => ?_⟩
                      have hw3 : w3 = w2 := hbConf (hfnPcF hpcF)
                      exact hw3.trans ((hseq.2.2.2 hpcF).trans (hfConf hpcF))
                    | wrong | outOfFuel => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
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
            simp only [exprNoSpecCalls, hf, Bool.and_eq_true, Bool.not_eq_true'] at hens
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i hpcSubFn
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i hzipSub
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hpcSubFn
            simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hzipSub
            have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
              And.intro
                (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
                (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
            have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hwWf hesafe hens.2 ha
            cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
            | aborted out =>
              dsimp only; rw [hseqOut] at hseq; exact hseq
            | ok argVals w1 =>
              rw [hseqOut] at hseq; dsimp only
              split
              · exact ⟨trivial, trivial, fun _ => trivial⟩
              · rename_i hlenOk
                simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                have haWf := evalSeq_sound (eval fuel' prog env pc)
                  (fun w' e' eLTy hw' he' => hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he') hwWf ha
                rw [hseqOut] at haWf
                rcases checkFunDecl_valid hprog hf with ⟨bodyLTy, hbodyChk, _⟩
                rw [hens.1] at hbodyChk
                have hbodyNs := checkExpr_noSpecCalls hbodyChk
                have hsafeProg' := hsafeProg
                simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hsafeProg'
                have hfSafe := hsafeProg'.2 fDecl (List.mem_of_find?_eq_some hf)
                simp only [hens.1, Bool.false_or, Bool.and_eq_true] at hfSafe
                have hvsParamsWf := valListWf_of_zip_tyEq (bs1 := fDecl.params.map Prod.snd) haWf.1
                  (by rw [← haWf.1.length_eq, hlenOk, List.length_map])
                  (fun p hp => (hzipSub p hp).1)
                let callEnv : Env := (List.zip fDecl.params argVals).reverse.map
                  (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })
                rcases callEnv_props hlenOk hvsParamsWf hfSafe.1.1.1 hseq.1 with
                  ⟨hcallEnvWf, hcallEnvSafe, hcallTyEq⟩
                have hcallEnvNs : envNoSpecCalls prog callEnv = true := by
                  dsimp only [callEnv]; rw [List.map_reverse]
                  exact envNoSpecCalls_reverse (by simpa using extendEnv_noSpecCalls (params := fDecl.params) hseq.2.1 (rfl : envNoSpecCalls prog [] = true))
                rw [← hcallTyEq] at hbodyChk
                rcases ihE hprog hsafeProg callEnv [] fDecl.pc false w1 fDecl.body bodyLTy
                  hcallEnvWf hcallEnvSafe hcallEnvNs (by rfl) hseq.2.2.1 hfSafe.1.2 hbodyNs hbodyChk with ⟨hbSafe, hbNs, hbConf⟩
                have hfnPcF : pc.subset L = false → fDecl.pc.subset L = false := by
                  intro hpcF
                  cases hfn : fDecl.pc.subset L
                  · rfl
                  · have := TagSet.subset_trans hpcSubFn hfn; rw [hpcF] at this; nomatch this
                cases houtB : eval fuel' prog callEnv fDecl.pc w1 fDecl.body with
                | jumped _ _ _ => try dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
                | ok v w2 | stopped v w2 | failed v w2 =>
                  try dsimp only
                  rw [houtB] at hbSafe hbNs hbConf
                  refine ⟨hbSafe, hbNs, fun hpcF => ?_⟩
                  exact (hbConf (hfnPcF hpcF)).trans (hseq.2.2.2 hpcF)
                | wrong | outOfFuel => try dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
      | join label params rhs body =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        dsimp only at hchk
        let guess1 := pc.union (inferJumpPc prog label (envToTyEnv env) pc body)
        let rhsEnv := extendTyEnv (envToTyEnv env) params
        let joinPc := guess1.union (inferJumpPc prog label rhsEnv guess1 rhs)
        have hrhsEnvOk := extendTyEnv_sinksAllowed htyEnvOk hesafe.1.1
        cases hinf : inferJoinRetLTy prog rhsEnv jenv joinPc label rhs body with
        | none => rw [hinf] at hchk; contradiction
        | some candRetLTy =>
          rw [hinf] at hchk
          have hcandOk : ltySinksAllowed L candRetLTy = true := by
            unfold inferJoinRetLTy at hinf
            cases h1 : inferBranchLTy prog rhsEnv jenv joinPc [label] rhs with
            | some l =>
              rw [h1] at hinf; injection hinf with h; subst h
              exact inferBranchLTy_sinksAllowed hsafeProg hrhsEnvOk hjenvSafe hesafe.1.2 hens.1 h1
            | none =>
              rw [h1] at hinf
              exact inferBranchLTy_sinksAllowed hsafeProg hrhsEnvOk hjenvSafe hesafe.2 hens.2 hinf
          dsimp only [bind, Except.bind] at hchk
          split at hchk <;> try contradiction
          have hjoinCheck : ∃ effRet rLTy bLTy,
              ltySinksAllowed L effRet = true ∧
              checkExpr prog rhsEnv ((label, { params := params, joinPc := joinPc, retLTy := effRet }) :: jenv) joinPc inSpec rhs = .ok rLTy ∧
              checkExpr prog (envToTyEnv env) ((label, { params := params, joinPc := joinPc, retLTy := effRet }) :: jenv) pc inSpec body = .ok bLTy ∧
              rLTy.ty = effRet.ty := by
            cases hr1 : checkExpr prog rhsEnv _ joinPc inSpec rhs with
            | error _ => rw [hr1] at hchk; contradiction
            | ok r1 =>
              rw [hr1] at hchk; dsimp only at hchk
              cases hb1 : checkExpr prog (envToTyEnv env) _ pc inSpec body with
              | error _ => rw [hb1] at hchk; contradiction
              | ok b1 =>
                rw [hb1] at hchk; dsimp only at hchk
                split at hchk <;> try contradiction
                rename_i htyEq
                simp only [Bool.and_eq_true, decide_eq_true_eq] at htyEq
                split at hchk
                · exact ⟨candRetLTy.addTags joinPc, r1, b1, by simpa using hcandOk, hr1, hb1, htyEq.1⟩
                · cases hr2 : checkExpr prog rhsEnv _ joinPc inSpec rhs with
                  | error _ => rw [hr2] at hchk; contradiction
                  | ok r2 =>
                    rw [hr2] at hchk; dsimp only at hchk
                    cases hb2 : checkExpr prog (envToTyEnv env) _ pc inSpec body with
                    | error _ => rw [hb2] at hchk; contradiction
                    | ok b2 =>
                      rw [hb2] at hchk; dsimp only at hchk
                      split at hchk <;> try contradiction
                      rename_i hsub2
                      simp only [Bool.and_eq_true, ltySubtype, decide_eq_true_eq] at hsub2
                      exact ⟨_, r2, b2, by simpa [ltySinksAllowed] using hcandOk, hr2, hb2, hsub2.1.1⟩
          rcases hjoinCheck with ⟨effRet, rLTy, bLTy, heffRetOk, hrChk, hbChk, hrTyEq⟩
          have hjenv'Safe : joinEnvSinksAllowed L ((label, { params := params, joinPc := joinPc, retLTy := effRet }) :: jenv) = true := by
            simp only [joinEnvSinksAllowed, List.all_cons, Bool.and_eq_true]
            exact ⟨⟨hesafe.1.1, heffRetOk⟩, hjenvSafe⟩
          have hbWf := hsound.2.2.1 hprog env _ pc inSpec w body bLTy henvWf hwWf hbChk
          rcases ihE hprog hsafeProg env _ pc inSpec w body bLTy henvWf henvSafe henvNs hjenv'Safe hwWf hesafe.2 hens.2 hbChk with ⟨hbSafe, hbNs, hbConf⟩
          cases houtB : eval fuel' prog env pc w body with
          | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtB] at hbSafe hbNs hbConf; exact ⟨hbSafe, hbNs, hbConf⟩
          | jumped lbl jVals w1 =>
            dsimp only
            rw [houtB] at hbWf hbSafe hbNs hbConf
            cases hbWf with | @jumped _ _ _ otherSig hlookJ hjValsWf hw1 =>
            cases hlbl : (lbl == label)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨hbSafe, hbNs, hbConf⟩
            · simp only [↓reduceIte]
              have heq : label = lbl := (beq_iff_eq.mp hlbl).symm
              simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlookJ
              subst hlookJ
              split
              · exact ⟨trivial, trivial, fun _ => trivial⟩
              · rename_i hlenOk
                simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                have hjEnvWf := extendEnv_wf hjValsWf henvWf
                have hjEnvSafe := extendEnv_safeForNI hesafe.1.1 hbSafe henvSafe
                have hjEnvNs := extendEnv_noSpecCalls (params := params) hbNs henvNs
                have hjTyEq : envToTyEnv ((List.zip params jVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env) =
                    extendTyEnv (envToTyEnv env) params := by
                  rw [envToTyEnv_append, envToTyEnv_zip_params params jVals hlenOk, extendTyEnv]
                rcases ihJL hprog hsafeProg env _ jenv label params joinPc effRet rLTy inSpec rhs w1
                  henvWf henvSafe henvNs hjEnvWf hjEnvSafe hjEnvNs hjTyEq hjenvSafe hesafe.1.1 heffRetOk hw1 hesafe.1.2 hens.1 hrChk hrTyEq with ⟨hjlSafe, hjlNs, hjlConf⟩
                refine ⟨hjlSafe, hjlNs, fun hpcF => ?_⟩
                have hjoinPcF : joinPc.subset L = false :=
                  not_subset_union_left (not_subset_union_left hpcF)
                have hw1Eq : w1 = w := hbConf hpcF; subst hw1Eq
                exact hjlConf hjoinPcF
      | jump label args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
            And.intro
              (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
              (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
          have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hwWf hesafe hens ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq
          | ok vs w1 => dsimp only; rw [hseqOut] at hseq; exact ⟨hseq.1, hseq.2.1, hseq.2.2.2⟩
      | tuple elems =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec elems with
        | error _ => simp [ha] at hchk
        | ok elemLTys =>
          have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
            And.intro
              (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
              (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
          have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hwWf hesafe hens ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w elems with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq
          | ok vs w1 => dsimp only; rw [hseqOut] at hseq; exact ⟨hseq.1, hseq.2.1, hseq.2.2.2⟩
      | proj tup idx =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ht : checkExpr prog (envToTyEnv env) [] pc inSpec tup with
        | error _ => simp [ht] at hchk
        | ok tupLTy =>
          rcases ihE hprog hsafeProg env [] pc inSpec w tup tupLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe hens ht with ⟨htSafe, htNs, htConf⟩
          cases houtT : eval fuel' prog env pc w tup with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtT] at htSafe htNs htConf; exact ⟨htSafe, htNs, htConf⟩
          | ok tv w1 =>
            try dsimp only
            rw [houtT] at htSafe htNs htConf
            cases tv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
            case tuple vs =>
              cases hg : vs[idx]? with
              | none => try dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
              | some v =>
                try dsimp only
                simp only [outcomeValSafe, valSafeForNI] at htSafe
                simp only [outcomeNoSpecCalls, valNoSpecCalls] at htNs
                exact ⟨(valListSafeForNI_iff.mp htSafe) v (List.mem_of_getElem? hg),
                       (valListNoSpecCalls_iff.mp htNs) v (List.mem_of_getElem? hg), htConf⟩
      | ctor _ _ args =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok _ =>
          have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
            And.intro
              (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
              (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
          have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hwWf hesafe hens ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq
          | ok vs w1 => dsimp only; rw [hseqOut] at hseq; exact ⟨hseq.1, hseq.2.1, hseq.2.2.2⟩
      | tableLit _ _ =>
        dsimp only
        exact ⟨rfl, rfl, fun _ => rfl⟩
      | prim op args =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok _ =>
          have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
            And.intro
              (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
              (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
          have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hwWf hesafe.2 hens ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq
          | ok vs w1 =>
            rw [hseqOut] at hseq; dsimp only
            cases hp : evalPrimOp op vs with
            | ok v => dsimp only; exact ⟨evalPrimOp_safeForNI hseq.1 hp, evalPrimOp_noSpecCalls hseq.2.1 hp, hseq.2.2.2⟩
            | stopped _ => dsimp only; exact ⟨trivial, trivial, hseq.2.2.2⟩
            | outOfFuel | wrong => dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
      | rel plan =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hp : checkPlan prog (envToTyEnv env) pc inSpec plan with
        | error _ => simp [hp] at hchk
        | ok pTy => exact ihP hprog hsafeProg env pc inSpec w plan pTy henvWf henvSafe henvNs hwWf hesafe hens hp
      | host op args =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args with
        | error _ => simp [ha] at hchk
        | ok argLTys =>
          simp only [ha] at hchk
          have hargSinks := checkExprList_sinksAllowed hsafeProg htyEnvOk hesafe.2 hens ha
          have hseqStep := fun w' e' eLTy hw' hes' hns' he' =>
            And.intro
              (hsound.2.2.1 hprog env [] pc inSpec w' e' eLTy henvWf hw' he')
              (ihE hprog hsafeProg env [] pc inSpec w' e' eLTy henvWf henvSafe henvNs (by rfl) hw' hes' hns' he')
          have hseq := evalSeq_safe_and_confined (eval fuel' prog env pc) hseqStep hwWf hesafe.2 hens ha
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => dsimp only; rw [hseqOut] at hseq; exact hseq
          | ok vs w1 =>
            rw [hseqOut] at hseq; dsimp only
            rcases evalHostOp_safe_and_confined hesafe.1 hargSinks hseq.1 hchk (w := w1) with ⟨hhSafe, hhConf⟩
            refine ⟨hhSafe, evalHostOp_noSpecCalls hseq.2.1, fun hpcF => ?_⟩
            have hw1Eq : w1 = w := hseq.2.2.2 hpcF; subst hw1Eq
            exact hhConf hpcF
      | stop kind detail =>
        dsimp only
        unfold checkExpr at hchk
        cases detail with
        | none => dsimp only; exact ⟨trivial, trivial, fun _ => rfl⟩
        | some dExpr =>
          dsimp only at hchk ⊢
          split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hd : checkExpr prog (envToTyEnv env) [] pc inSpec dExpr with
          | error _ => simp [hd] at hchk
          | ok dLTy =>
            rw [checkExpr_inSpec_true hd]; dsimp only
            rcases ihE hprog hsafeProg env [] pc inSpec w dExpr dLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe hens hd with ⟨hdSafe, hdNs, hdConf⟩
            cases houtD : eval fuel' prog env pc w dExpr with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              dsimp only; rw [houtD] at hdSafe hdNs hdConf; exact ⟨hdSafe, hdNs, hdConf⟩
            | ok _ w1 =>
              dsimp only; rw [houtD] at hdConf; exact ⟨trivial, trivial, hdConf⟩
      | fail msgExpr =>
        dsimp only
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hm : checkExpr prog (envToTyEnv env) [] pc inSpec msgExpr with
        | error _ => simp [hm] at hchk
        | ok mLTy =>
          rcases ihE hprog hsafeProg env [] pc inSpec w msgExpr mLTy henvWf henvSafe henvNs (by rfl) hwWf hesafe hens hm with ⟨hmSafe, hmNs, hmConf⟩
          cases houtM : eval fuel' prog env pc w msgExpr with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtM] at hmSafe hmNs hmConf; exact ⟨hmSafe, hmNs, hmConf⟩
          | ok mv w1 =>
            try dsimp only
            rw [houtM] at hmConf
            dsimp only [outcomeWorldEq] at hmConf
            cases mv <;> (try dsimp only) <;>
              first | exact ⟨trivial, trivial, fun _ => trivial⟩ | exact ⟨trivial, trivial, fun hpcF => hmConf hpcF⟩
    -- 2. JoinLoopSafeAndConfinedAt (fuel' + 1)
    · intro hprog hsafeProg baseEnv curEnv jenv label params joinPc retLTy rLTy inSpec rhs w
        hbaseWf hbaseSafe hbaseNs hcurWf hcurSafe hcurNs hcurTy hjenvSafe hparamsOk hretOk hwWf hrhsSafe hrhsNs hrChk hrTyEq
      unfold evalJoinLoop; dsimp only
      have hjenv'Safe : joinEnvSinksAllowed L ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv) = true := by
        simp only [joinEnvSinksAllowed, List.all_cons, Bool.and_eq_true]
        exact ⟨⟨hparamsOk, hretOk⟩, hjenvSafe⟩
      have hrChk' := hrChk; rw [← hcurTy] at hrChk'
      have hrWf := hsound.2.2.1 hprog curEnv _ joinPc inSpec w rhs rLTy hcurWf hwWf hrChk'
      rcases ihE hprog hsafeProg curEnv _ joinPc inSpec w rhs rLTy hcurWf hcurSafe hcurNs hjenv'Safe hwWf hrhsSafe hrhsNs hrChk' with ⟨hrSafe, hrNs, hrConf⟩
      cases houtR : eval fuel' prog curEnv joinPc w rhs with
      | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel =>
        try dsimp only; rw [houtR] at hrSafe hrNs hrConf; exact ⟨hrSafe, hrNs, hrConf⟩
      | jumped lbl jVals w1 =>
        try dsimp only
        rw [houtR] at hrWf hrSafe hrNs hrConf
        cases hrWf with | @jumped _ _ _ otherSig hlookJ hjValsWf hw1 =>
        cases hlbl : (lbl == label)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hrSafe, hrNs, hrConf⟩
        · simp only [↓reduceIte]
          have heq : label = lbl := (beq_iff_eq.mp hlbl).symm
          simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlookJ
          subst hlookJ
          split
          · exact ⟨trivial, trivial, fun _ => trivial⟩
          · rename_i hlenOk
            simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
            have hjEnvWf := extendEnv_wf hjValsWf hbaseWf
            have hjEnvSafe := extendEnv_safeForNI hparamsOk hrSafe hbaseSafe
            have hjEnvNs := extendEnv_noSpecCalls (params := params) hrNs hbaseNs
            have hjTyEq : envToTyEnv ((List.zip params jVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ baseEnv) =
                extendTyEnv (envToTyEnv baseEnv) params := by
              rw [envToTyEnv_append, envToTyEnv_zip_params params jVals hlenOk, extendTyEnv]
            rcases ihJL hprog hsafeProg baseEnv _ jenv label params joinPc retLTy rLTy inSpec rhs w1
              hbaseWf hbaseSafe hbaseNs hjEnvWf hjEnvSafe hjEnvNs hjTyEq hjenvSafe hparamsOk hretOk hw1 hrhsSafe hrhsNs hrChk hrTyEq with ⟨hjlSafe, hjlNs, hjlConf⟩
            refine ⟨hjlSafe, hjlNs, fun hpcF => ?_⟩
            have hw1Eq : w1 = w := hrConf hpcF; subst hw1Eq
            exact hjlConf hpcF
    -- 3. PlanSafeAndConfinedAt (fuel' + 1)
    · intro hprog hsafeProg env pc inSpec w plan pTy henvWf henvSafe henvNs hwWf hpsafe hpns hchk
      unfold evalPlan
      cases plan with
      | sourceExpr e =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases he : checkExpr prog (envToTyEnv env) [] pc inSpec e with
        | error _ => simp [he] at hchk
        | ok eLTy =>
          rcases ihE hprog hsafeProg env [] pc inSpec w e eLTy henvWf henvSafe henvNs (by rfl) hwWf hpsafe hpns he with ⟨heSafe, heNs, heConf⟩
          cases houtE : eval fuel' prog env pc w e with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            try dsimp only; rw [houtE] at heSafe heNs heConf; exact ⟨heSafe, heNs, heConf⟩
          | ok ev w1 =>
            try dsimp only
            rw [houtE] at heConf
            dsimp only [outcomeWorldEq] at heConf
            cases ev <;> (try dsimp only) <;>
              first | exact ⟨trivial, trivial, fun _ => trivial⟩ | exact ⟨rfl, rfl, fun hpcF => heConf hpcF⟩
      | sourceDB cap tableName schema =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hc : checkExpr prog (envToTyEnv env) [] pc inSpec cap with
        | error _ => simp [hc] at hchk
        | ok capLTy =>
          rcases ihE hprog hsafeProg env [] pc inSpec w cap capLTy henvWf henvSafe henvNs (by rfl) hwWf hpsafe hpns hc with ⟨hcSafe, hcNs, hcConf⟩
          cases houtC : eval fuel' prog env pc w cap with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            try dsimp only; rw [houtC] at hcSafe hcNs hcConf; exact ⟨hcSafe, hcNs, hcConf⟩
          | ok cv w1 =>
            try dsimp only
            rw [houtC] at hcConf
            cases cv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
            case capReadDB h db =>
              refine ⟨?_, ?_, fun hpcF => ?_⟩
              · cases h with
                | real => try dsimp only; split; (split <;> trivial); rfl
                | fake fid =>
                  try dsimp only
                  cases w1.fakeDBs[fid]? <;> try dsimp only
                  · rfl
                  · split; (split <;> trivial); rfl
              · cases h with
                | real => try dsimp only; split; (split <;> trivial); rfl
                | fake fid =>
                  try dsimp only
                  cases w1.fakeDBs[fid]? <;> try dsimp only
                  · rfl
                  · split; (split <;> trivial); rfl
              · have hw1Eq : w1 = w := hcConf hpcF
                rw [hw1Eq]; dsimp only [outcomeWorldEq]
                cases h with
                | real =>
                  dsimp only
                  cases w.realDBTables.find? (fun st => st.db == db && st.tableName == tableName) with
                  | none => rfl
                  | some st =>
                    dsimp only
                    cases decide (st.schema.cols.map ColSpec.ty = schema.cols.map ColSpec.ty) <;> rfl
                | fake fid =>
                  dsimp only
                  cases w.fakeDBs[fid]? with
                  | none => rfl
                  | some fdb =>
                    dsimp only
                    cases fdb.tables.find? (fun st => st.tableName == tableName) with
                    | none => rfl
                    | some st =>
                      dsimp only
                      cases decide (st.schema.cols.map ColSpec.ty = schema.cols.map ColSpec.ty) <;> rfl
      | select inp _ | drop inp _ | rename inp _ | distinct inp _ | sort inp _
      | limit inp _ | groupBy inp _ | suppressSmallGroups inp _ _ _ | crosstab inp _ _ _ _ | redact inp _ _ =>
        dsimp only
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          rcases ihP hprog hsafeProg env pc inSpec w inp inP henvWf henvSafe henvNs hwWf hpsafe hpns hi with ⟨hiSafe, hiNs, hiConf⟩
          cases houtI : evalPlan fuel' prog env pc w inp with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            try dsimp only; rw [houtI] at hiSafe hiNs hiConf; exact ⟨hiSafe, hiNs, hiConf⟩
          | ok iv w1 =>
            try dsimp only
            rw [houtI] at hiConf
            cases iv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
            refine ⟨?_, ?_, fun hpcF => ?_⟩
            · repeat (first | rfl | trivial | split)
            · repeat (first | rfl | trivial | split)
            · have hw1Eq : w1 = w := hiConf hpcF; subst hw1Eq
              repeat (first | rfl | trivial | split)
      | derive inp items =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          rcases ihP hprog hsafeProg env pc inSpec w inp inP henvWf henvSafe henvNs hwWf hpsafe.1 hpns hi with ⟨hiSafe, hiNs, hiConf⟩
          cases houtI : evalPlan fuel' prog env pc w inp with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            try dsimp only; rw [houtI] at hiSafe hiNs hiConf; exact ⟨hiSafe, hiNs, hiConf⟩
          | ok iv w1 =>
            try dsimp only
            rw [houtI] at hiConf
            cases iv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
            rcases evalDeriveItems_world_and_safe (L := L) (prog := prog) (tEnv := envToTyEnv env)
              (evalRowExpr fuel' prog env) w1 _ items with ⟨hdS, hdNs, hdW⟩
            refine ⟨hdS, hdNs, fun hpcF => ?_⟩
            have hw1Eq : w1 = w := hiConf hpcF; subst hw1Eq; exact hdW
      | filter inp pred =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          rcases ihP hprog hsafeProg env pc inSpec w inp inP henvWf henvSafe henvNs hwWf hpsafe.1 hpns hi with ⟨hiSafe, hiNs, hiConf⟩
          cases houtI : evalPlan fuel' prog env pc w inp with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            try dsimp only; rw [houtI] at hiSafe hiNs hiConf; exact ⟨hiSafe, hiNs, hiConf⟩
          | ok iv w1 =>
            try dsimp only
            rw [houtI] at hiConf
            cases iv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
            rcases evalFilterRows_world_and_safe (prog := prog) (L := L) (evalRowExpr fuel' prog env) _ _ pred w1 _ with ⟨hfS, hfNs, hfW⟩
            refine ⟨hfS, hfNs, fun hpcF => ?_⟩
            have hw1Eq : w1 = w := hiConf hpcF; subst hw1Eq; exact hfW
      | join kind leftP rightP on suffixes =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
        simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hl : checkPlan prog (envToTyEnv env) pc inSpec leftP with
        | error _ => simp [hl] at hchk
        | ok lP =>
          simp only [hl] at hchk
          cases hr : checkPlan prog (envToTyEnv env) pc inSpec rightP with
          | error _ => simp [hr] at hchk
          | ok rP =>
            have hlWf := hsound.2.2.2.2 hprog env pc inSpec w leftP lP henvWf hwWf hl
            rcases ihP hprog hsafeProg env pc inSpec w leftP lP henvWf henvSafe henvNs hwWf hpsafe.1 hpns.1 hl with ⟨hlSafe, hlNs, hlConf⟩
            cases houtL : evalPlan fuel' prog env pc w leftP with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              try dsimp only; rw [houtL] at hlSafe hlNs hlConf; exact ⟨hlSafe, hlNs, hlConf⟩
            | ok lv w1 =>
              try dsimp only
              rw [houtL] at hlWf hlConf
              cases hlWf with | ok _ hw1 =>
              cases lv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
              rcases ihP hprog hsafeProg env pc inSpec w1 rightP rP henvWf henvSafe henvNs hw1 hpsafe.2 hpns.2 hr with ⟨hrSafe, hrNs, hrConf⟩
              cases houtR : evalPlan fuel' prog env pc w1 rightP with
              | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
                try dsimp only; rw [houtR] at hrSafe hrNs hrConf
                refine ⟨hrSafe, hrNs, fun hpcF => ?_⟩
                have hw1Eq : w1 = w := hlConf hpcF; subst hw1Eq; exact hrConf hpcF
              | ok rv w2 =>
                try dsimp only
                rw [houtR] at hrConf
                cases rv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
                refine ⟨?_, ?_, fun hpcF => ?_⟩
                · repeat (first | rfl | trivial | split)
                · repeat (first | rfl | trivial | split)
                · have hw2Eq : w2 = w := (hrConf hpcF).trans (hlConf hpcF)
                  subst hw2Eq
                  repeat (first | rfl | trivial | split)
      | union leftP rightP =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
        simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hl : checkPlan prog (envToTyEnv env) pc inSpec leftP with
        | error _ => simp [hl] at hchk
        | ok lP =>
          simp only [hl] at hchk
          cases hr : checkPlan prog (envToTyEnv env) pc inSpec rightP with
          | error _ => simp [hr] at hchk
          | ok rP =>
            have hlWf := hsound.2.2.2.2 hprog env pc inSpec w leftP lP henvWf hwWf hl
            rcases ihP hprog hsafeProg env pc inSpec w leftP lP henvWf henvSafe henvNs hwWf hpsafe.1 hpns.1 hl with ⟨hlSafe, hlNs, hlConf⟩
            cases houtL : evalPlan fuel' prog env pc w leftP with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              try dsimp only; rw [houtL] at hlSafe hlNs hlConf; exact ⟨hlSafe, hlNs, hlConf⟩
            | ok lv w1 =>
              try dsimp only
              rw [houtL] at hlWf hlConf
              cases hlWf with | ok _ hw1 =>
              cases lv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
              rcases ihP hprog hsafeProg env pc inSpec w1 rightP rP henvWf henvSafe henvNs hw1 hpsafe.2 hpns.2 hr with ⟨hrSafe, hrNs, hrConf⟩
              cases houtR : evalPlan fuel' prog env pc w1 rightP with
              | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
                try dsimp only; rw [houtR] at hrSafe hrNs hrConf
                refine ⟨hrSafe, hrNs, fun hpcF => ?_⟩
                have hw1Eq : w1 = w := hlConf hpcF; subst hw1Eq; exact hrConf hpcF
              | ok rv w2 =>
                try dsimp only
                rw [houtR] at hrConf
                cases rv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
                refine ⟨?_, ?_, fun hpcF => ?_⟩
                · split <;> trivial
                · split <;> trivial
                · have hw2Eq : w2 = w := (hrConf hpcF).trans (hlConf hpcF)
                  subst hw2Eq; split <;> trivial
      | summarize inp aggs distinctKey =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
        rw [checkPlan_inSpec_true hchk]; try dsimp only
        cases pTy with
        | dynamic _ => try dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
        | table outTT =>
          try dsimp only
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
          | error _ => simp [hi] at hchk
          | ok inP =>
            rcases ihP hprog hsafeProg env pc inSpec w inp inP henvWf henvSafe henvNs hwWf hpsafe.1 hpns hi with ⟨hiSafe, hiNs, hiConf⟩
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              try dsimp only; rw [houtI] at hiSafe hiNs hiConf; exact ⟨hiSafe, hiNs, hiConf⟩
            | ok iv w1 =>
              try dsimp only
              rw [houtI] at hiConf
              cases iv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
              split
              · exact ⟨trivial, trivial, fun _ => trivial⟩
              · cases extractAllRowsKeyVals _ _ _ with
                | none => try dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
                | some rawKeys =>
                  try dsimp only
                  rcases evalSummarizeGroups_world_and_safe (prog := prog) (L := L) (evalRowExpr fuel' prog env)
                    _ _ distinctKey _ aggs _ outTT.cols w1 _ with ⟨hsS, hsNs, hsW⟩
                  refine ⟨hsS, hsNs, fun hpcF => ?_⟩
                  have hw1Eq : w1 = w := hiConf hpcF; subst hw1Eq; exact hsW
      | window inp _ | fillGaps inp _ _ _ _ | pivotWider inp _ _ _ _ =>
        dsimp only
        rw [checkPlan_inSpec_true hchk]; try dsimp only
        cases pTy with
        | dynamic _ => try dsimp only; exact ⟨trivial, trivial, fun _ => trivial⟩
        | table outTT =>
          try dsimp only
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
          | error _ => simp [hi] at hchk
          | ok inP =>
            rcases ihP hprog hsafeProg env pc inSpec w inp inP henvWf henvSafe henvNs hwWf hpsafe hpns hi with ⟨hiSafe, hiNs, hiConf⟩
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              try dsimp only; rw [houtI] at hiSafe hiNs hiConf; exact ⟨hiSafe, hiNs, hiConf⟩
            | ok iv w1 =>
              try dsimp only
              rw [houtI] at hiConf
              cases iv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
              refine ⟨?_, ?_, fun hpcF => ?_⟩
              · repeat (first | rfl | trivial | split)
              · repeat (first | rfl | trivial | split)
              · have hw1Eq : w1 = w := hiConf hpcF; subst hw1Eq
                repeat (first | rfl | trivial | split)
      | pseudonymize inp col secretExpr =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
        simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
        unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
        cases hi : checkPlan prog (envToTyEnv env) pc inSpec inp with
        | error _ => simp [hi] at hchk
        | ok inP =>
          simp only [hi] at hchk
          cases hs : checkExpr prog (envToTyEnv env) [] pc inSpec secretExpr with
          | error _ => simp [hs] at hchk
          | ok secLTy =>
            have hiWf := hsound.2.2.2.2 hprog env pc inSpec w inp inP henvWf hwWf hi
            rcases ihP hprog hsafeProg env pc inSpec w inp inP henvWf henvSafe henvNs hwWf hpsafe.1.2 hpns.1 hi with ⟨hiSafe, hiNs, hiConf⟩
            cases houtI : evalPlan fuel' prog env pc w inp with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              try dsimp only; rw [houtI] at hiSafe hiNs hiConf; exact ⟨hiSafe, hiNs, hiConf⟩
            | ok iv w1 =>
              try dsimp only
              rw [houtI] at hiWf hiConf
              cases hiWf with | ok _ hw1 =>
              cases iv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
              rcases ihE hprog hsafeProg env [] pc inSpec w1 secretExpr secLTy henvWf henvSafe henvNs (by rfl) hw1 hpsafe.2 hpns.2 hs with ⟨hsSafe, hsNs, hsConf⟩
              cases houtS : eval fuel' prog env pc w1 secretExpr with
              | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
                try dsimp only; rw [houtS] at hsSafe hsNs hsConf
                refine ⟨hsSafe, hsNs, fun hpcF => ?_⟩
                have hw1Eq : w1 = w := hiConf hpcF; subst hw1Eq; exact hsConf hpcF
              | ok sv w2 =>
                try dsimp only
                rw [houtS] at hsConf
                cases sv <;> (try dsimp only) <;> try exact ⟨trivial, trivial, fun _ => trivial⟩
                refine ⟨?_, ?_, fun hpcF => ?_⟩
                · repeat (first | rfl | trivial | split)
                · repeat (first | rfl | trivial | split)
                · have hw2Eq : w2 = w := (hsConf hpcF).trans (hiConf hpcF)
                  subst hw2Eq
                  repeat (first | rfl | trivial | split)


/-! ## `L`-Indistinguishability (`≈_L`) on Rows, Tables, Values, Environments & Worlds -/

private theorem congrArg2 {α β γ : Type} (f : α → β → γ) {a1 a2 : α} {b1 b2 : β}
    (ha : a1 = a2) (hb : b1 = b2) : f a1 b1 = f a2 b2 := by
  subst ha; subst hb; rfl

inductive CellsEquiv (L : TagSet) : List ColSpec → List Val → List Val → Prop where
  | nil : CellsEquiv L [] [] []
  | cons {c : ColSpec} {cs : List ColSpec} {v1 v2 : Val} {vs1 vs2 : List Val}
      (hcell : c.tags.subset L = true → v1 = v2)
      (htl : CellsEquiv L cs vs1 vs2) :
      CellsEquiv L (c :: cs) (v1 :: vs1) (v2 :: vs2)

def RowEquiv (L : TagSet) (cols : List ColSpec) (r1 r2 : TableRow) : Prop :=
  CellsEquiv L cols r1.cells r2.cells

theorem CellsEquiv.refl (L : TagSet) :
    ∀ {cols : List ColSpec} {vs : List Val}, CellsWf prog vs cols → CellsEquiv L cols vs vs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons _ htl => .cons (fun _ => rfl) (CellsEquiv.refl L htl)

theorem CellsEquiv.symm {L : TagSet} :
    ∀ {cols : List ColSpec} {vs1 vs2 : List Val},
      CellsEquiv L cols vs1 vs2 → CellsEquiv L cols vs2 vs1
  | [], [], [], .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hc htl => .cons (fun hl => (hc hl).symm) htl.symm

theorem CellsEquiv.trans {L : TagSet} :
    ∀ {cols : List ColSpec} {vs1 vs2 vs3 : List Val},
      CellsEquiv L cols vs1 vs2 → CellsEquiv L cols vs2 vs3 → CellsEquiv L cols vs1 vs3
  | [], [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons h1 htl1, .cons h2 htl2 =>
    .cons (fun hl => (h1 hl).trans (h2 hl)) (htl1.trans htl2)

theorem CellsEquiv.length_eq {L : TagSet} :
    ∀ {cols : List ColSpec} {vs1 vs2 : List Val},
      CellsEquiv L cols vs1 vs2 → vs1.length = cols.length ∧ vs2.length = cols.length
  | [], [], [], .nil => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, .cons _ htl =>
    ⟨congrArg (· + 1) htl.length_eq.1, congrArg (· + 1) htl.length_eq.2⟩

theorem CellsEquiv.all_low_eq {L : TagSet} :
    ∀ {cols : List ColSpec} {vs1 vs2 : List Val},
      (∀ c ∈ cols, c.tags.subset L = true) →
      CellsEquiv L cols vs1 vs2 →
      vs1 = vs2
  | [], [], [], _, .nil => rfl
  | c :: _, _ :: _, _ :: _, hall, .cons hcell htl =>
    congrArg2 List.cons (hcell (hall c (.head _)))
      (CellsEquiv.all_low_eq (fun d hd => hall d (.tail _ hd)) htl)

theorem CellsEquiv.getElem?_eq {L : TagSet} :
    ∀ {cols : List ColSpec} {vs1 vs2 : List Val} {idx : Nat} {c : ColSpec},
      CellsEquiv L cols vs1 vs2 →
      cols[idx]? = some c →
      c.tags.subset L = true →
      vs1[idx]? = vs2[idx]?
  | _ :: _, _ :: _, _ :: _, 0, _, .cons hcell _, hcol, hlow => by
    injection hcol with h; subst h; simp [hcell hlow]
  | _ :: _, _ :: _, _ :: _, n + 1, _, .cons _ htl, hcol, hlow =>
    htl.getElem?_eq hcol hlow

/-- Relational `Table` `L`-equivalence accounting for all three sensitivity dimensions:
    column-level `c.tags`, row-presence/count `tt.rowTags`, and row-ordering `tt.orderTags`
    (allowing arbitrary row permutations when `tt.orderTags ⊈ L`). -/
structure TableEquiv (prog : Program) (L : TagSet) (tv1 tv2 : TableVal) (tt : TableTy) : Prop where
  wf1 : ValWf prog (.table tv1) (.table tt)
  wf2 : ValWf prog (.table tv2) (.table tt)
  groupingLow : tt.rowTags.subset L = true →
    ∀ c ∈ tt.cols, c.aggKind = .groupKey → c.tags.subset L = true
  lowRows : tt.rowTags.subset L = true →
    if tt.orderTags.subset L = true then
      RelList (RowEquiv L tt.cols) tv1.rows tv2.rows
    else
      ∃ rows1', List.Perm tv1.rows rows1' ∧ RelList (RowEquiv L tt.cols) rows1' tv2.rows
  sumMetaEq : tt.summarized = true → tt.rowTags.subset L = true →
    if tt.orderTags.subset L = true then
      RelList (fun r1 r2 => RowEquiv L tt.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta) tv1.rows tv2.rows
    else
      ∃ rows1', List.Perm tv1.rows rows1' ∧
        RelList (fun r1 r2 => RowEquiv L tt.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta) rows1' tv2.rows

theorem TableEquiv.perm_rows {prog : Program} {L : TagSet} {tv1 tv2 : TableVal} {tt : TableTy}
    (ht : TableEquiv prog L tv1 tv2 tt) (hr : tt.rowTags.subset L = true) :
    ∃ rows1', List.Perm tv1.rows rows1' ∧ RelList (RowEquiv L tt.cols) rows1' tv2.rows := by
  have h := ht.lowRows hr
  split at h
  · exact ⟨tv1.rows, .refl _, h⟩
  · exact h

theorem TableEquiv.length_eq {prog : Program} {L : TagSet} {tv1 tv2 : TableVal} {tt : TableTy}
    (ht : TableEquiv prog L tv1 tv2 tt) (hr : tt.rowTags.subset L = true) :
    tv1.rows.length = tv2.rows.length := by
  rcases ht.perm_rows hr with ⟨rows1', hp, hf⟩
  exact hp.length_eq.trans hf.length_eq

theorem TableEquiv.cols_eq {prog : Program} {L : TagSet} {tv1 tv2 : TableVal} {tt : TableTy}
    (ht : TableEquiv prog L tv1 tv2 tt) :
    tv1.cols = tt.cols ∧ tv2.cols = tt.cols := by
  cases ht.wf1 with | table hc1 _ _ =>
  cases ht.wf2 with | table hc2 _ _ =>
  exact ⟨hc1, hc2⟩

theorem TableEquiv.totalTags_cells_eq {prog : Program} {L : TagSet} {tv1 tv2 : TableVal} {tt : TableTy}
    (ht : TableEquiv prog L tv1 tv2 tt)
    (htot : tt.totalTags.subset L = true) :
    tv1.cols = tv2.cols ∧ tv1.rows.map TableRow.cells = tv2.rows.map TableRow.cells := by
  unfold TableTy.totalTags TableTy.allColTags at htot
  simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at htot
  rcases htot with ⟨⟨hrLow, hoLow⟩, hcAll⟩
  have hcolsLow : ∀ c ∈ tt.cols, c.tags.subset L = true :=
    fun c hc => hcAll c.tags (List.mem_map_of_mem hc)
  have hlr := ht.lowRows hrLow
  simp only [hoLow, ↓reduceIte] at hlr
  rcases ht.cols_eq with ⟨hc1, hc2⟩
  refine ⟨hc1.trans hc2.symm, ?_⟩
  clear ht hc1 hc2
  generalize tv1.rows = rs1, tv2.rows = rs2 at hlr ⊢
  induction hlr with
  | nil => rfl
  | @cons r1 r2 _ _ hr htl ih =>
    simp only [List.map_cons]
    exact congrArg2 List.cons (CellsEquiv.all_low_eq hcolsLow hr) ih

mutual
inductive ValPayloadEquiv (prog : Program) (L : TagSet) : Val → Val → Ty → Prop where
  | unit : ValPayloadEquiv prog L .unit .unit .unit
  | bool (b : Bool) : ValPayloadEquiv prog L (.bool b) (.bool b) .bool
  | int (n : Int) : ValPayloadEquiv prog L (.int n) (.int n) .int
  | decimal (d : Int) : ValPayloadEquiv prog L (.decimal d) (.decimal d) .decimal
  | float (f : Float64) : ValPayloadEquiv prog L (.float f) (.float f) .float
  | text (s : String) : ValPayloadEquiv prog L (.text s) (.text s) .text
  | bytes (bs : List UInt8) : ValPayloadEquiv prog L (.bytes bs) (.bytes bs) .bytes
  | date (d : Int) : ValPayloadEquiv prog L (.date d) (.date d) .date
  | timestamp (ts : Int) : ValPayloadEquiv prog L (.timestamp ts) (.timestamp ts) .timestamp
  | duration (dur : Int) : ValPayloadEquiv prog L (.duration dur) (.duration dur) .duration
  | optNone (inner : Ty) : ValPayloadEquiv prog L .optNone .optNone (.option inner)
  | optSome {v1 v2 : Val} {inner : Ty} (hv : ValPayloadEquiv prog L v1 v2 inner) :
      ValPayloadEquiv prog L (.optSome v1) (.optSome v2) (.option inner)
  | resOk {v1 v2 : Val} {okTy errTy : Ty} (hv : ValPayloadEquiv prog L v1 v2 okTy) :
      ValPayloadEquiv prog L (.resOk v1) (.resOk v2) (.result okTy errTy)
  | resErr {e1 e2 : Val} {okTy errTy : Ty} (he : ValPayloadEquiv prog L e1 e2 errTy) :
      ValPayloadEquiv prog L (.resErr e1) (.resErr e2) (.result okTy errTy)
  | tuple {vs1 vs2 : List Val} {ltys : List LTy}
      (hvs : ValListEquiv prog L vs1 vs2 ltys) :
      ValPayloadEquiv prog L (.tuple vs1) (.tuple vs2) (.tuple ltys)
  | list {vs1 vs2 : List Val} {elem : LTy}
      (hvs : ValAllEquiv prog L vs1 vs2 elem) :
      ValPayloadEquiv prog L (.list vs1) (.list vs2) (.list elem)
  | map {kvs1 kvs2 : List (Val × Val)} {kLTy vLTy : LTy}
      (hkvs : ValPairsEquiv prog L kvs1 kvs2 kLTy vLTy) :
      ValPayloadEquiv prog L (.map kvs1) (.map kvs2) (.map kLTy vLTy)
  | ctor {dName cName : Ident} {vs1 vs2 : List Val} {dDecl : DataDecl} {cDecl : CtorDecl}
      (hd : prog.findData? dName = some dDecl)
      (hc : dDecl.ctors.find? (fun c => c.name == cName) = some cDecl)
      (heq : vs1 = vs2)
      (hvs : ValListEquiv prog L vs1 vs2 cDecl.fields) :
      ValPayloadEquiv prog L (.ctor dName cName vs1) (.ctor dName cName vs2) (.data dName)
  | table {tv1 tv2 : TableVal} {tt : TableTy}
      (ht : TableEquiv prog L tv1 tv2 tt) :
      ValPayloadEquiv prog L (.table tv1) (.table tv2) (.table tt)
  | dynTable {hs1 : List String} {rs1 : List (List Val)}
      {hs2 : List String} {rs2 : List (List Val)} {ts : TagSet}
      (hlow : ts.subset L = true → hs1 = hs2 ∧ rs1 = rs2) :
      ValPayloadEquiv prog L (.dynTable hs1 rs1) (.dynTable hs2 rs2) (.dynamicTable ts)
  | chart {cv1 cv2 : ChartVal} {ts : TagSet}
      (hlow : ts.subset L = true → cv1 = cv2) :
      ValPayloadEquiv prog L (.chart cv1) (.chart cv2) (.chart ts)
  | report {rv1 rv2 : ReportVal} {ts : TagSet}
      (hlow : ts.subset L = true → rv1 = rv2) :
      ValPayloadEquiv prog L (.report rv1) (.report rv2) (.report ts)
  | profile {pv1 pv2 : ProfileVal} {ts : TagSet}
      (hlow : ts.subset L = true → pv1 = pv2) :
      ValPayloadEquiv prog L (.profile pv1) (.profile pv2) (.profile ts)
  | linearModel (s i r2 : Float64) :
      ValPayloadEquiv prog L (.linearModel s i r2) (.linearModel s i r2) .linearModel
  | statTest (s p : Float64) :
      ValPayloadEquiv prog L (.statTest s p) (.statTest s p) .statTest
  | closure {params : List (Ident × LTy)} {fnPc : TagSet} {retLTy : LTy}
      {body : Expr} {capEnv1 capEnv2 : Env}
      (henv : EnvEquiv prog L capEnv1 capEnv2) :
      ValPayloadEquiv prog L
        (.closure params fnPc retLTy body capEnv1)
        (.closure params fnPc retLTy body capEnv2)
        (.fn (params.map Prod.snd) fnPc retLTy)
  | capArgs : ValPayloadEquiv prog L .capArgs .capArgs .args
  | capClock : ValPayloadEquiv prog L .capClock .capClock .clock
  | capConsole (h : CapHandle) (allows : TagSet) :
      ValPayloadEquiv prog L (.capConsole h allows) (.capConsole h allows) (.console allows)
  | capReadFiles (h : CapHandle) :
      ValPayloadEquiv prog L (.capReadFiles h) (.capReadFiles h) .readFiles
  | capWriteFiles (h : CapHandle) (root : String) (allows : TagSet) :
      ValPayloadEquiv prog L (.capWriteFiles h root allows) (.capWriteFiles h root allows) (.writeFiles root allows)
  | capReadDB (h : CapHandle) (db : Ident) :
      ValPayloadEquiv prog L (.capReadDB h db) (.capReadDB h db) (.readDB db)
  | capWriteTable (h : CapHandle) (db tbl : Ident) (cols : List ColSpec) (rt allows : TagSet) :
      ValPayloadEquiv prog L (.capWriteTable h db tbl) (.capWriteTable h db tbl) (.writeTable db tbl cols rt allows)
  | capRawReadDB (db : Ident) :
      ValPayloadEquiv prog L (.capRawReadDB db) (.capRawReadDB db) (.rawReadDB db)
  | capHttpsAllow (h : CapHandle) (host : String) (allows : TagSet) :
      ValPayloadEquiv prog L (.capHttpsAllow h host allows) (.capHttpsAllow h host allows) (.httpsAllow host allows)
  | capSecret (h : CapHandle) (name : String) :
      ValPayloadEquiv prog L (.capSecret h name) (.capSecret h name) (.secret name)
  | capDeclassify (allows : TagSet) :
      ValPayloadEquiv prog L (.capDeclassify allows) (.capDeclassify allows) (.declassify allows)

inductive ValEquiv (prog : Program) (L : TagSet) : Val → Val → LTy → Prop where
  | high {v1 v2 : Val} {lty : LTy}
      (hhigh : lty.tags.subset L = false)
      (hwf1 : ValWf prog v1 lty.ty)
      (hwf2 : ValWf prog v2 lty.ty)
      (hsafe1 : valSafeForNI L v1 = true)
      (hsafe2 : valSafeForNI L v2 = true) :
      ValEquiv prog L v1 v2 lty
  | low {v1 v2 : Val} {lty : LTy}
      (hlow : lty.tags.subset L = true)
      (hwf1 : ValWf prog v1 lty.ty)
      (hwf2 : ValWf prog v2 lty.ty)
      (hsafe1 : valSafeForNI L v1 = true)
      (hsafe2 : valSafeForNI L v2 = true)
      (hpay : ValPayloadEquiv prog L v1 v2 lty.ty) :
      ValEquiv prog L v1 v2 lty

inductive ValListEquiv (prog : Program) (L : TagSet) : List Val → List Val → List LTy → Prop where
  | nil : ValListEquiv prog L [] [] []
  | cons {v1 v2 vs1 vs2 l ls}
      (hv : ValEquiv prog L v1 v2 l)
      (htl : ValListEquiv prog L vs1 vs2 ls) :
      ValListEquiv prog L (v1 :: vs1) (v2 :: vs2) (l :: ls)

inductive ValAllEquiv (prog : Program) (L : TagSet) : List Val → List Val → LTy → Prop where
  | nil (elem : LTy) : ValAllEquiv prog L [] [] elem
  | cons {v1 v2 vs1 vs2 elem}
      (hv : ValEquiv prog L v1 v2 elem)
      (htl : ValAllEquiv prog L vs1 vs2 elem) :
      ValAllEquiv prog L (v1 :: vs1) (v2 :: vs2) elem

inductive ValPairsEquiv (prog : Program) (L : TagSet) :
    List (Val × Val) → List (Val × Val) → LTy → LTy → Prop where
  | nil (kLTy vLTy : LTy) : ValPairsEquiv prog L [] [] kLTy vLTy
  | cons {k1 v1 k2 v2 r1 r2 kLTy vLTy}
      (hk : ValEquiv prog L k1 k2 kLTy)
      (hv : ValEquiv prog L v1 v2 vLTy)
      (htl : ValPairsEquiv prog L r1 r2 kLTy vLTy) :
      ValPairsEquiv prog L ((k1, v1) :: r1) ((k2, v2) :: r2) kLTy vLTy

inductive EnvEquiv (prog : Program) (L : TagSet) : Env → Env → Prop where
  | nil : EnvEquiv prog L [] []
  | cons {name : Ident} {lty : LTy} {v1 v2 : Val} {rest1 rest2 : Env}
      (hsink : ltySinksAllowed L lty = true)
      (hv : ValEquiv prog L v1 v2 lty)
      (htl : EnvEquiv prog L rest1 rest2) :
      EnvEquiv prog L ({ name := name, lty := lty, val := v1 } :: rest1)
                      ({ name := name, lty := lty, val := v2 } :: rest2)
end

/-! ### Structural Lemmas on `ValEquiv` and `EnvEquiv` -/

theorem ValEquiv.wf_left {prog L v1 v2 lty} (h : ValEquiv prog L v1 v2 lty) :
    ValWf prog v1 lty.ty := by
  cases h <;> assumption

theorem ValEquiv.wf_right {prog L v1 v2 lty} (h : ValEquiv prog L v1 v2 lty) :
    ValWf prog v2 lty.ty := by
  cases h <;> assumption

theorem ValEquiv.safe_left {prog L v1 v2 lty} (h : ValEquiv prog L v1 v2 lty) :
    valSafeForNI L v1 = true := by
  cases h <;> assumption

theorem ValEquiv.safe_right {prog L v1 v2 lty} (h : ValEquiv prog L v1 v2 lty) :
    valSafeForNI L v2 = true := by
  cases h <;> assumption

theorem ValEquiv.payload {prog L v1 v2 lty} (h : ValEquiv prog L v1 v2 lty)
    (hlow : lty.tags.subset L = true) :
    ValPayloadEquiv prog L v1 v2 lty.ty := by
  cases h with
  | high hh _ _ _ _ => rw [hlow] at hh; nomatch hh
  | low _ _ _ _ _ hp => exact hp

theorem ValEquiv.mk_smart {prog L v1 v2 lty}
    (hwf1 : ValWf prog v1 lty.ty) (hwf2 : ValWf prog v2 lty.ty)
    (hsafe1 : valSafeForNI L v1 = true) (hsafe2 : valSafeForNI L v2 = true)
    (hpay : lty.tags.subset L = true → ValPayloadEquiv prog L v1 v2 lty.ty) :
    ValEquiv prog L v1 v2 lty := by
  cases hsub : lty.tags.subset L
  · exact .high hsub hwf1 hwf2 hsafe1 hsafe2
  · exact .low hsub hwf1 hwf2 hsafe1 hsafe2 (hpay hsub)

theorem ValEquiv.addTags {prog L v1 v2 lty} (extra : TagSet)
    (h : ValEquiv prog L v1 v2 lty) :
    ValEquiv prog L v1 v2 (lty.addTags extra) := by
  cases lty with | mk ty ts =>
  dsimp only [LTy.addTags]
  apply ValEquiv.mk_smart (lty := LTy.mk ty (ts.union extra)) h.wf_left h.wf_right h.safe_left h.safe_right
  intro hlow
  simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
  exact h.payload hlow.1

theorem ValEquiv.subtype {prog L v1 v2 sub sup}
    (hsub : ltySubtype sub sup = true)
    (h : ValEquiv prog L v1 v2 sub) :
    ValEquiv prog L v1 v2 sup := by
  simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
  rcases hsub with ⟨hty, htags⟩
  apply ValEquiv.mk_smart (hty ▸ h.wf_left) (hty ▸ h.wf_right) h.safe_left h.safe_right
  intro hlow
  exact hty ▸ h.payload (TagSet.subset_trans htags hlow)

theorem ValListEquiv.length_eq {prog L} :
    ∀ {vs1 vs2 ltys}, ValListEquiv prog L vs1 vs2 ltys →
      vs1.length = ltys.length ∧ vs2.length = ltys.length
  | [], [], [], .nil => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, .cons _ htl =>
    ⟨congrArg (· + 1) htl.length_eq.1, congrArg (· + 1) htl.length_eq.2⟩

theorem EnvEquiv.envToTyEnv_eq {prog L} :
    ∀ {env1 env2}, EnvEquiv prog L env1 env2 → envToTyEnv env1 = envToTyEnv env2
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ _ htl => by
    simp only [envToTyEnv, List.map_cons]
    exact congrArg _ htl.envToTyEnv_eq

theorem EnvEquiv.wf_left {prog L} :
    ∀ {env1 env2}, EnvEquiv prog L env1 env2 → EnvWf prog env1
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons _ hv htl => .cons hv.wf_left htl.wf_left

theorem EnvEquiv.wf_right {prog L} :
    ∀ {env1 env2}, EnvEquiv prog L env1 env2 → EnvWf prog env2
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons _ hv htl => .cons hv.wf_right htl.wf_right

theorem EnvEquiv.safe_left {prog L} :
    ∀ {env1 env2}, EnvEquiv prog L env1 env2 → envSafeForNI L env1 = true
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hsink hv htl => by
    simp [envSafeForNI, hsink, hv.safe_left, htl.safe_left]

theorem EnvEquiv.safe_right {prog L} :
    ∀ {env1 env2}, EnvEquiv prog L env1 env2 → envSafeForNI L env2 = true
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hsink hv htl => by
    simp [envSafeForNI, hsink, hv.safe_right, htl.safe_right]

theorem EnvEquiv.lookup {prog L} :
    ∀ {env1 env2 : Env} {name : Ident} {lty : LTy},
      EnvEquiv prog L env1 env2 →
      lookupTyEnv (envToTyEnv env1) name = some lty →
      ∃ v1 v2,
        lookupEnv env1 name = some (lty, v1) ∧
        lookupEnv env2 name = some (lty, v2) ∧
        ValEquiv prog L v1 v2 lty
  | [], [], _, _, .nil, hlook => by simp [envToTyEnv, lookupTyEnv] at hlook
  | _ :: _, _ :: _, name, _, .cons _ hv htl, hlook => by
    simp only [envToTyEnv, List.map_cons, lookupTyEnv] at hlook
    simp only [lookupEnv]
    split at hlook
    · rename_i heq
      injection hlook with hl; subst hl
      simp only [heq, ↓reduceIte]
      exact ⟨_, _, rfl, rfl, hv⟩
    · rename_i hne
      simp only [hne, ↓reduceIte]
      exact htl.lookup hlook

theorem EnvEquiv.append {prog L} :
    ∀ {a1 a2 b1 b2 : Env},
      EnvEquiv prog L a1 a2 → EnvEquiv prog L b1 b2 →
      EnvEquiv prog L (a1 ++ b1) (a2 ++ b2)
  | [], [], _, _, .nil, hb => hb
  | _ :: _, _ :: _, _, _, .cons hsink hv htl, hb =>
    .cons hsink hv (htl.append hb)

/-! ### Golden Bridge Lemma (`stripGroupMeta` & `LTy.effectiveTags ⊆ L`) -/

mutual
def stripGroupMeta (v : Val) : Val :=
  match v with
  | .optSome u => .optSome (stripGroupMeta u)
  | .resOk u => .resOk (stripGroupMeta u)
  | .resErr e => .resErr (stripGroupMeta e)
  | .tuple vs => .tuple (stripGroupMetaList vs)
  | .list vs => .list (stripGroupMetaList vs)
  | .map kvs => .map (stripGroupMetaPairs kvs)
  | .ctor tn cn fs => .ctor tn cn (stripGroupMetaList fs)
  | .table (.mk cols rows) =>
    .table { cols := cols, rows := rows.map (fun r => { cells := r.cells, groupMeta := none }) }
  | other => other
  termination_by structural v

def stripGroupMetaList (vs : List Val) : List Val :=
  match vs with
  | [] => []
  | u :: rest => stripGroupMeta u :: stripGroupMetaList rest
  termination_by structural vs

def stripGroupMetaPairs (rest : List (Val × Val)) : List (Val × Val) :=
  match rest with
  | [] => []
  | (k, u) :: tl => (stripGroupMeta k, stripGroupMeta u) :: stripGroupMetaPairs tl
  termination_by structural rest
end

mutual
theorem stripGroupMeta_eq_of_sortable :
    ∀ {v : Val}, SortableVal v → stripGroupMeta v = v
  | _, .optNone | _, .unit | _, .bool _ | _, .int _ | _, .decimal _ | _, .float _
  | _, .text _ | _, .bytes _ | _, .date _ | _, .timestamp _ | _, .duration _
  | _, .linearModel _ _ _ | _, .statTest _ _ => rfl
  | _, .optSome hv => congrArg Val.optSome (stripGroupMeta_eq_of_sortable hv)
  | _, .resOk hv => congrArg Val.resOk (stripGroupMeta_eq_of_sortable hv)
  | _, .resErr he => congrArg Val.resErr (stripGroupMeta_eq_of_sortable he)
  | _, .tuple hvs => congrArg Val.tuple (stripGroupMetaList_eq_of_sortable hvs)
  | _, .list hvs => congrArg Val.list (stripGroupMetaList_eq_of_sortable hvs)
  | _, .ctor tn cn hfs => congrArg (Val.ctor tn cn) (stripGroupMetaList_eq_of_sortable hfs)

theorem stripGroupMetaList_eq_of_sortable :
    ∀ {vs : List Val}, SortableValList vs → stripGroupMetaList vs = vs
  | [], .nil => rfl
  | _ :: _, .cons hv hvs =>
    congrArg2 List.cons (stripGroupMeta_eq_of_sortable hv) (stripGroupMetaList_eq_of_sortable hvs)
end

private theorem valTableRowsEq_map_reset :
    ∀ (r1 r2 : List TableRow),
      valTableRowsEq (r1.map (fun r => { cells := r.cells, groupMeta := none }))
                     (r2.map (fun r => { cells := r.cells, groupMeta := none })) =
      valTableRowsEq r1 r2
  | [], [] => rfl
  | [], _ :: _ => by simp [valTableRowsEq]
  | _ :: _, [] => by simp [valTableRowsEq]
  | .mk c1 _ :: rs1, .mk c2 _ :: rs2 => by
    simp [valTableRowsEq, valTableRowsEq_map_reset rs1 rs2]

private def valTagIdx : Val → Nat
  | .unit => 0 | .bool _ => 1 | .int _ => 2 | .decimal _ => 3 | .float _ => 4
  | .text _ => 5 | .bytes _ => 6 | .date _ => 7 | .timestamp _ => 8 | .duration _ => 9
  | .optNone => 10 | .optSome _ => 11 | .resOk _ => 12 | .resErr _ => 13
  | .tuple _ => 14 | .list _ => 15 | .map _ => 16 | .ctor _ _ _ => 17 | .table _ => 18
  | .dynTable _ _ => 19 | .chart _ => 20 | .report _ => 21 | .profile _ => 22
  | .linearModel _ _ _ => 23 | .statTest _ _ => 24 | .closure _ _ _ _ _ => 25
  | .capArgs => 26 | .capClock => 27 | .capConsole _ _ => 28 | .capReadFiles _ => 29
  | .capWriteFiles _ _ _ => 30 | .capReadDB _ _ => 31 | .capWriteTable _ _ _ => 32
  | .capRawReadDB _ => 33 | .capHttpsAllow _ _ _ => 34 | .capSecret _ _ => 35
  | .capDeclassify _ => 36

private theorem valTagIdx_stripGroupMeta (v : Val) : valTagIdx (stripGroupMeta v) = valTagIdx v := by
  cases v <;> (try cases ‹TableVal›) <;> rfl

private theorem valEq_false_of_tagIdx_ne {v1 v2 : Val} (h : valTagIdx v1 ≠ valTagIdx v2) :
    valEq v1 v2 = false := by
  cases v1 <;> cases v2 <;> simp only [valTagIdx] at h <;> (try contradiction) <;>
    (try cases ‹TableVal›) <;> simp [valEq]

mutual
theorem valEq_stripGroupMeta :
    ∀ (v1 v2 : Val), valEq (stripGroupMeta v1) (stripGroupMeta v2) = valEq v1 v2
  | v1, v2 => by
    by_cases h : valTagIdx v1 = valTagIdx v2
    · cases v1 <;> cases v2 <;> simp only [valTagIdx] at h <;> try contradiction
      case optSome.optSome a b => exact valEq_stripGroupMeta a b
      case resOk.resOk a b => exact valEq_stripGroupMeta a b
      case resErr.resErr a b => exact valEq_stripGroupMeta a b
      case tuple.tuple as1 bs1 => exact valListEq_stripGroupMeta as1 bs1
      case list.list as1 bs1 => exact valListEq_stripGroupMeta as1 bs1
      case map.map as1 bs1 => exact valPairsEq_stripGroupMeta as1 bs1
      case ctor.ctor tn1 cn1 fs1 tn2 cn2 fs2 =>
        simp [stripGroupMeta, valEq, valListEq_stripGroupMeta fs1 fs2]
      case table.table tv1 tv2 =>
        cases tv1 with | mk c1 r1 =>
        cases tv2 with | mk c2 r2 =>
        simp [stripGroupMeta, valEq, valTableRowsEq_map_reset r1 r2]
      all_goals rfl
    · have hs : valTagIdx (stripGroupMeta v1) ≠ valTagIdx (stripGroupMeta v2) := by
        rwa [valTagIdx_stripGroupMeta, valTagIdx_stripGroupMeta]
      rw [valEq_false_of_tagIdx_ne hs, valEq_false_of_tagIdx_ne h]
  termination_by v1 => sizeOf v1

theorem valListEq_stripGroupMeta :
    ∀ (xs ys : List Val), valListEq (stripGroupMetaList xs) (stripGroupMetaList ys) = valListEq xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as1, b :: bs1 => by
    simp [stripGroupMetaList, valListEq, valEq_stripGroupMeta a b, valListEq_stripGroupMeta as1 bs1]
  termination_by xs => sizeOf xs

theorem valPairsEq_stripGroupMeta :
    ∀ (xs ys : List (Val × Val)),
      valPairsEq (stripGroupMetaPairs xs) (stripGroupMetaPairs ys) = valPairsEq xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (k1, v1) :: r1, (k2, v2) :: r2 => by
    simp [stripGroupMetaPairs, valPairsEq, valEq_stripGroupMeta k1 k2, valEq_stripGroupMeta v1 v2,
      valPairsEq_stripGroupMeta r1 r2]
  termination_by xs => sizeOf xs
end

mutual
theorem renderPublicVal_stripGroupMeta (v : Val) :
    renderPublicVal (stripGroupMeta v) = renderPublicVal v := by
  cases v with
  | optSome u => simp [stripGroupMeta, renderPublicVal, renderPublicVal_stripGroupMeta u]
  | resOk u => simp [stripGroupMeta, renderPublicVal, renderPublicVal_stripGroupMeta u]
  | resErr e => simp [stripGroupMeta, renderPublicVal, renderPublicVal_stripGroupMeta e]
  | tuple vs => simp [stripGroupMeta, renderPublicVal, renderPublicVal_stripGroupMeta_list vs]
  | list vs => simp [stripGroupMeta, renderPublicVal, renderPublicVal_stripGroupMeta_list vs]
  | ctor tn cn fs =>
    have hlen : (stripGroupMetaList fs).isEmpty = fs.isEmpty := by cases fs <;> rfl
    simp [stripGroupMeta, renderPublicVal, hlen, renderPublicVal_stripGroupMeta_list fs]
  | table tv =>
    cases tv
    simp [stripGroupMeta, renderPublicVal]
  | map _ => simp [stripGroupMeta, renderPublicVal]
  | _ => rfl
  termination_by structural v

theorem renderPublicVal_stripGroupMeta_list (vs : List Val) :
    (stripGroupMetaList vs).map renderPublicVal = vs.map renderPublicVal := by
  cases vs with
  | nil => rfl
  | cons x xs =>
    exact congrArg2 List.cons (renderPublicVal_stripGroupMeta x) (renderPublicVal_stripGroupMeta_list xs)
  termination_by structural vs
end

mutual
theorem isSortableTy_imp_isEquatableTy (t : Ty) (hs : isSortableTy t = true) :
    isEquatableTy t = true := by
  cases t with
  | option inner => exact isSortableTy_imp_isEquatableTy inner hs
  | result okTy errTy =>
    simp only [isSortableTy, isEquatableTy, Bool.and_eq_true] at hs ⊢
    exact ⟨isSortableTy_imp_isEquatableTy okTy hs.1, isSortableTy_imp_isEquatableTy errTy hs.2⟩
  | tuple elems => exact isSortableLTyList_imp_isEquatableLTyList elems hs
  | list elem =>
    cases elem with | mk ty _ =>
    exact isSortableTy_imp_isEquatableTy ty hs
  | _ => first | rfl | contradiction
  termination_by structural t

theorem isSortableLTyList_imp_isEquatableLTyList (ls : List LTy) (hs : isSortableLTyList ls = true) :
    isEquatableLTyList ls = true := by
  cases ls with
  | nil => rfl
  | cons hd rest =>
    cases hd with | mk ty _ =>
    simp only [isSortableLTyList, isSortableLTy, isEquatableLTyList, isEquatableLTy, Bool.and_eq_true] at hs ⊢
    exact ⟨isSortableTy_imp_isEquatableTy ty hs.1, isSortableLTyList_imp_isEquatableLTyList rest hs.2⟩
  termination_by structural ls
end

mutual
theorem ValPayloadEquiv.allTags_strip_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {v1 v2 : Val} {ty : Ty}
    (heq : isEquatableTy ty = true)
    (hall : ty.allTags.subset L = true)
    (hp : ValPayloadEquiv prog L v1 v2 ty) :
    stripGroupMeta v1 = stripGroupMeta v2 := by
  cases hp with
  | unit | bool _ | int _ | decimal _ | float _ | text _ | bytes _
  | date _ | timestamp _ | duration _ | optNone _
  | linearModel _ _ _ | statTest _ _ => rfl
  | optSome hu =>
    simp only [isEquatableTy, Ty.allTags] at heq hall
    exact congrArg Val.optSome (ValPayloadEquiv.allTags_strip_eq hd heq hall hu)
  | resOk hu =>
    simp only [isEquatableTy, Ty.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at heq hall
    exact congrArg Val.resOk (ValPayloadEquiv.allTags_strip_eq hd heq.1 hall.1 hu)
  | resErr he =>
    simp only [isEquatableTy, Ty.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at heq hall
    exact congrArg Val.resErr (ValPayloadEquiv.allTags_strip_eq hd heq.2 hall.2 he)
  | tuple hvs =>
    simp only [isEquatableTy, Ty.allTags] at heq hall
    exact congrArg Val.tuple (ValListEquiv.allTags_strip_eq hd heq hall hvs)
  | list hvs =>
    simp only [isEquatableTy, Ty.allTags] at heq hall
    exact congrArg Val.list (ValAllEquiv.allTags_strip_eq hd heq hall hvs)
  | map hkvs =>
    simp only [isEquatableTy, Ty.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at heq hall
    exact congrArg Val.map (ValPairsEquiv.allTags_strip_eq hd heq.1 heq.2 hall.1 hall.2 hkvs)
  | @ctor tn cn vs1 vs2 _ _ _ _ heqVs _ =>
    subst heqVs; rfl
  | @table tv1 tv2 tt ht =>
    simp only [Ty.allTags] at hall
    rcases ht.totalTags_cells_eq hall with ⟨hcols, hcells⟩
    cases tv1 with | mk c1 r1 =>
    cases tv2 with | mk c2 r2 =>
    dsimp only at hcols hcells
    subst hcols
    simp only [stripGroupMeta]
    have hrowsEq : r1.map (fun r => ({ cells := r.cells, groupMeta := none } : TableRow)) =
        r2.map (fun r => ({ cells := r.cells, groupMeta := none } : TableRow)) := by
      clear ht hall
      induction r1 generalizing r2 with
      | nil => cases r2 <;> simp at hcells ⊢
      | cons x1 xs1 ih =>
        cases r2 with
        | nil => simp at hcells
        | cons x2 xs2 =>
          simp only [List.map_cons, List.cons.injEq] at hcells ⊢
          exact ⟨by rw [hcells.1], ih xs2 hcells.2⟩
    rw [hrowsEq]
  | _ => contradiction
  termination_by sizeOf v1

theorem ValListEquiv.allTags_strip_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {vs1 vs2 : List Val} {ltys : List LTy}
    (heq : isEquatableLTyList ltys = true)
    (hall : (LTy.allTagsList ltys).subset L = true)
    (hvs : ValListEquiv prog L vs1 vs2 ltys) :
    stripGroupMetaList vs1 = stripGroupMetaList vs2 := by
  cases hvs with
  | nil => rfl
  | @cons _ _ _ _ l _ hv htl =>
    cases l with | mk ty ts =>
    have hvPay := hv.payload (by
      simp only [LTy.allTagsList, LTy.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at hall
      exact hall.1.2)
    simp only [isEquatableLTyList, isEquatableLTy, LTy.allTagsList, LTy.allTags,
      TagSet.union_subset_iff, Bool.and_eq_true] at heq hall
    exact congrArg2 List.cons
      (ValPayloadEquiv.allTags_strip_eq hd heq.1 hall.1.1 hvPay)
      (ValListEquiv.allTags_strip_eq hd heq.2 hall.2 htl)
  termination_by sizeOf vs1

theorem ValAllEquiv.allTags_strip_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {vs1 vs2 : List Val} {elem : LTy}
    (heq : isEquatableLTy elem = true)
    (hall : elem.allTags.subset L = true)
    (hvs : ValAllEquiv prog L vs1 vs2 elem) :
    stripGroupMetaList vs1 = stripGroupMetaList vs2 := by
  cases hvs with
  | nil _ => rfl
  | cons hv htl =>
    cases elem with | mk ty ts =>
    have heq' := heq
    have hall' := hall
    simp only [isEquatableLTy, LTy.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at heq hall
    exact congrArg2 List.cons
      (ValPayloadEquiv.allTags_strip_eq hd heq hall.1 (hv.payload hall.2))
      (ValAllEquiv.allTags_strip_eq hd heq' hall' htl)
  termination_by sizeOf vs1

theorem ValPairsEquiv.allTags_strip_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {kvs1 kvs2 : List (Val × Val)} {kLTy vLTy : LTy}
    (heqk : isEquatableLTy kLTy = true)
    (heqv : isEquatableLTy vLTy = true)
    (hallk : kLTy.allTags.subset L = true)
    (hallv : vLTy.allTags.subset L = true)
    (hkvs : ValPairsEquiv prog L kvs1 kvs2 kLTy vLTy) :
    stripGroupMetaPairs kvs1 = stripGroupMetaPairs kvs2 := by
  cases hkvs with
  | nil _ _ => rfl
  | cons hk hv htl =>
    cases kLTy with | mk kt kts =>
    cases vLTy with | mk vt vts =>
    have heqk' := heqk; have heqv' := heqv
    have hallk' := hallk; have hallv' := hallv
    simp only [isEquatableLTy, LTy.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at heqk heqv hallk hallv
    have hkEq := ValPayloadEquiv.allTags_strip_eq hd heqk hallk.1 (hk.payload hallk.2)
    have hvEq := ValPayloadEquiv.allTags_strip_eq hd heqv hallv.1 (hv.payload hallv.2)
    simp only [stripGroupMetaPairs, hkEq, hvEq]
    congr 1
    exact ValPairsEquiv.allTags_strip_eq hd heqk' heqv' hallk' hallv' htl
  termination_by sizeOf kvs1
end

theorem LTy.effectiveTags_eq_allTags_of_equatable {lty : LTy} (heq : isEquatableTy lty.ty = true) :
    lty.effectiveTags = lty.allTags := by
  cases lty with | mk ty ts =>
  cases ty <;> try rfl
  all_goals simp [isEquatableTy] at heq

theorem ValEquiv.effectiveTags_strip_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {v1 v2 : Val} {lty : LTy}
    (heq : isEquatableTy lty.ty = true)
    (heff : lty.effectiveTags.subset L = true)
    (hv : ValEquiv prog L v1 v2 lty) :
    stripGroupMeta v1 = stripGroupMeta v2 := by
  rw [LTy.effectiveTags_eq_allTags_of_equatable heq] at heff
  cases lty with | mk ty ts =>
  simp only [LTy.allTags, TagSet.union_subset_iff, Bool.and_eq_true] at heff
  exact ValPayloadEquiv.allTags_strip_eq hd heq heff.1 (hv.payload heff.2)

theorem ValEquiv.effectiveTags_valEq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {a1 a2 b1 b2 : Val} {la lb : LTy}
    (heqA : isEquatableTy la.ty = true)
    (heqB : isEquatableTy lb.ty = true)
    (heffA : la.effectiveTags.subset L = true)
    (heffB : lb.effectiveTags.subset L = true)
    (ha : ValEquiv prog L a1 a2 la)
    (hb : ValEquiv prog L b1 b2 lb) :
    valEq a1 b1 = valEq a2 b2 := by
  rw [← valEq_stripGroupMeta a1 b1, ← valEq_stripGroupMeta a2 b2,
      ha.effectiveTags_strip_eq hd heqA heffA,
      hb.effectiveTags_strip_eq hd heqB heffB]

theorem ValEquiv.effectiveTags_renderPublicVal {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {v1 v2 : Val} {lty : LTy}
    (heq : isEquatableTy lty.ty = true)
    (heff : lty.effectiveTags.subset L = true)
    (hv : ValEquiv prog L v1 v2 lty) :
    renderPublicVal v1 = renderPublicVal v2 := by
  rw [← renderPublicVal_stripGroupMeta v1, ← renderPublicVal_stripGroupMeta v2,
      hv.effectiveTags_strip_eq hd heq heff]

theorem ValEquiv.effectiveTags_sortable_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {v1 v2 : Val} {lty : LTy}
    (hs : isSortableTy lty.ty = true)
    (heff : lty.effectiveTags.subset L = true)
    (hv : ValEquiv prog L v1 v2 lty) :
    v1 = v2 := by
  have heq : isEquatableTy lty.ty = true :=
    isSortableTy_imp_isEquatableTy lty.ty hs
  have hs1 := stripGroupMeta_eq_of_sortable (valWf_sortable hd hv.wf_left hs)
  have hs2 := stripGroupMeta_eq_of_sortable (valWf_sortable hd hv.wf_right hs)
  rw [← hs1, ← hs2]
  exact hv.effectiveTags_strip_eq hd heq heff

/-! ### `WorldEquiv` and Observable `ExecReport` Equality -/

structure StoredTableEquiv (prog : Program) (L : TagSet) (st1 st2 : StoredTable) : Prop where
  dbEq     : st1.db = st2.db
  nameEq   : st1.tableName = st2.tableName
  schemaEq : st1.schema = st2.schema
  tblEquiv : TableEquiv prog L
    { cols := st1.schema.cols, rows := st1.rows.map (fun cs => { cells := cs }) }
    { cols := st2.schema.cols, rows := st2.rows.map (fun cs => { cells := cs }) }
    st1.schema

structure FakeDBEquiv (prog : Program) (L : TagSet) (f1 f2 : FakeDBState) : Prop where
  dbEq   : f1.db = f2.db
  tables : RelList (StoredTableEquiv prog L) f1.tables f2.tables

structure CsvFixtureEquiv (prog : Program) (L : TagSet)
    (fx1 fx2 : String × TableVal × TableVal) : Prop where
  pathEq     : fx1.1 = fx2.1
  goodTysEq  : fx1.2.1.cols.map ColSpec.ty = fx2.2.1.cols.map ColSpec.ty
  badTysEq   : fx1.2.2.cols.map ColSpec.ty = fx2.2.2.cols.map ColSpec.ty
  schemaRows : ∀ sDecl ∈ prog.schemas,
    fx1.2.1.cols.map ColSpec.ty = sDecl.schema.cols.map ColSpec.ty →
    fx1.2.2.cols.map ColSpec.ty = (quarantineBadRowTableTy sDecl.schema).cols.map ColSpec.ty →
    TableEquiv prog L
      { cols := sDecl.schema.cols, rows := fx1.2.1.rows }
      { cols := sDecl.schema.cols, rows := fx2.2.1.rows }
      sDecl.schema ∧
    TableEquiv prog L
      { cols := (quarantineBadRowTableTy sDecl.schema).cols, rows := fx1.2.2.rows }
      { cols := (quarantineBadRowTableTy sDecl.schema).cols, rows := fx2.2.2.rows }
      (quarantineBadRowTableTy sDecl.schema)

/- Consistency between in-memory DB fixture schemas and `SourceDB` nodes in an AST. -/
mutual
def exprRespectsDB (w : World) : Expr → Prop
  | .lit _ | .var _ | .constRef _ | .tableLit _ _ => True
  | .letE _ _ b1 b2 | .join _ _ b1 b2 => exprRespectsDB w b1 ∧ exprRespectsDB w b2
  | .ifE c t e => exprRespectsDB w c ∧ exprRespectsDB w t ∧ exprRespectsDB w e
  | .caseE s arms => exprRespectsDB w s ∧ armsRespectsDB w arms
  | .lam _ _ _ b | .proj b _ | .fail b => exprRespectsDB w b
  | .app f as1 => exprRespectsDB w f ∧ listRespectsDB w as1
  | .call _ as1 | .jump _ as1 | .tuple as1 | .ctor _ _ as1
  | .prim _ as1 | .host _ as1 => listRespectsDB w as1
  | .rel p => planRespectsDB w p
  | .stop _ d => match d with | none => True | some e => exprRespectsDB w e

def listRespectsDB (w : World) : List Expr → Prop
  | [] => True
  | e :: es => exprRespectsDB w e ∧ listRespectsDB w es

def armsRespectsDB (w : World) : List CaseArm → Prop
  | [] => True
  | .mk _ _ b :: rest => exprRespectsDB w b ∧ armsRespectsDB w rest

def planRespectsDB (w : World) : Plan → Prop
  | .sourceExpr e => exprRespectsDB w e
  | .sourceDB cap tableName schema =>
    exprRespectsDB w cap ∧
    (∀ st ∈ w.realDBTables, st.tableName = tableName → st.schema = schema) ∧
    (∀ fdb ∈ w.fakeDBs, ∀ st ∈ fdb.tables, st.tableName = tableName → st.schema = schema)
  | .select p _ | .drop p _ | .rename p _ | .derive p _ | .filter p _
  | .distinct p _ | .sort p _ | .limit p _ | .groupBy p _
  | .summarize p _ _ | .suppressSmallGroups p _ _ _ | .window p _
  | .fillGaps p _ _ _ _ | .pivotWider p _ _ _ _ | .crosstab p _ _ _ _
  | .redact p _ _ => planRespectsDB w p
  | .join _ l r _ _ | .union l r => planRespectsDB w l ∧ planRespectsDB w r
  | .pseudonymize p _ sec => planRespectsDB w p ∧ exprRespectsDB w sec
end

def progRespectsDB (w : World) (prog : Program) : Prop :=
  ∀ f ∈ prog.funs, f.kind.isSpec = false → exprRespectsDB w f.body

/-- `L`-equivalence on execution `World`s:
    - Public/authorized I/O channels (`stdout`, `stderr`, `writtenFiles`, `writtenTables`,
      `fakeConsoles`, `fakeFiles`, `fakeHttps`, `args`, `clockMicros`, `runtimeAllowExport`)
      are literally equal;
    - Database tables and CSV fixtures satisfy `TableEquiv` (allowing high columns, high
      `row_tags`, and high `order_tags` permutations to vary freely);
    - Secret keys (`realSecrets`, `fakeSecrets`) are equated iff `"secret" ∈ L`. -/
structure WorldEquiv (prog : Program) (L : TagSet) (w1 w2 : World) : Prop where
  wf1                : WorldWf prog w1
  wf2                : WorldWf prog w2
  argsEq             : w1.args = w2.args
  clockEq            : w1.clockMicros = w2.clockMicros
  stdoutEq           : w1.stdout = w2.stdout
  stderrEq           : w1.stderr = w2.stderr
  writtenFilesEq     : w1.writtenFiles = w2.writtenFiles
  writtenTablesEq    : w1.writtenTables = w2.writtenTables
  allowExportEq      : w1.runtimeAllowExport = w2.runtimeAllowExport
  fakeConsolesEq     : w1.fakeConsoles = w2.fakeConsoles
  fakeFilesEq        : w1.fakeFiles = w2.fakeFiles
  fakeHttpsEq        : w1.fakeHttps = w2.fakeHttps
  csvFixturesEquiv   : RelList (CsvFixtureEquiv prog L) w1.realCsvFixtures w2.realCsvFixtures
  realDBTablesEquiv  : RelList (StoredTableEquiv prog L) w1.realDBTables w2.realDBTables
  fakeDBsEquiv       : RelList (FakeDBEquiv prog L) w1.fakeDBs w2.fakeDBs
  secretsLowEq       : L.mem "secret" = true →
    w1.realSecrets = w2.realSecrets ∧ w1.fakeSecrets = w2.fakeSecrets

theorem worldEquiv_empty (prog : Program) (L : TagSet) : WorldEquiv prog L {} {} :=
  { wf1 := worldWf_empty prog
    wf2 := worldWf_empty prog
    argsEq := rfl
    clockEq := rfl
    stdoutEq := rfl
    stderrEq := rfl
    writtenFilesEq := rfl
    writtenTablesEq := rfl
    allowExportEq := rfl
    fakeConsolesEq := rfl
    fakeFilesEq := rfl
    fakeHttpsEq := rfl
    csvFixturesEquiv := .nil
    realDBTablesEquiv := .nil
    fakeDBsEquiv := .nil
    secretsLowEq := fun _ => ⟨rfl, rfl⟩ }

/-- Any two `L`-equivalent post-worlds extract **byte-for-byte identical** observable `ExecReport`s! -/
theorem WorldEquiv.extractReport_ok_eq {prog : Program} {L : TagSet}
    {v1 v2 : Val} {w1 w2 : World}
    (hw : WorldEquiv prog L w1 w2) :
    extractReport (.ok v1 w1) = extractReport (.ok v2 w2) := by
  simp only [extractReport, hw.stdoutEq, hw.stderrEq, hw.writtenFilesEq,
    hw.writtenTablesEq, hw.fakeConsolesEq, hw.fakeFilesEq]

theorem WorldEquiv.extractReport_stopped_eq {prog : Program} {L : TagSet}
    {b1 b2 : Bug} {w1 w2 : World}
    (hmsg : b1.message = b2.message)
    (hw : WorldEquiv prog L w1 w2) :
    extractReport (.stopped b1 w1) = extractReport (.stopped b2 w2) := by
  simp only [extractReport, hmsg, hw.stdoutEq, hw.stderrEq, hw.writtenFilesEq,
    hw.writtenTablesEq, hw.fakeConsolesEq, hw.fakeFilesEq]


/-! ## Part 4A: Tag Containment, Primitive NI, `RowExpr` NI & Host Capability NI -/

@[simp] theorem LTy.effectiveTags_eq_allTags (l : LTy) : l.effectiveTags = l.allTags := by
  cases l with | mk ty ts =>
  cases ty <;> rfl

theorem LTy.tags_subset_effectiveTags (l : LTy) : l.tags.subset l.effectiveTags = true := by
  rw [l.effectiveTags_eq_allTags]
  cases l
  exact TagSet.subset_union_right _ _

theorem LTy.ty_allTags_subset_effectiveTags (l : LTy) : l.ty.allTags.subset l.effectiveTags = true := by
  rw [l.effectiveTags_eq_allTags]
  cases l
  exact TagSet.subset_union_left _ _

@[simp] theorem ScalarTy.allTags_toTy_empty : ∀ (s : ScalarTy), s.toTy.allTags = TagSet.empty
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .data _ => rfl
  | .option inner => ScalarTy.allTags_toTy_empty inner

@[simp] theorem ScalarTy.effectiveTags_mk (s : ScalarTy) (ts : TagSet) :
    (LTy.mk s.toTy ts).effectiveTags = ts := by
  rw [LTy.effectiveTags_eq_allTags]
  simp [LTy.allTags]

theorem isOrderedScalarTy_imp_isSortableTy {ty : Ty} (h : isOrderedScalarTy ty = true) :
    isSortableTy ty = true := by
  cases ty <;> simp [isOrderedScalarTy, isSortableTy] at h ⊢

mutual
theorem SortableVal.valSafeForNI (L : TagSet) :
    ∀ {v : Val}, SortableVal v → valSafeForNI L v = true
  | _, .optNone | _, .unit | _, .bool _ | _, .int _ | _, .decimal _ | _, .float _
  | _, .text _ | _, .bytes _ | _, .date _ | _, .timestamp _ | _, .duration _
  | _, .linearModel _ _ _ | _, .statTest _ _ => rfl
  | _, .optSome hv | _, .resOk hv | _, .resErr hv => hv.valSafeForNI L
  | _, .tuple hvs | _, .list hvs | _, .ctor _ _ hvs => hvs.valListSafeForNI L

theorem SortableValList.valListSafeForNI (L : TagSet) :
    ∀ {vs : List Val}, SortableValList vs → valListSafeForNI L vs = true
  | [], .nil => rfl
  | _ :: _, .cons hv hvs => by
    simp [ DanaCore.valListSafeForNI, hv.valSafeForNI L, hvs.valListSafeForNI L]
end

mutual
theorem ValPayloadEquiv.refl_of_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {v : Val} {ty : Ty}, ValWf prog v ty → isSortableTy ty = true → ValPayloadEquiv prog L v v ty
  | _, _, hwf, hs => by
    cases hwf
    case unit => exact .unit
    case bool b => exact .bool b
    case int n _ => exact .int n
    case decimal d _ => exact .decimal d
    case float f => exact .float f
    case text s => exact .text s
    case bytes bs => exact .bytes bs
    case date d => exact .date d
    case timestamp ts => exact .timestamp ts
    case duration dur => exact .duration dur
    case optNone inner => exact .optNone inner
    case optSome _ _ hu => exact .optSome (ValPayloadEquiv.refl_of_sortable hd hu hs)
    case resOk _ _ _ hu =>
      simp only [isSortableTy, Bool.and_eq_true] at hs
      exact .resOk (ValPayloadEquiv.refl_of_sortable hd hu hs.1)
    case resErr _ _ _ he =>
      simp only [isSortableTy, Bool.and_eq_true] at hs
      exact .resErr (ValPayloadEquiv.refl_of_sortable hd he hs.2)
    case tuple _ _ hvs =>
      exact .tuple (ValListEquiv.refl_of_sortable hd hvs hs)
    case list _ elem hvs =>
      exact .list (ValAllEquiv.refl_of_sortable hd hvs hs)
    case ctor dName cName _ _ cDecl hfindD hfindC hvs =>
      have hdAll : ∀ d ∈ prog.datas, ∀ c ∈ d.ctors, ∀ f ∈ c.fields, isSortableTy f.ty = true := by
        unfold progDatasSortableForNI at hd
        simp only [List.all_eq_true] at hd
        intro d hdMem c hcMem f hfMem
        exact hd d hdMem c hcMem f hfMem
      have hfieldsS : isSortableLTyList cDecl.fields = true :=
        isSortableLTyList_of_forall (fun f hf =>
          hdAll _ (List.mem_of_find?_eq_some hfindD) _ (List.mem_of_find?_eq_some hfindC) f hf)
      exact .ctor hfindD hfindC rfl (ValListEquiv.refl_of_sortable hd hvs hfieldsS)
    case linearModel s i r2 => exact .linearModel s i r2
    case statTest s p => exact .statTest s p
    all_goals contradiction

theorem ValListEquiv.refl_of_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {vs : List Val} {ltys : List LTy},
      ValListWf prog vs ltys → isSortableLTyList ltys = true → ValListEquiv prog L vs vs ltys
  | [], [], .nil, _ => .nil
  | _ :: _, .mk _ _ :: _, .cons hv htl, hs => by
    simp only [isSortableLTyList, isSortableLTy, Bool.and_eq_true] at hs
    have hsVal := (valWf_sortable hd hv hs.1).valSafeForNI L
    exact .cons (ValEquiv.mk_smart hv hv hsVal hsVal (fun _ => ValPayloadEquiv.refl_of_sortable hd hv hs.1))
      (ValListEquiv.refl_of_sortable hd htl hs.2)

theorem ValAllEquiv.refl_of_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {vs : List Val} {elem : LTy},
      ValAllWf prog vs elem.ty → isSortableLTy elem = true → ValAllEquiv prog L vs vs elem
  | [], elem, .nil _, _ => .nil elem
  | _ :: _, .mk _ _, .cons hv htl, hs => by
    simp only [isSortableLTy] at hs
    have hsVal := (valWf_sortable hd hv hs).valSafeForNI L
    exact .cons (ValEquiv.mk_smart hv hv hsVal hsVal (fun _ => ValPayloadEquiv.refl_of_sortable hd hv hs))
      (ValAllEquiv.refl_of_sortable hd htl hs)
end

theorem ValEquiv.of_eq_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {v1 v2 : Val} {lty : LTy}
    (heq : v1 = v2) (hwf1 : ValWf prog v1 lty.ty) (hs : isSortableTy lty.ty = true) :
    ValEquiv prog L v1 v2 lty := by
  subst heq
  have hsafe := (valWf_sortable hd hwf1 hs).valSafeForNI L
  exact ValEquiv.mk_smart hwf1 hwf1 hsafe hsafe (fun _ => ValPayloadEquiv.refl_of_sortable hd hwf1 hs)

/-! ### Structural Helpers on `RelList`, `ValListEquiv`, `ValAllEquiv`, and `TableEquiv` -/

theorem RelList.append {α β : Type} {R : α → β → Prop} :
    ∀ {xs1 ys1 : List α} {xs2 ys2 : List β},
      RelList R xs1 xs2 → RelList R ys1 ys2 → RelList R (xs1 ++ ys1) (xs2 ++ ys2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, _, _ :: _, _, .cons hd tl, h2 => .cons hd (tl.append h2)

theorem ValListEquiv.wf_left {prog L} :
    ∀ {vs1 vs2 ltys}, ValListEquiv prog L vs1 vs2 ltys → ValListWf prog vs1 ltys
  | [], [], [], .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hv htl => .cons hv.wf_left htl.wf_left

theorem ValListEquiv.wf_right {prog L} :
    ∀ {vs1 vs2 ltys}, ValListEquiv prog L vs1 vs2 ltys → ValListWf prog vs2 ltys
  | [], [], [], .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hv htl => .cons hv.wf_right htl.wf_right

theorem ValListEquiv.safe_left {prog L} :
    ∀ {vs1 vs2 ltys}, ValListEquiv prog L vs1 vs2 ltys → valListSafeForNI L vs1 = true
  | [], [], [], .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons hv htl => by
    simp [valListSafeForNI, hv.safe_left, htl.safe_left]

theorem ValListEquiv.safe_right {prog L} :
    ∀ {vs1 vs2 ltys}, ValListEquiv prog L vs1 vs2 ltys → valListSafeForNI L vs2 = true
  | [], [], [], .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons hv htl => by
    simp [valListSafeForNI, hv.safe_right, htl.safe_right]

theorem valListEquiv_zero {prog L vs1 vs2} (h : ValListEquiv prog L vs1 vs2 []) :
    vs1 = [] ∧ vs2 = [] := by
  cases h; exact ⟨rfl, rfl⟩

theorem valListEquiv_one {prog L vs1 vs2 l1} (h : ValListEquiv prog L vs1 vs2 [l1]) :
    ∃ a1 a2, vs1 = [a1] ∧ vs2 = [a2] ∧ ValEquiv prog L a1 a2 l1 := by
  cases h with | cons ha htl => cases htl; exact ⟨_, _, rfl, rfl, ha⟩

theorem valListEquiv_two {prog L vs1 vs2 l1 l2} (h : ValListEquiv prog L vs1 vs2 [l1, l2]) :
    ∃ a1 a2 b1 b2, vs1 = [a1, b1] ∧ vs2 = [a2, b2] ∧
      ValEquiv prog L a1 a2 l1 ∧ ValEquiv prog L b1 b2 l2 := by
  cases h with | cons ha htl =>
    cases htl with | cons hb htl2 =>
      cases htl2
      exact ⟨_, _, _, _, rfl, rfl, ha, hb⟩

theorem valListEquiv_three {prog L vs1 vs2 l1 l2 l3}
    (h : ValListEquiv prog L vs1 vs2 [l1, l2, l3]) :
    ∃ a1 a2 b1 b2 c1 c2, vs1 = [a1, b1, c1] ∧ vs2 = [a2, b2, c2] ∧
      ValEquiv prog L a1 a2 l1 ∧ ValEquiv prog L b1 b2 l2 ∧ ValEquiv prog L c1 c2 l3 := by
  cases h with | cons ha htl =>
    cases htl with | cons hb htl2 =>
      cases htl2 with | cons hc htl3 =>
        cases htl3
        exact ⟨_, _, _, _, _, _, rfl, rfl, ha, hb, hc⟩

theorem ValAllEquiv.length_eq {prog L} :
    ∀ {vs1 vs2 elem}, ValAllEquiv prog L vs1 vs2 elem → vs1.length = vs2.length
  | [], [], _, .nil _ => rfl
  | _ :: _, _ :: _, _, .cons _ htl => congrArg (· + 1) htl.length_eq

theorem ValAllEquiv.append {prog L} :
    ∀ {xs1 xs2 ys1 ys2 elem},
      ValAllEquiv prog L xs1 xs2 elem →
      ValAllEquiv prog L ys1 ys2 elem →
      ValAllEquiv prog L (xs1 ++ ys1) (xs2 ++ ys2) elem
  | [], [], _, _, _, .nil _, h2 => h2
  | _ :: _, _ :: _, _, _, _, .cons hv htl, h2 => .cons hv (htl.append h2)

theorem ValAllEquiv.addTags {prog L extra} :
    ∀ {vs1 vs2 elem},
      ValAllEquiv prog L vs1 vs2 elem →
      ValAllEquiv prog L vs1 vs2 (elem.addTags extra)
  | [], [], elem, .nil _ => .nil (elem.addTags extra)
  | _ :: _, _ :: _, _, .cons hv htl => .cons (hv.addTags extra) htl.addTags

theorem TableEquiv.widenRowOrderTags {prog : Program} {L : TagSet}
    {tv1 tv2 : TableVal} {tt : TableTy} (extraR extraO : TagSet)
    (ht : TableEquiv prog L tv1 tv2 tt) :
    TableEquiv prog L tv1 tv2
      { tt with rowTags := tt.rowTags.union extraR, orderTags := tt.orderTags.union extraO } := by
  have hwf1 : ValWf prog (.table tv1) (.table { tt with rowTags := tt.rowTags.union extraR, orderTags := tt.orderTags.union extraO }) := by
    cases ht.wf1 with | table hc hs hr => exact .table hc hs hr
  have hwf2 : ValWf prog (.table tv2) (.table { tt with rowTags := tt.rowTags.union extraR, orderTags := tt.orderTags.union extraO }) := by
    cases ht.wf2 with | table hc hs hr => exact .table hc hs hr
  refine ⟨hwf1, hwf2, ?_, ?_, ?_⟩
  · intro hrowLow
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrowLow
    exact ht.groupingLow hrowLow.1
  · intro hrowLow
    dsimp only
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrowLow
    cases hord : (tt.orderTags.union extraO).subset L
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ht.perm_rows hrowLow.1
    · simp only [↓reduceIte]
      simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hord
      have hlr := ht.lowRows hrowLow.1
      simpa [hord.1] using hlr
  · intro hsum hrowLow
    dsimp only
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrowLow
    cases hord : (tt.orderTags.union extraO).subset L
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hm := ht.sumMetaEq hsum hrowLow.1
      split at hm
      · exact ⟨tv1.rows, .refl _, hm⟩
      · exact hm
    · simp only [↓reduceIte]
      simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hord
      have hm := ht.sumMetaEq hsum hrowLow.1
      simpa [hord.1] using hm

theorem TableEquiv.of_high_rowTags {prog : Program} {L : TagSet}
    {tv1 tv2 : TableVal} {tt : TableTy}
    (hwf1 : ValWf prog (.table tv1) (.table tt))
    (hwf2 : ValWf prog (.table tv2) (.table tt))
    (hhigh : tt.rowTags.subset L = false) :
    TableEquiv prog L tv1 tv2 tt :=
  { wf1 := hwf1
    wf2 := hwf2
    groupingLow := fun h => by rw [hhigh] at h; nomatch h
    lowRows := fun h => by rw [hhigh] at h; nomatch h
    sumMetaEq := fun _ h => by rw [hhigh] at h; nomatch h }

/-! ### High-`pc` Tag Containment (`checkExpr_pc_subset_tags` & `checkPlan_pc_subset_tags`) -/

theorem checkLiteral_pc_subset_tags {prog : Program} {pc : TagSet} {lit : Literal} {lty : LTy}
    (hchk : checkLiteral prog pc lit = .ok lty) :
    pc.subset lty.tags = true := by
  cases lit <;> simp only [checkLiteral] at hchk
  all_goals (try (split at hchk <;> try contradiction))
  all_goals (injection hchk with h; subst h; exact TagSet.subset_refl pc)

theorem checkPrimOp_pc_subset_tags {prog : Program} {pc : TagSet} {op : PrimOp}
    {args : List LTy} {lty : LTy}
    (hchk : checkPrimOp prog pc op args = .ok lty) :
    pc.subset lty.tags = true := by
  unfold checkPrimOp at hchk
  split at hchk
  all_goals (
    repeat (
      (try dsimp only at hchk)
      first
      | contradiction
      | (injection hchk with h; subst h)
      | (split at hchk <;> try contradiction)
    )
  )
  all_goals (rw [TagSet.subset_iff]; intro t ht; simp [LTy.tags, ht])

theorem checkHostOp_pc_subset_tags {prog : Program} {pc : TagSet} {inSpec : Bool}
    {op : HostOp} {args : List LTy} {lty : LTy}
    (hchk : checkHostOp prog pc inSpec op args = .ok lty) :
    pc.subset lty.tags = true := by
  unfold checkHostOp at hchk
  split at hchk
  all_goals (
    repeat (
      (try dsimp only at hchk)
      first
      | contradiction
      | (injection hchk with h; subst h)
      | (simp only [bind, Except.bind] at hchk; split at hchk <;> try contradiction)
      | (split at hchk <;> try contradiction)
    )
  )
  all_goals (rw [TagSet.subset_iff]; intro t ht; simp [LTy.tags, ht])

theorem lookupJoinEnv_mem {jenv : JoinEnv} {label : Ident} {sig : JoinSig}
    (hlook : lookupJoinEnv jenv label = some sig) :
    (label, sig) ∈ jenv := by
  induction jenv with
  | nil => simp [lookupJoinEnv] at hlook
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [lookupJoinEnv] at hlook
    split at hlook
    · rename_i heq; subst heq; injection hlook with h; subst h; exact .head _
    · exact .tail _ (ih hlook)

@[simp] theorem LTy.tags_addTags (extra : TagSet) (l : LTy) :
    (l.addTags extra).tags = l.tags.union extra := by
  cases l; rfl

@[simp] theorem LTy.ty_addTags (extra : TagSet) (l : LTy) :
    (l.addTags extra).ty = l.ty := by
  cases l; rfl

theorem checkExpr_pc_subset_tags {prog : Program} :
    ∀ {env : TyEnv} {jenv : JoinEnv} {pc : TagSet} {inSpec : Bool} {e : Expr} {lty : LTy},
      (∀ p ∈ jenv, p.2.joinPc.subset p.2.retLTy.tags = true) →
      checkExpr prog env jenv pc inSpec e = .ok lty →
      pc.subset lty.tags = true
  | _, _, _, _, .lit v, _, _, hchk => checkLiteral_pc_subset_tags hchk
  | env, _, pc, _, .var name, _, _, hchk => by
    unfold checkExpr at hchk
    cases hl : lookupTyEnv env name <;> rw [hl] at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht; simp [ht]
  | _, _, pc, _, .constRef name, _, _, hchk => by
    unfold checkExpr at hchk
    cases hc : prog.findConst? name <;> rw [hc] at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht; simp [ht]
  | env, jenv, pc, inSpec, .letE name declLTy bound body, _, hjenv, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hb : checkExpr prog env [] pc inSpec bound <;> rw [hb] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    exact checkExpr_pc_subset_tags hjenv hchk
  | env, jenv, pc, inSpec, .ifE cond tBr eBr, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hc : checkExpr prog env [] pc inSpec cond <;> rw [hc] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    cases ht : checkExpr prog env jenv _ inSpec tBr <;> rw [ht] at hchk <;> try contradiction
    dsimp only at hchk
    cases he : checkExpr prog env jenv _ inSpec eBr <;> rw [he] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t htMem; simp [LTy.tags, htMem]
  | env, jenv, pc, inSpec, .caseE scrut arms, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hsc : checkExpr prog env [] pc inSpec scrut <;> rw [hsc] at hchk <;> try contradiction
    dsimp only at hchk
    cases hsp : expectedCaseSpecs prog _ _ <;> rw [hsp] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    cases ha : checkCaseArms prog env jenv _ inSpec _ arms <;> rw [ha] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i armLTys
    cases armLTys <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t htMem; simp [LTy.tags, htMem]
  | _, _, pc, _, .lam _ _ _ _, _, _, hchk => by
    unfold checkExpr at hchk
    repeat (split at hchk <;> try contradiction)
    simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    injection hchk with h; subst h; exact TagSet.subset_refl pc
  | env, _, pc, inSpec, .app fnExpr args, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hf : checkExpr prog env [] pc inSpec fnExpr <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk
    cases ha : checkExprList prog env pc inSpec args <;> rw [ha] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i fnLTy _
    cases hfty : fnLTy.ty <;> rw [hfty] at hchk <;> try contradiction
    dsimp only at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t htMem; simp [htMem]
  | env, _, pc, inSpec, .call fnName args, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args <;> rw [ha] at hchk <;> try contradiction
    dsimp only at hchk
    cases hf : prog.findFun? fnName <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t htMem; simp [htMem]
  | env, jenv, pc, inSpec, .join label params rhs body, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    dsimp only at hchk
    cases hinf : inferJoinRetLTy prog _ jenv _ label rhs body with
    | none => rw [hinf] at hchk; contradiction
    | some candRetLTy =>
      rw [hinf] at hchk; dsimp only [bind, Except.bind] at hchk
      split at hchk <;> try contradiction
      cases hr : checkExpr prog _ _ _ inSpec rhs with
      | error _ => rw [hr] at hchk; contradiction
      | ok rLTy =>
        rw [hr] at hchk; dsimp only at hchk
        cases hb : checkExpr prog env _ pc inSpec body with
        | error _ => rw [hb] at hchk; contradiction
        | ok bLTy =>
          rw [hb] at hchk; dsimp only at hchk
          split at hchk <;> try contradiction
          split at hchk
          · injection hchk with h; subst h
            rw [TagSet.subset_iff]; intro t htMem; simp [htMem]
          · cases hr2 : checkExpr prog _ _ _ inSpec rhs with
            | error _ => rw [hr2] at hchk; contradiction
            | ok _ =>
              rw [hr2] at hchk; dsimp only at hchk
              cases hb2 : checkExpr prog env _ pc inSpec body with
              | error _ => rw [hb2] at hchk; contradiction
              | ok _ =>
                rw [hb2] at hchk; dsimp only at hchk
                split at hchk <;> try contradiction
                injection hchk with h; subst h
                rw [TagSet.subset_iff]; intro t htMem; simp [LTy.tags, htMem]
  | env, jenv, pc, inSpec, .jump label args, _, hjenv, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args <;> rw [ha] at hchk <;> try contradiction
    dsimp only at hchk
    cases hl : lookupJoinEnv jenv label with
    | none => rw [hl] at hchk; contradiction
    | some sig =>
      rw [hl] at hchk; dsimp only at hchk
      cases hpcJ : pc.subset sig.joinPc
      · simp [hpcJ] at hchk
      · simp only [hpcJ, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
        repeat (split at hchk <;> try contradiction)
        injection hchk with h; subst h
        exact TagSet.subset_trans hpcJ (hjenv (label, sig) (lookupJoinEnv_mem hl))
  | env, _, pc, inSpec, .tuple elems, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec elems <;> rw [ha] at hchk <;> try contradiction
    injection hchk with h; subst h; exact TagSet.subset_refl pc
  | env, _, pc, inSpec, .proj tup idx, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ht : checkExpr prog env [] pc inSpec tup <;> rw [ht] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i tupLTy
    cases htty : tupLTy.ty <;> rw [htty] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i elemLTys
    cases helem : elemLTys[idx]? <;> rw [helem] at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t htMem; simp [htMem]
  | env, _, pc, inSpec, .ctor tName cName args, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args <;> rw [ha] at hchk <;> try contradiction
    dsimp only at hchk
    cases hd : prog.findData? tName <;> rw [hd] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i dDecl
    cases hc : dDecl.ctors.find? (fun c => c.name == cName) <;> rw [hc] at hchk <;> try contradiction
    dsimp only at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t htMem; simp [LTy.tags, htMem]
  | _, _, pc, _, .tableLit _ _, _, _, hchk => by
    unfold checkExpr at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h; exact TagSet.subset_refl pc
  | env, _, pc, inSpec, .prim op args, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args <;> rw [ha] at hchk <;> try contradiction
    exact checkPrimOp_pc_subset_tags hchk
  | env, _, pc, inSpec, .rel plan, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hp : checkPlan prog env pc inSpec plan <;> rw [hp] at hchk <;> try contradiction
    injection hchk with h; subst h
    rename_i pTy; cases pTy <;> exact TagSet.subset_refl pc
  | env, _, pc, inSpec, .host op args, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases ha : checkExprList prog env pc inSpec args <;> rw [ha] at hchk <;> try contradiction
    exact checkHostOp_pc_subset_tags hchk
  | env, _, pc, inSpec, .stop _ detail, _, _, hchk => by
    unfold checkExpr at hchk
    cases detail with
    | none => injection hchk with h; subst h; exact TagSet.subset_refl pc
    | some d =>
      dsimp only at hchk
      split at hchk <;> try contradiction
      simp only [bind, Except.bind] at hchk
      cases hd : checkExpr prog env [] pc inSpec d <;> rw [hd] at hchk <;> try contradiction
      dsimp only at hchk
      split at hchk <;> try contradiction
      injection hchk with h; subst h; exact TagSet.subset_refl pc
  | env, _, pc, inSpec, .fail msg, _, _, hchk => by
    unfold checkExpr at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    simp only [bind, Except.bind] at hchk
    cases hm : checkExpr prog env [] pc inSpec msg <;> rw [hm] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with h; subst h; exact TagSet.subset_refl pc

def planTyMainTags : PlanTy → TagSet
  | .table tt => tt.rowTags
  | .dynamic ts => ts

theorem checkPlan_pc_subset_tags {prog : Program} {L : TagSet} :
    ∀ {env : TyEnv} {pc : TagSet} {inSpec : Bool} {plan : Plan} {pTy : PlanTy},
      planSafeForNI L plan = true →
      checkPlan prog env pc inSpec plan = .ok pTy →
      pc.subset (planTyMainTags pTy) = true
  | env, pc, inSpec, .sourceExpr e, _, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases he : checkExpr prog env [] pc inSpec e <;> rw [he] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i eLTy; cases hety : eLTy.ty <;> rw [hety] at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht; simp [planTyMainTags, ht]
  | env, pc, inSpec, .sourceDB cap _ _, _, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hc : checkExpr prog env [] pc inSpec cap <;> rw [hc] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i cLTy; cases hcty : cLTy.ty <;> rw [hcty] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht; simp [planTyMainTags, ht]
  | env, pc, inSpec, .suppressSmallGroups inp _ _ _, _, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i inP; cases inP <;> try contradiction
    dsimp only at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht; simp [planTyMainTags, ht]
  | env, pc, inSpec, .crosstab inp rC cC vC fill, _, _, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i inP; cases inP <;> try contradiction
    dsimp only at hchk
    rename_i tt
    cases hr : tt.findCol? rC <;> cases hc : tt.findCol? cC <;> cases hv : tt.findCol? vC <;>
      rw [hr, hc, hv] at hchk <;> try contradiction
    dsimp only at hchk
    cases hl : checkLiteral prog TagSet.empty fill <;> rw [hl] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht; simp [planTyMainTags, ht]
  | env, pc, inSpec, .select inp _, _, hs, hchk
  | env, pc, inSpec, .drop inp _, _, hs, hchk
  | env, pc, inSpec, .rename inp _, _, hs, hchk
  | env, pc, inSpec, .distinct inp _, _, hs, hchk
  | env, pc, inSpec, .sort inp _, _, hs, hchk
  | env, pc, inSpec, .limit inp _, _, hs, hchk
  | env, pc, inSpec, .groupBy inp _, _, hs, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    all_goals ((try dsimp only at hchk); try (split at hchk <;> try contradiction))
    all_goals ((try dsimp only at hchk); try (split at hchk <;> try contradiction))
    all_goals ((try dsimp only at hchk); try (split at hchk <;> try contradiction))
    all_goals ((try dsimp only at hchk); try (split at hchk <;> try contradiction))
    all_goals (
      injection hchk with h; subst h
      rw [TagSet.subset_iff]; intro t ht
      have h1 := (TagSet.subset_iff _ _).mp ih t ht
      simp [planTyMainTags, h1])
  | env, pc, inSpec, .derive inp items, _, hs, hchk => by
    simp only [planSafeForNI, Bool.and_eq_true] at hs
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs.1 hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    cases hd : applyDeriveItems prog env _ items <;> rw [hd] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    injection hchk with h; subst h; exact ih
  | env, pc, inSpec, .filter inp pred, _, hs, hchk => by
    simp only [planSafeForNI, Bool.and_eq_true] at hs
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs.1 hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    cases hp : checkRowExpr prog env _ pred with
    | error _ => rw [hp] at hchk; contradiction
    | ok pair =>
      rcases pair with ⟨_, _⟩
      rw [hp] at hchk; dsimp only at hchk
      split at hchk <;> try contradiction
      injection hchk with h; subst h
      exact TagSet.subset_trans ih (TagSet.subset_union_left _ _)
  | env, pc, inSpec, .join _ lP rP on suffixes, _, hs, hchk => by
    simp only [planSafeForNI, Bool.and_eq_true] at hs
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hl : checkPlan prog env pc inSpec lP <;> rw [hl] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := lP) hs.1 hl
    dsimp only at hchk
    cases hr : checkPlan prog env pc inSpec rP <;> rw [hr] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i lP' rP'; cases lP' <;> cases rP' <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    cases hrj : resolveJoinPairs _ _ on <;> rw [hrj] at hchk <;> try contradiction
    dsimp only at hchk
    cases hbj : buildJoinedCols _ _ _ on suffixes <;> rw [hbj] at hchk <;> try contradiction
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht
    have h1 := (TagSet.subset_iff _ _).mp ih t ht
    simp [planTyMainTags, h1]
  | env, pc, inSpec, .union lP rP, _, hs, hchk => by
    simp only [planSafeForNI, Bool.and_eq_true] at hs
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hl : checkPlan prog env pc inSpec lP <;> rw [hl] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := lP) hs.1 hl
    dsimp only at hchk
    cases hr : checkPlan prog env pc inSpec rP <;> rw [hr] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i lP' rP'; cases lP' <;> cases rP' <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    cases hm : mergeUnionCols _ _ <;> rw [hm] at hchk <;> try contradiction
    injection hchk with h; subst h
    exact TagSet.subset_trans ih (TagSet.subset_union_left _ _)
  | env, pc, inSpec, .summarize inp aggs dk, _, hs, hchk => by
    simp only [planSafeForNI, Bool.and_eq_true] at hs
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs.1 hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    split at hchk <;> try contradiction
    cases dk with
    | none =>
      dsimp only at hchk
      cases ha : checkAggItemList prog env _ aggs <;> rw [ha] at hchk <;> try contradiction
      dsimp only at hchk; split at hchk <;> try contradiction
      injection hchk with h; subst h
      exact TagSet.subset_trans ih (TagSet.subset_union_left _ _)
    | some d =>
      dsimp only at hchk
      cases hf : TableTy.findCol? _ d <;> rw [hf] at hchk <;> try contradiction
      dsimp only at hchk; split at hchk <;> try contradiction
      cases ha : checkAggItemList prog env _ aggs <;> rw [ha] at hchk <;> try contradiction
      dsimp only at hchk; split at hchk <;> try contradiction
      injection hchk with h; subst h
      exact TagSet.subset_trans ih (TagSet.subset_union_left _ _)
  | env, pc, inSpec, .window inp items, _, hs, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    split at hchk <;> try contradiction
    cases hw : applyWindowItems _ _ items <;> rw [hw] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    injection hchk with h; subst h; exact ih
  | env, pc, inSpec, .fillGaps inp col _ _ _, _, hs, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    split at hchk <;> try contradiction
    cases hf : TableTy.findCol? _ col <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht
    have h1 := (TagSet.subset_iff _ _).mp ih t ht
    simp [planTyMainTags, h1]
  | env, pc, inSpec, .pivotWider inp nf vf _ fill, _, hs, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    split at hchk <;> try contradiction
    cases hnf : TableTy.findCol? _ nf <;> cases hvf : TableTy.findCol? _ vf <;>
      rw [hnf, hvf] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    cases hl : checkLiteral prog TagSet.empty fill <;> rw [hl] at hchk <;> try contradiction
    dsimp only at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with h; subst h
    rw [TagSet.subset_iff]; intro t ht
    have h1 := (TagSet.subset_iff _ _).mp ih t ht
    simp [planTyMainTags, h1]
  | env, pc, inSpec, .redact inp col _, _, hs, hchk => by
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs hi
    rename_i inP; cases inP <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    cases hf : TableTy.findCol? _ col <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    injection hchk with h; subst h; exact ih
  | env, pc, inSpec, .pseudonymize inp col sec, _, hs, hchk => by
    simp only [planSafeForNI, Bool.and_eq_true] at hs
    unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
    cases hi : checkPlan prog env pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
    have ih := checkPlan_pc_subset_tags (plan := inp) hs.1.2 hi
    dsimp only at hchk
    cases hsec : checkExpr prog env [] pc inSpec sec <;> rw [hsec] at hchk <;> try contradiction
    dsimp only at hchk
    rename_i inP sLTy; cases inP <;> cases hsty : sLTy.ty <;> rw [hsty] at hchk <;> try contradiction
    dsimp only [planTyMainTags] at ih hchk
    cases hf : TableTy.findCol? _ col <;> rw [hf] at hchk <;> try contradiction
    dsimp only at hchk; split at hchk <;> try contradiction
    injection hchk with h; subst h; exact ih

/-! ### Helper Lemmas for `evalPrimOp_ni` -/

private def resetGroupMetaTV (tv : TableVal) : TableVal :=
  { cols := tv.cols, rows := tv.rows.map (fun r => { cells := r.cells, groupMeta := none }) }

private theorem resetGroupMetaTV_eq_of_cells_eq {tv1 tv2 : TableVal}
    (hcols : tv1.cols = tv2.cols)
    (hcells : tv1.rows.map TableRow.cells = tv2.rows.map TableRow.cells) :
    resetGroupMetaTV tv1 = resetGroupMetaTV tv2 := by
  cases tv1 with | mk c1 r1 =>
  cases tv2 with | mk c2 r2 =>
  dsimp only [resetGroupMetaTV] at hcols hcells ⊢
  subst hcols
  congr 1
  induction r1 generalizing r2 with
  | nil => cases r2 <;> simp at hcells ⊢
  | cons x1 xs1 ih =>
    cases r2 with
    | nil => simp at hcells
    | cons x2 xs2 =>
      simp only [List.map_cons, List.cons.injEq] at hcells ⊢
      exact ⟨by rw [hcells.1], ih xs2 hcells.2⟩

private theorem pairValMatch_cases (vx vy : Val) {p : List Val}
    (h : (match vx, vy with
          | .optNone, _ => none | _, .optNone => none
          | .optSome ux, .optSome uy => some [ux, uy]
          | .optSome ux, uy => some [ux, uy]
          | ux, .optSome uy => some [ux, uy]
          | ux, uy => some [ux, uy]) = some p) :
    ∃ ax ay, p = [ax, ay] ∧ (ax = vx ∨ vx = .optSome ax) ∧ (ay = vy ∨ vy = .optSome ay) := by
  split at h
  · nomatch h
  · nomatch h
  · injection h with e; subst e; exact ⟨_, _, rfl, .inr rfl, .inr rfl⟩
  · injection h with e; subst e; exact ⟨_, _, rfl, .inr rfl, .inl rfl⟩
  · injection h with e; subst e; exact ⟨_, _, rfl, .inl rfl, .inr rfl⟩
  · injection h with e; subst e; exact ⟨_, _, rfl, .inl rfl, .inl rfl⟩

private theorem extractPairVals_sort_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {tt : TableTy} {tv1 tv2 : TableVal} {colX colY : Ident} {cX cY : ColSpec}
    {raw1 raw2 : List (List Val)}
    (ht : TableEquiv prog L tv1 tv2 tt)
    (hx : tt.findCol? colX = some cX) (hy : tt.findCol? colY = some cY)
    (hrowL : tt.rowTags.subset L = true)
    (hxL : cX.tags.subset L = true) (hyL : cY.tags.subset L = true)
    (hp1 : extractPairVals tv1.cols colX colY tv1.rows = some raw1)
    (hp2 : extractPairVals tv2.cols colX colY tv2.rows = some raw2) :
    insertionSortBy valListLt raw1 = insertionSortBy valListLt raw2 := by
  rcases ht.cols_eq with ⟨hc1, hc2⟩
  cases ht.wf1 with | table _ _ hrWf1 =>
  unfold TableTy.findCol? at hx hy
  rcases lookupColIdx?_of_find? hx with ⟨idxX, hlkX, hgX⟩
  rcases lookupColIdx?_of_find? hy with ⟨idxY, hlkY, hgY⟩
  unfold extractPairVals at hp1 hp2
  rw [hc1, hlkX, hlkY] at hp1; rw [hc2, hlkX, hlkY] at hp2
  dsimp only [bind, Option.bind] at hp1 hp2
  injection hp1 with e1; injection hp2 with e2; subst e1; subst e2
  rcases ht.perm_rows hrowL with ⟨rows1', hpRows, hrelRows⟩
  let pairFn : TableRow → Option (List Val) := fun r =>
    match r.cells[idxX]?, r.cells[idxY]? with
    | some vx, some vy =>
      match vx, vy with
      | .optNone, _ => none | _, .optNone => none
      | .optSome ux, .optSome uy => some [ux, uy]
      | .optSome ux, uy => some [ux, uy]
      | ux, .optSome uy => some [ux, uy]
      | ux, uy => some [ux, uy]
    | _, _ => none
  have hfmAux : ∀ {as bs : List TableRow}, RelList (RowEquiv L tt.cols) as bs →
      as.filterMap pairFn = bs.filterMap pairFn := by
    intro as bs hrel
    induction hrel with
    | nil => rfl
    | @cons a b _ _ hab _ ih =>
      simp only [List.filterMap_cons]
      have hpeq : pairFn a = pairFn b := by
        dsimp only [pairFn]; rw [hab.getElem?_eq hgX hxL, hab.getElem?_eq hgY hyL]
      rw [hpeq]; cases pairFn b <;> simp [ih]
  have hfmEq : rows1'.filterMap pairFn = tv2.rows.filterMap pairFn := hfmAux hrelRows
  have hpf : ∀ {as1 bs1 : List TableRow}, List.Perm as1 bs1 →
      List.Perm (as1.filterMap pairFn) (bs1.filterMap pairFn) := by
    intro as1 bs1 hp; induction hp with
    | nil => exact .nil
    | cons x _ ih => simp only [List.filterMap_cons]; cases pairFn x <;> simp [ih]
    | swap x y l => simp only [List.filterMap_cons]; cases pairFn x <;> cases pairFn y <;> simp [List.Perm.swap]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  have hpermRaw : List.Perm (tv1.rows.filterMap pairFn) (tv2.rows.filterMap pairFn) :=
    hfmEq ▸ hpf hpRows
  have hsortRaw : ∀ p ∈ tv1.rows.filterMap pairFn, SortableValList p := by
    intro p hpMem
    rw [List.mem_filterMap] at hpMem
    rcases hpMem with ⟨r, hrMem, hfm⟩
    have hcw := hrWf1.to_forall r hrMem
    rcases hcw.getElem?_wf hgX with ⟨vx, hgx, hvxWf⟩
    rcases hcw.getElem?_wf hgY with ⟨vy, hgy, hvyWf⟩
    dsimp only [pairFn] at hfm; rw [hgx, hgy] at hfm
    rcases pairValMatch_cases vx vy hfm with ⟨ax, ay, rfl, hax, hay⟩
    have hsortOf : ∀ {s : ScalarTy} {v a : Val}, ValWf prog v s.toTy →
        (a = v ∨ v = .optSome a) → SortableVal a := by
      intro s v a hv ha
      rcases ha with rfl | rfl
      · exact valWf_sortable hd hv (ScalarTy.isSortable_toTy s)
      · cases s <;> cases hv; rename_i hi; exact valWf_sortable hd hi (ScalarTy.isSortable_toTy _)
    exact .cons (hsortOf hvxWf hax) (.cons (hsortOf hvyWf hay) .nil)
  exact insertionSortBy_perm_eq valListLt_irrefl valListLt_trans valListLt_trichotomy hsortRaw hpermRaw

theorem renderTableText_eq_of_cells_eq {tv1 tv2 : TableVal}
    (hcols : tv1.cols = tv2.cols)
    (hcells : tv1.rows.map TableRow.cells = tv2.rows.map TableRow.cells) :
    renderTableText tv1 = renderTableText tv2 := by
  have hreset : ∀ (tv : TableVal), renderTableText (resetGroupMetaTV tv) = renderTableText tv := by
    intro ⟨cols, rows⟩
    simp only [resetGroupMetaTV, renderTableText, List.map_map]; rfl
  rw [← hreset tv1, ← hreset tv2, resetGroupMetaTV_eq_of_cells_eq hcols hcells]

private theorem buildProfileCol_gather_reset (idx : Nat) :
    ∀ (rows : List TableRow),
      buildProfileCol.gather idx (rows.map (fun r => { cells := r.cells, groupMeta := none })) =
      buildProfileCol.gather idx rows
  | [] => rfl
  | r :: rs => by
    simp [buildProfileCol.gather, buildProfileCol_gather_reset idx rs]

private theorem buildProfileCols_reset (tv : TableVal) :
    ∀ (idx : Nat) (cs : List ColSpec),
      buildProfileCols (resetGroupMetaTV tv) idx cs = buildProfileCols tv idx cs
  | _, [] => rfl
  | idx, c :: cs => by
    have hg : buildProfileCol (resetGroupMetaTV tv) idx c = buildProfileCol tv idx c := by
      simp [buildProfileCol, resetGroupMetaTV, buildProfileCol_gather_reset idx tv.rows]
    simp [buildProfileCols, hg, buildProfileCols_reset tv (idx + 1) cs]

theorem buildProfileCols_eq_of_cells_eq {tv1 tv2 : TableVal}
    (hcols : tv1.cols = tv2.cols)
    (hcells : tv1.rows.map TableRow.cells = tv2.rows.map TableRow.cells) :
    buildProfileCols tv1 0 tv1.cols = buildProfileCols tv2 0 tv2.cols := by
  rw [← buildProfileCols_reset tv1 0 tv1.cols,
      ← buildProfileCols_reset tv2 0 tv2.cols,
      resetGroupMetaTV_eq_of_cells_eq hcols hcells, hcols]

private theorem valAllEquiv_of_ltySubtype {prog : Program} {L : TagSet} {elemLTy : LTy} :
    ∀ {vs1 vs2 : List Val} {ltys : List LTy},
      ValListEquiv prog L vs1 vs2 ltys →
      ltys.all (fun a => ltySubtype a elemLTy) = true →
      ValAllEquiv prog L vs1 vs2 elemLTy
  | [], [], [], .nil, _ => .nil elemLTy
  | _ :: _, _ :: _, _ :: _, .cons hv htl, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    exact .cons (hv.subtype hall.1) (valAllEquiv_of_ltySubtype htl hall.2)

private theorem flattenValLists_equiv {prog : Program} {L : TagSet} {elemLTy : LTy} {innerTs : TagSet}
    (hinner : innerTs.subset L = true) :
    ∀ {nested1 nested2 : List Val} {flat1 flat2 : List Val},
      ValAllEquiv prog L nested1 nested2 (.mk (.list elemLTy) innerTs) →
      flattenValLists nested1 = some flat1 →
      flattenValLists nested2 = some flat2 →
      ValAllEquiv prog L flat1 flat2 (elemLTy.addTags innerTs)
  | [], [], _, _, .nil _, hf1, hf2 => by
    injection hf1 with h1; injection hf2 with h2; subst h1; subst h2
    exact .nil _
  | _ :: _, _ :: _, _, _, .cons hv htl, hf1, hf2 => by
    cases hv.payload hinner with | list hxs =>
    simp only [flattenValLists, Option.map_eq_some_iff] at hf1 hf2
    rcases hf1 with ⟨tl1, htl1, rfl⟩
    rcases hf2 with ⟨tl2, htl2, rfl⟩
    exact hxs.addTags.append (flattenValLists_equiv hinner htl htl1 htl2)

private theorem buildPairs_equiv {prog : Program} {L : TagSet} {kLTy vLTy : LTy} :
    ∀ {vs1 vs2 : List Val} {ltys : List LTy} {ps1 ps2 : List (Val × Val)},
      ValListEquiv prog L vs1 vs2 ltys →
      checkPrimOp.checkPairs kLTy vLTy ltys = true →
      buildPairs vs1 = some ps1 →
      buildPairs vs2 = some ps2 →
      ValPairsEquiv prog L ps1 ps2 kLTy vLTy
  | [], [], [], _, _, .nil, _, hb1, hb2 => by
    injection hb1 with h1; injection hb2 with h2; subst h1; subst h2
    exact .nil kLTy vLTy
  | [_], [_], [_], _, _, _, hcp, _, _ => by
    simp [checkPrimOp.checkPairs] at hcp
  | _ :: _ :: _, _ :: _ :: _, _ :: _ :: _, _, _, .cons hk (.cons hv htl), hcp, hb1, hb2 => by
    simp only [checkPrimOp.checkPairs, Bool.and_eq_true] at hcp
    simp only [buildPairs, Option.map_eq_some_iff] at hb1 hb2
    rcases hb1 with ⟨tl1, htl1, rfl⟩
    rcases hb2 with ⟨tl2, htl2, rfl⟩
    exact .cons (hk.subtype hcp.1.1) (hv.subtype hcp.1.2) (buildPairs_equiv htl hcp.2 htl1 htl2)

private theorem mapGet_equiv {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {kLTy vLTy : LTy} {qKey1 qKey2 : Val} {qTs : TagSet}
    (heqK : isEquatableTy kLTy.ty = true)
    (hkEff : kLTy.effectiveTags.subset L = true)
    (hvLow : vLTy.tags.subset L = true)
    (hqLow : qTs.subset L = true)
    (hq : ValEquiv prog L qKey1 qKey2 (.mk kLTy.ty qTs)) :
    ∀ {ps1 ps2 : List (Val × Val)},
      ValPairsEquiv prog L ps1 ps2 kLTy vLTy →
      ValPayloadEquiv prog L
        (match ps1.find? (fun (k, _) => valEq k qKey1) with | some (_, v) => .optSome v | none => .optNone)
        (match ps2.find? (fun (k, _) => valEq k qKey2) with | some (_, v) => .optSome v | none => .optNone)
        (.option vLTy.ty)
  | [], [], .nil _ _ => .optNone vLTy.ty
  | (k1, u1) :: r1, (k2, u2) :: r2, .cons hk hu htl => by
    have hqEff : (LTy.mk kLTy.ty qTs).effectiveTags.subset L = true := by
      rw [LTy.effectiveTags_eq_allTags]
      simp only [LTy.allTags, TagSet.union_subset_iff, Bool.and_eq_true]
      exact ⟨TagSet.subset_trans kLTy.ty_allTags_subset_effectiveTags hkEff, hqLow⟩
    have hkeq := ValEquiv.effectiveTags_valEq (la := kLTy) (lb := .mk kLTy.ty qTs)
      hd heqK heqK hkEff hqEff hk hq
    simp only [List.find?, hkeq]
    cases valEq k2 qKey2
    · exact mapGet_equiv hd heqK hkEff hvLow hqLow hq htl
    · exact .optSome (hu.payload hvLow)

private theorem cellsEquiv_reset_raw {L : TagSet} :
    ∀ {cols : List ColSpec} {cs1 cs2 : List Val},
      CellsEquiv L cols cs1 cs2 →
      CellsEquiv L (cols.map (fun c => { c with aggKind := .raw })) cs1 cs2
  | [], [], [], .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hc htl => .cons hc (cellsEquiv_reset_raw htl)

private theorem relList_rowEquiv_reset_raw {L : TagSet} {cols : List ColSpec} :
    ∀ {rs1 rs2 : List TableRow},
      RelList (RowEquiv L cols) rs1 rs2 →
      RelList (RowEquiv L (cols.map (fun c => { c with aggKind := .raw })))
        (rs1.map (fun row => { row with groupMeta := none }))
        (rs2.map (fun row => { row with groupMeta := none }))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hr htl =>
    .cons (cellsEquiv_reset_raw hr) (relList_rowEquiv_reset_raw htl)

private theorem gatherConcatRows_ordered_equiv {prog : Program} {L : TagSet}
    {tt : TableTy} {elemTs : TagSet}
    (helemLow : elemTs.subset L = true)
    (hrowLow : tt.rowTags.subset L = true)
    (hordLow : tt.orderTags.subset L = true) :
    ∀ {tbls1 tbls2 : List Val} {all1 all2 : List TableRow},
      ValAllEquiv prog L tbls1 tbls2 (.mk (.table tt) elemTs) →
      gatherConcatRows tbls1 = some all1 →
      gatherConcatRows tbls2 = some all2 →
      RelList (RowEquiv L (tt.cols.map (fun c => { c with aggKind := .raw }))) all1 all2
  | [], [], _, _, .nil _, hg1, hg2 => by
    injection hg1 with h1; injection hg2 with h2; subst h1; subst h2; exact .nil
  | _ :: _, _ :: _, _, _, .cons hv htl, hg1, hg2 => by
    cases hv.payload helemLow with | table ht =>
    have hlr := ht.lowRows hrowLow
    simp only [hordLow, ↓reduceIte] at hlr
    simp only [gatherConcatRows, Option.map_eq_some_iff] at hg1 hg2
    rcases hg1 with ⟨r1, hr1, rfl⟩
    rcases hg2 with ⟨r2, hr2, rfl⟩
    exact (relList_rowEquiv_reset_raw hlr).append
      (gatherConcatRows_ordered_equiv helemLow hrowLow hordLow htl hr1 hr2)

private theorem gatherConcatRows_perm_equiv {prog : Program} {L : TagSet}
    {tt : TableTy} {elemTs : TagSet}
    (helemLow : elemTs.subset L = true)
    (hrowLow : tt.rowTags.subset L = true) :
    ∀ {tbls1 tbls2 : List Val} {all1 all2 : List TableRow},
      ValAllEquiv prog L tbls1 tbls2 (.mk (.table tt) elemTs) →
      gatherConcatRows tbls1 = some all1 →
      gatherConcatRows tbls2 = some all2 →
      ∃ all1', List.Perm all1 all1' ∧
        RelList (RowEquiv L (tt.cols.map (fun c => { c with aggKind := .raw }))) all1' all2
  | [], [], _, _, .nil _, hg1, hg2 => by
    injection hg1 with h1; injection hg2 with h2; subst h1; subst h2
    exact ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, _, _, .cons hv htl, hg1, hg2 => by
    cases hv.payload helemLow with | table ht =>
    rcases ht.perm_rows hrowLow with ⟨rows1', hpermHd, hrelHd⟩
    simp only [gatherConcatRows, Option.map_eq_some_iff] at hg1 hg2
    rcases hg1 with ⟨r1, hr1, rfl⟩
    rcases hg2 with ⟨r2, hr2, rfl⟩
    rcases gatherConcatRows_perm_equiv helemLow hrowLow htl hr1 hr2 with ⟨tl1', hpermTl, hrelTl⟩
    exact ⟨rows1'.map (fun row => { row with groupMeta := none }) ++ tl1',
      (hpermHd.map _).append hpermTl,
      (relList_rowEquiv_reset_raw hrelHd).append hrelTl⟩

private theorem projectColCells_gather_length (idx : Nat) :
    ∀ {rows : List TableRow} {vals : List Val},
      projectColCells.gather idx rows = some vals → vals.length = rows.length
  | [], _, h => by injection h with h'; subst h'; rfl
  | r :: rs, _, h => by
    simp only [projectColCells.gather, bind, Option.bind] at h
    cases hc : r.cells[idx]? with
    | none => rw [hc] at h; contradiction
    | some _ =>
      rw [hc] at h; dsimp only at h
      cases hg : projectColCells.gather idx rs with
      | none => rw [hg] at h; contradiction
      | some _ =>
        rw [hg] at h; injection h with h'; subst h'
        exact congrArg (· + 1) (projectColCells_gather_length idx hg)

private theorem projectColCells_gather_eq_of_low {L : TagSet} {cols : List ColSpec}
    {idx : Nat} {c : ColSpec} (hidx : cols[idx]? = some c) (hlow : c.tags.subset L = true) :
    ∀ {rs1 rs2 : List TableRow},
      RelList (RowEquiv L cols) rs1 rs2 →
      projectColCells.gather idx rs1 = projectColCells.gather idx rs2
  | [], [], .nil => rfl
  | r1 :: rs1, r2 :: rs2, .cons hr htl => by
    have hcell := hr.getElem?_eq hidx hlow
    simp only [projectColCells.gather, hcell, projectColCells_gather_eq_of_low hidx hlow htl]

private theorem gatherChartSeries_eq_of_low {L : TagSet} {tv1 tv2 : TableVal} {tt : TableTy}
    (hc1 : tv1.cols = tt.cols) (hc2 : tv2.cols = tt.cols)
    (hrows : RelList (RowEquiv L tt.cols) tv1.rows tv2.rows) :
    ∀ (cns : List Ident),
      (TagSet.unionList (cns.filterMap (fun cn => (tt.findCol? cn).map ColSpec.tags))).subset L = true →
      gatherChartSeries tv1 cns = gatherChartSeries tv2 cns
  | [], _ => rfl
  | cn :: rest, htags => by
    have hrest : (TagSet.unionList (rest.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))).subset L = true := by
      rw [TagSet.unionList_subset_iff] at htags ⊢
      intro s hs
      apply htags s
      simp only [List.filterMap_cons]
      cases (tt.findCol? cn).map ColSpec.tags <;> simp [hs]
    have hpcEq : projectColCells tv1 cn = projectColCells tv2 cn := by
      unfold projectColCells
      rw [hc1, hc2]
      cases hlk : lookupColIdx? tt.cols cn with
      | none => rfl
      | some pair =>
        rcases pair with ⟨idx, cSpec⟩
        have hfind : tt.findCol? cn = some cSpec := by
          unfold TableTy.findCol?
          rw [← lookupColIdx?_snd_eq_find?, hlk]; rfl
        have hcLow : cSpec.tags.subset L = true := by
          rw [TagSet.unionList_subset_iff] at htags
          apply htags cSpec.tags
          simp [hfind]
        rcases lookupColIdx?_props hlk with ⟨hcolIdx, _⟩
        simp only [bind, Option.bind, projectColCells_gather_eq_of_low hcolIdx hcLow hrows]
    simp only [gatherChartSeries, hpcEq, gatherChartSeries_eq_of_low hc1 hc2 hrows rest hrest]

/-! ### Standalone Primitive Evaluation Non-Interference (`evalPrimOp_ni`) -/

theorem evalPrimOp_ni {prog : Program} {L pc : TagSet} {op : PrimOp}
    {argLTys : List LTy} {vs1 vs2 : List Val} {lty : LTy} {v1 v2 : Val}
    (hsafeProg : progSafeForNI prog L = true)
    (hargs : ValListEquiv prog L vs1 vs2 argLTys)
    (hchk : checkPrimOp prog pc op argLTys = .ok lty)
    (hev1 : evalPrimOp op vs1 = .ok v1)
    (hev2 : evalPrimOp op vs2 = .ok v2) :
    ValEquiv prog L v1 v2 lty := by
  have hd : progDatasSortableForNI prog L = true := by
    simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg
    exact hsafeProg.1.1.1
  have hwf1 : ValWf prog v1 lty.ty := by
    have hs := evalPrimOp_sound hchk hargs.wf_left
    rw [hev1] at hs; cases hs; assumption
  have hwf2 : ValWf prog v2 lty.ty := by
    have hs := evalPrimOp_sound hchk hargs.wf_right
    rw [hev2] at hs; cases hs; assumption
  have hsafe1 : valSafeForNI L v1 = true := evalPrimOp_safeForNI hargs.safe_left hev1
  have hsafe2 : valSafeForNI L v2 = true := evalPrimOp_safeForNI hargs.safe_right hev2
  apply ValEquiv.mk_smart hwf1 hwf2 hsafe1 hsafe2
  intro hlow
  -- Helpers for unary/binary sortable scalar ops whose argument tags sit inside `lty.tags`
  have unary_prim : ∀ {ty1 : Ty} {t1 : TagSet},
      ValListEquiv prog L vs1 vs2 [.mk ty1 t1] →
      isSortableTy ty1 = true →
      ty1.allTags = TagSet.empty →
      t1.subset L = true →
      isSortableTy lty.ty = true →
      ValPayloadEquiv prog L v1 v2 lty.ty := by
    intro ty1 t1 h1 hsArg hall1 ht1 hsRet
    rcases valListEquiv_one h1 with ⟨a1, a2, rfl, rfl, ha⟩
    have heff1 : (LTy.mk ty1 t1).effectiveTags.subset L = true := by
      rw [LTy.effectiveTags_eq_allTags]; simp [LTy.allTags, hall1, ht1]
    have haEq := ValEquiv.effectiveTags_sortable_eq (lty := .mk ty1 t1) hd hsArg heff1 ha
    subst haEq
    rw [hev1] at hev2; injection hev2 with hvEq; subst hvEq
    exact ValPayloadEquiv.refl_of_sortable hd hwf1 hsRet
  have binary_prim : ∀ {ty1 ty2 : Ty} {t1 t2 : TagSet},
      ValListEquiv prog L vs1 vs2 [.mk ty1 t1, .mk ty2 t2] →
      isSortableTy ty1 = true →
      isSortableTy ty2 = true →
      ty1.allTags = TagSet.empty →
      ty2.allTags = TagSet.empty →
      t1.subset L = true →
      t2.subset L = true →
      isSortableTy lty.ty = true →
      ValPayloadEquiv prog L v1 v2 lty.ty := by
    intro ty1 ty2 t1 t2 h2 hs1 hs2 hall1 hall2 ht1 ht2 hsRet
    rcases valListEquiv_two h2 with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
    have heff1 : (LTy.mk ty1 t1).effectiveTags.subset L = true := by
      rw [LTy.effectiveTags_eq_allTags]; simp [LTy.allTags, hall1, ht1]
    have heff2 : (LTy.mk ty2 t2).effectiveTags.subset L = true := by
      rw [LTy.effectiveTags_eq_allTags]; simp [LTy.allTags, hall2, ht2]
    have haEq := ValEquiv.effectiveTags_sortable_eq (lty := .mk ty1 t1) hd hs1 heff1 ha
    have hbEq := ValEquiv.effectiveTags_sortable_eq (lty := .mk ty2 t2) hd hs2 heff2 hb
    subst haEq; subst hbEq
    rw [hev1] at hev2; injection hev2 with hvEq; subst hvEq
    exact ValPayloadEquiv.refl_of_sortable hd hwf1 hsRet
  have binary_sortable : ∀ {l1 l2 : LTy},
      ValListEquiv prog L vs1 vs2 [l1, l2] →
      isSortableTy l1.ty = true →
      isSortableTy l2.ty = true →
      l1.effectiveTags.subset L = true →
      l2.effectiveTags.subset L = true →
      isSortableTy lty.ty = true →
      ValPayloadEquiv prog L v1 v2 lty.ty := by
    intro l1 l2 h2 hs1 hs2 heff1 heff2 hsRet
    rcases valListEquiv_two h2 with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
    have haEq := ValEquiv.effectiveTags_sortable_eq (lty := l1) hd hs1 heff1 ha
    have hbEq := ValEquiv.effectiveTags_sortable_eq (lty := l2) hd hs2 heff2 hb
    subst haEq; subst hbEq
    rw [hev1] at hev2; injection hev2 with hvEq; subst hvEq
    exact ValPayloadEquiv.refl_of_sortable hd hwf1 hsRet
  unfold checkPrimOp at hchk
  split at hchk
  -- 1. someVal
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
      injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
      exact .optSome (hc.2 ▸ ha.payload hlow.1)
  -- 2. isSome
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1 <;>
      (simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2; subst hev1; subst hev2; exact .bool _)
  -- 3. isNone
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1 <;>
      (simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2; subst hev1; subst hev2; exact .bool _)
  -- 4. unwrapOr
  · split at hchk <;> try contradiction
    case isTrue heq =>
      injection hchk with hret; subst hret
      have hty := of_decide_eq_true heq; subst hty
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
      cases ha.payload hlow.1.1 with
      | optNone _ =>
        simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2; subst hev1; subst hev2
        exact hb.payload hlow.1.2
      | optSome hu =>
        simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2; subst hev1; subst hev2
        exact hu
  -- 5. unwrapBang
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1 with
    | optNone _ => simp [evalPrimOp] at hev1
    | optSome hu =>
      simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2; subst hev1; subst hev2
      exact hu
  -- 6. okVal
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    exact .resOk (ha.payload hlow.1)
  -- 7. errVal
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    exact .resErr (ha.payload hlow.1)
  -- 8..12. addInt, subInt, mulInt, divInt, modInt
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  -- 13. negInt
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  -- 14..17. addDec, subDec, mulDec, divDec
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  -- 18..20. negDec, intToDec, boolToDec
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  -- 21..22. eq, ne
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
      have heqVal := ValEquiv.effectiveTags_valEq hd hc.2 (hc.1 ▸ hc.2) hlow.1.1 hlow.1.2 ha hb
      simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2
      subst hev1; subst hev2; rw [heqVal]; exact .bool _
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
      have heqVal := ValEquiv.effectiveTags_valEq hd hc.2 (hc.1 ▸ hc.2) hlow.1.1 hlow.1.2 ha hb
      simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2
      subst hev1; subst hev2; rw [heqVal]; exact .bool _
  -- 23..26. lt, le, gt, ge
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      have hs := isOrderedScalarTy_imp_isSortableTy hc.2
      exact binary_sortable hargs hs (hc.1 ▸ hs) hlow.1.1 hlow.1.2 rfl
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      have hs := isOrderedScalarTy_imp_isSortableTy hc.2
      exact binary_sortable hargs hs (hc.1 ▸ hs) hlow.1.1 hlow.1.2 rfl
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      have hs := isOrderedScalarTy_imp_isSortableTy hc.2
      exact binary_sortable hargs hs (hc.1 ▸ hs) hlow.1.1 hlow.1.2 rfl
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      have hs := isOrderedScalarTy_imp_isSortableTy hc.2
      exact binary_sortable hargs hs (hc.1 ▸ hs) hlow.1.1 hlow.1.2 rfl
  -- 27..29. notBool, andBool, orBool
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  -- 30..36. concatText, containsText, trimText, lowerAsciiText, emptyText, intToText, decToText
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  -- 37..39. dateTruncMonth, addDuration, diffTimestamp
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact unary_prim hargs rfl rfl hlow.1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    exact binary_prim hargs rfl rfl rfl rfl hlow.1.1 hlow.1.2 rfl
  -- 40. listLit
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true] at hc
      injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
      exact .list (valAllEquiv_of_ltySubtype hargs hc.2)
  -- 41..42. listLen, listEmpty
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1 with | list hvs =>
    simp only [evalPrimOp] at hev1 hev2
    rw [hvs.length_eq] at hev1; rw [hev1] at hev2; injection hev2 with hvEq; subst hvEq
    exact ValPayloadEquiv.refl_of_sortable hd hwf1 rfl
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1 with | list hvs =>
    have hem : ∀ {xs ys : List Val}, xs.length = ys.length → xs.isEmpty = ys.isEmpty := by
      intro xs ys hl; cases xs <;> cases ys <;> simp at hl ⊢
    simp only [evalPrimOp, hem hvs.length_eq, PrimResult.ok.injEq] at hev1 hev2
    subst hev1; subst hev2; exact .bool _
  -- 43. listAppend
  · split at hchk <;> try contradiction
    case isTrue hsub =>
      injection hchk with hret; subst hret
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
      cases ha.payload hlow.1 with | list hvs =>
      simp only [evalPrimOp, PrimResult.ok.injEq] at hev1 hev2; subst hev1; subst hev2
      exact .list (hvs.append (.cons (hb.subtype hsub) (.nil _)))
  -- 44. listConcat
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1.1 with | list hnested =>
    dsimp only [evalPrimOp] at hev1 hev2
    cases hf1 : flattenValLists _ <;> rw [hf1] at hev1 <;> try contradiction
    cases hf2 : flattenValLists _ <;> rw [hf2] at hev2 <;> try contradiction
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    exact .list (flattenValLists_equiv hlow.1.2 hnested hf1 hf2)
  -- 45. mapLit
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true] at hc
      dsimp only [evalPrimOp] at hev1 hev2
      cases hb1 : buildPairs vs1 <;> rw [hb1] at hev1 <;> try contradiction
      cases hb2 : buildPairs vs2 <;> rw [hb2] at hev2 <;> try contradiction
      injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
      exact .map (buildPairs_equiv hargs hc.2 hb1 hb2)
  -- 46. mapGet
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨rfl, heqK⟩, _⟩
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases valListEquiv_two hargs with ⟨a1, a2, q1, q2, rfl, rfl, ha, hq⟩
      cases ha.payload hlow.1.1.1.1 with | map hkvs =>
      dsimp only [evalPrimOp] at hev1 hev2
      have hmg := mapGet_equiv hd heqK hlow.1.1.1.2 hlow.1.1.2 hlow.1.2 hq hkvs
      cases ps1_find : List.find? _ _ with
      | none =>
        rw [ps1_find] at hev1 hmg
        cases ps2_find : List.find? _ _ with
        | none =>
          rw [ps2_find] at hev2 hmg
          injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
          exact hmg
        | some p2 =>
          rcases p2 with ⟨_, _⟩
          rw [ps2_find] at hev2 hmg
          injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
          exact hmg
      | some p1 =>
        rcases p1 with ⟨_, _⟩
        rw [ps1_find] at hev1 hmg
        cases ps2_find : List.find? _ _ with
        | none =>
          rw [ps2_find] at hev2 hmg
          injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
          exact hmg
        | some p2 =>
          rcases p2 with ⟨_, _⟩
          rw [ps2_find] at hev2 hmg
          injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
          exact hmg
  -- 47. tableCount
  · injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1.2 with | table ht =>
    simp only [evalPrimOp] at hev1 hev2
    rw [ht.length_eq hlow.1.1] at hev1; rw [hev1] at hev2; injection hev2 with hvEq; subst hvEq
    exact ValPayloadEquiv.refl_of_sortable hd hwf1 rfl
  -- 48. tableConcat
  · split at hchk <;> try contradiction
    case isTrue hc =>
      injection hchk with hret; subst hret
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, _⟩
      rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
      cases ha.wf_left; cases ha.wf_right
      try dsimp only [evalPrimOp] at hev1 hev2
      cases hg1 : gatherConcatRows _ <;> rw [hg1] at hev1 <;> try contradiction
      cases hg2 : gatherConcatRows _ <;> rw [hg2] at hev2 <;> try contradiction
      injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
      apply ValPayloadEquiv.table
      refine ⟨hwf1, hwf2, ?_, ?_, fun h _ => by nomatch h⟩
      · intro _ c hcMem hk
        rw [List.mem_map] at hcMem; rcases hcMem with ⟨_, _, rfl⟩; nomatch hk
      · intro hrowLow
        dsimp only at hrowLow ⊢
        simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrowLow
        cases ha.payload hrowLow.2.1.2 with | list htbls =>
        split
        · rename_i hord
          simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hord
          exact gatherConcatRows_ordered_equiv hrowLow.2.1.1 hrowLow.1 hord.1 htbls hg1 hg2
        · exact gatherConcatRows_perm_equiv hrowLow.2.1.1 hrowLow.1 htbls hg1 hg2
  -- 49. tableProfile
  · injection hchk with hret; subst hret
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.wf_left; cases ha.wf_right
    try dsimp only [evalPrimOp] at hev1 hev2
    cases hb1 : buildProfileCols _ 0 _ <;> rw [hb1] at hev1 <;> try contradiction
    cases hb2 : buildProfileCols _ 0 _ <;> rw [hb2] at hev2 <;> try contradiction
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    apply ValPayloadEquiv.profile
    intro hpLow
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hpLow
    cases ha.payload hpLow.1.2 with | table ht =>
    rcases ht.totalTags_cells_eq hpLow.1.1 with ⟨hcolsEq, hcellsEq⟩
    rw [buildProfileCols_eq_of_cells_eq hcolsEq hcellsEq, hb2] at hb1
    injection hb1 with hsEq; subst hsEq; rfl
  -- 50..52. statsCorr, statsLinReg, statsTTest
  · rename_i colX colY tt tTs
    cases hx : tt.findCol? colX <;> cases hy : tt.findCol? colY <;>
      rw [hx, hy] at hchk <;> try contradiction
    rename_i cX cY
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1.1.1.2 with | @table tv1 tv2 _ ht =>
    dsimp only [evalPrimOp] at hev1 hev2
    cases hp1 : extractPairVals tv1.cols colX colY tv1.rows <;> rw [hp1] at hev1 <;> try contradiction
    cases hp2 : extractPairVals tv2.cols colX colY tv2.rows <;> rw [hp2] at hev2 <;> try contradiction
    rename_i raw1 raw2
    dsimp only at hev1 hev2
    have hsortPairsEq : insertionSortBy valListLt raw1 = insertionSortBy valListLt raw2 :=
      extractPairVals_sort_eq hd ht hx hy hlow.1.1.1.1 hlow.1.1.2 hlow.1.2 hp1 hp2
    rw [hsortPairsEq] at hev1
    rw [hev2] at hev1; injection hev1 with hvEq; subst hvEq
    exact ValPayloadEquiv.refl_of_sortable hd hwf1 rfl
  · rename_i colX colY tt tTs
    cases hx : tt.findCol? colX <;> cases hy : tt.findCol? colY <;>
      rw [hx, hy] at hchk <;> try contradiction
    rename_i cX cY
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.payload hlow.1.1.1.2 with | @table tv1 tv2 _ ht =>
    dsimp only [evalPrimOp] at hev1 hev2
    cases hp1 : extractPairVals tv1.cols colX colY tv1.rows <;> rw [hp1] at hev1 <;> try contradiction
    cases hp2 : extractPairVals tv2.cols colX colY tv2.rows <;> rw [hp2] at hev2 <;> try contradiction
    rename_i raw1 raw2
    dsimp only at hev1 hev2
    have hsortEq : insertionSortBy valListLt raw1 = insertionSortBy valListLt raw2 :=
      extractPairVals_sort_eq hd ht hx hy hlow.1.1.1.1 hlow.1.1.2 hlow.1.2 hp1 hp2
    rw [hsortEq] at hev1
    rw [hev2] at hev1; injection hev1 with hvEq; subst hvEq
    cases hwf1; exact .linearModel _ _ _
  · rename_i colX colY tt tTs
    cases hx : tt.findCol? colX <;> cases hy : tt.findCol? colY <;>
      rw [hx, hy] at hchk <;> try contradiction
    dsimp only at hchk
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.wf_left; cases ha.wf_right
    dsimp only [evalPrimOp] at hev1
    split at hev1 <;> contradiction
  -- 53. chartMake
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.wf_left; cases ha.wf_right
    try dsimp only [evalPrimOp] at hev1 hev2
    cases hg1 : gatherChartSeries _ _ <;> rw [hg1] at hev1 <;> try contradiction
    cases hg2 : gatherChartSeries _ _ <;> rw [hg2] at hev2 <;> try contradiction
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    apply ValPayloadEquiv.chart
    intro hcLow
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hcLow
    cases ha.payload hcLow.1.1.2 with | table ht =>
    rcases ht.cols_eq with ⟨hc1, hc2⟩
    have hlr := ht.lowRows hcLow.1.1.1.1
    simp only [hcLow.1.1.1.2, ↓reduceIte] at hlr
    rw [gatherChartSeries_eq_of_low hc1 hc2 hlr _ hcLow.1.2, hg2] at hg1
    injection hg1 with hsEq; subst hsEq; rfl
  -- 54..57. reportNew, reportAddSummary, reportAddChart, reportAddTable
  · injection hchk with hret; subst hret
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.wf_left; cases ha.wf_right
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    apply ValPayloadEquiv.report
    intro hrLow; simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
    cases ha.payload hrLow.1; rfl
  · injection hchk with hret; subst hret
    rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
    cases ha.wf_left; cases hb.wf_left; cases ha.wf_right; cases hb.wf_right
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    apply ValPayloadEquiv.report
    intro hrLow; simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
    cases ha.payload hrLow.1.1.2 with | report hrv =>
    cases hb.payload hrLow.1.2
    rw [hrv hrLow.1.1.1]
  · injection hchk with hret; subst hret
    rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
    cases ha.wf_left; cases hb.wf_left; cases ha.wf_right; cases hb.wf_right
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    apply ValPayloadEquiv.report
    intro hrLow; simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
    cases ha.payload hrLow.1.1.1.2 with | report hrv =>
    cases hb.payload hrLow.1.2 with | chart hcv =>
    rw [hrv hrLow.1.1.1.1, hcv hrLow.1.1.2]
  · injection hchk with hret; subst hret
    rcases valListEquiv_two hargs with ⟨a1, a2, b1, b2, rfl, rfl, ha, hb⟩
    cases ha.wf_left; cases hb.wf_left; cases ha.wf_right; cases hb.wf_right
    injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
    apply ValPayloadEquiv.report
    intro hrLow; simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
    cases ha.payload hrLow.1.1.1.2 with | report hrv =>
    cases hb.payload hrLow.1.2 with | table ht =>
    rcases ht.totalTags_cells_eq hrLow.1.1.2 with ⟨hcEq, hrEq⟩
    rw [hrv hrLow.1.1.1.1, hcEq, hrEq]
  -- 58. error catch-all
  · contradiction

/-! ### Standalone `RowExpr` Non-Interference (`evalRowExpr_ni` & `evalRowExprList_ni`) -/

def RowExprNIAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ (env1 env2 : Env) (cols : List ColSpec) (r1 r2 : TableRow)
    (re : RowExpr) (sTy : ScalarTy) (rTags : TagSet) (v1 v2 : Val),
    EnvEquiv prog L env1 env2 →
    (∀ c ∈ cols, validScalarTy prog c.ty = true) →
    CellsWf prog r1.cells cols →
    CellsWf prog r2.cells cols →
    RowEquiv L cols r1 r2 →
    checkRowExpr prog (envToTyEnv env1) cols re = .ok (sTy, rTags) →
    evalRowExpr fuel prog env1 cols r1 re = .ok v1 →
    evalRowExpr fuel prog env2 cols r2 re = .ok v2 →
    ValEquiv prog L v1 v2 (.mk sTy.toTy rTags)

def RowExprListNIAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ (env1 env2 : Env) (cols : List ColSpec) (r1 r2 : TableRow)
    (rs : List RowExpr) (pairs : List (ScalarTy × TagSet)) (vs1 vs2 : List Val),
    EnvEquiv prog L env1 env2 →
    (∀ c ∈ cols, validScalarTy prog c.ty = true) →
    CellsWf prog r1.cells cols →
    CellsWf prog r2.cells cols →
    RowEquiv L cols r1 r2 →
    checkRowExprList prog (envToTyEnv env1) cols rs = .ok pairs →
    evalRowExprList fuel prog env1 cols r1 rs = .ok vs1 →
    evalRowExprList fuel prog env2 cols r2 rs = .ok vs2 →
    ValListEquiv prog L vs1 vs2 (pairs.map (fun (st, ts) => LTy.mk st.toTy ts))

theorem ValEquiv.scalar_low_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {v1 v2 : Val} {sTy : ScalarTy} {ts : TagSet}
    (hv : ValEquiv prog L v1 v2 (.mk sTy.toTy ts))
    (hts : ts.subset L = true) : v1 = v2 := by
  have heff : (LTy.mk sTy.toTy ts).effectiveTags.subset L = true := by
    rw [LTy.effectiveTags_eq_allTags]; simp [LTy.allTags, hts]
  exact ValEquiv.effectiveTags_sortable_eq (lty := .mk sTy.toTy ts)
    hd (ScalarTy.isSortable_toTy sTy) heff hv

private theorem valListEquiv_scalar_all_low_eq {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {vs1 vs2 : List Val} {pairs : List (ScalarTy × TagSet)},
      ValListEquiv prog L vs1 vs2 (pairs.map (fun (st, ts) => LTy.mk st.toTy ts)) →
      (TagSet.unionList (pairs.map Prod.snd)).subset L = true →
      vs1 = vs2
  | [], [], [], .nil, _ => rfl
  | _ :: _, _ :: _, (st, ts) :: rest, .cons hv htl, hlow => by
    have htsLow : ts.subset L = true := by
      rw [TagSet.unionList_subset_iff] at hlow
      exact hlow ts (.head _)
    have hrestLow : (TagSet.unionList (rest.map Prod.snd)).subset L = true := by
      rw [TagSet.unionList_subset_iff] at hlow ⊢
      intro s hs; exact hlow s (.tail _ hs)
    have hvEq := ValEquiv.scalar_low_eq (sTy := st) hd hv htsLow
    exact congrArg2 List.cons hvEq (valListEquiv_scalar_all_low_eq hd htl hrestLow)

theorem evalRowExpr_ni_all (fuel : Nat) (prog : Program) (L : TagSet) :
    RowExprNIAt fuel prog L ∧ RowExprListNIAt fuel prog L := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold RowExprNIAt
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hev1 _
      unfold evalRowExpr at hev1; nomatch hev1
    · unfold RowExprListNIAt
      intro _ _ _ _ _ _ _ rs pairs _ _ _ _ _ _ _ hchk hev1 hev2
      cases rs with
      | nil =>
        unfold checkRowExprList at hchk; injection hchk with h; subst h
        unfold evalRowExprList at hev1 hev2
        injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
        exact .nil
      | cons _ _ => unfold evalRowExprList at hev1; contradiction
  | succ fuel' ih =>
    rcases ih with ⟨ihRE, ihREL⟩
    have hsound := eval_fuel_sound prog (fuel' + 1)
    refine ⟨?_, ?_⟩
    · unfold RowExprNIAt
      intro hprog hsafeProg env1 env2 cols r1 r2 re sTy rTags v1 v2 henv hcols hr1Wf hr2Wf hrowEq hchk hev1 hev2
      have hd : progDatasSortableForNI prog L = true := by
        simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
      have hchk2 : checkRowExpr prog (envToTyEnv env2) cols re = .ok (sTy, rTags) := by
        rwa [← henv.envToTyEnv_eq]
      have hwf1 : ValWf prog v1 sTy.toTy := by
        have hs := hsound.1 hprog env1 cols r1 re sTy rTags henv.wf_left hcols hr1Wf hchk
        rw [hev1] at hs; cases hs; assumption
      have hwf2 : ValWf prog v2 sTy.toTy := by
        have hs := hsound.1 hprog env2 cols r2 re sTy rTags henv.wf_right hcols hr2Wf hchk2
        rw [hev2] at hs; cases hs; assumption
      have hsafe1 : valSafeForNI L v1 = true :=
        (valWf_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)).valSafeForNI L
      have hsafe2 : valSafeForNI L v2 = true :=
        (valWf_sortable hd hwf2 (ScalarTy.isSortable_toTy sTy)).valSafeForNI L
      apply ValEquiv.mk_smart hwf1 hwf2 hsafe1 hsafe2
      intro hlow
      dsimp only [LTy.tags, LTy.ty] at hlow ⊢
      unfold evalRowExpr at hev1 hev2
      cases re with
      | lit lit =>
        dsimp only at hev1 hev2
        injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
        exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
      | col name =>
        dsimp only at hev1 hev2
        unfold checkRowExpr at hchk
        cases hf : cols.find? (fun c => c.name == name) with
        | none => simp [hf] at hchk
        | some cSpec =>
          simp only [hf, Except.ok.injEq, Prod.mk.injEq] at hchk
          rcases hchk with ⟨rfl, rfl⟩
          cases hlk : lookupColIdx? cols name with
          | none => rw [hlk] at hev1; simp at hev1
          | some pair =>
            rcases pair with ⟨idx, c'⟩
            have hcEq : c' = cSpec := by
              have hsnd := lookupColIdx?_snd_eq_find? cols name
              rw [hlk, hf] at hsnd; injection hsnd
            subst hcEq
            rcases lookupColIdx?_props hlk with ⟨hcolIdx, _⟩
            rw [hlk] at hev1 hev2; dsimp only at hev1 hev2
            have hcellEq := hrowEq.getElem?_eq hcolIdx hlow
            rw [hcellEq] at hev1
            cases hcell : r2.cells[idx]? with
            | none => rw [hcell] at hev1; contradiction
            | some _ =>
              rw [hcell] at hev1 hev2
              injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
              exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy c'.ty)
      | outerVar name =>
        dsimp only at hev1 hev2
        unfold checkRowExpr at hchk
        cases hlt : lookupTyEnv (envToTyEnv env1) name with
        | none => rw [hlt] at hchk; contradiction
        | some oLTy =>
          rw [hlt] at hchk; dsimp only at hchk
          cases hs : oLTy.ty.toScalarTy? with
          | none => rw [hs] at hchk; contradiction
          | some st =>
            rw [hs] at hchk; dsimp only at hchk; split at hchk <;> try contradiction
            injection hchk with hp; rcases hp with ⟨rfl, rfl⟩
            rcases henv.lookup hlt with ⟨u1, u2, hlk1, hlk2, huEq⟩
            rw [hlk1] at hev1; rw [hlk2] at hev2
            injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
            have htyEq := Ty.toScalarTy?_some_imp hs
            have hvEq := ValEquiv.effectiveTags_sortable_eq (lty := oLTy) hd (htyEq ▸ ScalarTy.isSortable_toTy sTy) hlow huEq
            subst hvEq
            exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
      | constRef name =>
        dsimp only at hev1 hev2
        cases hc : prog.findConst? name with
        | none => rw [hc] at hev1; contradiction
        | some _ =>
          rw [hc] at hev1 hev2
          injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
          exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
      | prim op args =>
        dsimp only at hev1 hev2
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases ha : checkRowExprList prog (envToTyEnv env1) cols args with
        | error _ => rw [ha] at hchk; contradiction
        | ok pairs =>
          rw [ha] at hchk; dsimp only at hchk
          cases hp : checkPrimOp prog TagSet.empty op (pairs.map (fun (st, ts) => LTy.mk st.toTy ts)) with
          | error _ => rw [hp] at hchk; contradiction
          | ok resLTy =>
            rw [hp] at hchk; dsimp only at hchk
            cases hs : resLTy.ty.toScalarTy? with
            | none => rw [hs] at hchk; contradiction
            | some st =>
              rw [hs] at hchk; dsimp only at hchk; split at hchk <;> try contradiction
              injection hchk with hpEq; rcases hpEq with ⟨rfl, rfl⟩
              cases hrl1 : evalRowExprList fuel' prog env1 cols r1 args <;> rw [hrl1] at hev1 <;> try contradiction
              cases hrl2 : evalRowExprList fuel' prog env2 cols r2 args <;> rw [hrl2] at hev2 <;> try contradiction
              have hargsEq := ihREL hprog hsafeProg env1 env2 cols r1 r2 args pairs _ _
                henv hcols hr1Wf hr2Wf hrowEq ha hrl1 hrl2
              have hprimEq := evalPrimOp_ni hsafeProg hargsEq hp hev1 hev2
              have htyEq := Ty.toScalarTy?_some_imp hs
              have hvEq := ValEquiv.effectiveTags_sortable_eq (lty := resLTy) hd (htyEq ▸ ScalarTy.isSortable_toTy sTy) hlow hprimEq
              subst hvEq
              exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
      | ifE cond tBr eBr =>
        dsimp only at hev1 hev2
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases hc : checkRowExpr prog (envToTyEnv env1) cols cond with
        | error _ => rw [hc] at hchk; contradiction
        | ok cp =>
          rcases cp with ⟨cTy, cTags⟩; rw [hc] at hchk; dsimp only at hchk
          cases ht : checkRowExpr prog (envToTyEnv env1) cols tBr with
          | error _ => rw [ht] at hchk; contradiction
          | ok tp =>
            rcases tp with ⟨tTy, tTags⟩; rw [ht] at hchk; dsimp only at hchk
            cases he : checkRowExpr prog (envToTyEnv env1) cols eBr with
            | error _ => rw [he] at hchk; contradiction
            | ok ep =>
              rcases ep with ⟨eTy, eTags⟩; rw [he] at hchk; dsimp only at hchk
              split at hchk <;> try contradiction
              rename_i htyOk; simp only [Bool.and_eq_true, decide_eq_true_eq] at htyOk
              rcases htyOk with ⟨rfl, rfl⟩
              injection hchk with hpEq; rcases hpEq with ⟨rfl, rfl⟩
              simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hlow
              cases hcv1 : evalRowExpr fuel' prog env1 cols r1 cond <;> rw [hcv1] at hev1 <;> try contradiction
              cases hcv2 : evalRowExpr fuel' prog env2 cols r2 cond <;> rw [hcv2] at hev2 <;> try contradiction
              have hcEqV := ValEquiv.scalar_low_eq (sTy := .bool) hd
                (ihRE hprog hsafeProg env1 env2 cols r1 r2 cond .bool cTags _ _
                  henv hcols hr1Wf hr2Wf hrowEq hc hcv1 hcv2) hlow.1.1
              subst hcEqV
              rename_i cVal
              cases cVal <;> try contradiction
              rename_i b
              cases b
              · have hbEq := ValEquiv.scalar_low_eq (sTy := sTy) hd
                  (ihRE hprog hsafeProg env1 env2 cols r1 r2 eBr sTy eTags _ _
                    henv hcols hr1Wf hr2Wf hrowEq he hev1 hev2) hlow.2
                subst hbEq; exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
              · have hbEq := ValEquiv.scalar_low_eq (sTy := sTy) hd
                  (ihRE hprog hsafeProg env1 env2 cols r1 r2 tBr sTy tTags _ _
                    henv hcols hr1Wf hr2Wf hrowEq ht hev1 hev2) hlow.1.2
                subst hbEq; exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
      | coalesce optE defE =>
        dsimp only at hev1 hev2
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases ho : checkRowExpr prog (envToTyEnv env1) cols optE with
        | error _ => rw [ho] at hchk; contradiction
        | ok op1 =>
          rcases op1 with ⟨oTy, oTags⟩; rw [ho] at hchk; dsimp only at hchk
          cases hde : checkRowExpr prog (envToTyEnv env1) cols defE with
          | error _ => rw [hde] at hchk; contradiction
          | ok dp1 =>
            rcases dp1 with ⟨dTy, dTags⟩; rw [hde] at hchk; dsimp only at hchk
            cases oTy <;> try contradiction
            dsimp only at hchk; split at hchk <;> try contradiction
            rename_i hinner; have hinnerEq := of_decide_eq_true hinner; subst hinnerEq
            injection hchk with hpEq; rcases hpEq with ⟨rfl, rfl⟩
            simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hlow
            cases hov1 : evalRowExpr fuel' prog env1 cols r1 optE <;> rw [hov1] at hev1 <;> try contradiction
            cases hov2 : evalRowExpr fuel' prog env2 cols r2 optE <;> rw [hov2] at hev2 <;> try contradiction
            have hoEqV := ValEquiv.scalar_low_eq (sTy := .option sTy) hd
              (ihRE hprog hsafeProg env1 env2 cols r1 r2 optE (.option sTy) oTags _ _
                henv hcols hr1Wf hr2Wf hrowEq ho hov1 hov2) hlow.1
            subst hoEqV
            rename_i optVal
            cases optVal <;> try contradiction
            · have hdEqV := ValEquiv.scalar_low_eq (sTy := sTy) hd
                (ihRE hprog hsafeProg env1 env2 cols r1 r2 defE sTy dTags _ _
                  henv hcols hr1Wf hr2Wf hrowEq hde hev1 hev2) hlow.2
              subst hdEqV; exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
            · injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
              exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
      | callPure fnName args =>
        dsimp only at hev1 hev2
        unfold checkRowExpr at hchk; simp only [bind, Except.bind] at hchk
        cases ha : checkRowExprList prog (envToTyEnv env1) cols args <;> rw [ha] at hchk <;> try contradiction
        dsimp only at hchk
        rename_i pairs
        cases hf : prog.findFun? fnName <;> rw [hf] at hchk <;> try contradiction
        dsimp only at hchk
        rename_i fDecl
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        cases hs : fDecl.ret.ty.toScalarTy? <;> rw [hs] at hchk <;> try contradiction
        dsimp only at hchk
        split at hchk <;> try contradiction
        injection hchk with hpEq; rcases hpEq with ⟨rfl, rfl⟩
        simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hlow
        cases hrl1 : evalRowExprList fuel' prog env1 cols r1 args <;> rw [hrl1] at hev1 <;> try contradiction
        cases hrl2 : evalRowExprList fuel' prog env2 cols r2 args <;> rw [hrl2] at hev2 <;> try contradiction
        have hargsEq := ihREL hprog hsafeProg env1 env2 cols r1 r2 args pairs _ _
          henv hcols hr1Wf hr2Wf hrowEq ha hrl1 hrl2
        have hvsEq := valListEquiv_scalar_all_low_eq hd hargsEq hlow.2
        subst hvsEq
        rw [hev1] at hev2; injection hev2 with hvEq; subst hvEq
        exact ValPayloadEquiv.refl_of_sortable hd hwf1 (ScalarTy.isSortable_toTy sTy)
    · unfold RowExprListNIAt
      intro hprog hsafeProg env1 env2 cols r1 r2 rs pairs vs1 vs2 henv hcols hr1Wf hr2Wf hrowEq hchk hev1 hev2
      cases rs with
      | nil =>
        unfold checkRowExprList at hchk; injection hchk with h; subst h
        unfold evalRowExprList at hev1 hev2
        injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
        exact .nil
      | cons r rest =>
        unfold checkRowExprList at hchk; simp only [bind, Except.bind] at hchk
        unfold evalRowExprList at hev1 hev2; dsimp only at hev1 hev2
        cases hr : checkRowExpr prog (envToTyEnv env1) cols r with
        | error _ => rw [hr] at hchk; contradiction
        | ok hp1 =>
          rcases hp1 with ⟨st, ts⟩; rw [hr] at hchk; dsimp only at hchk
          cases hrest : checkRowExprList prog (envToTyEnv env1) cols rest with
          | error _ => rw [hrest] at hchk; contradiction
          | ok tlPairs =>
            rw [hrest] at hchk; injection hchk with h; subst h
            cases he1 : evalRowExpr fuel' prog env1 cols r1 r <;> rw [he1] at hev1 <;> try contradiction
            cases he2 : evalRowExpr fuel' prog env2 cols r2 r <;> rw [he2] at hev2 <;> try contradiction
            cases htl1 : evalRowExprList fuel' prog env1 cols r1 rest <;> rw [htl1] at hev1 <;> try contradiction
            cases htl2 : evalRowExprList fuel' prog env2 cols r2 rest <;> rw [htl2] at hev2 <;> try contradiction
            injection hev1 with h1; injection hev2 with h2; subst h1; subst h2
            exact .cons
              (ihRE hprog hsafeProg env1 env2 cols r1 r2 r st ts _ _ henv hcols hr1Wf hr2Wf hrowEq hr he1 he2)
              (ihREL hprog hsafeProg env1 env2 cols r1 r2 rest _ _ _ henv hcols hr1Wf hr2Wf hrowEq hrest htl1 htl2)

theorem evalRowExpr_low_eq {fuel : Nat} {prog : Program} {L : TagSet}
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    {env1 env2 : Env} {cols : List ColSpec} {r1 r2 : TableRow}
    {re : RowExpr} {sTy : ScalarTy} {rTags : TagSet} {v1 v2 : Val}
    (henv : EnvEquiv prog L env1 env2)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true)
    (hr1Wf : CellsWf prog r1.cells cols)
    (hr2Wf : CellsWf prog r2.cells cols)
    (hrowEq : RowEquiv L cols r1 r2)
    (hchk : checkRowExpr prog (envToTyEnv env1) cols re = .ok (sTy, rTags))
    (hlow : rTags.subset L = true)
    (hev1 : evalRowExpr fuel prog env1 cols r1 re = .ok v1)
    (hev2 : evalRowExpr fuel prog env2 cols r2 re = .ok v2) :
    v1 = v2 := by
  have hd : progDatasSortableForNI prog L = true := by
    simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
  have hvEq := (evalRowExpr_ni_all fuel prog L).1 hprog hsafeProg env1 env2 cols r1 r2
    re sTy rTags v1 v2 henv hcols hr1Wf hr2Wf hrowEq hchk hev1 hev2
  exact ValEquiv.scalar_low_eq (sTy := sTy) hd hvEq hlow

/-! ### Standalone Host Capability Evaluation Non-Interference (`evalHostOp_ni`) -/

private theorem relList_csvFixture_find {prog : Program} {L : TagSet} (path : String) :
    ∀ {fxs1 fxs2 : List (String × TableVal × TableVal)},
      RelList (CsvFixtureEquiv prog L) fxs1 fxs2 →
      ((fxs1.find? (fun x => x.1 == path) = none ∧ fxs2.find? (fun x => x.1 == path) = none) ∨
       ∃ fx1 fx2,
         fxs1.find? (fun x => x.1 == path) = some fx1 ∧
         fxs2.find? (fun x => x.1 == path) = some fx2 ∧
         CsvFixtureEquiv prog L fx1 fx2)
  | [], [], .nil => Or.inl ⟨rfl, rfl⟩
  | fx1 :: _, fx2 :: _, .cons hfx htl => by
    simp only [List.find?, hfx.pathEq]
    cases (fx2.1 == path)
    · exact relList_csvFixture_find path htl
    · exact Or.inr ⟨fx1, fx2, rfl, rfl, hfx⟩

private theorem declassify_tags_subset_L {vTags capTs pc clearTags L : TagSet}
    (hcl : clearTags.subset L = true)
    (hres : ((((vTags.union capTs).union pc).diff clearTags).union pc).subset L = true) :
    vTags.subset L = true := by
  rw [TagSet.subset_iff]
  intro t ht
  cases hmem : clearTags.mem t
  · apply (TagSet.subset_iff _ _).mp hres t
    simp [ht, hmem]
  · exact (TagSet.subset_iff _ _).mp hcl t hmem

set_option maxHeartbeats 400000 in
theorem evalHostOp_ni {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {op : HostOp} {argLTys : List LTy} {vs1 vs2 : List Val} {lty : LTy}
    {w1 w2 w1' w2' : World} {v1 v2 : Val}
    (hprog : checkProgram prog = .ok ())
    (hsafeOp : hostOpSafeForNI L op = true)
    (hargSinks : ltyListSinksAllowed L argLTys = true)
    (hargs : ValListEquiv prog L vs1 vs2 argLTys)
    (hw : WorldEquiv prog L w1 w2)
    (hchk : checkHostOp prog pc inSpec op argLTys = .ok lty)
    (hev1 : evalHostOp prog op vs1 w1 = .ok v1 w1')
    (hev2 : evalHostOp prog op vs2 w2 = .ok v2 w2') :
    ValEquiv prog L v1 v2 lty ∧ WorldEquiv prog L w1' w2' := by
  have hwfOut1 := evalHostOp_sound hprog hchk hargs.wf_left hw.wf1
  have hwfOut2 := evalHostOp_sound hprog hchk hargs.wf_right hw.wf2
  rw [hev1] at hwfOut1; cases hwfOut1 with | ok hwf1 hwwf1 =>
  rw [hev2] at hwfOut2; cases hwfOut2 with | ok hwf2 hwwf2 =>
  have hs1 := evalHostOp_valSafe (prog := prog) (op := op) (w := w1) hargs.safe_left
  have hs2 := evalHostOp_valSafe (prog := prog) (op := op) (w := w2) hargs.safe_right
  rw [hev1] at hs1; rw [hev2] at hs2
  dsimp only [outcomeValSafe] at hs1 hs2
  -- Helper to rebuild `WorldEquiv` when DB/CSV/secret heaps are untouched
  have mkWorldEq :
      w1'.args = w2'.args →
      w1'.clockMicros = w2'.clockMicros →
      w1'.stdout = w2'.stdout →
      w1'.stderr = w2'.stderr →
      w1'.writtenFiles = w2'.writtenFiles →
      w1'.writtenTables = w2'.writtenTables →
      w1'.runtimeAllowExport = w2'.runtimeAllowExport →
      w1'.fakeConsoles = w2'.fakeConsoles →
      w1'.fakeFiles = w2'.fakeFiles →
      w1'.fakeHttps = w2'.fakeHttps →
      w1'.realCsvFixtures = w1.realCsvFixtures →
      w2'.realCsvFixtures = w2.realCsvFixtures →
      w1'.realDBTables = w1.realDBTables →
      w2'.realDBTables = w2.realDBTables →
      w1'.fakeDBs = w1.fakeDBs →
      w2'.fakeDBs = w2.fakeDBs →
      w1'.realSecrets = w1.realSecrets →
      w2'.realSecrets = w2.realSecrets →
      w1'.fakeSecrets = w1.fakeSecrets →
      w2'.fakeSecrets = w2.fakeSecrets →
      WorldEquiv prog L w1' w2' := by
    intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hc1 hc2 hd1 hd2 hf1 hf2 hs1' hs2' hfs1 hfs2
    exact {
      wf1 := hwwf1, wf2 := hwwf2, argsEq := h1, clockEq := h2,
      stdoutEq := h3, stderrEq := h4, writtenFilesEq := h5, writtenTablesEq := h6,
      allowExportEq := h7, fakeConsolesEq := h8, fakeFilesEq := h9, fakeHttpsEq := h10,
      csvFixturesEquiv := hc1 ▸ hc2 ▸ hw.csvFixturesEquiv,
      realDBTablesEquiv := hd1 ▸ hd2 ▸ hw.realDBTablesEquiv,
      fakeDBsEquiv := hf1 ▸ hf2 ▸ hw.fakeDBsEquiv,
      secretsLowEq := fun hl => by rw [hs1', hs2', hfs1, hfs2]; exact hw.secretsLowEq hl
    }
  unfold checkHostOp at hchk
  split at hchk
  -- 1. argsGet
  · injection hchk with hret; subst hret
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.wf_left; cases ha.wf_right
    injection hev1 with hv1 hw1'; injection hev2 with hv2 hw2'
    subst hv1; subst hv2; subst hw1'; subst hw2'
    refine ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => ?_), hw⟩
    rw [hw.argsEq]
    have hlist : ∀ (ss : List String), ValAllEquiv prog L (ss.map Val.text) (ss.map Val.text) (.mk .text TagSet.empty) := by
      intro ss; induction ss with
      | nil => exact .nil _
      | cons s tl ih => exact .cons (.low rfl (.text s) (.text s) rfl rfl (.text s)) ih
    exact .list (hlist w2.args)
  -- 2. clockNow
  · injection hchk with hret; subst hret
    rcases valListEquiv_one hargs with ⟨a1, a2, rfl, rfl, ha⟩
    cases ha.wf_left; cases ha.wf_right
    injection hev1 with hv1 hw1'; injection hev2 with hv2 hw2'
    subst hv1; subst hv2; subst hw1'; subst hw2'
    refine ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => ?_), hw⟩
    rw [hw.clockEq]; exact .timestamp _
  -- 3. consolePrint
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_two hargs with ⟨c1, c2, m1, m2, rfl, rfl, hc, hm⟩
    cases hc.payload heffLow.1.2 with | capConsole h _ =>
    cases hm.payload heffLow.2 with | text msg =>
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases h with
      | real =>
        dsimp only at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit),
          mkWorldEq hw.argsEq hw.clockEq (by simp [hw.stdoutEq]) hw.stderrEq hw.writtenFilesEq
            hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq hw.fakeHttpsEq
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
      | fake fid =>
        dsimp only at hev1 hev2
        rw [hw.fakeConsolesEq] at hev1
        cases hfc : w2.fakeConsoles[fid]? with
        | none =>
          rw [hfc] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit), hw⟩
        | some _ =>
          rw [hfc] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
              hw.writtenTablesEq hw.allowExportEq rfl hw.fakeFilesEq hw.fakeHttpsEq
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 4. consoleError
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_two hargs with ⟨c1, c2, m1, m2, rfl, rfl, hc, hm⟩
    cases hc.payload heffLow.1.2 with | capConsole h _ =>
    cases hm.payload heffLow.2 with | text msg =>
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases h with
      | real =>
        dsimp only at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit),
          mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq (by simp [hw.stderrEq]) hw.writtenFilesEq
            hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq hw.fakeHttpsEq
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
      | fake fid =>
        dsimp only at hev1 hev2
        rw [hw.fakeConsolesEq] at hev1
        cases hfc : w2.fakeConsoles[fid]? with
        | none =>
          rw [hfc] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit), hw⟩
        | some _ =>
          rw [hfc] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
              hw.writtenTablesEq hw.allowExportEq rfl hw.fakeFilesEq hw.fakeHttpsEq
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 5. consolePrintTable
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_two hargs with ⟨c1, c2, t1, t2, rfl, rfl, hc, htV⟩
    cases hc.payload heffLow.1.1.2 with | capConsole h _ =>
    cases htV.payload heffLow.1.2 with | table ht =>
    rcases ht.totalTags_cells_eq heffLow.2 with ⟨hcolsEq, hcellsEq⟩
    have hlineEq := renderTableText_eq_of_cells_eq hcolsEq hcellsEq
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate, hlineEq] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases h with
      | real =>
        dsimp only at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit),
          mkWorldEq hw.argsEq hw.clockEq (by simp [hw.stdoutEq]) hw.stderrEq hw.writtenFilesEq
            hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq hw.fakeHttpsEq
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
      | fake fid =>
        dsimp only at hev1 hev2
        rw [hw.fakeConsolesEq] at hev1
        cases hfc : w2.fakeConsoles[fid]? with
        | none =>
          rw [hfc] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit), hw⟩
        | some _ =>
          rw [hfc] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .unit),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
              hw.writtenTablesEq hw.allowExportEq rfl hw.fakeFilesEq hw.fakeHttpsEq
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 6. readCsv
  · rename_i schemaName capTs pathTs
    cases hfs : prog.findSchema? schemaName with
    | none => simp [hfs] at hchk
    | some sDecl =>
      simp only [hfs, Except.ok.injEq] at hchk; subst hchk
      rcases valListEquiv_two hargs with ⟨c1, c2, p1, p2, rfl, rfl, hc, hp⟩
      cases hc.wf_left; cases hp.wf_left with | text path1 =>
      cases hc.wf_right; cases hp.wf_right with | text path2 =>
      have hw1Eq : w1' = w1 := by
        simp only [evalHostOp, hfs] at hev1
        cases hf1' : w1.realCsvFixtures.find? _ with
        | none => rw [hf1'] at hev1; injection hev1 with _ hwEq; exact hwEq.symm
        | some fx =>
          rcases fx with ⟨_, _, _⟩; rw [hf1'] at hev1; dsimp only at hev1
          split at hev1 <;> injection hev1 with _ hwEq <;> exact hwEq.symm
      have hw2Eq : w2' = w2 := by
        simp only [evalHostOp, hfs] at hev2
        cases hf2' : w2.realCsvFixtures.find? _ with
        | none => rw [hf2'] at hev2; injection hev2 with _ hwEq; exact hwEq.symm
        | some fx =>
          rcases fx with ⟨_, _, _⟩; rw [hf2'] at hev2; dsimp only at hev2
          split at hev2 <;> injection hev2 with _ hwEq <;> exact hwEq.symm
      subst hw1Eq; subst hw2Eq
      refine ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun hctxLow => ?_), hw⟩
      simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at hctxLow
      cases hp.payload hctxLow.2
      simp only [evalHostOp, hfs] at hev1 hev2
      rcases relList_csvFixture_find path1 hw.csvFixturesEquiv with ⟨hn1, hn2⟩ | ⟨fx1, fx2, hf1, hf2, hfxEq⟩
      · rw [hn1] at hev1; rw [hn2] at hev2
        injection hev1 with hv1 _; injection hev2 with hv2 _; subst hv1; subst hv2
        cases hwf1 with | resOk htwf =>
        cases htwf with | tuple hlwf =>
        cases hlwf with | cons hgwf hlwf2 =>
        cases hlwf2 with | cons hbwf _ =>
        refine .resOk (.tuple (.cons (.low rfl hgwf hgwf rfl rfl (.table ?_))
          (.cons (.low rfl hbwf hbwf rfl rfl (.table ?_)) .nil)))
        · exact ⟨hgwf, hgwf, (fun _ c hc hk => by
            cases hgwf with | table _ hsch _ =>
            rcases checkSchema_valid hprog hfs with ⟨_, _, _⟩
            have hmemS := List.mem_of_find?_eq_some hfs
            have hsc := (checkProgram_parts hprog).2.1
            unfold checkSchemaDecls at hsc
            split at hsc <;> try contradiction
            split at hsc <;> try contradiction
            rename_i hallS
            have hsd := (List.all_eq_true.mp hallS) sDecl hmemS
            simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsd
            have hraw := (hsd.2 c hc).2
            rw [hk] at hraw; nomatch hraw),
            (fun _ => by split; exact .nil; exact ⟨[], .nil, .nil⟩),
            fun hsum _ => by
              have hmemS := List.mem_of_find?_eq_some hfs
              have hsc := (checkProgram_parts hprog).2.1
              unfold checkSchemaDecls at hsc
              split at hsc <;> try contradiction
              split at hsc <;> try contradiction
              rename_i hallS
              have hsd := (List.all_eq_true.mp hallS) sDecl hmemS
              simp only [Bool.and_eq_true] at hsd
              rw [hsum] at hsd; nomatch hsd.1.1.1⟩
        · exact ⟨hbwf, hbwf, (fun _ c hc hk => by
            simp only [quarantineBadRowTableTy, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> nomatch hk),
            (fun _ => by split; exact .nil; exact ⟨[], .nil, .nil⟩),
            fun h _ => by nomatch h⟩
      · rcases fx1 with ⟨p1', gTV1, bTV1⟩
        rcases fx2 with ⟨p2', gTV2, bTV2⟩
        rw [hf1] at hev1; rw [hf2] at hev2
        dsimp only at hev1 hev2
        have hcondEq : (decide (gTV1.cols.map ColSpec.ty = sDecl.schema.cols.map ColSpec.ty) &&
            decide (bTV1.cols.map ColSpec.ty = (quarantineBadRowTableTy sDecl.schema).cols.map ColSpec.ty)) =
            (decide (gTV2.cols.map ColSpec.ty = sDecl.schema.cols.map ColSpec.ty) &&
            decide (bTV2.cols.map ColSpec.ty = (quarantineBadRowTableTy sDecl.schema).cols.map ColSpec.ty)) := by
          rw [hfxEq.goodTysEq, hfxEq.badTysEq]
        cases hcond : (decide (gTV1.cols.map ColSpec.ty = sDecl.schema.cols.map ColSpec.ty) &&
            decide (bTV1.cols.map ColSpec.ty = (quarantineBadRowTableTy sDecl.schema).cols.map ColSpec.ty))
        · rw [hcond] at hev1 hcondEq
          rw [← hcondEq] at hev2
          simp only [Bool.false_eq_true, ↓reduceIte, Outcome.ok.injEq] at hev1 hev2
          rcases hev1 with ⟨rfl, _⟩; rcases hev2 with ⟨rfl, _⟩
          exact .resErr (.text _)
        · rw [hcond] at hev1 hcondEq
          rw [← hcondEq] at hev2
          simp only [↓reduceIte, Outcome.ok.injEq] at hev1 hev2
          rcases hev1 with ⟨rfl, _⟩; rcases hev2 with ⟨rfl, _⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          rcases hfxEq.schemaRows sDecl (List.mem_of_find?_eq_some hfs) hcond.1 hcond.2 with ⟨hgEq, hbEq⟩
          have hgW := hgEq.widenRowOrderTags ((pc.union capTs).union pathTs) ((pc.union capTs).union pathTs)
          have hbW := hbEq.widenRowOrderTags ((pc.union capTs).union pathTs) ((pc.union capTs).union pathTs)
          exact .resOk (.tuple (.cons (.low rfl hgW.wf1 hgW.wf2 rfl rfl (.table hgW))
            (.cons (.low rfl hbW.wf1 hbW.wf2 rfl rfl (.table hbW)) .nil)))
  -- 7. writeFile
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_three hargs with ⟨c1, c2, p1, p2, s1, s2, rfl, rfl, hc, hp, hsV⟩
    cases hc.payload heffLow.1.1.2 with | capWriteFiles h _ _ =>
    cases hp.payload heffLow.1.2 with | text relPath =>
    cases hsV.payload heffLow.2 with | text content =>
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases hsafe : isSafeRelativePath relPath with
      | false =>
        simp only [hsafe, Bool.not_false, ↓reduceIte] at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)), hw⟩
      | true =>
        simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hev1 hev2
        cases h with
        | real =>
          dsimp only at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq (by simp [hw.writtenFilesEq])
              hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq hw.fakeHttpsEq
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
        | fake fid =>
          dsimp only at hev1 hev2
          rw [hw.fakeFilesEq] at hev1
          cases hff : w2.fakeFiles[fid]? with
          | none =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit), hw⟩
          | some _ =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit),
              mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
                hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq rfl hw.fakeHttpsEq
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 8. writeReportHtml
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_three hargs with ⟨c1, c2, p1, p2, r1, r2, rfl, rfl, hc, hp, hrV⟩
    cases hc.payload heffLow.1.1.1.2 with | capWriteFiles h _ _ =>
    cases hp.payload heffLow.1.1.2 with | text relPath =>
    cases hrV.payload heffLow.2 with | report hrv =>
    have hrvEq := hrv heffLow.1.2; subst hrvEq
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases hsafe : isSafeRelativePath relPath with
      | false =>
        simp only [hsafe, Bool.not_false, ↓reduceIte] at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)), hw⟩
      | true =>
        simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hev1 hev2
        cases h with
        | real =>
          dsimp only at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq (by simp [hw.writtenFilesEq])
              hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq hw.fakeHttpsEq
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
        | fake fid =>
          dsimp only at hev1 hev2
          rw [hw.fakeFilesEq] at hev1
          cases hff : w2.fakeFiles[fid]? with
          | none =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit), hw⟩
          | some _ =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit),
              mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
                hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq rfl hw.fakeHttpsEq
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 9. writeTable
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i hnotEffSub
    split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    simp only [Bool.not_eq_true, Bool.not_eq_false'] at hnotEffSub
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans hnotEffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_two hargs with ⟨c1, c2, t1, t2, rfl, rfl, hc, htV⟩
    cases hc.payload heffLow.1.1.1.2 with | capWriteTable h _ _ =>
    cases htV.payload heffLow.1.1.2 with | table ht =>
    rcases ht.totalTags_cells_eq (by unfold TableTy.totalTags; simp [heffLow.1.2.1, heffLow.1.2.2, heffLow.2]) with ⟨hcolsEq, hcellsEq⟩
    dsimp only [evalHostOp] at hev1 hev2
    rw [hcolsEq, hcellsEq] at hev1
    cases hci : checkedInt _ <;> rw [hci] at hev1 hev2 <;> try contradiction
    rename_i cntVal
    have hcntInt : ∃ n, cntVal = .int n := by
      unfold checkedInt at hci; split at hci <;> first | contradiction | (injection hci with e; exact ⟨_, e.symm⟩)
    rcases hcntInt with ⟨n, rfl⟩
    cases h with
    | real =>
      dsimp only at hev1 hev2
      rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
      exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk (.int n)),
        mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
          (by simp [hw.writtenTablesEq]) hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq hw.fakeHttpsEq
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
    | fake _ =>
      dsimp only at hev1 hev2
      rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
      exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk (.int n)), hw⟩
  -- 10. declassifyApprove
  · simp only [bind, Except.bind] at hchk
    repeat (split at hchk <;> try contradiction)
    injection hchk with hret; subst hret
    unfold hostOpSafeForNI at hsafeOp
    rcases valListEquiv_three hargs with ⟨c1, c2, u1, u2, r1, r2, rfl, rfl, hc, hu, hr⟩
    cases hc.wf_left; cases hr.wf_left; cases hc.wf_right; cases hr.wf_right
    dsimp only [evalHostOp] at hev1 hev2
    injection hev1 with hv1 hw1'; injection hev2 with hv2 hw2'
    subst hv1; subst hv2; subst hw1'; subst hw2'
    exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2
      (fun hresLow => hu.payload (declassify_tags_subset_L hsafeOp hresLow)), hw⟩
  -- 11. rawSqlQuery
  · rcases valListEquiv_two hargs with ⟨c1, _, s1, _, rfl, _, hc, hsV⟩
    cases hc.wf_left; cases hsV.wf_left
    unfold evalHostOp at hev1; contradiction
  -- 12. httpsGetJson
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_two hargs with ⟨c1, c2, u1, u2, rfl, rfl, hc, hu⟩
    cases hc.payload heffLow.1.2 with | capHttpsAllow h _ _ =>
    cases hu.payload heffLow.2 with | text url =>
    cases h with
    | real => unfold evalHostOp at hev1; contradiction
    | fake fid =>
      dsimp only [evalHostOp, checkRuntimeExportGate] at hev1 hev2
      rw [hw.fakeHttpsEq] at hev1
      cases hfh : w2.fakeHttps[fid]? with
      | none =>
        rw [hfh] at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)), hw⟩
      | some fh =>
        rw [hfh] at hev1 hev2; dsimp only at hev1 hev2
        cases hresp : fh.responses.find? (fun x => x.1 == url) with
        | none =>
          rw [hresp] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
              hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
        | some pair =>
          rcases pair with ⟨_, body⟩
          rw [hresp] at hev1 hev2
          rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
          exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk (.text body)),
            mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
              hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq hw.fakeFilesEq rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 13. readParquet
  · split at hchk <;> try contradiction
    injection hchk with hret; subst hret
    rcases valListEquiv_two hargs with ⟨c1, c2, p1, p2, rfl, rfl, hc, hp⟩
    cases hc.wf_left with | capReadFiles h1 =>
    cases hp.wf_left
    cases hc.wf_right with | capReadFiles h2 =>
    cases hp.wf_right
    cases h1 with
    | real => unfold evalHostOp at hev1; contradiction
    | fake _ =>
      cases h2 with
      | real => unfold evalHostOp at hev2; contradiction
      | fake _ =>
        unfold evalHostOp at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)), hw⟩
  -- 14..15. writeParquet, writeXlsx
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_three hargs with ⟨c1, c2, p1, p2, t1, t2, rfl, rfl, hc, hp, htV⟩
    cases hc.payload heffLow.1.1.1.2 with | capWriteFiles h _ _ =>
    cases hp.payload heffLow.1.1.2 with | text relPath =>
    cases htV.payload heffLow.1.2 with | table ht =>
    rcases ht.totalTags_cells_eq heffLow.2 with ⟨hcolsEq, hcellsEq⟩
    have hreprEq := renderTableText_eq_of_cells_eq hcolsEq hcellsEq
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases hsafe : isSafeRelativePath relPath with
      | false =>
        simp only [hsafe, Bool.not_false, ↓reduceIte] at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)), hw⟩
      | true =>
        simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hev1 hev2
        cases h with
        | real => contradiction
        | fake fid =>
          dsimp only at hev1 hev2
          rw [hw.fakeFilesEq, hreprEq] at hev1
          cases hff : w2.fakeFiles[fid]? with
          | none =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit), hw⟩
          | some _ =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit),
              mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
                hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq rfl hw.fakeHttpsEq
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  · simp only [bind, Except.bind] at hchk
    split at hchk <;> try contradiction
    split at hchk <;> try contradiction
    rename_i heffSub
    injection hchk with hret; subst hret
    simp only [ltyListSinksAllowed, ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hargSinks
    have heffLow := TagSet.subset_trans heffSub hargSinks.1
    simp only [TagSet.union_subset_iff, Bool.and_eq_true] at heffLow
    rcases valListEquiv_three hargs with ⟨c1, c2, p1, p2, t1, t2, rfl, rfl, hc, hp, htV⟩
    cases hc.payload heffLow.1.1.1.2 with | capWriteFiles h _ _ =>
    cases hp.payload heffLow.1.1.2 with | text relPath =>
    cases htV.payload heffLow.1.2 with | table ht =>
    rcases ht.totalTags_cells_eq heffLow.2 with ⟨hcolsEq, hcellsEq⟩
    have hreprEq := renderTableText_eq_of_cells_eq hcolsEq hcellsEq
    dsimp only [evalHostOp] at hev1 hev2
    have hgate : ∀ al, checkRuntimeExportGate h al w1 = checkRuntimeExportGate h al w2 :=
      fun al => by simp [checkRuntimeExportGate, hw.allowExportEq]
    rw [hgate] at hev1
    cases hcg : checkRuntimeExportGate h _ w2 with
    | some _ => rw [hcg] at hev1; contradiction
    | none =>
      rw [hcg] at hev1 hev2
      cases hsafe : isSafeRelativePath relPath with
      | false =>
        simp only [hsafe, Bool.not_false, ↓reduceIte] at hev1 hev2
        rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
        exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resErr (.text _)), hw⟩
      | true =>
        simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hev1 hev2
        cases h with
        | real => contradiction
        | fake fid =>
          dsimp only at hev1 hev2
          rw [hw.fakeFilesEq, hreprEq] at hev1
          cases hff : w2.fakeFiles[fid]? with
          | none =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit), hw⟩
          | some _ =>
            rw [hff] at hev1 hev2
            rcases hev1 with ⟨rfl, rfl⟩; rcases hev2 with ⟨rfl, rfl⟩
            exact ⟨ValEquiv.mk_smart hwf1 hwf2 hs1 hs2 (fun _ => .resOk .unit),
              mkWorldEq hw.argsEq hw.clockEq hw.stdoutEq hw.stderrEq hw.writtenFilesEq
                hw.writtenTablesEq hw.allowExportEq hw.fakeConsolesEq rfl hw.fakeHttpsEq
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  -- 16..20. fakeConsole, fakeFiles, fakeDB, fakeHttps, fakeSecret
  · simp [hostOpSafeForNI] at hsafeOp
  · simp [hostOpSafeForNI] at hsafeOp
  · simp [hostOpSafeForNI] at hsafeOp
  · simp [hostOpSafeForNI] at hsafeOp
  · simp [hostOpSafeForNI] at hsafeOp
  -- 21. catch-all
  · contradiction


/-! ## Part 4B.1: Database Fixture Schema Preservation (`WorldDBSame` & `valClosureSafe`) -/

def WorldDBSame (w w' : World) : Prop :=
  w'.realDBTables = w.realDBTables ∧ w'.fakeDBs = w.fakeDBs

theorem WorldDBSame.refl (w : World) : WorldDBSame w w := ⟨rfl, rfl⟩

theorem WorldDBSame.trans {w1 w2 w3 : World}
    (h12 : WorldDBSame w1 w2) (h23 : WorldDBSame w2 w3) : WorldDBSame w1 w3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

mutual
theorem exprRespectsDB_congr {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {e : Expr} → exprRespectsDB w1 e → exprRespectsDB w2 e
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .constRef _, _ => trivial
  | .tableLit _ _, _ => trivial
  | .letE _ _ b1 b2, h => ⟨exprRespectsDB_congr hw (e := b1) h.1, exprRespectsDB_congr hw (e := b2) h.2⟩
  | .join _ _ b1 b2, h => ⟨exprRespectsDB_congr hw (e := b1) h.1, exprRespectsDB_congr hw (e := b2) h.2⟩
  | .ifE c t e, h => ⟨exprRespectsDB_congr hw (e := c) h.1, exprRespectsDB_congr hw (e := t) h.2.1, exprRespectsDB_congr hw (e := e) h.2.2⟩
  | .caseE s arms, h => ⟨exprRespectsDB_congr hw (e := s) h.1, armsRespectsDB_congr hw (arms := arms) h.2⟩
  | .lam _ _ _ b, h => exprRespectsDB_congr hw (e := b) h
  | .proj b _, h => exprRespectsDB_congr hw (e := b) h
  | .fail b, h => exprRespectsDB_congr hw (e := b) h
  | .app f as1, h => ⟨exprRespectsDB_congr hw (e := f) h.1, listRespectsDB_congr hw (es := as1) h.2⟩
  | .call _ as1, h => listRespectsDB_congr hw (es := as1) h
  | .jump _ as1, h => listRespectsDB_congr hw (es := as1) h
  | .tuple as1, h => listRespectsDB_congr hw (es := as1) h
  | .ctor _ _ as1, h => listRespectsDB_congr hw (es := as1) h
  | .prim _ as1, h => listRespectsDB_congr hw (es := as1) h
  | .host _ as1, h => listRespectsDB_congr hw (es := as1) h
  | .rel p, h => planRespectsDB_congr hw (p := p) h
  | .stop _ none, _ => trivial
  | .stop _ (some b), h => exprRespectsDB_congr hw (e := b) h
  termination_by e => sizeOf e

theorem listRespectsDB_congr {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {es : List Expr} → listRespectsDB w1 es → listRespectsDB w2 es
  | [], _ => trivial
  | e :: es, h => ⟨exprRespectsDB_congr hw (e := e) h.1, listRespectsDB_congr hw (es := es) h.2⟩
  termination_by es => sizeOf es

theorem armsRespectsDB_congr {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {arms : List CaseArm} → armsRespectsDB w1 arms → armsRespectsDB w2 arms
  | [], _ => trivial
  | .mk _ _ b :: rest, h => ⟨exprRespectsDB_congr hw (e := b) h.1, armsRespectsDB_congr hw (arms := rest) h.2⟩
  termination_by arms => sizeOf arms

theorem planRespectsDB_congr {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {p : Plan} → planRespectsDB w1 p → planRespectsDB w2 p
  | .sourceExpr e, h => exprRespectsDB_congr hw (e := e) h
  | .sourceDB cap _ _, h =>
    ⟨exprRespectsDB_congr hw (e := cap) h.1,
      fun st hst => h.2.1 st (hw.1 ▸ hst),
      fun fdb hfdb st hst => h.2.2 fdb (hw.2 ▸ hfdb) st hst⟩
  | .select p _, h => planRespectsDB_congr hw (p := p) h
  | .drop p _, h => planRespectsDB_congr hw (p := p) h
  | .rename p _, h => planRespectsDB_congr hw (p := p) h
  | .derive p _, h => planRespectsDB_congr hw (p := p) h
  | .filter p _, h => planRespectsDB_congr hw (p := p) h
  | .distinct p _, h => planRespectsDB_congr hw (p := p) h
  | .sort p _, h => planRespectsDB_congr hw (p := p) h
  | .limit p _, h => planRespectsDB_congr hw (p := p) h
  | .groupBy p _, h => planRespectsDB_congr hw (p := p) h
  | .summarize p _ _, h => planRespectsDB_congr hw (p := p) h
  | .suppressSmallGroups p _ _ _, h => planRespectsDB_congr hw (p := p) h
  | .window p _, h => planRespectsDB_congr hw (p := p) h
  | .fillGaps p _ _ _ _, h => planRespectsDB_congr hw (p := p) h
  | .pivotWider p _ _ _ _, h => planRespectsDB_congr hw (p := p) h
  | .crosstab p _ _ _ _, h => planRespectsDB_congr hw (p := p) h
  | .redact p _ _, h => planRespectsDB_congr hw (p := p) h
  | .join _ l r _ _, h => ⟨planRespectsDB_congr hw (p := l) h.1, planRespectsDB_congr hw (p := r) h.2⟩
  | .union l r, h => ⟨planRespectsDB_congr hw (p := l) h.1, planRespectsDB_congr hw (p := r) h.2⟩
  | .pseudonymize p _ sec, h => ⟨planRespectsDB_congr hw (p := p) h.1, exprRespectsDB_congr hw (e := sec) h.2⟩
  termination_by p => sizeOf p
end

theorem progRespectsDB_congr {w1 w2 : World} (hw : WorldDBSame w1 w2)
    {prog : Program} (hp : progRespectsDB w1 prog) : progRespectsDB w2 prog :=
  fun f hf hns => exprRespectsDB_congr hw (hp f hf hns)

mutual
def valClosureSafe (prog : Program) (L : TagSet) (w : World) : Val → Prop
  | .optSome u | .resOk u | .resErr u => valClosureSafe prog L w u
  | .tuple vs | .list vs | .ctor _ _ vs => valListClosureSafe prog L w vs
  | .map kvs => valPairsClosureSafe prog L w kvs
  | .closure params fnPc _ body capEnv =>
    exprSafeForNI L body = true ∧
    exprNoSpecCalls prog body = true ∧
    exprSuppressSafe prog L (extendTyEnv (envToTyEnv capEnv) params) fnPc body = true ∧
    exprRespectsDB w body ∧ envClosureSafe prog L w capEnv
  | _ => True
  termination_by structural v => v

def valListClosureSafe (prog : Program) (L : TagSet) (w : World) : List Val → Prop
  | [] => True
  | v :: vs => valClosureSafe prog L w v ∧ valListClosureSafe prog L w vs
  termination_by structural vs => vs

def valPairsClosureSafe (prog : Program) (L : TagSet) (w : World) : List (Val × Val) → Prop
  | [] => True
  | (k, v) :: rest => valClosureSafe prog L w k ∧ valClosureSafe prog L w v ∧ valPairsClosureSafe prog L w rest
  termination_by structural ps => ps

def envClosureSafe (prog : Program) (L : TagSet) (w : World) : List EnvEntry → Prop
  | [] => True
  | .mk _ _ v :: rest => valClosureSafe prog L w v ∧ envClosureSafe prog L w rest
  termination_by structural es => es
end

mutual
theorem valClosureSafe_imp_noSpecCalls {prog : Program} {L : TagSet} {w : World} :
    {v : Val} → valClosureSafe prog L w v → valNoSpecCalls prog v = true
  | .optSome u, h => valClosureSafe_imp_noSpecCalls (v := u) h
  | .resOk u, h => valClosureSafe_imp_noSpecCalls (v := u) h
  | .resErr u, h => valClosureSafe_imp_noSpecCalls (v := u) h
  | .tuple vs, h => valListClosureSafe_imp_noSpecCalls (vs := vs) h
  | .list vs, h => valListClosureSafe_imp_noSpecCalls (vs := vs) h
  | .ctor _ _ vs, h => valListClosureSafe_imp_noSpecCalls (vs := vs) h
  | .map kvs, h => valPairsClosureSafe_imp_noSpecCalls (ps := kvs) h
  | .closure _ _ _ _ capEnv, h => by
    simp [valNoSpecCalls, h.2.1, envClosureSafe_imp_noSpecCalls (es := capEnv) h.2.2.2.2]
  | .unit, _ | .bool _, _ | .int _, _ | .decimal _, _ | .float _, _ | .text _, _ | .bytes _, _
  | .date _, _ | .timestamp _, _ | .duration _, _ | .optNone, _ | .table _, _ | .dynTable _ _, _
  | .chart _, _ | .report _, _ | .profile _, _ | .linearModel _ _ _, _ | .statTest _ _, _
  | .capArgs, _ | .capClock, _ | .capConsole _ _, _ | .capReadFiles _, _ | .capWriteFiles _ _ _, _
  | .capReadDB _ _, _ | .capWriteTable _ _ _, _ | .capRawReadDB _, _ | .capHttpsAllow _ _ _, _
  | .capSecret _ _, _ | .capDeclassify _, _ => rfl
  termination_by v => sizeOf v

theorem valListClosureSafe_imp_noSpecCalls {prog : Program} {L : TagSet} {w : World} :
    {vs : List Val} → valListClosureSafe prog L w vs → valListNoSpecCalls prog vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp [valListNoSpecCalls, valClosureSafe_imp_noSpecCalls (v := v) h.1, valListClosureSafe_imp_noSpecCalls (vs := vs) h.2]
  termination_by vs => sizeOf vs

theorem valPairsClosureSafe_imp_noSpecCalls {prog : Program} {L : TagSet} {w : World} :
    {ps : List (Val × Val)} → valPairsClosureSafe prog L w ps → valPairsNoSpecCalls prog ps = true
  | [], _ => rfl
  | (k, v) :: rest, h => by
    simp [valPairsNoSpecCalls, valClosureSafe_imp_noSpecCalls (v := k) h.1,
      valClosureSafe_imp_noSpecCalls (v := v) h.2.1, valPairsClosureSafe_imp_noSpecCalls (ps := rest) h.2.2]
  termination_by ps => sizeOf ps

theorem envClosureSafe_imp_noSpecCalls {prog : Program} {L : TagSet} {w : World} :
    {es : List EnvEntry} → envClosureSafe prog L w es → envNoSpecCalls prog es = true
  | [], _ => rfl
  | .mk _ _ v :: rest, h => by
    simp [envNoSpecCalls, valClosureSafe_imp_noSpecCalls (v := v) h.1, envClosureSafe_imp_noSpecCalls (es := rest) h.2]
  termination_by es => sizeOf es
end

mutual
theorem valClosureSafe_congr {prog : Program} {L : TagSet} {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {v : Val} → valClosureSafe prog L w1 v → valClosureSafe prog L w2 v
  | .optSome u, h => valClosureSafe_congr hw (v := u) h
  | .resOk u, h => valClosureSafe_congr hw (v := u) h
  | .resErr u, h => valClosureSafe_congr hw (v := u) h
  | .tuple vs, h => valListClosureSafe_congr hw (vs := vs) h
  | .list vs, h => valListClosureSafe_congr hw (vs := vs) h
  | .ctor _ _ vs, h => valListClosureSafe_congr hw (vs := vs) h
  | .map kvs, h => valPairsClosureSafe_congr hw (ps := kvs) h
  | .closure _ _ _ body capEnv, h =>
    ⟨h.1, h.2.1, h.2.2.1, exprRespectsDB_congr hw (e := body) h.2.2.2.1, envClosureSafe_congr hw (es := capEnv) h.2.2.2.2⟩
  | .unit, _ | .bool _, _ | .int _, _ | .decimal _, _ | .float _, _ | .text _, _ | .bytes _, _
  | .date _, _ | .timestamp _, _ | .duration _, _ | .optNone, _ | .table _, _ | .dynTable _ _, _
  | .chart _, _ | .report _, _ | .profile _, _ | .linearModel _ _ _, _ | .statTest _ _, _
  | .capArgs, _ | .capClock, _ | .capConsole _ _, _ | .capReadFiles _, _ | .capWriteFiles _ _ _, _
  | .capReadDB _ _, _ | .capWriteTable _ _ _, _ | .capRawReadDB _, _ | .capHttpsAllow _ _ _, _
  | .capSecret _ _, _ | .capDeclassify _, _ => trivial
  termination_by v => sizeOf v

theorem valListClosureSafe_congr {prog : Program} {L : TagSet} {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {vs : List Val} → valListClosureSafe prog L w1 vs → valListClosureSafe prog L w2 vs
  | [], _ => trivial
  | v :: vs, h => ⟨valClosureSafe_congr hw (v := v) h.1, valListClosureSafe_congr hw (vs := vs) h.2⟩
  termination_by vs => sizeOf vs

theorem valPairsClosureSafe_congr {prog : Program} {L : TagSet} {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {ps : List (Val × Val)} → valPairsClosureSafe prog L w1 ps → valPairsClosureSafe prog L w2 ps
  | [], _ => trivial
  | (k, v) :: rest, h => ⟨valClosureSafe_congr hw (v := k) h.1, valClosureSafe_congr hw (v := v) h.2.1, valPairsClosureSafe_congr hw (ps := rest) h.2.2⟩
  termination_by ps => sizeOf ps

theorem envClosureSafe_congr {prog : Program} {L : TagSet} {w1 w2 : World} (hw : WorldDBSame w1 w2) :
    {es : List EnvEntry} → envClosureSafe prog L w1 es → envClosureSafe prog L w2 es
  | [], _ => trivial
  | .mk _ _ v :: rest, h => ⟨valClosureSafe_congr hw (v := v) h.1, envClosureSafe_congr hw (es := rest) h.2⟩
  termination_by es => sizeOf es
end

theorem valListClosureSafe_append {prog : Program} {L : TagSet} {w : World} :
    ∀ {xs ys : List Val},
      valListClosureSafe prog L w xs → valListClosureSafe prog L w ys → valListClosureSafe prog L w (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, ⟨hx, hxs⟩, hy => ⟨hx, valListClosureSafe_append hxs hy⟩

theorem envClosureSafe_append {prog : Program} {L : TagSet} {w : World} :
    ∀ {a b : Env}, envClosureSafe prog L w a → envClosureSafe prog L w b → envClosureSafe prog L w (a ++ b)
  | [], _, _, hb => hb
  | .mk _ _ _ :: _, _, ⟨ha, has⟩, hb => ⟨ha, envClosureSafe_append has hb⟩

theorem envClosureSafe_zip_params {prog : Program} {L : TagSet} {w : World} :
    ∀ {params : List (Ident × LTy)} {vs : List Val},
      valListClosureSafe prog L w vs →
      envClosureSafe prog L w ((List.zip params vs).map (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v }))
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | (_, _) :: _, _ :: _, ⟨hv, hvs⟩ => ⟨hv, envClosureSafe_zip_params hvs⟩

theorem envClosureSafe_reverse {prog : Program} {L : TagSet} {w : World} :
    ∀ {env : Env}, envClosureSafe prog L w env → envClosureSafe prog L w env.reverse
  | [], _ => trivial
  | .mk n l v :: _, ⟨hv, htl⟩ => by
    rw [List.reverse_cons]
    exact envClosureSafe_append (envClosureSafe_reverse htl) (⟨hv, trivial⟩ : envClosureSafe prog L w [.mk n l v])

private theorem lookupEnv_closureSafe {prog : Program} {L : TagSet} {w : World} :
    ∀ {env : Env} {name : Ident} {lty : LTy} {v : Val},
      envClosureSafe prog L w env → lookupEnv env name = some (lty, v) → valClosureSafe prog L w v
  | [], _, _, _, _, hl => nomatch hl
  | .mk _ _ _ :: _, _, _, _, ⟨hv, htl⟩, hl => by
    simp only [lookupEnv] at hl
    split at hl
    · injection hl with h; injection h with _ h2; subst h2; exact hv
    · exact lookupEnv_closureSafe htl hl

private theorem evalLiteral_closureSafe (prog : Program) (L : TagSet) (w : World) (lit : Literal) :
    valClosureSafe prog L w (evalLiteral lit) := by
  cases lit <;> trivial

private theorem checkedInt_closureSafe {prog : Program} {L : TagSet} {w : World} {n : Int} {v : Val}
    (h : checkedInt n = .ok v) : valClosureSafe prog L w v := by
  unfold checkedInt at h; split at h <;> first | contradiction | (injection h with e; subst e; trivial)

private theorem checkedDecimal_closureSafe {prog : Program} {L : TagSet} {w : World} {n : Int} {v : Val}
    (h : checkedDecimal n = .ok v) : valClosureSafe prog L w v := by
  unfold checkedDecimal at h; split at h <;> first | contradiction | (injection h with e; subst e; trivial)

private theorem flattenValLists_closureSafe {prog : Program} {L : TagSet} {w : World} :
    ∀ {nested flat : List Val},
      valListClosureSafe prog L w nested → flattenValLists nested = some flat → valListClosureSafe prog L w flat
  | [], _, _, hf => by injection hf with h; subst h; trivial
  | x :: _, _, ⟨hx, hxs⟩, hf => by
    cases x <;> try contradiction
    simp only [flattenValLists, Option.map_eq_some_iff] at hf
    rcases hf with ⟨tl, htl, rfl⟩
    exact valListClosureSafe_append hx (flattenValLists_closureSafe hxs htl)

private theorem buildPairs_closureSafe {prog : Program} {L : TagSet} {w : World} :
    ∀ {args : List Val} {ps : List (Val × Val)},
      valListClosureSafe prog L w args → buildPairs args = some ps → valPairsClosureSafe prog L w ps
  | [], _, _, hb => by injection hb with h; subst h; trivial
  | [_], _, _, hb => nomatch hb
  | _ :: _ :: _, _, ⟨hk, hv, hrest⟩, hb => by
    simp only [buildPairs, Option.map_eq_some_iff] at hb
    rcases hb with ⟨tl, htl, rfl⟩
    exact ⟨hk, hv, buildPairs_closureSafe hrest htl⟩

private theorem valPairsClosureSafe_snd {prog : Program} {L : TagSet} {w : World} :
    ∀ {ps : List (Val × Val)}, valPairsClosureSafe prog L w ps → ∀ p ∈ ps, valClosureSafe prog L w p.2
  | [], _, _, hm => nomatch hm
  | (_, _) :: _, ⟨_, hv, htl⟩, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hrest
    · exact hv
    · exact valPairsClosureSafe_snd htl _ hrest

private theorem evalPrimOp_closureSafe {prog : Program} {L : TagSet} {w : World} {op : PrimOp}
    {vs : List Val} {v : Val}
    (hvs : valListClosureSafe prog L w vs)
    (hev : evalPrimOp op vs = .ok v) :
    valClosureSafe prog L w v := by
  unfold evalPrimOp at hev
  split at hev
  all_goals (try simp only [valListClosureSafe, valClosureSafe] at hvs)
  all_goals (
    repeat (
      (try simp only [] at hev)
      first
      | contradiction
      | (injection hev with h; rw [← h])
      | (simp only [checkedInt, checkedDecimal] at hev; split at hev <;> try contradiction)
      | (split at hev <;> try contradiction)
    )
  )
  all_goals ((try simp only [] at hev); try (injection hev with h; rw [← h]))
  all_goals (try simp only [valClosureSafe])
  all_goals (
    first
    | trivial
    | exact hvs
    | exact hvs.1
    | exact hvs.2.1
    | exact valListClosureSafe_append hvs.1 ⟨hvs.2.1, trivial⟩
    | exact flattenValLists_closureSafe hvs.1 ‹flattenValLists _ = some _›
    | exact buildPairs_closureSafe hvs ‹buildPairs _ = some _›
    | exact valPairsClosureSafe_snd hvs.1 _ (List.mem_of_find?_eq_some ‹List.find? _ _ = some _›)
  )

def outcomeDBAndClosureSafe (prog : Program) (L : TagSet) (w : World) : Outcome → Prop
  | .ok v w' => valClosureSafe prog L w v ∧ WorldDBSame w w'
  | .stopped _ w' | .failed _ w' => WorldDBSame w w'
  | .jumped _ vs w' => valListClosureSafe prog L w vs ∧ WorldDBSame w w'
  | .wrong | .outOfFuel => True

private theorem outcomeDBAndClosureSafe_trans {prog : Program} {L : TagSet} {w1 w2 : World} {out : Outcome}
    (hw12 : WorldDBSame w1 w2)
    (hout : outcomeDBAndClosureSafe prog L w2 out) :
    outcomeDBAndClosureSafe prog L w1 out := by
  have hw21 : WorldDBSame w2 w1 := ⟨hw12.1.symm, hw12.2.symm⟩
  cases out with
  | ok v w3 => exact ⟨valClosureSafe_congr hw21 hout.1, hw12.trans hout.2⟩
  | stopped _ w3 | failed _ w3 => exact hw12.trans hout
  | jumped _ vs w3 => exact ⟨valListClosureSafe_congr hw21 hout.1, hw12.trans hout.2⟩
  | wrong | outOfFuel => trivial

private theorem evalHostOp_db_and_closureSafe {prog : Program} {L : TagSet} {op : HostOp}
    {vs : List Val} {w : World}
    (hsafe : hostOpSafeForNI L op = true)
    (hvs : valListClosureSafe prog L w vs) :
    outcomeDBAndClosureSafe prog L w (evalHostOp prog op vs w) := by
  have htextList : ∀ (ss : List String), valListClosureSafe prog L w (ss.map Val.text) := by
    intro ss; induction ss with
    | nil => trivial
    | cons _ _ ih => exact ⟨trivial, ih⟩
  cases op with
  | argsGet =>
    unfold evalHostOp; cases vs with
    | cons v tl => cases v <;> cases tl <;> first | trivial | exact ⟨htextList w.args, WorldDBSame.refl w⟩
    | nil => trivial
  | clockNow =>
    unfold evalHostOp; cases vs with
    | cons v tl => cases v <;> cases tl <;> first | trivial | exact ⟨trivial, WorldDBSame.refl w⟩
    | nil => trivial
  | writeTable =>
    unfold evalHostOp
    cases vs with
    | cons v1 tl1 =>
      cases v1 <;> try trivial
      cases tl1 with
      | cons v2 tl2 =>
        cases v2 <;> try trivial
        cases tl2 with
        | cons _ _ => trivial
        | nil =>
          dsimp only
          cases hci : checkedInt _ with
          | ok cntVal =>
            rename_i h _ _ _
            cases h <;> (dsimp only [outcomeDBAndClosureSafe, valClosureSafe]; exact ⟨checkedInt_closureSafe hci, WorldDBSame.refl w⟩)
          | stopped _ => exact WorldDBSame.refl w
          | outOfFuel | wrong => trivial
      | nil => trivial
    | nil => trivial
  | declassifyApprove _ =>
    unfold evalHostOp
    cases vs with
    | cons v1 tl1 =>
      cases v1 <;> try trivial
      cases tl1 with
      | cons v2 tl2 =>
        cases tl2 with
        | cons v3 tl3 =>
          cases v3 <;> try trivial
          cases tl3 with
          | nil => exact ⟨hvs.2.1, WorldDBSame.refl w⟩
          | cons _ _ => trivial
        | nil => trivial
      | nil => trivial
    | nil => trivial
  | _ =>
    unfold evalHostOp
    try (simp [hostOpSafeForNI] at hsafe)
    all_goals ((try simp only []); try split)
    all_goals ((try simp only []); try split)
    all_goals ((try simp only []); try split)
    all_goals ((try simp only []); try split)
    all_goals ((try simp only []); try split)
    all_goals ((try simp only []); try split)
    all_goals (try simp only [outcomeDBAndClosureSafe, valClosureSafe, valListClosureSafe, WorldDBSame])
    all_goals (
      first
      | trivial
      | exact ⟨trivial, rfl, rfl⟩
      | exact ⟨⟨trivial, trivial, trivial⟩, rfl, rfl⟩
      | exact ⟨rfl, rfl⟩
    )

private theorem matchCaseVal_closureSafe {prog : Program} {L armPc : TagSet} {w : World}
    {sVal : Val} {scrutLTy : LTy} {cName : Ident} {typedVals : List (LTy × Val)}
    (hs : valClosureSafe prog L w sVal)
    (hm : matchCaseVal prog sVal scrutLTy armPc = some (cName, typedVals)) :
    ∀ p ∈ typedVals, valClosureSafe prog L w p.2 := by
  unfold matchCaseVal at hm
  cases scrutLTy with | mk sty _ =>
  dsimp only [LTy.ty] at hm
  cases sty <;> cases sVal <;> (try simp only at hm) <;> try contradiction
  case bool.bool b =>
    cases b <;> injection hm with h <;> injection h with _ h2 <;> subst h2 <;> intro _ hm0 <;> nomatch hm0
  case option.optNone =>
    injection hm with h; injection h with _ h2; subst h2; intro _ hm0; nomatch hm0
  case option.optSome _ _ =>
    injection hm with h; injection h with _ h2; subst h2
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hs
  case result.resOk _ _ _ =>
    injection hm with h; injection h with _ h2; subst h2
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hs
  case result.resErr _ _ _ =>
    injection hm with h; injection h with _ h2; subst h2
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hs
  case data.ctor dName _ cn fields =>
    split at hm; nomatch hm
    cases hd : prog.findData? dName with
    | none => rw [hd] at hm; nomatch hm
    | some dDecl =>
      rw [hd] at hm; dsimp only at hm
      cases hc : dDecl.ctors.find? (fun c => c.name == cn) with
      | none => rw [hc] at hm; nomatch hm
      | some cDecl =>
        rw [hc] at hm; dsimp only at hm
        split at hm <;> try contradiction
        injection hm with h; injection h with _ h2; subst h2
        have hmemSafe : ∀ {fs : List Val}, valListClosureSafe prog L w fs → ∀ v ∈ fs, valClosureSafe prog L w v := by
          intro fs hfs v hv
          induction fs with
          | nil => nomatch hv
          | cons f ftl ih =>
            rcases List.mem_cons.mp hv with rfl | htl
            · exact hfs.1
            · exact ih hfs.2 htl
        intro p hp
        exact hmemSafe hs p.2 (List.of_mem_zip hp).2

private theorem matchCaseVal_fst_eq_expectedCaseSpecs {prog : Program} {armPc : TagSet}
    {sVal : Val} {sLTy : LTy} {specs : List (Ident × List LTy)}
    {cName : Ident} {typedVals : List (LTy × Val)}
    (hm : matchCaseVal prog sVal sLTy armPc = some (cName, typedVals))
    (hsp : expectedCaseSpecs prog sLTy.ty sLTy.effectiveTags = .ok specs) :
    ∃ fieldLTys,
      specs.find? (fun (sn, _) => sn == cName) = some (cName, fieldLTys) ∧
      typedVals.map Prod.fst = fieldLTys.map (fun f => f.addTags armPc) := by
  unfold matchCaseVal at hm
  cases sLTy with | mk sty sts =>
  dsimp only [LTy.ty] at hm hsp
  have haddEq : ∀ (f : LTy) (a b : TagSet), (f.addTags a).addTags b = f.addTags (a.union b) := by
    intro f a b; cases f with | mk _ t =>
    simp only [LTy.addTags, LTy.mk.injEq, true_and]
    exact TagSet.union_assoc t a b
  cases sty <;> cases sVal <;> (try simp only [expectedCaseSpecs] at hsp hm) <;> try contradiction
  case bool.bool b =>
    injection hsp with esp; subst esp
    cases b <;> (injection hm with h; injection h with h1 h2; subst h1; subst h2; exact ⟨[], rfl, rfl⟩)
  case option.optNone =>
    injection hsp with esp; subst esp
    injection hm with h; injection h with h1 h2; subst h1; subst h2; exact ⟨[], rfl, rfl⟩
  case option.optSome inner u =>
    injection hsp with esp; subst esp
    injection hm with h; injection h with h1 h2; subst h1; subst h2
    exact ⟨[LTy.mk inner (LTy.mk (.option inner) sts).effectiveTags], rfl, by simp [LTy.addTags]⟩
  case result.resOk okTy errTy u =>
    injection hsp with esp; subst esp
    injection hm with h; injection h with h1 h2; subst h1; subst h2
    exact ⟨[LTy.mk okTy (LTy.mk (.result okTy errTy) sts).effectiveTags], rfl, by simp [LTy.addTags]⟩
  case result.resErr okTy errTy e =>
    injection hsp with esp; subst esp
    injection hm with h; injection h with h1 h2; subst h1; subst h2
    exact ⟨[LTy.mk errTy (LTy.mk (.result okTy errTy) sts).effectiveTags], rfl, by simp [LTy.addTags]⟩
  case data.ctor dName vType cn fields =>
    split at hm; nomatch hm
    cases hd : prog.findData? dName with
    | none => rw [hd] at hm; nomatch hm
    | some dDecl =>
      rw [hd] at hm hsp; dsimp only at hm hsp
      injection hsp with esp; subst esp
      cases hc : dDecl.ctors.find? (fun c => c.name == cn) with
      | none => rw [hc] at hm; nomatch hm
      | some cDecl =>
        rw [hc] at hm; dsimp only at hm
        split at hm <;> try contradiction
        rename_i hlen
        have hlenEq : fields.length = cDecl.fields.length := by simpa using hlen
        injection hm with h; injection h with h1 h2; subst h1; subst h2
        have hcnEq : cDecl.name = cn := by
          have hs := List.find?_some hc; exact beq_iff_eq.mp hs
        have hfindMap : ∀ (cs : List CtorDecl),
            cs.find? (fun c => c.name == cn) = some cDecl →
            (cs.map (fun c => (c.name, c.fields.map (fun f => f.addTags (LTy.mk (.data dName) sts).effectiveTags)))).find?
              (fun (sn, _) => sn == cn) =
            some (cn, cDecl.fields.map (fun f => f.addTags (LTy.mk (.data dName) sts).effectiveTags)) := by
          intro cs hfc
          induction cs with
          | nil => simp at hfc
          | cons c rest ih =>
            simp only [List.map_cons, List.find?_cons] at hfc ⊢
            cases hcb : (c.name == cn) <;> simp only [hcb] at hfc ⊢
            · exact ih hfc
            · injection hfc with ec; subst ec; simp [hcnEq]
        refine ⟨cDecl.fields.map (fun f => f.addTags (LTy.mk (.data dName) sts).effectiveTags), hfindMap dDecl.ctors hc, ?_⟩
        rw [List.map_fst_zip (by simp [hlenEq]), List.map_map]
        apply List.map_congr_left
        intro f _; exact (haddEq f _ armPc).symm

private theorem evalSeq_db_and_closureSafe {prog : Program} {L pc : TagSet} {env : TyEnv} {w0 : World}
    (step : World → Expr → Outcome)
    (hstep : ∀ w e, WorldDBSame w0 w → exprSafeForNI L e = true → exprNoSpecCalls prog e = true →
      exprSuppressSafe prog L env pc e = true → exprRespectsDB w e → outcomeDBAndClosureSafe prog L w (step w e)) :
    ∀ {es : List Expr} {w : World},
      WorldDBSame w0 w →
      exprListSafeForNI L es = true →
      exprListNoSpecCalls prog es = true →
      exprListSuppressSafe prog L env pc es = true →
      listRespectsDB w es →
      match evalSeq step w es with
      | .ok vs w' => valListClosureSafe prog L w vs ∧ WorldDBSame w w'
      | .aborted out => outcomeDBAndClosureSafe prog L w out
  | [], w, _, _, _, _, _ => ⟨trivial, WorldDBSame.refl w⟩
  | e :: rest, w, hw0, hs, hns, hsup, hr => by
    simp only [exprListSafeForNI, Bool.and_eq_true] at hs
    simp only [exprListNoSpecCalls, Bool.and_eq_true] at hns
    simp only [exprListSuppressSafe, Bool.and_eq_true] at hsup
    rcases hr with ⟨hr1, hr2⟩
    have h1 := hstep w e hw0 hs.1 hns.1 hsup.1 hr1
    simp only [evalSeq]
    cases hout : step w e with
    | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
      dsimp only; rw [hout] at h1; exact h1
    | ok v w1 =>
      dsimp only; rw [hout] at h1
      rcases h1 with ⟨hv, hw1⟩
      have ih := evalSeq_db_and_closureSafe step hstep (hw0.trans hw1) hs.2 hns.2 hsup.2 (listRespectsDB_congr hw1 hr2)
      cases hrest : evalSeq step w1 rest with
      | aborted out =>
        dsimp only; rw [hrest] at ih
        exact outcomeDBAndClosureSafe_trans hw1 ih
      | ok vs w2 =>
        dsimp only; rw [hrest] at ih
        exact ⟨⟨hv, valListClosureSafe_congr ⟨hw1.1.symm, hw1.2.symm⟩ ih.1⟩, hw1.trans ih.2⟩

private theorem valListClosureSafe_getElem? {prog : Program} {L : TagSet} {w : World} :
    ∀ {vs : List Val} {idx : Nat} {v : Val},
      valListClosureSafe prog L w vs → vs[idx]? = some v → valClosureSafe prog L w v
  | [], _, _, _, hg => by simp at hg
  | _ :: _, 0, _, ⟨hv, _⟩, hg => by simp at hg; subst hg; exact hv
  | _ :: _, n + 1, _, ⟨_, htl⟩, hg => valListClosureSafe_getElem? htl hg

private theorem evalDeriveItems_aux {prog : Program} {tEnv : TyEnv}
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult) (w1 : World) :
    ∀ (curTV : TableVal) (items : List DeriveItem),
      (∀ v w', evalDeriveItems prog tEnv evalRE w1 curTV items = .ok v w' → ∃ tv, v = .table tv) ∧
      (∀ lbl vs w', evalDeriveItems prog tEnv evalRE w1 curTV items ≠ .jumped lbl vs w')
  | curTV, [] => ⟨(fun _ _ h => by injection h with hv _; exact ⟨curTV, hv.symm⟩), (fun _ _ _ h => nomatch h)⟩
  | curTV, item :: rest => by
    unfold evalDeriveItems
    cases applyDeriveItem prog tEnv curTV.cols item with
    | error _ => exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    | ok nextCols =>
      dsimp only
      cases evalDeriveMapRows evalRE curTV.cols item (lookupColIdx? curTV.cols (deriveItemTargetName item)) curTV.rows with
      | ok _ => exact evalDeriveItems_aux evalRE w1 _ rest
      | stopped _ | outOfFuel | wrong => exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem evalFilterRows_aux
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (inCols outCols : List ColSpec) (pred : RowExpr) (w1 : World) :
    ∀ (rows : List TableRow),
      (∀ v w', evalFilterRows evalRE inCols outCols pred w1 rows = .ok v w' → ∃ tv, v = .table tv) ∧
      (∀ lbl vs w', evalFilterRows evalRE inCols outCols pred w1 rows ≠ .jumped lbl vs w')
  | [] => ⟨(fun _ _ h => by injection h with hv _; exact ⟨_, hv.symm⟩), (fun _ _ _ h => nomatch h)⟩
  | r :: rs => by
    unfold evalFilterRows
    split
    · rcases evalFilterRows_aux evalRE inCols outCols pred w1 rs with ⟨hok, hnj⟩
      cases hrest : evalFilterRows evalRE inCols outCols pred w1 rs with
      | stopped _ _ | failed _ _ | wrong | outOfFuel =>
        exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
      | jumped l vs w' => exact absurd hrest (hnj l vs w')
      | ok rv w' =>
        rcases hok rv w' hrest with ⟨_, rfl⟩
        exact ⟨(fun _ _ h => by injection h with hv _; exact ⟨_, hv.symm⟩), (fun _ _ _ h => nomatch h)⟩
    · exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    · exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    · exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    · exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem evalSummarizeGroups_aux
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (tv : TableVal) (groupKeys : List Ident) (distinctKey : Option Ident)
    (dkIdx? : Option (Nat × ColSpec)) (aggs : List AggItem) (aggCols outCols : List ColSpec)
    (w1 : World) :
    ∀ (gks : List (List Val)),
      (∀ v w', evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks = .ok v w' → ∃ resTV, v = .table resTV) ∧
      (∀ lbl vs w', evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks ≠ .jumped lbl vs w')
  | [] => ⟨(fun _ _ h => by injection h with hv _; exact ⟨_, hv.symm⟩), (fun _ _ _ h => nomatch h)⟩
  | _ :: gks => by
    unfold evalSummarizeGroups; dsimp only
    cases evalGroupAggItems evalRE tv.cols _ (List.zip aggs aggCols) with
    | stopped _ | outOfFuel | wrong => exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    | ok _ =>
      dsimp only
      rcases evalSummarizeGroups_aux evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks with ⟨hok, hnj⟩
      cases hrest : evalSummarizeGroups evalRE tv groupKeys distinctKey dkIdx? aggs aggCols outCols w1 gks with
      | stopped _ _ | failed _ _ | wrong | outOfFuel =>
        exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
      | jumped l vs w' => exact absurd hrest (hnj l vs w')
      | ok rv w' =>
        rcases hok rv w' hrest with ⟨_, rfl⟩
        exact ⟨(fun _ _ h => by injection h with hv _; exact ⟨_, hv.symm⟩), (fun _ _ _ h => nomatch h)⟩

private theorem relHelper_db_and_closureSafe {prog : Program} {L : TagSet} {w1 : World} {out : Outcome}
    (hwEq : outcomeWorldEq w1 out)
    (hnj : ∀ lbl vs w', out ≠ .jumped lbl vs w')
    (htbl : ∀ v w', out = .ok v w' → valClosureSafe prog L w1 v) :
    outcomeDBAndClosureSafe prog L w1 out := by
  cases hout : out with
  | ok v w' =>
    have hc := htbl v w' hout
    rw [hout] at hwEq; dsimp only [outcomeWorldEq] at hwEq; subst hwEq
    exact ⟨hc, WorldDBSame.refl _⟩
  | stopped _ w' | failed _ w' =>
    rw [hout] at hwEq; dsimp only [outcomeWorldEq] at hwEq; subst hwEq
    exact WorldDBSame.refl _
  | jumped l vs w' => exact absurd hout (hnj l vs w')
  | wrong | outOfFuel => trivial

set_option maxHeartbeats 400000 in
theorem eval_preserves_db_all (prog : Program) (L : TagSet) :
    ∀ (fuel : Nat),
      (checkProgram prog = .ok () →
        progSafeForNI prog L = true →
        ∀ env pc w e,
          progRespectsDB w prog →
          envClosureSafe prog L w env →
          exprSafeForNI L e = true →
          exprNoSpecCalls prog e = true →
          exprSuppressSafe prog L (envToTyEnv env) pc e = true →
          exprRespectsDB w e →
          outcomeDBAndClosureSafe prog L w (eval fuel prog env pc w e)) ∧
      (checkProgram prog = .ok () →
        progSafeForNI prog L = true →
        ∀ baseEnv curEnv label params joinPc rhs w,
          progRespectsDB w prog →
          envClosureSafe prog L w baseEnv →
          envClosureSafe prog L w curEnv →
          envToTyEnv curEnv = extendTyEnv (envToTyEnv baseEnv) params →
          exprSafeForNI L rhs = true →
          exprNoSpecCalls prog rhs = true →
          exprSuppressSafe prog L (extendTyEnv (envToTyEnv baseEnv) params) joinPc rhs = true →
          exprRespectsDB w rhs →
          outcomeDBAndClosureSafe prog L w (evalJoinLoop fuel prog baseEnv label params joinPc rhs curEnv w)) ∧
      (checkProgram prog = .ok () →
        progSafeForNI prog L = true →
        ∀ env pc w plan,
          progRespectsDB w prog →
          envClosureSafe prog L w env →
          planSafeForNI L plan = true →
          planNoSpecCalls prog plan = true →
          planSuppressSafe prog L (envToTyEnv env) pc plan = true →
          planRespectsDB w plan →
          outcomeDBAndClosureSafe prog L w (evalPlan fuel prog env pc w plan))
  | 0 => ⟨by intros; unfold eval; trivial,
          by intros; unfold evalJoinLoop; trivial,
          by intros; unfold evalPlan; trivial⟩
  | fuel' + 1 => by
    rcases eval_preserves_db_all prog L fuel' with ⟨ihE, ihJL, ihP⟩
    refine ⟨?_, ?_, ?_⟩
    -- 1. Expr
    · intro hprog hsafeProg env pc w e hprogDB henv hes hns hsup her
      have hstep : ∀ w' e', WorldDBSame w w' → exprSafeForNI L e' = true → exprNoSpecCalls prog e' = true →
          exprSuppressSafe prog L (envToTyEnv env) pc e' = true → exprRespectsDB w' e' →
          outcomeDBAndClosureSafe prog L w' (eval fuel' prog env pc w' e') :=
        fun w' e' hww' hs' hns' hsup' hr' =>
          ihE hprog hsafeProg env pc w' e' (progRespectsDB_congr hww' hprogDB) (envClosureSafe_congr hww' henv) hs' hns' hsup' hr'
      unfold eval
      cases e with
      | lit v => exact ⟨evalLiteral_closureSafe prog L w v, WorldDBSame.refl w⟩
      | var name =>
        dsimp only
        cases hl : lookupEnv env name with
        | none => trivial
        | some pair => exact ⟨lookupEnv_closureSafe henv hl, WorldDBSame.refl w⟩
      | constRef name =>
        dsimp only
        cases prog.findConst? name with
        | none => trivial
        | some cDecl => exact ⟨evalLiteral_closureSafe prog L w cDecl.value, WorldDBSame.refl w⟩
      | letE name declLTy bound body =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
        simp only [exprSuppressSafe, Bool.and_eq_true] at hsup
        rcases her with ⟨her1, her2⟩
        have hb := ihE hprog hsafeProg env pc w bound hprogDB henv hes.1.2 hns.1 hsup.1 her1
        cases houtB : eval fuel' prog env pc w bound with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtB] at hb; exact hb
        | ok bVal w1 =>
          dsimp only; rw [houtB] at hb
          rcases hb with ⟨hbVal, hw1⟩
          have henv' : envClosureSafe prog L w1 ({ name := name, lty := declLTy.addTags pc, val := bVal } :: env) :=
            ⟨valClosureSafe_congr hw1 hbVal, envClosureSafe_congr hw1 henv⟩
          exact outcomeDBAndClosureSafe_trans hw1
            (ihE hprog hsafeProg _ pc w1 body (progRespectsDB_congr hw1 hprogDB) henv' hes.2 hns.2 hsup.2 (exprRespectsDB_congr hw1 her2))
      | ifE cond tBr eBr =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
        unfold exprSuppressSafe at hsup
        cases hchkC : checkExpr prog (envToTyEnv env) [] pc false cond with
        | error _ => rw [hchkC] at hsup; nomatch hsup
        | ok cLTy =>
          rw [hchkC] at hsup; simp only [Bool.and_eq_true] at hsup
          rw [checkExpr_inSpec_true hchkC]; dsimp only
          rcases her with ⟨herC, herT, herE⟩
          have hc := ihE hprog hsafeProg env pc w cond hprogDB henv hes.1.1 hns.1.1 hsup.1.1 herC
          cases houtC : eval fuel' prog env pc w cond with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtC] at hc; exact hc
          | ok cv w1 =>
            rw [houtC] at hc; rcases hc with ⟨_, hw1⟩
            cases cv with
            | bool b =>
              cases b
              · exact outcomeDBAndClosureSafe_trans hw1
                  (ihE hprog hsafeProg env _ w1 eBr (progRespectsDB_congr hw1 hprogDB) (envClosureSafe_congr hw1 henv) hes.2 hns.2 hsup.2 (exprRespectsDB_congr hw1 herE))
              · exact outcomeDBAndClosureSafe_trans hw1
                  (ihE hprog hsafeProg env _ w1 tBr (progRespectsDB_congr hw1 hprogDB) (envClosureSafe_congr hw1 henv) hes.1.2 hns.1.2 hsup.1.2 (exprRespectsDB_congr hw1 herT))
            | _ => trivial
      | caseE scrut arms =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
        unfold exprSuppressSafe at hsup
        cases hchkS : checkExpr prog (envToTyEnv env) [] pc false scrut with
        | error _ => rw [hchkS] at hsup; nomatch hsup
        | ok scrutLTy =>
          rw [hchkS] at hsup; dsimp only at hsup
          cases hsp : expectedCaseSpecs prog scrutLTy.ty scrutLTy.effectiveTags with
          | error _ => rw [hsp] at hsup; nomatch hsup
          | ok specs =>
            rw [hsp] at hsup; simp only [Bool.and_eq_true] at hsup
            rw [checkExpr_inSpec_true hchkS]; dsimp only
            rcases her with ⟨herS, herA⟩
            have hs := ihE hprog hsafeProg env pc w scrut hprogDB henv hes.1 hns.1 hsup.1 herS
            cases houtS : eval fuel' prog env pc w scrut with
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              dsimp only; rw [houtS] at hs; exact hs
            | ok sVal w1 =>
              dsimp only; rw [houtS] at hs; rcases hs with ⟨hsVal, hw1⟩
              cases hm : matchCaseVal prog sVal scrutLTy (pc.union scrutLTy.effectiveTags) with
              | none => trivial
              | some pair =>
                rcases pair with ⟨cName, typedVals⟩; dsimp only
                cases hfind : arms.find? (fun (.mk ac _ _) => ac == cName) with
                | none => trivial
                | some arm =>
                  rcases arm with ⟨ac, binders, armBody⟩; dsimp only
                  split
                  · trivial
                  · rename_i hlenOk
                    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                    have hcEq : cName = ac := by
                      have hs := List.find?_some hfind; dsimp only at hs; exact (beq_iff_eq.mp hs).symm
                    subst hcEq
                    rcases matchCaseVal_fst_eq_expectedCaseSpecs hm hsp with ⟨fieldLTys, hspecFind, htvFst⟩
                    have hmem := List.mem_of_find?_eq_some hfind
                    have harmProps : exprSafeForNI L armBody = true ∧ exprNoSpecCalls prog armBody = true ∧
                        exprSuppressSafe prog L (extendTyEnv (envToTyEnv env) (List.zip binders (fieldLTys.map (fun f => f.addTags (pc.union scrutLTy.effectiveTags))))) (pc.union scrutLTy.effectiveTags) armBody = true ∧
                        exprRespectsDB w armBody := by
                      have haux : ∀ (as1 : List CaseArm), CaseArm.mk cName binders armBody ∈ as1 →
                          caseArmsSafeForNI L as1 = true → caseArmsNoSpecCalls prog as1 = true →
                          caseArmsSuppressSafe prog L (envToTyEnv env) (pc.union scrutLTy.effectiveTags) specs as1 = true →
                          armsRespectsDB w as1 →
                          exprSafeForNI L armBody = true ∧ exprNoSpecCalls prog armBody = true ∧
                          exprSuppressSafe prog L (extendTyEnv (envToTyEnv env) (List.zip binders (fieldLTys.map (fun f => f.addTags (pc.union scrutLTy.effectiveTags))))) (pc.union scrutLTy.effectiveTags) armBody = true ∧
                          exprRespectsDB w armBody := by
                        intro as1 hm0 hc0 hn0 hsu0 hr0
                        induction as1 with
                        | nil => nomatch hm0
                        | cons hd tl iha =>
                          cases hd
                          simp only [caseArmsSafeForNI, Bool.and_eq_true] at hc0
                          simp only [caseArmsNoSpecCalls, Bool.and_eq_true] at hn0
                          unfold caseArmsSuppressSafe at hsu0
                          split at hsu0 <;> try contradiction
                          simp only [Bool.and_eq_true] at hsu0
                          rcases List.mem_cons.mp hm0 with heq | htl
                          · injection heq with ec eb1 eb2; subst ec; subst eb1; subst eb2
                            rename_i hsp'
                            rw [hspecFind] at hsp'; injection hsp' with hp'; injection hp' with _ hf'; subst hf'
                            exact ⟨hc0.1, hn0.1, hsu0.1, hr0.1⟩
                          · exact iha htl hc0.2 hn0.2 hsu0.2 hr0.2
                      exact haux arms hmem hes.2 hns.2 hsup.2 herA
                    have htvSafe := matchCaseVal_closureSafe (valClosureSafe_congr hw1 hsVal) hm
                    have harmEnv : envClosureSafe prog L w1
                        ((List.zip binders typedVals).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ env) := by
                      have hzip : ∀ (bs : List Ident) (tvs : List (LTy × Val)),
                          (∀ p ∈ tvs, valClosureSafe prog L w1 p.2) →
                          envClosureSafe prog L w1 ((List.zip bs tvs).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) := by
                        intro bs tvs hp
                        induction bs generalizing tvs with
                        | nil => trivial
                        | cons _ bsTl ihb =>
                          cases tvs with
                          | nil => trivial
                          | cons tv tvsTl => exact ⟨hp tv (.head _), ihb tvsTl (fun q hq => hp q (.tail _ hq))⟩
                      exact envClosureSafe_append (hzip binders typedVals htvSafe) (envClosureSafe_congr hw1 henv)
                    have harmTyEq : envToTyEnv ((List.zip binders typedVals).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ env) =
                        extendTyEnv (envToTyEnv env) (List.zip binders (fieldLTys.map (fun f => f.addTags (pc.union scrutLTy.effectiveTags)))) := by
                      rw [envToTyEnv_append, extendTyEnv]; congr 1
                      rw [← htvFst]
                      have hzipMap : ∀ (bs : List Ident) (tvs : List (LTy × Val)),
                          envToTyEnv ((List.zip bs tvs).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) =
                          List.zip bs (tvs.map Prod.fst) := by
                        intro bs; induction bs with
                        | nil => intro _; rfl
                        | cons b bs ih =>
                          intro tvs; cases tvs with
                          | nil => rfl
                          | cons tv tvs =>
                            rcases tv with ⟨tl, tv'⟩
                            simp only [List.map_cons, List.zip_cons_cons, envToTyEnv]
                            exact congrArg _ (ih tvs)
                      exact hzipMap binders typedVals
                    exact outcomeDBAndClosureSafe_trans hw1
                      (ihE hprog hsafeProg _ _ w1 armBody (progRespectsDB_congr hw1 hprogDB) harmEnv
                        harmProps.1 harmProps.2.1 (harmTyEq ▸ harmProps.2.2.1) (exprRespectsDB_congr hw1 harmProps.2.2.2))
      | lam _ _ _ body =>
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        exact ⟨⟨hes.2, hns, hsup, her, henv⟩, WorldDBSame.refl w⟩
      | app fnExpr args =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
        simp only [exprSuppressSafe, Bool.and_eq_true] at hsup
        rcases her with ⟨herF, herA⟩
        have hf := ihE hprog hsafeProg env pc w fnExpr hprogDB henv hes.1 hns.1 hsup.1 herF
        cases houtF : eval fuel' prog env pc w fnExpr with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtF] at hf; exact hf
        | ok fv w1 =>
          rw [houtF] at hf; rcases hf with ⟨hfVal, hw1⟩
          cases fv <;> try trivial
          case closure params fnPc _ body capEnv =>
            dsimp only
            rcases valClosureSafe_congr hw1 hfVal with ⟨hbodySafe, hbodyNs, hbodySup, hbodyDB, hcapEnv⟩
            have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep hw1 hes.2 hns.2 hsup.2 (listRespectsDB_congr hw1 herA)
            cases hseqOut : evalSeq (eval fuel' prog env pc) w1 args with
            | aborted out =>
              rw [hseqOut] at hseq; dsimp only
              exact outcomeDBAndClosureSafe_trans hw1 hseq
            | ok argVals w2 =>
              rw [hseqOut] at hseq; dsimp only
              rcases hseq with ⟨hargsSafe, hw12⟩
              split
              · trivial
              · rename_i hlenOk
                simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                have hw02 := hw1.trans hw12
                have hcallEnv : envClosureSafe prog L w2
                    ((List.zip params argVals).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv) :=
                  envClosureSafe_append
                    (envClosureSafe_zip_params (valListClosureSafe_congr hw12 hargsSafe))
                    (envClosureSafe_congr hw12 hcapEnv)
                have hcallTy : envToTyEnv ((List.zip params argVals).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv) =
                    extendTyEnv (envToTyEnv capEnv) params := by
                  rw [envToTyEnv_append, envToTyEnv_zip_params params argVals hlenOk, extendTyEnv]
                have hb := ihE hprog hsafeProg _ fnPc w2 body (progRespectsDB_congr hw02 hprogDB) hcallEnv
                  hbodySafe hbodyNs (hcallTy ▸ hbodySup) (exprRespectsDB_congr hw12 hbodyDB)
                cases houtB : eval fuel' prog _ fnPc w2 body with
                | jumped _ _ _ => dsimp only; trivial
                | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel =>
                  dsimp only; rw [houtB] at hb; exact outcomeDBAndClosureSafe_trans hw02 hb
      | call fnName args =>
        dsimp only
        cases hf : prog.findFun? fnName with
        | none =>
          simp only [exprNoSpecCalls, hf, Bool.true_and] at hns
          have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes hns hsup her
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => rw [hseqOut] at hseq; exact hseq
          | ok argVals w1 => dsimp only; trivial
        | some fDecl =>
          simp only [exprNoSpecCalls, hf, Bool.and_eq_true, Bool.not_eq_true'] at hns
          have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes hns.2 hsup her
          cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
          | aborted out => rw [hseqOut] at hseq; exact hseq
          | ok argVals w1 =>
            rw [hseqOut] at hseq; dsimp only
            rcases hseq with ⟨hargsSafe, hw1⟩
            split
            · trivial
            · rename_i hlenOk
              simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
              have hsp := hsafeProg
              simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hsp
              have hfd := hsp.2 fDecl (List.mem_of_find?_eq_some hf)
              simp only [hns.1, Bool.false_or, Bool.and_eq_true] at hfd
              rcases checkFunDecl_valid hprog hf with ⟨_, hbodyChk, _⟩
              rw [hns.1] at hbodyChk
              have hfNs := checkExpr_noSpecCalls hbodyChk
              have hfDB : exprRespectsDB w1 fDecl.body :=
                exprRespectsDB_congr hw1 (hprogDB fDecl (List.mem_of_find?_eq_some hf) hns.1)
              have hcallEnv : envClosureSafe prog L w1
                  ((List.zip fDecl.params argVals).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) := by
                rw [List.map_reverse]
                exact envClosureSafe_reverse (envClosureSafe_zip_params (valListClosureSafe_congr hw1 hargsSafe))
              have hcallTy : envToTyEnv ((List.zip fDecl.params argVals).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) =
                  fDecl.params.reverse := by
                rw [List.map_reverse, envToTyEnv_reverse, envToTyEnv_zip_params fDecl.params argVals hlenOk]
              have hb := ihE hprog hsafeProg _ fDecl.pc w1 fDecl.body (progRespectsDB_congr hw1 hprogDB) hcallEnv
                hfd.1.2 hfNs (hcallTy ▸ hfd.2) hfDB
              cases houtB : eval fuel' prog _ fDecl.pc w1 fDecl.body with
              | jumped _ _ _ => dsimp only; trivial
              | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel =>
                dsimp only; rw [houtB] at hb; exact outcomeDBAndClosureSafe_trans hw1 hb
      | join label params rhs body =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        simp only [exprNoSpecCalls, Bool.and_eq_true] at hns
        simp only [exprSuppressSafe, Bool.and_eq_true] at hsup
        rcases her with ⟨herR, herB⟩
        have hb := ihE hprog hsafeProg env pc w body hprogDB henv hes.2 hns.2 hsup.2 herB
        cases houtB : eval fuel' prog env pc w body with
        | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtB] at hb; exact hb
        | jumped lbl jVals w1 =>
          dsimp only; rw [houtB] at hb; rcases hb with ⟨hjSafe, hw1⟩
          cases (lbl == label)
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hjSafe, hw1⟩
          · simp only [↓reduceIte]; split
            · trivial
            · rename_i hlenOk
              simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
              have hcurEnv : envClosureSafe prog L w1
                  ((List.zip params jVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env) :=
                envClosureSafe_append
                  (envClosureSafe_zip_params (valListClosureSafe_congr hw1 hjSafe))
                  (envClosureSafe_congr hw1 henv)
              have hcurTy : envToTyEnv ((List.zip params jVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env) =
                  extendTyEnv (envToTyEnv env) params := by
                rw [envToTyEnv_append, envToTyEnv_zip_params params jVals hlenOk, extendTyEnv]
              exact outcomeDBAndClosureSafe_trans hw1
                (ihJL hprog hsafeProg env _ label params _ rhs w1 (progRespectsDB_congr hw1 hprogDB)
                  (envClosureSafe_congr hw1 henv) hcurEnv hcurTy hes.1.2 hns.1 hsup.1 (exprRespectsDB_congr hw1 herR))
      | jump _ args =>
        dsimp only
        have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes hns hsup her
        cases hseqOut : evalSeq (eval fuel' prog env pc) w args <;> (rw [hseqOut] at hseq; exact hseq)
      | tuple elems =>
        dsimp only
        have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes hns hsup her
        cases hseqOut : evalSeq (eval fuel' prog env pc) w elems <;> (rw [hseqOut] at hseq; exact hseq)
      | proj tup idx =>
        dsimp only
        have ht := ihE hprog hsafeProg env pc w tup hprogDB henv hes hns hsup her
        cases houtT : eval fuel' prog env pc w tup with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtT] at ht; exact ht
        | ok tv w1 =>
          rw [houtT] at ht; rcases ht with ⟨htVal, hw1⟩
          cases tv <;> try trivial
          case tuple vs =>
            dsimp only
            cases hget : vs[idx]? with
            | none => trivial
            | some v => exact ⟨valListClosureSafe_getElem? htVal hget, hw1⟩
      | ctor _ _ args =>
        dsimp only
        have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes hns hsup her
        cases hseqOut : evalSeq (eval fuel' prog env pc) w args <;> (rw [hseqOut] at hseq; exact hseq)
      | tableLit _ _ => exact ⟨trivial, WorldDBSame.refl w⟩
      | prim op args =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes.2 hns hsup her
        cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
        | aborted out => rw [hseqOut] at hseq; exact hseq
        | ok vs w1 =>
          rw [hseqOut] at hseq; dsimp only
          rcases hseq with ⟨hvs, hw1⟩
          cases hp : evalPrimOp op vs with
          | ok v => exact ⟨evalPrimOp_closureSafe hvs hp, hw1⟩
          | stopped _ => exact hw1
          | outOfFuel | wrong => trivial
      | rel plan => exact ihP hprog hsafeProg env pc w plan hprogDB henv hes hns hsup her
      | host op args =>
        dsimp only
        simp only [exprSafeForNI, Bool.and_eq_true] at hes
        have hseq := evalSeq_db_and_closureSafe (eval fuel' prog env pc) hstep (WorldDBSame.refl w) hes.2 hns hsup her
        cases hseqOut : evalSeq (eval fuel' prog env pc) w args with
        | aborted out => rw [hseqOut] at hseq; exact hseq
        | ok vs w1 =>
          rw [hseqOut] at hseq; dsimp only
          rcases hseq with ⟨hvs, hw1⟩
          exact outcomeDBAndClosureSafe_trans hw1
            (evalHostOp_db_and_closureSafe hes.1 (valListClosureSafe_congr hw1 hvs))
      | stop _ detail =>
        dsimp only
        cases detail with
        | none => exact WorldDBSame.refl w
        | some dExpr =>
          dsimp only
          cases checkExpr prog (envToTyEnv env) [] pc true dExpr with
          | error _ => trivial
          | ok _ =>
            dsimp only
            have hd := ihE hprog hsafeProg env pc w dExpr hprogDB henv hes hns hsup her
            cases houtD : eval fuel' prog env pc w dExpr with
            | ok _ w1 => rw [houtD] at hd; exact hd.2
            | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
              dsimp only; rw [houtD] at hd; exact hd
      | fail msgExpr =>
        dsimp only
        have hm := ihE hprog hsafeProg env pc w msgExpr hprogDB henv hes hns hsup her
        cases houtM : eval fuel' prog env pc w msgExpr with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtM] at hm; exact hm
        | ok mv w1 =>
          rw [houtM] at hm; cases mv <;> first | trivial | exact hm.2
    -- 2. JoinLoop
    · intro hprog hsafeProg baseEnv curEnv label params joinPc rhs w hprogDB hbase hcur hcurTy hes hns hsup her
      unfold evalJoinLoop
      have hr := ihE hprog hsafeProg curEnv joinPc w rhs hprogDB hcur hes hns (hcurTy ▸ hsup) her
      cases houtR : eval fuel' prog curEnv joinPc w rhs with
      | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel =>
        dsimp only; rw [houtR] at hr; exact hr
      | jumped lbl jVals w1 =>
        dsimp only; rw [houtR] at hr; rcases hr with ⟨hjSafe, hw1⟩
        cases (lbl == label)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hjSafe, hw1⟩
        · simp only [↓reduceIte]; split
          · trivial
          · rename_i hlenOk
            simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
            have hnextEnv : envClosureSafe prog L w1
                ((List.zip params jVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ baseEnv) :=
              envClosureSafe_append
                (envClosureSafe_zip_params (valListClosureSafe_congr hw1 hjSafe))
                (envClosureSafe_congr hw1 hbase)
            have hnextTy : envToTyEnv ((List.zip params jVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ baseEnv) =
                extendTyEnv (envToTyEnv baseEnv) params := by
              rw [envToTyEnv_append, envToTyEnv_zip_params params jVals hlenOk, extendTyEnv]
            exact outcomeDBAndClosureSafe_trans hw1
              (ihJL hprog hsafeProg baseEnv _ label params joinPc rhs w1 (progRespectsDB_congr hw1 hprogDB)
                (envClosureSafe_congr hw1 hbase) hnextEnv hnextTy hes hns hsup (exprRespectsDB_congr hw1 her))
    -- 3. Plan
    · intro hprog hsafeProg env pc w plan hprogDB henv hps hpns hpsup hpr
      unfold evalPlan
      cases plan with
      | sourceExpr e =>
        dsimp only
        have he := ihE hprog hsafeProg env pc w e hprogDB henv hps hpns hpsup hpr
        cases houtE : eval fuel' prog env pc w e with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtE] at he; exact he
        | ok ev w1 =>
          rw [houtE] at he; cases ev <;> first | trivial | exact ⟨trivial, he.2⟩
      | sourceDB cap tableName schema =>
        dsimp only
        have hc := ihE hprog hsafeProg env pc w cap hprogDB henv hps hpns hpsup hpr.1
        cases houtC : eval fuel' prog env pc w cap with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtC] at hc; exact hc
        | ok cv w1 =>
          rw [houtC] at hc; rcases hc with ⟨_, hw1⟩
          cases cv with
          | capReadDB h db =>
            simp only []
            cases h with
            | real =>
              simp only []
              cases w1.realDBTables.find? (fun st => st.db == db && st.tableName == tableName) with
              | none => exact ⟨trivial, hw1⟩
              | some st => simp only []; split <;> first | exact ⟨trivial, hw1⟩ | exact hw1
            | fake fid =>
              simp only []
              cases w1.fakeDBs[fid]? with
              | none => exact ⟨trivial, hw1⟩
              | some fdb =>
                simp only []
                cases fdb.tables.find? (fun st => st.tableName == tableName) with
                | none => exact ⟨trivial, hw1⟩
                | some st => simp only []; split <;> first | exact ⟨trivial, hw1⟩ | exact hw1
          | _ => trivial
      | select inp _ | drop inp _ | rename inp _ | distinct inp _ | sort inp _
      | limit inp _ | groupBy inp _ | crosstab inp _ _ _ _ | redact inp _ _ =>
        dsimp only
        have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps hpns hpsup hpr
        cases houtI : evalPlan fuel' prog env pc w inp with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtI] at hi; exact hi
        | ok iv w1 =>
          rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
          cases iv <;> try trivial
          repeat ((try simp only []); first | exact ⟨trivial, hw1⟩ | exact hw1 | trivial | split)
      | suppressSmallGroups inp _ _ _ =>
        dsimp only
        simp only [planSuppressSafe, Bool.and_eq_true] at hpsup
        have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps hpns hpsup.1 hpr
        cases houtI : evalPlan fuel' prog env pc w inp with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtI] at hi; exact hi
        | ok iv w1 =>
          rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
          cases iv <;> try trivial
          repeat ((try simp only []); first | exact ⟨trivial, hw1⟩ | exact hw1 | trivial | split)
      | window inp _ | fillGaps inp _ _ _ _ | pivotWider inp _ _ _ _ =>
        dsimp only
        cases checkPlan prog (envToTyEnv env) pc true _ with
        | error _ => trivial
        | ok pTy =>
          cases pTy <;> try trivial
          dsimp only
          have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps hpns hpsup hpr
          cases houtI : evalPlan fuel' prog env pc w inp with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtI] at hi; exact hi
          | ok iv w1 =>
            rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
            cases iv <;> try trivial
            repeat ((try simp only []); first | exact ⟨trivial, hw1⟩ | exact hw1 | trivial | split)
      | derive inp items =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hps
        have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps.1 hpns hpsup hpr
        cases houtI : evalPlan fuel' prog env pc w inp with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtI] at hi; exact hi
        | ok iv w1 =>
          rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
          cases iv <;> try trivial
          case table tv =>
            dsimp only
            apply outcomeDBAndClosureSafe_trans hw1
            rcases evalDeriveItems_aux (prog := prog) (tEnv := envToTyEnv env) (evalRowExpr fuel' prog env) w1 _ items with ⟨hok, hnj⟩
            apply relHelper_db_and_closureSafe (evalDeriveItems_world_and_safe (L := L) (evalRowExpr fuel' prog env) w1 _ items).2.2 hnj
            intro v w' hok0
            rcases hok v w' hok0 with ⟨_, rfl⟩
            trivial
      | filter inp pred =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hps
        have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps.1 hpns hpsup hpr
        cases houtI : evalPlan fuel' prog env pc w inp with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtI] at hi; exact hi
        | ok iv w1 =>
          rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
          cases iv with
          | table tv =>
            dsimp only
            apply outcomeDBAndClosureSafe_trans hw1
            rcases evalFilterRows_aux (evalRowExpr fuel' prog env) tv.cols (tv.cols.map (fun c => { c with aggKind := .raw })) pred w1 tv.rows with ⟨hok, hnj⟩
            apply relHelper_db_and_closureSafe (evalFilterRows_world_and_safe (prog := prog) (L := L) (evalRowExpr fuel' prog env) tv.cols (tv.cols.map (fun c => { c with aggKind := .raw })) pred w1 tv.rows).2.2 hnj
            intro v w' hok0
            rcases hok v w' hok0 with ⟨_, rfl⟩
            trivial
          | _ => trivial
      | summarize inp aggs dk =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hps
        cases checkPlan prog (envToTyEnv env) pc true (.summarize inp aggs dk) with
        | error _ => trivial
        | ok pTy =>
          cases pTy <;> try trivial
          dsimp only
          have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps.1 hpns hpsup hpr
          cases houtI : evalPlan fuel' prog env pc w inp with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtI] at hi; exact hi
          | ok iv w1 =>
            rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
            cases iv <;> try trivial
            dsimp only
            split
            · trivial
            · cases extractAllRowsKeyVals _ _ _ with
              | none => trivial
              | some _ =>
                dsimp only
                apply outcomeDBAndClosureSafe_trans hw1
                rcases evalSummarizeGroups_aux (evalRowExpr fuel' prog env) _ _ dk _ aggs _ _ w1 _ with ⟨hok, hnj⟩
                apply relHelper_db_and_closureSafe (evalSummarizeGroups_world_and_safe (prog := prog) (L := L) (evalRowExpr fuel' prog env) _ _ dk _ aggs _ _ w1 _).2.2 hnj
                intro v w' hok0
                rcases hok v w' hok0 with ⟨_, rfl⟩
                trivial
      | join _ lP rP _ _ | union lP rP =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hps
        simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
        simp only [planSuppressSafe, Bool.and_eq_true] at hpsup
        rcases hpr with ⟨hprL, hprR⟩
        have hl := ihP hprog hsafeProg env pc w lP hprogDB henv hps.1 hpns.1 hpsup.1 hprL
        cases houtL : evalPlan fuel' prog env pc w lP with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtL] at hl; exact hl
        | ok lv w1 =>
          rw [houtL] at hl; rcases hl with ⟨_, hw1⟩
          cases lv <;> try trivial
          dsimp only
          have hr := ihP hprog hsafeProg env pc w1 rP (progRespectsDB_congr hw1 hprogDB)
            (envClosureSafe_congr hw1 henv) hps.2 hpns.2 hpsup.2 (planRespectsDB_congr hw1 hprR)
          cases houtR : evalPlan fuel' prog env pc w1 rP with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtR] at hr; exact outcomeDBAndClosureSafe_trans hw1 hr
          | ok rv w2 =>
            rw [houtR] at hr; rcases hr with ⟨_, hw12⟩
            have hw02 := hw1.trans hw12
            cases rv <;> try trivial
            repeat ((try simp only []); first | exact ⟨trivial, hw02⟩ | exact hw02 | trivial | split)
      | pseudonymize inp col sec =>
        dsimp only
        simp only [planSafeForNI, Bool.and_eq_true] at hps
        simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
        simp only [planSuppressSafe, Bool.and_eq_true] at hpsup
        rcases hpr with ⟨hprI, hprS⟩
        have hi := ihP hprog hsafeProg env pc w inp hprogDB henv hps.1.2 hpns.1 hpsup.1 hprI
        cases houtI : evalPlan fuel' prog env pc w inp with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
          dsimp only; rw [houtI] at hi; exact hi
        | ok iv w1 =>
          rw [houtI] at hi; rcases hi with ⟨_, hw1⟩
          cases iv <;> try trivial
          dsimp only
          have hs := ihE hprog hsafeProg env pc w1 sec (progRespectsDB_congr hw1 hprogDB)
            (envClosureSafe_congr hw1 henv) hps.2 hpns.2 hpsup.2 (exprRespectsDB_congr hw1 hprS)
          cases houtS : eval fuel' prog env pc w1 sec with
          | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel =>
            dsimp only; rw [houtS] at hs; exact outcomeDBAndClosureSafe_trans hw1 hs
          | ok sv w2 =>
            rw [houtS] at hs; rcases hs with ⟨_, hw12⟩
            have hw02 := hw1.trans hw12
            cases sv <;> try trivial
            repeat ((try simp only []); first | exact ⟨trivial, hw02⟩ | exact hw02 | trivial | split)


/-! ## Part 4B.2: High-`pc` Jump Signatures & `JoinOutcomeEquiv` -/

def outWorld : Outcome → World
  | .ok _ w | .stopped _ w | .failed _ w | .jumped _ _ w => w
  | .wrong | .outOfFuel => {}

private theorem evalSeq_not_jumped {prog : Program} {env : Env} {pc : TagSet} {inSpec : Bool}
    (step : World → Expr → Outcome)
    (hstep : ∀ w e lty, WorldWf prog w →
      checkExpr prog (envToTyEnv env) [] pc inSpec e = .ok lty →
      OutcomeWf prog [] lty.ty (step w e)) :
    ∀ {es : List Expr} {ltys : List LTy} {w : World},
      WorldWf prog w →
      checkExprList prog (envToTyEnv env) pc inSpec es = .ok ltys →
      ∀ lbl vs w', evalSeq step w es ≠ .aborted (.jumped lbl vs w')
  | [], _, _, _, _, _, _, _, h => nomatch h
  | e :: rest, _, w, hw, hchk, lbl, vs, w', h => by
    unfold checkExprList at hchk; simp only [bind, Except.bind] at hchk
    cases hh : checkExpr prog (envToTyEnv env) [] pc inSpec e <;> rw [hh] at hchk <;> try contradiction
    dsimp only at hchk
    cases ht : checkExprList prog (envToTyEnv env) pc inSpec rest <;> rw [ht] at hchk <;> try contradiction
    rename_i hdLTy _
    have hwf1 := hstep w e hdLTy hw hh
    simp only [evalSeq] at h
    cases hout1 : step w e with
    | jumped _ _ _ =>
      rw [hout1] at hwf1; cases hwf1 with | jumped hlook _ _ => simp [lookupJoinEnv] at hlook
    | stopped _ _ | failed _ _ | wrong | outOfFuel =>
      rw [hout1] at h; nomatch h
    | ok _ w1 =>
      rw [hout1] at h hwf1; dsimp only at h
      cases hwf1 with | ok _ hw1 =>
      cases hrest : evalSeq step w1 rest with
      | ok _ _ => rw [hrest] at h; nomatch h
      | aborted out =>
        rw [hrest] at h; injection h with houtEq; subst houtEq
        exact evalSeq_not_jumped step hstep hw1 ht lbl vs w' hrest

theorem eval_high_pc_jump_sig_all (prog : Program) (L : TagSet) :
    ∀ (fuel : Nat),
      (checkProgram prog = .ok () →
        ∀ env jenv pc inSpec w e lty lbl jVals w',
          EnvWf prog env →
          WorldWf prog w →
          checkExpr prog (envToTyEnv env) jenv pc inSpec e = .ok lty →
          pc.subset L = false →
          eval fuel prog env pc w e = .jumped lbl jVals w' →
          ∃ sig, lookupJoinEnv jenv lbl = some sig ∧ sig.joinPc.subset L = false) ∧
      (checkProgram prog = .ok () →
        ∀ baseEnv curEnv jenv label params joinPc retLTy rLTy inSpec rhs w lbl jVals w',
          EnvWf prog baseEnv →
          EnvWf prog curEnv →
          envToTyEnv curEnv = extendTyEnv (envToTyEnv baseEnv) params →
          WorldWf prog w →
          checkExpr prog (extendTyEnv (envToTyEnv baseEnv) params)
            ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
            joinPc inSpec rhs = .ok rLTy →
          joinPc.subset L = false →
          evalJoinLoop fuel prog baseEnv label params joinPc rhs curEnv w = .jumped lbl jVals w' →
          ∃ sig, lookupJoinEnv jenv lbl = some sig ∧ sig.joinPc.subset L = false)
  | 0 => ⟨by intros; unfold eval at *; contradiction,
          by intros; unfold evalJoinLoop at *; contradiction⟩
  | fuel' + 1 => by
    rcases eval_high_pc_jump_sig_all prog L fuel' with ⟨ihE, ihJL⟩
    have hsound := eval_fuel_sound prog fuel'
    refine ⟨?_, ?_⟩
    · intro hprog env jenv pc inSpec w e lty lbl jVals w' henv hw hchk hpcF hev
      have hwfFull := (eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env jenv pc inSpec w e lty henv hw hchk
      have hevOrig := hev
      unfold eval at hev
      cases e with
      | lit _ | tableLit _ _ | lam _ _ _ _ => nomatch hev
      | var name =>
        dsimp only at hev
        cases hl : lookupEnv env name with
        | none => rw [hl] at hev; nomatch hev
        | some p => rw [hl] at hev; nomatch hev
      | constRef name =>
        dsimp only at hev
        cases hc : prog.findConst? name with
        | none => rw [hc] at hev; nomatch hev
        | some _ => rw [hc] at hev; nomatch hev
      | letE name declLTy bound body =>
        dsimp only at hev
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hb : checkExpr prog (envToTyEnv env) [] pc inSpec bound <;> rw [hb] at hchk <;> try contradiction
        dsimp only at hchk
        split at hchk <;> try contradiction
        rename_i bLTy hsub
        simp only [Bool.not_eq_true', Bool.not_eq_false, ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hsub
        have hbWf := hsound.2.2.1 hprog env [] pc inSpec w bound bLTy henv hw hb
        cases houtB : eval fuel' prog env pc w bound with
        | jumped _ _ _ => rw [houtB] at hbWf; exact absurd rfl hbWf.not_jumped_nil
        | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [houtB] at hev; nomatch hev
        | ok bVal w1 =>
          rw [houtB] at hev hbWf; dsimp only at hev
          cases hbWf with | ok hbValWf hw1 =>
          have hentryWf : EnvWf prog ({ name := name, lty := declLTy.addTags pc, val := bVal } :: env) :=
            .cons (by simpa [hsub.1] using hbValWf) henv
          exact ihE hprog _ jenv pc inSpec w1 body lty lbl jVals w' hentryWf hw1 hchk hpcF hev
      | ifE cond tBr eBr =>
        dsimp only at hev
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hc : checkExpr prog (envToTyEnv env) [] pc inSpec cond <;> rw [hc] at hchk <;> try contradiction
        dsimp only at hchk
        split at hchk <;> try contradiction
        rename_i cLTy hcBool
        simp only [decide_eq_true_eq] at hcBool
        cases ht : checkExpr prog (envToTyEnv env) jenv (pc.union cLTy.tags) inSpec tBr <;> rw [ht] at hchk <;> try contradiction
        dsimp only at hchk
        cases he : checkExpr prog (envToTyEnv env) jenv (pc.union cLTy.tags) inSpec eBr <;> rw [he] at hchk <;> try contradiction
        rw [checkExpr_inSpec_true hc] at hev; dsimp only at hev
        have hcWf := hsound.2.2.1 hprog env [] pc inSpec w cond cLTy henv hw hc
        cases houtC : eval fuel' prog env pc w cond with
        | jumped _ _ _ => rw [houtC] at hcWf; exact absurd rfl hcWf.not_jumped_nil
        | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [houtC] at hev; nomatch hev
        | ok cv w1 =>
          rw [houtC] at hev hcWf; cases hcWf with | ok hcValWf hw1 =>
          rw [hcBool] at hcValWf; cases hcValWf with | bool b =>
          cases b
          · exact ihE hprog env jenv _ inSpec w1 eBr _ lbl jVals w' henv hw1 he (not_subset_union_left hpcF) hev
          · exact ihE hprog env jenv _ inSpec w1 tBr _ lbl jVals w' henv hw1 ht (not_subset_union_left hpcF) hev
      | caseE scrut arms =>
        dsimp only at hev
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases hsc : checkExpr prog (envToTyEnv env) [] pc inSpec scrut <;> rw [hsc] at hchk <;> try contradiction
        dsimp only at hchk
        rename_i scrutLTy
        cases hsp : expectedCaseSpecs prog scrutLTy.ty scrutLTy.effectiveTags <;> rw [hsp] at hchk <;> try contradiction
        dsimp only at hchk
        split at hchk <;> try contradiction
        cases ha : checkCaseArms prog (envToTyEnv env) jenv (pc.union scrutLTy.effectiveTags) inSpec _ arms <;> rw [ha] at hchk <;> try contradiction
        rw [checkExpr_inSpec_true hsc] at hev; dsimp only at hev
        have hscWf := hsound.2.2.1 hprog env [] pc inSpec w scrut scrutLTy henv hw hsc
        cases houtS : eval fuel' prog env pc w scrut with
        | jumped _ _ _ => rw [houtS] at hscWf; exact absurd rfl hscWf.not_jumped_nil
        | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [houtS] at hev; nomatch hev
        | ok sVal w1 =>
          rw [houtS] at hev hscWf; dsimp only at hev; cases hscWf with | ok hsValWf hw1 =>
          cases hm : matchCaseVal prog sVal scrutLTy (pc.union scrutLTy.effectiveTags) with
          | none => rw [hm] at hev; nomatch hev
          | some pair =>
            rcases pair with ⟨cName, typedVals⟩; rw [hm] at hev; dsimp only at hev
            revert hev
            cases hfindArm : arms.find? (fun (.mk ac _ _) => ac == cName) with
            | none => intro hev; nomatch hev
            | some arm =>
              rcases arm with ⟨ac, binders, armBody⟩
              intro hev; dsimp only at hev
              split at hev
              · nomatch hev
              · have hbeq := List.find?_some hfindArm
                dsimp only at hbeq
                have hcEq : cName = ac := (beq_iff_eq.mp hbeq).symm
                subst hcEq
                rcases matchCaseVal_sound hsValWf hsp (armPc := pc.union scrutLTy.effectiveTags) with
                  ⟨cName2, fieldLTys, typedVals2, hm2, hspecFind, htvLTys, htvWf⟩
                rw [hm] at hm2; injection hm2 with hpEq; injection hpEq with hc2 htv2; subst hc2; subst htv2
                rcases (checkCaseArms_props ha).2 cName binders armBody fieldLTys hfindArm hspecFind with
                  ⟨hbindLen, armLTy, _, harmBodyChk⟩
                rcases envWf_armEntries binders
                  (fieldLTys.map (fun f => f.addTags (pc.union scrutLTy.effectiveTags)))
                  (typedVals.map Prod.snd) typedVals env
                  (by simp [hbindLen]) htvLTys rfl htvWf henv with ⟨harmEnvWf, harmTyEq⟩
                rw [extendTyEnv, ← harmTyEq] at harmBodyChk
                exact ihE hprog _ jenv _ inSpec w1 armBody armLTy lbl jVals w' harmEnvWf hw1
                  harmBodyChk (not_subset_union_left hpcF) hev
      | join label params rhs body =>
        dsimp only at hev
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        dsimp only at hchk
        let guess1 := pc.union (inferJumpPc prog label (envToTyEnv env) pc body)
        let rhsEnv := extendTyEnv (envToTyEnv env) params
        let joinPc := guess1.union (inferJumpPc prog label rhsEnv guess1 rhs)
        have hjoinPcF : joinPc.subset L = false := not_subset_union_left (not_subset_union_left hpcF)
        cases hinf : inferJoinRetLTy prog rhsEnv jenv joinPc label rhs body with
        | none => rw [hinf] at hchk; contradiction
        | some candRetLTy =>
          rw [hinf] at hchk; dsimp only [bind, Except.bind] at hchk
          split at hchk <;> try contradiction
          have hjoinCheck : ∃ effRet rLTy bLTy,
              checkExpr prog rhsEnv ((label, { params := params, joinPc := joinPc, retLTy := effRet }) :: jenv) joinPc inSpec rhs = .ok rLTy ∧
              checkExpr prog (envToTyEnv env) ((label, { params := params, joinPc := joinPc, retLTy := effRet }) :: jenv) pc inSpec body = .ok bLTy := by
            cases hr1 : checkExpr prog rhsEnv _ joinPc inSpec rhs <;> rw [hr1] at hchk <;> try contradiction
            dsimp only at hchk
            cases hb1 : checkExpr prog (envToTyEnv env) _ pc inSpec body <;> rw [hb1] at hchk <;> try contradiction
            dsimp only at hchk
            split at hchk <;> try contradiction
            split at hchk
            · exact ⟨_, _, _, hr1, hb1⟩
            · cases hr2 : checkExpr prog rhsEnv _ joinPc inSpec rhs <;> rw [hr2] at hchk <;> try contradiction
              dsimp only at hchk
              cases hb2 : checkExpr prog (envToTyEnv env) _ pc inSpec body <;> rw [hb2] at hchk <;> try contradiction
              exact ⟨_, _, _, hr2, hb2⟩
          rcases hjoinCheck with ⟨effRet, rLTy, bLTy, hrChk, hbChk⟩
          have hbWf := hsound.2.2.1 hprog env _ pc inSpec w body bLTy henv hw hbChk
          cases houtB : eval fuel' prog env pc w body with
          | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [houtB] at hev; nomatch hev
          | jumped bLbl bVals w1 =>
            rw [houtB] at hev hbWf; dsimp only at hev
            cases hbWf with | @jumped _ _ _ bSig hlookB hbValsWf hw1 =>
            cases hlbl : (bLbl == label)
            · simp only [hlbl, Bool.false_eq_true, ↓reduceIte, Outcome.jumped.injEq] at hev
              rcases hev with ⟨rfl, rfl, rfl⟩
              rcases ihE hprog env _ pc inSpec w body bLTy bLbl bVals w1 henv hw hbChk hpcF houtB with ⟨sig, hlookS, hsigF⟩
              have hne : bLbl ≠ label := fun heq => by subst heq; simp at hlbl
              simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlookS
              exact ⟨sig, hlookS, hsigF⟩
            · simp only [hlbl, ↓reduceIte] at hev
              have heq : label = bLbl := (beq_iff_eq.mp hlbl).symm
              simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlookB
              subst hlookB
              split at hev
              · nomatch hev
              · rename_i hlenOk
                simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
                have hcurWf := extendEnv_wf hbValsWf henv
                have hcurTy : envToTyEnv ((List.zip params bVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env) =
                    extendTyEnv (envToTyEnv env) params := by
                  rw [envToTyEnv_append, envToTyEnv_zip_params params bVals hlenOk, extendTyEnv]
                exact ihJL hprog env _ jenv label params joinPc effRet rLTy inSpec rhs w1 lbl jVals w'
                  henv hcurWf hcurTy hw1 hrChk hjoinPcF hev
      | jump jumpLbl args =>
        dsimp only at hev
        unfold checkExpr at hchk
        split at hchk <;> try contradiction
        simp only [bind, Except.bind] at hchk
        cases ha : checkExprList prog (envToTyEnv env) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
        dsimp only at hchk
        cases hl : lookupJoinEnv jenv jumpLbl with
        | none => rw [hl] at hchk; contradiction
        | some sig =>
          rw [hl] at hchk; dsimp only at hchk
          cases hpcJ : pc.subset sig.joinPc
          · simp [hpcJ] at hchk
          · have hnotSeq := evalSeq_not_jumped (eval fuel' prog env pc)
              (fun w0 e0 l0 hw0 hc0 => hsound.2.2.1 hprog env [] pc inSpec w0 e0 l0 henv hw0 hc0) hw ha
            cases hseq : evalSeq (eval fuel' prog env pc) w args with
            | aborted out =>
              rw [hseq] at hev
              exact absurd (hev ▸ hseq) (hnotSeq lbl jVals w')
            | ok _ _ =>
              rw [hseq] at hev; injection hev with hlbl _ _; subst hlbl
              refine ⟨sig, hl, ?_⟩
              cases hsL : sig.joinPc.subset L
              · rfl
              · have := TagSet.subset_trans hpcJ hsL; rw [hpcF] at this; nomatch this
      | app fnExpr args =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.app fnExpr args) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | call fnName args =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.call fnName args) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | tuple elems =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.tuple elems) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | ctor tn cn elems =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.ctor tn cn elems) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | prim op elems =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.prim op elems) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | host op elems =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.host op elems) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | proj tup idx =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.proj tup idx) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | rel plan =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.rel plan) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | stop kind detail =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.stop kind detail) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
      | fail msg =>
        have hchkNil : checkExpr prog (envToTyEnv env) [] pc inSpec (.fail msg) = .ok lty := by
          unfold checkExpr at hchk ⊢; exact hchk
        exact absurd hevOrig
          ((eval_fuel_sound prog (fuel' + 1)).2.2.1 hprog env [] pc inSpec w _ lty henv hw hchkNil).not_jumped_nil
    -- 2. JoinLoop
    · intro hprog baseEnv curEnv jenv label params joinPc retLTy rLTy inSpec rhs w lbl jVals w'
        hbase hcur hcurTy hw hrChk hjpF hev
      unfold evalJoinLoop at hev
      have hrChkCur : checkExpr prog (envToTyEnv curEnv)
          ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
          joinPc inSpec rhs = .ok rLTy := hcurTy ▸ hrChk
      have hrWf := hsound.2.2.1 hprog curEnv _ joinPc inSpec w rhs rLTy hcur hw hrChkCur
      cases houtR : eval fuel' prog curEnv joinPc w rhs with
      | ok _ _ | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [houtR] at hev; nomatch hev
      | jumped rLbl rVals w1 =>
        rw [houtR] at hev hrWf; dsimp only at hev
        cases hrWf with | @jumped _ _ _ rSig hlookR hrValsWf hw1 =>
        cases hlbl : (rLbl == label)
        · simp only [hlbl, Bool.false_eq_true, ↓reduceIte, Outcome.jumped.injEq] at hev
          rcases hev with ⟨rfl, rfl, rfl⟩
          rcases ihE hprog curEnv _ joinPc inSpec w rhs rLTy rLbl rVals w1 hcur hw hrChkCur hjpF houtR with ⟨sig, hlookS, hsigF⟩
          have hne : rLbl ≠ label := fun heq => by subst heq; simp at hlbl
          simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlookS
          exact ⟨sig, hlookS, hsigF⟩
        · simp only [hlbl, ↓reduceIte] at hev
          have heq : label = rLbl := (beq_iff_eq.mp hlbl).symm
          simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlookR
          subst hlookR
          split at hev
          · nomatch hev
          · rename_i hlenOk
            simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlenOk
            have hnextWf := extendEnv_wf hrValsWf hbase
            have hnextTy : envToTyEnv ((List.zip params rVals).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ baseEnv) =
                extendTyEnv (envToTyEnv baseEnv) params := by
              rw [envToTyEnv_append, envToTyEnv_zip_params params rVals hlenOk, extendTyEnv]
            exact ihJL hprog baseEnv _ jenv label params joinPc retLTy rLTy inSpec rhs w1 lbl jVals w'
              hbase hnextWf hnextTy hw1 hrChk hjpF hev

/-- Relational `L`-equivalence on normal (`.ok`) and tail-jump (`.jumped`) outcomes,
    supporting lockstep low jumps as well as asymmetric high-`pc` branch/loop exits. -/
def JoinOutcomeEquiv (prog : Program) (L : TagSet) (jenv : JoinEnv) (lty : LTy)
    (out1 out2 : Outcome) : Prop :=
  WorldEquiv prog L (outWorld out1) (outWorld out2) ∧
  match out1, out2 with
  | .ok v1 _, .ok v2 _ => ValEquiv prog L v1 v2 lty
  | .jumped lbl1 vs1 _, .jumped lbl2 vs2 _ =>
    (lbl1 = lbl2 ∧ ∃ sig, lookupJoinEnv jenv lbl1 = some sig ∧
      sig.joinPc.subset L = true ∧ ValListEquiv prog L vs1 vs2 (sig.params.map Prod.snd)) ∨
    ((∃ sig1, lookupJoinEnv jenv lbl1 = some sig1 ∧ sig1.joinPc.subset L = false) ∧
     (∃ sig2, lookupJoinEnv jenv lbl2 = some sig2 ∧ sig2.joinPc.subset L = false))
  | .ok _ _, .jumped lbl2 _ _ =>
    lty.tags.subset L = false ∧
    ∃ sig2, lookupJoinEnv jenv lbl2 = some sig2 ∧ sig2.joinPc.subset L = false
  | .jumped lbl1 _ _, .ok _ _ =>
    (∃ sig1, lookupJoinEnv jenv lbl1 = some sig1 ∧ sig1.joinPc.subset L = false) ∧
    lty.tags.subset L = false
  | _, _ => False

theorem JoinOutcomeEquiv.subtype {prog : Program} {L : TagSet} {jenv : JoinEnv}
    {sub sup : LTy} {out1 out2 : Outcome}
    (hsub : ltySubtype sub sup = true)
    (h : JoinOutcomeEquiv prog L jenv sub out1 out2) :
    JoinOutcomeEquiv prog L jenv sup out1 out2 := by
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have htagsSub : sub.tags.subset sup.tags = true := by
    simp only [ltySubtype, Bool.and_eq_true] at hsub; exact hsub.2
  have hhighImp : sub.tags.subset L = false → sup.tags.subset L = false := by
    intro hf
    cases hs : sup.tags.subset L
    · rfl
    · have := TagSet.subset_trans htagsSub hs; rw [hf] at this; nomatch this
  cases out1 <;> cases out2 <;> try exact h2
  · exact h2.subtype hsub
  · exact ⟨hhighImp h2.1, h2.2⟩
  · exact ⟨h2.1, hhighImp h2.2⟩


/-! ## Part 4B.3: Standalone Relational Operator Non-Interference Combinators -/

theorem ValWf.table_change_tags {prog : Program} {tv : TableVal} {tt : TableTy} (rt ot : TagSet)
    (h : ValWf prog (.table tv) (.table tt)) :
    ValWf prog (.table tv) (.table { tt with rowTags := rt, orderTags := ot }) := by
  cases h with | table hc hs hr =>
  exact .table hc (by unfold TableSchemaWf at hs ⊢; exact hs) hr

theorem groupingLow_of_groupedBy_none {prog : Program} {L : TagSet} {tt : TableTy}
    (hgb : tt.groupedBy = none)
    (hsch : TableSchemaWf prog tt = true) :
    tt.rowTags.subset L = true → ∀ c ∈ tt.cols, c.aggKind = .groupKey → c.tags.subset L = true := by
  intro _ c hc hk
  unfold TableSchemaWf at hsch
  simp only [hgb, Option.getD_none, Bool.and_eq_true, List.all_eq_true] at hsch
  have hcProp := (hsch.1.2 c hc).2
  simp [hk] at hcProp

theorem TableEquiv.to_valEquiv_planTy {prog : Program} {L pc : TagSet}
    {tv1 tv2 : TableVal} {tt : TableTy}
    (ht : TableEquiv prog L tv1 tv2 tt) :
    ValEquiv prog L (.table tv1) (.table tv2) (PlanTy.toLTy pc (.table tt)) := by
  have hw := ht.widenRowOrderTags pc pc
  exact ValEquiv.mk_smart hw.wf1 hw.wf2 rfl rfl (fun _ => .table hw)

theorem RelList.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    (f : α → γ) (g : β → δ) (hfg : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → RelList S (xs.map f) (ys.map g)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hd tl => .cons (hfg _ _ hd) (tl.map f g hfg)

theorem RelList.take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, RelList R xs ys → RelList R (xs.take n) (ys.take n)
  | 0, _, _, _ => .nil
  | _ + 1, [], [], .nil => .nil
  | n + 1, _ :: _, _ :: _, .cons hd tl => .cons hd (tl.take n)

theorem RelList.filter_congr {α β : Type} {R : α → β → Prop}
    {p1 : α → Bool} {p2 : β → Bool}
    (hp : ∀ a b, R a b → p1 a = p2 b) :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → RelList R (xs.filter p1) (ys.filter p2)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons hd tl => by
    simp only [List.filter_cons, hp a b hd]
    cases p2 b
    · exact tl.filter_congr hp
    · exact .cons hd (tl.filter_congr hp)

theorem RelList.zipIdx_go {α β : Type} {R : α → β → Prop} :
    ∀ (k : Nat) {xs : List α} {ys : List β},
      RelList R xs ys →
      RelList (fun p1 p2 => R p1.1 p2.1 ∧ p1.2 = p2.2) (xs.zipIdx k) (ys.zipIdx k)
  | _, [], [], .nil => .nil
  | k, _ :: _, _ :: _, .cons hd tl => .cons ⟨hd, rfl⟩ (tl.zipIdx_go (k + 1))

theorem relList_perm_right {α β : Type} {R : α → β → Prop} :
    ∀ {ys ys' : List β} {xs : List α},
      RelList R xs ys → List.Perm ys ys' →
      ∃ xs', List.Perm xs xs' ∧ RelList R xs' ys'
  | _, _, _, hrel, .nil => by cases hrel; exact ⟨[], .nil, .nil⟩
  | _, _, _, .cons hr htl, .cons _ hp => by
    rcases relList_perm_right htl hp with ⟨xs', hp', hr'⟩
    exact ⟨_, .cons _ hp', .cons hr hr'⟩
  | _, _, _, .cons h1 (.cons h2 htl), .swap _ _ _ =>
    ⟨_, .swap _ _ _, .cons h2 (.cons h1 htl)⟩
  | _, _, _, hrel, .trans hp1 hp2 => by
    rcases relList_perm_right hrel hp1 with ⟨xm, hpm1, hrm⟩
    rcases relList_perm_right hrm hp2 with ⟨xs', hpm2, hrs⟩
    exact ⟨xs', hpm1.trans hpm2, hrs⟩

theorem perm_filter {α : Type} (p : α → Bool) :
    ∀ {xs ys : List α}, List.Perm xs ys → List.Perm (xs.filter p) (ys.filter p)
  | _, _, .nil => .nil
  | x :: _, _ :: _, .cons _ hp => by
    simp only [List.filter_cons]
    cases p x
    · exact perm_filter p hp
    · exact .cons x (perm_filter p hp)
  | _, _, .swap x y rest => by
    simp only [List.filter_cons]
    cases p x <;> cases p y <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact .refl _
    · exact .refl _
    · exact .refl _
    · exact .swap x y (rest.filter p)
  | _, _, .trans h1 h2 => (perm_filter p h1).trans (perm_filter p h2)

theorem perm_filterMap {α β : Type} (f : α → Option β) :
    ∀ {xs ys : List α}, List.Perm xs ys → List.Perm (xs.filterMap f) (ys.filterMap f)
  | _, _, .nil => .nil
  | x :: _, _ :: _, .cons _ hp => by
    simp only [List.filterMap_cons]
    cases f x
    · exact perm_filterMap f hp
    · exact .cons _ (perm_filterMap f hp)
  | _, _, .swap x y rest => by
    simp only [List.filterMap_cons]
    cases f x <;> cases f y
    · exact .refl _
    · exact .refl _
    · exact .refl _
    · exact .swap _ _ (rest.filterMap f)
  | _, _, .trans h1 h2 => (perm_filterMap f h1).trans (perm_filterMap f h2)

theorem extractKeyVals_congr_of_low {L : TagSet} {cols : List ColSpec} {r1 r2 : TableRow}
    (hrow : RowEquiv L cols r1 r2) :
    ∀ {keyNames : List Ident},
      (∀ k ∈ keyNames, ∀ c, cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true) →
      extractKeyVals cols keyNames r1 = extractKeyVals cols keyNames r2
  | [], _ => rfl
  | k :: ks, hlow => by
    unfold extractKeyVals
    unfold extractKeyVals.go
    cases hlk : lookupColIdx? cols k with
    | none => rfl
    | some pair =>
      rcases pair with ⟨idx, cSpec⟩
      have hfind : cols.find? (fun x => x.name == k) = some cSpec := by
        rw [← lookupColIdx?_snd_eq_find?, hlk]; rfl
      have hcLow := hlow k (.head _) cSpec hfind
      rcases lookupColIdx?_props hlk with ⟨hcolIdx, _⟩
      have hcellEq := hrow.getElem?_eq hcolIdx hcLow
      have htlEq : extractKeyVals cols ks r1 = extractKeyVals cols ks r2 :=
        extractKeyVals_congr_of_low hrow (fun m hm => hlow m (.tail _ hm))
      unfold extractKeyVals at htlEq
      simp only [bind, Option.bind, hcellEq, htlEq]

theorem extractKeyVals_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {cols : List ColSpec} {r : TableRow}
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true)
    (hrWf : CellsWf prog r.cells cols) :
    ∀ {keyNames : List Ident} {kv : List Val},
      extractKeyVals cols keyNames r = some kv →
      SortableValList kv
  | [], _, h => by unfold extractKeyVals extractKeyVals.go at h; injection h with h'; subst h'; exact .nil
  | k :: ks, _, h => by
    unfold extractKeyVals at h; unfold extractKeyVals.go at h
    simp only [bind, Option.bind] at h
    cases hlk : lookupColIdx? cols k with
    | none => rw [hlk] at h; contradiction
    | some pair =>
      rcases pair with ⟨idx, cSpec⟩; rw [hlk] at h; dsimp only at h
      rcases lookupColIdx?_props hlk with ⟨hcolIdx, _⟩
      rcases hrWf.getElem?_wf hcolIdx with ⟨cell, hget, hcellWf⟩
      rw [hget] at h; dsimp only at h
      cases htl : extractKeyVals.go cols r ks with
      | none => rw [htl] at h; contradiction
      | some tl =>
        rw [htl] at h; injection h with h'; subst h'
        have hs := valWf_sortable hd hcellWf (ScalarTy.isSortable_toTy cSpec.ty)
        exact .cons hs (extractKeyVals_sortable hd hcols hrWf htl)

theorem rowLtByKeys_congr_of_low {L : TagSet} {cols : List ColSpec}
    {a1 a2 b1 b2 : TableRow}
    (h1 : RowEquiv L cols a1 b1)
    (h2 : RowEquiv L cols a2 b2) :
    ∀ {keys : List (Ident × SortDir)},
      (∀ p ∈ keys, ∀ c, cols.find? (fun x => x.name == p.1) = some c → c.tags.subset L = true) →
      rowLtByKeys cols keys a1 a2 = rowLtByKeys cols keys b1 b2
  | [], _ => rfl
  | (k, dir) :: rest, hlow => by
    unfold rowLtByKeys
    unfold rowLtByKeys.go
    cases hlk : lookupColIdx? cols k with
    | none => rfl
    | some pair =>
      rcases pair with ⟨idx, cSpec⟩
      have hfind : cols.find? (fun x => x.name == k) = some cSpec := by
        rw [← lookupColIdx?_snd_eq_find?, hlk]; rfl
      have hcLow := hlow (k, dir) (.head _) cSpec hfind
      rcases lookupColIdx?_props hlk with ⟨hcolIdx, _⟩
      have hc1 := h1.getElem?_eq hcolIdx hcLow
      have hc2 := h2.getElem?_eq hcolIdx hcLow
      have htl := rowLtByKeys_congr_of_low h1 h2 (fun p hp => hlow p (.tail _ hp))
      unfold rowLtByKeys at htl
      simp only [hc1, hc2, htl]

theorem rowLtByKeys_asc_eq_valListLt {cols : List ColSpec} {r1 r2 : TableRow} :
    ∀ {keyNames : List Ident} {kv1 kv2 : List Val},
      extractKeyVals cols keyNames r1 = some kv1 →
      extractKeyVals cols keyNames r2 = some kv2 →
      SortableValList kv1 →
      SortableValList kv2 →
      rowLtByKeys cols (keyNames.map (fun k => (k, SortDir.asc))) r1 r2 = valListLt kv1 kv2
  | [], _, _, h1, h2, _, _ => by
    unfold extractKeyVals extractKeyVals.go at h1 h2
    injection h1 with e1; injection h2 with e2; subst e1; subst e2
    rfl
  | k :: ks, _, _, h1, h2, hs1, hs2 => by
    unfold extractKeyVals at h1 h2; unfold extractKeyVals.go at h1 h2
    simp only [bind, Option.bind] at h1 h2
    cases hlk : lookupColIdx? cols k with
    | none => rw [hlk] at h1; contradiction
    | some pair =>
      rcases pair with ⟨idx, _⟩
      rw [hlk] at h1 h2; dsimp only at h1 h2
      cases hc1 : r1.cells[idx]? with
      | none => rw [hc1] at h1; contradiction
      | some v1 =>
        cases hc2 : r2.cells[idx]? with
        | none => rw [hc2] at h2; contradiction
        | some v2 =>
          rw [hc1] at h1; rw [hc2] at h2; dsimp only at h1 h2
          cases htl1 : extractKeyVals.go cols r1 ks with
          | none => rw [htl1] at h1; contradiction
          | some tl1 =>
            cases htl2 : extractKeyVals.go cols r2 ks with
            | none => rw [htl2] at h2; contradiction
            | some tl2 =>
              rw [htl1] at h1; rw [htl2] at h2
              injection h1 with e1; injection h2 with e2; subst e1; subst e2
              cases hs1 with | cons hv1 htlS1 =>
              cases hs2 with | cons hv2 htlS2 =>
              have ih := rowLtByKeys_asc_eq_valListLt (r1 := r1) (r2 := r2) htl1 htl2 htlS1 htlS2
              simp only [List.map_cons]
              unfold rowLtByKeys at ih ⊢
              unfold rowLtByKeys.go
              simp only [hlk, hc1, hc2, ih]
              simp only [valListLt, valListCmp]
              rcases valLt_trichotomy hv1 hv2 with hlt | rfl | hgt
              · have hcLt : valCmp v1 v2 = .lt := by simpa [valLt] using hlt
                simp [hlt, hcLt]
              · simp [valLt_irrefl hv1, (valCmp_eq_iff hv1 hv1).mpr rfl]
              · have hcGt : valCmp v1 v2 = .gt := (valCmp_gt_iff hv1 hv2).mpr (by simpa [valLt] using hgt)
                have hnotLt : valLt v1 v2 = false := by
                  cases hb : valLt v1 v2; rfl
                  have := valLt_trans hv1 hv2 hv1 hb hgt; rw [valLt_irrefl hv1] at this; nomatch this
                simp [hnotLt, hgt, hcGt]

theorem projectRowsByIndices_pick_equiv {L : TagSet} {inCols : List ColSpec} {r1 r2 : TableRow}
    (hr : RowEquiv L inCols r1 r2) :
    ∀ {idxCols : List (Nat × ColSpec)} {cs1 cs2 : List Val},
      (∀ ic ∈ idxCols, inCols[ic.1]? = some ic.2) →
      projectRowsByIndices.pick r1 (idxCols.map Prod.fst) = some cs1 →
      projectRowsByIndices.pick r2 (idxCols.map Prod.fst) = some cs2 →
      CellsEquiv L (idxCols.map (fun (_, c) => { c with aggKind := .raw })) cs1 cs2
  | [], _, _, _, hp1, hp2 => by
    injection hp1 with e1; injection hp2 with e2; subst e1; subst e2; exact .nil
  | (idx, cSpec) :: rest, _, _, hall, hp1, hp2 => by
    simp only [List.map_cons, projectRowsByIndices.pick, bind, Option.bind] at hp1 hp2
    cases hg1 : r1.cells[idx]? <;> rw [hg1] at hp1 <;> try contradiction
    cases hg2 : r2.cells[idx]? <;> rw [hg2] at hp2 <;> try contradiction
    dsimp only at hp1 hp2
    cases htl1 : projectRowsByIndices.pick r1 (rest.map Prod.fst) <;> rw [htl1] at hp1 <;> try contradiction
    cases htl2 : projectRowsByIndices.pick r2 (rest.map Prod.fst) <;> rw [htl2] at hp2 <;> try contradiction
    injection hp1 with e1; injection hp2 with e2; subst e1; subst e2
    refine .cons (fun hlow => ?_) (projectRowsByIndices_pick_equiv hr (fun ic hic => hall ic (.tail _ hic)) htl1 htl2)
    have hce := hr.getElem?_eq (hall (idx, cSpec) (.head _)) hlow
    rw [hg1, hg2] at hce; injection hce

theorem projectRowsByIndices_relList {L : TagSet} {inCols : List ColSpec}
    {idxCols : List (Nat × ColSpec)}
    (hallIdx : ∀ ic ∈ idxCols, inCols[ic.1]? = some ic.2) :
    ∀ {rs1 rs2 out1 out2 : List TableRow},
      RelList (RowEquiv L inCols) rs1 rs2 →
      projectRowsByIndices (idxCols.map Prod.fst) rs1 = some out1 →
      projectRowsByIndices (idxCols.map Prod.fst) rs2 = some out2 →
      RelList (RowEquiv L (idxCols.map (fun (_, c) => { c with aggKind := .raw }))) out1 out2
  | [], [], _, _, .nil, ho1, ho2 => by
    injection ho1 with e1; injection ho2 with e2; subst e1; subst e2; exact .nil
  | r1 :: _, r2 :: _, _, _, .cons hr htl, ho1, ho2 => by
    unfold projectRowsByIndices at ho1 ho2; simp only [bind, Option.bind] at ho1 ho2
    cases hp1 : projectRowsByIndices.pick r1 (idxCols.map Prod.fst) <;> rw [hp1] at ho1 <;> try contradiction
    cases hp2 : projectRowsByIndices.pick r2 (idxCols.map Prod.fst) <;> rw [hp2] at ho2 <;> try contradiction
    dsimp only at ho1 ho2
    cases ht1 : projectRowsByIndices (idxCols.map Prod.fst) _ <;> rw [ht1] at ho1 <;> try contradiction
    cases ht2 : projectRowsByIndices (idxCols.map Prod.fst) _ <;> rw [ht2] at ho2 <;> try contradiction
    injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
    exact .cons (projectRowsByIndices_pick_equiv hr hallIdx hp1 hp2)
      (projectRowsByIndices_relList hallIdx htl ht1 ht2)

theorem projectRowsByIndices_eq_filterMap (idxs : List Nat) :
    ∀ {rs out : List TableRow},
      projectRowsByIndices idxs rs = some out →
      out = rs.filterMap (fun r => (projectRowsByIndices.pick r idxs).map (fun cs => { cells := cs, groupMeta := none }))
  | [], _, h => by injection h with e; exact e.symm
  | r :: rs, _, h => by
    unfold projectRowsByIndices at h; simp only [bind, Option.bind] at h
    cases hp : projectRowsByIndices.pick r idxs <;> rw [hp] at h <;> try contradiction
    dsimp only at h
    cases ht : projectRowsByIndices idxs rs <;> rw [ht] at h <;> try contradiction
    injection h with e; subst e
    simp [hp, ← projectRowsByIndices_eq_filterMap idxs ht]

theorem mapPseudonymizeRows_eq_filterMap (keyMat : String) (cIdx : Nat) :
    ∀ {rs out : List TableRow},
      mapPseudonymizeRows keyMat cIdx rs = some out →
      out = rs.filterMap (fun r => (r.cells[cIdx]?).map (fun origVal =>
        { cells := r.cells.set cIdx (.text (pseudonymizeToken keyMat origVal)), groupMeta := none }))
  | [], _, h => by injection h with e; exact e.symm
  | r :: rs, _, h => by
    unfold mapPseudonymizeRows at h; simp only [bind, Option.bind] at h
    cases hc : r.cells[cIdx]? <;> rw [hc] at h <;> try contradiction
    dsimp only at h
    cases ht : mapPseudonymizeRows keyMat cIdx rs <;> rw [ht] at h <;> try contradiction
    injection h with e; subst e
    simp [hc, ← mapPseudonymizeRows_eq_filterMap keyMat cIdx ht]

theorem cellsEquiv_map_tags {L : TagSet} (f : ColSpec → ColSpec) :
    ∀ {cols : List ColSpec} {cs1 cs2 : List Val},
      CellsEquiv L cols cs1 cs2 →
      (∀ c ∈ cols, (f c).tags.subset L = true → c.tags.subset L = true) →
      CellsEquiv L (cols.map f) cs1 cs2
  | [], [], [], .nil, _ => .nil
  | c :: _, _ :: _, _ :: _, .cons hc htl, hsub =>
    .cons (fun hl => hc (hsub c (.head _) hl))
      (cellsEquiv_map_tags f htl (fun d hd => hsub d (.tail _ hd)))

theorem cellsEquiv_set_at {L : TagSet} (f : ColSpec → ColSpec) :
    ∀ {cols : List ColSpec} {cs1 cs2 : List Val} (idx : Nat) {v1 v2 : Val},
      CellsEquiv L cols cs1 cs2 →
      (∀ (i : Nat) (c : ColSpec), cols[i]? = some c →
        (i = idx → (f c).tags.subset L = true → v1 = v2) ∧
        (i ≠ idx → (f c).tags.subset L = true → c.tags.subset L = true)) →
      CellsEquiv L (cols.map f) (cs1.set idx v1) (cs2.set idx v2)
  | [], [], [], _, _, _, .nil, _ => .nil
  | c :: rest, _ :: _, _ :: _, 0, _, _, .cons _ htl, hprop => by
    refine .cons ((hprop 0 c rfl).1 rfl) ?_
    apply cellsEquiv_map_tags f htl
    intro d hd
    rcases List.mem_iff_getElem.mp hd with ⟨j, hjLt, rfl⟩
    have hjGet : (c :: rest)[j + 1]? = some rest[j] := by simp [List.getElem?_eq_getElem hjLt]
    exact (hprop (j + 1) rest[j] hjGet).2 (by omega)
  | c :: _, _ :: _, _ :: _, n + 1, _, _, .cons hc htl, hprop =>
    .cons (fun hl => hc ((hprop 0 c rfl).2 (by omega) hl))
      (cellsEquiv_set_at f n htl (fun i d hi =>
        ⟨fun heq => (hprop (i + 1) d hi).1 (congrArg (· + 1) heq),
         fun hne => (hprop (i + 1) d hi).2 (by omega)⟩))


/-! ## Part 4B.4: Relational Operator Non-Interference Lemmas -/

theorem CellsEquiv.append {L : TagSet} :
    ∀ {c1 c2 : List ColSpec} {xs1 xs2 ys1 ys2 : List Val},
      CellsEquiv L c1 xs1 xs2 → CellsEquiv L c2 ys1 ys2 →
      CellsEquiv L (c1 ++ c2) (xs1 ++ ys1) (xs2 ++ ys2)
  | [], _, [], [], _, _, .nil, h2 => h2
  | _ :: _, _, _ :: _, _ :: _, _, _, .cons hc htl, h2 =>
    .cons hc (htl.append h2)

theorem CellsEquiv.congr_tags {L : TagSet} :
    ∀ {c1 c2 : List ColSpec} {xs1 xs2 : List Val},
      c1.map ColSpec.tags = c2.map ColSpec.tags →
      CellsEquiv L c1 xs1 xs2 →
      CellsEquiv L c2 xs1 xs2
  | [], [], [], [], _, .nil => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, htags, .cons hc htl => by
    simp only [List.map_cons, List.cons.injEq] at htags
    exact .cons (htags.1 ▸ hc) (htl.congr_tags htags.2)

theorem CellsEquiv.of_all_eq {L : TagSet} :
    ∀ (cols : List ColSpec) (vs : List Val),
      vs.length = cols.length → CellsEquiv L cols vs vs
  | [], [], _ => .nil
  | _ :: cs, _ :: vs, hlen =>
    .cons (fun _ => rfl) (CellsEquiv.of_all_eq cs vs (Nat.succ.inj hlen))

theorem CellsEquiv.of_high_cols {L : TagSet} :
    ∀ {cols : List ColSpec} {xs1 xs2 : List Val},
      xs1.length = cols.length →
      xs2.length = cols.length →
      (∀ c ∈ cols, c.tags.subset L = false) →
      CellsEquiv L cols xs1 xs2
  | [], [], [], _, _, _ => .nil
  | c :: cs, _ :: vs1, _ :: vs2, h1, h2, hhigh =>
    .cons (fun hl => by rw [hhigh c (.head _)] at hl; nomatch hl)
      (CellsEquiv.of_high_cols (Nat.succ.inj h1) (Nat.succ.inj h2) (fun d hd => hhigh d (.tail _ hd)))

theorem RelList.symm {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → RelList (fun b a => R a b) ys xs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hd tl => .cons hd (tl.symm)

theorem RelList.trans {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (himp : ∀ a b c, R a b → S b c → T a c) :
    ∀ {xs : List α} {ys : List β} {zs : List γ},
      RelList R xs ys → RelList S ys zs → RelList T xs zs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 =>
    .cons (himp _ _ _ h1 h2) (t1.trans himp t2)

theorem RelList.with_mem {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : RelList R xs ys) :
    RelList (fun a b => a ∈ xs ∧ b ∈ ys ∧ R a b) xs ys := by
  let rec go {as1 : List α} {bs1 : List β}
      (ha : ∀ a ∈ as1, a ∈ xs) (hb : ∀ b ∈ bs1, b ∈ ys) :
      RelList R as1 bs1 → RelList (fun a b => a ∈ xs ∧ b ∈ ys ∧ R a b) as1 bs1
    | .nil => .nil
    | .cons hd tl =>
      .cons ⟨ha _ (.head _), hb _ (.head _), hd⟩
        (go (fun x hx => ha x (.tail _ hx)) (fun y hy => hb y (.tail _ hy)) tl)
  exact go (fun _ hm => hm) (fun _ hm => hm) h

theorem RelList.filterMap_congr {α β γ : Type} {R : α → β → Prop}
    {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → xs.filterMap f = ys.filterMap g
  | [], [], .nil => rfl
  | a :: _, b :: _, .cons hd tl => by
    simp only [List.filterMap_cons, hfg a b hd, tl.filterMap_congr hfg]

theorem RelList.filterMap_rel {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → Option γ} {g : β → Option δ}
    (hfg : ∀ a b, R a b →
      (f a = none ∧ g b = none) ∨ ∃ c d, f a = some c ∧ g b = some d ∧ S c d) :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → RelList S (xs.filterMap f) (ys.filterMap g)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons hd tl => by
    simp only [List.filterMap_cons]
    rcases hfg a b hd with ⟨hn1, hn2⟩ | ⟨c, d, hs1, hs2, hcd⟩
    · rw [hn1, hn2]; exact tl.filterMap_rel hfg
    · rw [hs1, hs2]; exact .cons hcd (tl.filterMap_rel hfg)

theorem RelList.find?_rel {α β : Type} {R : α → β → Prop}
    {p1 : α → Bool} {p2 : β → Bool}
    (hp : ∀ a b, R a b → p1 a = p2 b) :
    ∀ {xs : List α} {ys : List β},
      RelList R xs ys →
      (xs.find? p1 = none ∧ ys.find? p2 = none) ∨
      ∃ a b, xs.find? p1 = some a ∧ ys.find? p2 = some b ∧ R a b
  | [], [], .nil => Or.inl ⟨rfl, rfl⟩
  | a :: _, b :: _, .cons hd tl => by
    simp only [List.find?, hp a b hd]
    cases p2 b
    · exact tl.find?_rel hp
    · exact Or.inr ⟨a, b, rfl, rfl, hd⟩

theorem TableEquiv.map_lowRows {prog : Program} {L : TagSet}
    {tv1 tv2 : TableVal} {tt : TableTy} {outCols : List ColSpec}
    (ht : TableEquiv prog L tv1 tv2 tt)
    (hrLow : tt.rowTags.subset L = true)
    (g1 g2 : TableRow → TableRow)
    (hg : ∀ r1 r2, RowEquiv L tt.cols r1 r2 → RowEquiv L outCols (g1 r1) (g2 r2)) :
    if tt.orderTags.subset L = true then
      RelList (RowEquiv L outCols) (tv1.rows.map g1) (tv2.rows.map g2)
    else
      ∃ rows1', List.Perm (tv1.rows.map g1) rows1' ∧ RelList (RowEquiv L outCols) rows1' (tv2.rows.map g2) := by
  have hlr := ht.lowRows hrLow
  cases hord : tt.orderTags.subset L
  · simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr ⊢
    rcases hlr with ⟨rows1', hp, hrel⟩
    exact ⟨rows1'.map g1, hp.map g1, hrel.map g1 g2 hg⟩
  · simp only [hord, ↓reduceIte] at hlr ⊢
    exact hlr.map g1 g2 hg

theorem projectPlan_lowRows {prog : Program} {L : TagSet}
    {tv1 tv2 : TableVal} {tt : TableTy} {idxCols : List (Nat × ColSpec)}
    {outRows1 outRows2 : List TableRow}
    (ht : TableEquiv prog L tv1 tv2 tt)
    (hrLow : tt.rowTags.subset L = true)
    (hallIdx : ∀ ic ∈ idxCols, tt.cols[ic.1]? = some ic.2)
    (ho1 : projectRowsByIndices (idxCols.map Prod.fst) tv1.rows = some outRows1)
    (ho2 : projectRowsByIndices (idxCols.map Prod.fst) tv2.rows = some outRows2) :
    let outCols := idxCols.map (fun (_, c) => { c with aggKind := .raw })
    if tt.orderTags.subset L = true then
      RelList (RowEquiv L outCols) outRows1 outRows2
    else
      ∃ rows1', List.Perm outRows1 rows1' ∧ RelList (RowEquiv L outCols) rows1' outRows2 := by
  intro outCols
  have hlr := ht.lowRows hrLow
  cases hord : tt.orderTags.subset L
  · simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr ⊢
    rcases hlr with ⟨rows1', hp, hrel⟩
    cases ht.wf1 with | table _ _ hrWf1 =>
    have hwf1' : ∀ r ∈ rows1', CellsWf prog r.cells tt.cols :=
      fun r hr => hrWf1.to_forall r (hp.symm.subset hr)
    rcases projectRowsByIndices_sound idxCols hallIdx rows1' hwf1' with ⟨out1', ho1', _⟩
    have hfm1 := projectRowsByIndices_eq_filterMap (idxCols.map Prod.fst) ho1
    have hfm1' := projectRowsByIndices_eq_filterMap (idxCols.map Prod.fst) ho1'
    rw [hfm1]
    refine ⟨out1', hfm1' ▸ perm_filterMap _ hp, projectRowsByIndices_relList hallIdx hrel ho1' ho2⟩
  · simp only [hord, ↓reduceIte] at hlr ⊢
    exact projectRowsByIndices_relList hallIdx hlr ho1 ho2

/-! ### `SourceDB` Lookup Equivalence -/

theorem relList_storedTable_findReal {prog : Program} {L : TagSet} (db tbl : Ident) :
    ∀ {sts1 sts2 : List StoredTable},
      RelList (StoredTableEquiv prog L) sts1 sts2 →
      ((sts1.find? (fun st => st.db == db && st.tableName == tbl) = none ∧
        sts2.find? (fun st => st.db == db && st.tableName == tbl) = none) ∨
       ∃ st1 st2,
         sts1.find? (fun st => st.db == db && st.tableName == tbl) = some st1 ∧
         sts2.find? (fun st => st.db == db && st.tableName == tbl) = some st2 ∧
         StoredTableEquiv prog L st1 st2) :=
  RelList.find?_rel (fun _ _ h => by rw [h.dbEq, h.nameEq])

theorem relList_storedTable_findFake {prog : Program} {L : TagSet} (tbl : Ident) :
    ∀ {sts1 sts2 : List StoredTable},
      RelList (StoredTableEquiv prog L) sts1 sts2 →
      ((sts1.find? (fun st => st.tableName == tbl) = none ∧
        sts2.find? (fun st => st.tableName == tbl) = none) ∨
       ∃ st1 st2,
         sts1.find? (fun st => st.tableName == tbl) = some st1 ∧
         sts2.find? (fun st => st.tableName == tbl) = some st2 ∧
         StoredTableEquiv prog L st1 st2) :=
  RelList.find?_rel (fun _ _ h => by rw [h.nameEq])

theorem relList_fakeDB_getElem? {prog : Program} {L : TagSet} :
    ∀ (fid : Nat) {fs1 fs2 : List FakeDBState},
      RelList (FakeDBEquiv prog L) fs1 fs2 →
      (fs1[fid]? = none ∧ fs2[fid]? = none) ∨
      ∃ f1 f2, fs1[fid]? = some f1 ∧ fs2[fid]? = some f2 ∧ FakeDBEquiv prog L f1 f2
  | _, [], [], .nil => Or.inl ⟨rfl, rfl⟩
  | 0, f1 :: _, f2 :: _, .cons hf _ => Or.inr ⟨f1, f2, rfl, rfl, hf⟩
  | n + 1, _ :: _, _ :: _, .cons _ tl => relList_fakeDB_getElem? n tl

/-! ### `Derive` Non-Interference Helpers -/

theorem RelList.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, RelList R xs ys → RelList S xs ys
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons hd tl => .cons (h a b hd) (tl.imp h)

def deriveRowOpt (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (cols : List ColSpec) (item : DeriveItem) (existingIdx? : Option (Nat × ColSpec))
    (r : TableRow) : Option TableRow :=
  match evalDeriveCell evalRE cols r item with
  | .ok newCell =>
    let newCells :=
      match existingIdx? with
      | some (idx, _) => r.cells.set idx newCell
      | none => r.cells ++ [newCell]
    some { cells := newCells, groupMeta := none }
  | _ => none

theorem evalDeriveMapRows_eq_filterMap
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (cols : List ColSpec) (item : DeriveItem) (existingIdx? : Option (Nat × ColSpec)) :
    ∀ {rs : List TableRow} {rowTuples : List Val},
      evalDeriveMapRows evalRE cols item existingIdx? rs = .ok rowTuples →
      rowTuples.filterMap (fun | .tuple cs => some ({ cells := cs, groupMeta := none } : TableRow) | _ => none) =
        rs.filterMap (deriveRowOpt evalRE cols item existingIdx?) ∧
      (∀ r ∈ rs, ∃ nr, deriveRowOpt evalRE cols item existingIdx? r = some nr)
  | [], _, h => by
    injection h with e; subst e; exact ⟨rfl, fun _ hm => nomatch hm⟩
  | r :: rs, _, h => by
    unfold evalDeriveMapRows at h
    cases hc : evalDeriveCell evalRE cols r item with
    | stopped _ | outOfFuel | wrong => rw [hc] at h; nomatch h
    | ok newCell =>
      rw [hc] at h; dsimp only at h
      cases htl : evalDeriveMapRows evalRE cols item existingIdx? rs with
      | stopped _ | outOfFuel | wrong => rw [htl] at h; nomatch h
      | ok restVals =>
        rw [htl] at h; injection h with e; subst e
        rcases evalDeriveMapRows_eq_filterMap evalRE cols item existingIdx? htl with ⟨ihEq, ihAll⟩
        refine ⟨by simp only [List.filterMap_cons, deriveRowOpt, hc, ihEq]; rfl, ?_⟩
        intro x hx; rcases List.mem_cons.mp hx with rfl | hrest
        · exact ⟨_, by dsimp only [deriveRowOpt]; rw [hc]⟩
        · exact ihAll x hrest

private theorem distinctIdents_idx_unique {cols : List ColSpec}
    (huniq : distinctIdents (cols.map ColSpec.name) = true) :
    ∀ {i j : Nat} {ci cj : ColSpec},
      cols[i]? = some ci → cols[j]? = some cj → ci.name = cj.name → i = j := by
  induction cols with
  | nil => intro i _ _ _ hi _ _; simp at hi
  | cons c cs ih =>
    rcases distinctIdents_not_mem huniq with ⟨hcnot, htl⟩
    intro i j ci cj hi hj hname
    cases i <;> cases j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
      simp only [List.getElem?_cons_succ] at hj
      exact absurd (hname ▸ List.mem_map_of_mem (List.mem_of_getElem? hj)) hcnot
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      simp only [List.getElem?_cons_succ] at hi
      exact absurd (hname.symm ▸ List.mem_map_of_mem (List.mem_of_getElem? hi)) hcnot
    · simp only [List.getElem?_cons_succ] at hi hj
      exact congrArg (· + 1) (ih htl hi hj hname)

theorem find_unique_of_mem {cols : List ColSpec} {c : ColSpec}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hmem : c ∈ cols) :
    cols.find? (fun x => x.name == c.name) = some c := by
  induction cols with
  | nil => nomatch hmem
  | cons d ds ih =>
    rcases distinctIdents_not_mem huniq with ⟨hdnot, hdtl⟩
    simp only [List.find?]
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp
    · have hne : (d.name == c.name) = false := by
        cases h : (d.name == c.name)
        · rfl
        · exact absurd ((beq_iff_eq.mp h) ▸ List.mem_map_of_mem htl) hdnot
      simp [hne, ih hdtl htl]

private theorem cellsEquiv_replace_or_append {L : TagSet} {cols : List ColSpec} {newCol : ColSpec}
    {cs1 cs2 : List Val} {v1 v2 : Val}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hce : CellsEquiv L cols cs1 cs2)
    (hv : newCol.tags.subset L = true → v1 = v2) :
    CellsEquiv L
      (if (cols.find? (fun c => c.name == newCol.name)).isSome then
         cols.map (fun c => if c.name == newCol.name then newCol else c)
       else cols ++ [newCol])
      (match lookupColIdx? cols newCol.name with
       | some (idx, _) => cs1.set idx v1
       | none => cs1 ++ [v1])
      (match lookupColIdx? cols newCol.name with
       | some (idx, _) => cs2.set idx v2
       | none => cs2 ++ [v2]) := by
  cases hlk : lookupColIdx? cols newCol.name with
  | none =>
    have hfNone := (lookupColIdx?_none_iff_find?_none cols newCol.name).mp hlk
    simp only [hfNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact hce.append (.cons hv .nil)
  | some pair =>
    rcases pair with ⟨idx, origC⟩
    rcases lookupColIdx?_props hlk with ⟨hidxGet, horigName⟩
    have hfSome : (cols.find? (fun c => c.name == newCol.name)).isSome = true := by
      rw [← horigName, find_unique_of_mem huniq (List.mem_of_getElem? hidxGet)]; rfl
    simp only [hfSome, ↓reduceIte]
    apply cellsEquiv_set_at (fun c => if c.name == newCol.name then newCol else c) idx hce
    intro i c hi
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · subst heq; rw [hidxGet] at hi; injection hi with e; subst e
      simp only [horigName, beq_self_eq_true, ↓reduceIte]; exact hv
    · have hnameNe : (c.name == newCol.name) = false := by
        cases hb : (c.name == newCol.name)
        · rfl
        · exact absurd (distinctIdents_idx_unique huniq hi hidxGet ((beq_iff_eq.mp hb).trans horigName.symm)) hne
      simp [hnameNe]

theorem deriveRowOpt_rel {fuel' : Nat} {prog : Program} {L : TagSet}
    {env1 env2 : Env} {cols nextCols : List ColSpec} {item : DeriveItem}
    {r1 r2 nr1 nr2 : TableRow}
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true)
    (hr1Wf : CellsWf prog r1.cells cols)
    (hr2Wf : CellsWf prog r2.cells cols)
    (hrow : RowEquiv L cols r1 r2)
    (happly : applyDeriveItem prog (envToTyEnv env1) cols item = .ok nextCols)
    (hd1 : deriveRowOpt (evalRowExpr fuel' prog env1) cols item (lookupColIdx? cols (deriveItemTargetName item)) r1 = some nr1)
    (hd2 : deriveRowOpt (evalRowExpr fuel' prog env2) cols item (lookupColIdx? cols (deriveItemTargetName item)) r2 = some nr2) :
    RowEquiv L nextCols nr1 nr2 := by
  unfold deriveRowOpt at hd1 hd2
  cases hc1 : evalDeriveCell (evalRowExpr fuel' prog env1) cols r1 item <;> rw [hc1] at hd1 <;> try contradiction
  cases hc2 : evalDeriveCell (evalRowExpr fuel' prog env2) cols r2 item <;> rw [hc2] at hd2 <;> try contradiction
  injection hd1 with e1; injection hd2 with e2; subst e1; subst e2
  unfold RowEquiv; dsimp only
  cases item with
  | colExpr name re =>
    unfold applyDeriveItem at happly; simp only [bind, Except.bind] at happly
    cases hre : checkRowExpr prog (envToTyEnv env1) cols re with
    | error _ => rw [hre] at happly; contradiction
    | ok pair =>
      rcases pair with ⟨sTy, rTags⟩; rw [hre] at happly; simp only [] at happly
      let nc : ColSpec := { name := name, ty := sTy, tags := rTags, bucketed := false, aggKind := .raw }
      have hnextEq : nextCols = (if (cols.find? (fun c => c.name == nc.name)).isSome then
          cols.map (fun c => if c.name == nc.name then nc else c) else cols ++ [nc]) := by
        dsimp only [nc]; split at happly <;> simp_all
      rw [hnextEq]
      exact cellsEquiv_replace_or_append (newCol := nc) huniq hrow (fun hlow =>
        evalRowExpr_low_eq hprog hsafeProg henv hcols hr1Wf hr2Wf hrow hre hlow hc1 hc2)
  | bucketCol name src cuts labels =>
    unfold applyDeriveItem at happly; dsimp only at happly
    cases hs : cols.find? (fun c => c.name == src) with
    | none => rw [hs] at happly; contradiction
    | some srcCol =>
      rw [hs] at happly; dsimp only at happly
      split at happly <;> try contradiction
      let nc : ColSpec := { name := name, ty := .text, tags := srcCol.tags, bucketed := true, aggKind := .raw }
      have hnextEq : nextCols = (if (cols.find? (fun c => c.name == nc.name)).isSome then
          cols.map (fun c => if c.name == nc.name then nc else c) else cols ++ [nc]) := by
        dsimp only [nc]; split at happly <;> simp_all
      rw [hnextEq]
      apply cellsEquiv_replace_or_append (newCol := nc) huniq hrow
      intro hlow
      dsimp only [evalDeriveCell] at hc1 hc2
      rcases lookupColIdx?_of_find? hs with ⟨sIdx, hlkSrc, hgetSrc⟩
      rw [hlkSrc] at hc1 hc2; dsimp only at hc1 hc2
      have hcellEq := hrow.getElem?_eq hgetSrc hlow
      rw [hcellEq] at hc1
      cases hg2 : r2.cells[sIdx]? <;> rw [hg2] at hc1 hc2 <;> try contradiction
      dsimp only at hc1 hc2
      cases hb : evalBucketCell _ (cuts.map evalLiteral) labels <;> rw [hb] at hc1 hc2 <;> try contradiction
      injection hc1 with e1; injection hc2 with e2; exact e1.symm.trans e2

theorem evalDeriveItems_ni {fuel' : Nat} {prog : Program} {L : TagSet}
    {env1 env2 : Env} {w1 w2 : World}
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (hw1 : WorldWf prog w1) (hw2 : WorldWf prog w2) :
    ∀ (items : List DeriveItem) {curTV1 curTV2 : TableVal} {curCols outCols : List ColSpec}
      {ot : TagSet} {resTV1 resTV2 : TableVal} {w1' w2' : World},
      curTV1.cols = curCols → curTV2.cols = curCols →
      distinctIdents (curCols.map ColSpec.name) = true →
      (∀ c ∈ curCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
      RowsWf prog curTV1.rows curCols false false →
      RowsWf prog curTV2.rows curCols false false →
      applyDeriveItems prog (envToTyEnv env1) curCols items = .ok outCols →
      evalDeriveItems prog (envToTyEnv env1) (evalRowExpr fuel' prog env1) w1 curTV1 items = .ok (.table resTV1) w1' →
      evalDeriveItems prog (envToTyEnv env2) (evalRowExpr fuel' prog env2) w2 curTV2 items = .ok (.table resTV2) w2' →
      (if ot.subset L = true then
         RelList (RowEquiv L curCols) curTV1.rows curTV2.rows
       else
         ∃ rows1', List.Perm curTV1.rows rows1' ∧ RelList (RowEquiv L curCols) rows1' curTV2.rows) →
      if ot.subset L = true then
        RelList (RowEquiv L outCols) resTV1.rows resTV2.rows
      else
        ∃ rows1', List.Perm resTV1.rows rows1' ∧ RelList (RowEquiv L outCols) rows1' resTV2.rows
  | [], _, _, _, _, _, _, _, _, _, hc1, _, _, _, _, _, happly, hev1, hev2, hrel => by
    unfold applyDeriveItems at happly; injection happly with ec; subst ec
    unfold evalDeriveItems at hev1 hev2
    injection hev1 with ev1 _; injection hev2 with ev2 _
    injection ev1 with et1; injection ev2 with et2; subst et1; subst et2; exact hrel
  | item :: rest, curTV1, curTV2, curCols, outCols, ot, resTV1, resTV2, _, _,
    hc1, hc2, huniq, hcols, hrWf1, hrWf2, happly, hev1, hev2, hrel => by
    unfold applyDeriveItems at happly; simp only [bind, Except.bind] at happly
    cases hstep1 : applyDeriveItem prog (envToTyEnv env1) curCols item with
    | error _ => rw [hstep1] at happly; contradiction
    | ok nextCols =>
      rw [hstep1] at happly; dsimp only at happly
      have hstep2 : applyDeriveItem prog (envToTyEnv env2) curCols item = .ok nextCols := by
        rwa [← henv.envToTyEnv_eq]
      unfold evalDeriveItems at hev1 hev2
      rw [hc1, hstep1] at hev1; rw [hc2, hstep2] at hev2; dsimp only at hev1 hev2
      cases hm1 : evalDeriveMapRows (evalRowExpr fuel' prog env1) curCols item (lookupColIdx? curCols (deriveItemTargetName item)) curTV1.rows <;>
        rw [hm1] at hev1 <;> try contradiction
      cases hm2 : evalDeriveMapRows (evalRowExpr fuel' prog env2) curCols item (lookupColIdx? curCols (deriveItemTargetName item)) curTV2.rows <;>
        rw [hm2] at hev2 <;> try contradiction
      dsimp only at hev1 hev2
      rcases evalDeriveMapRows_eq_filterMap _ _ _ _ hm1 with ⟨hfm1, hall1⟩
      rcases evalDeriveMapRows_eq_filterMap _ _ _ _ hm2 with ⟨hfm2, hall2⟩
      have hreS1 := fun r re sTy rTags hr hre =>
        (eval_fuel_sound prog fuel').1 hprog env1 curCols r re sTy rTags henv.wf_left (fun c hc => (hcols c hc).1) hr hre
      have hreS2 := fun r re sTy rTags hr hre =>
        (eval_fuel_sound prog fuel').1 hprog env2 curCols r re sTy rTags henv.wf_right (fun c hc => (hcols c hc).1) hr hre
      have htnEq : deriveItemTargetName item = deriveItemName item := by cases item <;> rfl
      have hmapWf1 := evalDeriveMapRows_sound (evalRowExpr fuel' prog env1) huniq hstep1 hreS1 curTV1.rows hrWf1.to_forall
      have hmapWf2 := evalDeriveMapRows_sound (evalRowExpr fuel' prog env2) huniq hstep2 hreS2 curTV2.rows hrWf2.to_forall
      rw [← htnEq, hm1] at hmapWf1; rw [← htnEq, hm2] at hmapWf2
      dsimp only at hmapWf1 hmapWf2
      rcases applyDeriveItem_props huniq (fun c hc => ⟨(hcols c hc).1, (hcols c hc).2.1⟩) hstep1 with ⟨hnUniq, hnProps⟩
      have hnRaw := applyDeriveItem_raw (fun c hc => (hcols c hc).2.2) hstep1
      have hnextRel :
          if ot.subset L = true then
            RelList (RowEquiv L nextCols)
              (curTV1.rows.filterMap (deriveRowOpt (evalRowExpr fuel' prog env1) curCols item (lookupColIdx? curCols (deriveItemTargetName item))))
              (curTV2.rows.filterMap (deriveRowOpt (evalRowExpr fuel' prog env2) curCols item (lookupColIdx? curCols (deriveItemTargetName item))))
          else
            ∃ rows1', List.Perm
              (curTV1.rows.filterMap (deriveRowOpt (evalRowExpr fuel' prog env1) curCols item (lookupColIdx? curCols (deriveItemTargetName item))))
              rows1' ∧
              RelList (RowEquiv L nextCols) rows1'
                (curTV2.rows.filterMap (deriveRowOpt (evalRowExpr fuel' prog env2) curCols item (lookupColIdx? curCols (deriveItemTargetName item)))) := by
        cases hord : ot.subset L
        · simp only [hord, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
          rcases hrel with ⟨rows1', hp, hr'⟩
          refine ⟨rows1'.filterMap (deriveRowOpt (evalRowExpr fuel' prog env1) curCols item (lookupColIdx? curCols (deriveItemTargetName item))),
            perm_filterMap _ hp, ?_⟩
          apply hr'.with_mem.filterMap_rel
          intro r1 r2 ⟨hr1Mem, hr2Mem, hrowEq⟩
          have hr1InOrig := hp.symm.subset hr1Mem
          rcases hall1 r1 hr1InOrig with ⟨nr1, hd1⟩
          rcases hall2 r2 hr2Mem with ⟨nr2, hd2⟩
          exact Or.inr ⟨nr1, nr2, hd1, hd2, deriveRowOpt_rel hprog hsafeProg henv huniq
            (fun c hc => (hcols c hc).1) (hrWf1.to_forall r1 hr1InOrig) (hrWf2.to_forall r2 hr2Mem) hrowEq hstep1 hd1 hd2⟩
        · simp only [hord, ↓reduceIte] at hrel ⊢
          apply hrel.with_mem.filterMap_rel
          intro r1 r2 ⟨hr1Mem, hr2Mem, hrowEq⟩
          rcases hall1 r1 hr1Mem with ⟨nr1, hd1⟩
          rcases hall2 r2 hr2Mem with ⟨nr2, hd2⟩
          exact Or.inr ⟨nr1, nr2, hd1, hd2, deriveRowOpt_rel hprog hsafeProg henv huniq
            (fun c hc => (hcols c hc).1) (hrWf1.to_forall r1 hr1Mem) (hrWf2.to_forall r2 hr2Mem) hrowEq hstep1 hd1 hd2⟩
      rw [← hfm1, ← hfm2] at hnextRel
      exact evalDeriveItems_ni hprog hsafeProg henv hw1 hw2 rest (curCols := nextCols) (ot := ot)
        rfl rfl hnUniq (fun c hc => ⟨(hnProps c hc).1, (hnProps c hc).2, hnRaw c hc⟩)
        (RowsWf.of_forall_raw hmapWf1) (RowsWf.of_forall_raw hmapWf2)
        happly hev1 hev2 hnextRel

/-! ### `Filter` Non-Interference Helpers -/

theorem evalFilterRows_eq_filter
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (inCols outCols : List ColSpec) (pred : RowExpr) (w : World) :
    ∀ {rs : List TableRow} {resTV : TableVal} {w' : World},
      evalFilterRows evalRE inCols outCols pred w rs = .ok (.table resTV) w' →
      resTV.rows = (rs.filter (fun r => match evalRE inCols r pred with | .ok (.bool b) => b | _ => false)).map
        (fun r => { r with groupMeta := none }) ∧
      (∀ r ∈ rs, ∃ b, evalRE inCols r pred = .ok (.bool b))
  | [], _, _, h => by
    injection h with ev _; injection ev with et; subst et
    exact ⟨rfl, fun _ hm => nomatch hm⟩
  | r :: rs, _, _, h => by
    unfold evalFilterRows at h
    cases hp : evalRE inCols r pred with
    | stopped _ | outOfFuel | wrong => rw [hp] at h; nomatch h
    | ok pv =>
      rw [hp] at h
      cases pv with
      | bool keep =>
        dsimp only at h
        cases hrest : evalFilterRows evalRE inCols outCols pred w rs with
        | stopped _ _ | failed _ _ | jumped _ _ _ | wrong | outOfFuel => rw [hrest] at h; nomatch h
        | ok rv _ =>
          rw [hrest] at h
          cases rv with
          | table restTV =>
            dsimp only at h
            injection h with ev2 _; injection ev2 with et; subst et
            rcases evalFilterRows_eq_filter evalRE inCols outCols pred w hrest with ⟨ihEq, ihAll⟩
            refine ⟨?_, ?_⟩
            · simp only [List.filter_cons, hp]
              cases keep <;> simp [ihEq]
            · intro x hx; rcases List.mem_cons.mp hx with rfl | htl
              · exact ⟨keep, hp⟩
              · exact ihAll x htl
          | _ => dsimp only at h; injection h with hv _; cases hv
      | _ => dsimp only at h; contradiction

theorem evalFilterRows_ni {fuel' : Nat} {prog : Program} {L : TagSet}
    {env1 env2 : Env} {tv1 tv2 resTV1 resTV2 : TableVal} {tt : TableTy}
    {pred : RowExpr} {pTags : TagSet} {w1 w2 w1' w2' : World}
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (ht : TableEquiv prog L tv1 tv2 tt)
    (hrLow : tt.rowTags.subset L = true)
    (hpLow : pTags.subset L = true)
    (hpred : checkRowExpr prog (envToTyEnv env1) tt.cols pred = .ok (.bool, pTags))
    (hev1 : evalFilterRows (evalRowExpr fuel' prog env1) tv1.cols (tv1.cols.map (fun c => { c with aggKind := .raw })) pred w1 tv1.rows = .ok (.table resTV1) w1')
    (hev2 : evalFilterRows (evalRowExpr fuel' prog env2) tv2.cols (tv2.cols.map (fun c => { c with aggKind := .raw })) pred w2 tv2.rows = .ok (.table resTV2) w2') :
    let outCols := tt.cols.map (fun c => { c with aggKind := .raw })
    if tt.orderTags.subset L = true then
      RelList (RowEquiv L outCols) resTV1.rows resTV2.rows
    else
      ∃ rows1', List.Perm resTV1.rows rows1' ∧ RelList (RowEquiv L outCols) rows1' resTV2.rows := by
  intro outCols
  rcases ht.cols_eq with ⟨hc1, hc2⟩
  rw [hc1] at hev1; rw [hc2] at hev2
  cases ht.wf1 with | table _ hsch hrWf1 =>
  cases ht.wf2 with | table _ _ hrWf2 =>
  have hcols := fun c hc => (tableSchemaWf_cols_props hsch).2 c hc |>.1
  rcases evalFilterRows_eq_filter _ _ _ _ _ hev1 with ⟨hflt1, hall1⟩
  rcases evalFilterRows_eq_filter _ _ _ _ _ hev2 with ⟨hflt2, hall2⟩
  rw [hflt1, hflt2]
  let p1 := fun r => match evalRowExpr fuel' prog env1 tt.cols r pred with | .ok (.bool b) => b | _ => false
  let p2 := fun r => match evalRowExpr fuel' prog env2 tt.cols r pred with | .ok (.bool b) => b | _ => false
  let resetGM : TableRow → TableRow := fun r => { r with groupMeta := none }
  have hpCongr : ∀ r1 r2, r1 ∈ tv1.rows → r2 ∈ tv2.rows → RowEquiv L tt.cols r1 r2 → p1 r1 = p2 r2 := by
    intro r1 r2 hm1 hm2 hrow
    rcases hall1 r1 hm1 with ⟨b1, hb1⟩
    rcases hall2 r2 hm2 with ⟨b2, hb2⟩
    have hvEq := evalRowExpr_low_eq hprog hsafeProg henv hcols
      (hrWf1.to_forall r1 hm1) (hrWf2.to_forall r2 hm2) hrow hpred hpLow hb1 hb2
    injection hvEq with hbEq; subst hbEq
    dsimp only [p1, p2]; rw [hb1, hb2]
  have hrowMap : ∀ r1 r2, RowEquiv L tt.cols r1 r2 → RowEquiv L outCols (resetGM r1) (resetGM r2) :=
    fun _ _ hr => cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hr (fun _ _ h => h)
  have hlr := ht.lowRows hrLow
  cases hord : tt.orderTags.subset L
  · simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr ⊢
    rcases hlr with ⟨rows1', hp, hrel⟩
    refine ⟨(rows1'.filter p1).map resetGM, (perm_filter p1 hp).map resetGM, ?_⟩
    have hfltRel := hrel.with_mem.filter_congr (fun a b ⟨ha, hb, hr⟩ => hpCongr a b (hp.symm.subset ha) hb hr)
    exact hfltRel.map resetGM resetGM (fun _ _ ⟨_, _, hr⟩ => hrowMap _ _ hr)
  · simp only [hord, ↓reduceIte] at hlr ⊢
    have hfltRel := hlr.with_mem.filter_congr (fun a b ⟨ha, hb, hr⟩ => hpCongr a b ha hb hr)
    exact hfltRel.map resetGM resetGM (fun _ _ ⟨_, _, hr⟩ => hrowMap _ _ hr)

/-! ### `Distinct` Non-Interference Helpers -/

theorem dedupTableRows_relList {L : TagSet} {cols : List ColSpec} {keyNames : List Ident}
    (hlowKeys : ∀ k ∈ keyNames, ∀ c, cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true) :
    ∀ (seen : List (List Val)) {rs1 rs2 out1 out2 : List TableRow},
      RelList (RowEquiv L cols) rs1 rs2 →
      dedupTableRows cols keyNames seen rs1 = some out1 →
      dedupTableRows cols keyNames seen rs2 = some out2 →
      RelList (RowEquiv L (cols.map (fun c => { c with aggKind := .raw }))) out1 out2
  | _, [], [], _, _, .nil, ho1, ho2 => by
    injection ho1 with e1; injection ho2 with e2; subst e1; subst e2; exact .nil
  | seen, r1 :: _, r2 :: _, _, _, .cons hr htl, ho1, ho2 => by
    unfold dedupTableRows at ho1 ho2; simp only [bind, Option.bind] at ho1 ho2
    have hkvEq := extractKeyVals_congr_of_low hr hlowKeys
    rw [hkvEq] at ho1
    cases hkv : extractKeyVals cols keyNames r2 <;> rw [hkv] at ho1 ho2 <;> try contradiction
    rename_i kv; dsimp only at ho1 ho2
    cases hany : seen.any (fun sk => valListEq sk kv)
    · simp only [hany, Bool.false_eq_true, ↓reduceIte] at ho1 ho2
      cases ht1 : dedupTableRows cols keyNames (kv :: seen) _ <;> rw [ht1] at ho1 <;> try contradiction
      cases ht2 : dedupTableRows cols keyNames (kv :: seen) _ <;> rw [ht2] at ho2 <;> try contradiction
      injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
      exact .cons (cellsEquiv_map_tags _ hr (fun _ _ h => h))
        (dedupTableRows_relList hlowKeys (kv :: seen) htl ht1 ht2)
    · simp only [hany, ↓reduceIte] at ho1 ho2
      exact dedupTableRows_relList hlowKeys seen htl ho1 ho2

private theorem sorted_strict_unique_ext {α : Type} {l1 l2 : List α} {lt : α → α → Bool}
    (hirrefl : ∀ x ∈ l1, lt x x = false)
    (htrans : ∀ a b c, a ∈ l1 → b ∈ l2 → c ∈ l1 → lt a b = true → lt b c = true → lt a c = true) :
    ∀ {xs ys : List α},
      (∀ x ∈ xs, x ∈ l1) →
      (∀ y ∈ ys, y ∈ l2) →
      xs.Pairwise (fun a b => lt a b = true) →
      ys.Pairwise (fun a b => lt a b = true) →
      (∀ z, z ∈ xs ↔ z ∈ ys) →
      xs = ys
  | [], [], _, _, _, _, _ => rfl
  | [], y :: _, _, _, _, _, hm => nomatch (hm y).mpr (.head _)
  | x :: _, [], _, _, _, _, hm => nomatch (hm x).mp (.head _)
  | x :: xs, y :: ys, h1, h2, .cons hx hxs, .cons hy hys, hm => by
    have hxIn : x ∈ y :: ys := (hm x).mp (.head _)
    have hyIn : y ∈ x :: xs := (hm y).mpr (.head _)
    have hxy : x = y := by
      rcases List.mem_cons.mp hxIn with rfl | hxy'
      · rfl
      · rcases List.mem_cons.mp hyIn with rfl | hyx'
        · rfl
        · exfalso
          have hlt := htrans x y x (h1 x (.head _)) (h2 y (.head _)) (h1 x (.head _)) (hx y hyx') (hy x hxy')
          rw [hirrefl x (h1 x (.head _))] at hlt; nomatch hlt
    subst hxy
    congr 1
    apply sorted_strict_unique_ext hirrefl htrans (fun a ha => h1 a (.tail _ ha)) (fun b hb => h2 b (.tail _ hb)) hxs hys
    intro z
    have hzx : z ∈ xs → z ≠ x := fun hz heq => by
      subst heq; have := hx z hz; rw [hirrefl z (h1 z (.head _))] at this; nomatch this
    have hzy : z ∈ ys → z ≠ x := fun hz heq => by
      subst heq; have := hy z hz; rw [hirrefl z (h1 z (.head _))] at this; nomatch this
    constructor
    · intro hz; rcases List.mem_cons.mp ((hm z).mp (.tail _ hz)) with rfl | h'; exact absurd rfl (hzx hz); exact h'
    · intro hz; rcases List.mem_cons.mp ((hm z).mpr (.tail _ hz)) with rfl | h'; exact absurd rfl (hzy hz); exact h'

private theorem cells_eq_of_extractKeyVals_all {prog : Program} {cols : List ColSpec} {keyNames : List Ident}
    {r1 r2 : TableRow} {kv : List Val}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hallNames : ∀ c ∈ cols, c.name ∈ keyNames)
    (hr1Wf : CellsWf prog r1.cells cols)
    (hr2Wf : CellsWf prog r2.cells cols)
    (hkv1 : extractKeyVals cols keyNames r1 = some kv)
    (hkv2 : extractKeyVals cols keyNames r2 = some kv) :
    r1.cells = r2.cells := by
  have hgetEq : ∀ (ks : List Ident) (kv0 : List Val) (k : Ident) (idx : Nat) (c : ColSpec),
      k ∈ ks → lookupColIdx? cols k = some (idx, c) →
      extractKeyVals.go cols r1 ks = some kv0 →
      extractKeyVals.go cols r2 ks = some kv0 →
      r1.cells[idx]? = r2.cells[idx]? := by
    intro ks
    induction ks with
    | nil => intro _ _ _ _ hm; nomatch hm
    | cons k0 rest ih =>
      intro kv0 k idx c hm hlk h1 h2
      unfold extractKeyVals.go at h1 h2; simp only [bind, Option.bind] at h1 h2
      cases hlk0 : lookupColIdx? cols k0 with
      | none => rw [hlk0] at h1; contradiction
      | some p0 =>
        rcases p0 with ⟨idx0, c0⟩; rw [hlk0] at h1 h2; dsimp only at h1 h2
        cases hc1 : r1.cells[idx0]? <;> rw [hc1] at h1 <;> try contradiction
        cases hc2 : r2.cells[idx0]? <;> rw [hc2] at h2 <;> try contradiction
        dsimp only at h1 h2
        cases ht1 : extractKeyVals.go cols r1 rest <;> rw [ht1] at h1 <;> try contradiction
        cases ht2 : extractKeyVals.go cols r2 rest <;> rw [ht2] at h2 <;> try contradiction
        injection h1 with e1; injection h2 with e2; subst e2
        injection e1 with eh et
        rcases List.mem_cons.mp hm with rfl | hrest
        · rw [hlk] at hlk0; injection hlk0 with hpEq; injection hpEq with hi _; subst hi; rw [hc1, hc2, eh]
        · exact ih _ k idx c hrest hlk ht1 (et ▸ ht2)
  apply List.ext_getElem?
  intro i
  cases hci : cols[i]? with
  | none =>
    have hge := List.getElem?_eq_none_iff.mp hci
    rw [List.getElem?_eq_none (hr1Wf.length_eq ▸ hge), List.getElem?_eq_none (hr2Wf.length_eq ▸ hge)]
  | some c =>
    have hcMem := List.mem_of_getElem? hci
    have hfind := find_unique_of_mem huniq hcMem
    rcases lookupColIdx?_of_find? hfind with ⟨idx, hlk, hgetIdx⟩
    have hiEq := distinctIdents_idx_unique huniq hci hgetIdx rfl
    subst hiEq
    exact hgetEq keyNames kv c.name i c (hallNames c hcMem) hlk hkv1 hkv2

private theorem cellsWf_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {cs : List Val} {cols : List ColSpec},
      CellsWf prog cs cols → SortableValList cs
  | [], [], .nil => .nil
  | _ :: _, c :: _, .cons hv htl =>
    .cons (valWf_sortable hd hv (ScalarTy.isSortable_toTy c.ty)) (cellsWf_sortable hd htl)

theorem dedupTableRows_all_cols_props {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {cols : List ColSpec} {keyNames : List Ident}
    (huniq : distinctIdents (cols.map ColSpec.name) = true)
    (hcols : ∀ c ∈ cols, validScalarTy prog c.ty = true)
    (hallNames : ∀ c ∈ cols, c.name ∈ keyNames) :
    ∀ {seen : List (List Val)} {rs out : List TableRow},
      (∀ sk ∈ seen, SortableValList sk) →
      (∀ r ∈ rs, CellsWf prog r.cells cols) →
      dedupTableRows cols keyNames seen rs = some out →
      (∀ x ∈ out, x.groupMeta = none ∧ CellsWf prog x.cells cols ∧
        ∃ kx, extractKeyVals cols keyNames x = some kx ∧ kx ∉ seen) ∧
      out.Pairwise (· ≠ ·) ∧
      (∀ x, x.groupMeta = none →
        (x ∈ out ↔ (x ∈ rs.map (fun r => { r with groupMeta := none }) ∧
          ∀ kx, extractKeyVals cols keyNames x = some kx → kx ∉ seen)))
  | _, [], _, _, _, ho => by
    injection ho with e; subst e
    exact ⟨(fun _ hm => nomatch hm), .nil, fun _ _ => by simp⟩
  | seen, r :: rs, _, hseenS, hrsWf, ho => by
    unfold dedupTableRows at ho; simp only [bind, Option.bind] at ho
    cases hkv : extractKeyVals cols keyNames r with
    | none => rw [hkv] at ho; contradiction
    | some kv =>
      rw [hkv] at ho; dsimp only at ho
      have hrWf := hrsWf r (.head _)
      have hkvS := extractKeyVals_sortable hd hcols hrWf hkv
      have hanyIff : seen.any (fun sk => valListEq sk kv) = true ↔ kv ∈ seen := by
        rw [List.any_eq_true]
        constructor
        · rintro ⟨sk, hsk, heq⟩; rwa [← (valListEq_iff_eq (hseenS sk hsk) hkvS).mp heq]
        · intro hmem; exact ⟨kv, hmem, (valListEq_iff_eq hkvS hkvS).mpr rfl⟩
      have hkvReset : ∀ y : TableRow, extractKeyVals cols keyNames { y with groupMeta := none } = extractKeyVals cols keyNames y := by
        intro y; unfold extractKeyVals
        let rec aux : ∀ ks, extractKeyVals.go cols { y with groupMeta := none } ks = extractKeyVals.go cols y ks
          | [] => rfl
          | k :: ks => by unfold extractKeyVals.go; simp [aux ks]
        exact aux keyNames
      cases hany : seen.any (fun sk => valListEq sk kv)
      · simp only [hany, Bool.false_eq_true, ↓reduceIte] at ho
        have hkvNot : kv ∉ seen := fun hm => by rw [hanyIff.mpr hm] at hany; nomatch hany
        cases htl : dedupTableRows cols keyNames (kv :: seen) rs with
        | none => rw [htl] at ho; contradiction
        | some tl =>
          rw [htl] at ho; injection ho with e; subst e
          have hseen' : ∀ sk ∈ kv :: seen, SortableValList sk := by
            intro sk hsk; rcases List.mem_cons.mp hsk with rfl | hs; exact hkvS; exact hseenS sk hs
          rcases dedupTableRows_all_cols_props hd huniq hcols hallNames hseen' (fun x hx => hrsWf x (.tail _ hx)) htl with
            ⟨htlProps, htlNodup, htlMem⟩
          let r0 : TableRow := { r with groupMeta := none }
          have hr0Kv : extractKeyVals cols keyNames r0 = some kv := (hkvReset r).trans hkv
          refine ⟨?_, ?_, ?_⟩
          · intro x hx; rcases List.mem_cons.mp hx with rfl | hxtl
            · exact ⟨rfl, hrWf, kv, hr0Kv, hkvNot⟩
            · rcases htlProps x hxtl with ⟨hgm, hwf, kx, hkx, hkxNot⟩
              exact ⟨hgm, hwf, kx, hkx, fun hm => hkxNot (.tail _ hm)⟩
          · refine .cons ?_ htlNodup
            intro y hy heq; subst heq
            rcases htlProps r0 hy with ⟨_, _, ky, hky, hkyNot⟩
            rw [hr0Kv] at hky; injection hky with ek; subst ek
            exact hkyNot (.head _)
          · intro x hxGm
            simp only [List.mem_cons, List.map_cons]
            constructor
            · rintro (rfl | hxtl)
              · exact ⟨Or.inl rfl, fun kx hkx => by rw [hr0Kv] at hkx; injection hkx with e; subst e; exact hkvNot⟩
              · rcases (htlMem x hxGm).mp hxtl with ⟨hxInRs, hkxNot⟩
                exact ⟨Or.inr hxInRs, fun kx hkx hm => hkxNot kx hkx (.tail _ hm)⟩
            · rintro ⟨(rfl | hxInRs), hkxNot⟩
              · exact Or.inl rfl
              · by_cases hxeq : valListEq x.cells r0.cells = true
                · rw [List.mem_map] at hxInRs; rcases hxInRs with ⟨orig, horig, horigEq⟩
                  have hwfX : CellsWf prog x.cells cols := horigEq ▸ hrsWf orig (.tail _ horig)
                  have hcEq := (valListEq_iff_eq (cellsWf_sortable hd hwfX) (cellsWf_sortable hd hrWf)).mp hxeq
                  cases x with | mk xcs xgm =>
                  dsimp only at hxGm hcEq; subst hxGm; subst hcEq
                  exact Or.inl rfl
                · apply Or.inr
                  apply (htlMem x hxGm).mpr
                  refine ⟨hxInRs, fun kx hkx hmemCons => ?_⟩
                  rcases List.mem_cons.mp hmemCons with rfl | hmemSeen
                  · rw [List.mem_map] at hxInRs; rcases hxInRs with ⟨orig, horig, horigEq⟩
                    have hwfX : CellsWf prog x.cells cols := horigEq ▸ hrsWf orig (.tail _ horig)
                    have hcEq := cells_eq_of_extractKeyVals_all huniq hallNames hwfX hrWf hkx hkv
                    have hr0S := cellsWf_sortable hd hrWf
                    exact hxeq (hcEq ▸ (valListEq_iff_eq hr0S hr0S).mpr rfl)
                  · exact hkxNot kx hkx hmemSeen
      · simp only [hany, ↓reduceIte] at ho
        have hkvIn : kv ∈ seen := hanyIff.mp hany
        rcases dedupTableRows_all_cols_props hd huniq hcols hallNames hseenS (fun x hx => hrsWf x (.tail _ hx)) ho with
          ⟨htlProps, htlNodup, htlMem⟩
        refine ⟨htlProps, htlNodup, ?_⟩
        intro x hxGm
        rw [htlMem x hxGm]
        simp only [List.map_cons, List.mem_cons]
        constructor
        · rintro ⟨hxIn, hnot⟩; exact ⟨Or.inr hxIn, hnot⟩
        · rintro ⟨(rfl | hxIn), hnot⟩
          · exact absurd hkvIn (hnot kv ((hkvReset r).trans hkv))
          · exact ⟨hxIn, hnot⟩

theorem cellsWf_sortableList {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {cols : List ColSpec} {cs : List Val},
      CellsWf prog cs cols → SortableValList cs
  | [], [], .nil => .nil
  | c :: _, _ :: _, .cons hv htl =>
    .cons (valWf_sortable hd hv (ScalarTy.isSortable_toTy c.ty)) (cellsWf_sortableList hd htl)

private theorem perm_of_nodup_same_mem_rows {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {cols : List ColSpec} {xs ys : List TableRow}
    (hxProps : ∀ x ∈ xs, x.groupMeta = none ∧ CellsWf prog x.cells cols)
    (hyProps : ∀ y ∈ ys, y.groupMeta = none ∧ CellsWf prog y.cells cols)
    (hxNodup : xs.Pairwise (· ≠ ·))
    (hyNodup : ys.Pairwise (· ≠ ·))
    (hmem : ∀ z, z.groupMeta = none → (z ∈ xs ↔ z ∈ ys)) :
    List.Perm xs ys := by
  let ltRow : TableRow → TableRow → Bool := fun a b => valListLt a.cells b.cells
  let P : TableRow → Prop := fun r => r.groupMeta = none ∧ SortableValList r.cells
  have hxP : ∀ x ∈ xs, P x := fun x hx => ⟨(hxProps x hx).1, cellsWf_sortableList hd (hxProps x hx).2⟩
  have hyP : ∀ y ∈ ys, P y := fun y hy => ⟨(hyProps y hy).1, cellsWf_sortableList hd (hyProps y hy).2⟩
  have hirrefl : ∀ {a}, P a → ltRow a a = false := fun ha => valListLt_irrefl ha.2
  have htrans : ∀ {a b c}, P a → P b → P c → ltRow a b = true → ltRow b c = true → ltRow a c = true :=
    fun ha hb hc => valListLt_trans ha.2 hb.2 hc.2
  have htrich : ∀ {a b}, P a → P b → ltRow a b = true ∨ a = b ∨ ltRow b a = true := by
    intro a b ha hb
    rcases valListLt_trichotomy ha.2 hb.2 with hlt | hcEq | hgt
    · exact Or.inl hlt
    · cases a with | mk ac agm => cases b with | mk bc bgm =>
      dsimp only [P] at ha hb hcEq; rw [ha.1, hb.1, hcEq]; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hgt)
  let sxs := insertionSortBy ltRow xs
  let sys := insertionSortBy ltRow ys
  have hpX := insertionSortBy_perm ltRow xs
  have hpY := insertionSortBy_perm ltRow ys
  have hpwX := pairwise_insertionSortBy hirrefl htrans htrich hxP
  have hpwY := pairwise_insertionSortBy hirrefl htrans htrich hyP
  have hndX : sxs.Pairwise (· ≠ ·) := (List.Perm.pairwise_iff (@Ne.symm TableRow) hpX).mpr hxNodup
  have hndY : sys.Pairwise (· ≠ ·) := (List.Perm.pairwise_iff (@Ne.symm TableRow) hpY).mpr hyNodup
  have toStrict : ∀ {zs : List TableRow}, (∀ z ∈ zs, P z) → zs.Pairwise (fun a b => ¬ ltRow b a = true) → zs.Pairwise (· ≠ ·) → zs.Pairwise (fun a b => ltRow a b = true) := by
    intro zs hzP hpw hnd
    induction zs with
    | nil => exact .nil
    | cons z ztl ih =>
      cases hpw with | cons h1 hpwTl =>
      cases hnd with | cons h2 hndTl =>
      refine .cons (fun w hw => ?_) (ih (fun u hu => hzP u (.tail _ hu)) hpwTl hndTl)
      rcases htrich (hzP z (.head _)) (hzP w (.tail _ hw)) with hlt | heq | hgt
      · exact hlt
      · exact absurd heq (h2 w hw)
      · exact absurd hgt (h1 w hw)
  have hsxP : ∀ z ∈ sxs, P z := fun z hz => hxP z (hpX.subset hz)
  have hsyP : ∀ z ∈ sys, P z := fun z hz => hyP z (hpY.subset hz)
  have hstrX := toStrict hsxP hpwX hndX
  have hstrY := toStrict hsyP hpwY hndY
  have heqS : sxs = sys := by
    apply sorted_strict_unique_ext (l1 := sxs) (l2 := sys)
      (fun x hx => hirrefl (hsxP x hx))
      (fun a b c ha hb hc => htrans (hsxP a ha) (hsyP b hb) (hsxP c hc))
      (fun _ h => h) (fun _ h => h) hstrX hstrY
    intro z
    constructor
    · intro hz; have hgm := (hsxP z hz).1
      exact hpY.symm.subset ((hmem z hgm).mp (hpX.subset hz))
    · intro hz; have hgm := (hsyP z hz).1
      exact hpX.symm.subset ((hmem z hgm).mpr (hpY.subset hz))
  dsimp only [sxs, sys] at hpX hpY heqS
  rw [← heqS] at hpY
  exact hpX.symm.trans hpY

/-! ### `Join` Non-Interference Helpers -/

theorem wrapIntoOptionVal_congr (sTy : ScalarTy) {v1 v2 : Val} (h : v1 = v2) :
    wrapIntoOptionVal sTy v1 = wrapIntoOptionVal sTy v2 := h ▸ rfl

theorem extractRightJoinCells_rel {L : TagSet} (isLeftOuter : Bool) {rCols : List ColSpec}
    {mr1 mr2 : TableRow} (hmr : RowEquiv L rCols mr1 mr2) :
    ∀ {rKeepIdxs : List (ColSpec × Nat)} {rc1 rc2 : List Val},
      (∀ p ∈ rKeepIdxs, rCols[p.2]? = some p.1) →
      extractRightJoinCells isLeftOuter mr1 rKeepIdxs = some rc1 →
      extractRightJoinCells isLeftOuter mr2 rKeepIdxs = some rc2 →
      CellsEquiv L (rKeepIdxs.map (fun (rc, _) =>
        { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty,
                  bucketed := if isLeftOuter then false else rc.bucketed,
                  aggKind := .raw })) rc1 rc2
  | [], _, _, _, h1, h2 => by injection h1 with e1; injection h2 with e2; subst e1; subst e2; exact .nil
  | (rc, idx) :: rest, _, _, hall, h1, h2 => by
    unfold extractRightJoinCells at h1 h2; simp only [bind, Option.bind] at h1 h2
    cases hg1 : mr1.cells[idx]? <;> rw [hg1] at h1 <;> try contradiction
    cases hg2 : mr2.cells[idx]? <;> rw [hg2] at h2 <;> try contradiction
    dsimp only at h1 h2
    cases ht1 : extractRightJoinCells isLeftOuter mr1 rest <;> rw [ht1] at h1 <;> try contradiction
    cases ht2 : extractRightJoinCells isLeftOuter mr2 rest <;> rw [ht2] at h2 <;> try contradiction
    injection h1 with e1; injection h2 with e2; subst e1; subst e2
    refine .cons (fun hlow => ?_)
      (extractRightJoinCells_rel isLeftOuter hmr (fun p hp => hall p (.tail _ hp)) ht1 ht2)
    have hce := hmr.getElem?_eq (hall (rc, idx) (.head _)) hlow
    rw [hg1, hg2] at hce; injection hce with ev; subst ev; rfl

theorem combineJoinMatches_eq_filterMap (isLeftOuter : Bool)
    (rKeepIdxs : List (ColSpec × Nat)) (lCells : List Val) :
    ∀ {mrs curJ : List TableRow},
      combineJoinMatches isLeftOuter rKeepIdxs lCells mrs = some curJ →
      curJ = mrs.filterMap (fun mr => (extractRightJoinCells isLeftOuter mr rKeepIdxs).map
        (fun rc => { cells := lCells ++ rc, groupMeta := none }))
  | [], _, h => by injection h with e; exact e.symm
  | mr :: mrs, _, h => by
    unfold combineJoinMatches at h; simp only [bind, Option.bind] at h
    cases hr : extractRightJoinCells isLeftOuter mr rKeepIdxs <;> rw [hr] at h <;> try contradiction
    dsimp only at h
    cases ht : combineJoinMatches isLeftOuter rKeepIdxs lCells mrs <;> rw [ht] at h <;> try contradiction
    injection h with e; subst e
    simp [hr, ← combineJoinMatches_eq_filterMap isLeftOuter rKeepIdxs lCells ht]

theorem combineJoinMatches_relList {L : TagSet} (isLeftOuter : Bool)
    {lUpdated rCols : List ColSpec} {rKeepIdxs : List (ColSpec × Nat)}
    {lCells1 lCells2 : List Val}
    (hlCells : CellsEquiv L lUpdated lCells1 lCells2)
    (hallIdx : ∀ p ∈ rKeepIdxs, rCols[p.2]? = some p.1) :
    ∀ {mrs1 mrs2 curJ1 curJ2 : List TableRow},
      RelList (RowEquiv L rCols) mrs1 mrs2 →
      combineJoinMatches isLeftOuter rKeepIdxs lCells1 mrs1 = some curJ1 →
      combineJoinMatches isLeftOuter rKeepIdxs lCells2 mrs2 = some curJ2 →
      RelList (RowEquiv L (lUpdated ++ rKeepIdxs.map (fun (rc, _) =>
        { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty,
                  bucketed := if isLeftOuter then false else rc.bucketed,
                  aggKind := .raw }))) curJ1 curJ2
  | [], [], _, _, .nil, h1, h2 => by
    injection h1 with e1; injection h2 with e2; subst e1; subst e2; exact .nil
  | mr1 :: _, mr2 :: _, _, _, .cons hmr htl, h1, h2 => by
    unfold combineJoinMatches at h1 h2; simp only [bind, Option.bind] at h1 h2
    cases hr1 : extractRightJoinCells isLeftOuter mr1 rKeepIdxs <;> rw [hr1] at h1 <;> try contradiction
    cases hr2 : extractRightJoinCells isLeftOuter mr2 rKeepIdxs <;> rw [hr2] at h2 <;> try contradiction
    dsimp only at h1 h2
    cases ht1 : combineJoinMatches isLeftOuter rKeepIdxs lCells1 _ <;> rw [ht1] at h1 <;> try contradiction
    cases ht2 : combineJoinMatches isLeftOuter rKeepIdxs lCells2 _ <;> rw [ht2] at h2 <;> try contradiction
    injection h1 with e1; injection h2 with e2; subst e1; subst e2
    exact .cons (hlCells.append (extractRightJoinCells_rel isLeftOuter hmr hallIdx hr1 hr2))
      (combineJoinMatches_relList isLeftOuter hlCells hallIdx htl ht1 ht2)

theorem buildJoinedCols_tags_eq (kind : JoinKind) (lCols rCols joinedCols : List ColSpec)
    (on : JoinOn) (suffixes : Suffixes)
    (hb : buildJoinedCols kind lCols rCols on suffixes = .ok joinedCols) :
    match kind with
    | .semi | .anti => joinedCols = lCols.map (fun c => { c with aggKind := .raw })
    | _ =>
      let sameKeyNames := match on with | .sameKeys ks => ks | .pairs _ => []
      let rFiltered := rCols.filter (fun rc => !sameKeyNames.contains rc.name)
      let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
      let lUpdated := lCols.map (fun lc =>
        if sameKeyNames.contains lc.name then
          match rCols.find? (fun rc => rc.name == lc.name) with
          | some rc => { lc with tags := lc.tags.union rc.tags, bucketed := false, aggKind := .raw }
          | none => { lc with aggKind := .raw }
        else { lc with aggKind := .raw })
      let rPrepared := rFiltered.map (fun rc =>
        { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty,
                  bucketed := if isLeftOuter then false else rc.bucketed,
                  aggKind := .raw })
      joinedCols.map ColSpec.tags = (lUpdated ++ rPrepared).map ColSpec.tags := by
  have hrenTags : ∀ (ns : List Ident) (suf : String) (cs : List ColSpec),
      (cs.map (fun c => if ns.contains c.name then { c with name := c.name ++ suf } else c)).map ColSpec.tags =
        cs.map ColSpec.tags := by
    intro ns suf cs; induction cs with
    | nil => rfl
    | cons d ds ih => simp only [List.map_cons, ih]; cases ns.contains d.name <;> rfl
  have hcolStep : ∀ (lUpd rPrep : List ColSpec),
      (if !((lUpd.map ColSpec.name).any (fun n => (rPrep.map ColSpec.name).contains n)) then
          Except.ok (lUpd ++ rPrep)
        else
          match suffixes with
          | none => Except.error "overlapping non-key join columns require explicit suffixes"
          | some (sL, sR) =>
            if sL == sR || (sL.isEmpty && sR.isEmpty) then
              Except.error "join suffixes must be distinct"
            else
              let lRenamed := lUpd.map (fun c => if (rPrep.map ColSpec.name).contains c.name then { c with name := c.name ++ sL } else c)
              let rRenamed := rPrep.map (fun c => if (lUpd.map ColSpec.name).contains c.name then { c with name := c.name ++ sR } else c)
              let combined := lRenamed ++ rRenamed
              if distinctIdents (combined.map ColSpec.name) then Except.ok combined
              else Except.error "join suffixes still produced duplicate column names") = Except.ok joinedCols →
      joinedCols.map ColSpec.tags = (lUpd ++ rPrep).map ColSpec.tags := by
    intro lUpd rPrep h
    cases hcol : ((lUpd.map ColSpec.name).any (fun n => (rPrep.map ColSpec.name).contains n))
    · rw [hcol] at h; simp only [Bool.not_false, ↓reduceIte, Except.ok.injEq] at h; subst h; rfl
    · rw [hcol] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases suffixes with
      | none => contradiction
      | some sf =>
        rcases sf with ⟨sL, sR⟩; dsimp only at h
        cases hsf : (sL == sR || (sL.isEmpty && sR.isEmpty))
        · rw [hsf] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hdist : distinctIdents _
          · rw [hdist] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; contradiction
          · rw [hdist] at h; simp only [↓reduceIte, Except.ok.injEq] at h
            subst h; simp only [List.map_append, hrenTags]
        · rw [hsf] at h; simp only [↓reduceIte] at h; contradiction
  cases kind with
  | semi | anti => unfold buildJoinedCols at hb; injection hb with e; exact e.symm
  | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
    unfold buildJoinedCols at hb
    exact hcolStep _ _ hb

private def joinMatchPred (rCols : List ColSpec) (rKeyNames : List Ident) (lkv : List Val) (rRow : TableRow) : Bool :=
  match extractKeyVals rCols rKeyNames rRow with
  | some rkv => valListEq lkv rkv
  | none => false

private theorem joinTableRows_cons_eq (kind : JoinKind) (lCols rCols : List ColSpec)
    (lKeyNames rKeyNames : List Ident) (rKeepIdxs : List (ColSpec × Nat))
    (isLeftOuter : Bool) (nullRightCells : List Val) (rRows : List TableRow)
    (lRow : TableRow) (lRest : List TableRow) :
    joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows (lRow :: lRest) =
      match extractKeyVals lCols lKeyNames lRow with
      | none => none
      | some lkv =>
        match joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows lRest with
        | none => none
        | some restJoined =>
          let matchingR := rRows.filter (joinMatchPred rCols rKeyNames lkv)
          match kind with
          | .semi => if !matchingR.isEmpty then some ({ cells := lRow.cells, groupMeta := none } :: restJoined) else some restJoined
          | .anti => if matchingR.isEmpty then some ({ cells := lRow.cells, groupMeta := none } :: restJoined) else some restJoined
          | _ =>
            if matchingR.isEmpty then
              if isLeftOuter then some ({ cells := lRow.cells ++ nullRightCells, groupMeta := none } :: restJoined) else some restJoined
            else
              match combineJoinMatches isLeftOuter rKeepIdxs lRow.cells matchingR with
              | none => none
              | some curJoined => some (curJoined ++ restJoined) := by
  rw [joinTableRows]
  cases extractKeyVals lCols lKeyNames lRow with
  | none => rfl
  | some lkv =>
    cases joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows lRest with
    | none => rfl
    | some restJoined =>
      dsimp only [bind, Option.bind]
      have hite : ∀ (b : Bool) (t : Option (List TableRow)) (o : Option (List TableRow)),
          (if b = true then t else Option.bind o (fun curJoined => some (curJoined ++ restJoined))) =
          (if b = true then t else match o with | none => none | some curJoined => some (curJoined ++ restJoined)) := by
        intro b t o; cases b <;> cases o <;> rfl
      cases kind with
      | semi | anti => rfl
      | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
        exact hite _ _ _

theorem joinTableRows_perm_right (kind : JoinKind) (lCols rCols : List ColSpec)
    (lKeyNames rKeyNames : List Ident) (rKeepIdxs : List (ColSpec × Nat))
    (isLeftOuter : Bool) (nullRightCells : List Val)
    {rRows1 rRows2 : List TableRow} (hpR : List.Perm rRows1 rRows2) :
    ∀ {lRows out1 out2 : List TableRow},
      joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows1 lRows = some out1 →
      joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows2 lRows = some out2 →
      List.Perm out1 out2
  | [], _, _, h1, h2 => by injection h1 with e1; injection h2 with e2; subst e1; subst e2; exact .nil
  | lRow :: lRest, _, _, h1, h2 => by
    rw [joinTableRows_cons_eq] at h1; rw [joinTableRows_cons_eq] at h2
    cases hlkv : extractKeyVals lCols lKeyNames lRow <;> rw [hlkv] at h1 h2 <;> try contradiction
    rename_i lkv; dsimp only at h1 h2
    cases ht1 : joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows1 lRest <;> rw [ht1] at h1 <;> try contradiction
    cases ht2 : joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows2 lRest <;> rw [ht2] at h2 <;> try contradiction
    dsimp only at h1 h2
    have ih := joinTableRows_perm_right kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells hpR ht1 ht2
    have hpMatch := perm_filter (joinMatchPred rCols rKeyNames lkv) hpR
    have hemEq : (rRows1.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty =
        (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty := by
      have hlen := hpMatch.length_eq
      generalize rRows1.filter (joinMatchPred rCols rKeyNames lkv) = m1,
                 rRows2.filter (joinMatchPred rCols rKeyNames lkv) = m2 at hlen ⊢
      cases m1 <;> cases m2 <;> first | rfl | simp at hlen
    cases kind with
    | semi | anti =>
      dsimp only at h1 h2
      rw [hemEq] at h1
      cases hm : (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty <;>
        (rw [hm] at h1 h2
         try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1 h2
         injection h1 with e1; injection h2 with e2; subst e1; subst e2; first | exact ih | exact .cons _ ih)
    | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
      dsimp only at h1 h2
      rw [hemEq] at h1
      cases hm : (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty
      · rw [hm] at h1 h2; simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
        cases hc1 : combineJoinMatches isLeftOuter rKeepIdxs lRow.cells (rRows1.filter (joinMatchPred rCols rKeyNames lkv)) <;> rw [hc1] at h1 <;> try contradiction
        cases hc2 : combineJoinMatches isLeftOuter rKeepIdxs lRow.cells (rRows2.filter (joinMatchPred rCols rKeyNames lkv)) <;> rw [hc2] at h2 <;> try contradiction
        injection h1 with e1; injection h2 with e2; subst e1; subst e2
        rw [combineJoinMatches_eq_filterMap _ _ _ hc1, combineJoinMatches_eq_filterMap _ _ _ hc2]
        exact (perm_filterMap _ hpMatch).append ih
      · rw [hm] at h1 h2; simp only [↓reduceIte] at h1 h2
        cases isLeftOuter <;> (simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2; injection h1 with e1; injection h2 with e2; subst e1; subst e2; first | exact ih | exact .cons _ ih)

private def joinStepRows (kind : JoinKind) (lCols rCols : List ColSpec)
    (lKeyNames rKeyNames : List Ident) (rKeepIdxs : List (ColSpec × Nat))
    (isLeftOuter : Bool) (nullRightCells : List Val) (rRows : List TableRow)
    (lRow : TableRow) : List TableRow :=
  match extractKeyVals lCols lKeyNames lRow with
  | none => []
  | some lkv =>
    let matchingR := rRows.filter (joinMatchPred rCols rKeyNames lkv)
    match kind with
    | .semi => if !matchingR.isEmpty then [{ cells := lRow.cells, groupMeta := none }] else []
    | .anti => if matchingR.isEmpty then [{ cells := lRow.cells, groupMeta := none }] else []
    | _ =>
      if matchingR.isEmpty then
        if isLeftOuter then [{ cells := lRow.cells ++ nullRightCells, groupMeta := none }] else []
      else
        (combineJoinMatches isLeftOuter rKeepIdxs lRow.cells matchingR).getD []

private theorem joinTableRows_eq_flatMap (kind : JoinKind) (lCols rCols : List ColSpec)
    (lKeyNames rKeyNames : List Ident) (rKeepIdxs : List (ColSpec × Nat))
    (isLeftOuter : Bool) (nullRightCells : List Val) (rRows : List TableRow) :
    ∀ {lRows out : List TableRow},
      joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows lRows = some out →
      out = lRows.flatMap (joinStepRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows)
  | [], _, h => by injection h with e; exact e.symm
  | lRow :: lRest, _, h => by
    rw [joinTableRows_cons_eq] at h
    cases hlkv : extractKeyVals lCols lKeyNames lRow <;> rw [hlkv] at h <;> try contradiction
    rename_i lkv; dsimp only at h
    cases htl : joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows lRest <;> rw [htl] at h <;> try contradiction
    dsimp only at h
    have ih := joinTableRows_eq_flatMap kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows htl
    simp only [List.flatMap_cons, joinStepRows, hlkv, ← ih]
    cases hmEmpty : (rRows.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty
    · cases kind with
      | semi | anti =>
        rw [hmEmpty] at h
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
        injection h with e; subst e; rfl
      | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
        rw [hmEmpty] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hc : combineJoinMatches isLeftOuter rKeepIdxs lRow.cells (rRows.filter (joinMatchPred rCols rKeyNames lkv)) <;> rw [hc] at h <;> try contradiction
        injection h with e; subst e; rfl
    · cases kind with
      | semi | anti =>
        rw [hmEmpty] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        injection h with e; subst e; rfl
      | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
        rw [hmEmpty] at h
        simp only [↓reduceIte] at h ⊢
        cases isLeftOuter <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
          (injection h with e; subst e; rfl)

theorem perm_flatMap {α β : Type} (f : α → List β) :
    ∀ {xs ys : List α}, List.Perm xs ys → List.Perm (xs.flatMap f) (ys.flatMap f)
  | _, _, .nil => .nil
  | x :: _, _ :: _, .cons _ hp => (List.Perm.refl (f x)).append (perm_flatMap f hp)
  | x :: y :: _, _, .swap _ _ rest => by
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact (List.perm_append_comm).append_right (rest.flatMap f)
  | _, _, .trans h1 h2 => (perm_flatMap f h1).trans (perm_flatMap f h2)

theorem joinTableRows_relList {L : TagSet} (kind : JoinKind)
    {lCols rCols joinedCols : List ColSpec} {on : JoinOn} {suffixes : Suffixes}
    {lKeyNames rKeyNames : List Ident} {rKeepIdxs : List (ColSpec × Nat)}
    {rRows1 rRows2 : List TableRow}
    (hb : buildJoinedCols kind lCols rCols on suffixes = .ok joinedCols)
    (hrKeepEq : rKeepIdxs.map Prod.fst = rCols.filter (fun rc => !(match on with | .sameKeys ks => ks | .pairs _ => []).contains rc.name))
    (hallIdx : ∀ p ∈ rKeepIdxs, rCols[p.2]? = some p.1)
    (hlLowKeys : ∀ k ∈ lKeyNames, ∀ c, lCols.find? (fun x => x.name == k) = some c → c.tags.subset L = true)
    (hrLowKeys : ∀ k ∈ rKeyNames, ∀ c, rCols.find? (fun x => x.name == k) = some c → c.tags.subset L = true)
    (hrRel : match kind with
             | .semi | .anti => ∃ rRows1', List.Perm rRows1 rRows1' ∧ RelList (RowEquiv L rCols) rRows1' rRows2
             | _ => RelList (RowEquiv L rCols) rRows1 rRows2) :
    let isLeftOuter := match kind with | .leftOne | .leftManyToOne => true | _ => false
    let nullRightCells := rKeepIdxs.map (fun _ => Val.optNone)
    ∀ {lRows1 lRows2 out1 out2 : List TableRow},
      RelList (RowEquiv L lCols) lRows1 lRows2 →
      joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows1 lRows1 = some out1 →
      joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows2 lRows2 = some out2 →
      RelList (RowEquiv L joinedCols) out1 out2 := by
  intro isLeftOuter nullRightCells lRows1 lRows2 out1 out2 hlRel ho1 ho2
  have htags := buildJoinedCols_tags_eq kind lCols rCols joinedCols on suffixes hb
  induction hlRel generalizing out1 out2 with
  | nil => injection ho1 with e1; injection ho2 with e2; subst e1; subst e2; exact .nil
  | @cons lr1 lr2 _ _ hlr htl ih =>
    rw [joinTableRows_cons_eq] at ho1; rw [joinTableRows_cons_eq] at ho2
    have hlkvEq := extractKeyVals_congr_of_low hlr hlLowKeys
    rw [hlkvEq] at ho1
    cases hlkv : extractKeyVals lCols lKeyNames lr2 <;> rw [hlkv] at ho1 ho2 <;> try contradiction
    rename_i lkv; dsimp only at ho1 ho2
    cases ht1 : joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows1 _ <;> rw [ht1] at ho1 <;> try contradiction
    cases ht2 : joinTableRows kind lCols rCols lKeyNames rKeyNames rKeepIdxs isLeftOuter nullRightCells rRows2 _ <;> rw [ht2] at ho2 <;> try contradiction
    dsimp only at ho1 ho2
    have hrestRel := ih ht1 ht2
    have hmpCongr : ∀ a b, RowEquiv L rCols a b → joinMatchPred rCols rKeyNames lkv a = joinMatchPred rCols rKeyNames lkv b := by
      intro a b hab; unfold joinMatchPred; rw [extractKeyVals_congr_of_low hab hrLowKeys]
    cases kind with
    | semi | anti =>
      dsimp only at hrRel htags ho1 ho2
      rcases hrRel with ⟨rRows1', hpR, hrRel'⟩
      have hpM := perm_filter (joinMatchPred rCols rKeyNames lkv) hpR
      have hrM := hrRel'.filter_congr hmpCongr
      have hemEq : (rRows1.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty =
          (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty := by
        have hlen := hpM.length_eq.trans hrM.length_eq
        generalize rRows1.filter (joinMatchPred rCols rKeyNames lkv) = m1,
                   rRows2.filter (joinMatchPred rCols rKeyNames lkv) = m2 at hlen ⊢
        cases m1 <;> cases m2 <;> first | rfl | simp at hlen
      rw [hemEq] at ho1; rw [htags] at hrestRel ⊢
      cases hm : (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty <;>
        (rw [hm] at ho1 ho2
         try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho1 ho2
         injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
         first | exact hrestRel | exact .cons (cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hlr (fun _ _ h => h)) hrestRel)
    | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
      dsimp only [isLeftOuter] at hrRel htags ho1 ho2 ⊢
      have hrM := hrRel.filter_congr hmpCongr
      have hemEq : (rRows1.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty =
          (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty := by
        have hlen := hrM.length_eq
        generalize rRows1.filter (joinMatchPred rCols rKeyNames lkv) = m1,
                   rRows2.filter (joinMatchPred rCols rKeyNames lkv) = m2 at hlen ⊢
        cases m1 <;> cases m2 <;> first | rfl | simp at hlen
      rw [hemEq] at ho1
      let sks := match on with | .sameKeys ks => ks | .pairs _ => []
      let lUpd := lCols.map (fun lc =>
        if sks.contains lc.name then
          match rCols.find? (fun rc => rc.name == lc.name) with
          | some rc => { lc with tags := lc.tags.union rc.tags, bucketed := false, aggKind := .raw }
          | none => { lc with aggKind := .raw }
        else { lc with aggKind := .raw })
      let rKPrep := rKeepIdxs.map (fun (rc, _) =>
        { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty,
                  bucketed := if isLeftOuter then false else rc.bucketed,
                  aggKind := .raw })
      have hlUpdCells : CellsEquiv L lUpd lr1.cells lr2.cells := by
        apply cellsEquiv_map_tags _ hlr
        intro c _ hsub
        split at hsub
        · cases hfr : rCols.find? (fun rc => rc.name == c.name) with
          | none => rw [hfr] at hsub; exact hsub
          | some rc => rw [hfr] at hsub; dsimp only at hsub; simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hsub; exact hsub.1
        · exact hsub
      have htagsEq : (lUpd ++ rKPrep).map ColSpec.tags = joinedCols.map ColSpec.tags := by
        have hrPrepEq : rKPrep = (rCols.filter (fun rc => !sks.contains rc.name)).map
            (fun rc => { rc with ty := if isLeftOuter then ensureOptionScalar rc.ty else rc.ty,
                                 bucketed := if isLeftOuter then false else rc.bucketed,
                                 aggKind := .raw }) := by
          rw [← hrKeepEq, List.map_map]; rfl
        rw [hrPrepEq]
        exact htags.symm
      cases hm : (rRows2.filter (joinMatchPred rCols rKeyNames lkv)).isEmpty
      · rw [hm] at ho1 ho2; simp only [Bool.false_eq_true, ↓reduceIte] at ho1 ho2
        cases hc1 : combineJoinMatches isLeftOuter rKeepIdxs lr1.cells (rRows1.filter (joinMatchPred rCols rKeyNames lkv)) <;> rw [hc1] at ho1 <;> try contradiction
        cases hc2 : combineJoinMatches isLeftOuter rKeepIdxs lr2.cells (rRows2.filter (joinMatchPred rCols rKeyNames lkv)) <;> rw [hc2] at ho2 <;> try contradiction
        injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
        have hcomb := combineJoinMatches_relList isLeftOuter hlUpdCells hallIdx hrM hc1 hc2
        exact (hcomb.imp (fun _ _ hr => hr.congr_tags htagsEq)).append hrestRel
      · rw [hm] at ho1 ho2; simp only [↓reduceIte] at ho1 ho2
        try simp only [Bool.false_eq_true, ↓reduceIte] at ho1 ho2
        injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
        first
        | exact hrestRel
        | (have hnullEq : CellsEquiv L rKPrep nullRightCells nullRightCells :=
             CellsEquiv.of_all_eq rKPrep nullRightCells (by simp [nullRightCells, rKPrep])
           exact .cons ((hlUpdCells.append hnullEq).congr_tags htagsEq) hrestRel)

/-! ### `Summarize` Non-Interference Helpers -/

theorem extractAllRowsKeyVals_eq_filterMap (cols : List ColSpec) (keyNames : List Ident) :
    ∀ {rs : List TableRow} {kvs : List (List Val)},
      extractAllRowsKeyVals cols keyNames rs = some kvs →
      kvs = rs.filterMap (extractKeyVals cols keyNames) ∧
      (∀ r ∈ rs, ∃ kv, extractKeyVals cols keyNames r = some kv)
  | [], _, h => by injection h with e; subst e; exact ⟨rfl, fun _ hm => nomatch hm⟩
  | r :: rs, _, h => by
    unfold extractAllRowsKeyVals at h; simp only [bind, Option.bind] at h
    cases hk : extractKeyVals cols keyNames r <;> rw [hk] at h <;> try contradiction
    dsimp only at h
    cases ht : extractAllRowsKeyVals cols keyNames rs <;> rw [ht] at h <;> try contradiction
    injection h with e; subst e
    rcases extractAllRowsKeyVals_eq_filterMap cols keyNames ht with ⟨ihEq, ihAll⟩
    refine ⟨by simp [hk, ihEq], ?_⟩
    intro x hx; rcases List.mem_cons.mp hx with rfl | hr; exact ⟨_, hk⟩; exact ihAll x hr

def rowExprOpt (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (cols : List ColSpec) (re : RowExpr) (gr : TableRow) : Option Val :=
  match evalRE cols gr re with
  | .ok cv => some cv
  | _ => none

theorem evalArgOnGroupRows_eq_filterMap
    (evalRE : List ColSpec → TableRow → RowExpr → PrimResult)
    (cols : List ColSpec) (re : RowExpr) :
    ∀ {grs : List TableRow} {cvs : List Val},
      evalArgOnGroupRows evalRE cols re grs = .ok cvs →
      cvs = grs.filterMap (rowExprOpt evalRE cols re) ∧
      (∀ gr ∈ grs, ∃ cv, evalRE cols gr re = .ok cv)
  | [], _, h => by injection h with e; subst e; exact ⟨rfl, fun _ hm => nomatch hm⟩
  | gr :: grs, _, h => by
    unfold evalArgOnGroupRows at h
    cases hc : evalRE cols gr re with
    | stopped _ | outOfFuel | wrong => rw [hc] at h; nomatch h
    | ok cv =>
      rw [hc] at h; dsimp only at h
      cases ht : evalArgOnGroupRows evalRE cols re grs with
      | stopped _ | outOfFuel | wrong => rw [ht] at h; nomatch h
      | ok rest =>
        rw [ht] at h; injection h with e; subst e
        rcases evalArgOnGroupRows_eq_filterMap evalRE cols re ht with ⟨ihEq, ihAll⟩
        refine ⟨by simp [rowExprOpt, hc, ihEq], ?_⟩
        intro x hx; rcases List.mem_cons.mp hx with rfl | hr; exact ⟨cv, hc⟩; exact ihAll x hr

theorem evalAggClean_perm_eq {op : AggOp} {outTy : ScalarTy} {raw1 raw2 : List Val}
    {c1 c2 : Val}
    (hord : op.isOrderSensitive = false)
    (hperm : List.Perm raw1 raw2)
    (hsort : ∀ u ∈ raw1.filterMap (fun v => match v with | .optNone => none | .optSome inner => some inner | other => some other), SortableVal u)
    (hev1 : evalAggClean op outTy raw1 = .ok c1)
    (hev2 : evalAggClean op outTy raw2 = .ok c2) :
    c1 = c2 := by
  have hlenEq : raw1.length = raw2.length := hperm.length_eq
  have hsortEq : ∀ (f : Val → Option Val),
      (∀ v, f v = match v with | .optNone => none | .optSome inner => some inner | other => some other) →
      insertionSortBy valLt (raw1.filterMap f) = insertionSortBy valLt (raw2.filterMap f) := by
    intro f hf
    have hfeq : f = (fun v => match v with | .optNone => none | .optSome inner => some inner | other => some other) := funext hf
    rw [hfeq]
    exact insertionSortBy_perm_eq valLt_irrefl valLt_trans valLt_trichotomy hsort (perm_filterMap _ hperm)
  unfold evalAggClean at hev1 hev2
  dsimp only at hev1 hev2
  cases op with
  | first | last => simp [AggOp.isOrderSensitive] at hord
  | count => rw [hlenEq] at hev1; rw [hev2] at hev1; injection hev1 with e; exact e.symm
  | countDistinct | sum | mean | median | stddev | variance | percentile _ | min | max =>
    rw [hsortEq _ (fun v => by cases v <;> rfl)] at hev1
    rw [hev2] at hev1
    injection hev1 with e; exact e.symm

theorem evalGroupAggItems_ni {fuel' : Nat} {prog : Program} {L : TagSet}
    {env1 env2 : Env} {inTT : TableTy} {gRows1 gRows2 : List TableRow}
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (hcols : ∀ c ∈ inTT.cols, validScalarTy prog c.ty = true)
    (hgWf1 : ∀ gr ∈ gRows1, CellsWf prog gr.cells inTT.cols)
    (hgWf2 : ∀ gr ∈ gRows2, CellsWf prog gr.cells inTT.cols)
    (hgRel : if inTT.orderTags.subset L = true then
               RelList (RowEquiv L inTT.cols) gRows1 gRows2
             else
               ∃ gRows1', List.Perm gRows1 gRows1' ∧ RelList (RowEquiv L inTT.cols) gRows1' gRows2) :
    ∀ {aggs : List AggItem} {aggCols : List ColSpec} {cs1 cs2 : List Val},
      checkAggItemList prog (envToTyEnv env1) inTT aggs = .ok aggCols →
      evalGroupAggItems (evalRowExpr fuel' prog env1) inTT.cols gRows1 (List.zip aggs aggCols) = .ok cs1 →
      evalGroupAggItems (evalRowExpr fuel' prog env2) inTT.cols gRows2 (List.zip aggs aggCols) = .ok cs2 →
      CellsEquiv L aggCols cs1 cs2
  | [], _, _, _, hchk, hev1, hev2 => by
    unfold checkAggItemList at hchk; injection hchk with e; subst e
    unfold evalGroupAggItems at hev1 hev2
    injection hev1 with e1; injection hev2 with e2; subst e1; subst e2; exact .nil
  | aItem :: restAggs, _, _, _, hchk, hev1, hev2 => by
    unfold checkAggItemList at hchk; simp only [bind, Except.bind] at hchk
    cases hhd : checkAggItem prog (envToTyEnv env1) inTT aItem <;> rw [hhd] at hchk <;> try contradiction
    rename_i aSpec; dsimp only at hchk
    cases htl : checkAggItemList prog (envToTyEnv env1) inTT restAggs <;> rw [htl] at hchk <;> try contradiction
    rename_i tlSpecs; injection hchk with e; subst e
    rw [List.zip_cons_cons] at hev1 hev2
    unfold evalGroupAggItems at hev1 hev2; dsimp only at hev1 hev2
    have hd : progDatasSortableForNI prog L = true := by
      simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
    have hgPerm : ∃ gRows1', List.Perm gRows1 gRows1' ∧ RelList (RowEquiv L inTT.cols) gRows1' gRows2 := by
      cases hord : inTT.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hgRel
      · exact hgRel
      · exact ⟨gRows1, .refl _, hgRel⟩
    rcases hgPerm with ⟨gRows1', hpG, hrG⟩
    have hgLenEq : gRows1.length = gRows2.length := hpG.length_eq.trans hrG.length_eq
    unfold checkAggItem at hhd
    cases harg : aItem.arg with
    | none =>
      rw [harg] at hhd hev1 hev2; dsimp only at hev1 hev2
      cases hac1 : evalAggClean aItem.op aSpec.ty (gRows1.map (fun _ => Val.unit)) <;> rw [hac1] at hev1 <;> try contradiction
      cases hac2 : evalAggClean aItem.op aSpec.ty (gRows2.map (fun _ => Val.unit)) <;> rw [hac2] at hev2 <;> try contradiction
      dsimp only at hev1 hev2
      cases hrest1 : evalGroupAggItems (evalRowExpr fuel' prog env1) inTT.cols gRows1 (List.zip restAggs tlSpecs) <;> rw [hrest1] at hev1 <;> try contradiction
      cases hrest2 : evalGroupAggItems (evalRowExpr fuel' prog env2) inTT.cols gRows2 (List.zip restAggs tlSpecs) <;> rw [hrest2] at hev2 <;> try contradiction
      injection hev1 with e1; injection hev2 with e2; subst e1; subst e2
      refine .cons (fun _ => ?_)
        (evalGroupAggItems_ni hprog hsafeProg henv hcols hgWf1 hgWf2 hgRel htl hrest1 hrest2)
      have hmapEq : gRows1.map (fun _ => Val.unit) = gRows2.map (fun _ => Val.unit) := by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < gRows1.length
        · have hi2 : i < gRows2.length := hgLenEq ▸ hi
          simp [hi, hi2]
        · have hi2 : ¬ i < gRows2.length := hgLenEq ▸ hi
          simp [List.getElem?_eq_none (Nat.le_of_not_lt hi), List.getElem?_eq_none (Nat.le_of_not_lt hi2)]
      rw [hmapEq, hac2] at hac1; injection hac1 with e; exact e.symm
    | some re =>
      rw [harg] at hhd hev1 hev2; dsimp only at hev1 hev2
      cases hv1 : evalArgOnGroupRows (evalRowExpr fuel' prog env1) inTT.cols re gRows1 <;> rw [hv1] at hev1 <;> try contradiction
      cases hv2 : evalArgOnGroupRows (evalRowExpr fuel' prog env2) inTT.cols re gRows2 <;> rw [hv2] at hev2 <;> try contradiction
      dsimp only at hev1 hev2
      cases hac1 : evalAggClean aItem.op aSpec.ty _ <;> rw [hac1] at hev1 <;> try contradiction
      cases hac2 : evalAggClean aItem.op aSpec.ty _ <;> rw [hac2] at hev2 <;> try contradiction
      dsimp only at hev1 hev2
      cases hrest1 : evalGroupAggItems (evalRowExpr fuel' prog env1) inTT.cols gRows1 (List.zip restAggs tlSpecs) <;> rw [hrest1] at hev1 <;> try contradiction
      cases hrest2 : evalGroupAggItems (evalRowExpr fuel' prog env2) inTT.cols gRows2 (List.zip restAggs tlSpecs) <;> rw [hrest2] at hev2 <;> try contradiction
      injection hev1 with e1; injection hev2 with e2; subst e1; subst e2
      refine .cons (fun hlow => ?_)
        (evalGroupAggItems_ni hprog hsafeProg henv hcols hgWf1 hgWf2 hgRel htl hrest1 hrest2)
      have hargProps : ∃ sTy rTags,
          checkRowExpr prog (envToTyEnv env1) inTT.cols re = .ok (sTy, rTags) ∧
          aSpec.tags = rTags.union (inTT.rowTags.union (if aItem.op.isOrderSensitive then inTT.orderTags else TagSet.empty)) := by
        cases hre : checkRowExpr prog (envToTyEnv env1) inTT.cols re with
        | error _ =>
          cases hop : aItem.op <;> simp only [hop, bind, Except.bind, hre] at hhd <;> contradiction
        | ok pair =>
          rcases pair with ⟨sTy, rTags⟩
          cases hop : aItem.op <;> simp only [hop, bind, Except.bind, hre] at hhd <;> try contradiction
          all_goals (
            try dsimp only at hhd
            repeat (first | contradiction | (injection hhd with e; subst e; exact ⟨sTy, rTags, rfl, by simp [AggOp.isOrderSensitive]⟩) | split at hhd)
          )
      rcases hargProps with ⟨sTy, rTags, hreChk, htagsEq⟩
      rw [htagsEq] at hlow
      simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hlow
      rcases evalArgOnGroupRows_eq_filterMap _ _ _ hv1 with ⟨hfm1, hall1⟩
      rcases evalArgOnGroupRows_eq_filterMap _ _ _ hv2 with ⟨hfm2, hall2⟩
      let f1 := rowExprOpt (evalRowExpr fuel' prog env1) inTT.cols re
      let f2 := rowExprOpt (evalRowExpr fuel' prog env2) inTT.cols re
      have hfCongr : ∀ gr1 gr2, gr1 ∈ gRows1 → gr2 ∈ gRows2 → RowEquiv L inTT.cols gr1 gr2 → f1 gr1 = f2 gr2 := by
        intro gr1 gr2 hm1 hm2 hr
        rcases hall1 gr1 hm1 with ⟨c1, hc1⟩
        rcases hall2 gr2 hm2 with ⟨c2, hc2⟩
        have hvEq := evalRowExpr_low_eq hprog hsafeProg henv hcols (hgWf1 gr1 hm1) (hgWf2 gr2 hm2) hr hreChk hlow.1 hc1 hc2
        dsimp only [f1, f2, rowExprOpt]; rw [hc1, hc2, hvEq]
      cases hos : aItem.op.isOrderSensitive
      · have hpVals : List.Perm (gRows1.filterMap f1) (gRows2.filterMap f2) := by
          have heq' : gRows1'.filterMap f1 = gRows2.filterMap f2 :=
            hrG.with_mem.filterMap_congr (fun a b ⟨ha, hb, hr⟩ => hfCongr a b (hpG.symm.subset ha) hb hr)
          exact heq' ▸ perm_filterMap f1 hpG
        have hrawWf : ∀ v ∈ gRows1.filterMap f1, ValWf prog v sTy.toTy := by
          intro v hv; rw [List.mem_filterMap] at hv; rcases hv with ⟨gr, hgr, hfg⟩
          rcases hall1 gr hgr with ⟨cv, hcv⟩
          dsimp only [f1, rowExprOpt] at hfg; rw [hcv] at hfg; injection hfg with ev; subst ev
          have hs := (eval_fuel_sound prog fuel').1 hprog env1 inTT.cols gr re sTy rTags henv.wf_left hcols (hgWf1 gr hgr) hreChk
          rw [hcv] at hs; cases hs; assumption
        have hnnWf := nonNull_wf (checkRowExpr_validScalarTy hcols hreChk) hrawWf
        have hnnSort : ∀ u ∈ (gRows1.filterMap f1).filterMap (fun v => match v with | .optNone => none | .optSome inner => some inner | other => some other), SortableVal u :=
          fun u hu => valWf_sortable hd (hnnWf u hu) (ScalarTy.isSortable_toTy _)
        exact evalAggClean_perm_eq hos (hfm1 ▸ hfm2 ▸ hpVals) (hfm1 ▸ hnnSort) hac1 hac2
      · simp only [hos, ↓reduceIte] at hlow
        simp only [hlow.2.2, ↓reduceIte] at hgRel
        have heqVals : gRows1.filterMap f1 = gRows2.filterMap f2 :=
          hgRel.with_mem.filterMap_congr (fun a b ⟨ha, hb, hr⟩ => hfCongr a b ha hb hr)
        rw [hfm1] at hac1; rw [hfm2] at hac2
        dsimp only [f1, f2] at heqVals
        rw [heqVals, hac2] at hac1; injection hac1 with e; exact e.symm

theorem evalSummarizeGroups_ni {fuel' : Nat} {prog : Program} {L : TagSet}
    {env1 env2 : Env} {tv1 tv2 : TableVal} {inTT : TableTy}
    {groupKeys : List Ident} {distinctKey : Option Ident}
    {dkIdx1? dkIdx2? : Option (Nat × ColSpec)}
    {aggs : List AggItem} {keyCols aggCols outCols : List ColSpec}
    {w1 w2 w1' w2' : World}
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (ht : TableEquiv prog L tv1 tv2 inTT)
    (hrLow : inTT.rowTags.subset L = true)
    (hlowGK : ∀ k ∈ groupKeys, ∀ c, inTT.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true)
    (hdk : match distinctKey, dkIdx1?, dkIdx2? with
      | none, _, _ => True
      | some _, some (i1, c1), some (i2, _) => i1 = i2 ∧ inTT.cols[i1]? = some c1 ∧ c1.tags.subset L = true
      | some _, none, none => True
      | _, _, _ => False)
    (haggChk : checkAggItemList prog (envToTyEnv env1) inTT aggs = .ok aggCols)
    (houtCols : outCols = keyCols ++ aggCols) :
    ∀ {gks : List (List Val)} {resTV1 resTV2 : TableVal},
      (∀ gk ∈ gks, gk.length = keyCols.length) →
      evalSummarizeGroups (evalRowExpr fuel' prog env1) tv1 groupKeys distinctKey dkIdx1? aggs aggCols outCols w1 gks = .ok (.table resTV1) w1' →
      evalSummarizeGroups (evalRowExpr fuel' prog env2) tv2 groupKeys distinctKey dkIdx2? aggs aggCols outCols w2 gks = .ok (.table resTV2) w2' →
      RelList (fun r1 r2 => RowEquiv L outCols r1 r2 ∧ r1.groupMeta = r2.groupMeta) resTV1.rows resTV2.rows
  | [], _, _, _, hev1, hev2 => by
    unfold evalSummarizeGroups at hev1 hev2
    injection hev1 with ev1 _; injection hev2 with ev2 _
    injection ev1 with et1; injection ev2 with et2; subst et1; subst et2; exact .nil
  | gKey :: gks, _, _, hgksLen, hev1, hev2 => by
    unfold evalSummarizeGroups at hev1 hev2; dsimp only at hev1 hev2
    rcases ht.cols_eq with ⟨hc1, hc2⟩
    cases ht.wf1 with | table _ hsch hrWf1 =>
    cases ht.wf2 with | table _ _ hrWf2 =>
    have hcols := fun c hc => (tableSchemaWf_cols_props hsch).2 c hc |>.1
    have hd : progDatasSortableForNI prog L = true := by
      simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
    cases hga1 : evalGroupAggItems (evalRowExpr fuel' prog env1) tv1.cols _ (List.zip aggs aggCols) <;>
      rw [hga1] at hev1 <;> try contradiction
    cases hga2 : evalGroupAggItems (evalRowExpr fuel' prog env2) tv2.cols _ (List.zip aggs aggCols) <;>
      rw [hga2] at hev2 <;> try contradiction
    dsimp only at hev1 hev2
    cases htl1 : evalSummarizeGroups (evalRowExpr fuel' prog env1) tv1 groupKeys distinctKey dkIdx1? aggs aggCols outCols w1 gks <;>
      rw [htl1] at hev1 <;> try contradiction
    cases htl2 : evalSummarizeGroups (evalRowExpr fuel' prog env2) tv2 groupKeys distinctKey dkIdx2? aggs aggCols outCols w2 gks <;>
      rw [htl2] at hev2 <;> try contradiction
    rename_i rv1 _ rv2 _
    have hrv1 : ∃ restTV1, rv1 = .table restTV1 := by
      cases rv1 with | table restTV1 => exact ⟨restTV1, rfl⟩ | _ => dsimp only at hev1; injection hev1 with hv _; cases hv
    have hrv2 : ∃ restTV2, rv2 = .table restTV2 := by
      cases rv2 with | table restTV2 => exact ⟨restTV2, rfl⟩ | _ => dsimp only at hev2; injection hev2 with hv _; cases hv
    rcases hrv1 with ⟨restTV1, rfl⟩; rcases hrv2 with ⟨restTV2, rfl⟩
    dsimp only at hev1 hev2
    injection hev1 with ev1 _; injection hev2 with ev2 _
    injection ev1 with et1; injection ev2 with et2; subst et1; subst et2
    rw [hc1] at hga1; rw [hc2] at hga2
    have hgRel :
        if inTT.orderTags.subset L = true then
          RelList (RowEquiv L inTT.cols)
            (if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false))
            (if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false))
        else
          ∃ gRows1', List.Perm
            (if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false))
            gRows1' ∧
            RelList (RowEquiv L inTT.cols) gRows1'
              (if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)) := by
      cases groupKeys.isEmpty
      · have hpCongr : ∀ a b, RowEquiv L inTT.cols a b →
            (match extractKeyVals inTT.cols groupKeys a with | some kv => valListEq kv gKey | none => false) =
            (match extractKeyVals inTT.cols groupKeys b with | some kv => valListEq kv gKey | none => false) := by
          intro a b hab; rw [extractKeyVals_congr_of_low hab hlowGK]
        have hlr := ht.lowRows hrLow
        cases hord : inTT.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr ⊢
        · rcases hlr with ⟨rows1', hp, hr'⟩
          exact ⟨rows1'.filter _, perm_filter _ hp, hr'.filter_congr hpCongr⟩
        · exact hlr.filter_congr hpCongr
      · exact ht.lowRows hrLow
    have hgPerm : ∃ gRows1', List.Perm
        (if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false))
        gRows1' ∧
        RelList (RowEquiv L inTT.cols) gRows1'
          (if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)) := by
      cases hord : inTT.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hgRel
      · exact hgRel
      · exact ⟨_, .refl _, hgRel⟩
    have hgWf1 : ∀ gr ∈ (if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)), CellsWf prog gr.cells inTT.cols := by
      intro gr hgr; cases hgk : groupKeys.isEmpty <;> simp only [hgk, Bool.false_eq_true, ↓reduceIte] at hgr
      · exact hrWf1.to_forall gr (List.mem_filter.mp hgr).1
      · exact hrWf1.to_forall gr hgr
    have hgWf2 : ∀ gr ∈ (if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)), CellsWf prog gr.cells inTT.cols := by
      intro gr hgr; cases hgk : groupKeys.isEmpty <;> simp only [hgk, Bool.false_eq_true, ↓reduceIte] at hgr
      · exact hrWf2.to_forall gr (List.mem_filter.mp hgr).1
      · exact hrWf2.to_forall gr hgr
    have haggCells := evalGroupAggItems_ni hprog hsafeProg henv hcols hgWf1 hgWf2 hgRel haggChk hga1 hga2
    have hkCells := CellsEquiv.of_all_eq (L := L) keyCols gKey (hgksLen gKey (.head _))
    refine .cons ⟨houtCols ▸ hkCells.append haggCells, ?_⟩
      (evalSummarizeGroups_ni hprog hsafeProg henv ht hrLow hlowGK hdk haggChk houtCols
        (fun gk hgk => hgksLen gk (.tail _ hgk)) htl1 htl2)
    dsimp only
    rw [hc1, hc2]
    rcases hgPerm with ⟨gRows1', hpG, hrG⟩
    have hlenG : (if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)).length =
        (if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)).length :=
      hpG.length_eq.trans hrG.length_eq
    congr 1; congr 1
    cases distinctKey with
    | none => rfl
    | some dk =>
      cases dkIdx1? with
      | none => cases dkIdx2? with | none => rfl | some _ => nomatch hdk
      | some p1 =>
        rcases p1 with ⟨i1, c1⟩
        cases dkIdx2? with
        | none => nomatch hdk
        | some p2 =>
          rcases p2 with ⟨i2, c2⟩
          rcases hdk with ⟨rfl, hgC1, hc1Low⟩
          dsimp only
          congr 1; congr 1; congr 1
          let fD : TableRow → Option Val := fun r =>
            match (r.cells[i1]? : Option Val) with
            | some Val.optNone | none => none
            | some (Val.optSome inner) => some inner
            | some v => some v
          have hpD : List.Perm ((if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)).filterMap fD)
              ((if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)).filterMap fD) := by
            have hfmEq : gRows1'.filterMap fD = (if groupKeys.isEmpty then tv2.rows else tv2.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)).filterMap fD :=
              hrG.filterMap_congr (fun a b hab => by dsimp only [fD]; rw [hab.getElem?_eq hgC1 hc1Low])
            exact hfmEq ▸ perm_filterMap fD hpG
          have hsD : ∀ u ∈ (if groupKeys.isEmpty then tv1.rows else tv1.rows.filter (fun r => match extractKeyVals inTT.cols groupKeys r with | some kv => valListEq kv gKey | none => false)).filterMap fD, SortableVal u := by
            intro u hu
            rw [List.mem_filterMap] at hu; rcases hu with ⟨gr, hgr, hfu⟩
            rcases (hgWf1 gr hgr).getElem?_wf hgC1 with ⟨cv, hgc, hcvWf⟩
            dsimp only [fD] at hfu; rw [hgc] at hfu
            cases hcv : cv <;> simp only [hcv] at hfu <;> try contradiction
            case optSome inner =>
              injection hfu with eu; subst eu
              cases hcty : c1.ty <;> rw [hcv, hcty] at hcvWf <;> cases hcvWf
              rename_i hi
              exact valWf_sortable hd hi (ScalarTy.isSortable_toTy _)
            all_goals (injection hfu with eu; subst eu; exact valWf_sortable hd (hcv ▸ hcvWf) (ScalarTy.isSortable_toTy _))
          exact insertionSortBy_perm_eq valLt_irrefl valLt_trans valLt_trichotomy hsD hpD

/-! ### `Window` Non-Interference Helpers -/

private theorem buildWindowRows_untouched_wf {prog : Program} {cols : List ColSpec} (over : List Ident)
    (sortedIdx : List (TableRow × Nat)) (ex? : Option (Nat × ColSpec))
    (comp : List TableRow → Nat → Option Val) (itemName : Ident)
    (hexSpec : match ex? with
               | some (idx, c) => cols[idx]? = some c ∧ c.name = itemName
               | none => True) :
    ∀ {k : Nat} {rows newRows : List TableRow},
      (∀ r ∈ rows, CellsWf prog r.cells cols) →
      evalWindowOnTable.buildWindowRows cols over sortedIdx ex? comp (rows.zipIdx k) = some newRows →
      RelList (fun r nr =>
        nr.cells.length = (if ex?.isSome then cols.length else cols.length + 1) ∧
        ∀ (i : Nat) (c : ColSpec), cols[i]? = some c → c.name ≠ itemName → nr.cells[i]? = r.cells[i]?) rows newRows
  | _, [], _, _, h => by injection h with e; subst e; exact .nil
  | k, row :: rest, _, hrsWf, h => by
    unfold evalWindowOnTable.buildWindowRows at h; simp only [List.zipIdx_cons, bind, Option.bind] at h
    cases hmk : extractKeyVals cols over row <;> rw [hmk] at h <;> try contradiction
    dsimp only at h
    cases hwv : comp _ _ <;> rw [hwv] at h <;> try contradiction
    dsimp only at h
    cases htl : evalWindowOnTable.buildWindowRows cols over sortedIdx ex? comp (rest.zipIdx (k + 1)) <;> rw [htl] at h <;> try contradiction
    injection h with e; subst e
    have hlenRow := (hrsWf row (.head _)).length_eq
    refine .cons ?_ (buildWindowRows_untouched_wf over sortedIdx ex? comp itemName hexSpec (fun r hr => hrsWf r (.tail _ hr)) htl)
    cases ex? with
    | none =>
      refine ⟨by simp [hlenRow], fun i c hi _ => ?_⟩
      have hlt : i < row.cells.length := hlenRow ▸ (List.getElem?_eq_some_iff.mp hi).1
      exact List.getElem?_append_left hlt
    | some pair =>
      rcases pair with ⟨idx, exC⟩
      rcases hexSpec with ⟨hexGet, hexName⟩
      refine ⟨by simp [hlenRow], fun i c hi hne => ?_⟩
      have hneIdx : idx ≠ i := by
        intro heq; subst heq; rw [hexGet] at hi; injection hi with ec; subst ec; exact hne hexName
      exact List.getElem?_set_ne hneIdx

private theorem cellsEquiv_from_getElem? {L : TagSet} :
    ∀ {cols : List ColSpec} {xs1 xs2 : List Val},
      xs1.length = cols.length →
      xs2.length = cols.length →
      (∀ (i : Nat) (c : ColSpec), cols[i]? = some c → c.tags.subset L = true → xs1[i]? = xs2[i]?) →
      CellsEquiv L cols xs1 xs2
  | [], [], [], _, _, _ => .nil
  | c :: cs, v1 :: vs1, v2 :: vs2, h1, h2, hget => by
    refine .cons (fun hlow => ?_)
      (cellsEquiv_from_getElem? (Nat.succ.inj h1) (Nat.succ.inj h2)
        (fun i d hi hl => hget (i + 1) d hi hl))
    have h0 := hget 0 c rfl hlow
    injection h0

private theorem lookupColIdx?_congr_names {c1 c2 : List ColSpec} (name : Ident)
    (hnames : c1.map ColSpec.name = c2.map ColSpec.name)
    (htys : c1.map ColSpec.ty = c2.map ColSpec.ty) :
    (lookupColIdx? c1 name).map Prod.fst = (lookupColIdx? c2 name).map Prod.fst ∧
    (lookupColIdx? c1 name).map (fun p => p.2.ty) = (lookupColIdx? c2 name).map (fun p => p.2.ty) := by
  have aux : ∀ (k : Nat) (l1 l2 : List ColSpec),
      l1.map ColSpec.name = l2.map ColSpec.name →
      l1.map ColSpec.ty = l2.map ColSpec.ty →
      (lookupColIdx?.go name k l1).map Prod.fst = (lookupColIdx?.go name k l2).map Prod.fst ∧
      (lookupColIdx?.go name k l1).map (fun p => p.2.ty) = (lookupColIdx?.go name k l2).map (fun p => p.2.ty) := by
    intro k l1 l2 hn ht
    induction l1 generalizing l2 k with
    | nil => cases l2 <;> simp at hn ⊢
    | cons a1 r1 ih =>
      cases l2 with
      | nil => simp at hn
      | cons a2 r2 =>
        simp only [List.map_cons, List.cons.injEq] at hn ht
        unfold lookupColIdx?.go
        rw [hn.1]
        cases (a2.name == name)
        · exact ih (k + 1) r2 hn.2 ht.2
        · simp [ht.1]
  exact aux 0 c1 c2 hnames htys

private theorem evalWindowComputeCell_congr {L : TagSet}
    {specCols c1 c2 : List ColSpec} {item : WindowItem} {targetTy : ScalarTy}
    {part1 part2 : List TableRow} (pos : Nat)
    (hn1 : c1.map ColSpec.name = specCols.map ColSpec.name)
    (ht1 : c1.map ColSpec.ty = specCols.map ColSpec.ty)
    (hn2 : c2.map ColSpec.name = specCols.map ColSpec.name)
    (ht2 : c2.map ColSpec.ty = specCols.map ColSpec.ty)
    (hpart : RelList (RowEquiv L specCols) part1 part2)
    (hfnColLow : ∀ col, (item.fn = .rank col ∨ (∃ o, item.fn = .lag col o) ∨ (∃ o, item.fn = .lead col o) ∨
      item.fn = .runningSum col ∨ (∃ w, item.fn = .rollingMean col w)) →
      ∀ c, specCols.find? (fun x => x.name == col) = some c → c.tags.subset L = true) :
    evalWindowComputeCell c1 item targetTy part1 pos = evalWindowComputeCell c2 item targetTy part2 pos := by
  have hcolCellsEq : ∀ (col : Ident) (idx : Nat) (sc : ColSpec),
      lookupColIdx? specCols col = some (idx, sc) → sc.tags.subset L = true →
      part1.map (fun r => r.cells[idx]?) = part2.map (fun r => r.cells[idx]?) := by
    intro col idx sc hlk hlow
    rcases lookupColIdx?_props hlk with ⟨hgetSc, _⟩
    clear hn1 ht1 hn2 ht2 hfnColLow
    induction hpart with
    | nil => rfl
    | cons hr htl ih => simp [hr.getElem?_eq hgetSc hlow, ih]
  have hpartGetEq : ∀ (idx : Nat) (sc : ColSpec) (k : Nat),
      specCols[idx]? = some sc → sc.tags.subset L = true →
      (part1[k]?).bind (fun r => r.cells[idx]?) = (part2[k]?).bind (fun r => r.cells[idx]?) := by
    intro idx sc k hgetSc hlow
    clear hn1 ht1 hn2 ht2 hfnColLow hcolCellsEq
    induction hpart generalizing k with
    | nil => simp
    | cons hr htl ih =>
      cases k
      · simp [hr.getElem?_eq hgetSc hlow]
      · simp [ih _]
  unfold evalWindowComputeCell
  cases hfn : item.fn
  case rowNumber => rfl
  case rank col =>
    rcases lookupColIdx?_congr_names col hn1 ht1 with ⟨hl1, _⟩
    rcases lookupColIdx?_congr_names col hn2 ht2 with ⟨hl2, _⟩
    cases hlkS : lookupColIdx? specCols col with
    | none =>
      rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col <;> rw [l1] at hl1 <;> try contradiction
      cases l2 : lookupColIdx? c2 col <;> rw [l2] at hl2 <;> try contradiction
      simp [l1, l2, bind, Option.bind]
    | some pS =>
      rcases pS with ⟨idx, sc⟩; rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col with
      | none => rw [l1] at hl1; contradiction
      | some p1 =>
        cases l2 : lookupColIdx? c2 col with
        | none => rw [l2] at hl2; contradiction
        | some p2 =>
          rw [l1] at hl1; rw [l2] at hl2
          rcases p1 with ⟨i1, _⟩; rcases p2 with ⟨i2, _⟩
          simp only [Option.map_some, Option.some.injEq] at hl1 hl2; subst i1; subst i2
          simp only [l1, l2, bind, Option.bind]
          have hfindSc : specCols.find? (fun x => x.name == col) = some sc := by
            rw [← lookupColIdx?_snd_eq_find?, hlkS]; rfl
          have hlow := hfnColLow col (Or.inl hfn) sc hfindSc
          rcases lookupColIdx?_props hlkS with ⟨hgetSc, _⟩
          have hcurEq := hpartGetEq idx sc pos hgetSc hlow
          cases hp1 : part1[pos]? <;> cases hp2 : part2[pos]?
          · rfl
          · exfalso; have := hpart.length_eq; have hlt := (List.getElem?_eq_some_iff.mp hp2).1
            have hn := List.getElem?_eq_none_iff.mp hp1; omega
          · exfalso; have := hpart.length_eq; have hlt := (List.getElem?_eq_some_iff.mp hp1).1
            have hn := List.getElem?_eq_none_iff.mp hp2; omega
          · rename_i curRow1 curRow2
            rw [hp1, hp2] at hcurEq; dsimp only [Option.bind] at hcurEq ⊢
            rw [hcurEq]
            cases curRow2.cells[idx]? with
            | none => rfl
            | some curVal =>
              dsimp only
              have hflt := (hpart.take pos).filter_congr
                (p1 := fun pr => match pr.cells[idx]? with | some pv => valLt pv curVal | none => false)
                (p2 := fun pr => match pr.cells[idx]? with | some pv => valLt pv curVal | none => false)
                (fun _ _ hr => by rw [hr.getElem?_eq hgetSc hlow])
              exact congrArg (fun n => some (Val.int (clampInt64Nat (n + 1)))) hflt.length_eq
  case lag col offset =>
    rcases lookupColIdx?_congr_names col hn1 ht1 with ⟨hl1, hty1⟩
    rcases lookupColIdx?_congr_names col hn2 ht2 with ⟨hl2, hty2⟩
    cases hlkS : lookupColIdx? specCols col with
    | none =>
      rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col <;> rw [l1] at hl1 <;> try contradiction
      cases l2 : lookupColIdx? c2 col <;> rw [l2] at hl2 <;> try contradiction
      simp [l1, l2, bind, Option.bind]
    | some pS =>
      rcases pS with ⟨idx, sc⟩; rw [hlkS] at hl1 hl2 hty1 hty2
      cases l1 : lookupColIdx? c1 col with
      | none => rw [l1] at hl1; contradiction
      | some p1 =>
        cases l2 : lookupColIdx? c2 col with
        | none => rw [l2] at hl2; contradiction
        | some p2 =>
          rw [l1] at hl1 hty1; rw [l2] at hl2 hty2
          rcases p1 with ⟨i1, sc1⟩; rcases p2 with ⟨i2, sc2⟩
          simp only [Option.map_some, Option.some.injEq] at hl1 hl2; subst i1; subst i2
          simp only [Option.map_some, Option.some.injEq] at hty1 hty2
          simp only [l1, l2, bind, Option.bind]
          split; rfl
          have hfindSc : specCols.find? (fun x => x.name == col) = some sc := by
            rw [← lookupColIdx?_snd_eq_find?, hlkS]; rfl
          have hlow := hfnColLow col (Or.inr (Or.inl ⟨offset, hfn⟩)) sc hfindSc
          rcases lookupColIdx?_props hlkS with ⟨hgetSc, _⟩
          have hprevEq := hpartGetEq idx sc (pos - offset) hgetSc hlow
          rw [hty1, hty2]
          cases hp1 : part1[pos - offset]? <;> cases hp2 : part2[pos - offset]? <;>
            rw [hp1, hp2] at hprevEq <;> dsimp only [Option.bind] at hprevEq ⊢
          · exfalso; have := hpart.length_eq; have hlt := (List.getElem?_eq_some_iff.mp hp2).1
            have hn := List.getElem?_eq_none_iff.mp hp1; omega
          · exfalso; have := hpart.length_eq; have hlt := (List.getElem?_eq_some_iff.mp hp1).1
            have hn := List.getElem?_eq_none_iff.mp hp2; omega
          · rw [hprevEq]
  case lead col offset =>
    rcases lookupColIdx?_congr_names col hn1 ht1 with ⟨hl1, hty1⟩
    rcases lookupColIdx?_congr_names col hn2 ht2 with ⟨hl2, hty2⟩
    cases hlkS : lookupColIdx? specCols col with
    | none =>
      rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col <;> rw [l1] at hl1 <;> try contradiction
      cases l2 : lookupColIdx? c2 col <;> rw [l2] at hl2 <;> try contradiction
      simp [l1, l2, bind, Option.bind]
    | some pS =>
      rcases pS with ⟨idx, sc⟩; rw [hlkS] at hl1 hl2 hty1 hty2
      cases l1 : lookupColIdx? c1 col with
      | none => rw [l1] at hl1; contradiction
      | some p1 =>
        cases l2 : lookupColIdx? c2 col with
        | none => rw [l2] at hl2; contradiction
        | some p2 =>
          rw [l1] at hl1 hty1; rw [l2] at hl2 hty2
          rcases p1 with ⟨i1, sc1⟩; rcases p2 with ⟨i2, sc2⟩
          simp only [Option.map_some, Option.some.injEq] at hl1 hl2; subst i1; subst i2
          simp only [Option.map_some, Option.some.injEq] at hty1 hty2
          simp only [l1, l2, bind, Option.bind]
          have hfindSc : specCols.find? (fun x => x.name == col) = some sc := by
            rw [← lookupColIdx?_snd_eq_find?, hlkS]; rfl
          have hlow := hfnColLow col (Or.inr (Or.inr (Or.inl ⟨offset, hfn⟩))) sc hfindSc
          rcases lookupColIdx?_props hlkS with ⟨hgetSc, _⟩
          have hnextEq := hpartGetEq idx sc (pos + offset) hgetSc hlow
          rw [hty1, hty2]
          cases hp1 : part1[pos + offset]? <;> cases hp2 : part2[pos + offset]? <;>
            rw [hp1, hp2] at hnextEq <;> dsimp only [Option.bind] at hnextEq ⊢
          · exfalso; have := hpart.length_eq; have hlt := (List.getElem?_eq_some_iff.mp hp2).1
            have hn := List.getElem?_eq_none_iff.mp hp1; omega
          · exfalso; have := hpart.length_eq; have hlt := (List.getElem?_eq_some_iff.mp hp1).1
            have hn := List.getElem?_eq_none_iff.mp hp2; omega
          · rw [hnextEq]
  case runningSum col =>
    rcases lookupColIdx?_congr_names col hn1 ht1 with ⟨hl1, _⟩
    rcases lookupColIdx?_congr_names col hn2 ht2 with ⟨hl2, _⟩
    cases hlkS : lookupColIdx? specCols col with
    | none =>
      rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col <;> rw [l1] at hl1 <;> try contradiction
      cases l2 : lookupColIdx? c2 col <;> rw [l2] at hl2 <;> try contradiction
      simp [l1, l2, bind, Option.bind]
    | some pS =>
      rcases pS with ⟨idx, sc⟩; rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col with
      | none => rw [l1] at hl1; contradiction
      | some p1 =>
        cases l2 : lookupColIdx? c2 col with
        | none => rw [l2] at hl2; contradiction
        | some p2 =>
          rw [l1] at hl1; rw [l2] at hl2
          rcases p1 with ⟨i1, _⟩; rcases p2 with ⟨i2, _⟩
          simp only [Option.map_some, Option.some.injEq] at hl1 hl2; subst i1; subst i2
          simp only [l1, l2, bind, Option.bind]
          have hfindSc : specCols.find? (fun x => x.name == col) = some sc := by
            rw [← lookupColIdx?_snd_eq_find?, hlkS]; rfl
          have hlow := hfnColLow col (Or.inr (Or.inr (Or.inr (Or.inl hfn)))) sc hfindSc
          have hpre := (hpart.take (pos + 1)).filterMap_congr (f := fun r => r.cells[idx]?) (g := fun r => r.cells[idx]?)
            (fun _ _ hr => hr.getElem?_eq (lookupColIdx?_props hlkS).1 hlow)
          rw [hpre]
  case rollingMean col wSz =>
    rcases lookupColIdx?_congr_names col hn1 ht1 with ⟨hl1, _⟩
    rcases lookupColIdx?_congr_names col hn2 ht2 with ⟨hl2, _⟩
    cases hlkS : lookupColIdx? specCols col with
    | none =>
      rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col <;> rw [l1] at hl1 <;> try contradiction
      cases l2 : lookupColIdx? c2 col <;> rw [l2] at hl2 <;> try contradiction
      simp [l1, l2, bind, Option.bind]
    | some pS =>
      rcases pS with ⟨idx, sc⟩; rw [hlkS] at hl1 hl2
      cases l1 : lookupColIdx? c1 col with
      | none => rw [l1] at hl1; contradiction
      | some p1 =>
        cases l2 : lookupColIdx? c2 col with
        | none => rw [l2] at hl2; contradiction
        | some p2 =>
          rw [l1] at hl1; rw [l2] at hl2
          rcases p1 with ⟨i1, _⟩; rcases p2 with ⟨i2, _⟩
          simp only [Option.map_some, Option.some.injEq] at hl1 hl2; subst i1; subst i2
          simp only [l1, l2, bind, Option.bind]
          have hfindSc : specCols.find? (fun x => x.name == col) = some sc := by
            rw [← lookupColIdx?_snd_eq_find?, hlkS]; rfl
          have hlow := hfnColLow col (Or.inr (Or.inr (Or.inr (Or.inr ⟨wSz, hfn⟩)))) sc hfindSc
          have hdropRel : ∀ (d : Nat) {xs ys : List TableRow}, RelList (RowEquiv L specCols) xs ys → RelList (RowEquiv L specCols) (xs.drop d) (ys.drop d) := by
            intro d; induction d with
            | zero => intro _ _ h; exact h
            | succ n ih => intro _ _ h; cases h with | nil => exact .nil | cons _ tl => exact ih tl
          rw [(hdropRel _ (hpart.take (pos + 1))).filterMap_congr
            (f := fun r => r.cells[idx]?) (g := fun r => r.cells[idx]?)
            (fun _ _ hr => hr.getElem?_eq (lookupColIdx?_props hlkS).1 hlow)]

private theorem lookupColIdx?_fst_congr {c1 c2 : List ColSpec} (k : Ident)
    (hn : c1.map ColSpec.name = c2.map ColSpec.name) :
    (lookupColIdx? c1 k).map Prod.fst = (lookupColIdx? c2 k).map Prod.fst := by
  let rec go (m : Nat) (l1 l2 : List ColSpec) (h : l1.map ColSpec.name = l2.map ColSpec.name) :
      (lookupColIdx?.go k m l1).map Prod.fst = (lookupColIdx?.go k m l2).map Prod.fst := by
    cases l1 with
    | nil => cases l2 <;> simp at h ⊢
    | cons a1 r1 =>
      cases l2 with
      | nil => simp at h
      | cons a2 r2 =>
        simp only [List.map_cons, List.cons.injEq] at h
        unfold lookupColIdx?.go; rw [h.1]
        cases (a2.name == k)
        · exact go (m + 1) r1 r2 h.2
        · rfl
  exact go 0 c1 c2 hn

private theorem extractKeyVals_congr_cols {c1 c2 : List ColSpec}
    (hn : c1.map ColSpec.name = c2.map ColSpec.name) (r : TableRow) :
    ∀ (ks : List Ident), extractKeyVals c1 ks r = extractKeyVals c2 ks r
  | [] => rfl
  | k :: ks => by
    unfold extractKeyVals; unfold extractKeyVals.go
    have hfst := lookupColIdx?_fst_congr k hn
    have htl := extractKeyVals_congr_cols hn r ks
    unfold extractKeyVals at htl
    cases l1 : lookupColIdx? c1 k with
    | none =>
      cases l2 : lookupColIdx? c2 k <;> rw [l1, l2] at hfst <;> first | contradiction | rfl
    | some p1 =>
      cases l2 : lookupColIdx? c2 k with
      | none => rw [l1, l2] at hfst; contradiction
      | some p2 =>
        rw [l1, l2] at hfst
        rcases p1 with ⟨i1, _⟩; rcases p2 with ⟨i2, _⟩
        injection hfst with ei; subst ei
        simp [bind, Option.bind, htl]

private theorem rowLtByKeys_congr_cols {c1 c2 : List ColSpec}
    (hn : c1.map ColSpec.name = c2.map ColSpec.name) (r1 r2 : TableRow) :
    ∀ (keys : List (Ident × SortDir)), rowLtByKeys c1 keys r1 r2 = rowLtByKeys c2 keys r1 r2
  | [] => rfl
  | (k, dir) :: rest => by
    unfold rowLtByKeys; unfold rowLtByKeys.go
    have hfst := lookupColIdx?_fst_congr k hn
    have htl := rowLtByKeys_congr_cols hn r1 r2 rest
    unfold rowLtByKeys at htl
    cases l1 : lookupColIdx? c1 k with
    | none =>
      cases l2 : lookupColIdx? c2 k <;> rw [l1, l2] at hfst <;> first | contradiction | rfl
    | some p1 =>
      cases l2 : lookupColIdx? c2 k with
      | none => rw [l1, l2] at hfst; contradiction
      | some p2 =>
        rw [l1, l2] at hfst
        rcases p1 with ⟨i1, _⟩; rcases p2 with ⟨i2, _⟩
        injection hfst with ei; subst ei
        simp [htl]

private theorem buildWindowRows_lockstep {L : TagSet}
    {curCols curSpecCols nextCols : List ColSpec}
    {item : WindowItem} {newCol : ColSpec} {targetTy : ScalarTy}
    {sIdx1 sIdx2 : List (TableRow × Nat)}
    (huniq : distinctIdents (curSpecCols.map ColSpec.name) = true)
    (hn : curCols.map ColSpec.name = curSpecCols.map ColSpec.name)
    (ht : curCols.map ColSpec.ty = curSpecCols.map ColSpec.ty)
    (hnewName : newCol.name = item.name)
    (hnextEq : nextCols = (if (curSpecCols.find? (fun c => c.name == newCol.name)).isSome then
        curSpecCols.map (fun c => if c.name == newCol.name then newCol else c)
      else curSpecCols ++ [newCol]))
    (hoverLow : ∀ k ∈ item.over, ∀ c, curSpecCols.find? (fun x => x.name == k) = some c → c.tags.subset L = true)
    (hfnColLow : ∀ col, (item.fn = .rank col ∨ (∃ o, item.fn = .lag col o) ∨ (∃ o, item.fn = .lead col o) ∨
      item.fn = .runningSum col ∨ (∃ w, item.fn = .rollingMean col w)) →
      ∀ c, curSpecCols.find? (fun x => x.name == col) = some c → c.tags.subset L = true)
    (hsRel : RelList (fun p1 p2 => RowEquiv L curSpecCols p1.1 p2.1 ∧ p1.2 = p2.2) sIdx1 sIdx2) :
    ∀ {idx1 idx2 : List (TableRow × Nat)} {out1 out2 : List TableRow},
      RelList (fun p1 p2 => RowEquiv L curSpecCols p1.1 p2.1 ∧ p1.2 = p2.2) idx1 idx2 →
      evalWindowOnTable.buildWindowRows curCols item.over sIdx1 (lookupColIdx? curCols item.name)
        (evalWindowComputeCell curCols item targetTy) idx1 = some out1 →
      evalWindowOnTable.buildWindowRows curCols item.over sIdx2 (lookupColIdx? curCols item.name)
        (evalWindowComputeCell curCols item targetTy) idx2 = some out2 →
      RelList (RowEquiv L nextCols) out1 out2
  | [], [], _, _, .nil, ho1, ho2 => by
    injection ho1 with e1; injection ho2 with e2; subst e1; subst e2; exact .nil
  | (r1, i1) :: _, (r2, i2) :: _, _, _, .cons ⟨hr, hiEq⟩ htl, ho1, ho2 => by
    subst hiEq
    unfold evalWindowOnTable.buildWindowRows at ho1 ho2; simp only [bind, Option.bind] at ho1 ho2
    have hmkEq : extractKeyVals curCols item.over r1 = extractKeyVals curCols item.over r2 := by
      rw [extractKeyVals_congr_cols hn r1, extractKeyVals_congr_cols hn r2]
      exact extractKeyVals_congr_of_low hr hoverLow
    rw [hmkEq] at ho1
    cases hmk : extractKeyVals curCols item.over r2 <;> rw [hmk] at ho1 ho2 <;> try contradiction
    rename_i myKey; dsimp only at ho1 ho2
    have hpartRel : RelList (fun p1 p2 => RowEquiv L curSpecCols p1.1 p2.1 ∧ p1.2 = p2.2)
        (windowPartIndexed curCols item.over sIdx1 myKey)
        (windowPartIndexed curCols item.over sIdx2 myKey) := by
      unfold windowPartIndexed
      apply hsRel.filter_congr
      intro a b ⟨hab, _⟩
      dsimp only
      rw [extractKeyVals_congr_cols hn a.1, extractKeyVals_congr_cols hn b.1,
          extractKeyVals_congr_of_low hab hoverLow]
    have hsndEq : (windowPartIndexed curCols item.over sIdx1 myKey).map Prod.snd =
        (windowPartIndexed curCols item.over sIdx2 myKey).map Prod.snd := by
      clear ho1 ho2 htl hsRel
      generalize windowPartIndexed curCols item.over sIdx1 myKey = wp1,
                 windowPartIndexed curCols item.over sIdx2 myKey = wp2 at hpartRel ⊢
      induction hpartRel with
      | nil => rfl
      | cons hd _ ih => simp [hd.2, ih]
    have hfindIdxEq : ∀ {l1 l2 : List (TableRow × Nat)}, l1.map Prod.snd = l2.map Prod.snd →
        l1.findIdx? (fun (_, j) => j == i1) = l2.findIdx? (fun (_, j) => j == i1) := by
      intro l1 l2 h
      have aux : ∀ (k : Nat) (a1 a2 : List (TableRow × Nat)), a1.map Prod.snd = a2.map Prod.snd →
          List.findIdx?.go (fun (_, j) => j == i1) a1 k = List.findIdx?.go (fun (_, j) => j == i1) a2 k := by
        intro k a1 a2 hm
        induction a1 generalizing a2 k with
        | nil => cases a2 <;> simp at hm ⊢
        | cons x1 xs1 ih =>
          cases a2 with
          | nil => simp at hm
          | cons x2 xs2 =>
            rcases x1 with ⟨_, j1⟩; rcases x2 with ⟨_, j2⟩
            simp only [List.map_cons, List.cons.injEq] at hm
            unfold List.findIdx?.go; dsimp only; rw [hm.1]
            by_cases hbeq : (j2 == i1) = true <;> simp [hbeq, ih (k + 1) xs2 hm.2]
      exact aux 0 l1 l2 h
    have hposEq : ((windowPartIndexed curCols item.over sIdx1 myKey).findIdx? (fun (_, j) => j == i1)).getD 0 =
        ((windowPartIndexed curCols item.over sIdx2 myKey).findIdx? (fun (_, j) => j == i1)).getD 0 :=
      congrArg (·.getD 0) (hfindIdxEq hsndEq)
    have hpartFst : RelList (RowEquiv L curSpecCols)
        ((windowPartIndexed curCols item.over sIdx1 myKey).map Prod.fst)
        ((windowPartIndexed curCols item.over sIdx2 myKey).map Prod.fst) :=
      hpartRel.map Prod.fst Prod.fst (fun _ _ h => h.1)
    have hwvEq : evalWindowComputeCell curCols item targetTy ((windowPartIndexed curCols item.over sIdx1 myKey).map Prod.fst)
        (((windowPartIndexed curCols item.over sIdx1 myKey).findIdx? (fun (_, j) => j == i1)).getD 0) =
        evalWindowComputeCell curCols item targetTy ((windowPartIndexed curCols item.over sIdx2 myKey).map Prod.fst)
        (((windowPartIndexed curCols item.over sIdx2 myKey).findIdx? (fun (_, j) => j == i1)).getD 0) := by
      rw [hposEq]
      exact evalWindowComputeCell_congr _ hn ht hn ht hpartFst hfnColLow
    rw [hwvEq] at ho1
    cases hwv : evalWindowComputeCell curCols item targetTy ((windowPartIndexed curCols item.over sIdx2 myKey).map Prod.fst) _ <;>
      rw [hwv] at ho1 ho2 <;> try contradiction
    rename_i wVal; dsimp only at ho1 ho2
    cases ht1 : evalWindowOnTable.buildWindowRows curCols item.over sIdx1 _ _ _ <;> rw [ht1] at ho1 <;> try contradiction
    cases ht2 : evalWindowOnTable.buildWindowRows curCols item.over sIdx2 _ _ _ <;> rw [ht2] at ho2 <;> try contradiction
    injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
    refine .cons ?_ (buildWindowRows_lockstep huniq hn ht hnewName hnextEq hoverLow hfnColLow hsRel htl ht1 ht2)
    unfold RowEquiv; dsimp only
    rw [hnextEq]
    have hcell := cellsEquiv_replace_or_append (newCol := newCol) (v1 := wVal) (v2 := wVal) huniq hr (fun _ => rfl)
    rw [hnewName] at hcell ⊢
    have hfst := lookupColIdx?_fst_congr item.name hn
    cases l1 : lookupColIdx? curCols item.name with
    | none =>
      cases l2 : lookupColIdx? curSpecCols item.name <;> rw [l1, l2] at hfst <;> try contradiction
      simpa [l2] using hcell
    | some p1 =>
      cases l2 : lookupColIdx? curSpecCols item.name with
      | none => rw [l1, l2] at hfst; contradiction
      | some p2 =>
        rw [l1, l2] at hfst
        rcases p1 with ⟨k1, _⟩; rcases p2 with ⟨k2, _⟩
        injection hfst with ek; subst ek
        simpa [l2] using hcell

private theorem RowsWf.congr_ty_same {prog : Program} {rs : List TableRow} {c1 c2 : List ColSpec}
    (hty : c1.map ColSpec.ty = c2.map ColSpec.ty)
    (hr : RowsWf prog rs c1 false false) : RowsWf prog rs c2 false false :=
  RowsWf.of_forall_raw (fun r h => (hr.to_forall r h).congr_ty hty)

private theorem find_name_ty_congr :
    ∀ {l1 l2 : List ColSpec} (k : Ident),
      l1.map ColSpec.name = l2.map ColSpec.name →
      l1.map ColSpec.ty = l2.map ColSpec.ty →
      (l1.find? (fun c => c.name == k)).map (fun c => (c.name, c.ty)) =
        (l2.find? (fun c => c.name == k)).map (fun c => (c.name, c.ty))
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hn, _ => by simp at hn
  | _ :: _, [], _, hn, _ => by simp at hn
  | a1 :: r1, a2 :: r2, k, hn, ht => by
    simp only [List.map_cons, List.cons.injEq] at hn ht
    simp only [List.find?, hn.1]
    cases (a2.name == k)
    · exact find_name_ty_congr k hn.2 ht.2
    · simp [hn.1, ht.1]

set_option maxHeartbeats 400000 in
theorem evalWindowOnTable_ni {prog : Program} {L ot : TagSet}
    {curTV1 curTV2 nextTV1 nextTV2 : TableVal}
    {curCols curSpecCols nextCols nextSpecCols : List ColSpec}
    {item : WindowItem}
    (huniq : distinctIdents (curSpecCols.map ColSpec.name) = true)
    (hcolsSpec : ∀ c ∈ curSpecCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
    (hcolsCur : ∀ c ∈ curCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw)
    (hc1 : curTV1.cols = curCols) (hc2 : curTV2.cols = curCols)
    (hn : curCols.map ColSpec.name = curSpecCols.map ColSpec.name)
    (ht : curCols.map ColSpec.ty = curSpecCols.map ColSpec.ty)
    (hrWf1 : RowsWf prog curTV1.rows curSpecCols false false)
    (hrWf2 : RowsWf prog curTV2.rows curSpecCols false false)
    (happlySpec : applyWindowItem curSpecCols ot item = .ok nextSpecCols)
    (happlyCur : applyWindowItem curCols TagSet.empty item = .ok nextCols)
    (hev1 : evalWindowOnTable curTV1 item nextCols = some nextTV1)
    (hev2 : evalWindowOnTable curTV2 item nextCols = some nextTV2)
    (hrel : if ot.subset L = true then
              RelList (RowEquiv L curSpecCols) curTV1.rows curTV2.rows
            else
              ∃ rows1', List.Perm curTV1.rows rows1' ∧ RelList (RowEquiv L curSpecCols) rows1' curTV2.rows) :
    nextTV1.cols = nextCols ∧
    nextTV2.cols = nextCols ∧
    distinctIdents (nextSpecCols.map ColSpec.name) = true ∧
    (∀ c ∈ nextSpecCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) ∧
    (∀ c ∈ nextCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) ∧
    nextCols.map ColSpec.name = nextSpecCols.map ColSpec.name ∧
    nextCols.map ColSpec.ty = nextSpecCols.map ColSpec.ty ∧
    RowsWf prog nextTV1.rows nextSpecCols false false ∧
    RowsWf prog nextTV2.rows nextSpecCols false false ∧
    (if ot.subset L = true then
       RelList (RowEquiv L nextSpecCols) nextTV1.rows nextTV2.rows
     else
       ∃ rows1', List.Perm nextTV1.rows rows1' ∧ RelList (RowEquiv L nextSpecCols) rows1' nextTV2.rows) := by
  have huniqCur : distinctIdents (curCols.map ColSpec.name) = true := hn ▸ huniq
  rcases applyWindowItem_props TagSet.empty huniq hcolsSpec happlySpec with
    ⟨nextCols', happlySpec0, hnNext', htNext', hdistNext, hnextSpecProps, _⟩
  rcases applyWindowItem_props TagSet.empty huniqCur hcolsCur happlyCur with
    ⟨_, _, _, _, _, hnextCurProps, _⟩
  have hcurRowsWf1 : RowsWf prog curTV1.rows curTV1.cols false false :=
    hrWf1.congr_ty_same (hc1 ▸ ht.symm)
  have hcurRowsWf2 : RowsWf prog curTV2.rows curTV2.cols false false :=
    hrWf2.congr_ty_same (hc2 ▸ ht.symm)
  rcases evalWindowOnTable_sound (hc1 ▸ huniqCur) (hc1 ▸ hcolsCur) hcurRowsWf1 (hc1 ▸ happlyCur) with
    ⟨ntv1', hev1', hnc1, hnrWf1⟩
  rcases evalWindowOnTable_sound (hc2 ▸ huniqCur) (hc2 ▸ hcolsCur) hcurRowsWf2 (hc2 ▸ happlyCur) with
    ⟨ntv2', hev2', hnc2, hnrWf2⟩
  rw [hev1] at hev1'; injection hev1' with e1; subst e1
  rw [hev2] at hev2'; injection hev2' with e2; subst e2
  have hnextNt : nextCols.map ColSpec.name = nextSpecCols.map ColSpec.name ∧
      nextCols.map ColSpec.ty = nextSpecCols.map ColSpec.ty := by
    rw [← hnNext', ← htNext']
    rw [applyWindowItem_eq] at happlyCur happlySpec0
    split at happlyCur; contradiction
    split at happlySpec0; contradiction
    cases hfS : windowFnSpec? curSpecCols TagSet.empty item with
    | none => rw [hfS] at happlySpec0; contradiction
    | some pS =>
      rcases pS with ⟨wTy, wTsS⟩
      rcases windowFnSpec?_cols_congr (fun k => find_name_ty_congr k hn ht) hfS with ⟨wTsC, hfC⟩
      rw [hfS] at happlySpec0; rw [hfC] at happlyCur
      dsimp only at happlyCur happlySpec0
      have hisSomeEq : (curCols.find? (fun c => c.name == item.name)).isSome =
          (curSpecCols.find? (fun c => c.name == item.name)).isSome := by
        rw [← lookupColIdx?_snd_eq_find?, ← lookupColIdx?_snd_eq_find?]
        have hfst := lookupColIdx?_fst_congr item.name hn
        cases l1 : lookupColIdx? curCols item.name <;> cases l2 : lookupColIdx? curSpecCols item.name <;>
          simp only [l1, l2, Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some, reduceCtorEq] at hfst ⊢
      rw [hisSomeEq] at happlyCur
      cases hsome : (curSpecCols.find? (fun c => c.name == item.name)).isSome <;>
        rw [hsome] at happlyCur happlySpec0 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happlyCur happlySpec0
      · subst happlyCur; subst happlySpec0; simp [hn, ht]
      · subst happlyCur; subst happlySpec0
        let ncC := ({ name := item.name, ty := wTy, tags := wTsC, bucketed := false, aggKind := .raw } : ColSpec)
        let ncS := ({ name := item.name, ty := wTy, tags := wTsS, bucketed := false, aggKind := .raw } : ColSpec)
        have aux : ∀ (l1 l2 : List ColSpec), l1.map ColSpec.name = l2.map ColSpec.name → l1.map ColSpec.ty = l2.map ColSpec.ty →
            (l1.map (fun c => if c.name == item.name then ncC else c)).map ColSpec.name =
              (l2.map (fun c => if c.name == item.name then ncS else c)).map ColSpec.name ∧
            (l1.map (fun c => if c.name == item.name then ncC else c)).map ColSpec.ty =
              (l2.map (fun c => if c.name == item.name then ncS else c)).map ColSpec.ty := by
          intro l1 l2 h1 h2
          induction l1 generalizing l2 with
          | nil => cases l2 <;> simp at h1 ⊢
          | cons a1 r1 ih =>
            cases l2 with
            | nil => simp at h1
            | cons a2 r2 =>
              simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
              rcases ih r2 h1.2 h2.2 with ⟨in1, it1⟩
              cases hbe : (a2.name == item.name) <;>
                simp only [h1.1, h2.1, hbe, Bool.false_eq_true, ↓reduceIte, ncC, ncS, in1, it1, and_self]
        exact aux curCols curSpecCols hn ht
  refine ⟨hnc1, hnc2, hdistNext, hnextSpecProps, hnextCurProps, hnextNt.1, hnextNt.2,
    hnrWf1.congr_ty_same hnextNt.2, hnrWf2.congr_ty_same hnextNt.2, ?_⟩
  -- Unpack `applyWindowItem curSpecCols ot item = .ok nextSpecCols`
  have happlySpecSave := happlySpec
  rw [applyWindowItem_eq] at happlySpec
  split at happlySpec; contradiction
  cases hfnS : windowFnSpec? curSpecCols ot item with
  | none => rw [hfnS] at happlySpec; contradiction
  | some fnPair =>
    rcases fnPair with ⟨wTy, wTags⟩; rw [hfnS] at happlySpec; dsimp only at happlySpec
    let newCol : ColSpec := { name := item.name, ty := wTy, tags := wTags, bucketed := false, aggKind := .raw }
    have hnextEq : nextSpecCols = (if (curSpecCols.find? (fun c => c.name == newCol.name)).isSome then
        curSpecCols.map (fun c => if c.name == newCol.name then newCol else c) else curSpecCols ++ [newCol]) := by
      dsimp only [newCol]
      cases hsome : (curSpecCols.find? (fun c => c.name == item.name)).isSome <;>
        simp only [hsome, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happlySpec ⊢ <;>
        exact happlySpec.symm
    unfold evalWindowOnTable at hev1 hev2; simp only [hc1, hc2, bind, Option.bind] at hev1 hev2
    cases htc : nextCols.find? (fun c => c.name == item.name) <;> rw [htc] at hev1 hev2 <;> try contradiction
    rename_i targetSpec; dsimp only at hev1 hev2
    cases hbw1 : evalWindowOnTable.buildWindowRows curCols item.over _ (lookupColIdx? curCols item.name) _ curTV1.rows.zipIdx <;>
      rw [hbw1] at hev1 <;> try contradiction
    cases hbw2 : evalWindowOnTable.buildWindowRows curCols item.over _ (lookupColIdx? curCols item.name) _ curTV2.rows.zipIdx <;>
      rw [hbw2] at hev2 <;> try contradiction
    injection hev1 with etv1; injection hev2 with etv2; subst etv1; subst etv2; dsimp only
    cases hwLow : wTags.subset L
    · -- High window column (`wTags ⊈ L`): untouched columns come directly from input rows!
      have hlenNext : (if (lookupColIdx? curCols item.name).isSome then curCols.length else curCols.length + 1) =
          nextSpecCols.length := by
        have hlenEq : curCols.length = curSpecCols.length := by
          have := congrArg List.length hn; simpa using this
        have hfst := lookupColIdx?_fst_congr item.name hn
        rw [hnextEq]; dsimp only [newCol]
        cases l1 : lookupColIdx? curCols item.name with
        | none =>
          cases l2 : lookupColIdx? curSpecCols item.name <;> rw [l1, l2] at hfst <;> try contradiction
          have hfN := (lookupColIdx?_none_iff_find?_none curSpecCols item.name).mp l2
          simp [hfN, hlenEq]
        | some p1 =>
          cases l2 : lookupColIdx? curSpecCols item.name with
          | none => rw [l1, l2] at hfst; contradiction
          | some p2 =>
            rcases lookupColIdx?_props l2 with ⟨hg2, hn2'⟩
            have hfindNew : curSpecCols.find? (fun c => c.name == item.name) = some p2.2 := by
              rw [← hn2']; exact find_unique_of_mem huniq (List.mem_of_getElem? hg2)
            simp [hfindNew, hlenEq]
      have hu1 := buildWindowRows_untouched_wf item.over _ _ _ item.name
        (by cases hlk : lookupColIdx? curCols item.name with | none => trivial | some p => exact lookupColIdx?_props hlk)
        (hc1 ▸ hcurRowsWf1).to_forall hbw1
      have hu2 := buildWindowRows_untouched_wf item.over _ _ _ item.name
        (by cases hlk : lookupColIdx? curCols item.name with | none => trivial | some p => exact lookupColIdx?_props hlk)
        (hc2 ▸ hcurRowsWf2).to_forall hbw2
      have hcompose : ∀ {nr1 r1' r2 nr2 : TableRow},
          (nr1.cells.length = nextSpecCols.length ∧ ∀ (i : Nat) (c : ColSpec), curCols[i]? = some c → c.name ≠ item.name → nr1.cells[i]? = r1'.cells[i]?) →
          RowEquiv L curSpecCols r1' r2 →
          (nr2.cells.length = nextSpecCols.length ∧ ∀ (i : Nat) (c : ColSpec), curCols[i]? = some c → c.name ≠ item.name → nr2.cells[i]? = r2.cells[i]?) →
          RowEquiv L nextSpecCols nr1 nr2 := by
        intro nr1 r1' r2 nr2 ⟨hl1, hg1⟩ hr12 ⟨hl2, hg2⟩
        apply cellsEquiv_from_getElem? hl1 hl2
        intro i c hgetNext hcLow
        have hcNe : c.name ≠ item.name := by
          intro hcEq
          have hcIsNew : c = newCol := by
            rw [hnextEq] at hgetNext
            split at hgetNext
            · rw [List.getElem?_map] at hgetNext
              cases hgS : curSpecCols[i]? with
              | none => rw [hgS] at hgetNext; simp at hgetNext
              | some d =>
                rw [hgS] at hgetNext; simp only [Option.map_some, Option.some.injEq] at hgetNext
                split at hgetNext
                · exact hgetNext.symm
                · rename_i hdn; subst hgetNext; simp [newCol, hcEq] at hdn
            · by_cases hlt : i < curSpecCols.length
              · rw [List.getElem?_append_left hlt] at hgetNext
                have hfSome := find_unique_of_mem huniq (List.mem_of_getElem? hgetNext)
                rw [hcEq] at hfSome
                rename_i hfNot; simp [newCol, hfSome] at hfNot
              · have hge : curSpecCols.length ≤ i := by omega
                rw [List.getElem?_append_right hge] at hgetNext
                cases hd : i - curSpecCols.length with
                | zero => rw [hd] at hgetNext; simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetNext; exact hgetNext.symm
                | succ _ => rw [hd] at hgetNext; simp at hgetNext
          subst hcIsNew; dsimp only [newCol] at hcLow; rw [hwLow] at hcLow; nomatch hcLow
        have hgetSpec : curSpecCols[i]? = some c := by
          rw [hnextEq] at hgetNext
          split at hgetNext
          · rw [List.getElem?_map] at hgetNext
            cases hgS : curSpecCols[i]? with
            | none => rw [hgS] at hgetNext; simp at hgetNext
            | some d =>
              rw [hgS] at hgetNext; simp only [Option.map_some, Option.some.injEq] at hgetNext
              split at hgetNext
              · subst hgetNext; exact absurd rfl hcNe
              · subst hgetNext; exact rfl
          · by_cases hlt : i < curSpecCols.length
            · rwa [List.getElem?_append_left hlt] at hgetNext
            · have hge : curSpecCols.length ≤ i := by omega
              rw [List.getElem?_append_right hge] at hgetNext
              cases hd : i - curSpecCols.length with
              | zero => rw [hd] at hgetNext; simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetNext; subst hgetNext; exact absurd rfl hcNe
              | succ _ => rw [hd] at hgetNext; simp at hgetNext
        have hgetCur : ∃ d, curCols[i]? = some d ∧ d.name = c.name := by
          have hnGet : (curCols.map ColSpec.name)[i]? = (curSpecCols.map ColSpec.name)[i]? := by rw [hn]
          rw [List.getElem?_map, List.getElem?_map, hgetSpec] at hnGet
          cases hd : curCols[i]? with
          | none => rw [hd] at hnGet; simp at hnGet
          | some d => rw [hd] at hnGet; injection hnGet with edn; exact ⟨d, rfl, edn⟩
        rcases hgetCur with ⟨d, hdGet, hdName⟩
        rw [hg1 i d hdGet (hdName ▸ hcNe), hg2 i d hdGet (hdName ▸ hcNe)]
        exact hr12.getElem?_eq hgetSpec hcLow
      have hu1' : RelList (fun (r nr : TableRow) => nr.cells.length = nextSpecCols.length ∧
            ∀ (i : Nat) (c : ColSpec), curCols[i]? = some c → c.name ≠ item.name → nr.cells[i]? = r.cells[i]?) curTV1.rows _ :=
        hu1.imp (fun _ _ ⟨hl, hg⟩ => ⟨hl.trans hlenNext, hg⟩)
      have hu2' : RelList (fun (r nr : TableRow) => nr.cells.length = nextSpecCols.length ∧
            ∀ (i : Nat) (c : ColSpec), curCols[i]? = some c → c.name ≠ item.name → nr.cells[i]? = r.cells[i]?) curTV2.rows _ :=
        hu2.imp (fun _ _ ⟨hl, hg⟩ => ⟨hl.trans hlenNext, hg⟩)
      cases hord : ot.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
      · rcases hrel with ⟨rows1', hp, hr'⟩
        rcases relList_perm_right hu1'.symm hp with ⟨nr1', hpNr, hnr1Rel⟩
        refine ⟨nr1', hpNr, (hnr1Rel.trans (T := fun a b => ∃ r1', (a.cells.length = nextSpecCols.length ∧
          ∀ (i : Nat) (c : ColSpec), curCols[i]? = some c → c.name ≠ item.name → a.cells[i]? = r1'.cells[i]?) ∧ RowEquiv L curSpecCols r1' b)
          (fun _ _ _ a b => ⟨_, a, b⟩) hr').trans (fun _ _ _ ⟨_, a, b⟩ c => hcompose a b c) hu2'⟩
      · exact (hu1'.symm.trans (T := fun a b => ∃ r1', (a.cells.length = nextSpecCols.length ∧
          ∀ (i : Nat) (c : ColSpec), curCols[i]? = some c → c.name ≠ item.name → a.cells[i]? = r1'.cells[i]?) ∧ RowEquiv L curSpecCols r1' b)
          (fun _ _ _ a b => ⟨_, a, b⟩) hrel).trans (fun _ _ _ ⟨_, a, b⟩ c => hcompose a b c) hu2'
    · -- Low window column (`wTags ⊆ L`): implies `ot ⊆ L`, `over ⊆ L`, `order ⊆ L`, and `fnCol ⊆ L`!
      have hctxSub : (((TagSet.unionList (item.over.filterMap (fun k => (curSpecCols.find? (fun c => c.name == k)).map ColSpec.tags))).union
          (TagSet.unionList (item.order.filterMap (fun (k, _) => (curSpecCols.find? (fun c => c.name == k)).map ColSpec.tags)))).union ot).subset wTags = true := by
        unfold windowFnSpec? at hfnS
        cases hfn : item.fn <;> rw [hfn] at hfnS <;> dsimp only at hfnS
        case rowNumber =>
          injection hfnS with hp; injection hp with _ htEq; subst htEq; exact TagSet.subset_refl _
        all_goals (
          repeat (first
            | contradiction
            | (injection hfnS with hp; injection hp with _ htEq; subst htEq; exact TagSet.subset_union_right _ _)
            | (simp only [Option.map_eq_some_iff] at hfnS; rcases hfnS with ⟨_, _, hp⟩; injection hp with _ htEq; subst htEq; exact TagSet.subset_union_right _ _)
            | split at hfnS)
        )
      have hctxLow := TagSet.subset_trans hctxSub hwLow
      simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hctxLow
      rcases hctxLow with ⟨⟨hoverSub, hordSub⟩, hotLow⟩
      simp only [hotLow, ↓reduceIte] at hrel ⊢
      have hoverLow : ∀ k ∈ item.over, ∀ c, curSpecCols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
        intro k hk c hfc
        exact hoverSub c.tags (List.mem_filterMap.mpr ⟨k, hk, by simp [hfc]⟩)
      have hordLow : ∀ p ∈ item.order, ∀ c, curSpecCols.find? (fun x => x.name == p.1) = some c → c.tags.subset L = true := by
        intro p hp c hfc
        exact hordSub c.tags (List.mem_filterMap.mpr ⟨p, hp, by cases p; simp [hfc]⟩)
      have hfnColLow : ∀ col, (item.fn = .rank col ∨ (∃ o, item.fn = .lag col o) ∨ (∃ o, item.fn = .lead col o) ∨
          item.fn = .runningSum col ∨ (∃ w, item.fn = .rollingMean col w)) →
          ∀ c, curSpecCols.find? (fun x => x.name == col) = some c → c.tags.subset L = true := by
        intro col hdisj c hfc
        unfold windowFnSpec? at hfnS
        rcases hdisj with h | ⟨_, h⟩ | ⟨_, h⟩ | h | ⟨_, h⟩ <;>
          (rw [h] at hfnS; dsimp only at hfnS)
        · rw [hfc] at hfnS; dsimp only at hfnS; split at hfnS <;> try contradiction
          injection hfnS with hp; injection hp with _ htEq; subst htEq
          exact TagSet.subset_trans (TagSet.subset_union_left _ _) hwLow
        · rw [hfc] at hfnS; dsimp only at hfnS
          injection hfnS with hp; injection hp with _ htEq; subst htEq
          exact TagSet.subset_trans (TagSet.subset_union_left _ _) hwLow
        · rw [hfc] at hfnS; dsimp only at hfnS
          injection hfnS with hp; injection hp with _ htEq; subst htEq
          exact TagSet.subset_trans (TagSet.subset_union_left _ _) hwLow
        · rw [hfc] at hfnS; dsimp only at hfnS
          simp only [Option.map_eq_some_iff] at hfnS; rcases hfnS with ⟨_, _, hp⟩
          injection hp with _ htEq; subst htEq
          exact TagSet.subset_trans (TagSet.subset_union_left _ _) hwLow
        · split at hfnS <;> try contradiction
          rw [hfc] at hfnS; dsimp only at hfnS
          split at hfnS <;> try contradiction
          injection hfnS with hp; injection hp with _ htEq; subst htEq
          exact TagSet.subset_trans (TagSet.subset_union_left _ _) hwLow
      have hidxRel := hrel.zipIdx_go 0
      have hsRel : RelList (fun p1 p2 => RowEquiv L curSpecCols p1.1 p2.1 ∧ p1.2 = p2.2)
          (if item.order.isEmpty then curTV1.rows.zipIdx else insertionSortBy (fun a b => rowLtByKeys curCols item.order a.1 b.1) curTV1.rows.zipIdx)
          (if item.order.isEmpty then curTV2.rows.zipIdx else insertionSortBy (fun a b => rowLtByKeys curCols item.order a.1 b.1) curTV2.rows.zipIdx) := by
        cases item.order.isEmpty
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply insertionSortBy_forall2 _ hidxRel
          intro a1 a2 b1 b2 ha hb
          rw [rowLtByKeys_congr_cols hn a1.1 a2.1, rowLtByKeys_congr_cols hn b1.1 b2.1]
          exact rowLtByKeys_congr_of_low ha.1 hb.1 hordLow
        · exact hidxRel
      exact buildWindowRows_lockstep huniq hn ht rfl hnextEq hoverLow hfnColLow hsRel hidxRel hbw1 hbw2

theorem evalWindowItems_ni {prog : Program} {L ot : TagSet} :
    ∀ (items : List WindowItem) {curTV1 curTV2 winTV1 winTV2 : TableVal}
      {curCols curSpecCols outSpecCols : List ColSpec},
      distinctIdents (curSpecCols.map ColSpec.name) = true →
      (∀ c ∈ curSpecCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
      (∀ c ∈ curCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw) →
      curTV1.cols = curCols → curTV2.cols = curCols →
      curCols.map ColSpec.name = curSpecCols.map ColSpec.name →
      curCols.map ColSpec.ty = curSpecCols.map ColSpec.ty →
      RowsWf prog curTV1.rows curSpecCols false false →
      RowsWf prog curTV2.rows curSpecCols false false →
      applyWindowItems ot curSpecCols items = .ok outSpecCols →
      evalWindowItems curTV1 items = some winTV1 →
      evalWindowItems curTV2 items = some winTV2 →
      (if ot.subset L = true then
         RelList (RowEquiv L curSpecCols) curTV1.rows curTV2.rows
       else
         ∃ rows1', List.Perm curTV1.rows rows1' ∧ RelList (RowEquiv L curSpecCols) rows1' curTV2.rows) →
      if ot.subset L = true then
        RelList (RowEquiv L outSpecCols) winTV1.rows winTV2.rows
      else
        ∃ rows1', List.Perm winTV1.rows rows1' ∧ RelList (RowEquiv L outSpecCols) rows1' winTV2.rows
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, happly, hev1, hev2, hrel => by
    unfold applyWindowItems at happly; injection happly with e; subst e
    unfold evalWindowItems at hev1 hev2
    injection hev1 with e1; injection hev2 with e2; subst e1; subst e2; exact hrel
  | it :: rest, curTV1, curTV2, winTV1, winTV2, curCols, curSpecCols, outSpecCols,
    huniq, hcolsSpec, hcolsCur, hc1, hc2, hn, ht, hr1, hr2, happly, hev1, hev2, hrel => by
    unfold applyWindowItems at happly; simp only [bind, Except.bind] at happly
    cases hstepS : applyWindowItem curSpecCols ot it <;> rw [hstepS] at happly <;> try contradiction
    rename_i nextSpecCols; dsimp only at happly
    unfold evalWindowItems at hev1 hev2; simp only [hc1, hc2, bind, Option.bind] at hev1 hev2
    cases hstepC : applyWindowItem curCols TagSet.empty it with
    | error _ => rw [hstepC] at hev1; simp [Except.toOption] at hev1
    | ok nextCols =>
      rw [hstepC] at hev1 hev2; dsimp only [Except.toOption] at hev1 hev2
      cases hw1 : evalWindowOnTable curTV1 it nextCols <;> rw [hw1] at hev1 <;> try contradiction
      cases hw2 : evalWindowOnTable curTV2 it nextCols <;> rw [hw2] at hev2 <;> try contradiction
      rcases evalWindowOnTable_ni huniq hcolsSpec hcolsCur hc1 hc2 hn ht hr1 hr2 hstepS hstepC hw1 hw2 hrel with
        ⟨hnc1, hnc2, hnUniq, hnSpecP, hnCurP, hnN, hnT, hnr1, hnr2, hnRel⟩
      exact evalWindowItems_ni rest hnUniq hnSpecP hnCurP hnc1 hnc2 hnN hnT hnr1 hnr2 happly hev1 hev2 hnRel

/-! ### `FillGaps`, `PivotWider` & `Crosstab` Non-Interference Helpers -/

theorem fillGaps_lowRows {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {tv1 tv2 : TableVal} {tt : TableTy} {col : Ident} {over : List Ident} {newRowTags : TagSet}
    (ht : TableEquiv prog L tv1 tv2 tt)
    (hrLow : tt.rowTags.subset L = true)
    (hkeysExist : ∀ k ∈ over ++ [col], (tt.cols.find? (fun c => c.name == k)).isSome = true)
    (hkeysLow : ∀ k ∈ over ++ [col], ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true) :
    let outCols := tt.cols.map (fun c =>
      if c.name == col || over.contains c.name then
        { c with aggKind := .raw, bucketed := false }
      else
        { c with tags := (c.tags.union newRowTags).union tt.orderTags, aggKind := .raw, bucketed := false })
    let sortSpec := (over ++ [col]).map (fun k => (k, SortDir.asc))
    let sorted1 := insertionSortBy (rowLtByKeys tv1.cols sortSpec) (tv1.rows.map (fun r => { r with groupMeta := none }))
    let sorted2 := insertionSortBy (rowLtByKeys tv2.cols sortSpec) (tv2.rows.map (fun r => { r with groupMeta := none }))
    RelList (RowEquiv L outCols) sorted1 sorted2 := by
  intro outCols sortSpec sorted1 sorted2
  rcases ht.cols_eq with ⟨hc1, hc2⟩
  dsimp only [sorted1, sorted2]; rw [hc1, hc2]
  cases ht.wf1 with | table _ hsch hrWf1 =>
  cases ht.wf2 with | table _ _ hrWf2 =>
  have huniq := (tableSchemaWf_cols_props hsch).1
  have hcols := fun c hc => (tableSchemaWf_cols_props hsch).2 c hc |>.1
  let resetGM : TableRow → TableRow := fun r => { r with groupMeta := none }
  cases hord : tt.orderTags.subset L
  · -- High `orderTags`: non-key columns have `.union tt.orderTags` (`⊈ L`), while key columns sort canonically!
    have hlr := ht.lowRows hrLow
    simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr
    rcases hlr with ⟨rows1', hp, hrel⟩
    let keys := over ++ [col]
    let R : TableRow → List Val → Prop := fun r kv => extractKeyVals tt.cols keys r = some kv ∧ CellsWf prog r.cells tt.cols
    have hmkRel : ∀ (rs : List TableRow), (∀ r ∈ rs, CellsWf prog r.cells tt.cols) →
        ∃ kvs, kvs = rs.filterMap (extractKeyVals tt.cols keys) ∧ RelList R rs kvs := by
      intro rs hrs
      induction rs with
      | nil => exact ⟨[], rfl, .nil⟩
      | cons r rtl ih =>
        have hrw := hrs r (.head _)
        rcases extractKeyVals_some hrw keys hkeysExist with ⟨kv, hkv⟩
        rcases ih (fun x hx => hrs x (.tail _ hx)) with ⟨tlKvs, htlEq, htlRel⟩
        exact ⟨kv :: tlKvs, by simp [hkv, htlEq], .cons ⟨hkv, hrw⟩ htlRel⟩
    have hr1sWf : ∀ r ∈ tv1.rows.map resetGM, CellsWf prog r.cells tt.cols := by
      intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨o, ho, rfl⟩; exact hrWf1.to_forall o ho
    have hr2sWf : ∀ r ∈ tv2.rows.map resetGM, CellsWf prog r.cells tt.cols := by
      intro r hr; rw [List.mem_map] at hr; rcases hr with ⟨o, ho, rfl⟩; exact hrWf2.to_forall o ho
    rcases hmkRel (tv1.rows.map resetGM) hr1sWf with ⟨kvs1, hkvs1Eq, hrel1⟩
    rcases hmkRel (tv2.rows.map resetGM) hr2sWf with ⟨kvs2, hkvs2Eq, hrel2⟩
    have hsortCongr : ∀ a1 a2 b1 b2, R a1 b1 → R a2 b2 → rowLtByKeys tt.cols sortSpec a1 a2 = valListLt b1 b2 :=
      fun _ _ _ _ ha hb => rowLtByKeys_asc_eq_valListLt ha.1 hb.1
        (extractKeyVals_sortable hd hcols ha.2 ha.1) (extractKeyVals_sortable hd hcols hb.2 hb.1)
    have hs1 := insertionSortBy_forall2 hsortCongr hrel1
    have hs2 := insertionSortBy_forall2 hsortCongr hrel2
    have hkvReset : ∀ r : TableRow, extractKeyVals tt.cols keys (resetGM r) = extractKeyVals tt.cols keys r := by
      intro r; unfold extractKeyVals
      let rec aux : ∀ ks, extractKeyVals.go tt.cols (resetGM r) ks = extractKeyVals.go tt.cols r ks
        | [] => rfl
        | k :: ks => by
          unfold extractKeyVals.go
          cases lookupColIdx? tt.cols k with
          | none => rfl
          | some p => rcases p with ⟨idx, _⟩; dsimp only [resetGM, bind, Option.bind]; rw [aux ks]
      exact aux keys
    have hpKvs : List.Perm kvs1 kvs2 := by
      rw [hkvs1Eq, hkvs2Eq, List.filterMap_map, List.filterMap_map]
      have heq' : rows1'.filterMap (extractKeyVals tt.cols keys ∘ resetGM) =
          tv2.rows.filterMap (extractKeyVals tt.cols keys ∘ resetGM) :=
        RelList.filterMap_congr (R := RowEquiv L tt.cols) (fun a b hr => by
          simp only [Function.comp, hkvReset]; exact extractKeyVals_congr_of_low hr hkeysLow) hrel
      exact heq' ▸ perm_filterMap _ hp
    have hkvs1Sort : ∀ kv ∈ kvs1, SortableValList kv := by
      intro kv hkv; rw [hkvs1Eq, List.mem_filterMap] at hkv
      rcases hkv with ⟨r, hr, hkvEq⟩; exact extractKeyVals_sortable hd hcols (hr1sWf r hr) hkvEq
    have hsortEq := insertionSortBy_perm_eq valListLt_irrefl valListLt_trans valListLt_trichotomy hkvs1Sort hpKvs
    rw [hsortEq] at hs1
    have hpaired : RelList (fun a b => ∃ kv, R a kv ∧ R b kv)
        (insertionSortBy (rowLtByKeys tt.cols sortSpec) (tv1.rows.map resetGM))
        (insertionSortBy (rowLtByKeys tt.cols sortSpec) (tv2.rows.map resetGM)) :=
      hs1.trans (fun _ kv _ a b => ⟨kv, a, b⟩) hs2.symm
    apply hpaired.imp
    intro a b ⟨kv, ⟨haKv, haWf⟩, ⟨hbKv, hbWf⟩⟩
    apply cellsEquiv_from_getElem? (by simp [outCols, haWf.length_eq]) (by simp [outCols, hbWf.length_eq])
    intro i outC houtGet houtLow
    rw [List.getElem?_map] at houtGet
    cases hci : tt.cols[i]? with
    | none => rw [hci] at houtGet; simp at houtGet
    | some origC =>
      rw [hci] at houtGet; simp only [Option.map_some, Option.some.injEq] at houtGet
      cases hkeyB : (origC.name == col || over.contains origC.name)
      · rw [hkeyB] at houtGet; simp only [Bool.false_eq_true, ↓reduceIte] at houtGet
        subst houtGet; dsimp only at houtLow
        simp only [TagSet.union_subset_iff, Bool.and_eq_true] at houtLow
        rw [hord] at houtLow; nomatch houtLow.2
      · have hkMem : origC.name ∈ keys := by
          simp only [keys, List.mem_append, List.mem_singleton]
          simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hkeyB
          exact hkeyB.symm
        have hfind := find_unique_of_mem huniq (List.mem_of_getElem? hci)
        rcases lookupColIdx?_of_find? hfind with ⟨idx, hlk, hgetIdx⟩
        have hiEq := distinctIdents_idx_unique huniq hci hgetIdx rfl; subst hiEq
        let rec getEq (ks : List Ident) (kv0 : List Val) (hm : origC.name ∈ ks)
            (h1 : extractKeyVals.go tt.cols a ks = some kv0) (h2 : extractKeyVals.go tt.cols b ks = some kv0) :
            a.cells[i]? = b.cells[i]? := by
          cases ks with
          | nil => nomatch hm
          | cons k0 rest =>
            unfold extractKeyVals.go at h1 h2; simp only [bind, Option.bind] at h1 h2
            cases hlk0 : lookupColIdx? tt.cols k0 with
            | none => rw [hlk0] at h1; contradiction
            | some p0 =>
              rcases p0 with ⟨i0, _⟩; rw [hlk0] at h1 h2; dsimp only at h1 h2
              cases ca : a.cells[i0]? <;> rw [ca] at h1 <;> try contradiction
              cases cb : b.cells[i0]? <;> rw [cb] at h2 <;> try contradiction
              dsimp only at h1 h2
              cases ta : extractKeyVals.go tt.cols a rest <;> rw [ta] at h1 <;> try contradiction
              cases tb : extractKeyVals.go tt.cols b rest <;> rw [tb] at h2 <;> try contradiction
              injection h1 with e1; injection h2 with e2; subst e2; injection e1 with eh et
              rcases List.mem_cons.mp hm with rfl | hrest
              · rw [hlk] at hlk0; injection hlk0 with hpEq; injection hpEq with ei _; subst ei; rw [ca, cb, eh]
              · exact getEq rest _ hrest ta (et ▸ tb)
        exact getEq keys kv hkMem haKv hbKv
  · -- Low `orderTags`: lockstep `insertionSortBy_forall2`
    have hlr := ht.lowRows hrLow
    simp only [hord, ↓reduceIte] at hlr
    have hmap : RelList (RowEquiv L tt.cols) (tv1.rows.map resetGM) (tv2.rows.map resetGM) :=
      hlr.map resetGM resetGM (fun _ _ h => h)
    have hsortLow : ∀ p ∈ sortSpec, ∀ c, tt.cols.find? (fun x => x.name == p.1) = some c → c.tags.subset L = true := by
      intro p hp c hfc; rw [List.mem_map] at hp; rcases hp with ⟨k, hk, rfl⟩
      exact hkeysLow k hk c hfc
    have hs := insertionSortBy_forall2 (R := RowEquiv L tt.cols)
      (fun _ _ _ _ ha hb => rowLtByKeys_congr_of_low ha hb hsortLow) hmap
    apply hs.imp
    intro _ _ hr
    apply cellsEquiv_map_tags _ hr
    intro c _ hsub
    split at hsub
    · exact hsub
    · simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hsub; exact hsub.1.1

theorem pivotWider_lowRows {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true)
    {tv1 tv2 : TableVal} {tt : TableTy}
    {namesFrom valuesFrom : Ident} {nCol vCol : ColSpec} {nIdx vIdx : Nat}
    {staticCols : List Ident} {fillVal : Val}
    {rawIds1 rawIds2 : List (List Val)}
    (ht : TableEquiv prog L tv1 tv2 tt)
    (hrLow : tt.rowTags.subset L = true)
    (hnGet : tt.cols[nIdx]? = some nCol) (hvGet : tt.cols[vIdx]? = some vCol)
    (hnLow : nCol.tags.subset L = true)
    (hidLow : ∀ k ∈ ((tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map ColSpec.name),
      ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true)
    (hext1 : extractAllRowsKeyVals tv1.cols ((tv1.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun (c : ColSpec) => ({ c with aggKind := .raw } : ColSpec).name)) tv1.rows = some rawIds1)
    (hext2 : extractAllRowsKeyVals tv2.cols ((tv2.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun (c : ColSpec) => ({ c with aggKind := .raw } : ColSpec).name)) tv2.rows = some rawIds2) :
    let idCols := (tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun c => { c with aggKind := .raw })
    let idNames := idCols.map ColSpec.name
    let idTags := TagSet.unionList (idCols.map ColSpec.tags)
    let newRowTags := (tt.rowTags.union nCol.tags).union idTags
    let cellTags := ((nCol.tags.union vCol.tags).union newRowTags).union tt.orderTags
    let pivotedCols := staticCols.map (fun sc => ({ name := sc, ty := vCol.ty, tags := cellTags, bucketed := false, aggKind := .raw } : ColSpec))
    let mkRows (tv : TableVal) (uids : List (List Val)) : List TableRow :=
      uids.map (fun idKey =>
        let pRows := tv.rows.filter (fun r => match extractKeyVals tv.cols idNames r with | some kv => valListEq kv idKey | none => false)
        let pivCells := staticCols.map (fun sc =>
          match pRows.find? (fun r => match (r.cells[nIdx]? : Option Val) with | some (.text s) => s == sc | _ => false) with
          | some mr => mr.cells[vIdx]?.getD fillVal | none => fillVal)
        { cells := idKey ++ pivCells, groupMeta := none })
    RelList (RowEquiv L (idCols ++ pivotedCols))
      (mkRows tv1 (dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds1)))
      (mkRows tv2 (dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds2))) := by
  intro idCols idNames idTags newRowTags cellTags pivotedCols mkRows
  rcases ht.cols_eq with ⟨hc1, hc2⟩
  cases ht.wf1 with | table _ hsch hrWf1 =>
  have huniq := (tableSchemaWf_cols_props hsch).1
  have hcols := fun c hc => (tableSchemaWf_cols_props hsch).2 c hc |>.1
  have hidNamesEq : ((tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun (c : ColSpec) => ({ c with aggKind := .raw } : ColSpec).name)) = idNames := by
    dsimp only [idNames, idCols]; rw [List.map_map]; rfl
  rw [hc1, hidNamesEq] at hext1; rw [hc2, hidNamesEq] at hext2
  have hidLow' : ∀ k ∈ idNames, ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
    intro k hk; dsimp only [idNames, idCols] at hk
    rw [List.map_map] at hk; exact hidLow k hk
  rcases extractAllRowsKeyVals_eq_filterMap tt.cols idNames hext1 with ⟨hfm1, _⟩
  rcases extractAllRowsKeyVals_eq_filterMap tt.cols idNames hext2 with ⟨hfm2, _⟩
  rcases ht.perm_rows hrLow with ⟨rows1', hp, hrelP⟩
  have hpRaw : List.Perm rawIds1 rawIds2 := by
    rw [hfm1, hfm2]
    have heq' := RelList.filterMap_congr (R := RowEquiv L tt.cols)
      (fun a b hr => extractKeyVals_congr_of_low hr hidLow') hrelP
    exact heq' ▸ perm_filterMap _ hp
  have hrawSort : ∀ kv ∈ rawIds1, SortableValList kv := by
    intro kv hkv; rw [hfm1, List.mem_filterMap] at hkv; rcases hkv with ⟨r, hr, hkvEq⟩
    exact extractKeyVals_sortable hd hcols (hrWf1.to_forall r hr) hkvEq
  have huidsEq : dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds1) =
      dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds2) :=
    congrArg (dedupAdjacentBy valListEq)
      (insertionSortBy_perm_eq valListLt_irrefl valListLt_trans valListLt_trichotomy hrawSort hpRaw)
  rw [← huidsEq]
  have hidKeyProps : ∀ kc ∈ idCols, ∃ origC, tt.cols.find? (fun c => c.name == kc.name) = some origC ∧ origC.ty = kc.ty := by
    intro kc hkc; dsimp only [idCols] at hkc; rw [List.mem_map] at hkc
    rcases hkc with ⟨orig, horigF, rfl⟩
    exact ⟨orig, find_unique_of_mem huniq (List.mem_filter.mp horigF).1, rfl⟩
  rcases extractAllRowsKeyVals_typed hidKeyProps tv1.rows hrWf1.to_forall with ⟨rawIds1', hext1', hrawWf⟩
  rw [hext1] at hext1'; injection hext1' with er; subst er
  have huidsLen : ∀ idKey ∈ dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds1), idKey.length = idCols.length := by
    intro idKey hmem
    have h1 := mem_dedupAdjacentBy valListEq idKey _ hmem
    have h2 := mem_insertionSortBy valListLt idKey rawIds1 h1
    exact (hrawWf idKey h2).length_eq
  dsimp only [mkRows]
  generalize dedupAdjacentBy valListEq (insertionSortBy valListLt rawIds1) = uids at huidsLen ⊢
  induction uids with
  | nil => exact .nil
  | cons idKey restU ih =>
    refine .cons ?_ (ih fun u hu => huidsLen u (.tail _ hu))
    unfold RowEquiv; dsimp only
    apply (CellsEquiv.of_all_eq idCols idKey (huidsLen idKey (.head _))).append
    cases hcLow : cellTags.subset L
    · exact CellsEquiv.of_high_cols (by simp [pivotedCols]) (by simp [pivotedCols])
        (fun c hc => by dsimp only [pivotedCols] at hc; rw [List.mem_map] at hc; rcases hc with ⟨_, _, rfl⟩; exact hcLow)
    · have hcLow' := hcLow
      dsimp only [cellTags] at hcLow'
      simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hcLow'
      have hvLow : vCol.tags.subset L = true := hcLow'.1.1.2
      have hordLow : tt.orderTags.subset L = true := hcLow'.2
      have hlr := ht.lowRows hrLow
      simp only [hordLow, ↓reduceIte] at hlr
      rw [hc1, hc2]
      have hpRowsRel : RelList (RowEquiv L tt.cols)
          (tv1.rows.filter (fun r => match extractKeyVals tt.cols idNames r with | some kv => valListEq kv idKey | none => false))
          (tv2.rows.filter (fun r => match extractKeyVals tt.cols idNames r with | some kv => valListEq kv idKey | none => false)) :=
        hlr.filter_congr (fun _ _ hr => by rw [extractKeyVals_congr_of_low hr hidLow'])
      have hpivEq : staticCols.map (fun sc =>
          match (tv1.rows.filter (fun r => match extractKeyVals tt.cols idNames r with | some kv => valListEq kv idKey | none => false)).find?
            (fun r => match (r.cells[nIdx]? : Option Val) with | some (.text s) => s == sc | _ => false) with
          | some mr => mr.cells[vIdx]?.getD fillVal | none => fillVal) =
          staticCols.map (fun sc =>
          match (tv2.rows.filter (fun r => match extractKeyVals tt.cols idNames r with | some kv => valListEq kv idKey | none => false)).find?
            (fun r => match (r.cells[nIdx]? : Option Val) with | some (.text s) => s == sc | _ => false) with
          | some mr => mr.cells[vIdx]?.getD fillVal | none => fillVal) := by
        apply List.map_congr_left
        intro sc _
        rcases hpRowsRel.find?_rel
          (p1 := fun (r : TableRow) => match (r.cells[nIdx]? : Option Val) with | some (.text s) => s == sc | _ => false)
          (p2 := fun (r : TableRow) => match (r.cells[nIdx]? : Option Val) with | some (.text s) => s == sc | _ => false)
          (fun a b hr => by rw [hr.getElem?_eq hnGet hnLow]) with ⟨hf1, hf2⟩ | ⟨mr1, mr2, hf1, hf2, hmr⟩
        · rw [hf1, hf2]
        · rw [hf1, hf2]; dsimp only; rw [hmr.getElem?_eq hvGet hvLow]
      rw [hpivEq]
      exact CellsEquiv.of_all_eq pivotedCols _ (by simp [pivotedCols])

theorem crosstab_eq_of_low {L : TagSet} {cols : List ColSpec} {rows1 rows2 : List TableRow}
    {rCol cCol vCol : ColSpec} {rIdx cIdx vIdx : Nat}
    (rowsCol : Ident) (fillVal : Val)
    (hrel : RelList (RowEquiv L cols) rows1 rows2)
    (hrGet : cols[rIdx]? = some rCol) (hcGet : cols[cIdx]? = some cCol) (hvGet : cols[vIdx]? = some vCol)
    (hrLow : rCol.tags.subset L = true) (hcLow : cCol.tags.subset L = true) (hvLow : vCol.tags.subset L = true) :
    let rKeys (rs : List TableRow) := dedupAdjacentBy valEq (insertionSortBy valLt (rs.filterMap (fun r => r.cells[rIdx]?)))
    let cKeys (rs : List TableRow) := dedupAdjacentBy valEq (insertionSortBy valLt (rs.filterMap (fun r => r.cells[cIdx]?)))
    let headers (rs : List TableRow) := rowsCol :: (cKeys rs).map renderPublicVal
    let matrix (rs : List TableRow) := (rKeys rs).map (fun rk =>
      rk :: (cKeys rs).map (fun ck =>
        match rs.find? (fun r => match r.cells[rIdx]?, r.cells[cIdx]? with | some rv, some cv => valEq rv rk && valEq cv ck | _, _ => false) with
        | some mr => mr.cells[vIdx]?.getD fillVal | none => fillVal))
    headers rows1 = headers rows2 ∧ matrix rows1 = matrix rows2 := by
  intro rKeys cKeys headers matrix
  have hrFm : rows1.filterMap (fun r => r.cells[rIdx]?) = rows2.filterMap (fun r => r.cells[rIdx]?) :=
    hrel.filterMap_congr (fun _ _ hr => hr.getElem?_eq hrGet hrLow)
  have hcFm : rows1.filterMap (fun r => r.cells[cIdx]?) = rows2.filterMap (fun r => r.cells[cIdx]?) :=
    hrel.filterMap_congr (fun _ _ hr => hr.getElem?_eq hcGet hcLow)
  have hrkEq : rKeys rows1 = rKeys rows2 := by dsimp only [rKeys]; rw [hrFm]
  have hckEq : cKeys rows1 = cKeys rows2 := by dsimp only [cKeys]; rw [hcFm]
  refine ⟨by dsimp only [headers]; rw [hckEq], ?_⟩
  dsimp only [matrix]; rw [hrkEq, hckEq]
  apply List.map_congr_left
  intro rk _; congr 1
  apply List.map_congr_left
  intro ck _
  rcases hrel.find?_rel
    (p1 := fun (r : TableRow) => match r.cells[rIdx]?, r.cells[cIdx]? with | some rv, some cv => valEq rv rk && valEq cv ck | _, _ => false)
    (p2 := fun (r : TableRow) => match r.cells[rIdx]?, r.cells[cIdx]? with | some rv, some cv => valEq rv rk && valEq cv ck | _, _ => false)
    (fun a b hr => by rw [hr.getElem?_eq hrGet hrLow, hr.getElem?_eq hcGet hcLow]) with
    ⟨hf1, hf2⟩ | ⟨mr1, mr2, hf1, hf2, hmr⟩
  · rw [hf1, hf2]
  · rw [hf1, hf2]; dsimp only; rw [hmr.getElem?_eq hvGet hvLow]


/-! ## Part 4B.5: Mutual Big-Step Non-Interference (`Expr`, `JoinLoop`, `Plan`) -/

def OutcomeNormalOrJump : Outcome → Prop
  | .ok _ _ | .jumped _ _ _ => True
  | _ => False

theorem TableEquiv.of_planTy_valEquiv {prog : Program} {L pc : TagSet}
    {tv1 tv2 : TableVal} {tt : TableTy}
    (hpc : pc.subset L = true)
    (hv : ValEquiv prog L (.table tv1) (.table tv2) (PlanTy.toLTy pc (.table tt))) :
    TableEquiv prog L tv1 tv2 tt := by
  cases hv.payload hpc with | table hwide =>
  refine ⟨hwide.wf1.table_change_tags tt.rowTags tt.orderTags,
          hwide.wf2.table_change_tags tt.rowTags tt.orderTags, ?_, ?_, ?_⟩
  · intro hrLow
    exact hwide.groupingLow (by simp [hrLow, hpc])
  · intro hrLow
    have hlr := hwide.lowRows (by simp [hrLow, hpc])
    dsimp only at hlr
    have hoEq : (tt.orderTags.union pc).subset L = tt.orderTags.subset L := by simp [hpc]
    rwa [hoEq] at hlr
  · intro hsum hrLow
    have hsm := hwide.sumMetaEq hsum (by simp [hrLow, hpc])
    dsimp only at hsm
    have hoEq : (tt.orderTags.union pc).subset L = tt.orderTags.subset L := by simp [hpc]
    rwa [hoEq] at hsm

theorem ValListEquiv.getElem? {prog : Program} {L : TagSet} :
    ∀ {vs1 vs2 : List Val} {ltys : List LTy} {idx : Nat} {eLTy : LTy},
      ValListEquiv prog L vs1 vs2 ltys →
      ltys[idx]? = some eLTy →
      ∃ v1 v2, vs1[idx]? = some v1 ∧ vs2[idx]? = some v2 ∧ ValEquiv prog L v1 v2 eLTy
  | [], [], [], _, _, .nil, hget => by simp at hget
  | _ :: _, _ :: _, _ :: _, 0, _, .cons hv _, hget => by
    injection hget with e; subst e; exact ⟨_, _, rfl, rfl, hv⟩
  | _ :: _, _ :: _, _ :: _, n + 1, _, .cons _ htl, hget => htl.getElem? hget

theorem ValListEquiv.subtype_zip {prog : Program} {L : TagSet} :
    ∀ {vs1 vs2 : List Val} {as1 ps : List LTy},
      ValListEquiv prog L vs1 vs2 as1 →
      as1.length = ps.length →
      (∀ pair ∈ List.zip as1 ps, ltySubtype pair.1 pair.2 = true) →
      ValListEquiv prog L vs1 vs2 ps
  | [], [], [], [], .nil, _, _ => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons hv htl, hlen, hsub =>
    .cons (hv.subtype (hsub _ (.head _)))
      (htl.subtype_zip (Nat.succ.inj hlen) (fun p hp => hsub p (.tail _ hp)))

theorem ValListEquiv.addTags_subtype_zip {prog : Program} {L pc : TagSet} :
    ∀ {vs1 vs2 : List Val} {as1 ps : List LTy},
      ValListEquiv prog L vs1 vs2 as1 →
      as1.length = ps.length →
      (∀ pair ∈ List.zip as1 ps, ltySubtype (pair.1.addTags pc) pair.2 = true) →
      ValListEquiv prog L vs1 vs2 ps
  | [], [], [], [], .nil, _, _ => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons hv htl, hlen, hsub =>
    .cons ((hv.addTags pc).subtype (hsub _ (.head _)))
      (htl.addTags_subtype_zip (Nat.succ.inj hlen) (fun p hp => hsub p (.tail _ hp)))

theorem extendEnv_equiv {prog : Program} {L : TagSet} :
    ∀ {params : List (Ident × LTy)} {vs1 vs2 : List Val} {base1 base2 : Env},
      ltyListSinksAllowed L (params.map Prod.snd) = true →
      ValListEquiv prog L vs1 vs2 (params.map Prod.snd) →
      EnvEquiv prog L base1 base2 →
      EnvEquiv prog L
        ((List.zip params vs1).map (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v }) ++ base1)
        ((List.zip params vs2).map (fun ((pName, pLTy), v) => { name := pName, lty := pLTy, val := v }) ++ base2)
  | [], [], [], _, _, _, .nil, hbase => hbase
  | (_, _) :: _, _ :: _, _ :: _, _, _, hsink, .cons hv htl, hbase => by
    simp only [List.map_cons, ltyListSinksAllowed, Bool.and_eq_true] at hsink
    exact .cons hsink.1 hv (extendEnv_equiv hsink.2 htl hbase)

theorem EnvEquiv.reverse {prog : Program} {L : TagSet} :
    ∀ {e1 e2 : Env}, EnvEquiv prog L e1 e2 → EnvEquiv prog L e1.reverse e2.reverse
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hsink hv htl => by
    simp only [List.reverse_cons]
    exact htl.reverse.append (.cons hsink hv .nil)

theorem evalLiteral_equiv {prog : Program} {L pc : TagSet} {lit : Literal} {lty : LTy}
    (hsafe : litSafeForNI L lit = true)
    (hchk : checkLiteral prog pc lit = .ok lty) :
    ValEquiv prog L (evalLiteral lit) (evalLiteral lit) lty := by
  have _ := hsafe
  have hwf := checkLiteral_sound hchk
  have hs : valSafeForNI L (evalLiteral lit) = true := by cases lit <;> rfl
  apply ValEquiv.mk_smart hwf hwf hs hs
  intro _
  cases lit <;> simp only [checkLiteral] at hchk
  all_goals (try (split at hchk <;> try contradiction))
  all_goals (injection hchk with e; subst e; dsimp only [evalLiteral, LTy.ty])
  · exact .unit
  · exact .bool _
  · exact .int _
  · exact .decimal _
  · exact .float _
  · exact .text _
  · exact .bytes _
  · exact .date _
  · exact .timestamp _
  · exact .duration _
  · exact .optNone _

theorem caseArmsSafeForNI_mem {L : TagSet} {cName : Ident} {binders : List Ident} {body : Expr} :
    ∀ {arms : List CaseArm},
      caseArmsSafeForNI L arms = true →
      CaseArm.mk cName binders body ∈ arms →
      exprSafeForNI L body = true
  | [], _, hm => nomatch hm
  | .mk _ _ _ :: _, hc, hm => by
    simp only [caseArmsSafeForNI, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hm with heq | htl
    · injection heq with _ _ hb; subst hb; exact hc.1
    · exact caseArmsSafeForNI_mem hc.2 htl

theorem envSafeForNI_armEntries {prog : Program} {L armPc : TagSet}
    (binders : List Ident) {sVal : Val} {scrutLTy : LTy} {cName : Ident}
    {typedVals : List (LTy × Val)} {base : Env}
    (hprog : progSafeForNI prog L = true)
    (hscrutSink : ltySinksAllowed L scrutLTy = true)
    (hsValSafe : valSafeForNI L sVal = true)
    (hm : matchCaseVal prog sVal scrutLTy armPc = some (cName, typedVals))
    (hbase : envSafeForNI L base = true) :
    envSafeForNI L ((List.zip binders typedVals).map
      (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ base) = true := by
  have hp := matchCaseVal_safeForNI hprog hscrutSink hsValSafe hm
  let rec go (bs : List Ident) (tvs : List (LTy × Val))
      (htvs : ∀ p ∈ tvs, ltySinksAllowed L p.1 = true ∧ valSafeForNI L p.2 = true) :
      envSafeForNI L ((List.zip bs tvs).map
        (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ base) = true := by
    cases bs with
    | nil => exact hbase
    | cons _ bsTl =>
      cases tvs with
      | nil => exact hbase
      | cons tv tvsTl =>
        rcases htvs tv (.head _) with ⟨h1, h2⟩
        simp [List.zip_cons_cons, envSafeForNI, h1, h2, go bsTl tvsTl (fun q hq => htvs q (.tail _ hq))]
  exact go binders typedVals hp

theorem matchCaseVal_ni {prog : Program} {L armPc : TagSet}
    {sVal1 sVal2 : Val} {scrutLTy : LTy}
    {cName1 cName2 : Ident} {tvs1 tvs2 : List (LTy × Val)}
    (hsink : ltySinksAllowed L scrutLTy = true)
    (hsProg : progSafeForNI prog L = true)
    (heffLow : scrutLTy.effectiveTags.subset L = true)
    (hv : ValEquiv prog L sVal1 sVal2 scrutLTy)
    (hm1 : matchCaseVal prog sVal1 scrutLTy armPc = some (cName1, tvs1))
    (hm2 : matchCaseVal prog sVal2 scrutLTy armPc = some (cName2, tvs2)) :
    cName1 = cName2 ∧
    ∀ binders, EnvEquiv prog L
      ((List.zip binders tvs1).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }))
      ((List.zip binders tvs2).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) := by
  have htagsLow : scrutLTy.tags.subset L = true :=
    TagSet.subset_trans scrutLTy.tags_subset_effectiveTags heffLow
  have hpay := hv.payload htagsLow
  unfold matchCaseVal at hm1 hm2
  cases scrutLTy with | mk sty sts =>
  dsimp only [LTy.ty] at hpay hm1 hm2
  have hzipEmpty : ∀ bs, EnvEquiv prog L
      ((List.zip bs ([] : List (LTy × Val))).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }))
      ((List.zip bs ([] : List (LTy × Val))).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) := by
    intro bs; cases bs <;> exact .nil
  have hzipOne : ∀ (l : LTy) (u1 u2 : Val), ltySinksAllowed L l = true → ValEquiv prog L u1 u2 l →
      ∀ bs, EnvEquiv prog L
        ((List.zip bs [(l, u1)]).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }))
        ((List.zip bs [(l, u2)]).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) := by
    intro l u1 u2 hl hu bs
    cases bs with
    | nil => exact .nil
    | cons b rest => cases rest <;> exact .cons hl hu .nil
  cases hpay with
  | bool b =>
    cases b <;> (injection hm1 with e1; injection hm2 with e2; rcases e1 with ⟨rfl, rfl⟩; rcases e2 with ⟨rfl, rfl⟩; exact ⟨rfl, hzipEmpty⟩)
  | optNone _ =>
    injection hm1 with e1; injection hm2 with e2; rcases e1 with ⟨rfl, rfl⟩; rcases e2 with ⟨rfl, rfl⟩; exact ⟨rfl, hzipEmpty⟩
  | @optSome u1 u2 inner hu =>
    injection hm1 with e1; injection hm2 with e2; rcases e1 with ⟨rfl, rfl⟩; rcases e2 with ⟨rfl, rfl⟩
    cases hv.wf_left with | optSome hw1 =>
    cases hv.wf_right with | optSome hw2 =>
    have hs1 : valSafeForNI L u1 = true := hv.safe_left
    have hs2 : valSafeForNI L u2 = true := hv.safe_right
    exact ⟨rfl, hzipOne _ u1 u2 hsink (ValEquiv.mk_smart hw1 hw2 hs1 hs2 (fun _ => hu))⟩
  | @resOk u1 u2 okTy errTy hu =>
    injection hm1 with e1; injection hm2 with e2; rcases e1 with ⟨rfl, rfl⟩; rcases e2 with ⟨rfl, rfl⟩
    cases hv.wf_left with | resOk hw1 =>
    cases hv.wf_right with | resOk hw2 =>
    simp only [ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hsink
    exact ⟨rfl, hzipOne _ u1 u2 hsink.1 (ValEquiv.mk_smart hw1 hw2 hv.safe_left hv.safe_right (fun _ => hu))⟩
  | @resErr u1 u2 okTy errTy he =>
    injection hm1 with e1; injection hm2 with e2; rcases e1 with ⟨rfl, rfl⟩; rcases e2 with ⟨rfl, rfl⟩
    cases hv.wf_left with | resErr hw1 =>
    cases hv.wf_right with | resErr hw2 =>
    simp only [ltySinksAllowed, tySinksAllowed, Bool.and_eq_true] at hsink
    exact ⟨rfl, hzipOne _ u1 u2 hsink.2 (ValEquiv.mk_smart hw1 hw2 hv.safe_left hv.safe_right (fun _ => he))⟩
  | @ctor dName cName vs1 vs2 dDecl cDecl hfd hfc _ hvs =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfd, hfc] at hm1 hm2
    rcases hvs.length_eq with ⟨hl1, hl2⟩
    simp only [hl1, hl2, beq_self_eq_true, ↓reduceIte] at hm1 hm2
    injection hm1 with e1; injection hm2 with e2; rcases e1 with ⟨rfl, rfl⟩; rcases e2 with ⟨rfl, rfl⟩
    have hcSinks : ltyListSinksAllowed L cDecl.fields = true := by
      simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hsProg
      exact hsProg.1.1.2 dDecl (List.mem_of_find?_eq_some hfd) cDecl (List.mem_of_find?_eq_some hfc)
    refine ⟨rfl, ?_⟩
    intro binders
    let sTags := (LTy.mk (.data dName) sts).effectiveTags.union armPc
    let rec goZip (bs : List Ident) {fs : List LTy} {xs1 xs2 : List Val}
        (hfs : ltyListSinksAllowed L fs = true) (hx : ValListEquiv prog L xs1 xs2 fs) :
        EnvEquiv prog L
          ((List.zip bs (List.zip (fs.map (fun f => f.addTags sTags)) xs1)).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }))
          ((List.zip bs (List.zip (fs.map (fun f => f.addTags sTags)) xs2)).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) := by
      cases bs with
      | nil => exact .nil
      | cons b restB =>
        cases hx with
        | nil => exact .nil
        | cons hvHd htl =>
          simp only [ltyListSinksAllowed, Bool.and_eq_true] at hfs
          exact .cons (by simp [hfs.1]) (hvHd.addTags sTags) (goZip restB hfs.2 htl)
    exact goZip binders hcSinks hvs
  | _ => contradiction

theorem joinOutcomeEquiv_of_high {prog : Program} {L : TagSet} {jenv : JoinEnv}
    {lty : LTy} {w1 w2 : World} {out1 out2 : Outcome}
    (hw : WorldEquiv prog L w1 w2)
    (hhigh : lty.tags.subset L = false)
    (hnj1 : OutcomeNormalOrJump out1) (hnj2 : OutcomeNormalOrJump out2)
    (hw1Eq : outWorld out1 = w1) (hw2Eq : outWorld out2 = w2)
    (hok1 : ∀ v w', out1 = .ok v w' → ValWf prog v lty.ty ∧ valSafeForNI L v = true)
    (hok2 : ∀ v w', out2 = .ok v w' → ValWf prog v lty.ty ∧ valSafeForNI L v = true)
    (hjp1 : ∀ lbl vs w', out1 = .jumped lbl vs w' → ∃ sig, lookupJoinEnv jenv lbl = some sig ∧ sig.joinPc.subset L = false)
    (hjp2 : ∀ lbl vs w', out2 = .jumped lbl vs w' → ∃ sig, lookupJoinEnv jenv lbl = some sig ∧ sig.joinPc.subset L = false) :
    JoinOutcomeEquiv prog L jenv lty out1 out2 := by
  refine ⟨by rw [hw1Eq, hw2Eq]; exact hw, ?_⟩
  cases h1 : out1 <;> rw [h1] at hnj1 <;> try contradiction
  all_goals (cases h2 : out2 <;> rw [h2] at hnj2 <;> try contradiction)
  · exact .high hhigh (hok1 _ _ h1).1 (hok2 _ _ h2).1 (hok1 _ _ h1).2 (hok2 _ _ h2).2
  · exact ⟨hhigh, hjp2 _ _ _ h2⟩
  · exact ⟨hjp1 _ _ _ h1, hhigh⟩
  · exact Or.inr ⟨hjp1 _ _ _ h1, hjp2 _ _ _ h2⟩

def ExprNIAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ (env1 env2 : Env) (jenv : JoinEnv) (pc : TagSet) (inSpec : Bool)
    (w1 w2 : World) (e : Expr) (lty : LTy),
    EnvEquiv prog L env1 env2 →
    joinEnvSinksAllowed L jenv = true →
    (∀ p ∈ jenv, p.2.joinPc.subset p.2.retLTy.tags = true) →
    WorldEquiv prog L w1 w2 →
    progRespectsDB w1 prog →
    progRespectsDB w2 prog →
    envClosureSafe prog L w1 env1 →
    envClosureSafe prog L w2 env2 →
    exprSafeForNI L e = true →
    exprNoSpecCalls prog e = true →
    exprSuppressSafe prog L (envToTyEnv env1) pc e = true →
    exprRespectsDB w1 e →
    exprRespectsDB w2 e →
    checkExpr prog (envToTyEnv env1) jenv pc inSpec e = .ok lty →
    OutcomeNormalOrJump (eval fuel prog env1 pc w1 e) →
    OutcomeNormalOrJump (eval fuel prog env2 pc w2 e) →
    JoinOutcomeEquiv prog L jenv lty (eval fuel prog env1 pc w1 e) (eval fuel prog env2 pc w2 e)

def JoinLoopNIAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ (baseEnv1 baseEnv2 curEnv1 curEnv2 : Env) (jenv : JoinEnv)
    (label : Ident) (params : List (Ident × LTy)) (joinPc : TagSet)
    (retLTy rLTy : LTy) (inSpec : Bool) (rhs : Expr) (w1 w2 : World),
    EnvEquiv prog L baseEnv1 baseEnv2 →
    EnvEquiv prog L curEnv1 curEnv2 →
    envToTyEnv curEnv1 = extendTyEnv (envToTyEnv baseEnv1) params →
    joinEnvSinksAllowed L jenv = true →
    (∀ p ∈ jenv, p.2.joinPc.subset p.2.retLTy.tags = true) →
    ltyListSinksAllowed L (params.map Prod.snd) = true →
    ltySinksAllowed L retLTy = true →
    joinPc.subset retLTy.tags = true →
    ltySubtype rLTy retLTy = true →
    WorldEquiv prog L w1 w2 →
    progRespectsDB w1 prog →
    progRespectsDB w2 prog →
    envClosureSafe prog L w1 baseEnv1 →
    envClosureSafe prog L w2 baseEnv2 →
    envClosureSafe prog L w1 curEnv1 →
    envClosureSafe prog L w2 curEnv2 →
    exprSafeForNI L rhs = true →
    exprNoSpecCalls prog rhs = true →
    exprSuppressSafe prog L (extendTyEnv (envToTyEnv baseEnv1) params) joinPc rhs = true →
    exprRespectsDB w1 rhs →
    exprRespectsDB w2 rhs →
    checkExpr prog (extendTyEnv (envToTyEnv baseEnv1) params)
      ((label, { params := params, joinPc := joinPc, retLTy := retLTy }) :: jenv)
      joinPc inSpec rhs = .ok rLTy →
    OutcomeNormalOrJump (evalJoinLoop fuel prog baseEnv1 label params joinPc rhs curEnv1 w1) →
    OutcomeNormalOrJump (evalJoinLoop fuel prog baseEnv2 label params joinPc rhs curEnv2 w2) →
    JoinOutcomeEquiv prog L jenv retLTy
      (evalJoinLoop fuel prog baseEnv1 label params joinPc rhs curEnv1 w1)
      (evalJoinLoop fuel prog baseEnv2 label params joinPc rhs curEnv2 w2)

def PlanNIAt (fuel : Nat) (prog : Program) (L : TagSet) : Prop :=
  checkProgram prog = .ok () →
  progSafeForNI prog L = true →
  ∀ (env1 env2 : Env) (pc : TagSet) (inSpec : Bool) (w1 w2 : World)
    (plan : Plan) (pTy : PlanTy) (v1 v2 : Val) (w1' w2' : World),
    EnvEquiv prog L env1 env2 →
    WorldEquiv prog L w1 w2 →
    progRespectsDB w1 prog →
    progRespectsDB w2 prog →
    envClosureSafe prog L w1 env1 →
    envClosureSafe prog L w2 env2 →
    planSafeForNI L plan = true →
    planNoSpecCalls prog plan = true →
    planSuppressSafe prog L (envToTyEnv env1) pc plan = true →
    planRespectsDB w1 plan →
    planRespectsDB w2 plan →
    checkPlan prog (envToTyEnv env1) pc inSpec plan = .ok pTy →
    evalPlan fuel prog env1 pc w1 plan = .ok v1 w1' →
    evalPlan fuel prog env2 pc w2 plan = .ok v2 w2' →
    ValEquiv prog L v1 v2 (pTy.toLTy pc) ∧ WorldEquiv prog L w1' w2'

theorem evalSeq_ni {fuel : Nat} {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {env1 env2 : Env}
    (ihE : ExprNIAt fuel prog L)
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2) :
    ∀ {es : List Expr} {ltys : List LTy} {w1 w2 w1' w2' : World} {vs1 vs2 : List Val},
      WorldEquiv prog L w1 w2 →
      progRespectsDB w1 prog →
      progRespectsDB w2 prog →
      envClosureSafe prog L w1 env1 →
      envClosureSafe prog L w2 env2 →
      exprListSafeForNI L es = true →
      exprListNoSpecCalls prog es = true →
      exprListSuppressSafe prog L (envToTyEnv env1) pc es = true →
      listRespectsDB w1 es →
      listRespectsDB w2 es →
      checkExprList prog (envToTyEnv env1) pc inSpec es = .ok ltys →
      evalSeq (eval fuel prog env1 pc) w1 es = .ok vs1 w1' →
      evalSeq (eval fuel prog env2 pc) w2 es = .ok vs2 w2' →
      ValListEquiv prog L vs1 vs2 ltys ∧ WorldEquiv prog L w1' w2'
  | [], _, _, _, _, _, _, _, hw, _, _, _, _, _, _, _, _, _, hchk, hs1, hs2 => by
    unfold checkExprList at hchk; injection hchk with e; subst e
    injection hs1 with ev1 ew1; injection hs2 with ev2 ew2
    subst ev1; subst ev2; subst ew1; subst ew2; exact ⟨.nil, hw⟩
  | e :: rest, _, w1, w2, _, _, _, _, hw, hp1, hp2, hc1, hc2, hes, hns, hsup, hr1, hr2, hchk, hs1, hs2 => by
    simp only [exprListSafeForNI, Bool.and_eq_true] at hes
    simp only [exprListNoSpecCalls, Bool.and_eq_true] at hns
    simp only [exprListSuppressSafe, Bool.and_eq_true] at hsup
    rcases hr1 with ⟨hre1, hrr1⟩; rcases hr2 with ⟨hre2, hrr2⟩
    unfold checkExprList at hchk; simp only [bind, Except.bind] at hchk
    cases he : checkExpr prog (envToTyEnv env1) [] pc inSpec e <;> rw [he] at hchk <;> try contradiction
    rename_i hdLTy; dsimp only at hchk
    cases ht : checkExprList prog (envToTyEnv env1) pc inSpec rest <;> rw [ht] at hchk <;> try contradiction
    injection hchk with el; subst el
    simp only [evalSeq] at hs1 hs2
    cases ho1 : eval fuel prog env1 pc w1 e <;> rw [ho1] at hs1 <;> try contradiction
    cases ho2 : eval fuel prog env2 pc w2 e <;> rw [ho2] at hs2 <;> try contradiction
    rename_i v1 wm1 v2 wm2; dsimp only at hs1 hs2
    cases htl1 : evalSeq (eval fuel prog env1 pc) wm1 rest <;> rw [htl1] at hs1 <;> try contradiction
    cases htl2 : evalSeq (eval fuel prog env2 pc) wm2 rest <;> rw [htl2] at hs2 <;> try contradiction
    injection hs1 with ev1 ew1; injection hs2 with ev2 ew2; subst ev1; subst ev2; subst ew1; subst ew2
    have hhdEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 e hdLTy henv rfl (fun _ hm => nomatch hm)
      hw hp1 hp2 hc1 hc2 hes.1 hns.1 hsup.1 hre1 hre2 he (by rw [ho1]; trivial) (by rw [ho2]; trivial)
    rw [ho1, ho2] at hhdEq; rcases hhdEq with ⟨hwm, hvEq⟩
    have hdb1 := (eval_preserves_db_all prog L fuel).1 hprog hsafeProg env1 pc w1 e hp1 hc1 hes.1 hns.1 hsup.1 hre1
    have hdb2 := (eval_preserves_db_all prog L fuel).1 hprog hsafeProg env2 pc w2 e hp2 hc2 hes.1 hns.1 (henv.envToTyEnv_eq ▸ hsup.1) hre2
    rw [ho1] at hdb1; rw [ho2] at hdb2
    rcases evalSeq_ni ihE hprog hsafeProg henv hwm
      (progRespectsDB_congr hdb1.2 hp1) (progRespectsDB_congr hdb2.2 hp2)
      (envClosureSafe_congr hdb1.2 hc1) (envClosureSafe_congr hdb2.2 hc2)
      hes.2 hns.2 hsup.2 (listRespectsDB_congr hdb1.2 hrr1) (listRespectsDB_congr hdb2.2 hrr2)
      ht htl1 htl2 with ⟨htlVs, hwFinal⟩
    exact ⟨.cons hvEq htlVs, hwFinal⟩

private theorem evalSeq_aborted_not_ok {step : World → Expr → Outcome} :
    ∀ {w : World} {es : List Expr} {v : Val} {w' : World},
      evalSeq step w es = .aborted (.ok v w') → False
  | _, [], _, _, h => nomatch h
  | w, e :: rest, _, _, h => by
    simp only [evalSeq] at h
    cases ho : step w e <;> rw [ho] at h
    · dsimp only at h
      cases htl : evalSeq step _ rest <;> rw [htl] at h
      · nomatch h
      · injection h with e1; subst e1; exact evalSeq_aborted_not_ok htl
    all_goals nomatch h

private theorem match_table_eq_ok {out : Outcome} {v : Val} {w : World}
    {f : TableVal → World → Outcome}
    (h : (match out with | .ok (.table tv) w1 => f tv w1 | .ok _ _ => .wrong | other => other) = .ok v w) :
    ∃ tv w1, out = .ok (.table tv) w1 ∧ f tv w1 = .ok v w := by
  cases out with
  | ok v0 w1 => cases v0 <;> first | contradiction | exact ⟨_, _, rfl, h⟩
  | _ => contradiction

private theorem match_capReadDB_eq_ok {out : Outcome} {v : Val} {w : World}
    {f : CapHandle → String → World → Outcome}
    (h : (match out with | .ok (.capReadDB ch db) w1 => f ch db w1 | .ok _ _ => .wrong | other => other) = .ok v w) :
    ∃ ch db w1, out = .ok (.capReadDB ch db) w1 ∧ f ch db w1 = .ok v w := by
  cases out with
  | ok v0 w1 => cases v0 <;> first | contradiction | exact ⟨_, _, _, rfl, h⟩
  | _ => contradiction

private theorem match_capSecret_eq_ok {out : Outcome} {v : Val} {w : World}
    {f : CapHandle → String → World → Outcome}
    (h : (match out with | .ok (.capSecret ch s) w1 => f ch s w1 | .ok _ _ => .wrong | other => other) = .ok v w) :
    ∃ ch s w1, out = .ok (.capSecret ch s) w1 ∧ f ch s w1 = .ok v w := by
  cases out with
  | ok v0 w1 => cases v0 <;> first | contradiction | exact ⟨_, _, _, rfl, h⟩
  | _ => contradiction

set_option maxHeartbeats 800000 in
private theorem expr_ni_step {prog : Program} {L : TagSet} {fuel' : Nat}
    (ihE : ExprNIAt fuel' prog L) (ihJL : JoinLoopNIAt fuel' prog L) (ihP : PlanNIAt fuel' prog L) :
    ExprNIAt (fuel' + 1) prog L := by
      have hsound := eval_fuel_sound prog (fuel' + 1)
      have hsound' := eval_fuel_sound prog fuel'
      have hsc := eval_safe_and_confined_all prog L (fuel' + 1)
      have hsc' := eval_safe_and_confined_all prog L fuel'
      have hjmp := eval_high_pc_jump_sig_all prog L (fuel' + 1)
      have hjmp' := eval_high_pc_jump_sig_all prog L fuel'
      have hdb' := eval_preserves_db_all prog L fuel'
      intro hprog hsafeProg env1 env2 jenv pc inSpec w1 w2 e lty
        henv hjenvSafe hjenvSub hw hprogDB1 hprogDB2 henvCl1 henvCl2 hesafe hens hesup her1 her2 hchk hnj1 hnj2
      have hchkOrig := hchk
      have hd : progDatasSortableForNI prog L = true := by
        simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
      have hchk2 : checkExpr prog (envToTyEnv env2) jenv pc inSpec e = .ok lty := by
        rwa [← henv.envToTyEnv_eq]
      have henvNs1 : envNoSpecCalls prog env1 = true := envClosureSafe_imp_noSpecCalls henvCl1
      have henvNs2 : envNoSpecCalls prog env2 = true := envClosureSafe_imp_noSpecCalls henvCl2
      -- Uniform discharge of ALL high-`pc` expressions (`pc ⊈ L`) before case-splitting `e`!
      cases hpc : pc.subset L
      · have hwfOut1 := hsound.2.2.1 hprog env1 jenv pc inSpec w1 e lty henv.wf_left hw.wf1 hchk
        have hwfOut2 := hsound.2.2.1 hprog env2 jenv pc inSpec w2 e lty henv.wf_right hw.wf2 hchk2
        rcases hsc.1 hprog hsafeProg env1 jenv pc inSpec w1 e lty henv.wf_left henv.safe_left henvNs1 hjenvSafe hw.wf1 hesafe hens hchk with ⟨hsOut1, _, hconf1⟩
        rcases hsc.1 hprog hsafeProg env2 jenv pc inSpec w2 e lty henv.wf_right henv.safe_right henvNs2 hjenvSafe hw.wf2 hesafe hens hchk2 with ⟨hsOut2, _, hconf2⟩
        have hpcSub := checkExpr_pc_subset_tags hjenvSub hchk
        have hltyHigh : lty.tags.subset L = false := by
          cases hs : lty.tags.subset L; rfl
          have := TagSet.subset_trans hpcSub hs; rw [hpc] at this; nomatch this
        apply joinOutcomeEquiv_of_high hw hltyHigh hnj1 hnj2
        · have hc := hconf1 hpc
          cases ho : eval (fuel' + 1) prog env1 pc w1 e <;> rw [ho] at hnj1 hc <;> try contradiction
          all_goals exact hc
        · have hc := hconf2 hpc
          cases ho : eval (fuel' + 1) prog env2 pc w2 e <;> rw [ho] at hnj2 hc <;> try contradiction
          all_goals exact hc
        · intro v w' ho; rw [ho] at hwfOut1 hsOut1; cases hwfOut1 with | ok hv _ => exact ⟨hv, hsOut1⟩
        · intro v w' ho; rw [ho] at hwfOut2 hsOut2; cases hwfOut2 with | ok hv _ => exact ⟨hv, hsOut2⟩
        · exact fun lbl vs w' ho => hjmp.1 hprog env1 jenv pc inSpec w1 e lty lbl vs w' henv.wf_left hw.wf1 hchk hpc ho
        · exact fun lbl vs w' ho => hjmp.1 hprog env2 jenv pc inSpec w2 e lty lbl vs w' henv.wf_right hw.wf2 hchk2 hpc ho
      -- Low `pc` (`pc ⊆ L`)
      · unfold eval at hnj1 hnj2 ⊢
        cases e with
        | lit lit =>
          exact ⟨hw, evalLiteral_equiv hesafe hchk⟩
        | var name =>
          unfold checkExpr at hchk
          cases hlt : lookupTyEnv (envToTyEnv env1) name <;> rw [hlt] at hchk <;> try contradiction
          injection hchk with el; subst el
          rcases henv.lookup hlt with ⟨v1, v2, hl1, hl2, hvEq⟩
          simp only [hl1, hl2]
          exact ⟨hw, hvEq.addTags pc⟩
        | constRef name =>
          unfold checkExpr at hchk
          cases hc : prog.findConst? name <;> rw [hc] at hchk <;> try contradiction
          rename_i cDecl; injection hchk with el; subst el
          simp only [hc]
          have hcAll := (checkProgram_parts hprog).2.2.1
          unfold checkConstDecls at hcAll; split at hcAll <;> try contradiction
          have hmem := List.mem_of_find?_eq_some hc
          have hcOk : ∃ vLTy, checkLiteral prog TagSet.empty cDecl.value = .ok vLTy ∧ ltySubtype vLTy cDecl.lty = true := by
            let rec go (cs : List ConstDecl) (hm : cDecl ∈ cs) (hg : checkConstDecls.go prog cs = .ok ()) :
                ∃ vLTy, checkLiteral prog TagSet.empty cDecl.value = .ok vLTy ∧ ltySubtype vLTy cDecl.lty = true := by
              cases cs with
              | nil => nomatch hm
              | cons d ds =>
                unfold checkConstDecls.go at hg; split at hg <;> try contradiction
                simp only [bind, Except.bind] at hg
                cases hl : checkLiteral prog TagSet.empty d.value <;> rw [hl] at hg <;> try contradiction
                dsimp only at hg; split at hg <;> try contradiction
                rcases List.mem_cons.mp hm with rfl | htl
                · exact ⟨_, hl, by assumption⟩
                · exact go ds htl hg
            exact go prog.consts hmem hcAll
          rcases hcOk with ⟨vLTy, hvChk, hvSub⟩
          have hcSafe : litSafeForNI L cDecl.value = true := by
            simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true] at hsafeProg
            exact (hsafeProg.1.2 cDecl hmem).2
          exact ⟨hw, ((evalLiteral_equiv hcSafe hvChk).subtype hvSub).addTags pc⟩
        | letE name declLTy bound body =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
          simp only [exprSuppressSafe, Bool.and_eq_true] at hesup
          rcases her1 with ⟨herB1, herBody1⟩; rcases her2 with ⟨herB2, herBody2⟩
          unfold checkExpr at hchk
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hb : checkExpr prog (envToTyEnv env1) [] pc inSpec bound <;> rw [hb] at hchk <;> try contradiction
          rename_i bLTy; dsimp only at hchk
          split at hchk <;> try contradiction
          rename_i hsub; simp only [Bool.not_eq_true', Bool.not_eq_false] at hsub
          have hbWf1 := hsound'.2.2.1 hprog env1 [] pc inSpec w1 bound bLTy henv.wf_left hw.wf1 hb
          have hbWf2 := hsound'.2.2.1 hprog env2 [] pc inSpec w2 bound bLTy henv.wf_right hw.wf2 (henv.envToTyEnv_eq ▸ hb)
          cases hoB1 : eval fuel' prog env1 pc w1 bound with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoB1] at hnj1; nomatch hnj1
          | jumped _ _ _ => rw [hoB1] at hbWf1; exact absurd rfl hbWf1.not_jumped_nil
          | ok bVal1 wb1 =>
            cases hoB2 : eval fuel' prog env2 pc w2 bound with
            | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoB2] at hnj2; nomatch hnj2
            | jumped _ _ _ => rw [hoB2] at hbWf2; exact absurd rfl hbWf2.not_jumped_nil
            | ok bVal2 wb2 =>
              rw [hoB1] at hnj1; rw [hoB2] at hnj2; dsimp only at hnj1 hnj2 ⊢
              have hbEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 bound bLTy
                henv rfl (fun _ hm => nomatch hm) hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe.1.2 hens.1 hesup.1 herB1 herB2 hb (by rw [hoB1]; trivial) (by rw [hoB2]; trivial)
              rw [hoB1, hoB2] at hbEq; rcases hbEq with ⟨hwb, hbValEq⟩
              have hbDb1 := hdb'.1 hprog hsafeProg env1 pc w1 bound hprogDB1 henvCl1 hesafe.1.2 hens.1 hesup.1 herB1
              have hbDb2 := hdb'.1 hprog hsafeProg env2 pc w2 bound hprogDB2 henvCl2 hesafe.1.2 hens.1 (henv.envToTyEnv_eq ▸ hesup.1) herB2
              rw [hoB1] at hbDb1; rw [hoB2] at hbDb2
              have hentryEq : EnvEquiv prog L
                  ({ name := name, lty := declLTy.addTags pc, val := bVal1 } :: env1)
                  ({ name := name, lty := declLTy.addTags pc, val := bVal2 } :: env2) :=
                .cons (by simp [hesafe.1.1]) ((hbValEq.subtype hsub).addTags pc) henv
              exact ihE hprog hsafeProg _ _ jenv pc inSpec wb1 wb2 body lty
                hentryEq hjenvSafe hjenvSub hwb
                (progRespectsDB_congr hbDb1.2 hprogDB1) (progRespectsDB_congr hbDb2.2 hprogDB2)
                ⟨valClosureSafe_congr hbDb1.2 hbDb1.1, envClosureSafe_congr hbDb1.2 henvCl1⟩
                ⟨valClosureSafe_congr hbDb2.2 hbDb2.1, envClosureSafe_congr hbDb2.2 henvCl2⟩
                hesafe.2 hens.2 hesup.2 (exprRespectsDB_congr hbDb1.2 herBody1) (exprRespectsDB_congr hbDb2.2 herBody2)
                hchk hnj1 hnj2
        | ifE cond tBr eBr =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
          unfold exprSuppressSafe at hesup
          cases hchkCF : checkExpr prog (envToTyEnv env1) [] pc false cond with
          | error _ => rw [hchkCF] at hesup; nomatch hesup
          | ok cLTyF =>
          rw [hchkCF] at hesup; simp only [Bool.and_eq_true] at hesup
          rcases her1 with ⟨herC1, herT1, herE1⟩; rcases her2 with ⟨herC2, herT2, herE2⟩
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hc : checkExpr prog (envToTyEnv env1) [] pc inSpec cond <;> rw [hc] at hchk <;> try contradiction
          rename_i cLTy; dsimp only at hchk
          have hcLTyEq : cLTyF = cLTy := by
            have h1 := checkExpr_inSpec_true hchkCF; rw [checkExpr_inSpec_true hc] at h1; exact (Except.ok.inj h1).symm
          subst hcLTyEq
          split at hchk <;> try contradiction
          rename_i hcBool; simp only [decide_eq_true_eq] at hcBool
          cases ht : checkExpr prog (envToTyEnv env1) jenv (pc.union cLTyF.tags) inSpec tBr <;> rw [ht] at hchk <;> try contradiction
          rename_i tLTy; dsimp only at hchk
          cases he : checkExpr prog (envToTyEnv env1) jenv (pc.union cLTyF.tags) inSpec eBr <;> rw [he] at hchk <;> try contradiction
          rename_i eLTy; dsimp only at hchk
          split at hchk <;> try contradiction
          rename_i hteTy; simp only [decide_eq_true_eq] at hteTy
          injection hchk with el; subst el
          have hc2 : checkExpr prog (envToTyEnv env2) [] pc inSpec cond = .ok cLTyF := henv.envToTyEnv_eq ▸ hc
          rw [checkExpr_inSpec_true hc] at hnj1 ⊢
          rw [checkExpr_inSpec_true hc2] at hnj2 ⊢
          dsimp only at hnj1 hnj2 ⊢
          have hcWf1 := hsound'.2.2.1 hprog env1 [] pc inSpec w1 cond cLTyF henv.wf_left hw.wf1 hc
          have hcWf2 := hsound'.2.2.1 hprog env2 [] pc inSpec w2 cond cLTyF henv.wf_right hw.wf2 hc2
          cases hoC1 : eval fuel' prog env1 pc w1 cond with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoC1] at hnj1; nomatch hnj1
          | jumped _ _ _ => rw [hoC1] at hcWf1; exact absurd rfl hcWf1.not_jumped_nil
          | ok cv1 wc1 =>
            cases hoC2 : eval fuel' prog env2 pc w2 cond with
            | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoC2] at hnj2; nomatch hnj2
            | jumped _ _ _ => rw [hoC2] at hcWf2; exact absurd rfl hcWf2.not_jumped_nil
            | ok cv2 wc2 =>
              rw [hoC1] at hcWf1; cases hcWf1 with | ok hcv1 hwc1 =>
              rw [hoC2] at hcWf2; cases hcWf2 with | ok hcv2 hwc2 =>
              rw [hcBool] at hcv1 hcv2
              cases hcv1 with | bool b1 =>
              cases hcv2 with | bool b2 =>
              have hcEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 cond cLTyF
                henv rfl (fun _ hm => nomatch hm) hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe.1.1 hens.1.1 hesup.1.1 herC1 herC2 hc (by rw [hoC1]; trivial) (by rw [hoC2]; trivial)
              rw [hoC1, hoC2] at hcEq; rcases hcEq with ⟨hwc, hcvEq⟩
              rw [hoC1] at hnj1; rw [hoC2] at hnj2
              cases hcLow : cLTyF.tags.subset L
              · -- High condition: both branches run at `pc.union cLTyF.tags ⊈ L`!
                have hbrHigh : (pc.union cLTyF.tags).subset L = false := by simp [hcLow]
                have hltyHigh : ((tLTy.tags.union eLTy.tags).union (pc.union cLTyF.tags)).subset L = false := by simp [hcLow]
                have hbr1Props : outWorld (if b1 then eval fuel' prog env1 (pc.union cLTyF.tags) wc1 tBr else eval fuel' prog env1 (pc.union cLTyF.tags) wc1 eBr) = wc1 ∧
                    (∀ v w', (if b1 then eval fuel' prog env1 (pc.union cLTyF.tags) wc1 tBr else eval fuel' prog env1 (pc.union cLTyF.tags) wc1 eBr) = .ok v w' → ValWf prog v tLTy.ty ∧ valSafeForNI L v = true) ∧
                    (∀ lbl vs w', (if b1 then eval fuel' prog env1 (pc.union cLTyF.tags) wc1 tBr else eval fuel' prog env1 (pc.union cLTyF.tags) wc1 eBr) = .jumped lbl vs w' → ∃ sig, lookupJoinEnv jenv lbl = some sig ∧ sig.joinPc.subset L = false) := by
                  cases b1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> dsimp only at hnj1
                  · have hwfB := hsound'.2.2.1 hprog env1 jenv _ inSpec wc1 eBr eLTy henv.wf_left hwc1 he
                    rcases hsc'.1 hprog hsafeProg env1 jenv _ inSpec wc1 eBr eLTy henv.wf_left henv.safe_left henvNs1 hjenvSafe hwc1 hesafe.2 hens.2 he with ⟨hsB, _, hcB⟩
                    have hcB' := hcB hbrHigh
                    refine ⟨by cases ho : eval fuel' prog env1 (pc.union cLTyF.tags) wc1 eBr <;> rw [ho] at hnj1 hcB' <;> first | contradiction | exact hcB',
                            fun v w' ho => by rw [ho] at hwfB hsB; cases hwfB with | ok hv _ => exact ⟨hteTy ▸ hv, hsB⟩,
                            fun lbl vs w' ho => hjmp'.1 hprog env1 jenv _ inSpec wc1 eBr eLTy lbl vs w' henv.wf_left hwc1 he hbrHigh ho⟩
                  · have hwfB := hsound'.2.2.1 hprog env1 jenv _ inSpec wc1 tBr tLTy henv.wf_left hwc1 ht
                    rcases hsc'.1 hprog hsafeProg env1 jenv _ inSpec wc1 tBr tLTy henv.wf_left henv.safe_left henvNs1 hjenvSafe hwc1 hesafe.1.2 hens.1.2 ht with ⟨hsB, _, hcB⟩
                    have hcB' := hcB hbrHigh
                    refine ⟨by cases ho : eval fuel' prog env1 (pc.union cLTyF.tags) wc1 tBr <;> rw [ho] at hnj1 hcB' <;> first | contradiction | exact hcB',
                            fun v w' ho => by rw [ho] at hwfB hsB; cases hwfB with | ok hv _ => exact ⟨hv, hsB⟩,
                            fun lbl vs w' ho => hjmp'.1 hprog env1 jenv _ inSpec wc1 tBr tLTy lbl vs w' henv.wf_left hwc1 ht hbrHigh ho⟩
                have hbr2Props : outWorld (if b2 then eval fuel' prog env2 (pc.union cLTyF.tags) wc2 tBr else eval fuel' prog env2 (pc.union cLTyF.tags) wc2 eBr) = wc2 ∧
                    (∀ v w', (if b2 then eval fuel' prog env2 (pc.union cLTyF.tags) wc2 tBr else eval fuel' prog env2 (pc.union cLTyF.tags) wc2 eBr) = .ok v w' → ValWf prog v tLTy.ty ∧ valSafeForNI L v = true) ∧
                    (∀ lbl vs w', (if b2 then eval fuel' prog env2 (pc.union cLTyF.tags) wc2 tBr else eval fuel' prog env2 (pc.union cLTyF.tags) wc2 eBr) = .jumped lbl vs w' → ∃ sig, lookupJoinEnv jenv lbl = some sig ∧ sig.joinPc.subset L = false) := by
                  have ht2 : checkExpr prog (envToTyEnv env2) jenv (pc.union cLTyF.tags) inSpec tBr = .ok tLTy := henv.envToTyEnv_eq ▸ ht
                  have he2 : checkExpr prog (envToTyEnv env2) jenv (pc.union cLTyF.tags) inSpec eBr = .ok eLTy := henv.envToTyEnv_eq ▸ he
                  cases b2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> dsimp only at hnj2
                  · have hwfB := hsound'.2.2.1 hprog env2 jenv _ inSpec wc2 eBr eLTy henv.wf_right hwc2 he2
                    rcases hsc'.1 hprog hsafeProg env2 jenv _ inSpec wc2 eBr eLTy henv.wf_right henv.safe_right henvNs2 hjenvSafe hwc2 hesafe.2 hens.2 he2 with ⟨hsB, _, hcB⟩
                    have hcB' := hcB hbrHigh
                    refine ⟨by cases ho : eval fuel' prog env2 (pc.union cLTyF.tags) wc2 eBr <;> rw [ho] at hnj2 hcB' <;> first | contradiction | exact hcB',
                            fun v w' ho => by rw [ho] at hwfB hsB; cases hwfB with | ok hv _ => exact ⟨hteTy ▸ hv, hsB⟩,
                            fun lbl vs w' ho => hjmp'.1 hprog env2 jenv _ inSpec wc2 eBr eLTy lbl vs w' henv.wf_right hwc2 he2 hbrHigh ho⟩
                  · have hwfB := hsound'.2.2.1 hprog env2 jenv _ inSpec wc2 tBr tLTy henv.wf_right hwc2 ht2
                    rcases hsc'.1 hprog hsafeProg env2 jenv _ inSpec wc2 tBr tLTy henv.wf_right henv.safe_right henvNs2 hjenvSafe hwc2 hesafe.1.2 hens.1.2 ht2 with ⟨hsB, _, hcB⟩
                    have hcB' := hcB hbrHigh
                    refine ⟨by cases ho : eval fuel' prog env2 (pc.union cLTyF.tags) wc2 tBr <;> rw [ho] at hnj2 hcB' <;> first | contradiction | exact hcB',
                            fun v w' ho => by rw [ho] at hwfB hsB; cases hwfB with | ok hv _ => exact ⟨hv, hsB⟩,
                            fun lbl vs w' ho => hjmp'.1 hprog env2 jenv _ inSpec wc2 tBr tLTy lbl vs w' henv.wf_right hwc2 ht2 hbrHigh ho⟩
                cases b1 <;> cases b2 <;>
                  simp only [Bool.false_eq_true, ↓reduceIte] at hbr1Props hbr2Props <;>
                  dsimp only at hnj1 hnj2 ⊢ <;>
                  exact joinOutcomeEquiv_of_high hwc hltyHigh hnj1 hnj2 hbr1Props.1 hbr2Props.1 hbr1Props.2.1 hbr2Props.2.1 hbr1Props.2.2 hbr2Props.2.2
              · -- Low condition (`cLTyF.tags ⊆ L`): `b1 = b2`!
                have hpay := hcvEq.payload hcLow
                rw [hcBool] at hpay; cases hpay
                have hcDb1 := hdb'.1 hprog hsafeProg env1 pc w1 cond hprogDB1 henvCl1 hesafe.1.1 hens.1.1 hesup.1.1 herC1
                have hcDb2 := hdb'.1 hprog hsafeProg env2 pc w2 cond hprogDB2 henvCl2 hesafe.1.1 hens.1.1 (henv.envToTyEnv_eq ▸ hesup.1.1) herC2
                rw [hoC1] at hcDb1; rw [hoC2] at hcDb2
                cases b1
                · dsimp only at hnj1 hnj2 ⊢
                  have hsubE : ltySubtype eLTy (.mk tLTy.ty ((tLTy.tags.union eLTy.tags).union (pc.union cLTyF.tags))) = true := by
                    unfold ltySubtype; rw [Bool.and_eq_true]
                    exact ⟨decide_eq_true hteTy.symm, TagSet.subset_trans (TagSet.subset_union_right tLTy.tags eLTy.tags) (TagSet.subset_union_left _ _)⟩
                  exact (ihE hprog hsafeProg env1 env2 jenv _ inSpec wc1 wc2 eBr eLTy
                    henv hjenvSafe hjenvSub hwc
                    (progRespectsDB_congr hcDb1.2 hprogDB1) (progRespectsDB_congr hcDb2.2 hprogDB2)
                    (envClosureSafe_congr hcDb1.2 henvCl1) (envClosureSafe_congr hcDb2.2 henvCl2)
                    hesafe.2 hens.2 hesup.2 (exprRespectsDB_congr hcDb1.2 herE1) (exprRespectsDB_congr hcDb2.2 herE2)
                    he hnj1 hnj2).subtype hsubE
                · dsimp only at hnj1 hnj2 ⊢
                  have hsubT : ltySubtype tLTy (.mk tLTy.ty ((tLTy.tags.union eLTy.tags).union (pc.union cLTyF.tags))) = true := by
                    unfold ltySubtype; rw [Bool.and_eq_true]
                    exact ⟨decide_eq_true rfl, TagSet.subset_trans (TagSet.subset_union_left tLTy.tags eLTy.tags) (TagSet.subset_union_left _ _)⟩
                  exact (ihE hprog hsafeProg env1 env2 jenv _ inSpec wc1 wc2 tBr tLTy
                    henv hjenvSafe hjenvSub hwc
                    (progRespectsDB_congr hcDb1.2 hprogDB1) (progRespectsDB_congr hcDb2.2 hprogDB2)
                    (envClosureSafe_congr hcDb1.2 henvCl1) (envClosureSafe_congr hcDb2.2 henvCl2)
                    hesafe.1.2 hens.1.2 hesup.1.2 (exprRespectsDB_congr hcDb1.2 herT1) (exprRespectsDB_congr hcDb2.2 herT2)
                    ht hnj1 hnj2).subtype hsubT
        | caseE scrut arms =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
          unfold exprSuppressSafe at hesup
          cases hchkSF : checkExpr prog (envToTyEnv env1) [] pc false scrut with
          | error _ => rw [hchkSF] at hesup; nomatch hesup
          | ok scrutLTyF =>
          rw [hchkSF] at hesup; dsimp only at hesup
          cases hspF : expectedCaseSpecs prog scrutLTyF.ty scrutLTyF.effectiveTags with
          | error _ => rw [hspF] at hesup; nomatch hesup
          | ok specsF =>
          rw [hspF] at hesup; simp only [Bool.and_eq_true] at hesup
          rcases her1 with ⟨herS1, herA1⟩; rcases her2 with ⟨herS2, herA2⟩
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hscChk : checkExpr prog (envToTyEnv env1) [] pc inSpec scrut <;> rw [hscChk] at hchk <;> try contradiction
          rename_i scrutLTy; dsimp only at hchk
          have hsLTyEq : scrutLTyF = scrutLTy := by
            have h1 := checkExpr_inSpec_true hchkSF; rw [checkExpr_inSpec_true hscChk] at h1; exact (Except.ok.inj h1).symm
          subst hsLTyEq
          cases hsp : expectedCaseSpecs prog scrutLTyF.ty scrutLTyF.effectiveTags <;> rw [hsp] at hchk <;> try contradiction
          rename_i specs; dsimp only at hchk
          have hspecsEq : specsF = specs := by rw [hsp] at hspF; exact (Except.ok.inj hspF).symm
          subst hspecsEq
          split at hchk <;> try contradiction
          cases ha : checkCaseArms prog (envToTyEnv env1) jenv (pc.union scrutLTyF.effectiveTags) inSpec specsF arms <;> rw [ha] at hchk <;> try contradiction
          rename_i armLTys; dsimp only at hchk
          cases armLTys <;> try contradiction
          rename_i firstLTy restLTys; dsimp only at hchk
          split at hchk <;> try contradiction
          rename_i hallRestTy; simp only [List.all_eq_true, decide_eq_true_eq] at hallRestTy
          injection hchk with el; subst el
          have hscChk2 : checkExpr prog (envToTyEnv env2) [] pc inSpec scrut = .ok scrutLTyF := henv.envToTyEnv_eq ▸ hscChk
          rw [checkExpr_inSpec_true hscChk] at hnj1 ⊢
          rw [checkExpr_inSpec_true hscChk2] at hnj2 ⊢
          dsimp only at hnj1 hnj2 ⊢
          have hscWf1 := hsound'.2.2.1 hprog env1 [] pc inSpec w1 scrut scrutLTyF henv.wf_left hw.wf1 hscChk
          have hscWf2 := hsound'.2.2.1 hprog env2 [] pc inSpec w2 scrut scrutLTyF henv.wf_right hw.wf2 hscChk2
          cases hoS1 : eval fuel' prog env1 pc w1 scrut with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoS1] at hnj1; nomatch hnj1
          | jumped _ _ _ => rw [hoS1] at hscWf1; exact absurd rfl hscWf1.not_jumped_nil
          | ok sVal1 ws1 =>
            cases hoS2 : eval fuel' prog env2 pc w2 scrut with
            | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoS2] at hnj2; nomatch hnj2
            | jumped _ _ _ => rw [hoS2] at hscWf2; exact absurd rfl hscWf2.not_jumped_nil
            | ok sVal2 ws2 =>
              rw [hoS1] at hnj1; rw [hoS2] at hnj2; dsimp only at hnj1 hnj2 ⊢
              have hscEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 scrut scrutLTyF
                henv rfl (fun _ hm => nomatch hm) hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe.1 hens.1 hesup.1 herS1 herS2 hscChk (by rw [hoS1]; trivial) (by rw [hoS2]; trivial)
              rw [hoS1, hoS2] at hscEq; rcases hscEq with ⟨hws, hsValEq⟩
              have hsDb1 := hdb'.1 hprog hsafeProg env1 pc w1 scrut hprogDB1 henvCl1 hesafe.1 hens.1 hesup.1 herS1
              have hsDb2 := hdb'.1 hprog hsafeProg env2 pc w2 scrut hprogDB2 henvCl2 hesafe.1 hens.1 (henv.envToTyEnv_eq ▸ hesup.1) herS2
              rw [hoS1] at hsDb1; rw [hoS2] at hsDb2
              cases hm1 : matchCaseVal prog sVal1 scrutLTyF (pc.union scrutLTyF.effectiveTags) with
              | none => rw [hm1] at hnj1; nomatch hnj1
              | some p1 =>
                rcases p1 with ⟨cName1, tvs1⟩; rw [hm1] at hnj1; dsimp only at hnj1 ⊢
                cases hm2 : matchCaseVal prog sVal2 scrutLTyF (pc.union scrutLTyF.effectiveTags) with
                | none => rw [hm2] at hnj2; nomatch hnj2
                | some p2 =>
                  rcases p2 with ⟨cName2, tvs2⟩; rw [hm2] at hnj2; dsimp only at hnj2 ⊢
                  split at hnj1
                  · dsimp only [OutcomeNormalOrJump] at hnj1
                  · rename_i ac1 binders1 body1 hfArm1
                    split at hnj1; (dsimp only [OutcomeNormalOrJump] at hnj1)
                    rename_i hlen1Ok; simp only [hlen1Ok]
                    split at hnj2
                    · dsimp only [OutcomeNormalOrJump] at hnj2
                    · rename_i ac2 binders2 body2 hfArm2
                      split at hnj2; (dsimp only [OutcomeNormalOrJump] at hnj2)
                      rename_i hlen2Ok; simp only [hlen2Ok]
                      have hcaseArmNs : ∀ {cn : Ident} {bs : List Ident} {bd : Expr} (as1 : List CaseArm),
                          CaseArm.mk cn bs bd ∈ as1 → caseArmsNoSpecCalls prog as1 = true → exprNoSpecCalls prog bd = true := by
                        intro cn bs bd as1 hm0 hn0; induction as1 with
                        | nil => nomatch hm0
                        | cons hd tl ih =>
                          cases hd; simp only [caseArmsNoSpecCalls, Bool.and_eq_true] at hn0
                          rcases List.mem_cons.mp hm0 with e | htl
                          · injection e with _ _ eb; subst eb; exact hn0.1
                          · exact ih htl hn0.2
                      have htvNsZip : ∀ {bs : List Ident} {tvs : List (LTy × Val)} {base : Env},
                          (∀ p ∈ tvs, valNoSpecCalls prog p.2 = true) → envNoSpecCalls prog base = true →
                          envNoSpecCalls prog ((List.zip bs tvs).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal }) ++ base) = true := by
                        intro bs tvs base hp hbase; induction bs generalizing tvs with
                        | nil => exact hbase
                        | cons _ bsTl ih =>
                          cases tvs with
                          | nil => exact hbase
                          | cons tv tvsTl => simp [List.zip_cons_cons, envNoSpecCalls, hp tv (.head _), ih (fun q hq => hp q (.tail _ hq))]
                      cases heffLow : scrutLTyF.effectiveTags.subset L
                      · -- High scrutinee: both arms run at `armPc := pc.union scrutLTyF.effectiveTags ⊈ L`!
                        have harmHigh : (pc.union scrutLTyF.effectiveTags).subset L = false := by
                          cases h : (pc.union scrutLTyF.effectiveTags).subset L; rfl
                          simp only [TagSet.union_subset_iff, Bool.and_eq_true] at h
                          rw [heffLow] at h; exact absurd h.2 (by decide)
                        have hltyHigh : (LTy.mk firstLTy.ty ((TagSet.unionList ((firstLTy :: restLTys).map LTy.tags)).union (pc.union scrutLTyF.effectiveTags))).tags.subset L = false := by
                          cases h : (LTy.mk firstLTy.ty ((TagSet.unionList ((firstLTy :: restLTys).map LTy.tags)).union (pc.union scrutLTyF.effectiveTags))).tags.subset L; rfl
                          simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true] at h
                          rw [heffLow] at h; exact absurd h.2.2 (by decide)
                        rw [hoS1] at hscWf1; cases hscWf1 with | ok hsWf1 hws1 =>
                        rw [hoS2] at hscWf2; cases hscWf2 with | ok hsWf2 hws2 =>
                        have hbeq1 := List.find?_some hfArm1; dsimp only at hbeq1
                        have hcEq1 : cName1 = ac1 := (beq_iff_eq.mp hbeq1).symm; subst hcEq1
                        have hbeq2 := List.find?_some hfArm2; dsimp only at hbeq2
                        have hcEq2 : cName2 = ac2 := (beq_iff_eq.mp hbeq2).symm; subst hcEq2
                        rcases matchCaseVal_sound hsWf1 hsp (armPc := pc.union scrutLTyF.effectiveTags) with ⟨_, fLTys1, _, hm1', hsp1, htvL1, htvW1⟩
                        rw [hm1] at hm1'; injection hm1' with hp1; rcases hp1 with ⟨_, rfl⟩
                        rcases (checkCaseArms_props ha).2 cName1 binders1 body1 fLTys1 hfArm1 hsp1 with ⟨hbLen1, aLTy1, haMem1, hbChk1⟩
                        rcases envWf_armEntries binders1 (fLTys1.map (fun f => f.addTags (pc.union scrutLTyF.effectiveTags))) (tvs1.map Prod.snd) tvs1 env1 (by simp [hbLen1]) htvL1 rfl htvW1 henv.wf_left with ⟨haEnvWf1, haTyEq1⟩
                        rw [extendTyEnv, ← haTyEq1] at hbChk1
                        have hscSink := checkExpr_sinksAllowed hsafeProg (envSafeForNI_imp_tyEnv henv.safe_left) rfl hesafe.1 hens.1 hscChk
                        have haEnvSafe1 := envSafeForNI_armEntries binders1 hsafeProg hscSink hsValEq.safe_left hm1 henv.safe_left
                        have haEnvNs1 := htvNsZip (bs := binders1) (matchCaseVal_noSpecCalls (valClosureSafe_imp_noSpecCalls hsDb1.1) hm1) henvNs1
                        have hb1Safe : exprSafeForNI L body1 = true := caseArmsSafeForNI_mem hesafe.2 (List.mem_of_find?_eq_some hfArm1)
                        have hb1Ns : exprNoSpecCalls prog body1 = true := hcaseArmNs arms (List.mem_of_find?_eq_some hfArm1) hens.2
                        rcases hsc'.1 hprog hsafeProg _ jenv _ inSpec ws1 body1 aLTy1 haEnvWf1 haEnvSafe1 haEnvNs1 hjenvSafe hws1 hb1Safe hb1Ns hbChk1 with ⟨hsB1, _, hcB1⟩
                        have hwfB1 := hsound'.2.2.1 hprog _ jenv _ inSpec ws1 body1 aLTy1 haEnvWf1 hws1 hbChk1
                        have ha2 : checkCaseArms prog (envToTyEnv env2) jenv (pc.union scrutLTyF.effectiveTags) inSpec specsF arms = .ok (firstLTy :: restLTys) := henv.envToTyEnv_eq ▸ ha
                        rcases matchCaseVal_sound hsWf2 hsp (armPc := pc.union scrutLTyF.effectiveTags) with ⟨_, fLTys2, _, hm2', hsp2, htvL2, htvW2⟩
                        rw [hm2] at hm2'; injection hm2' with hp2; rcases hp2 with ⟨_, rfl⟩
                        rcases (checkCaseArms_props ha2).2 cName2 binders2 body2 fLTys2 hfArm2 hsp2 with ⟨hbLen2, aLTy2, haMem2, hbChk2⟩
                        rcases envWf_armEntries binders2 (fLTys2.map (fun f => f.addTags (pc.union scrutLTyF.effectiveTags))) (tvs2.map Prod.snd) tvs2 env2 (by simp [hbLen2]) htvL2 rfl htvW2 henv.wf_right with ⟨haEnvWf2, haTyEq2⟩
                        rw [extendTyEnv, ← haTyEq2] at hbChk2
                        have haEnvSafe2 := envSafeForNI_armEntries binders2 hsafeProg hscSink hsValEq.safe_right hm2 henv.safe_right
                        have haEnvNs2 := htvNsZip (bs := binders2) (matchCaseVal_noSpecCalls (valClosureSafe_imp_noSpecCalls hsDb2.1) hm2) henvNs2
                        have hb2Safe : exprSafeForNI L body2 = true := caseArmsSafeForNI_mem hesafe.2 (List.mem_of_find?_eq_some hfArm2)
                        have hb2Ns : exprNoSpecCalls prog body2 = true := hcaseArmNs arms (List.mem_of_find?_eq_some hfArm2) hens.2
                        rcases hsc'.1 hprog hsafeProg _ jenv _ inSpec ws2 body2 aLTy2 haEnvWf2 haEnvSafe2 haEnvNs2 hjenvSafe hws2 hb2Safe hb2Ns hbChk2 with ⟨hsB2, _, hcB2⟩
                        have hwfB2 := hsound'.2.2.1 hprog _ jenv _ inSpec ws2 body2 aLTy2 haEnvWf2 hws2 hbChk2
                        have hty1Eq : aLTy1.ty = firstLTy.ty := by rcases List.mem_cons.mp haMem1 with rfl | hr; rfl; exact hallRestTy aLTy1 hr
                        have hty2Eq : aLTy2.ty = firstLTy.ty := by rcases List.mem_cons.mp haMem2 with rfl | hr; rfl; exact hallRestTy aLTy2 hr
                        have hcB1' := hcB1 harmHigh; have hcB2' := hcB2 harmHigh
                        apply joinOutcomeEquiv_of_high hws hltyHigh hnj1 hnj2
                        · cases ho : eval fuel' prog _ (pc.union scrutLTyF.effectiveTags) ws1 body1 <;> rw [ho] at hnj1 hcB1' <;> first | contradiction | exact hcB1'
                        · cases ho : eval fuel' prog _ (pc.union scrutLTyF.effectiveTags) ws2 body2 <;> rw [ho] at hnj2 hcB2' <;> first | contradiction | exact hcB2'
                        · intro v w' ho; rw [ho] at hwfB1 hsB1; cases hwfB1 with | ok hv _ => exact ⟨hty1Eq ▸ hv, hsB1⟩
                        · intro v w' ho; rw [ho] at hwfB2 hsB2; cases hwfB2 with | ok hv _ => exact ⟨hty2Eq ▸ hv, hsB2⟩
                        · exact fun lbl vs w' ho => hjmp'.1 hprog _ jenv _ inSpec ws1 body1 aLTy1 lbl vs w' haEnvWf1 hws1 hbChk1 harmHigh ho
                        · exact fun lbl vs w' ho => hjmp'.1 hprog _ jenv _ inSpec ws2 body2 aLTy2 lbl vs w' haEnvWf2 hws2 hbChk2 harmHigh ho
                      · -- Low scrutinee (`scrutLTyF.effectiveTags ⊆ L`): same constructor `cName1 = cName2` & `EnvEquiv`!
                        have hscSink := checkExpr_sinksAllowed hsafeProg (envSafeForNI_imp_tyEnv henv.safe_left) rfl hesafe.1 hens.1 hscChk
                        rcases matchCaseVal_ni hscSink hsafeProg heffLow hsValEq hm1 hm2 with ⟨hcEq, hbindEq⟩
                        subst hcEq
                        rw [hfArm1] at hfArm2; injection hfArm2 with earm; cases earm
                        rw [hoS1] at hscWf1; cases hscWf1 with | ok hsWf1 _ =>
                        have hbeq1 := List.find?_some hfArm1; dsimp only at hbeq1
                        have hcEq1 : cName1 = ac1 := (beq_iff_eq.mp hbeq1).symm; subst hcEq1
                        rcases matchCaseVal_sound hsWf1 hsp (armPc := pc.union scrutLTyF.effectiveTags) with ⟨_, fLTys, _, hm1', hsp1, htvL1, htvW1⟩
                        rw [hm1] at hm1'; injection hm1' with hp1; rcases hp1 with ⟨_, rfl⟩
                        rcases (checkCaseArms_props ha).2 cName1 binders1 body1 fLTys hfArm1 hsp1 with ⟨hbLen, aLTy, haMem, hbChk⟩
                        rcases envWf_armEntries binders1 (fLTys.map (fun f => f.addTags (pc.union scrutLTyF.effectiveTags))) (tvs1.map Prod.snd) tvs1 env1 (by simp [hbLen]) htvL1 rfl htvW1 henv.wf_left with ⟨_, haTyEq⟩
                        rw [extendTyEnv, ← haTyEq] at hbChk
                        have htvCl1 := matchCaseVal_closureSafe (valClosureSafe_congr hsDb1.2 hsDb1.1) hm1
                        have htvCl2 := matchCaseVal_closureSafe (valClosureSafe_congr hsDb2.2 hsDb2.1) hm2
                        have hzipCl : ∀ {w : World} (bs : List Ident) (tvs : List (LTy × Val)),
                            (∀ p ∈ tvs, valClosureSafe prog L w p.2) →
                            envClosureSafe prog L w ((List.zip bs tvs).map (fun (bName, (bLTy, bVal)) => { name := bName, lty := bLTy, val := bVal })) := by
                          intro w bs tvs hp; induction bs generalizing tvs with
                          | nil => trivial
                          | cons _ bsTl ih => cases tvs with | nil => trivial | cons tv tvsTl => exact ⟨hp tv (.head _), ih tvsTl (fun q hq => hp q (.tail _ hq))⟩
                        have harmProps : ∀ (as1 : List CaseArm), CaseArm.mk cName1 binders1 body1 ∈ as1 →
                            caseArmsSafeForNI L as1 = true → caseArmsNoSpecCalls prog as1 = true →
                            caseArmsSuppressSafe prog L (envToTyEnv env1) (pc.union scrutLTyF.effectiveTags) specsF as1 = true →
                            armsRespectsDB w1 as1 → armsRespectsDB w2 as1 →
                            exprSafeForNI L body1 = true ∧ exprNoSpecCalls prog body1 = true ∧
                            exprSuppressSafe prog L (extendTyEnv (envToTyEnv env1) (List.zip binders1 (fLTys.map (fun f => f.addTags (pc.union scrutLTyF.effectiveTags))))) (pc.union scrutLTyF.effectiveTags) body1 = true ∧
                            exprRespectsDB w1 body1 ∧ exprRespectsDB w2 body1 := by
                          intro as1 hm0 hs0 hn0 hsu0 hr10 hr20; induction as1 with
                          | nil => nomatch hm0
                          | cons hd tl ih =>
                            cases hd
                            simp only [caseArmsSafeForNI, Bool.and_eq_true] at hs0
                            simp only [caseArmsNoSpecCalls, Bool.and_eq_true] at hn0
                            unfold caseArmsSuppressSafe at hsu0
                            split at hsu0 <;> try contradiction
                            simp only [Bool.and_eq_true] at hsu0
                            rcases List.mem_cons.mp hm0 with e | htl
                            · injection e with ec eb1 eb2; subst ec; subst eb1; subst eb2
                              rename_i hsp'
                              rw [hsp1] at hsp'; injection hsp' with hp'; injection hp' with _ hf'; subst hf'
                              exact ⟨hs0.1, hn0.1, hsu0.1, hr10.1, hr20.1⟩
                            · exact ih htl hs0.2 hn0.2 hsu0.2 hr10.2 hr20.2
                        rcases harmProps arms (List.mem_of_find?_eq_some hfArm1) hesafe.2 hens.2 hesup.2 herA1 herA2 with ⟨hbSafe, hbNs, hbSup, hbr1, hbr2⟩
                        have hsubArm : ltySubtype aLTy (.mk firstLTy.ty ((TagSet.unionList ((firstLTy :: restLTys).map LTy.tags)).union (pc.union scrutLTyF.effectiveTags))) = true := by
                          have htyEq : aLTy.ty = firstLTy.ty := by rcases List.mem_cons.mp haMem with rfl | hr; rfl; exact hallRestTy aLTy hr
                          have htagsSub : aLTy.tags.subset (TagSet.unionList ((firstLTy :: restLTys).map LTy.tags)) = true := by
                            rw [TagSet.subset_iff]; intro t htMem
                            rw [TagSet.mem_unionList, List.any_eq_true]
                            exact ⟨aLTy.tags, List.mem_map_of_mem haMem, htMem⟩
                          unfold ltySubtype; rw [Bool.and_eq_true]
                          refine ⟨decide_eq_true htyEq, ?_⟩
                          exact TagSet.subset_trans htagsSub (TagSet.subset_union_left _ _)
                        exact (ihE hprog hsafeProg _ _ jenv _ inSpec ws1 ws2 body1 aLTy
                          ((hbindEq binders1).append henv) hjenvSafe hjenvSub hws
                          (progRespectsDB_congr hsDb1.2 hprogDB1) (progRespectsDB_congr hsDb2.2 hprogDB2)
                          (envClosureSafe_append (hzipCl binders1 tvs1 htvCl1) (envClosureSafe_congr hsDb1.2 henvCl1))
                          (envClosureSafe_append (hzipCl binders1 tvs2 htvCl2) (envClosureSafe_congr hsDb2.2 henvCl2))
                          hbSafe hbNs (by rw [haTyEq]; exact hbSup) (exprRespectsDB_congr hsDb1.2 hbr1) (exprRespectsDB_congr hsDb2.2 hbr2)
                          hbChk hnj1 hnj2).subtype hsubArm
        | lam params fnPc retLTy body =>
          have hwfOut1 := hsound.2.2.1 hprog env1 jenv pc inSpec w1 _ _ henv.wf_left hw.wf1 hchkOrig
          have hwfOut2 := hsound.2.2.1 hprog env2 jenv pc inSpec w2 _ _ henv.wf_right hw.wf2 hchk2
          unfold eval at hwfOut1 hwfOut2
          unfold checkExpr at hchk
          repeat (split at hchk <;> try contradiction)
          simp only [bind, Except.bind] at hchk
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          injection hchk with el; subst el
          cases hwfOut1 with | ok hcWf1 _ =>
          cases hwfOut2 with | ok hcWf2 _ =>
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          exact ⟨hw, ValEquiv.mk_smart hcWf1 hcWf2
            (by simp [valSafeForNI, hesafe.1.1, hesafe.1.2, hesafe.2, henv.safe_left])
            (by simp [valSafeForNI, hesafe.1.1, hesafe.1.2, hesafe.2, henv.safe_right])
            (fun _ => .closure henv)⟩
        | app fnExpr args =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
          simp only [exprSuppressSafe, Bool.and_eq_true] at hesup
          rcases her1 with ⟨herF1, herA1⟩; rcases her2 with ⟨herF2, herA2⟩
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hf : checkExpr prog (envToTyEnv env1) [] pc inSpec fnExpr <;> rw [hf] at hchk <;> try contradiction
          rename_i fnLTy; dsimp only at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
          rename_i argLTys; dsimp only at hchk
          cases fnLTy with | mk fty fTs =>
          cases fty <;> dsimp only [LTy.ty] at hchk <;> try contradiction
          rename_i paramLTys fnPc retLTy
          split at hchk <;> try contradiction
          rename_i hcallPcSub; simp only [Bool.not_eq_true', Bool.not_eq_false] at hcallPcSub
          split at hchk <;> try contradiction
          rename_i harity; simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harity
          split at hchk <;> try contradiction
          rename_i hzipSub; simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hzipSub
          injection hchk with el; subst el
          have hfOutWf1 := hsound'.2.2.1 hprog env1 [] pc inSpec w1 fnExpr _ henv.wf_left hw.wf1 hf
          have hfOutWf2 := hsound'.2.2.1 hprog env2 [] pc inSpec w2 fnExpr _ henv.wf_right hw.wf2 (henv.envToTyEnv_eq ▸ hf)
          cases hoF1 : eval fuel' prog env1 pc w1 fnExpr with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoF1] at hnj1; dsimp only [OutcomeNormalOrJump] at hnj1
          | jumped _ _ _ => rw [hoF1] at hfOutWf1; exact absurd rfl hfOutWf1.not_jumped_nil
          | ok fv1 wf1 =>
          cases hoF2 : eval fuel' prog env2 pc w2 fnExpr with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoF2] at hnj2; dsimp only [OutcomeNormalOrJump] at hnj2
          | jumped _ _ _ => rw [hoF2] at hfOutWf2; exact absurd rfl hfOutWf2.not_jumped_nil
          | ok fv2 wf2 =>
          rw [hoF1] at hnj1; rw [hoF2] at hnj2
          have hfEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 fnExpr _
            henv rfl (fun _ hm => nomatch hm) hw hprogDB1 hprogDB2 henvCl1 henvCl2
            hesafe.1 hens.1 hesup.1 herF1 herF2 hf (by rw [hoF1]; trivial) (by rw [hoF2]; trivial)
          rw [hoF1, hoF2] at hfEq; rcases hfEq with ⟨hwf, hfvEq⟩
          have hfvWf1 := hfvEq.wf_left
          have hfvWf2 := hfvEq.wf_right
          generalize hp2Eq : paramLTys = pLTys2 at hfvWf2
          cases hfvWf1 with | @closure params1 _ _ bodyLTy1 body1 capEnv1 hcapWf1 hbChk1 hbSub1 =>
          cases hfvWf2 with | @closure params2 _ _ bodyLTy2 body2 capEnv2 hcapWf2 hbChk2 hbSub2 =>
          dsimp only at hnj1 hnj2 ⊢
          have hfDb1 := hdb'.1 hprog hsafeProg env1 pc w1 fnExpr hprogDB1 henvCl1 hesafe.1 hens.1 hesup.1 herF1
          have hfDb2 := hdb'.1 hprog hsafeProg env2 pc w2 fnExpr hprogDB2 henvCl2 hesafe.1 hens.1 (henv.envToTyEnv_eq ▸ hesup.1) herF2
          rw [hoF1] at hfDb1; rw [hoF2] at hfDb2
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) wf1 args with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0)
              hwf.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok argVals1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) wf2 args with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0)
                hwf.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok argVals2 wa2 =>
              rw [hseq1] at hnj1; rw [hseq2] at hnj2; dsimp only at hnj1 hnj2 ⊢
              rcases evalSeq_ni ihE hprog hsafeProg henv hwf
                (progRespectsDB_congr hfDb1.2 hprogDB1) (progRespectsDB_congr hfDb2.2 hprogDB2)
                (envClosureSafe_congr hfDb1.2 henvCl1) (envClosureSafe_congr hfDb2.2 henvCl2)
                hesafe.2 hens.2 hesup.2 (listRespectsDB_congr hfDb1.2 herA1) (listRespectsDB_congr hfDb2.2 herA2)
                ha hseq1 hseq2 with ⟨hargsEq, hwa⟩
              have hlen1 : argVals1.length = params1.length := by
                rw [hargsEq.length_eq.1, harity, List.length_map]
              have hlen2 : argVals2.length = params2.length := by
                rw [hargsEq.length_eq.2, harity, hp2Eq, List.length_map]
              simp only [hlen1, hlen2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hnj1 hnj2 ⊢
              have hargsSub : ValListEquiv prog L argVals1 argVals2 (params1.map Prod.snd) :=
                hargsEq.subtype_zip harity hzipSub
              have hseqStep1 := fun w' e' hww' hs' hns' hsup' hr' =>
                hdb'.1 hprog hsafeProg env1 pc w' e' (progRespectsDB_congr hww' (progRespectsDB_congr hfDb1.2 hprogDB1))
                  (envClosureSafe_congr hww' (envClosureSafe_congr hfDb1.2 henvCl1)) hs' hns' hsup' hr'
              have hseqStep2 := fun w' e' hww' hs' hns' hsup' hr' =>
                hdb'.1 hprog hsafeProg env2 pc w' e' (progRespectsDB_congr hww' (progRespectsDB_congr hfDb2.2 hprogDB2))
                  (envClosureSafe_congr hww' (envClosureSafe_congr hfDb2.2 henvCl2)) hs' hns' (henv.envToTyEnv_eq ▸ hsup') hr'
              have hsDb1 := evalSeq_db_and_closureSafe (eval fuel' prog env1 pc) hseqStep1 (WorldDBSame.refl wf1) hesafe.2 hens.2 hesup.2 (listRespectsDB_congr hfDb1.2 herA1)
              have hsDb2 := evalSeq_db_and_closureSafe (eval fuel' prog env2 pc) hseqStep2 (WorldDBSame.refl wf2) hesafe.2 hens.2 hesup.2 (listRespectsDB_congr hfDb2.2 herA2)
              rw [hseq1] at hsDb1; rw [hseq2] at hsDb2
              have hw1a := hfDb1.2.trans hsDb1.2
              have hw2a := hfDb2.2.trans hsDb2.2
              cases hfnPcLow : fnPc.subset L
              · -- High `fnPc`: both closure bodies are world-confined to `wa1, wa2` and `fnPc ⊆ retLTy.tags`!
                have hfnSubRet : fnPc.subset retLTy.tags = true := by
                  have h1 := checkExpr_pc_subset_tags (fun _ hm => False.elim (List.not_mem_nil hm)) hbChk1
                  simp only [ltySubtype, Bool.and_eq_true] at hbSub1
                  exact TagSet.subset_trans h1 hbSub1.2
                have hltyHigh : (retLTy.addTags (pc.union fTs)).tags.subset L = false := by
                  cases hs : (retLTy.addTags (pc.union fTs)).tags.subset L; rfl
                  simp only [LTy.tags_addTags, TagSet.union_subset_iff, Bool.and_eq_true] at hs
                  have := TagSet.subset_trans hfnSubRet hs.1; rw [hfnPcLow] at this; nomatch this
                have hclSafe1 := hfvEq.safe_left; simp only [valSafeForNI, Bool.and_eq_true] at hclSafe1
                have hclSafe2 := hfvEq.safe_right; simp only [valSafeForNI, Bool.and_eq_true] at hclSafe2
                have hpEnvWf1 := extendEnv_wf hargsSub.wf_left hcapWf1
                have hpEnvWf2 := extendEnv_wf (hp2Eq ▸ hargsSub.wf_right) hcapWf2
                have hpEnvSafe1 := extendEnv_safeForNI hclSafe1.1.1.1 hargsSub.safe_left hclSafe1.2
                have hpEnvSafe2 := extendEnv_safeForNI hclSafe2.1.1.1 hargsSub.safe_right hclSafe2.2
                rcases valClosureSafe_congr hw1a hfDb1.1 with ⟨_, hbodyNs1, _, _, hcapCl1⟩
                rcases valClosureSafe_congr hw2a hfDb2.1 with ⟨_, hbodyNs2, _, _, hcapCl2⟩
                have hpEnvNs1 : envNoSpecCalls prog ((List.zip params1 argVals1).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv1) = true :=
                  envClosureSafe_imp_noSpecCalls (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hsDb1.2 hsDb1.1)) hcapCl1)
                have hpEnvNs2 : envNoSpecCalls prog ((List.zip params2 argVals2).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv2) = true :=
                  envClosureSafe_imp_noSpecCalls (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hsDb2.2 hsDb2.1)) hcapCl2)
                have hpTy1 : envToTyEnv ((List.zip params1 argVals1).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv1) =
                    extendTyEnv (envToTyEnv capEnv1) params1 := by
                  rw [envToTyEnv_append, envToTyEnv_zip_params params1 argVals1 hlen1, extendTyEnv]
                have hpTy2 : envToTyEnv ((List.zip params2 argVals2).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv2) =
                    extendTyEnv (envToTyEnv capEnv2) params2 := by
                  rw [envToTyEnv_append, envToTyEnv_zip_params params2 argVals2 hlen2, extendTyEnv]
                rcases hsc'.1 hprog hsafeProg _ [] fnPc true wa1 body1 bodyLTy1 hpEnvWf1 hpEnvSafe1 hpEnvNs1 rfl hwa.wf1 hclSafe1.1.2 hbodyNs1 (hpTy1 ▸ hbChk1) with ⟨hsB1, _, hcB1⟩
                rcases hsc'.1 hprog hsafeProg _ [] fnPc true wa2 body2 bodyLTy2 hpEnvWf2 hpEnvSafe2 hpEnvNs2 rfl hwa.wf2 hclSafe2.1.2 hbodyNs2 (hpTy2 ▸ hbChk2) with ⟨hsB2, _, hcB2⟩
                have hwfB1 := hsound'.2.2.1 hprog _ [] fnPc true wa1 body1 bodyLTy1 hpEnvWf1 hwa.wf1 (hpTy1 ▸ hbChk1)
                have hwfB2 := hsound'.2.2.1 hprog _ [] fnPc true wa2 body2 bodyLTy2 hpEnvWf2 hwa.wf2 (hpTy2 ▸ hbChk2)
                cases hoB1 : eval fuel' prog _ fnPc wa1 body1 <;> rw [hoB1] at hnj1 <;> try contradiction
                cases hoB2 : eval fuel' prog _ fnPc wa2 body2 <;> rw [hoB2] at hnj2 <;> try contradiction
                rw [hoB1] at hwfB1 hsB1; rw [hoB2] at hwfB2 hsB2; dsimp only
                have ew1 := hcB1 hfnPcLow; rw [hoB1] at ew1; dsimp only [outcomeWorldEq] at ew1; subst ew1
                have ew2 := hcB2 hfnPcLow; rw [hoB2] at ew2; dsimp only [outcomeWorldEq] at ew2; subst ew2
                cases hwfB1 with | ok hv1 _ =>
                cases hwfB2 with | ok hv2 _ =>
                simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hbSub1 hbSub2
                exact ⟨hwa, .high hltyHigh (by simpa [hbSub1.1] using hv1) (by simpa [hbSub2.1] using hv2) hsB1 hsB2⟩
              · -- Low `fnPc`: implies `fTs ⊆ fnPc ⊆ L`, so `fv1` and `fv2` have the SAME body & `EnvEquiv`!
                have hfTsLow : fTs.subset L = true := by
                  simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hcallPcSub
                  exact TagSet.subset_trans hcallPcSub.2 hfnPcLow
                cases hfvEq.payload hfTsLow with | closure hcapEq =>
                have hclSafe1 := hfvEq.safe_left; simp only [valSafeForNI, Bool.and_eq_true] at hclSafe1
                rcases valClosureSafe_congr hw1a hfDb1.1 with ⟨hbodySafe, hbodyNs, hbodySup, hbodyDB1, hcapCl1⟩
                rcases valClosureSafe_congr hw2a hfDb2.1 with ⟨_, _, _, hbodyDB2, hcapCl2⟩
                have hpEnvEq := extendEnv_equiv hclSafe1.1.1.1 hargsSub hcapEq
                have hpTy1 : envToTyEnv ((List.zip params1 argVals1).map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }) ++ capEnv1) =
                    extendTyEnv (envToTyEnv capEnv1) params1 := by
                  rw [envToTyEnv_append, envToTyEnv_zip_params params1 argVals1 hlen1, extendTyEnv]
                cases hoB1 : eval fuel' prog _ fnPc wa1 body1 <;> rw [hoB1] at hnj1 <;> try contradiction
                cases hoB2 : eval fuel' prog _ fnPc wa2 body1 <;> rw [hoB2] at hnj2 <;> try contradiction
                dsimp only
                have hbEq := ihE hprog hsafeProg _ _ [] fnPc true wa1 wa2 body1 bodyLTy1
                  hpEnvEq rfl (fun _ hm => nomatch hm) hwa
                  (progRespectsDB_congr hw1a hprogDB1) (progRespectsDB_congr hw2a hprogDB2)
                  (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hsDb1.2 hsDb1.1)) hcapCl1)
                  (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hsDb2.2 hsDb2.1)) hcapCl2)
                  hbodySafe hbodyNs (hpTy1.symm ▸ hbodySup) hbodyDB1 hbodyDB2 (hpTy1 ▸ hbChk1) (by rw [hoB1]; trivial) (by rw [hoB2]; trivial)
                rw [hoB1, hoB2] at hbEq; rcases hbEq with ⟨hwFinal, hvEq⟩
                exact ⟨hwFinal, (hvEq.subtype hbSub1).addTags (pc.union fTs)⟩
        | call fnName args =>
          dsimp only at hnj1 hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
          rename_i argLTys; dsimp only at hchk
          cases hf : prog.findFun? fnName <;> rw [hf] at hchk <;> try contradiction
          rename_i fDecl; dsimp only at hchk
          simp only [exprNoSpecCalls, hf, Bool.and_eq_true, Bool.not_eq_true'] at hens
          rcases hens with ⟨hnotSpec, hensArgs⟩
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          rename_i hpcSubFn; simp only [Bool.not_eq_true', Bool.not_eq_false] at hpcSubFn
          split at hchk <;> try contradiction
          rename_i harity; simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harity
          split at hchk <;> try contradiction
          rename_i hzipSub; simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hzipSub
          injection hchk with el; subst el
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) w1 args with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0)
              hw.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok argVals1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) w2 args with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0)
                hw.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok argVals2 wa2 =>
              rw [hseq1] at hnj1; rw [hseq2] at hnj2; simp only [hf] at hnj1 hnj2 ⊢
              rcases evalSeq_ni ihE hprog hsafeProg henv hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe hensArgs hesup her1 her2 ha hseq1 hseq2 with ⟨hargsEq, hwa⟩
              have hlen1 : argVals1.length = fDecl.params.length := by rw [hargsEq.length_eq.1, harity]
              have hlen2 : argVals2.length = fDecl.params.length := by rw [hargsEq.length_eq.2, harity]
              simp only [hlen1, hlen2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hnj1 hnj2 ⊢
              have hargsSub : ValListEquiv prog L argVals1 argVals2 (fDecl.params.map Prod.snd) :=
                hargsEq.subtype_zip (by simp [harity]) hzipSub
              have hfnChk : ∃ bodyLTy,
                  checkExpr prog fDecl.params.reverse [] fDecl.pc fDecl.kind.isSpec fDecl.body = .ok bodyLTy ∧
                  ltySubtype bodyLTy fDecl.ret = true := by
                have hfd := checkFunDecls_mem (checkProgram_parts hprog).2.2.2 (List.mem_of_find?_eq_some hf)
                unfold checkFunDecl at hfd
                repeat (split at hfd <;> try contradiction)
                simp only [bind, Except.bind] at hfd
                cases hp : checkParamsPolicy prog.policy fDecl.params <;> rw [hp] at hfd <;> try contradiction
                dsimp only at hfd
                cases hb : checkExpr prog fDecl.params.reverse [] fDecl.pc fDecl.kind.isSpec fDecl.body <;> rw [hb] at hfd <;> try contradiction
                dsimp only at hfd; split at hfd <;> try contradiction
                exact ⟨_, rfl, by assumption⟩
              rcases hfnChk with ⟨bodyLTy, hbChk, hbSub⟩
              have hfSafe : ltyListSinksAllowed L (fDecl.params.map Prod.snd) = true ∧
                  exprSafeForNI L fDecl.body = true ∧
                  exprSuppressSafe prog L fDecl.params.reverse fDecl.pc fDecl.body = true := by
                have hsp := hsafeProg
                simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hsp
                rcases hsp.2 fDecl (List.mem_of_find?_eq_some hf) with hspec | hm
                · rw [hnotSpec] at hspec; nomatch hspec
                · exact ⟨hm.1.1.1, hm.1.2, hm.2⟩
              have hfNs : exprNoSpecCalls prog fDecl.body = true :=
                checkExpr_noSpecCalls (hnotSpec ▸ hbChk)
              have hseqStep1 := fun w' e' hww' hs' hns' hsup' hr' =>
                hdb'.1 hprog hsafeProg env1 pc w' e' (progRespectsDB_congr hww' hprogDB1) (envClosureSafe_congr hww' henvCl1) hs' hns' hsup' hr'
              have hseqStep2 := fun w' e' hww' hs' hns' hsup' hr' =>
                hdb'.1 hprog hsafeProg env2 pc w' e' (progRespectsDB_congr hww' hprogDB2) (envClosureSafe_congr hww' henvCl2) hs' hns' (henv.envToTyEnv_eq ▸ hsup') hr'
              have hsDb1 := evalSeq_db_and_closureSafe (eval fuel' prog env1 pc) hseqStep1 (WorldDBSame.refl w1) hesafe hensArgs hesup her1
              have hsDb2 := evalSeq_db_and_closureSafe (eval fuel' prog env2 pc) hseqStep2 (WorldDBSame.refl w2) hesafe hensArgs hesup her2
              rw [hseq1] at hsDb1; rw [hseq2] at hsDb2
              have hcallEnvEq : EnvEquiv prog L
                  ((List.zip fDecl.params argVals1).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal }))
                  ((List.zip fDecl.params argVals2).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) := by
                rw [List.map_reverse, List.map_reverse]
                have h0 := extendEnv_equiv (base1 := []) (base2 := []) hfSafe.1 hargsSub .nil
                simp only [List.append_nil] at h0
                exact h0.reverse
              have hcallTy : envToTyEnv ((List.zip fDecl.params argVals1).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) =
                  fDecl.params.reverse := by
                rw [List.map_reverse, envToTyEnv_reverse, envToTyEnv_zip_params fDecl.params argVals1 hlen1]
              have hcallCl1 : envClosureSafe prog L wa1 ((List.zip fDecl.params argVals1).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) := by
                rw [List.map_reverse]; exact envClosureSafe_reverse (envClosureSafe_zip_params (valListClosureSafe_congr hsDb1.2 hsDb1.1))
              have hcallCl2 : envClosureSafe prog L wa2 ((List.zip fDecl.params argVals2).reverse.map (fun ((pName, pLTy), aVal) => { name := pName, lty := pLTy, val := aVal })) := by
                rw [List.map_reverse]; exact envClosureSafe_reverse (envClosureSafe_zip_params (valListClosureSafe_congr hsDb2.2 hsDb2.1))
              cases hoB1 : eval fuel' prog _ fDecl.pc wa1 fDecl.body <;> rw [hoB1] at hnj1 <;> try contradiction
              cases hoB2 : eval fuel' prog _ fDecl.pc wa2 fDecl.body <;> rw [hoB2] at hnj2 <;> try contradiction
              dsimp only
              have hbEq := ihE hprog hsafeProg _ _ [] fDecl.pc fDecl.kind.isSpec wa1 wa2 fDecl.body bodyLTy
                hcallEnvEq rfl (fun _ hm => nomatch hm) hwa
                (progRespectsDB_congr hsDb1.2 hprogDB1) (progRespectsDB_congr hsDb2.2 hprogDB2)
                hcallCl1 hcallCl2 hfSafe.2.1 hfNs (hcallTy.symm ▸ hfSafe.2.2)
                (exprRespectsDB_congr hsDb1.2 (hprogDB1 fDecl (List.mem_of_find?_eq_some hf) hnotSpec))
                (exprRespectsDB_congr hsDb2.2 (hprogDB2 fDecl (List.mem_of_find?_eq_some hf) hnotSpec))
                (hcallTy ▸ hbChk) (by rw [hoB1]; trivial) (by rw [hoB2]; trivial)
              rw [hoB1, hoB2] at hbEq; rcases hbEq with ⟨hwFinal, hvEq⟩
              exact ⟨hwFinal, (hvEq.subtype hbSub).addTags pc⟩
        | join label params rhs body =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          simp only [exprNoSpecCalls, Bool.and_eq_true] at hens
          simp only [exprSuppressSafe, Bool.and_eq_true] at hesup
          rcases her1 with ⟨herR1, herB1⟩; rcases her2 with ⟨herR2, herB2⟩
          rw [← henv.envToTyEnv_eq] at hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          dsimp only at hchk
          let tEnv := envToTyEnv env1
          let guess1 := pc.union (inferJumpPc prog label tEnv pc body)
          let rhsTEnv := extendTyEnv tEnv params
          let joinPc := guess1.union (inferJumpPc prog label rhsTEnv guess1 rhs)
          cases hinf : inferJoinRetLTy prog rhsTEnv jenv joinPc label rhs body with
          | none => rw [hinf] at hchk; contradiction
          | some candRetLTy =>
            rw [hinf] at hchk; dsimp only [bind, Except.bind] at hchk
            split at hchk <;> try contradiction
            have hcandOk : ltySinksAllowed L candRetLTy = true := by
              unfold inferJoinRetLTy at hinf
              have hrEnvOk := extendTyEnv_sinksAllowed (envSafeForNI_imp_tyEnv henv.safe_left) hesafe.1.1
              cases h1 : inferBranchLTy prog rhsTEnv jenv joinPc [label] rhs with
              | some l => rw [h1] at hinf; injection hinf with e; subst e; exact inferBranchLTy_sinksAllowed hsafeProg hrEnvOk hjenvSafe hesafe.1.2 hens.1 h1
              | none => rw [h1] at hinf; exact inferBranchLTy_sinksAllowed hsafeProg hrEnvOk hjenvSafe hesafe.2 hens.2 hinf
            have hjoinProps : ∃ rLTy bLTy,
                ltySinksAllowed L lty = true ∧
                joinPc.subset lty.tags = true ∧
                ltySubtype rLTy lty = true ∧
                ltySubtype bLTy lty = true ∧
                checkExpr prog rhsTEnv ((label, { params := params, joinPc := joinPc, retLTy := lty }) :: jenv) joinPc inSpec rhs = .ok rLTy ∧
                checkExpr prog tEnv ((label, { params := params, joinPc := joinPc, retLTy := lty }) :: jenv) pc inSpec body = .ok bLTy := by
              cases hr1 : checkExpr prog rhsTEnv ((label, { params := params, joinPc := joinPc, retLTy := candRetLTy.addTags joinPc }) :: jenv) joinPc inSpec rhs <;>
                rw [hr1] at hchk <;> try contradiction
              rename_i rLTy1; dsimp only at hchk
              cases hb1 : checkExpr prog tEnv ((label, { params := params, joinPc := joinPc, retLTy := candRetLTy.addTags joinPc }) :: jenv) pc inSpec body <;>
                rw [hb1] at hchk <;> try contradiction
              rename_i bLTy1; dsimp only at hchk; split at hchk <;> try contradiction
              rename_i htyEq; simp only [Bool.and_eq_true, decide_eq_true_eq] at htyEq
              split at hchk
              · rename_i hfSub; injection hchk with el; subst el
                have hrSub : ltySubtype rLTy1 (candRetLTy.addTags joinPc) = true := by
                  unfold ltySubtype; rw [Bool.and_eq_true]
                  refine ⟨decide_eq_true (by simpa [LTy.ty_addTags] using htyEq.1), ?_⟩
                  rw [TagSet.subset_iff]; intro t htMem
                  exact (TagSet.subset_iff _ _).mp hfSub t (by simp [htMem])
                have hbSub : ltySubtype bLTy1 (candRetLTy.addTags joinPc) = true := by
                  unfold ltySubtype; rw [Bool.and_eq_true]
                  refine ⟨decide_eq_true (by simpa [LTy.ty_addTags] using htyEq.2), ?_⟩
                  rw [TagSet.subset_iff]; intro t htMem
                  exact (TagSet.subset_iff _ _).mp hfSub t (by simp [htMem])
                exact ⟨rLTy1, bLTy1, by simpa using hcandOk, by rw [LTy.tags_addTags]; exact TagSet.subset_union_right candRetLTy.tags joinPc, hrSub, hbSub, hr1, hb1⟩
              · split at hchk
                · contradiction
                · rename_i rLTy2 hr2
                  split at hchk
                  · contradiction
                  · rename_i bLTy2 hb2
                    split at hchk <;> try contradiction
                    rename_i hsub2; simp only [Bool.and_eq_true] at hsub2
                    injection hchk with el; subst el
                    have hjpSub : joinPc.subset (((candRetLTy.addTags joinPc).tags.union rLTy1.tags).union (bLTy1.tags.union pc)) = true := by
                      rw [TagSet.subset_iff]; intro t htMem; simp [LTy.tags_addTags, htMem]
                    exact ⟨rLTy2, bLTy2, by simpa [ltySinksAllowed] using hcandOk, hjpSub, hsub2.1, hsub2.2, hr2, hb2⟩
            rcases hjoinProps with ⟨rLTy, bLTy, hltySink, hjpSubRet, hrSub, hbSub, hrChk, hbChk⟩
            let sig : JoinSig := { params := params, joinPc := joinPc, retLTy := lty }
            have hjenv'Safe : joinEnvSinksAllowed L ((label, sig) :: jenv) = true := by
              unfold joinEnvSinksAllowed
              simp only [List.all_cons, sig, Bool.and_eq_true]
              exact ⟨⟨hesafe.1.1, hltySink⟩, hjenvSafe⟩
            have hjenv'Sub : ∀ p ∈ (label, sig) :: jenv, p.2.joinPc.subset p.2.retLTy.tags = true := by
              intro p hp; rcases List.mem_cons.mp hp with rfl | htl; exact hjpSubRet; exact hjenvSub p htl
            have hnjB1 : OutcomeNormalOrJump (eval fuel' prog env1 pc w1 body) := by
              cases ho : eval fuel' prog env1 pc w1 body <;> rw [ho] at hnj1 <;> first | contradiction | trivial
            have hnjB2 : OutcomeNormalOrJump (eval fuel' prog env2 pc w2 body) := by
              cases ho : eval fuel' prog env2 pc w2 body <;> rw [ho] at hnj2 <;> first | contradiction | trivial
            have hbEq := (ihE hprog hsafeProg env1 env2 ((label, sig) :: jenv) pc inSpec w1 w2 body bLTy
              henv hjenv'Safe hjenv'Sub hw hprogDB1 hprogDB2 henvCl1 henvCl2
              hesafe.2 hens.2 hesup.2 herB1 herB2 hbChk hnjB1 hnjB2).subtype hbSub
            have hbWf1 := hsound'.2.2.1 hprog env1 ((label, sig) :: jenv) pc inSpec w1 body bLTy henv.wf_left hw.wf1 hbChk
            have hbWf2 := hsound'.2.2.1 hprog env2 ((label, sig) :: jenv) pc inSpec w2 body bLTy henv.wf_right hw.wf2 (henv.envToTyEnv_eq ▸ hbChk)
            have hbDb1 := hdb'.1 hprog hsafeProg env1 pc w1 body hprogDB1 henvCl1 hesafe.2 hens.2 hesup.2 herB1
            have hbDb2 := hdb'.1 hprog hsafeProg env2 pc w2 body hprogDB2 henvCl2 hesafe.2 hens.2 (henv.envToTyEnv_eq ▸ hesup.2) herB2
            cases hjpLow : joinPc.subset L
            · -- High `joinPc`: if both jump to `lbl1 = lbl2 ≠ label` at low `joinPc` (`Or.inl`), lockstep outer jump;
              -- otherwise `lty.tags ⊈ L`, any `evalJoinLoop` is world-confined & jumps high in `jenv`!
              have hltyHigh : lty.tags.subset L = false := by
                cases hs : lty.tags.subset L; rfl
                have := TagSet.subset_trans hjpSubRet hs; rw [hjpLow] at this; nomatch this
              -- Helper for one side's post-body step when `joinPc ⊈ L`
              rcases hbEq with ⟨hwb, hbPay⟩
              cases hoB1 : eval fuel' prog env1 pc w1 body <;> rw [hoB1] at hnjB1 hnj1 hbWf1 hbDb1 hwb hbPay <;> try contradiction
              all_goals (cases hoB2 : eval fuel' prog env2 pc w2 body <;> rw [hoB2] at hnjB2 hnj2 hbWf2 hbDb2 hwb hbPay <;> try contradiction)
              all_goals (dsimp only at hnj1 hnj2 ⊢)
              · -- (.ok, .ok)
                exact ⟨hwb, hbPay⟩
              · -- (.ok, .jumped)
                rename_i v1 wb1 lbl2 vs2 wb2
                dsimp only [outWorld] at hwb
                rcases hbPay with ⟨_, sig2, hlk2, hs2F⟩
                cases hbWf1 with | ok hv1 _ =>
                have hsV1 : valSafeForNI L v1 = true := by
                  rcases hsc'.1 hprog hsafeProg env1 _ pc inSpec w1 body bLTy henv.wf_left henv.safe_left henvNs1 hjenv'Safe hw.wf1 hesafe.2 hens.2 hbChk with ⟨hs1, _, _⟩
                  rw [hoB1] at hs1; exact hs1
                have hsTySub : bLTy.ty = lty.ty := by simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hbSub; exact hbSub.1
                cases hlbl2 : (lbl2 == label)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  have hne : lbl2 ≠ label := fun e => by subst e; simp at hlbl2
                  simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk2
                  exact ⟨hwb, hltyHigh, sig2, hlk2, hs2F⟩
                · simp only [hlbl2, ↓reduceIte] at hnj2 ⊢
                  cases hlen2 : (vs2.length != params.length)
                  · simp only [hlen2, Bool.false_eq_true, ↓reduceIte] at hnj2 ⊢
                    have hlen2Eq : vs2.length = params.length := bne_eq_false_iff_eq.mp hlen2
                    cases hbWf2 with | @jumped _ _ _ bSig2 hlkB2 hjWf2 hwb2 =>
                    have heq2 : label = lbl2 := (beq_iff_eq.mp hlbl2).symm
                    simp only [lookupJoinEnv, heq2, ↓reduceIte, Option.some.injEq] at hlkB2; subst hlkB2
                    have hcurWf2 := extendEnv_wf hjWf2 henv.wf_right
                    have ⟨hbSafe2, hbNs2⟩ : valListSafeForNI L vs2 = true ∧ valListNoSpecCalls prog vs2 = true := by
                      rcases hsc'.1 hprog hsafeProg env2 _ pc inSpec w2 body bLTy henv.wf_right henv.safe_right henvNs2 hjenv'Safe hw.wf2 hesafe.2 hens.2 (henv.envToTyEnv_eq ▸ hbChk) with ⟨hs2, hns2, _⟩
                      rw [hoB2] at hs2 hns2; exact ⟨hs2, hns2⟩
                    have hcurSafe2 := extendEnv_safeForNI hesafe.1.1 hbSafe2 henv.safe_right
                    have hcurNs2 := extendEnv_noSpecCalls (params := params) hbNs2 henvNs2
                    have hcurTy2 : envToTyEnv ((List.zip params vs2).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env2) =
                        extendTyEnv (envToTyEnv env2) params := by
                      rw [envToTyEnv_append, envToTyEnv_zip_params params vs2 hlen2Eq, extendTyEnv]
                    have hrTyEq : rLTy.ty = lty.ty := by simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hrSub; exact hrSub.1
                    rcases hsc'.2.1 hprog hsafeProg env2 _ jenv label params joinPc lty rLTy inSpec rhs wb2
                      henv.wf_right henv.safe_right henvNs2 hcurWf2 hcurSafe2 hcurNs2 hcurTy2 hjenvSafe hesafe.1.1 hltySink hwb2 hesafe.1.2 hens.1 (henv.envToTyEnv_eq ▸ hrChk) hrTyEq with ⟨hsJL2, _, hcJL2⟩
                    have hwfJL2 := hsound'.2.2.2.1 hprog env2 _ jenv label params joinPc lty rLTy inSpec rhs wb2
                      henv.wf_right hcurWf2 hcurTy2 hwb2 (henv.envToTyEnv_eq ▸ hrChk) hrTyEq
                    have hcJL2' := hcJL2 hjpLow
                    apply joinOutcomeEquiv_of_high hwb hltyHigh (by trivial) hnj2 rfl
                    · cases ho : evalJoinLoop fuel' prog env2 label params joinPc rhs _ wb2 <;> rw [ho] at hnj2 hcJL2' <;> first | contradiction | exact hcJL2'
                    · intro v _ ho; injection ho with ev _; subst ev; exact ⟨hsTySub ▸ hv1, hsV1⟩
                    · intro v _ ho; rw [ho] at hwfJL2 hsJL2; cases hwfJL2 with | ok hv _ => exact ⟨hv, hsJL2⟩
                    · intro _ _ _ ho; nomatch ho
                    · exact fun lbl vs w' ho => hjmp'.2 hprog env2 _ jenv label params joinPc lty rLTy inSpec rhs wb2 lbl vs w' henv.wf_right hcurWf2 hcurTy2 hwb2 (henv.envToTyEnv_eq ▸ hrChk) hjpLow ho
                  · simp only [hlen2, ↓reduceIte, OutcomeNormalOrJump] at hnj2
              · -- (.jumped, .ok)
                rename_i lbl1 vs1 wb1 v2 wb2
                dsimp only [outWorld] at hwb
                rcases hbPay with ⟨⟨sig1, hlk1, hs1F⟩, _⟩
                cases hbWf2 with | ok hv2 _ =>
                have hsV2 : valSafeForNI L v2 = true := by
                  rcases hsc'.1 hprog hsafeProg env2 _ pc inSpec w2 body bLTy henv.wf_right henv.safe_right henvNs2 hjenv'Safe hw.wf2 hesafe.2 hens.2 (henv.envToTyEnv_eq ▸ hbChk) with ⟨hs2, _, _⟩
                  rw [hoB2] at hs2; exact hs2
                have hsTySub : bLTy.ty = lty.ty := by simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hbSub; exact hbSub.1
                cases hlbl1 : (lbl1 == label)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  have hne : lbl1 ≠ label := fun e => by subst e; simp at hlbl1
                  simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk1
                  exact ⟨hwb, ⟨sig1, hlk1, hs1F⟩, hltyHigh⟩
                · simp only [hlbl1, ↓reduceIte] at hnj1 ⊢
                  cases hlen1 : (vs1.length != params.length)
                  · simp only [hlen1, Bool.false_eq_true, ↓reduceIte] at hnj1 ⊢
                    have hlen1Eq : vs1.length = params.length := bne_eq_false_iff_eq.mp hlen1
                    cases hbWf1 with | @jumped _ _ _ bSig1 hlkB1 hjWf1 hwb1 =>
                    have heq1 : label = lbl1 := (beq_iff_eq.mp hlbl1).symm
                    simp only [lookupJoinEnv, heq1, ↓reduceIte, Option.some.injEq] at hlkB1; subst hlkB1
                    have hcurWf1 := extendEnv_wf hjWf1 henv.wf_left
                    have ⟨hbSafe1, hbNs1⟩ : valListSafeForNI L vs1 = true ∧ valListNoSpecCalls prog vs1 = true := by
                      rcases hsc'.1 hprog hsafeProg env1 _ pc inSpec w1 body bLTy henv.wf_left henv.safe_left henvNs1 hjenv'Safe hw.wf1 hesafe.2 hens.2 hbChk with ⟨hs1, hns1, _⟩
                      rw [hoB1] at hs1 hns1; exact ⟨hs1, hns1⟩
                    have hcurSafe1 := extendEnv_safeForNI hesafe.1.1 hbSafe1 henv.safe_left
                    have hcurNs1 := extendEnv_noSpecCalls (params := params) hbNs1 henvNs1
                    have hcurTy1 : envToTyEnv ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env1) =
                        extendTyEnv (envToTyEnv env1) params := by
                      rw [envToTyEnv_append, envToTyEnv_zip_params params vs1 hlen1Eq, extendTyEnv]
                    have hrTyEq : rLTy.ty = lty.ty := by simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hrSub; exact hrSub.1
                    rcases hsc'.2.1 hprog hsafeProg env1 _ jenv label params joinPc lty rLTy inSpec rhs wb1
                      henv.wf_left henv.safe_left henvNs1 hcurWf1 hcurSafe1 hcurNs1 hcurTy1 hjenvSafe hesafe.1.1 hltySink hwb1 hesafe.1.2 hens.1 hrChk hrTyEq with ⟨hsJL1, _, hcJL1⟩
                    have hwfJL1 := hsound'.2.2.2.1 hprog env1 _ jenv label params joinPc lty rLTy inSpec rhs wb1
                      henv.wf_left hcurWf1 hcurTy1 hwb1 hrChk hrTyEq
                    have hcJL1' := hcJL1 hjpLow
                    apply joinOutcomeEquiv_of_high hwb hltyHigh hnj1 (by trivial)
                    · cases ho : evalJoinLoop fuel' prog env1 label params joinPc rhs _ wb1 <;> rw [ho] at hnj1 hcJL1' <;> first | contradiction | exact hcJL1'
                    · rfl
                    · intro v _ ho; rw [ho] at hwfJL1 hsJL1; cases hwfJL1 with | ok hv _ => exact ⟨hv, hsJL1⟩
                    · intro v _ ho; injection ho with ev _; subst ev; exact ⟨hsTySub ▸ hv2, hsV2⟩
                    · exact fun lbl vs w' ho => hjmp'.2 hprog env1 _ jenv label params joinPc lty rLTy inSpec rhs wb1 lbl vs w' henv.wf_left hcurWf1 hcurTy1 hwb1 hrChk hjpLow ho
                    · intro _ _ _ ho; nomatch ho
                  · simp only [hlen1, ↓reduceIte, OutcomeNormalOrJump] at hnj1
              · -- (.jumped, .jumped)
                rename_i lbl1 vs1 wb1 lbl2 vs2 wb2
                dsimp only [outWorld] at hwb
                rcases hbPay with ⟨rfl, sig0, hlk0, hs0L, hvsEq⟩ | ⟨⟨sig1, hlk1, hs1F⟩, ⟨sig2, hlk2, hs2F⟩⟩
                · -- Lockstep low jump: cannot be `label` since `joinPc.subset L = false`!
                  cases hlbl : (lbl1 == label)
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    have hne : lbl1 ≠ label := fun e => by subst e; simp at hlbl
                    simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk0
                    exact ⟨hwb, Or.inl ⟨rfl, sig0, hlk0, hs0L, hvsEq⟩⟩
                  · have heq : label = lbl1 := (beq_iff_eq.mp hlbl).symm
                    simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlk0
                    subst hlk0; dsimp only [sig] at hs0L; rw [hjpLow] at hs0L; nomatch hs0L
                · -- Both high jumps: each either passes through (`lbl ≠ label`) or enters `evalJoinLoop` at `joinPc ⊈ L`!
                  have hrTyEq : rLTy.ty = lty.ty := by simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hrSub; exact hrSub.1
                  have hside1 : outWorld (if lbl1 == label then if vs1.length != params.length then .wrong else evalJoinLoop fuel' prog env1 label params joinPc rhs ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env1) wb1 else .jumped lbl1 vs1 wb1) = wb1 ∧
                      (∀ v w', (if lbl1 == label then if vs1.length != params.length then .wrong else evalJoinLoop fuel' prog env1 label params joinPc rhs ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env1) wb1 else .jumped lbl1 vs1 wb1) = .ok v w' → ValWf prog v lty.ty ∧ valSafeForNI L v = true) ∧
                      (∀ l vs w', (if lbl1 == label then if vs1.length != params.length then .wrong else evalJoinLoop fuel' prog env1 label params joinPc rhs ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env1) wb1 else .jumped lbl1 vs1 wb1) = .jumped l vs w' → ∃ s, lookupJoinEnv jenv l = some s ∧ s.joinPc.subset L = false) := by
                    cases hlbl1 : (lbl1 == label)
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      have hne : lbl1 ≠ label := fun e => by subst e; simp at hlbl1
                      simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk1
                      exact ⟨rfl, (fun _ _ ho => nomatch ho), fun l _ _ ho => by injection ho with el _ _; subst el; exact ⟨sig1, hlk1, hs1F⟩⟩
                    · simp only [↓reduceIte]; simp only [hlbl1, ↓reduceIte] at hnj1
                      split at hnj1; (simp only [OutcomeNormalOrJump] at hnj1)
                      rename_i hlen1; simp [hlen1]
                      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlen1
                      cases hbWf1 with | @jumped _ _ _ bSig1 hlkB1 hjWf1 hwb1 =>
                      have heq1 : label = lbl1 := (beq_iff_eq.mp hlbl1).symm
                      simp only [lookupJoinEnv, heq1, ↓reduceIte, Option.some.injEq] at hlkB1; subst hlkB1
                      have hcurWf1 := extendEnv_wf hjWf1 henv.wf_left
                      have ⟨hbSafe1, hbNs1⟩ : valListSafeForNI L vs1 = true ∧ valListNoSpecCalls prog vs1 = true := by
                        rcases hsc'.1 hprog hsafeProg env1 _ pc inSpec w1 body bLTy henv.wf_left henv.safe_left henvNs1 hjenv'Safe hw.wf1 hesafe.2 hens.2 hbChk with ⟨hs1, hns1, _⟩
                        rw [hoB1] at hs1 hns1; exact ⟨hs1, hns1⟩
                      have hcurSafe1 := extendEnv_safeForNI hesafe.1.1 hbSafe1 henv.safe_left
                      have hcurNs1 := extendEnv_noSpecCalls (params := params) hbNs1 henvNs1
                      have hcurTy1 : envToTyEnv ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env1) =
                          extendTyEnv (envToTyEnv env1) params := by
                        rw [envToTyEnv_append, envToTyEnv_zip_params params vs1 hlen1, extendTyEnv]
                      rcases hsc'.2.1 hprog hsafeProg env1 _ jenv label params joinPc lty rLTy inSpec rhs wb1
                        henv.wf_left henv.safe_left henvNs1 hcurWf1 hcurSafe1 hcurNs1 hcurTy1 hjenvSafe hesafe.1.1 hltySink hwb1 hesafe.1.2 hens.1 hrChk hrTyEq with ⟨hsJL1, _, hcJL1⟩
                      have hwfJL1 := hsound'.2.2.2.1 hprog env1 _ jenv label params joinPc lty rLTy inSpec rhs wb1
                        henv.wf_left hcurWf1 hcurTy1 hwb1 hrChk hrTyEq
                      have hcJL1' := hcJL1 hjpLow
                      refine ⟨by cases ho : evalJoinLoop fuel' prog env1 label params joinPc rhs _ wb1 <;> rw [ho] at hnj1 hcJL1' <;> first | contradiction | exact hcJL1',
                              fun v _ ho => by rw [ho] at hwfJL1 hsJL1; cases hwfJL1 with | ok hv _ => exact ⟨hv, hsJL1⟩,
                              fun l vs w' ho => hjmp'.2 hprog env1 _ jenv label params joinPc lty rLTy inSpec rhs wb1 l vs w' henv.wf_left hcurWf1 hcurTy1 hwb1 hrChk hjpLow ho⟩
                  have hside2 : outWorld (if lbl2 == label then if vs2.length != params.length then .wrong else evalJoinLoop fuel' prog env2 label params joinPc rhs ((List.zip params vs2).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env2) wb2 else .jumped lbl2 vs2 wb2) = wb2 ∧
                      (∀ v w', (if lbl2 == label then if vs2.length != params.length then .wrong else evalJoinLoop fuel' prog env2 label params joinPc rhs ((List.zip params vs2).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env2) wb2 else .jumped lbl2 vs2 wb2) = .ok v w' → ValWf prog v lty.ty ∧ valSafeForNI L v = true) ∧
                      (∀ l vs w', (if lbl2 == label then if vs2.length != params.length then .wrong else evalJoinLoop fuel' prog env2 label params joinPc rhs ((List.zip params vs2).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env2) wb2 else .jumped lbl2 vs2 wb2) = .jumped l vs w' → ∃ s, lookupJoinEnv jenv l = some s ∧ s.joinPc.subset L = false) := by
                    cases hlbl2 : (lbl2 == label)
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      have hne : lbl2 ≠ label := fun e => by subst e; simp at hlbl2
                      simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk2
                      exact ⟨rfl, (fun _ _ ho => nomatch ho), fun l _ _ ho => by injection ho with el _ _; subst el; exact ⟨sig2, hlk2, hs2F⟩⟩
                    · simp only [↓reduceIte]; simp only [hlbl2, ↓reduceIte] at hnj2
                      split at hnj2; (simp only [OutcomeNormalOrJump] at hnj2)
                      rename_i hlen2; simp [hlen2]
                      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hlen2
                      cases hbWf2 with | @jumped _ _ _ bSig2 hlkB2 hjWf2 hwb2 =>
                      have heq2 : label = lbl2 := (beq_iff_eq.mp hlbl2).symm
                      simp only [lookupJoinEnv, heq2, ↓reduceIte, Option.some.injEq] at hlkB2; subst hlkB2
                      have hcurWf2 := extendEnv_wf hjWf2 henv.wf_right
                      have ⟨hbSafe2, hbNs2⟩ : valListSafeForNI L vs2 = true ∧ valListNoSpecCalls prog vs2 = true := by
                        rcases hsc'.1 hprog hsafeProg env2 _ pc inSpec w2 body bLTy henv.wf_right henv.safe_right henvNs2 hjenv'Safe hw.wf2 hesafe.2 hens.2 (henv.envToTyEnv_eq ▸ hbChk) with ⟨hs2, hns2, _⟩
                        rw [hoB2] at hs2 hns2; exact ⟨hs2, hns2⟩
                      have hcurSafe2 := extendEnv_safeForNI hesafe.1.1 hbSafe2 henv.safe_right
                      have hcurNs2 := extendEnv_noSpecCalls (params := params) hbNs2 henvNs2
                      have hcurTy2 : envToTyEnv ((List.zip params vs2).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env2) =
                          extendTyEnv (envToTyEnv env2) params := by
                        rw [envToTyEnv_append, envToTyEnv_zip_params params vs2 hlen2, extendTyEnv]
                      rcases hsc'.2.1 hprog hsafeProg env2 _ jenv label params joinPc lty rLTy inSpec rhs wb2
                        henv.wf_right henv.safe_right henvNs2 hcurWf2 hcurSafe2 hcurNs2 hcurTy2 hjenvSafe hesafe.1.1 hltySink hwb2 hesafe.1.2 hens.1 (henv.envToTyEnv_eq ▸ hrChk) hrTyEq with ⟨hsJL2, _, hcJL2⟩
                      have hwfJL2 := hsound'.2.2.2.1 hprog env2 _ jenv label params joinPc lty rLTy inSpec rhs wb2
                        henv.wf_right hcurWf2 hcurTy2 hwb2 (henv.envToTyEnv_eq ▸ hrChk) hrTyEq
                      have hcJL2' := hcJL2 hjpLow
                      refine ⟨by cases ho : evalJoinLoop fuel' prog env2 label params joinPc rhs _ wb2 <;> rw [ho] at hnj2 hcJL2' <;> first | contradiction | exact hcJL2',
                              fun v _ ho => by rw [ho] at hwfJL2 hsJL2; cases hwfJL2 with | ok hv _ => exact ⟨hv, hsJL2⟩,
                              fun l vs w' ho => hjmp'.2 hprog env2 _ jenv label params joinPc lty rLTy inSpec rhs wb2 l vs w' henv.wf_right hcurWf2 hcurTy2 hwb2 (henv.envToTyEnv_eq ▸ hrChk) hjpLow ho⟩
                  exact joinOutcomeEquiv_of_high hwb hltyHigh hnj1 hnj2 hside1.1 hside2.1 hside1.2.1 hside2.2.1 hside1.2.2 hside2.2.2
            · -- Low `joinPc` (`joinPc ⊆ L`): `sig` is low, so ANY high jump must have `lbl ≠ label`!
              rcases hbEq with ⟨hwb, hbPay⟩
              cases hoB1 : eval fuel' prog env1 pc w1 body <;> rw [hoB1] at hnjB1 hnj1 hbDb1 hwb hbPay <;> try contradiction
              all_goals (cases hoB2 : eval fuel' prog env2 pc w2 body <;> rw [hoB2] at hnjB2 hnj2 hbDb2 hwb hbPay <;> try contradiction)
              all_goals (dsimp only at hnj1 hnj2 ⊢)
              · exact ⟨hwb, hbPay⟩
              · rename_i lbl2 _ _
                rcases hbPay with ⟨hh, sig2, hlk2, hs2F⟩
                have hne : lbl2 ≠ label := by
                  intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk2
                  subst hlk2; dsimp only [sig] at hs2F; rw [hjpLow] at hs2F; nomatch hs2F
                have hlblF : (lbl2 == label) = false := by cases h : (lbl2 == label); rfl; exact absurd (beq_iff_eq.mp h) hne
                simp only [hlblF, Bool.false_eq_true, ↓reduceIte]
                simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk2
                exact ⟨hwb, hh, sig2, hlk2, hs2F⟩
              · rename_i lbl1 _ _ _ _
                rcases hbPay with ⟨⟨sig1, hlk1, hs1F⟩, hh⟩
                have hne : lbl1 ≠ label := by
                  intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk1
                  subst hlk1; dsimp only [sig] at hs1F; rw [hjpLow] at hs1F; nomatch hs1F
                have hlblF : (lbl1 == label) = false := by cases h : (lbl1 == label); rfl; exact absurd (beq_iff_eq.mp h) hne
                simp only [hlblF, Bool.false_eq_true, ↓reduceIte]
                simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk1
                exact ⟨hwb, ⟨sig1, hlk1, hs1F⟩, hh⟩
              · rename_i lbl1 vs1 wb1 lbl2 vs2 wb2
                rcases hbPay with ⟨rfl, sig0, hlk0, hs0L, hvsEq⟩ | ⟨⟨sig1, hlk1, hs1F⟩, ⟨sig2, hlk2, hs2F⟩⟩
                · cases hlbl : (lbl1 == label)
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    have hne : lbl1 ≠ label := fun e => by subst e; simp at hlbl
                    simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk0
                    exact ⟨hwb, Or.inl ⟨rfl, sig0, hlk0, hs0L, hvsEq⟩⟩
                  · simp only [hlbl, ↓reduceIte] at hnj1 hnj2 ⊢
                    have heq : label = lbl1 := (beq_iff_eq.mp hlbl).symm
                    simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlk0; subst hlk0
                    rcases hvsEq.length_eq with ⟨hl1, hl2⟩
                    dsimp only [sig] at hl1 hl2
                    rw [List.length_map] at hl1 hl2
                    simp only [hl1, hl2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hnj1 hnj2 ⊢
                    have hcurEq := extendEnv_equiv hesafe.1.1 hvsEq henv
                    have hcurTy1 : envToTyEnv ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ env1) =
                        extendTyEnv (envToTyEnv env1) params := by
                      rw [envToTyEnv_append, envToTyEnv_zip_params params vs1 hl1, extendTyEnv]
                    exact ihJL hprog hsafeProg env1 env2 _ _ jenv label params joinPc lty rLTy inSpec rhs wb1 wb2
                      henv hcurEq hcurTy1 hjenvSafe hjenvSub hesafe.1.1 hltySink hjpSubRet hrSub hwb
                      (progRespectsDB_congr hbDb1.2 hprogDB1) (progRespectsDB_congr hbDb2.2 hprogDB2)
                      (envClosureSafe_congr hbDb1.2 henvCl1) (envClosureSafe_congr hbDb2.2 henvCl2)
                      (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hbDb1.2 hbDb1.1)) (envClosureSafe_congr hbDb1.2 henvCl1))
                      (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hbDb2.2 hbDb2.1)) (envClosureSafe_congr hbDb2.2 henvCl2))
                      hesafe.1.2 hens.1 hesup.1 (exprRespectsDB_congr hbDb1.2 herR1) (exprRespectsDB_congr hbDb2.2 herR2)
                      hrChk hnj1 hnj2
                · have hne1 : lbl1 ≠ label := by
                    intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk1
                    subst hlk1; dsimp only [sig] at hs1F; rw [hjpLow] at hs1F; nomatch hs1F
                  have hne2 : lbl2 ≠ label := by
                    intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk2
                    subst hlk2; dsimp only [sig] at hs2F; rw [hjpLow] at hs2F; nomatch hs2F
                  have hf1 : (lbl1 == label) = false := by cases h : (lbl1 == label); rfl; exact absurd (beq_iff_eq.mp h) hne1
                  have hf2 : (lbl2 == label) = false := by cases h : (lbl2 == label); rfl; exact absurd (beq_iff_eq.mp h) hne2
                  simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte]
                  simp only [lookupJoinEnv, Ne.symm hne1, Ne.symm hne2, ↓reduceIte] at hlk1 hlk2
                  exact ⟨hwb, Or.inr ⟨⟨sig1, hlk1, hs1F⟩, ⟨sig2, hlk2, hs2F⟩⟩⟩
        | jump label args =>
          dsimp only at hnj1 hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
          rename_i argLTys; dsimp only at hchk
          cases hl : lookupJoinEnv jenv label <;> rw [hl] at hchk <;> try contradiction
          rename_i sig; dsimp only at hchk
          repeat (split at hchk <;> try contradiction)
          rename_i harity hzipSub
          simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harity
          simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true] at hzipSub
          injection hchk with el; subst el
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) w1 args with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0)
              hw.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok argVals1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) w2 args with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0)
                hw.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok argVals2 wa2 =>
              dsimp only
              rcases evalSeq_ni ihE hprog hsafeProg henv hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe hens hesup her1 her2 ha hseq1 hseq2 with ⟨hargsEq, hwa⟩
              have hvalsEq := hargsEq.addTags_subtype_zip (pc := pc) (by simp [harity]) (fun p hp => (hzipSub p hp).1)
              refine ⟨hwa, ?_⟩
              cases hjp : sig.joinPc.subset L
              · exact Or.inr ⟨⟨sig, hl, hjp⟩, ⟨sig, hl, hjp⟩⟩
              · exact Or.inl ⟨rfl, sig, hl, hjp, hvalsEq⟩
        | tuple elems =>
          dsimp only at hnj1 hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec elems <;> rw [ha] at hchk <;> try contradiction
          injection hchk with el; subst el
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) w1 elems with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0) hw.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok vs1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) w2 elems with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0) hw.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok vs2 wa2 =>
              dsimp only
              rcases evalSeq_ni ihE hprog hsafeProg henv hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe hens hesup her1 her2 ha hseq1 hseq2 with ⟨hvsEq, hwa⟩
              exact ⟨hwa, ValEquiv.mk_smart (.tuple hvsEq.wf_left) (.tuple hvsEq.wf_right)
                hvsEq.safe_left hvsEq.safe_right (fun _ => .tuple hvsEq)⟩
        | proj tup idx =>
          dsimp only at hnj1 hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ht : checkExpr prog (envToTyEnv env1) [] pc inSpec tup <;> rw [ht] at hchk <;> try contradiction
          rename_i tupLTy; dsimp only at hchk
          cases tupLTy with | mk tty tTs =>
          cases tty <;> dsimp only [LTy.ty] at hchk <;> try contradiction
          rename_i elemLTys
          cases hg : elemLTys[idx]? <;> rw [hg] at hchk <;> try contradiction
          rename_i eLTy; injection hchk with el; subst el
          have htOutWf1 := hsound'.2.2.1 hprog env1 [] pc inSpec w1 tup _ henv.wf_left hw.wf1 ht
          have htOutWf2 := hsound'.2.2.1 hprog env2 [] pc inSpec w2 tup _ henv.wf_right hw.wf2 (henv.envToTyEnv_eq ▸ ht)
          cases hoT1 : eval fuel' prog env1 pc w1 tup with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoT1] at hnj1; dsimp only [OutcomeNormalOrJump] at hnj1
          | jumped _ _ _ => rw [hoT1] at htOutWf1; exact absurd rfl htOutWf1.not_jumped_nil
          | ok tv1 wt1 =>
          cases hoT2 : eval fuel' prog env2 pc w2 tup with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoT2] at hnj2; dsimp only [OutcomeNormalOrJump] at hnj2
          | jumped _ _ _ => rw [hoT2] at htOutWf2; exact absurd rfl htOutWf2.not_jumped_nil
          | ok tv2 wt2 =>
          rw [hoT1] at hnj1; rw [hoT2] at hnj2
          have htEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 tup _
            henv rfl (fun _ hm => nomatch hm) hw hprogDB1 hprogDB2 henvCl1 henvCl2
            hesafe hens hesup her1 her2 ht (by rw [hoT1]; trivial) (by rw [hoT2]; trivial)
          rw [hoT1, hoT2] at htEq; rcases htEq with ⟨hwt, htvEq⟩
          cases htvEq.wf_left with | tuple hvsWf1 =>
          cases htvEq.wf_right with | tuple hvsWf2 =>
          rcases hvsWf1.getElem?_wf hg with ⟨v1, hg1, hvWf1⟩
          rcases hvsWf2.getElem?_wf hg with ⟨v2, hg2, hvWf2⟩
          simp only [hg1, hg2]
          have hs1 := (valListSafeForNI_iff.mp htvEq.safe_left) v1 (List.mem_of_getElem? hg1)
          have hs2 := (valListSafeForNI_iff.mp htvEq.safe_right) v2 (List.mem_of_getElem? hg2)
          have htyE : (eLTy.addTags ((LTy.mk (Ty.tuple elemLTys) tTs).tags.union pc)).ty = eLTy.ty := LTy.ty_addTags _ _
          refine ⟨hwt, ValEquiv.mk_smart (htyE.symm ▸ hvWf1) (htyE.symm ▸ hvWf2) hs1 hs2 (fun hlow => ?_)⟩
          simp only [LTy.tags_addTags, TagSet.union_subset_iff, Bool.and_eq_true] at hlow
          cases htvEq.payload hlow.2.1 with | tuple hvsEq =>
          rcases hvsEq.getElem? hg with ⟨_, _, hg1', hg2', hvEq⟩
          rw [hg1] at hg1'; injection hg1' with e1; subst e1
          rw [hg2] at hg2'; injection hg2' with e2; subst e2
          exact htyE.symm ▸ hvEq.payload hlow.1
        | ctor tName cName args =>
          dsimp only at hnj1 hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
          rename_i argLTys; dsimp only at hchk
          cases hfd : prog.findData? tName <;> rw [hfd] at hchk <;> try contradiction
          rename_i dDecl; dsimp only at hchk
          cases hfc : dDecl.ctors.find? (fun c => c.name == cName) <;> rw [hfc] at hchk <;> try contradiction
          rename_i cDecl; dsimp only at hchk
          split at hchk <;> try contradiction
          rename_i harity; simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at harity
          split at hchk <;> try contradiction
          rename_i htyAll; simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, decide_eq_true_eq] at htyAll
          injection hchk with el; subst el
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) w1 args with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0) hw.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok vs1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) w2 args with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0) hw.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok vs2 wa2 =>
              dsimp only
              rcases evalSeq_ni ihE hprog hsafeProg henv hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe hens hesup her1 her2 ha hseq1 hseq2 with ⟨hvsEq, hwa⟩
              have hcWf1 : ValWf prog (.ctor tName cName vs1) (.data tName) :=
                .ctor hfd hfc (valListWf_of_zip_tyEq hvsEq.wf_left harity htyAll)
              have hcWf2 : ValWf prog (.ctor tName cName vs2) (.data tName) :=
                .ctor hfd hfc (valListWf_of_zip_tyEq hvsEq.wf_right harity htyAll)
              refine ⟨hwa, ValEquiv.mk_smart hcWf1 hcWf2 hvsEq.safe_left hvsEq.safe_right (fun hlow => ?_)⟩
              simp only [LTy.tags, TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hlow
              have hfSorts : ∀ f ∈ cDecl.fields, isSortableTy f.ty = true := by
                unfold progDatasSortableForNI at hd
                simp only [List.all_eq_true] at hd
                exact fun f hf => hd dDecl (List.mem_of_find?_eq_some hfd) cDecl (List.mem_of_find?_eq_some hfc) f hf
              have hvsIdent : vs1 = vs2 := by
                let rec goEq {xs1 xs2 : List Val} {as1 fs : List LTy}
                    (hx : ValListEquiv prog L xs1 xs2 as1) (hl : as1.length = fs.length)
                    (ht : ∀ p ∈ List.zip as1 fs, p.1.ty = p.2.ty)
                    (hfs : ∀ f ∈ fs, isSortableTy f.ty = true)
                    (heff : ∀ a ∈ as1, a.effectiveTags.subset L = true) : xs1 = xs2 := by
                  cases hx with
                  | nil => rfl
                  | @cons x1 x2 _ _ a _ hhd htl =>
                    cases fs with
                    | nil => simp at hl
                    | cons f fsTl =>
                      have haS : isSortableTy a.ty = true := ht (a, f) (.head _) ▸ hfs f (.head _)
                      exact congrArg2 List.cons
                        (hhd.effectiveTags_sortable_eq hd haS (heff a (.head _)))
                        (goEq htl (Nat.succ.inj hl) (fun p hp => ht p (.tail _ hp))
                          (fun g hg => hfs g (.tail _ hg)) (fun b hb => heff b (.tail _ hb)))
                exact goEq hvsEq harity htyAll hfSorts (fun a ha => hlow.1 a.effectiveTags (List.mem_map_of_mem ha))
              subst hvsIdent
              cases hcWf1 with | ctor hfd' hfc' hvsC =>
              rw [hfd] at hfd'; injection hfd' with ed; subst ed
              rw [hfc] at hfc'; injection hfc' with ec; subst ec
              exact .ctor hfd hfc rfl (ValListEquiv.refl_of_sortable hd hvsC (isSortableLTyList_of_forall hfSorts))
        | tableLit schema rows =>
          have hwfOut1 := hsound.2.2.1 hprog env1 jenv pc inSpec w1 _ _ henv.wf_left hw.wf1 hchkOrig
          unfold eval at hwfOut1
          unfold checkExpr at hchk
          split at hchk <;> try contradiction
          rename_i hbad1
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          injection hchk with el; subst el
          cases hwfOut1 with | ok htvWf _ =>
          cases htvWf with | table hcEq hsch hrWf =>
          refine ⟨hw, ValEquiv.mk_smart (.table hcEq hsch hrWf) (.table hcEq hsch hrWf) rfl rfl (fun _ => .table ?_)⟩
          refine ⟨.table hcEq hsch hrWf, .table hcEq hsch hrWf, ?_, ?_, ?_⟩
          · have hgb : schema.groupedBy = none := by
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Option.isSome_eq_false_iff] at hbad1
              exact Option.isNone_iff_eq_none.mp hbad1.1.2
            exact groupingLow_of_groupedBy_none hgb hsch
          · intro _
            have hrefl : RelList (RowEquiv L schema.cols)
                (rows.map (fun rl => ({ cells := rl.cells.map evalLiteral, groupMeta := none } : TableRow)))
                (rows.map (fun rl => ({ cells := rl.cells.map evalLiteral, groupMeta := none } : TableRow))) :=
              RelList.refl_of_forall (fun r hr => CellsEquiv.of_all_eq schema.cols r.cells (hrWf.to_forall r hr).length_eq)
            split; exact hrefl; exact ⟨_, .refl _, hrefl⟩
          · intro _ _
            have hrefl : RelList (fun r1 r2 => RowEquiv L schema.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta)
                (rows.map (fun rl => ({ cells := rl.cells.map evalLiteral, groupMeta := none } : TableRow)))
                (rows.map (fun rl => ({ cells := rl.cells.map evalLiteral, groupMeta := none } : TableRow))) :=
              RelList.refl_of_forall (fun r hr => ⟨CellsEquiv.of_all_eq schema.cols r.cells (hrWf.to_forall r hr).length_eq, rfl⟩)
            split; exact hrefl; exact ⟨_, .refl _, hrefl⟩
        | prim op args =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) w1 args with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0) hw.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok vs1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) w2 args with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0) hw.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok vs2 wa2 =>
              rw [hseq1] at hnj1; rw [hseq2] at hnj2; dsimp only at hnj1 hnj2 ⊢
              cases hp1 : evalPrimOp op vs1 <;> rw [hp1] at hnj1 <;> try contradiction
              cases hp2 : evalPrimOp op vs2 <;> rw [hp2] at hnj2 <;> try contradiction
              dsimp only
              rcases evalSeq_ni ihE hprog hsafeProg henv hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe.2 hens hesup her1 her2 ha hseq1 hseq2 with ⟨hvsEq, hwa⟩
              exact ⟨hwa, evalPrimOp_ni hsafeProg hvsEq hchk hp1 hp2⟩
        | rel plan =>
          dsimp only at hnj1 hnj2 ⊢
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hp : checkPlan prog (envToTyEnv env1) pc inSpec plan <;> rw [hp] at hchk <;> try contradiction
          rename_i pTy; injection hchk with el; subst el
          have hpWf1 := hsound'.2.2.2.2 hprog env1 pc inSpec w1 plan pTy henv.wf_left hw.wf1 hp
          have hpWf2 := hsound'.2.2.2.2 hprog env2 pc inSpec w2 plan pTy henv.wf_right hw.wf2 (henv.envToTyEnv_eq ▸ hp)
          cases hoP1 : evalPlan fuel' prog env1 pc w1 plan with
          | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoP1] at hnj1; nomatch hnj1
          | jumped _ _ _ => rw [hoP1] at hpWf1; exact absurd rfl hpWf1.not_jumped_nil
          | ok v1 w1' =>
            cases hoP2 : evalPlan fuel' prog env2 pc w2 plan with
            | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hoP2] at hnj2; nomatch hnj2
            | jumped _ _ _ => rw [hoP2] at hpWf2; exact absurd rfl hpWf2.not_jumped_nil
            | ok v2 w2' =>
              rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 plan pTy v1 v2 w1' w2'
                henv hw hprogDB1 hprogDB2 henvCl1 henvCl2 hesafe hens hesup her1 her2 hp hoP1 hoP2 with ⟨hvEq, hw'⟩
              exact ⟨hw', hvEq⟩
        | host op args =>
          dsimp only at hnj1 hnj2 ⊢
          simp only [exprSafeForNI, Bool.and_eq_true] at hesafe
          unfold checkExpr at hchk; split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases ha : checkExprList prog (envToTyEnv env1) pc inSpec args <;> rw [ha] at hchk <;> try contradiction
          have hargSinks := checkExprList_sinksAllowed hsafeProg (envSafeForNI_imp_tyEnv henv.safe_left) hesafe.2 hens ha
          cases hseq1 : evalSeq (eval fuel' prog env1 pc) w1 args with
          | aborted out =>
            rw [hseq1] at hnj1
            have hnj := evalSeq_not_jumped (eval fuel' prog env1 pc)
              (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env1 [] pc inSpec w0 e0 l0 henv.wf_left hw0 hc0) hw.wf1 ha
            cases out with
            | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq1)
            | jumped _ _ _ => exact absurd hseq1 (hnj _ _ _)
            | _ => dsimp only [OutcomeNormalOrJump] at hnj1
          | ok vs1 wa1 =>
            cases hseq2 : evalSeq (eval fuel' prog env2 pc) w2 args with
            | aborted out =>
              rw [hseq2] at hnj2
              have hnj := evalSeq_not_jumped (eval fuel' prog env2 pc)
                (fun w0 e0 l0 hw0 hc0 => hsound'.2.2.1 hprog env2 [] pc inSpec w0 e0 l0 henv.wf_right hw0 hc0) hw.wf2 (henv.envToTyEnv_eq ▸ ha)
              cases out with
              | ok _ _ => exact False.elim (evalSeq_aborted_not_ok hseq2)
              | jumped _ _ _ => exact absurd hseq2 (hnj _ _ _)
              | _ => dsimp only [OutcomeNormalOrJump] at hnj2
            | ok vs2 wa2 =>
              rw [hseq1] at hnj1; rw [hseq2] at hnj2; dsimp only at hnj1 hnj2 ⊢
              rcases evalSeq_ni ihE hprog hsafeProg henv hw hprogDB1 hprogDB2 henvCl1 henvCl2
                hesafe.2 hens hesup her1 her2 ha hseq1 hseq2 with ⟨hvsEq, hwa⟩
              cases hh1 : evalHostOp prog op vs1 wa1 with
              | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hh1] at hnj1; nomatch hnj1
              | jumped _ _ _ =>
                have hhWf := evalHostOp_sound hprog hchk hvsEq.wf_left hwa.wf1
                rw [hh1] at hhWf; exact absurd rfl hhWf.not_jumped_nil
              | ok hv1 hw1' =>
                cases hh2 : evalHostOp prog op vs2 wa2 with
                | stopped _ _ | failed _ _ | wrong | outOfFuel => rw [hh2] at hnj2; nomatch hnj2
                | jumped _ _ _ =>
                  have hhWf := evalHostOp_sound hprog hchk hvsEq.wf_right hwa.wf2
                  rw [hh2] at hhWf; exact absurd rfl hhWf.not_jumped_nil
                | ok hv2 hw2' =>
                  rcases evalHostOp_ni hprog hesafe.1 hargSinks hvsEq hwa hchk hh1 hh2 with ⟨hvEq, hwFinal⟩
                  exact ⟨hwFinal, hvEq⟩
        | stop kind detail =>
          dsimp only at hnj1
          cases detail with
          | none => nomatch hnj1
          | some dExpr =>
            dsimp only at hnj1
            unfold checkExpr at hchk; dsimp only at hchk
            split at hchk <;> try contradiction
            simp only [bind, Except.bind] at hchk
            cases hdChk : checkExpr prog (envToTyEnv env1) [] pc inSpec dExpr <;> rw [hdChk] at hchk <;> try contradiction
            rw [checkExpr_inSpec_true hdChk] at hnj1; dsimp only at hnj1
            have hdWf := hsound'.2.2.1 hprog env1 [] pc inSpec w1 dExpr _ henv.wf_left hw.wf1 hdChk
            cases hoD : eval fuel' prog env1 pc w1 dExpr <;> rw [hoD] at hnj1 hdWf
            · nomatch hnj1
            · nomatch hnj1
            · nomatch hnj1
            · exact absurd rfl hdWf.not_jumped_nil
            · nomatch hnj1
            · nomatch hnj1
        | fail msgExpr =>
          dsimp only at hnj1
          unfold checkExpr at hchk
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          simp only [bind, Except.bind] at hchk
          cases hmChk : checkExpr prog (envToTyEnv env1) [] pc inSpec msgExpr <;> rw [hmChk] at hchk <;> try contradiction
          have hmWf := hsound'.2.2.1 hprog env1 [] pc inSpec w1 msgExpr _ henv.wf_left hw.wf1 hmChk
          cases hoM : eval fuel' prog env1 pc w1 msgExpr <;> rw [hoM] at hnj1 hmWf
          · rename_i mv _; cases mv <;> nomatch hnj1
          · nomatch hnj1
          · nomatch hnj1
          · exact absurd rfl hmWf.not_jumped_nil
          · nomatch hnj1
          · nomatch hnj1
-- =========================================================================
-- 2. JoinLoopNIAt (fuel' + 1)
-- =========================================================================
set_option maxHeartbeats 400000 in
private theorem joinLoop_ni_step {prog : Program} {L : TagSet} {fuel' : Nat}
    (ihE : ExprNIAt fuel' prog L) (ihJL : JoinLoopNIAt fuel' prog L) :
    JoinLoopNIAt (fuel' + 1) prog L := by
      have hsound := eval_fuel_sound prog (fuel' + 1)
      have hsc := eval_safe_and_confined_all prog L (fuel' + 1)
      have hjmp := eval_high_pc_jump_sig_all prog L (fuel' + 1)
      have hdb' := eval_preserves_db_all prog L fuel'
      intro hprog hsafeProg baseEnv1 baseEnv2 curEnv1 curEnv2 jenv label params joinPc retLTy rLTy inSpec rhs w1 w2
        hbase henvCur hcurTy1 hjenvSafe hjenvSub hparamsOk hretOk hjpSubRet hrSub hw
        hpDB1 hpDB2 hbCl1 hbCl2 hcCl1 hcCl2 hrSafe hrNs hrSup hrr1 hrr2 hrChk hnj1 hnj2
      have hcurTy2 : envToTyEnv curEnv2 = extendTyEnv (envToTyEnv baseEnv2) params := by
        rw [← henvCur.envToTyEnv_eq, hcurTy1, extendTyEnv, extendTyEnv, hbase.envToTyEnv_eq]
      have hrTyEq : rLTy.ty = retLTy.ty := by simp only [ltySubtype, Bool.and_eq_true, decide_eq_true_eq] at hrSub; exact hrSub.1
      cases hjpLow : joinPc.subset L
      · -- High `joinPc`: world-confined & jumps high in `jenv`!
        have hltyHigh : retLTy.tags.subset L = false := by
          cases hs : retLTy.tags.subset L; rfl
          have := TagSet.subset_trans hjpSubRet hs; rw [hjpLow] at this; nomatch this
        have hbNs1 := envClosureSafe_imp_noSpecCalls hbCl1
        have hbNs2 := envClosureSafe_imp_noSpecCalls hbCl2
        have hcNs1 := envClosureSafe_imp_noSpecCalls hcCl1
        have hcNs2 := envClosureSafe_imp_noSpecCalls hcCl2
        rcases hsc.2.1 hprog hsafeProg baseEnv1 curEnv1 jenv label params joinPc retLTy rLTy inSpec rhs w1
          hbase.wf_left hbase.safe_left hbNs1 henvCur.wf_left henvCur.safe_left hcNs1 hcurTy1 hjenvSafe hparamsOk hretOk hw.wf1 hrSafe hrNs hrChk hrTyEq with ⟨hs1, _, hc1⟩
        rcases hsc.2.1 hprog hsafeProg baseEnv2 curEnv2 jenv label params joinPc retLTy rLTy inSpec rhs w2
          hbase.wf_right hbase.safe_right hbNs2 henvCur.wf_right henvCur.safe_right hcNs2 hcurTy2 hjenvSafe hparamsOk hretOk hw.wf2 hrSafe hrNs (hbase.envToTyEnv_eq ▸ hrChk) hrTyEq with ⟨hs2, _, hc2⟩
        have hwf1 := hsound.2.2.2.1 hprog baseEnv1 curEnv1 jenv label params joinPc retLTy rLTy inSpec rhs w1
          hbase.wf_left henvCur.wf_left hcurTy1 hw.wf1 hrChk hrTyEq
        have hwf2 := hsound.2.2.2.1 hprog baseEnv2 curEnv2 jenv label params joinPc retLTy rLTy inSpec rhs w2
          hbase.wf_right henvCur.wf_right hcurTy2 hw.wf2 (hbase.envToTyEnv_eq ▸ hrChk) hrTyEq
        have hc1' := hc1 hjpLow; have hc2' := hc2 hjpLow
        apply joinOutcomeEquiv_of_high hw hltyHigh hnj1 hnj2
        · cases ho : evalJoinLoop (fuel' + 1) prog baseEnv1 label params joinPc rhs curEnv1 w1 <;> rw [ho] at hnj1 hc1' <;> first | contradiction | exact hc1'
        · cases ho : evalJoinLoop (fuel' + 1) prog baseEnv2 label params joinPc rhs curEnv2 w2 <;> rw [ho] at hnj2 hc2' <;> first | contradiction | exact hc2'
        · intro v _ ho; rw [ho] at hwf1 hs1; cases hwf1 with | ok hv _ => exact ⟨hv, hs1⟩
        · intro v _ ho; rw [ho] at hwf2 hs2; cases hwf2 with | ok hv _ => exact ⟨hv, hs2⟩
        · exact fun l vs w' ho => hjmp.2 hprog baseEnv1 curEnv1 jenv label params joinPc retLTy rLTy inSpec rhs w1 l vs w' hbase.wf_left henvCur.wf_left hcurTy1 hw.wf1 hrChk hjpLow ho
        · exact fun l vs w' ho => hjmp.2 hprog baseEnv2 curEnv2 jenv label params joinPc retLTy rLTy inSpec rhs w2 l vs w' hbase.wf_right henvCur.wf_right hcurTy2 hw.wf2 (hbase.envToTyEnv_eq ▸ hrChk) hjpLow ho
      · -- Low `joinPc` (`joinPc ⊆ L`)
        unfold evalJoinLoop at hnj1 hnj2 ⊢
        let sig : JoinSig := { params := params, joinPc := joinPc, retLTy := retLTy }
        have hjenv'Safe : joinEnvSinksAllowed L ((label, sig) :: jenv) = true := by
          unfold joinEnvSinksAllowed
          simp only [List.all_cons, sig, Bool.and_eq_true]
          exact ⟨⟨hparamsOk, hretOk⟩, hjenvSafe⟩
        have hjenv'Sub : ∀ p ∈ (label, sig) :: jenv, p.2.joinPc.subset p.2.retLTy.tags = true := by
          intro p hp; rcases List.mem_cons.mp hp with rfl | htl; exact hjpSubRet; exact hjenvSub p htl
        have hnjR1 : OutcomeNormalOrJump (eval fuel' prog curEnv1 joinPc w1 rhs) := by
          cases ho : eval fuel' prog curEnv1 joinPc w1 rhs <;> rw [ho] at hnj1 <;> first | contradiction | trivial
        have hnjR2 : OutcomeNormalOrJump (eval fuel' prog curEnv2 joinPc w2 rhs) := by
          cases ho : eval fuel' prog curEnv2 joinPc w2 rhs <;> rw [ho] at hnj2 <;> first | contradiction | trivial
        have hrEq := (ihE hprog hsafeProg curEnv1 curEnv2 ((label, sig) :: jenv) joinPc inSpec w1 w2 rhs rLTy
          henvCur hjenv'Safe hjenv'Sub hw hpDB1 hpDB2 hcCl1 hcCl2 hrSafe hrNs (hcurTy1.symm ▸ hrSup) hrr1 hrr2
          (hcurTy1 ▸ hrChk) hnjR1 hnjR2).subtype hrSub
        have hrDb1 := hdb'.1 hprog hsafeProg curEnv1 joinPc w1 rhs hpDB1 hcCl1 hrSafe hrNs (hcurTy1.symm ▸ hrSup) hrr1
        have hrDb2 := hdb'.1 hprog hsafeProg curEnv2 joinPc w2 rhs hpDB2 hcCl2 hrSafe hrNs ((henvCur.envToTyEnv_eq ▸ hcurTy1).symm ▸ hrSup) hrr2
        rcases hrEq with ⟨hwr, hrPay⟩
        cases hoR1 : eval fuel' prog curEnv1 joinPc w1 rhs <;> rw [hoR1] at hnjR1 hnj1 hrDb1 hwr hrPay <;> try contradiction
        all_goals (cases hoR2 : eval fuel' prog curEnv2 joinPc w2 rhs <;> rw [hoR2] at hnjR2 hnj2 hrDb2 hwr hrPay <;> try contradiction)
        all_goals (dsimp only at hnj1 hnj2 ⊢)
        · exact ⟨hwr, hrPay⟩
        · rename_i lbl2 _ _
          rcases hrPay with ⟨hh, sig2, hlk2, hs2F⟩
          have hne : lbl2 ≠ label := by
            intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk2
            subst hlk2; dsimp only [sig] at hs2F; rw [hjpLow] at hs2F; nomatch hs2F
          have hlblF : (lbl2 == label) = false := by cases h : (lbl2 == label); rfl; exact absurd (beq_iff_eq.mp h) hne
          simp only [hlblF, Bool.false_eq_true, ↓reduceIte]
          simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk2
          exact ⟨hwr, hh, sig2, hlk2, hs2F⟩
        · rename_i lbl1 _ _ _ _
          rcases hrPay with ⟨⟨sig1, hlk1, hs1F⟩, hh⟩
          have hne : lbl1 ≠ label := by
            intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk1
            subst hlk1; dsimp only [sig] at hs1F; rw [hjpLow] at hs1F; nomatch hs1F
          have hlblF : (lbl1 == label) = false := by cases h : (lbl1 == label); rfl; exact absurd (beq_iff_eq.mp h) hne
          simp only [hlblF, Bool.false_eq_true, ↓reduceIte]
          simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk1
          exact ⟨hwr, ⟨sig1, hlk1, hs1F⟩, hh⟩
        · rename_i lbl1 vs1 wr1 lbl2 vs2 wr2
          rcases hrPay with ⟨rfl, sig0, hlk0, hs0L, hvsEq⟩ | ⟨⟨sig1, hlk1, hs1F⟩, ⟨sig2, hlk2, hs2F⟩⟩
          · cases hlbl : (lbl1 == label)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hne : lbl1 ≠ label := fun e => by subst e; simp at hlbl
              simp only [lookupJoinEnv, Ne.symm hne, ↓reduceIte] at hlk0
              exact ⟨hwr, Or.inl ⟨rfl, sig0, hlk0, hs0L, hvsEq⟩⟩
            · simp only [hlbl, ↓reduceIte] at hnj1 hnj2 ⊢
              have heq : label = lbl1 := (beq_iff_eq.mp hlbl).symm
              simp only [lookupJoinEnv, heq, ↓reduceIte, Option.some.injEq] at hlk0; subst hlk0
              rcases hvsEq.length_eq with ⟨hl1, hl2⟩
              dsimp only [sig] at hl1 hl2
              rw [List.length_map] at hl1 hl2
              simp only [hl1, hl2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hnj1 hnj2 ⊢
              have hnextEq := extendEnv_equiv hparamsOk hvsEq hbase
              have hnextTy1 : envToTyEnv ((List.zip params vs1).map (fun ((pName, pLTy), jVal) => { name := pName, lty := pLTy, val := jVal }) ++ baseEnv1) =
                  extendTyEnv (envToTyEnv baseEnv1) params := by
                rw [envToTyEnv_append, envToTyEnv_zip_params params vs1 hl1, extendTyEnv]
              exact ihJL hprog hsafeProg baseEnv1 baseEnv2 _ _ jenv label params joinPc retLTy rLTy inSpec rhs wr1 wr2
                hbase hnextEq hnextTy1 hjenvSafe hjenvSub hparamsOk hretOk hjpSubRet hrSub hwr
                (progRespectsDB_congr hrDb1.2 hpDB1) (progRespectsDB_congr hrDb2.2 hpDB2)
                (envClosureSafe_congr hrDb1.2 hbCl1) (envClosureSafe_congr hrDb2.2 hbCl2)
                (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hrDb1.2 hrDb1.1)) (envClosureSafe_congr hrDb1.2 hbCl1))
                (envClosureSafe_append (envClosureSafe_zip_params (valListClosureSafe_congr hrDb2.2 hrDb2.1)) (envClosureSafe_congr hrDb2.2 hbCl2))
                hrSafe hrNs hrSup (exprRespectsDB_congr hrDb1.2 hrr1) (exprRespectsDB_congr hrDb2.2 hrr2)
                hrChk hnj1 hnj2
          · have hne1 : lbl1 ≠ label := by
              intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk1
              subst hlk1; dsimp only [sig] at hs1F; rw [hjpLow] at hs1F; nomatch hs1F
            have hne2 : lbl2 ≠ label := by
              intro e; subst e; simp only [lookupJoinEnv, ↓reduceIte, Option.some.injEq] at hlk2
              subst hlk2; dsimp only [sig] at hs2F; rw [hjpLow] at hs2F; nomatch hs2F
            have hf1 : (lbl1 == label) = false := by cases h : (lbl1 == label); rfl; exact absurd (beq_iff_eq.mp h) hne1
            have hf2 : (lbl2 == label) = false := by cases h : (lbl2 == label); rfl; exact absurd (beq_iff_eq.mp h) hne2
            simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte]
            simp only [lookupJoinEnv, Ne.symm hne1, Ne.symm hne2, ↓reduceIte] at hlk1 hlk2
            exact ⟨hwr, Or.inr ⟨⟨sig1, hlk1, hs1F⟩, ⟨sig2, hlk2, hs2F⟩⟩⟩

private theorem ValWf.table_schemaWf {prog : Program} {tv : TableVal} {tt : TableTy}
    (h : ValWf prog (.table tv) (.table tt)) : TableSchemaWf prog tt = true := by
  cases h with | table _ hsch _ => exact hsch

-- =========================================================================
-- 3. PlanNIAt (fuel' + 1)
-- =========================================================================
private theorem foldl_add_init {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (init : Nat),
      xs.foldl (fun acc x => acc + f x) init = init + xs.foldl (fun acc x => acc + f x) 0
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_init f xs (init + f x), foldl_add_init f xs (f x), Nat.add_assoc]

private theorem foldl_add_perm {α : Type} (f : α → Nat) {xs ys : List α} (hp : List.Perm xs ys) :
    xs.foldl (fun acc x => acc + f x) 0 = ys.foldl (fun acc x => acc + f x) 0 := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_init f _ (f x), foldl_add_init f _ (f x), ih]
  | swap x y l =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [Nat.add_comm (f y) (f x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem foldl_add_relList {α : Type} {R : α → α → Prop} {f : α → Nat}
    (hcongr : ∀ a b, R a b → f a = f b) :
    ∀ {xs ys : List α}, RelList R xs ys →
      xs.foldl (fun acc x => acc + f x) 0 = ys.foldl (fun acc x => acc + f x) 0
  | [], [], .nil => rfl
  | x :: xs, y :: ys, .cons hxy htl => by
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_init f xs (f x), foldl_add_init f ys (f y), hcongr x y hxy, foldl_add_relList hcongr htl]

private theorem map_insertSortedBy_key {α β : Type} (f : α → β) (ltB : β → β → Bool) (x : α) :
    ∀ (xs : List α),
      (insertSortedBy (fun a b => ltB (f a) (f b)) x xs).map f =
        insertSortedBy ltB (f x) (xs.map f)
  | [] => rfl
  | y :: ys => by
    unfold insertSortedBy
    cases h : ltB (f y) (f x) <;> simp [h, map_insertSortedBy_key f ltB x ys]

private theorem map_insertionSortBy_key {α β : Type} (f : α → β) (ltB : β → β → Bool) :
    ∀ (xs : List α),
      (insertionSortBy (fun a b => ltB (f a) (f b)) xs).map f =
        insertionSortBy ltB (xs.map f)
  | [] => rfl
  | x :: xs => by
    simp only [insertionSortBy, List.map_cons, map_insertSortedBy_key, map_insertionSortBy_key]

private def supKeyLt (a b : Nat × List Val) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else valListLt a.2 b.2

private theorem supKeyLt_irrefl {a : Nat × List Val} (ha : SortableValList a.2) :
    supKeyLt a a = false := by
  unfold supKeyLt; simp [Nat.lt_irrefl, valListLt_irrefl ha]

private theorem supKeyLt_trans {a b c : Nat × List Val}
    (ha : SortableValList a.2) (hb : SortableValList b.2) (hc : SortableValList c.2)
    (hab : supKeyLt a b = true) (hbc : supKeyLt b c = true) :
    supKeyLt a c = true := by
  unfold supKeyLt at hab hbc ⊢
  by_cases h1 : a.1 < b.1
  · by_cases h2 : b.1 < c.1
    · simp [Nat.lt_trans h1 h2]
    · simp only [h2, ↓reduceIte] at hbc
      by_cases h3 : c.1 < b.1
      · simp [h3] at hbc
      · have hbcEq : b.1 = c.1 := Nat.le_antisymm (Nat.not_lt.mp h3) (Nat.not_lt.mp h2)
        rw [← hbcEq]; simp [h1]
  · simp only [h1, ↓reduceIte] at hab
    by_cases h1' : b.1 < a.1
    · simp [h1'] at hab
    · simp only [h1', ↓reduceIte] at hab
      have habEq : a.1 = b.1 := Nat.le_antisymm (Nat.not_lt.mp h1') (Nat.not_lt.mp h1)
      rw [habEq]
      by_cases h2 : b.1 < c.1
      · simp [h2]
      · simp only [h2, ↓reduceIte] at hbc ⊢
        by_cases h3 : c.1 < b.1
        · simp [h3] at hbc
        · simp only [h3, ↓reduceIte] at hbc ⊢
          exact valListLt_trans ha hb hc hab hbc

private theorem supKeyLt_trichotomy {a b : Nat × List Val}
    (ha : SortableValList a.2) (hb : SortableValList b.2) :
    supKeyLt a b = true ∨ a = b ∨ supKeyLt b a = true := by
  unfold supKeyLt
  by_cases h1 : a.1 < b.1
  · exact Or.inl (by simp [h1])
  · by_cases h2 : b.1 < a.1
    · exact Or.inr (Or.inr (by simp [h2]))
    · have heq : a.1 = b.1 := Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1)
      simp only [h1, h2, ↓reduceIte]
      rcases valListLt_trichotomy ha hb with hlt | heq2 | hgt
      · exact Or.inl hlt
      · exact Or.inr (Or.inl (Prod.ext heq heq2))
      · exact Or.inr (Or.inr hgt)

private theorem extractGroupKeyCells_congr {L : TagSet} :
    ∀ {cols : List ColSpec} {xs1 xs2 : List Val},
      CellsEquiv L cols xs1 xs2 →
      (∀ c ∈ cols, c.aggKind = .groupKey → c.tags.subset L = true) →
      extractGroupKeyCells cols xs1 = extractGroupKeyCells cols xs2
  | [], [], [], .nil, _ => rfl
  | c :: cs, v1 :: vs1, v2 :: vs2, .cons hv htl, hgk => by
    unfold extractGroupKeyCells
    cases hd : decide (c.aggKind = .groupKey)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact extractGroupKeyCells_congr htl (fun x hx => hgk x (.tail _ hx))
    · simp only [↓reduceIte]
      have hvEq := hv (hgk c (.head _) (of_decide_eq_true hd))
      exact congrArg2 List.cons hvEq (extractGroupKeyCells_congr htl (fun x hx => hgk x (.tail _ hx)))

private theorem extractGroupKeyCells_sortable {prog : Program} {L : TagSet}
    (hd : progDatasSortableForNI prog L = true) :
    ∀ {cols : List ColSpec} {xs : List Val},
      (∀ c ∈ cols, validScalarTy prog c.ty = true) →
      CellsWf prog xs cols →
      SortableValList (extractGroupKeyCells cols xs)
  | [], [], _, .nil => .nil
  | c :: cs, v :: vs, hval, .cons hv htl => by
    unfold extractGroupKeyCells
    cases decide (c.aggKind = .groupKey)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact extractGroupKeyCells_sortable hd (fun x hx => hval x (.tail _ hx)) htl
    · simp only [↓reduceIte]
      have hs := valWf_sortable hd hv (ScalarTy.isSortable_toTy c.ty)
      exact .cons hs (extractGroupKeyCells_sortable hd (fun x hx => hval x (.tail _ hx)) htl)

private def suppressOutColFn (pc : TagSet) (mode : SuppressMode) (c : ColSpec) : ColSpec :=
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
  | _, _ => base

private theorem cellsEquiv_maskAggCells {L pc : TagSet} (hpc : pc.subset L = true) :
    ∀ {cols : List ColSpec} {xs1 xs2 : List Val},
      CellsEquiv L cols xs1 xs2 →
      (∀ c ∈ cols, ((decide (c.aggKind = .groupKey) && c.bucketed) || decide (c.aggKind = .blending)) = true → c.tags.subset L = true) →
      CellsEquiv L (cols.map (suppressOutColFn pc .maskComplementary)) (maskAggCells cols xs1) (maskAggCells cols xs2)
  | [], [], [], .nil, _ => .nil
  | c :: cs, v1 :: vs1, v2 :: vs2, .cons hv htl, hclear => by
    simp only [List.map_cons, maskAggCells]
    refine .cons (fun hsub => ?_) (cellsEquiv_maskAggCells hpc htl (fun x hx => hclear x (.tail _ hx)))
    cases hak : c.aggKind with
    | blending | nonBlending => rfl
    | raw =>
      simp only [suppressOutColFn, hak] at hsub
      exact hv hsub
    | groupKey =>
      cases hb : c.bucketed
      · simp only [suppressOutColFn, hak, hb, Bool.false_eq_true, ↓reduceIte] at hsub
        exact hv hsub
      · exact hv (hclear c (.head _) (by simp [hak, hb]))

private theorem cellsEquiv_wrapAggCells {L pc : TagSet} (hpc : pc.subset L = true) :
    ∀ {cols : List ColSpec} {xs1 xs2 : List Val},
      CellsEquiv L cols xs1 xs2 →
      (∀ c ∈ cols, ((decide (c.aggKind = .groupKey) && c.bucketed) || decide (c.aggKind = .blending)) = true → c.tags.subset L = true) →
      CellsEquiv L (cols.map (suppressOutColFn pc .maskComplementary)) (wrapAggCells cols xs1) (wrapAggCells cols xs2)
  | [], [], [], .nil, _ => .nil
  | c :: cs, v1 :: vs1, v2 :: vs2, .cons hv htl, hclear => by
    simp only [List.map_cons, wrapAggCells]
    refine .cons (fun hsub => ?_) (cellsEquiv_wrapAggCells hpc htl (fun x hx => hclear x (.tail _ hx)))
    cases hak : c.aggKind with
    | blending =>
      exact wrapIntoOptionVal_congr c.ty (hv (hclear c (.head _) (by simp [hak])))
    | nonBlending =>
      simp only [suppressOutColFn, hak] at hsub
      exact wrapIntoOptionVal_congr c.ty (hv hsub)
    | raw =>
      simp only [suppressOutColFn, hak] at hsub
      exact hv hsub
    | groupKey =>
      cases hb : c.bucketed
      · simp only [suppressOutColFn, hak, hb, Bool.false_eq_true, ↓reduceIte] at hsub
        exact hv hsub
      · exact hv (hclear c (.head _) (by simp [hak, hb]))

set_option maxHeartbeats 1200000 in
private theorem plan_ni_step {prog : Program} {L : TagSet} {fuel' : Nat}
    (ihE : ExprNIAt fuel' prog L) (ihP : PlanNIAt fuel' prog L) :
    PlanNIAt (fuel' + 1) prog L := by
      have hsound := eval_fuel_sound prog (fuel' + 1)
      have hsc := eval_safe_and_confined_all prog L (fuel' + 1)
      have hdb' := eval_preserves_db_all prog L fuel'
      intro hprog hsafeProg env1 env2 pc inSpec w1 w2 plan pTy v1 v2 w1' w2'
        henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hchk hev1 hev2
      have hd : progDatasSortableForNI prog L = true := by
        simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
      have hchk2 : checkPlan prog (envToTyEnv env2) pc inSpec plan = .ok pTy := by
        rwa [← henv.envToTyEnv_eq]
      have hwfOut1 := hsound.2.2.2.2 hprog env1 pc inSpec w1 plan pTy henv.wf_left hw.wf1 hchk
      have hwfOut2 := hsound.2.2.2.2 hprog env2 pc inSpec w2 plan pTy henv.wf_right hw.wf2 hchk2
      rw [hev1] at hwfOut1; cases hwfOut1 with | ok hvWf1 _ =>
      rw [hev2] at hwfOut2; cases hwfOut2 with | ok hvWf2 _ =>
      have henvNs1 := envClosureSafe_imp_noSpecCalls henvCl1
      have henvNs2 := envClosureSafe_imp_noSpecCalls henvCl2
      -- Uniform discharge when `pc ⊈ L`!
      cases hpc : pc.subset L
      · rcases hsc.2.2 hprog hsafeProg env1 pc inSpec w1 plan pTy henv.wf_left henv.safe_left henvNs1 hw.wf1 hpsafe hpns hchk with ⟨hsOut1, _, hconf1⟩
        rcases hsc.2.2 hprog hsafeProg env2 pc inSpec w2 plan pTy henv.wf_right henv.safe_right henvNs2 hw.wf2 hpsafe hpns hchk2 with ⟨hsOut2, _, hconf2⟩
        rw [hev1] at hsOut1; rw [hev2] at hsOut2
        have ew1 := hconf1 hpc; rw [hev1] at ew1; dsimp only [outcomeWorldEq] at ew1; subst ew1
        have ew2 := hconf2 hpc; rw [hev2] at ew2; dsimp only [outcomeWorldEq] at ew2; subst ew2
        have hpTags : (pTy.toLTy pc).tags = pc := by cases pTy <;> rfl
        exact ⟨.high (by rw [hpTags]; exact hpc) hvWf1 hvWf2 hsOut1 hsOut2, hw⟩
      -- Low `pc` (`pc ⊆ L`)
      · unfold evalPlan at hev1 hev2
        cases plan with
        | suppressSmallGroups inp minK distinctBy mode =>
          dsimp only at hev1 hev2
          unfold planSuppressSafe at hpsup
          simp only [Bool.and_eq_true] at hpsup
          rcases hpsup with ⟨hpsupInp, hsupClearMatch⟩
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          have hsupClear : suppressClearsOnlyL L tt = true := by
            cases hiF : checkPlan prog (envToTyEnv env1) pc false inp with
            | error _ => rw [hiF] at hsupClearMatch; nomatch hsupClearMatch
            | ok pF =>
              rw [hiF] at hsupClearMatch
              cases pF with
              | dynamic _ => nomatch hsupClearMatch
              | table ttF =>
                have h1 := checkPlan_inSpec_true hiF
                rw [checkPlan_inSpec_true hi] at h1
                injection h1 with ep; injection ep with ett; subst ett
                exact hsupClearMatch
          split at hchk <;> try contradiction
          rename_i hsumNotF; simp only [Bool.not_eq_true', Bool.not_eq_false] at hsumNotF
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsupInp hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          simp only [suppressClearsOnlyL, Bool.and_eq_true, List.all_eq_true] at hsupClear
          rcases hsupClear with ⟨hrInLow, hcolsClear⟩
          have hmetaRel := ht.sumMetaEq hsumNotF hrInLow
          let rawKeyTags := TagSet.unionList ((tt.cols.filter (fun c => decide (c.aggKind = .groupKey) && !c.bucketed)).map ColSpec.tags)
          have hcolsClear' : ∀ c ∈ tt.cols,
              ((decide (c.aggKind = .groupKey) && c.bucketed) || decide (c.aggKind = .blending)) = true → c.tags.subset L = true := by
            intro c hc hcond
            have h1 := hcolsClear c hc
            simp only [hcond, ↓reduceIte] at h1
            exact h1
          cases mode with
          | drop =>
            dsimp only at hev1 hev2
            injection hev1 with e1 ew1; injection hev2 with e2 ew2
            subst e1; subst e2; subst ew1; subst ew2
            have hw1Raw := hvWf1.table_change_tags (rawKeyTags.union pc) tt.orderTags
            have hw2Raw := hvWf2.table_change_tags (rawKeyTags.union pc) tt.orderTags
            have hsch := hw1Raw.table_schemaWf
            refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
            intro _; dsimp only
            have hstep : ∀ {rs1 rs2 : List TableRow},
                RelList (fun r1 r2 => RowEquiv L tt.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta) rs1 rs2 →
                RelList (RowEquiv L (tt.cols.map (suppressOutColFn pc .drop)))
                  ((rs1.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map (fun r => { r with groupMeta := none }))
                  ((rs2.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map (fun r => { r with groupMeta := none })) := by
              intro rs1 rs2 hrel
              have hfil := RelList.filter_congr
                (p1 := fun r => decide (suppressGroupSize distinctBy r ≥ minK))
                (p2 := fun r => decide (suppressGroupSize distinctBy r ≥ minK))
                (fun r1 r2 hr => by unfold suppressGroupSize; rw [hr.2]) hrel
              exact hfil.map (fun (r : TableRow) => ({ cells := r.cells, groupMeta := none } : TableRow))
                (fun (r : TableRow) => ({ cells := r.cells, groupMeta := none } : TableRow)) (fun r1 r2 hr =>
                cellsEquiv_map_tags (suppressOutColFn pc .drop) hr.1 (fun c hc hsub => by
                  cases hak : c.aggKind with
                  | blending => exact hcolsClear' c hc (by simp [hak])
                  | nonBlending | raw => simp only [suppressOutColFn, hak] at hsub; exact hsub
                  | groupKey =>
                    cases hb : c.bucketed
                    · simp only [suppressOutColFn, hak, hb, Bool.false_eq_true, ↓reduceIte] at hsub; exact hsub
                    · exact hcolsClear' c hc (by simp [hak, hb])))
            cases hord : tt.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hmetaRel ⊢
            · rcases hmetaRel with ⟨rows1', hpIn, hrelIn⟩
              exact ⟨_, (perm_filter _ hpIn).map _, hstep hrelIn⟩
            · exact hstep hmetaRel
          | maskComplementary =>
            dsimp only at hev1 hev2
            injection hev1 with e1 ew1; injection hev2 with e2 ew2
            subst e1; subst e2; subst ew1; subst ew2
            have hw1Raw := hvWf1.table_change_tags (rawKeyTags.union pc) tt.orderTags
            have hw2Raw := hvWf2.table_change_tags (rawKeyTags.union pc) tt.orderTags
            have hsch := hw1Raw.table_schemaWf
            refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
            intro _; dsimp only
            rw [hc1, hc2]
            have hmetaPerm : ∃ rows1', List.Perm tv1.rows rows1' ∧
                RelList (fun r1 r2 => RowEquiv L tt.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta) rows1' tv2.rows := by
              cases hord : tt.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hmetaRel
              · exact hmetaRel
              · exact ⟨tv1.rows, .refl _, hmetaRel⟩
            rcases hmetaPerm with ⟨rows1', hpIn, hrelIn⟩
            have hgkLow : ∀ c ∈ tt.cols, c.aggKind = .groupKey → c.tags.subset L = true :=
              ht.groupingLow hrInLow
            have hsmallRel := RelList.filter_congr
              (p1 := fun r => decide (suppressGroupSize distinctBy r < minK))
              (p2 := fun r => decide (suppressGroupSize distinctBy r < minK))
              (fun r1 r2 hr => by unfold suppressGroupSize; rw [hr.2]) hrelIn
            have hsmallPerm := perm_filter (fun r => decide (suppressGroupSize distinctBy r < minK)) hpIn
            have hsmallEmptyEq :
                (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).isEmpty =
                (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).isEmpty := by
              have hlen : (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).length =
                  (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).length :=
                hsmallPerm.length_eq.trans hsmallRel.length_eq
              cases h1 : tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK)) <;>
              cases h2 : tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK)) <;>
                simp [h1, h2] at hlen ⊢
            have hsmallSumEq :
                (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).foldl (fun acc r => acc + suppressGroupSize distinctBy r) 0 =
                (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).foldl (fun acc r => acc + suppressGroupSize distinctBy r) 0 :=
              (foldl_add_perm (suppressGroupSize distinctBy) hsmallPerm).trans
                (foldl_add_relList (fun _ _ hr => by unfold suppressGroupSize; rw [hr.2]) hsmallRel)
            let keyFn : TableRow → Nat × List Val := fun r => (suppressGroupSize distinctBy r, extractGroupKeyCells tt.cols r.cells)
            have hvalidRel := RelList.filter_congr
              (p1 := fun r => decide (suppressGroupSize distinctBy r ≥ minK))
              (p2 := fun r => decide (suppressGroupSize distinctBy r ≥ minK))
              (fun r1 r2 hr => by unfold suppressGroupSize; rw [hr.2]) hrelIn
            have hvalidPerm := perm_filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK)) hpIn
            have hvalidKeyMapEq : (rows1'.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map keyFn =
                (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map keyFn := by
              have h1 : ∀ {as1 bs1}, RelList (fun r1 r2 => RowEquiv L tt.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta) as1 bs1 →
                  as1.map keyFn = bs1.map keyFn := by
                intro as1 bs1 hrel; induction hrel with
                | nil => rfl
                | cons h _ ih =>
                  simp only [List.map_cons, List.cons.injEq]
                  refine ⟨Prod.ext (by dsimp only [keyFn]; unfold suppressGroupSize; rw [h.2]) (extractGroupKeyCells_congr h.1 hgkLow), ih⟩
              exact h1 hvalidRel
            have hvalidKeyPerm : List.Perm
                ((tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map keyFn)
                ((tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map keyFn) :=
              hvalidKeyMapEq ▸ hvalidPerm.map keyFn
            cases ht.wf1 with | table _ hschIn hrWfIn1 =>
            have hcolsValIn := fun c hc => (tableSchemaWf_cols_props hschIn).2 c hc |>.1
            have hvalidSort : ∀ p ∈ (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK))).map keyFn,
                SortableValList p.2 := by
              intro p hp; rw [List.mem_map] at hp; rcases hp with ⟨r, hr, rfl⟩
              exact extractGroupKeyCells_sortable hd hcolsValIn (hrWfIn1.to_forall r (List.mem_filter.mp hr).1)
            have hsortedHeadEq :
                (insertionSortBy (suppressRowLt tt.cols distinctBy) (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK)))).head?.map (fun r => extractGroupKeyCells tt.cols r.cells) =
                (insertionSortBy (suppressRowLt tt.cols distinctBy) (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK)))).head?.map (fun r => extractGroupKeyCells tt.cols r.cells) := by
              have hheadKey : ∀ (rs : List TableRow),
                  (insertionSortBy (suppressRowLt tt.cols distinctBy) rs).head?.map (fun r => extractGroupKeyCells tt.cols r.cells) =
                  (insertionSortBy supKeyLt (rs.map keyFn)).head?.map Prod.snd := by
                intro rs
                have hmap := map_insertionSortBy_key keyFn supKeyLt rs
                have hltEq : (fun a b => supKeyLt (keyFn a) (keyFn b)) = suppressRowLt tt.cols distinctBy := rfl
                rw [hltEq] at hmap
                rw [← hmap, List.head?_map, Option.map_map]; rfl
              rw [hheadKey, hheadKey]
              rw [insertionSortBy_perm_eq supKeyLt_irrefl supKeyLt_trans supKeyLt_trichotomy hvalidSort hvalidKeyPerm]
            have hcompEq :
                (if !(tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).isEmpty &&
                    (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).foldl (fun acc r => acc + suppressGroupSize distinctBy r) 0 < minK
                 then (insertionSortBy (suppressRowLt tt.cols distinctBy) (tv1.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK)))).head?.map (fun r => extractGroupKeyCells tt.cols r.cells)
                 else none) =
                (if !(tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).isEmpty &&
                    (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).foldl (fun acc r => acc + suppressGroupSize distinctBy r) 0 < minK
                 then (insertionSortBy (suppressRowLt tt.cols distinctBy) (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK)))).head?.map (fun r => extractGroupKeyCells tt.cols r.cells)
                 else none) := by
              rw [hsmallEmptyEq, hsmallSumEq, hsortedHeadEq]
            rw [hcompEq]
            let ck? := if !(tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).isEmpty &&
                (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r < minK))).foldl (fun acc r => acc + suppressGroupSize distinctBy r) 0 < minK
              then (insertionSortBy (suppressRowLt tt.cols distinctBy) (tv2.rows.filter (fun r => decide (suppressGroupSize distinctBy r ≥ minK)))).head?.map (fun r => extractGroupKeyCells tt.cols r.cells)
              else none
            let rowFn : TableRow → TableRow := fun r =>
              let shouldMask :=
                decide (suppressGroupSize distinctBy r < minK) ||
                match ck? with
                | none => false
                | some ck => valListEq (extractGroupKeyCells tt.cols r.cells) ck
              if shouldMask then { cells := maskAggCells tt.cols r.cells, groupMeta := none }
              else { cells := wrapAggCells tt.cols r.cells, groupMeta := none }
            have hrowStep : ∀ r1 r2,
                (RowEquiv L tt.cols r1 r2 ∧ r1.groupMeta = r2.groupMeta) →
                RowEquiv L (tt.cols.map (suppressOutColFn pc .maskComplementary)) (rowFn r1) (rowFn r2) := by
              intro r1 r2 hr
              have hgkEq := extractGroupKeyCells_congr hr.1 hgkLow
              have hszEq : suppressGroupSize distinctBy r1 = suppressGroupSize distinctBy r2 := by
                unfold suppressGroupSize; rw [hr.2]
              dsimp only [rowFn]
              rw [hszEq, hgkEq]
              split
              · exact cellsEquiv_maskAggCells hpc hr.1 hcolsClear'
              · exact cellsEquiv_wrapAggCells hpc hr.1 hcolsClear'
            cases hord : tt.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hmetaRel ⊢
            · rcases hmetaRel with ⟨r1', hp1', hrel1'⟩
              exact ⟨r1'.map rowFn, hp1'.map rowFn, hrel1'.map rowFn rowFn hrowStep⟩
            · exact hmetaRel.map rowFn rowFn hrowStep
        | sourceExpr e =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases he : checkExpr prog (envToTyEnv env1) [] pc inSpec e <;> rw [he] at hchk <;> try contradiction
          rename_i eLTy; dsimp only at hchk
          cases eLTy with | mk ety eTs =>
          cases ety <;> dsimp only [LTy.ty] at hchk <;> try contradiction
          rename_i tt; injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoE1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoE2, hev2⟩
          injection hev1 with ev1' ew1'; injection hev2 with ev2' ew2'
          subst ev1'; subst ev2'; subst ew1'; subst ew2'
          have heEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 e _
            henv rfl (fun _ hm => nomatch hm) hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 he
            (by rw [hoE1]; trivial) (by rw [hoE2]; trivial)
          rw [hoE1, hoE2] at heEq; rcases heEq with ⟨hw', htvEq⟩
          refine ⟨TableEquiv.to_valEquiv_planTy ?_, hw'⟩
          have hw1Raw := hvWf1.table_change_tags (tt.rowTags.union (eTs.union pc)) (tt.orderTags.union (eTs.union pc))
          have hw2Raw := hvWf2.table_change_tags (tt.rowTags.union (eTs.union pc)) (tt.orderTags.union (eTs.union pc))
          by_cases hrLow : (tt.rowTags.union (eTs.union pc)).subset L = true
          · have heTsLow : eTs.subset L = true := by
              simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow; exact hrLow.2.1
            cases htvEq.payload heTsLow with | table ht =>
            exact ht.widenRowOrderTags (eTs.union pc) (eTs.union pc)
          · exact TableEquiv.of_high_rowTags hw1Raw hw2Raw (Bool.eq_false_iff.mpr hrLow)
        | sourceDB cap tableName schema =>
          dsimp only at hev1 hev2
          rcases hpr1 with ⟨hprC1, hrealS1, hfakeS1⟩
          rcases hpr2 with ⟨hprC2, hrealS2, hfakeS2⟩
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hc : checkExpr prog (envToTyEnv env1) [] pc inSpec cap <;> rw [hc] at hchk <;> try contradiction
          rename_i capLTy; dsimp only at hchk
          cases capLTy with | mk cty cTs =>
          cases cty <;> dsimp only [LTy.ty] at hchk <;> try contradiction
          split at hchk <;> try contradiction
          rename_i hschValid
          injection hchk with ep; subst ep
          rcases match_capReadDB_eq_ok hev1 with ⟨h1, db1, wc1, hoC1, hev1⟩
          rcases match_capReadDB_eq_ok hev2 with ⟨h2, db2, wc2, hoC2, hev2⟩
          have hcEq := ihE hprog hsafeProg env1 env2 [] pc inSpec w1 w2 cap _
            henv rfl (fun _ hm => nomatch hm) hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hprC1 hprC2 hc
            (by rw [hoC1]; trivial) (by rw [hoC2]; trivial)
          rw [hoC1, hoC2] at hcEq; rcases hcEq with ⟨hwc, hcapEq⟩
          have hcDb1 := hdb'.1 hprog hsafeProg env1 pc w1 cap hpDB1 henvCl1 hpsafe hpns hpsup hprC1
          have hcDb2 := hdb'.1 hprog hsafeProg env2 pc w2 cap hpDB2 henvCl2 hpsafe hpns (henv.envToTyEnv_eq ▸ hpsup) hprC2
          rw [hoC1] at hcDb1; rw [hoC2] at hcDb2
          have hworld1 : w1' = wc1 := by
            cases h1 with
            | real =>
              simp only [] at hev1
              cases hst1 : wc1.realDBTables.find? (fun st => st.db == db1 && st.tableName == tableName) <;>
                rw [hst1] at hev1 <;> simp only [] at hev1
              · injection hev1 with _ ew; exact ew.symm
              · split at hev1 <;> first | contradiction | (injection hev1 with _ ew; exact ew.symm)
            | fake fid =>
              simp only [] at hev1
              cases hfd1 : wc1.fakeDBs[fid]? <;> rw [hfd1] at hev1 <;> simp only [] at hev1
              · injection hev1 with _ ew; exact ew.symm
              · rename_i fdb1
                cases hst1 : fdb1.tables.find? (fun st => st.tableName == tableName) <;>
                  rw [hst1] at hev1 <;> simp only [] at hev1
                · injection hev1 with _ ew; exact ew.symm
                · split at hev1 <;> first | contradiction | (injection hev1 with _ ew; exact ew.symm)
          have hworld2 : w2' = wc2 := by
            cases h2 with
            | real =>
              simp only [] at hev2
              cases hst2 : wc2.realDBTables.find? (fun st => st.db == db2 && st.tableName == tableName) <;>
                rw [hst2] at hev2 <;> simp only [] at hev2
              · injection hev2 with _ ew; exact ew.symm
              · split at hev2 <;> first | contradiction | (injection hev2 with _ ew; exact ew.symm)
            | fake fid =>
              simp only [] at hev2
              cases hfd2 : wc2.fakeDBs[fid]? <;> rw [hfd2] at hev2 <;> simp only [] at hev2
              · injection hev2 with _ ew; exact ew.symm
              · rename_i fdb2
                cases hst2 : fdb2.tables.find? (fun st => st.tableName == tableName) <;>
                  rw [hst2] at hev2 <;> simp only [] at hev2
                · injection hev2 with _ ew; exact ew.symm
                · split at hev2 <;> first | contradiction | (injection hev2 with _ ew; exact ew.symm)
          subst hworld1; subst hworld2
          cases hvWf1 with | @table tv1 _ _ _ _ =>
          cases hvWf2 with | @table tv2 _ _ _ _ =>
          have hw1Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table tv1) _).table_change_tags
            (schema.rowTags.union (cTs.union pc)) (schema.orderTags.union (cTs.union pc))
          have hw2Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table tv2) _).table_change_tags
            (schema.rowTags.union (cTs.union pc)) (schema.orderTags.union (cTs.union pc))
          refine ⟨TableEquiv.to_valEquiv_planTy ?_, hwc⟩
          by_cases hrLow : (schema.rowTags.union (cTs.union pc)).subset L = true
          · have hcTsLow : cTs.subset L = true := by
              simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow; exact hrLow.2.1
            have ⟨hhEq, hdbEq⟩ : h1 = h2 ∧ db1 = db2 := by cases hcapEq.payload hcTsLow; exact ⟨rfl, rfl⟩
            subst hhEq; subst hdbEq
            have hgbNone : schema.groupedBy = none := by
              simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hschValid; exact hschValid.1.1.2
            cases hw1Raw with | table _ hsch _ =>
            have hEmptyEquiv : TableEquiv prog L { cols := schema.cols, rows := [] } { cols := schema.cols, rows := [] }
                { schema with rowTags := schema.rowTags.union (cTs.union pc), orderTags := schema.orderTags.union (cTs.union pc) } :=
              ⟨.table rfl hsch (.nil _ _ _), .table rfl hsch (.nil _ _ _),
               groupingLow_of_groupedBy_none hgbNone hsch,
               (fun _ => by split; exact .nil; exact ⟨[], .nil, .nil⟩),
               fun _ _ => by split; exact .nil; exact ⟨[], .nil, .nil⟩⟩
            dsimp only [outWorld] at hwc
            cases h1 with
            | real =>
              simp only [] at hev1 hev2
              rcases relList_storedTable_findReal db1 tableName hwc.realDBTablesEquiv with ⟨hf1, hf2⟩ | ⟨st1, st2, hf1, hf2, hstEq⟩
              · rw [hf1] at hev1; rw [hf2] at hev2; simp only [] at hev1 hev2
                injection hev1 with e1 _; injection hev2 with e2 _; injection e1 with et1; injection e2 with et2
                subst et1; subst et2; exact hEmptyEquiv
              · rw [hf1] at hev1; rw [hf2] at hev2; simp only [] at hev1 hev2
                have htn1 : st1.tableName = tableName := by
                  have hp := List.find?_some hf1; simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.2
                have hs1Eq : st1.schema = schema := hrealS1 st1 (hcDb1.2.1 ▸ List.mem_of_find?_eq_some hf1) htn1
                have hs2Eq : st2.schema = schema := hs1Eq ▸ hstEq.schemaEq.symm
                simp only [hs1Eq, hs2Eq, decide_true, ↓reduceIte] at hev1 hev2
                injection hev1 with e1 _; injection hev2 with e2 _; injection e1 with et1; injection e2 with et2
                subst et1; subst et2
                have htbl := hstEq.tblEquiv
                rw [hs1Eq, hs2Eq] at htbl
                exact htbl.widenRowOrderTags (cTs.union pc) (cTs.union pc)
            | fake fid =>
              simp only [] at hev1 hev2
              rcases relList_fakeDB_getElem? fid hwc.fakeDBsEquiv with ⟨hn1, hn2⟩ | ⟨fdb1, fdb2, hg1, hg2, hfdbEq⟩
              · rw [hn1] at hev1; rw [hn2] at hev2; simp only [] at hev1 hev2
                injection hev1 with e1 _; injection hev2 with e2 _; injection e1 with et1; injection e2 with et2
                subst et1; subst et2; exact hEmptyEquiv
              · rw [hg1] at hev1; rw [hg2] at hev2; simp only [] at hev1 hev2
                rcases relList_storedTable_findFake tableName hfdbEq.tables with ⟨hf1, hf2⟩ | ⟨st1, st2, hf1, hf2, hstEq⟩
                · rw [hf1] at hev1; rw [hf2] at hev2; simp only [] at hev1 hev2
                  injection hev1 with e1 _; injection hev2 with e2 _; injection e1 with et1; injection e2 with et2
                  subst et1; subst et2; exact hEmptyEquiv
                · rw [hf1] at hev1; rw [hf2] at hev2; simp only [] at hev1 hev2
                  have htn1 : st1.tableName = tableName := by
                    have hfind := List.find?_some hf1; exact beq_iff_eq.mp hfind
                  have hs1Eq : st1.schema = schema :=
                    hfakeS1 fdb1 (hcDb1.2.2 ▸ List.mem_of_getElem? hg1) st1 (List.mem_of_find?_eq_some hf1) htn1
                  have hs2Eq : st2.schema = schema := hs1Eq ▸ hstEq.schemaEq.symm
                  simp only [hs1Eq, hs2Eq, decide_true, ↓reduceIte] at hev1 hev2
                  injection hev1 with e1 _; injection hev2 with e2 _; injection e1 with et1; injection e2 with et2
                  subst et1; subst et2
                  have htbl := hstEq.tblEquiv
                  rw [hs1Eq, hs2Eq] at htbl
                  exact htbl.widenRowOrderTags (cTs.union pc) (cTs.union pc)
          · exact TableEquiv.of_high_rowTags hw1Raw hw2Raw (Bool.eq_false_iff.mpr hrLow)
        | select inp selCols =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          rename_i hallSome; simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hallSome
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          rw [hc1] at hev1; rw [hc2] at hev2
          rcases select_idxSpecs_props selCols hallSome with ⟨hlenIdx, hallIdx, hcolsIdx, _⟩
          simp only [hlenIdx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hev1 hev2
          cases hp1 : projectRowsByIndices _ tv1.rows <;> rw [hp1] at hev1 <;> try contradiction
          cases hp2 : projectRowsByIndices _ tv2.rows <;> rw [hp2] at hev2 <;> try contradiction
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          have hw1Raw := hvWf1.table_change_tags tt.rowTags tt.orderTags
          have hw2Raw := hvWf2.table_change_tags tt.rowTags tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only; unfold TableTy.findCol?; rw [← hcolsIdx]
          exact projectPlan_lowRows ht hrLow hallIdx hp1 hp2
        | drop inp dropCols =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          rw [hc1] at hev1; rw [hc2] at hev2
          cases hp1 : projectRowsByIndices _ tv1.rows <;> rw [hp1] at hev1 <;> try contradiction
          cases hp2 : projectRowsByIndices _ tv2.rows <;> rw [hp2] at hev2 <;> try contradiction
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          have hw1Raw := hvWf1.table_change_tags tt.rowTags tt.orderTags
          have hw2Raw := hvWf2.table_change_tags tt.rowTags tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only
          let kept := tt.cols.zipIdx.filter (fun (c, _) => !dropCols.contains c.name)
          let idxCols := kept.map (fun (c, i) => (i, c))
          rcases zipIdx_filter_props (fun c => !dropCols.contains c.name) tt.cols with ⟨hkeptFst, hkeptGet⟩
          have hfstEq : idxCols.map Prod.fst = kept.map Prod.snd := by
            dsimp only [idxCols]; rw [List.map_map]; rfl
          have hcolsEq : idxCols.map (fun (_, c) => { c with aggKind := .raw }) =
              (tt.cols.filter (fun c => !dropCols.contains c.name)).map (fun c => { c with aggKind := .raw }) := by
            rw [← hkeptFst, List.map_map]; dsimp only [idxCols]; rw [List.map_map]; rfl
          have hallIdx : ∀ ic ∈ idxCols, tt.cols[ic.1]? = some ic.2 := by
            intro ic hic; rw [List.mem_map] at hic; rcases hic with ⟨⟨c, i⟩, hm, rfl⟩
            exact hkeptGet (c, i) hm
          rw [← hcolsEq]
          exact projectPlan_lowRows ht hrLow hallIdx (hfstEq ▸ hp1) (hfstEq ▸ hp2)
        | rename inp pairs =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          split at hchk <;> try contradiction
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          have hw1Raw := hvWf1.table_change_tags tt.rowTags tt.orderTags
          have hw2Raw := hvWf2.table_change_tags tt.rowTags tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only
          exact ht.map_lowRows hrLow (fun r => { r with groupMeta := none }) (fun r => { r with groupMeta := none }) (fun _ _ hr =>
            cellsEquiv_map_tags (fun c => match pairs.find? (fun (_, oldN) => oldN == c.name) with | some (newN, _) => { c with name := newN, aggKind := .raw } | none => { c with aggKind := .raw })
              hr (fun c _ hsub => by split at hsub <;> exact hsub))
        | derive inp items =>
          dsimp only at hev1 hev2
          simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          cases hdApp : applyDeriveItems prog (envToTyEnv env1) (tt.cols.map (fun c => { c with aggKind := .raw })) items <;>
            rw [hdApp] at hchk <;> try contradiction
          rename_i outCols; dsimp only at hchk
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe.1 hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hwi⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          have hwEq1 := (evalDeriveItems_world_and_safe (L := L) (prog := prog) (tEnv := envToTyEnv env1) (evalRowExpr fuel' prog env1) wi1
            { cols := tv1.cols.map (fun c => { c with aggKind := .raw }), rows := tv1.rows.map (fun r => { r with groupMeta := none }) } items).2.2
          have hwEq2 := (evalDeriveItems_world_and_safe (L := L) (prog := prog) (tEnv := envToTyEnv env2) (evalRowExpr fuel' prog env2) wi2
            { cols := tv2.cols.map (fun c => { c with aggKind := .raw }), rows := tv2.rows.map (fun r => { r with groupMeta := none }) } items).2.2
          rw [hev1] at hwEq1; dsimp only [outcomeWorldEq] at hwEq1; subst hwEq1
          rw [hev2] at hwEq2; dsimp only [outcomeWorldEq] at hwEq2; subst hwEq2
          cases hvWf1 with | @table resTV1 _ _ _ _ =>
          cases hvWf2 with | @table resTV2 _ _ _ _ =>
          have hw1Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table resTV1) _).table_change_tags tt.rowTags tt.orderTags
          have hw2Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table resTV2) _).table_change_tags tt.rowTags tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hwi⟩
          intro hrLow; dsimp only
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          cases ht.wf1 with | table _ hschIn hrWfIn1 =>
          cases ht.wf2 with | table _ _ hrWfIn2 =>
          rcases tableSchemaWf_cols_props hschIn with ⟨huniqIn, hcolsIn⟩
          let rawCols := tt.cols.map (fun c => { c with aggKind := .raw })
          have hnamesRaw : rawCols.map ColSpec.name = tt.cols.map ColSpec.name := by dsimp only [rawCols]; induction tt.cols <;> simp [*]
          have hinitWf1 : RowsWf prog (tv1.rows.map (fun r => { r with groupMeta := none })) rawCols false false :=
            RowsWf.of_forall_raw (fun r hr => by rw [List.mem_map] at hr; rcases hr with ⟨o, ho, rfl⟩; exact (hrWfIn1.to_forall o ho).congr_ty (map_ty_with_aggKind tt.cols .raw).symm)
          have hinitWf2 : RowsWf prog (tv2.rows.map (fun r => { r with groupMeta := none })) rawCols false false :=
            RowsWf.of_forall_raw (fun r hr => by rw [List.mem_map] at hr; rcases hr with ⟨o, ho, rfl⟩; exact (hrWfIn2.to_forall o ho).congr_ty (map_ty_with_aggKind tt.cols .raw).symm)
          have hinitRel := ht.map_lowRows hrLow (fun r => { r with groupMeta := none }) (fun r => { r with groupMeta := none })
            (fun _ _ hr => cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hr (fun _ _ h => h))
          exact evalDeriveItems_ni hprog hsafeProg henv hwi.wf1 hwi.wf2 items (ot := tt.orderTags)
            (by simp [hc1]) (by simp [hc2]) (hnamesRaw ▸ huniqIn)
            (fun c hc => by rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩; exact ⟨(hcolsIn o ho).1, (hcolsIn o ho).2, rfl⟩)
            hinitWf1 hinitWf2 hdApp hev1 hev2 hinitRel
        | filter inp pred =>
          dsimp only at hev1 hev2
          simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          cases hp : checkRowExpr prog (envToTyEnv env1) tt.cols pred with
          | error _ => rw [hp] at hchk; contradiction
          | ok pair =>
          rcases pair with ⟨pTy', pTags⟩; rw [hp] at hchk; dsimp only at hchk
          split at hchk <;> try contradiction
          rename_i hpBool; simp only [decide_eq_true_eq] at hpBool; subst hpBool
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe.1 hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hwi⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          have hwEq1 := (evalFilterRows_world_and_safe (prog := prog) (L := L) (evalRowExpr fuel' prog env1) tv1.cols (tv1.cols.map (fun c => { c with aggKind := .raw })) pred wi1 tv1.rows).2.2
          have hwEq2 := (evalFilterRows_world_and_safe (prog := prog) (L := L) (evalRowExpr fuel' prog env2) tv2.cols (tv2.cols.map (fun c => { c with aggKind := .raw })) pred wi2 tv2.rows).2.2
          rw [hev1] at hwEq1; dsimp only [outcomeWorldEq] at hwEq1; subst hwEq1
          rw [hev2] at hwEq2; dsimp only [outcomeWorldEq] at hwEq2; subst hwEq2
          cases hvWf1 with | @table resTV1 _ _ _ _ =>
          cases hvWf2 with | @table resTV2 _ _ _ _ =>
          have hw1Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table resTV1) _).table_change_tags (tt.rowTags.union pTags) tt.orderTags
          have hw2Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table resTV2) _).table_change_tags (tt.rowTags.union pTags) tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hwi⟩
          intro hrLow; dsimp only
          simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
          exact evalFilterRows_ni hprog hsafeProg henv ht hrLow.1 hrLow.2 hp hev1 hev2
        | distinct inp cols =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          let keyNames := if cols.isEmpty then tt.cols.map ColSpec.name else cols
          change (if (!distinctIdents keyNames || !keyNames.all (fun k =>
              match tt.findCol? k with | some c => isEquatableTy c.ty.toTy | none => false)) then _ else _) = _ at hchk
          have hkValid : (distinctIdents keyNames && keyNames.all (fun k =>
              match tt.findCol? k with | some c => isEquatableTy c.ty.toTy | none => false)) = true := by
            cases hbad : (!distinctIdents keyNames || !keyNames.all (fun k =>
                match tt.findCol? k with | some c => isEquatableTy c.ty.toTy | none => false))
            · simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hbad
              simp only [Bool.and_eq_true]; exact hbad
            · rw [hbad] at hchk; contradiction
          have hbadF : (!distinctIdents keyNames || !keyNames.all (fun k =>
              match tt.findCol? k with | some c => isEquatableTy c.ty.toTy | none => false)) = false := by
            simp only [Bool.and_eq_true] at hkValid; simp [hkValid.1, hkValid.2]
          rw [hbadF] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          rw [hc1] at hev1; rw [hc2] at hev2
          cases hd1 : dedupTableRows tt.cols _ [] tv1.rows <;> rw [hd1] at hev1 <;> try contradiction
          cases hd2 : dedupTableRows tt.cols _ [] tv2.rows <;> rw [hd2] at hev2 <;> try contradiction
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          let keyTags := TagSet.unionList (keyNames.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
          let ordDep := if keyNames.length == tt.cols.length then TagSet.empty else tt.orderTags
          have hw1Raw := hvWf1.table_change_tags ((tt.rowTags.union keyTags).union ordDep) tt.orderTags
          have hw2Raw := hvWf2.table_change_tags ((tt.rowTags.union keyTags).union ordDep) tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only
          simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hrLow
          rcases hrLow with ⟨⟨hrInLow, hkTagsLow⟩, hordDepLow⟩
          have hlowKeys : ∀ k ∈ keyNames, ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true :=
            fun k hk c hfc => hkTagsLow c.tags (List.mem_filterMap.mpr ⟨k, hk, by unfold TableTy.findCol?; simp [hfc]⟩)
          have hlr := ht.lowRows hrInLow
          cases hord : tt.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr ⊢
          · -- `tt.orderTags ⊈ L` forces `keyNames.length == tt.cols.length`!
            have hlenEq : keyNames.length = tt.cols.length := by
              cases hkLen : (keyNames.length == tt.cols.length)
              · rw [hkLen] at hordDepLow; simp only [Bool.false_eq_true, ↓reduceIte] at hordDepLow
                rw [hord] at hordDepLow; nomatch hordDepLow
              · exact beq_iff_eq.mp hkLen
            cases ht.wf1 with | table _ hschIn hrWfIn1 =>
            cases ht.wf2 with | table _ _ hrWfIn2 =>
            rcases tableSchemaWf_cols_props hschIn with ⟨huniqIn, hcolsIn⟩
            simp only [Bool.and_eq_true, List.all_eq_true] at hkValid
            have hkSub : ∀ k ∈ keyNames, k ∈ tt.cols.map ColSpec.name := by
              intro k hk; have h1 := hkValid.2 k hk
              cases hf : tt.findCol? k <;> rw [hf] at h1 <;> try contradiction
              unfold TableTy.findCol? at hf
              have hfind := List.find?_some hf
              have hnEq := beq_iff_eq.mp hfind
              exact hnEq ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
            have hallInKeys : ∀ c ∈ tt.cols, c.name ∈ keyNames := fun c hc =>
              pigeonhole_distinct_idents hkValid.1 huniqIn hkSub (by simp [hlenEq]) c.name (List.mem_map_of_mem hc)
            have hallColsLow : ∀ c ∈ tt.cols, c.tags.subset L = true :=
              fun c hc => hlowKeys c.name (hallInKeys c hc) c (find_unique_of_mem huniqIn hc)
            rcases dedupTableRows_all_cols_props hd huniqIn (fun c hc => (hcolsIn c hc).1) hallInKeys
              (fun _ hm => False.elim (List.not_mem_nil hm)) hrWfIn1.to_forall hd1 with ⟨hp1, hnd1, hm1⟩
            rcases dedupTableRows_all_cols_props hd huniqIn (fun c hc => (hcolsIn c hc).1) hallInKeys
              (fun _ hm => False.elim (List.not_mem_nil hm)) hrWfIn2.to_forall hd2 with ⟨hp2, hnd2, hm2⟩
            rcases hlr with ⟨rows1', hpIn, hrelIn⟩
            have hmapEq : rows1'.map (fun r => ({ r with groupMeta := none } : TableRow)) =
                tv2.rows.map (fun r => ({ r with groupMeta := none } : TableRow)) := by
              clear hp1 hnd1 hm1 hp2 hnd2 hm2 hpIn hd1 hd2
              generalize tv2.rows = rows2 at hrelIn ⊢
              induction hrelIn with
              | nil => rfl
              | @cons a b _ _ hab _ ih =>
                have hcEq := CellsEquiv.all_low_eq hallColsLow hab
                simp only [List.map_cons, List.cons.injEq]
                exact ⟨by cases a; cases b; dsimp only at hcEq ⊢; rw [hcEq], ih⟩
            have hpReset : List.Perm (tv1.rows.map (fun r => ({ r with groupMeta := none } : TableRow)))
                (tv2.rows.map (fun r => ({ r with groupMeta := none } : TableRow))) :=
              hmapEq ▸ hpIn.map _
            have hpermOut : List.Perm _ _ := perm_of_nodup_same_mem_rows hd
              (fun x hx => ⟨(hp1 x hx).1, (hp1 x hx).2.1⟩)
              (fun y hy => ⟨(hp2 y hy).1, (hp2 y hy).2.1⟩)
              hnd1 hnd2
              (fun z hz => by
                rw [hm1 z hz, hm2 z hz]
                exact ⟨fun ⟨h, _⟩ => ⟨hpReset.subset h, fun _ _ hm => nomatch hm⟩,
                       fun ⟨h, _⟩ => ⟨hpReset.symm.subset h, fun _ _ hm => nomatch hm⟩⟩)
            refine ⟨_, hpermOut, RelList.refl_of_forall (fun r hr => ?_)⟩
            exact CellsEquiv.of_all_eq _ r.cells (by simp [(hp2 r hr).2.1.length_eq])
          · exact dedupTableRows_relList hlowKeys [] hlr hd1 hd2
        | sort inp keys =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          let sortKeyTags := TagSet.unionList ((keys.map Prod.fst).filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
          have hw1Raw := hvWf1.table_change_tags tt.rowTags (tt.orderTags.union sortKeyTags)
          have hw2Raw := hvWf2.table_change_tags tt.rowTags (tt.orderTags.union sortKeyTags)
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only; rw [hc1, hc2]
          let resetGM : TableRow → TableRow := fun r => { r with groupMeta := none }
          cases hord : (tt.orderTags.union sortKeyTags).subset L
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rcases ht.perm_rows hrLow with ⟨rows1', hpIn, hrelIn⟩
            have hmapRel : RelList (RowEquiv L (tt.cols.map (fun c => { c with aggKind := .raw })))
                (rows1'.map resetGM) (tv2.rows.map resetGM) :=
              hrelIn.map resetGM resetGM (fun _ _ hr => cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hr (fun _ _ h => h))
            have hpSort1 := insertionSortBy_perm (rowLtByKeys tt.cols keys) (tv1.rows.map resetGM)
            have hpSort2 := insertionSortBy_perm (rowLtByKeys tt.cols keys) (tv2.rows.map resetGM)
            rcases relList_perm_right hmapRel hpSort2.symm with ⟨rows1'', hpMid, hrelOut⟩
            exact ⟨rows1'', hpSort1.trans ((hpIn.map resetGM).trans hpMid), hrelOut⟩
          · simp only [↓reduceIte]
            dsimp only [sortKeyTags] at hord
            simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hord
            have hlr := ht.lowRows hrLow
            simp only [hord.1, ↓reduceIte] at hlr
            have hlowKeys : ∀ p ∈ keys, ∀ c, tt.cols.find? (fun x => x.name == p.1) = some c → c.tags.subset L = true :=
              fun p hp c hfc => hord.2 c.tags (List.mem_filterMap.mpr ⟨p.1, List.mem_map_of_mem hp, by unfold TableTy.findCol?; simp [hfc]⟩)
            have hs := insertionSortBy_forall2 (R := RowEquiv L tt.cols)
              (fun _ _ _ _ ha hb => rowLtByKeys_congr_of_low ha hb hlowKeys)
              (hlr.map resetGM resetGM (fun _ _ h => h))
            exact hs.imp (fun _ _ hr => cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hr (fun _ _ h => h))
        | limit inp n =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          have hw1Raw := hvWf1.table_change_tags (tt.rowTags.union tt.orderTags) tt.orderTags
          have hw2Raw := hvWf2.table_change_tags (tt.rowTags.union tt.orderTags) tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only
          simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
          have hlr := ht.lowRows hrLow.1
          simp only [hrLow.2, ↓reduceIte] at hlr ⊢
          exact RelList.map (R := RowEquiv L tt.cols)
            (S := RowEquiv L (tt.cols.map (fun (c : ColSpec) => { c with aggKind := .raw })))
            (fun r => ({ cells := r.cells, groupMeta := none } : TableRow))
            (fun r => ({ cells := r.cells, groupMeta := none } : TableRow))
            (fun _ _ hr => cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hr (fun _ _ h => h))
            (hlr.take n)
        | join kind leftP rightP on suffixes =>
          dsimp only at hev1 hev2
          simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
          simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
          simp only [planSuppressSafe, Bool.and_eq_true] at hpsup
          rcases hpr1 with ⟨hprL1, hprR1⟩; rcases hpr2 with ⟨hprL2, hprR2⟩
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hl : checkPlan prog (envToTyEnv env1) pc inSpec leftP <;> rw [hl] at hchk <;> try contradiction
          rename_i lPlan; dsimp only at hchk
          cases hr : checkPlan prog (envToTyEnv env1) pc inSpec rightP <;> rw [hr] at hchk <;> try contradiction
          rename_i rPlan; dsimp only at hchk
          cases lPlan <;> cases rPlan <;> try contradiction
          rename_i lTT rTT; dsimp only at hchk
          cases hrj : resolveJoinPairs lTT rTT on <;> rw [hrj] at hchk <;> try contradiction
          rename_i keyPairs; dsimp only at hchk
          cases hbj : buildJoinedCols kind lTT.cols rTT.cols on suffixes <;> rw [hbj] at hchk <;> try contradiction
          rename_i joinedCols; injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨lTV1, wl1, hoL1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨lTV2, wl2, hoL2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 leftP (.table lTT) (.table lTV1) (.table lTV2) wl1 wl2
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe.1 hpns.1 hpsup.1 hprL1 hprL2 hl hoL1 hoL2 with ⟨hlvEq, hwl⟩
          have hlDb1 := hdb'.2.2 hprog hsafeProg env1 pc w1 leftP hpDB1 henvCl1 hpsafe.1 hpns.1 hpsup.1 hprL1
          have hlDb2 := hdb'.2.2 hprog hsafeProg env2 pc w2 leftP hpDB2 henvCl2 hpsafe.1 hpns.1 (henv.envToTyEnv_eq ▸ hpsup.1) hprL2
          rw [hoL1] at hlDb1; rw [hoL2] at hlDb2
          rcases match_table_eq_ok hev1 with ⟨rTV1, wr1, hoR1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨rTV2, wr2, hoR2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec wl1 wl2 rightP (.table rTT) (.table rTV1) (.table rTV2) wr1 wr2
            henv hwl (progRespectsDB_congr hlDb1.2 hpDB1) (progRespectsDB_congr hlDb2.2 hpDB2)
            (envClosureSafe_congr hlDb1.2 henvCl1) (envClosureSafe_congr hlDb2.2 henvCl2)
            hpsafe.2 hpns.2 hpsup.2 (planRespectsDB_congr hlDb1.2 hprR1) (planRespectsDB_congr hlDb2.2 hprR2)
            hr hoR1 hoR2 with ⟨hrvEq, hwr⟩
          have htL := TableEquiv.of_planTy_valEquiv hpc hlvEq
          have htR := TableEquiv.of_planTy_valEquiv hpc hrvEq
          rcases htL.cols_eq with ⟨hlc1, hlc2⟩
          rcases htR.cols_eq with ⟨hrc1, hrc2⟩
          rw [hlc1, hrc1] at hev1; rw [hlc2, hrc2] at hev2
          have hrjEval : resolveJoinPairs { cols := lTT.cols } { cols := rTT.cols } on = .ok keyPairs := by
            let rec goEq (ps : List (Ident × Ident)) :
                resolveJoinPairs.go { cols := lTT.cols } { cols := rTT.cols } ps = resolveJoinPairs.go lTT rTT ps := by
              cases ps with
              | nil => rfl
              | cons p rest => cases p; unfold resolveJoinPairs.go; unfold TableTy.findCol?; dsimp only; rw [goEq rest]
            unfold resolveJoinPairs at hrj ⊢; dsimp only at hrj ⊢; rw [goEq]; exact hrj
          rw [hrjEval, hbj] at hev1 hev2; dsimp only at hev1 hev2
          split at hev1; contradiction
          split at hev2; contradiction
          cases hj1 : joinTableRows kind lTT.cols rTT.cols _ _ _ _ _ rTV1.rows lTV1.rows <;> rw [hj1] at hev1 <;> try contradiction
          cases hj2 : joinTableRows kind lTT.cols rTT.cols _ _ _ _ _ rTV2.rows lTV2.rows <;> rw [hj2] at hev2 <;> try contradiction
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          let onTags := TagSet.unionList (keyPairs.map (fun (lc, rc) => lc.tags.union rc.tags))
          let newRowTags := (lTT.rowTags.union rTT.rowTags).union onTags
          let newOrderTags := match kind with | .semi | .anti => lTT.orderTags | _ => lTT.orderTags.union rTT.orderTags
          have hw1Raw := hvWf1.table_change_tags newRowTags newOrderTags
          have hw2Raw := hvWf2.table_change_tags newRowTags newOrderTags
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hwr⟩
          intro hrLow; dsimp only
          dsimp only [newRowTags, onTags] at hrLow
          simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hrLow
          rcases hrLow with ⟨⟨hrLLow, hrRLow⟩, honLow⟩
          cases htL.wf1 with | table _ hschL hrWfL1 =>
          cases htR.wf1 with | table _ hschR hrWfR1 =>
          have hlUniq := (tableSchemaWf_cols_props hschL).1
          have hrUniq := (tableSchemaWf_cols_props hschR).1
          have hkpMem : ∀ kp ∈ keyPairs, kp.1 ∈ lTT.cols ∧ kp.2 ∈ rTT.cols := by
            let rec goMem (ps : List (Ident × Ident)) {kps : List (ColSpec × ColSpec)}
                (hg : resolveJoinPairs.go lTT rTT ps = .ok kps) : ∀ kp ∈ kps, kp.1 ∈ lTT.cols ∧ kp.2 ∈ rTT.cols := by
              cases ps with
              | nil => unfold resolveJoinPairs.go at hg; injection hg with e; subst e; intro _ hm; nomatch hm
              | cons p rest =>
                rcases p with ⟨lk, rk⟩; unfold resolveJoinPairs.go at hg
                cases hlF : lTT.findCol? lk <;> cases hrF : rTT.findCol? rk <;> simp [hlF, hrF] at hg
                split at hg <;> try contradiction
                simp only [bind, Except.bind] at hg
                cases htl : resolveJoinPairs.go lTT rTT rest <;> rw [htl] at hg <;> try contradiction
                injection hg with e; subst e
                intro kp hkp; rcases List.mem_cons.mp hkp with rfl | hrest
                · exact ⟨List.mem_of_find?_eq_some hlF, List.mem_of_find?_eq_some hrF⟩
                · exact goMem rest htl kp hrest
            unfold resolveJoinPairs at hrj
            cases on <;> dsimp only at hrj <;> (split at hrj; contradiction; exact goMem _ hrj)
          have hlLowKeys : ∀ k ∈ keyPairs.map (fun (lc, _) => lc.name), ∀ c, lTT.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
            intro k hk c hfc; rw [List.mem_map] at hk; rcases hk with ⟨⟨lc, rc⟩, hkp, rfl⟩
            have hfEq := find_unique_of_mem hlUniq (hkpMem (lc, rc) hkp).1
            rw [hfc] at hfEq; injection hfEq with ec; subst ec
            have hsub := honLow (c.tags.union rc.tags) (List.mem_map_of_mem hkp)
            simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hsub; exact hsub.1
          have hrLowKeys : ∀ k ∈ keyPairs.map (fun (_, rc) => rc.name), ∀ c, rTT.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
            intro k hk c hfc; rw [List.mem_map] at hk; rcases hk with ⟨⟨lc, rc⟩, hkp, rfl⟩
            have hfEq := find_unique_of_mem hrUniq (hkpMem (lc, rc) hkp).2
            rw [hfc] at hfEq; injection hfEq with ec; subst ec
            have hsub := honLow (lc.tags.union c.tags) (List.mem_map_of_mem hkp)
            simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hsub; exact hsub.2
          let sks := match on with | .sameKeys ks => ks | .pairs _ => []
          rcases zipIdx_filter_props (fun rc => !sks.contains rc.name) rTT.cols with ⟨hrKeepFst, hrKeepGet⟩
          change if newOrderTags.subset L = true then _ else _
          cases hord : newOrderTags.subset L
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rcases htL.perm_rows hrLLow with ⟨lRows1', hpL, hrelL⟩
            rcases htR.perm_rows hrRLow with ⟨rRows1', hpR, hrelR⟩
            have hrColsVal := fun c hc => (tableSchemaWf_cols_props hschR).2 c hc |>.1
            have hlKeysEx := resolveJoinPairs_keys_exist hrj
            rcases buildJoinedCols_props hlUniq hrUniq (tableSchemaWf_cols_props hschL).2 (tableSchemaWf_cols_props hschR).2 hbj with ⟨_, _, htyM⟩
            have hlWf1' : ∀ lr ∈ lRows1', CellsWf prog lr.cells lTT.cols := fun lr h => hrWfL1.to_forall lr (hpL.symm.subset h)
            have hrWf1' : ∀ rr ∈ rRows1', CellsWf prog rr.cells rTT.cols := fun rr h => hrWfR1.to_forall rr (hpR.symm.subset h)
            have htyPrep : ∀ (isLO : Bool),
                ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map (fun (rc, _) => { rc with ty := if isLO then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty =
                (rTT.cols.filter (fun rc => !sks.contains rc.name)).map (fun rc => if isLO then ensureOptionScalar rc.ty else rc.ty) := by
              intro isLO; rw [List.map_map, ← hrKeepFst, List.map_map]; rfl
            cases kind with
            | semi =>
              dsimp only at htyM hj1 hj2 ⊢
              rcases joinTableRows_sound .semi hrColsVal hlKeysEx hrKeepGet hrWf1' htyM lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .semi hrColsVal hlKeysEx hrKeepGet hrWf1' htyM lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .semi lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .semi hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys ⟨rRows1', .refl _, hrelR⟩ hrelL hj1' hj2⟩
            | anti =>
              dsimp only at htyM hj1 hj2 ⊢
              rcases joinTableRows_sound .anti hrColsVal hlKeysEx hrKeepGet hrWf1' htyM lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .anti hrColsVal hlKeysEx hrKeepGet hrWf1' htyM lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .anti lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .anti hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys ⟨rRows1', .refl _, hrelR⟩ hrelL hj1' hj2⟩
            | innerOne =>
              dsimp only at htyM hj1 hj2 ⊢
              have htyMatch' : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                  ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map (fun (rc, _) => { rc with ty := if false then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty := by
                rw [htyPrep false]; exact htyM
              rcases joinTableRows_sound .innerOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .innerOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .innerOne lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .innerOne hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys hrelR hrelL hj1' hj2⟩
            | innerManyToOne =>
              dsimp only at htyM hj1 hj2 ⊢
              have htyMatch' : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                  ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map (fun (rc, _) => { rc with ty := if false then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty := by
                rw [htyPrep false]; exact htyM
              rcases joinTableRows_sound .innerManyToOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .innerManyToOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .innerManyToOne lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .innerManyToOne hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys hrelR hrelL hj1' hj2⟩
            | innerMany =>
              dsimp only at htyM hj1 hj2 ⊢
              have htyMatch' : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                  ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map (fun (rc, _) => { rc with ty := if false then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty := by
                rw [htyPrep false]; exact htyM
              rcases joinTableRows_sound .innerMany hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .innerMany hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .innerMany lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .innerMany hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys hrelR hrelL hj1' hj2⟩
            | leftOne =>
              dsimp only at htyM hj1 hj2 ⊢
              have htyMatch' : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                  ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map (fun (rc, _) => { rc with ty := if true then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty := by
                rw [htyPrep true]; exact htyM
              rcases joinTableRows_sound .leftOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .leftOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .leftOne lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .leftOne hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys hrelR hrelL hj1' hj2⟩
            | leftManyToOne =>
              dsimp only at htyM hj1 hj2 ⊢
              have htyMatch' : joinedCols.map ColSpec.ty = lTT.cols.map ColSpec.ty ++
                  ((rTT.cols.zipIdx.filter (fun (rc, _) => !sks.contains rc.name)).map (fun (rc, _) => { rc with ty := if true then ensureOptionScalar rc.ty else rc.ty })).map ColSpec.ty := by
                rw [htyPrep true]; exact htyM
              rcases joinTableRows_sound .leftManyToOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lTV1.rows hrWfL1.to_forall with ⟨outMid, hjMid, _⟩
              rcases joinTableRows_sound .leftManyToOne hrColsVal hlKeysEx hrKeepGet hrWf1' htyMatch' lRows1' hlWf1' with ⟨out1', hj1', _⟩
              have hp1 := joinTableRows_perm_right .leftManyToOne lTT.cols rTT.cols _ _ _ _ _ hpR hj1 hjMid
              have hp2 : List.Perm outMid out1' := by
                rw [joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hjMid, joinTableRows_eq_flatMap _ _ _ _ _ _ _ _ _ hj1']
                exact perm_flatMap _ hpL
              exact ⟨out1', hp1.trans hp2, joinTableRows_relList .leftManyToOne hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys hrelR hrelL hj1' hj2⟩
          · simp only [↓reduceIte]
            cases kind with
            | semi | anti =>
              dsimp only [newOrderTags] at hord
              have hlrL := htL.lowRows hrLLow; simp only [hord, ↓reduceIte] at hlrL
              exact joinTableRows_relList _ hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys (htR.perm_rows hrRLow) hlrL hj1 hj2
            | innerOne | leftOne | innerManyToOne | leftManyToOne | innerMany =>
              dsimp only [newOrderTags] at hord
              simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hord
              have hlrL := htL.lowRows hrLLow; simp only [hord.1, ↓reduceIte] at hlrL
              have hlrR := htR.lowRows hrRLow; simp only [hord.2, ↓reduceIte] at hlrR
              exact joinTableRows_relList _ hbj hrKeepFst hrKeepGet hlLowKeys hrLowKeys hlrR hlrL hj1 hj2
        | union leftP rightP =>
          dsimp only at hev1 hev2
          simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
          simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
          simp only [planSuppressSafe, Bool.and_eq_true] at hpsup
          rcases hpr1 with ⟨hprL1, hprR1⟩; rcases hpr2 with ⟨hprL2, hprR2⟩
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hl : checkPlan prog (envToTyEnv env1) pc inSpec leftP <;> rw [hl] at hchk <;> try contradiction
          rename_i lPlan; dsimp only at hchk
          cases hr : checkPlan prog (envToTyEnv env1) pc inSpec rightP <;> rw [hr] at hchk <;> try contradiction
          rename_i rPlan; dsimp only at hchk
          cases lPlan <;> cases rPlan <;> try contradiction
          rename_i lTT rTT; dsimp only at hchk
          cases hmu : mergeUnionCols lTT.cols rTT.cols <;> rw [hmu] at hchk <;> try contradiction
          rename_i outCols; injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨lTV1, wl1, hoL1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨lTV2, wl2, hoL2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 leftP (.table lTT) (.table lTV1) (.table lTV2) wl1 wl2
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe.1 hpns.1 hpsup.1 hprL1 hprL2 hl hoL1 hoL2 with ⟨hlvEq, hwl⟩
          have hlDb1 := hdb'.2.2 hprog hsafeProg env1 pc w1 leftP hpDB1 henvCl1 hpsafe.1 hpns.1 hpsup.1 hprL1
          have hlDb2 := hdb'.2.2 hprog hsafeProg env2 pc w2 leftP hpDB2 henvCl2 hpsafe.1 hpns.1 (henv.envToTyEnv_eq ▸ hpsup.1) hprL2
          rw [hoL1] at hlDb1; rw [hoL2] at hlDb2
          rcases match_table_eq_ok hev1 with ⟨rTV1, wr1, hoR1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨rTV2, wr2, hoR2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec wl1 wl2 rightP (.table rTT) (.table rTV1) (.table rTV2) wr1 wr2
            henv hwl (progRespectsDB_congr hlDb1.2 hpDB1) (progRespectsDB_congr hlDb2.2 hpDB2)
            (envClosureSafe_congr hlDb1.2 henvCl1) (envClosureSafe_congr hlDb2.2 henvCl2)
            hpsafe.2 hpns.2 hpsup.2 (planRespectsDB_congr hlDb1.2 hprR1) (planRespectsDB_congr hlDb2.2 hprR2)
            hr hoR1 hoR2 with ⟨hrvEq, hwr⟩
          have htL := TableEquiv.of_planTy_valEquiv hpc hlvEq
          have htR := TableEquiv.of_planTy_valEquiv hpc hrvEq
          rcases htL.cols_eq with ⟨hlc1, hlc2⟩
          rcases htR.cols_eq with ⟨hrc1, hrc2⟩
          rw [hlc1, hrc1, hmu] at hev1; rw [hlc2, hrc2, hmu] at hev2
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          have hw1Raw := hvWf1.table_change_tags (lTT.rowTags.union rTT.rowTags) (lTT.orderTags.union rTT.orderTags)
          have hw2Raw := hvWf2.table_change_tags (lTT.rowTags.union rTT.rowTags) (lTT.orderTags.union rTT.orderTags)
          have hsch := hw1Raw.table_schemaWf
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hwr⟩
          intro hrLow; dsimp only
          simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
          have hmuSub : ∀ {lc rc oc : List ColSpec} {xs1 xs2 : List Val},
              mergeUnionCols lc rc = some oc →
              (CellsEquiv L lc xs1 xs2 → CellsEquiv L oc xs1 xs2) ∧
              (CellsEquiv L rc xs1 xs2 → CellsEquiv L oc xs1 xs2) := by
            intro lc rc oc xs1 xs2 hm
            induction lc generalizing rc oc xs1 xs2 with
            | nil => cases rc <;> simp [mergeUnionCols] at hm; subst hm; exact ⟨id, id⟩
            | cons l ltl ih =>
              cases rc with
              | nil => simp [mergeUnionCols] at hm
              | cons r rtl =>
                unfold mergeUnionCols at hm; split at hm <;> try contradiction
                simp only [Option.map_eq_some_iff] at hm; rcases hm with ⟨octl, hmtl, rfl⟩
                refine ⟨fun h => ?_, fun h => ?_⟩
                · cases h with | cons hc htl =>
                  exact .cons (fun hl => hc (by simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hl; exact hl.1)) ((ih hmtl).1 htl)
                · cases h with | cons hc htl =>
                  exact .cons (fun hl => hc (by simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hl; exact hl.2)) ((ih hmtl).2 htl)
          let resetGM : TableRow → TableRow := fun r => { r with groupMeta := none }
          rw [List.map_append, List.map_append]
          cases hord : (lTT.orderTags.union rTT.orderTags).subset L
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rcases htL.perm_rows hrLow.1 with ⟨l1', hpL, hrelL⟩
            rcases htR.perm_rows hrLow.2 with ⟨r1', hpR, hrelR⟩
            exact ⟨l1'.map resetGM ++ r1'.map resetGM, (hpL.map resetGM).append (hpR.map resetGM),
              (hrelL.map resetGM resetGM (fun _ _ h => (hmuSub hmu).1 h)).append
              (hrelR.map resetGM resetGM (fun _ _ h => (hmuSub hmu).2 h))⟩
          · simp only [↓reduceIte]
            simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hord
            have hlrL := htL.lowRows hrLow.1; simp only [hord.1, ↓reduceIte] at hlrL
            have hlrR := htR.lowRows hrLow.2; simp only [hord.2, ↓reduceIte] at hlrR
            exact (hlrL.map resetGM resetGM (fun _ _ h => (hmuSub hmu).1 h)).append
                  (hlrR.map resetGM resetGM (fun _ _ h => (hmuSub hmu).2 h))
        | groupBy inp keys =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          let keyTags := TagSet.unionList (keys.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
          have hw1Raw := hvWf1.table_change_tags (tt.rowTags.union keyTags) tt.orderTags
          have hw2Raw := hvWf2.table_change_tags (tt.rowTags.union keyTags) tt.orderTags
          cases ht.wf1 with | table _ hschIn _ =>
          have huniqIn := (tableSchemaWf_cols_props hschIn).1
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, ?_, ?_, fun h _ => by nomatch h⟩, hw'⟩
          · intro hrLow c hc hgk
            dsimp only [keyTags] at hrLow
            simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hrLow
            rw [List.mem_map] at hc; rcases hc with ⟨orig, horig, rfl⟩
            cases hcont : keys.contains orig.name
            · rw [hcont] at hgk; nomatch hgk
            · rw [hcont] at hgk; dsimp only at *
              have hfEq := find_unique_of_mem huniqIn horig
              exact hrLow.2 orig.tags (List.mem_filterMap.mpr ⟨orig.name, List.contains_iff_mem.mp hcont, by unfold TableTy.findCol?; simp [hfEq]⟩)
          · intro hrLow; dsimp only
            simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
            exact ht.map_lowRows hrLow.1 (fun r => { r with groupMeta := none }) (fun r => { r with groupMeta := none }) (fun _ _ hr =>
              cellsEquiv_map_tags (fun c => if keys.contains c.name then { c with aggKind := .groupKey } else { c with aggKind := .raw })
                hr (fun c _ hsub => by split at hsub <;> exact hsub))
        | summarize inp aggs distinctKey =>
          dsimp only at hev1 hev2
          simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
          rw [checkPlan_inSpec_true hchk] at hev1
          rw [checkPlan_inSpec_true hchk2] at hev2
          cases pTy with
          | dynamic _ => dsimp only at hev1; nomatch hev1
          | table outTT =>
            dsimp only at hev1 hev2
            unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
            cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
            rename_i inP; cases inP <;> try contradiction
            rename_i tt; dsimp only at hchk
            split at hchk <;> try contradiction
            have hdkStep : ∃ dkTags : TagSet,
                (∀ dk, distinctKey = some dk → ∃ dkCol, tt.findCol? dk = some dkCol ∧ dkCol.tags = dkTags) ∧
                (do
                  let aggCols ← checkAggItemList prog (envToTyEnv env1) tt aggs
                  let outCols := (tt.cols.filter (fun (c : ColSpec) => (tt.groupedBy.getD []).contains c.name)).map (fun (c : ColSpec) => { c with aggKind := .groupKey }) ++ aggCols
                  if !distinctIdents (outCols.map ColSpec.name) then .error "Summarize output column names must be strictly unique"
                  else .ok (PlanTy.table { cols := outCols, rowTags := tt.rowTags.union dkTags, orderTags := TagSet.empty, groupedBy := some (tt.groupedBy.getD []), summarized := true, distinctBy := distinctKey })) = .ok (.table outTT) := by
              cases distinctKey with
              | none => exact ⟨TagSet.empty, (fun _ h => nomatch h), hchk⟩
              | some dk =>
                dsimp only at hchk
                cases hfc : tt.findCol? dk <;> rw [hfc] at hchk <;> try contradiction
                rename_i dkCol; dsimp only at hchk
                split at hchk <;> try contradiction
                exact ⟨dkCol.tags, (fun _ he => by injection he with e; subst e; exact ⟨dkCol, hfc, rfl⟩), hchk⟩
            rcases hdkStep with ⟨dkTags, hdkFind, hchk⟩
            simp only [bind, Except.bind] at hchk
            cases hagg : checkAggItemList prog (envToTyEnv env1) tt aggs <;> rw [hagg] at hchk <;> try contradiction
            rename_i aggCols; dsimp only at hchk
            split at hchk <;> try contradiction
            injection hchk with ep; injection ep with ep; subst ep
            rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
            rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
            rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) wi1 wi2
              henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe.1 hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hwi⟩
            have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
            rcases ht.cols_eq with ⟨hc1, hc2⟩
            cases ht.wf1 with | table _ hschIn hrWfIn1 =>
            have hcolsIn := fun c hc => (tableSchemaWf_cols_props hschIn).2 c hc |>.1
            rcases summarize_keyCols_props hc1 hschIn with ⟨hkColsEq1, hgkNames1, hkTyped1⟩
            have hgkEvalEq : (tv2.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name =
                (tv1.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name := by rw [hc1, hc2]
            have hkColsEvalEq : (tv2.cols.filter (fun c => ((tv2.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name).contains c.name)).map (fun c => { c with aggKind := .groupKey }) =
                (tv1.cols.filter (fun c => ((tv1.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name).contains c.name)).map (fun c => { c with aggKind := .groupKey }) := by rw [hc1, hc2]
            rw [hkColsEvalEq, hgkEvalEq] at hev2
            rw [hkColsEq1, List.drop_left] at hev1 hev2
            rcases checkAggItemList_props hcolsIn hagg with ⟨haggLen, haggProps⟩
            simp only [haggLen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hev1 hev2
            cases hext1 : extractAllRowsKeyVals tv1.cols _ tv1.rows <;> rw [hext1] at hev1 <;> try contradiction
            cases hext2 : extractAllRowsKeyVals tv2.cols _ tv2.rows <;> rw [hext2] at hev2 <;> try contradiction
            rename_i rawKeys1 rawKeys2; dsimp only at hev1 hev2
            have hsw : ∀ {f tv gk dk dki ag ac oc w gks rv w'},
                evalSummarizeGroups f tv gk dk dki ag ac oc w gks = .ok rv w' → w' = w := by
              intro f tv gk dk dki ag ac oc w gks rv w' h
              have hw := (evalSummarizeGroups_world_and_safe (prog := prog) (L := L) f tv gk dk dki ag ac oc w gks).2.2
              rw [h] at hw; exact hw
            have hwEq1 := hsw hev1; subst hwEq1
            have hwEq2 := hsw hev2; subst hwEq2
            cases hvWf1 with | @table resTV1 _ _ _ _ =>
            cases hvWf2 with | @table resTV2 _ _ _ _ =>
            have hw1Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table resTV1) _).table_change_tags (tt.rowTags.union dkTags) TagSet.empty
            have hw2Raw := (ValWf.table ‹_› ‹_› ‹_› : ValWf prog (.table resTV2) _).table_change_tags (tt.rowTags.union dkTags) TagSet.empty
            have hsumFull : (tt.rowTags.union dkTags).subset L = true →
                RelList (fun r1 r2 => RowEquiv L ((tt.cols.filter (fun c => (tt.groupedBy.getD []).contains c.name)).map (fun c => { c with aggKind := .groupKey }) ++ aggCols) r1 r2 ∧ r1.groupMeta = r2.groupMeta)
                  resTV1.rows resTV2.rows := by
              intro hrLow
              simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
              let gkEval := (tv1.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name
              let keyColsChk := (tt.cols.filter (fun c => (tt.groupedBy.getD []).contains c.name)).map (fun c => { c with aggKind := .groupKey })
              have hlowGK : ∀ k ∈ gkEval, ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
                intro k hk c hfc
                dsimp only [gkEval] at hk; rw [hc1, List.mem_map] at hk
                rcases hk with ⟨orig, horigF, rfl⟩
                have huniqIn := (tableSchemaWf_cols_props hschIn).1
                have hfEq := find_unique_of_mem huniqIn (List.mem_filter.mp horigF).1
                rw [hfc] at hfEq; injection hfEq with ec; subst ec
                exact ht.groupingLow hrLow.1 c (List.mem_filter.mp horigF).1 (of_decide_eq_true (List.mem_filter.mp horigF).2)
              have hgkEqTT : gkEval = (tt.cols.filter (fun c => decide (c.aggKind = .groupKey))).map ColSpec.name := by
                dsimp only [gkEval]; rw [hc1]
              rw [hc1] at hext1; rw [← hgkEqTT] at hext1; rw [hc2] at hext2
              rcases extractAllRowsKeyVals_eq_filterMap tt.cols gkEval hext1 with ⟨hfm1, _⟩
              rcases extractAllRowsKeyVals_eq_filterMap tt.cols gkEval hext2 with ⟨hfm2, _⟩
              rcases ht.perm_rows hrLow.1 with ⟨rows1', hpIn, hrelIn⟩
              have hpRaw : List.Perm rawKeys1 rawKeys2 := by
                rw [hfm1, hfm2]
                have heq' := RelList.filterMap_congr (R := RowEquiv L tt.cols)
                  (fun a b hr => extractKeyVals_congr_of_low hr hlowGK) hrelIn
                exact heq' ▸ perm_filterMap _ hpIn
              have hrawSort : ∀ kv ∈ rawKeys1, SortableValList kv := by
                intro kv hkv; rw [hfm1, List.mem_filterMap] at hkv; rcases hkv with ⟨r, hr, hkvEq⟩
                exact extractKeyVals_sortable hd hcolsIn (hrWfIn1.to_forall r hr) hkvEq
              have hlenRowsEq := ht.length_eq hrLow.1
              have hemRowsEq : tv1.rows.isEmpty = tv2.rows.isEmpty := by
                cases h1 : tv1.rows <;> cases h2 : tv2.rows <;> simp [h1, h2] at hlenRowsEq ⊢
              have hsKeysEq : (if gkEval.isEmpty && tv1.rows.isEmpty then [[]] else dedupAdjacentBy valListEq (insertionSortBy valListLt rawKeys1)) =
                  (if gkEval.isEmpty && tv2.rows.isEmpty then [[]] else dedupAdjacentBy valListEq (insertionSortBy valListLt rawKeys2)) := by
                rw [hemRowsEq, insertionSortBy_perm_eq valListLt_irrefl valListLt_trans valListLt_trichotomy hrawSort hpRaw]
              rw [← hsKeysEq] at hev2
              rcases extractAllRowsKeyVals_typed hkTyped1 tv1.rows (hc1 ▸ hrWfIn1.to_forall) with ⟨rk1', hext1', hrkWf⟩
              rw [← hgkNames1] at hext1'; rw [hc1] at hext1'; rw [← hgkEqTT, hext1] at hext1'
              injection hext1' with erk; rw [← erk] at hrkWf
              have hlenKey : ((tv1.cols.filter (fun c => gkEval.contains c.name)).map (fun c => { c with aggKind := .groupKey })).length = keyColsChk.length :=
                congrArg List.length hkColsEq1
              have hgksLen : ∀ gk ∈ (if gkEval.isEmpty && tv1.rows.isEmpty then [[]] else dedupAdjacentBy valListEq (insertionSortBy valListLt rawKeys1)),
                  gk.length = keyColsChk.length := by
                intro gk hgk; rw [← hlenKey]
                cases hcond : (gkEval.isEmpty && tv1.rows.isEmpty)
                · rw [hcond] at hgk; simp only [Bool.false_eq_true, ↓reduceIte] at hgk
                  have h1 := mem_dedupAdjacentBy valListEq gk _ hgk
                  have h2 := mem_insertionSortBy valListLt gk rawKeys1 h1
                  exact (hrkWf gk h2).length_eq
                · rw [hcond] at hgk; simp only [↓reduceIte, List.mem_singleton] at hgk; subst hgk
                  simp only [Bool.and_eq_true, List.isEmpty_iff] at hcond
                  have hfil : tv1.cols.filter (fun _ => false) = [] := by
                    induction tv1.cols with | nil => rfl | cons _ _ ih => exact ih
                  rw [hcond.1]; simp only [List.contains_nil, List.length_nil, List.length_map, hfil]
              have hdkAux : ∀ (dk? : Option Ident) (cols1 cols2 : List ColSpec),
                  cols1 = tt.cols → cols2 = tt.cols →
                  (∀ dk, dk? = some dk → ∃ dkCol, tt.findCol? dk = some dkCol ∧ dkCol.tags = dkTags) →
                  match dk?, dk?.bind (lookupColIdx? cols1), dk?.bind (lookupColIdx? cols2) with
                  | none, _, _ => True
                  | some _, some (i1, c1), some (i2, _) => i1 = i2 ∧ tt.cols[i1]? = some c1 ∧ c1.tags.subset L = true
                  | some _, none, none => True
                  | _, _, _ => False := by
                intro dk? cols1 cols2 h1 h2 hfind
                cases dk? with
                | none => trivial
                | some dk =>
                  rcases hfind dk rfl with ⟨dkCol, hfc, htagsEq⟩
                  rcases lookupColIdx?_of_find? hfc with ⟨dIdx, hdLk, hdGet⟩
                  subst h1; subst h2; rw [Option.bind_some, hdLk]
                  exact ⟨rfl, hdGet, htagsEq.symm ▸ hrLow.2⟩
              have hdkCond := hdkAux distinctKey tv1.cols tv2.cols hc1 hc2 hdkFind
              exact evalSummarizeGroups_ni hprog hsafeProg henv ht hrLow.1 hlowGK hdkCond hagg rfl hgksLen hev1 hev2
            refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, ?_, ?_, ?_⟩, hwi⟩
            · intro hrLow c hc hgk
              simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hrLow
              rw [List.mem_append] at hc
              rcases hc with hkMem | haMem
              · rw [List.mem_map] at hkMem; rcases hkMem with ⟨orig, horigF, rfl⟩
                have horigIn := (List.mem_filter.mp horigF).1
                have horigCont := (List.mem_filter.mp horigF).2
                simp only [TableSchemaWf, Bool.and_eq_true, List.all_eq_true] at hschIn
                have hgkOrig : orig.aggKind = .groupKey :=
                  of_decide_eq_true ((of_decide_eq_true (hschIn.1.2 orig horigIn).2).trans horigCont)
                exact ht.groupingLow hrLow.1 orig horigIn hgkOrig
              · exact absurd hgk (haggProps c haMem).2.2
            · intro hrLow; dsimp only
              simp only [TagSet.empty_subset, ↓reduceIte]
              exact (hsumFull hrLow).imp (fun _ _ h => h.1)
            · intro _ hrLow; dsimp only
              simp only [TagSet.empty_subset, ↓reduceIte]
              exact hsumFull hrLow
        | window inp items =>
          dsimp only at hev1 hev2
          rw [checkPlan_inSpec_true hchk] at hev1
          rw [checkPlan_inSpec_true hchk2] at hev2
          cases pTy with
          | dynamic _ => dsimp only at hev1; nomatch hev1
          | table outTT =>
            dsimp only at hev1 hev2
            unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
            cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
            rename_i inP; cases inP <;> try contradiction
            rename_i tt; dsimp only at hchk
            split at hchk <;> try contradiction
            cases hwApp : applyWindowItems tt.orderTags (tt.cols.map (fun c => { c with aggKind := .raw })) items <;>
              rw [hwApp] at hchk <;> try contradiction
            rename_i outCols; dsimp only at hchk
            split at hchk <;> try contradiction
            injection hchk with ep; injection ep with ep; subst ep
            rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
            rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
            rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
              henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
            have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
            rcases ht.cols_eq with ⟨hc1, hc2⟩
            cases hw1 : evalWindowItems _ items <;> rw [hw1] at hev1 <;> try contradiction
            cases hw2 : evalWindowItems _ items <;> rw [hw2] at hev2 <;> try contradiction
            injection hev1 with e1 ew1; injection hev2 with e2 ew2
            subst e1; subst e2; subst ew1; subst ew2
            have hw1Raw := hvWf1.table_change_tags tt.rowTags tt.orderTags
            have hw2Raw := hvWf2.table_change_tags tt.rowTags tt.orderTags
            have hsch := hw1Raw.table_schemaWf
            refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
            intro hrLow; dsimp only
            cases ht.wf1 with | table _ hschIn hrWfIn1 =>
            cases ht.wf2 with | table _ _ hrWfIn2 =>
            rcases tableSchemaWf_cols_props hschIn with ⟨huniqIn, hcolsIn⟩
            let rawCols := tt.cols.map (fun c => { c with aggKind := .raw })
            have hnamesRaw : rawCols.map ColSpec.name = tt.cols.map ColSpec.name := by dsimp only [rawCols]; induction tt.cols <;> simp [*]
            have hrawProps : ∀ c ∈ rawCols, validScalarTy prog c.ty = true ∧ (c.bucketed = true → c.ty = .text) ∧ c.aggKind = .raw := by
              intro c hc; dsimp only [rawCols] at hc; rw [List.mem_map] at hc; rcases hc with ⟨o, ho, rfl⟩
              exact ⟨(hcolsIn o ho).1, (hcolsIn o ho).2, rfl⟩
            have hinitWf1 : RowsWf prog (tv1.rows.map (fun r => { r with groupMeta := none })) rawCols false false :=
              RowsWf.of_forall_raw (fun r hr => by rw [List.mem_map] at hr; rcases hr with ⟨o, ho, rfl⟩; exact (hrWfIn1.to_forall o ho).congr_ty (map_ty_with_aggKind tt.cols .raw).symm)
            have hinitWf2 : RowsWf prog (tv2.rows.map (fun r => { r with groupMeta := none })) rawCols false false :=
              RowsWf.of_forall_raw (fun r hr => by rw [List.mem_map] at hr; rcases hr with ⟨o, ho, rfl⟩; exact (hrWfIn2.to_forall o ho).congr_ty (map_ty_with_aggKind tt.cols .raw).symm)
            have hinitRel := ht.map_lowRows hrLow (fun r => { r with groupMeta := none }) (fun r => { r with groupMeta := none })
              (fun _ _ hr => cellsEquiv_map_tags (fun c => { c with aggKind := .raw }) hr (fun _ _ h => h))
            exact evalWindowItems_ni items (hnamesRaw ▸ huniqIn) hrawProps hrawProps
              (by simp [hc1, rawCols]) (by simp [hc2, rawCols]) rfl rfl hinitWf1 hinitWf2 hwApp hw1 hw2 hinitRel
        | fillGaps inp col stepMicros over fill =>
          dsimp only at hev1 hev2
          rw [checkPlan_inSpec_true hchk] at hev1
          rw [checkPlan_inSpec_true hchk2] at hev2
          cases pTy with
          | dynamic _ => dsimp only at hev1; nomatch hev1
          | table outTT =>
            dsimp only at hev1 hev2
            unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
            cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
            rename_i inP; cases inP <;> try contradiction
            rename_i tt; dsimp only at hchk
            split at hchk <;> try contradiction
            cases htc : tt.findCol? col <;> rw [htc] at hchk <;> try contradiction
            rename_i tCol; dsimp only at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            rename_i hoverEx; simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true] at hoverEx
            split at hchk <;> try contradiction
            injection hchk with ep; injection ep with ep; subst ep
            rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
            rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
            injection hev1 with e1 ew1; injection hev2 with e2 ew2
            subst e1; subst e2; subst ew1; subst ew2
            rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
              henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
            have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
            let overTags := TagSet.unionList (over.filterMap (fun k => (tt.findCol? k).map ColSpec.tags))
            let newRowTags := (tt.rowTags.union tCol.tags).union overTags
            have hw1Raw := hvWf1.table_change_tags newRowTags TagSet.empty
            have hw2Raw := hvWf2.table_change_tags newRowTags TagSet.empty
            have hsch := hw1Raw.table_schemaWf
            refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
            intro hrLow; dsimp only
            simp only [TagSet.empty_subset, ↓reduceIte]
            dsimp only [newRowTags, overTags] at hrLow
            simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hrLow
            rcases hrLow with ⟨⟨hrInLow, htColLow⟩, hoverLow⟩
            have hkeysExist : ∀ k ∈ over ++ [col], (tt.cols.find? (fun c => c.name == k)).isSome = true := by
              intro k hk; rw [List.mem_append, List.mem_singleton] at hk
              rcases hk with ho | rfl
              · exact (hoverEx k ho).2
              · unfold TableTy.findCol? at htc; simp [htc]
            have hkeysLow : ∀ k ∈ over ++ [col], ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
              intro k hk c hfc; rw [List.mem_append, List.mem_singleton] at hk
              rcases hk with ho | rfl
              · exact hoverLow c.tags (List.mem_filterMap.mpr ⟨k, ho, by unfold TableTy.findCol?; simp [hfc]⟩)
              · unfold TableTy.findCol? at htc; rw [htc] at hfc; injection hfc with ec; subst ec; exact htColLow
            exact fillGaps_lowRows hd ht hrInLow hkeysExist hkeysLow
        | pivotWider inp namesFrom valuesFrom staticCols fill =>
          dsimp only at hev1 hev2
          rw [checkPlan_inSpec_true hchk] at hev1
          rw [checkPlan_inSpec_true hchk2] at hev2
          cases pTy with
          | dynamic _ => dsimp only at hev1; nomatch hev1
          | table outTT =>
            dsimp only at hev1 hev2
            unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
            cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
            rename_i inP; cases inP <;> try contradiction
            rename_i tt; dsimp only at hchk
            split at hchk <;> try contradiction
            cases hnf : tt.findCol? namesFrom <;> cases hvf : tt.findCol? valuesFrom <;>
              rw [hnf, hvf] at hchk <;> try contradiction
            rename_i nCol vCol; dsimp only at hchk
            split at hchk <;> try contradiction
            cases hfl : checkLiteral prog TagSet.empty fill <;> rw [hfl] at hchk <;> try contradiction
            dsimp only at hchk
            split at hchk <;> try contradiction
            split at hchk <;> try contradiction
            injection hchk with ep; injection ep with ep; subst ep
            rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
            rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
            rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
              henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
            have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
            rcases ht.cols_eq with ⟨hc1, hc2⟩
            rcases lookupColIdx?_of_find? hnf with ⟨nIdx, hnLk, hnGet⟩
            rcases lookupColIdx?_of_find? hvf with ⟨vIdx, hvLk, hvGet⟩
            rw [hc1, hnLk, hvLk] at hev1; rw [hc2, hnLk, hvLk] at hev2; dsimp only at hev1 hev2
            cases hext1 : extractAllRowsKeyVals tt.cols _ tv1.rows <;> rw [hext1] at hev1 <;> try contradiction
            cases hext2 : extractAllRowsKeyVals tt.cols _ tv2.rows <;> rw [hext2] at hev2 <;> try contradiction
            injection hev1 with e1 ew1; injection hev2 with e2 ew2
            subst e1; subst e2; subst ew1; subst ew2
            let idCols := (tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map (fun c => { c with aggKind := .raw })
            let idTags := TagSet.unionList (idCols.map ColSpec.tags)
            let newRowTags := (tt.rowTags.union nCol.tags).union idTags
            have hw1Raw := hvWf1.table_change_tags newRowTags TagSet.empty
            have hw2Raw := hvWf2.table_change_tags newRowTags TagSet.empty
            have hsch := hw1Raw.table_schemaWf
            cases ht.wf1 with | table _ hschIn _ =>
            have huniqIn := (tableSchemaWf_cols_props hschIn).1
            refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
            intro hrLow; dsimp only
            simp only [TagSet.empty_subset, ↓reduceIte]
            dsimp only [newRowTags, idTags] at hrLow
            simp only [TagSet.union_subset_iff, Bool.and_eq_true, TagSet.unionList_subset_iff] at hrLow
            rcases hrLow with ⟨⟨hrInLow, hnLow⟩, hidTagsLow⟩
            have hidLow : ∀ k ∈ ((tt.cols.filter (fun c => c.name != namesFrom && c.name != valuesFrom)).map ColSpec.name),
                ∀ c, tt.cols.find? (fun x => x.name == k) = some c → c.tags.subset L = true := by
              intro k hk c hfc; rw [List.mem_map] at hk; rcases hk with ⟨orig, horigF, rfl⟩
              have hfEq := find_unique_of_mem huniqIn (List.mem_filter.mp horigF).1
              rw [hfc] at hfEq; injection hfEq with ec; subst ec
              exact hidTagsLow c.tags (by rw [List.mem_map]; refine ⟨{ c with aggKind := .raw }, List.mem_map.mpr ⟨c, horigF, rfl⟩, rfl⟩)
            have hpiv := pivotWider_lowRows hd ht hrInLow hnGet hvGet hnLow hidLow
              (by simpa [List.map_map, Function.comp_def, hc1] using hext1)
              (by simpa [List.map_map, Function.comp_def, hc2] using hext2)
              (staticCols := staticCols) (fillVal := evalLiteral fill)
            simp only [List.map_map, Function.comp_def, hc1, hc2] at hpiv ⊢
            exact hpiv
        | crosstab inp rowsCol colsCol valuesCol fill =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          cases hrc : tt.findCol? rowsCol <;> cases hcc : tt.findCol? colsCol <;> cases hvc : tt.findCol? valuesCol <;>
            rw [hrc, hcc, hvc] at hchk <;> try contradiction
          rename_i rCol cCol vCol; dsimp only at hchk
          cases hfl : checkLiteral prog TagSet.empty fill <;> rw [hfl] at hchk <;> try contradiction
          dsimp only at hchk
          split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          rcases lookupColIdx?_of_find? hrc with ⟨rIdx, hrLk, hrGet⟩
          rcases lookupColIdx?_of_find? hcc with ⟨cIdx, hcLk, hcGet⟩
          rcases lookupColIdx?_of_find? hvc with ⟨vIdx, hvLk, hvGet⟩
          rw [hc1, hrLk, hcLk, hvLk] at hev1; rw [hc2, hrLk, hcLk, hvLk] at hev2
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          refine ⟨ValEquiv.mk_smart hvWf1 hvWf2 rfl rfl (fun _ => .dynTable (fun hdtLow => ?_)), hw'⟩
          simp only [TagSet.union_subset_iff, Bool.and_eq_true] at hdtLow
          rcases hdtLow.1 with ⟨⟨⟨⟨⟨hrInLow, hoInLow⟩, hrColLow⟩, hcColLow⟩, hvColLow⟩, _⟩
          have hlr := ht.lowRows hrInLow
          simp only [hoInLow, ↓reduceIte] at hlr
          exact crosstab_eq_of_low rowsCol (evalLiteral fill) hlr hrGet hcGet hvGet hrColLow hcColLow hvColLow
        | redact inp col replacement =>
          dsimp only at hev1 hev2
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; cases inP <;> try contradiction
          rename_i tt; dsimp only at hchk
          cases htc : tt.findCol? col <;> rw [htc] at hchk <;> try contradiction
          dsimp only at hchk; split at hchk <;> try contradiction
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) _ _
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hi hoI1 hoI2 with ⟨hivEq, hw'⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          rcases lookupColIdx?_of_find? htc with ⟨cIdx, hcLk, hcGet⟩
          rw [hc1, hcLk] at hev1; rw [hc2, hcLk] at hev2
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          have hw1Raw := hvWf1.table_change_tags tt.rowTags tt.orderTags
          have hw2Raw := hvWf2.table_change_tags tt.rowTags tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          cases ht.wf1 with | table _ hschIn _ =>
          have huniqIn := (tableSchemaWf_cols_props hschIn).1
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hw'⟩
          intro hrLow; dsimp only
          exact ht.map_lowRows hrLow (fun r => { cells := r.cells.set cIdx (Val.text replacement), groupMeta := none })
            (fun r => { cells := r.cells.set cIdx (Val.text replacement), groupMeta := none }) (fun _ _ hr => by
            apply cellsEquiv_set_at (fun c => if c.name == col then { c with ty := .text, tags := pc, bucketed := false, aggKind := .raw } else { c with aggKind := .raw }) cIdx hr
            intro i c hi
            refine ⟨fun _ _ => rfl, fun hne hsub => ?_⟩
            have hcnEq := (lookupColIdx?_props hcLk).2
            have hneName : (c.name == col) = false := by
              cases hb : (c.name == col); rfl
              exact absurd (distinctIdents_idx_unique huniqIn hi hcGet ((beq_iff_eq.mp hb).trans hcnEq.symm)) hne
            rw [hneName] at hsub; exact hsub)
        | pseudonymize inp col secretExpr =>
          dsimp only at hev1 hev2
          simp only [planSafeForNI, Bool.and_eq_true] at hpsafe
          simp only [planNoSpecCalls, Bool.and_eq_true] at hpns
          simp only [planSuppressSafe, Bool.and_eq_true] at hpsup
          rcases hpsafe with ⟨⟨⟨hpiiL, hsecL⟩, hpsInp⟩, hesSec⟩
          rcases hpr1 with ⟨hprI1, hprS1⟩; rcases hpr2 with ⟨hprI2, hprS2⟩
          unfold checkPlan at hchk; simp only [bind, Except.bind] at hchk
          cases hi : checkPlan prog (envToTyEnv env1) pc inSpec inp <;> rw [hi] at hchk <;> try contradiction
          rename_i inP; dsimp only at hchk
          cases hs : checkExpr prog (envToTyEnv env1) [] pc inSpec secretExpr <;> rw [hs] at hchk <;> try contradiction
          rename_i secLTy; dsimp only at hchk
          cases inP <;> try contradiction
          rename_i tt
          cases secLTy with | mk sty sTs =>
          cases sty <;> dsimp only [LTy.ty] at hchk <;> try contradiction
          cases htc : tt.findCol? col <;> rw [htc] at hchk <;> try contradiction
          rename_i targetCol; dsimp only at hchk
          split at hchk <;> try contradiction
          rename_i hsecSub; simp only [Bool.and_eq_true] at hsecSub
          injection hchk with ep; subst ep
          rcases match_table_eq_ok hev1 with ⟨tv1, wi1, hoI1, hev1⟩
          rcases match_table_eq_ok hev2 with ⟨tv2, wi2, hoI2, hev2⟩
          rcases ihP hprog hsafeProg env1 env2 pc inSpec w1 w2 inp (.table tt) (.table tv1) (.table tv2) wi1 wi2
            henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsInp hpns.1 hpsup.1 hprI1 hprI2 hi hoI1 hoI2 with ⟨hivEq, hwi⟩
          have hiDb1 := hdb'.2.2 hprog hsafeProg env1 pc w1 inp hpDB1 henvCl1 hpsInp hpns.1 hpsup.1 hprI1
          have hiDb2 := hdb'.2.2 hprog hsafeProg env2 pc w2 inp hpDB2 henvCl2 hpsInp hpns.1 (henv.envToTyEnv_eq ▸ hpsup.1) hprI2
          rw [hoI1] at hiDb1; rw [hoI2] at hiDb2
          rcases match_capSecret_eq_ok hev1 with ⟨h1, sName1, ws1, hoS1, hev1⟩
          rcases match_capSecret_eq_ok hev2 with ⟨h2, sName2, ws2, hoS2, hev2⟩
          have hsEq := ihE hprog hsafeProg env1 env2 [] pc inSpec wi1 wi2 secretExpr _
            henv rfl (fun _ hm => nomatch hm) hwi
            (progRespectsDB_congr hiDb1.2 hpDB1) (progRespectsDB_congr hiDb2.2 hpDB2)
            (envClosureSafe_congr hiDb1.2 henvCl1) (envClosureSafe_congr hiDb2.2 henvCl2)
            hesSec hpns.2 hpsup.2 (exprRespectsDB_congr hiDb1.2 hprS1) (exprRespectsDB_congr hiDb2.2 hprS2)
            hs (by rw [hoS1]; trivial) (by rw [hoS2]; trivial)
          rw [hoS1, hoS2] at hsEq; rcases hsEq with ⟨hws, hsvEq⟩
          have hsTsLow : sTs.subset L = true := by
            have hbound : ((TagSet.singleton "secret").union pc).subset L = true := by
              rw [TagSet.union_subset_iff, Bool.and_eq_true]
              refine ⟨?_, hpc⟩
              rw [TagSet.subset_iff]; intro t htMem
              simp only [TagSet.mem_singleton, decide_eq_true_eq] at htMem; subst htMem; exact hsecL
            exact TagSet.subset_trans hsecSub.2 hbound
          have ⟨hhEq, hnEq⟩ : h1 = h2 ∧ sName1 = sName2 := by cases hsvEq.payload hsTsLow; exact ⟨rfl, rfl⟩
          subst hhEq; subst hnEq
          rcases hws.secretsLowEq hsecL with ⟨hrealSecEq, hfakeSecEq⟩
          have ht := TableEquiv.of_planTy_valEquiv hpc hivEq
          rcases ht.cols_eq with ⟨hc1, hc2⟩
          rcases lookupColIdx?_of_find? htc with ⟨cIdx, hcLk, hcGet⟩
          rw [hc1, hcLk] at hev1; rw [hc2, hcLk] at hev2; dsimp only at hev1 hev2
          dsimp only [outWorld] at hrealSecEq hfakeSecEq
          rw [hrealSecEq, hfakeSecEq] at hev1
          cases hm1 : mapPseudonymizeRows _ cIdx tv1.rows <;> rw [hm1] at hev1 <;> try contradiction
          cases hm2 : mapPseudonymizeRows _ cIdx tv2.rows <;> rw [hm2] at hev2 <;> try contradiction
          injection hev1 with e1 ew1; injection hev2 with e2 ew2
          subst e1; subst e2; subst ew1; subst ew2
          have hw1Raw := hvWf1.table_change_tags tt.rowTags tt.orderTags
          have hw2Raw := hvWf2.table_change_tags tt.rowTags tt.orderTags
          have hsch := hw1Raw.table_schemaWf
          cases ht.wf1 with | table _ hschIn hrWfIn1 =>
          have huniqIn := (tableSchemaWf_cols_props hschIn).1
          have hcnEq := (lookupColIdx?_props hcLk).2
          refine ⟨TableEquiv.to_valEquiv_planTy ⟨hw1Raw, hw2Raw, groupingLow_of_groupedBy_none rfl hsch, ?_, fun h _ => by nomatch h⟩, hws⟩
          intro hrLow; dsimp only
          let keyMat := match h1 with
            | .real => (match ws2.realSecrets.find? (fun (x : String × String) => x.fst == sName1) with | some (_, sv) => sv | none => sName1)
            | .fake id => ws2.fakeSecrets[id]?.getD sName1
          let pColFn := fun (c : ColSpec) => if c.name == col then { c with ty := .text, tags := (c.tags.remove "pii").union pc, bucketed := false, aggKind := .raw } else { c with aggKind := .raw }
          have hpRel : ∀ {rs1 rs2 o1 o2 : List TableRow},
              RelList (RowEquiv L tt.cols) rs1 rs2 →
              mapPseudonymizeRows keyMat cIdx rs1 = some o1 →
              mapPseudonymizeRows keyMat cIdx rs2 = some o2 →
              RelList (RowEquiv L (tt.cols.map pColFn)) o1 o2 := by
            intro rs1 rs2 o1 o2 hrel ho1 ho2
            induction hrel generalizing o1 o2 with
            | nil => injection ho1 with e1; injection ho2 with e2; subst e1; subst e2; exact .nil
            | @cons r1 r2 _ _ hr htl ih =>
              unfold mapPseudonymizeRows at ho1 ho2; simp only [bind, Option.bind] at ho1 ho2
              cases hg1 : r1.cells[cIdx]? <;> rw [hg1] at ho1 <;> try contradiction
              cases hg2 : r2.cells[cIdx]? <;> rw [hg2] at ho2 <;> try contradiction
              dsimp only at ho1 ho2
              cases ht1 : mapPseudonymizeRows keyMat cIdx _ <;> rw [ht1] at ho1 <;> try contradiction
              cases ht2 : mapPseudonymizeRows keyMat cIdx _ <;> rw [ht2] at ho2 <;> try contradiction
              injection ho1 with e1; injection ho2 with e2; subst e1; subst e2
              refine .cons ?_ (ih ht1 ht2)
              apply cellsEquiv_set_at pColFn cIdx hr
              intro i c hi
              refine ⟨fun heq hsub => ?_, fun hne hsub => ?_⟩
              · subst heq; rw [hcGet] at hi; injection hi with ec; subst ec
                dsimp only [pColFn] at hsub; simp only [hcnEq, beq_self_eq_true, ↓reduceIte, TagSet.union_subset_iff, Bool.and_eq_true] at hsub
                have hcOrigLow : targetCol.tags.subset L = true := by
                  rw [TagSet.subset_iff]; intro t htMem
                  by_cases htPii : t = "pii"
                  · subst htPii; exact hpiiL
                  · exact (TagSet.subset_iff _ _).mp hsub.1 t (by simp [htMem, htPii])
                have hcellEq := hr.getElem?_eq hcGet hcOrigLow
                rw [hg1, hg2] at hcellEq; injection hcellEq with ev; subst ev; rfl
              · have hneName : (c.name == col) = false := by
                  cases hb : (c.name == col); rfl
                  exact absurd (distinctIdents_idx_unique huniqIn hi hcGet ((beq_iff_eq.mp hb).trans hcnEq.symm)) hne
                dsimp only [pColFn] at hsub; rw [hneName] at hsub; exact hsub
          have hcolsMapEq : (tt.cols.map (fun c => if c.name == col then { c with ty := .text, tags := (targetCol.tags.remove "pii").union pc, bucketed := false, aggKind := .raw } else { c with aggKind := .raw })) =
              tt.cols.map pColFn := by
            apply List.map_congr_left; intro c hc
            cases hb : (c.name == col)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte, pColFn]
            · have hfEq := find_unique_of_mem huniqIn hc
              unfold TableTy.findCol? at htc
              rw [beq_iff_eq.mp hb, htc] at hfEq; injection hfEq with ec; subst ec
              simp only [hb, ↓reduceIte, pColFn]
          rw [hcolsMapEq]
          have hlr := ht.lowRows hrLow
          cases hord : tt.orderTags.subset L <;> simp only [hord, Bool.false_eq_true, ↓reduceIte] at hlr ⊢
          · rcases hlr with ⟨rows1', hpIn, hrelIn⟩
            have hwf1' : ∀ r ∈ rows1', CellsWf prog r.cells tt.cols := fun r h => hrWfIn1.to_forall r (hpIn.symm.subset h)
            have hsome1' : ∃ out1', mapPseudonymizeRows keyMat cIdx rows1' = some out1' := by
              clear hm1 hm2 hrelIn hpIn
              induction rows1' with
              | nil => exact ⟨[], rfl⟩
              | cons r rs ih =>
                rcases (hwf1' r (.head _)).getElem?_wf hcGet with ⟨v, hg, _⟩
                rcases ih (fun x hx => hwf1' x (.tail _ hx)) with ⟨tl, htl⟩
                exact ⟨{ cells := r.cells.set cIdx (Val.text (pseudonymizeToken keyMat v)) } :: tl,
                  by unfold mapPseudonymizeRows; simp [hg, htl]⟩
            rcases hsome1' with ⟨out1', hm1'⟩
            rw [mapPseudonymizeRows_eq_filterMap keyMat cIdx hm1]
            exact ⟨out1', (mapPseudonymizeRows_eq_filterMap keyMat cIdx hm1') ▸ perm_filterMap _ hpIn, hpRel hrelIn hm1' hm2⟩
          · exact hpRel hlr hm1 hm2

theorem eval_ni_all (prog : Program) (L : TagSet) :
    ∀ (fuel : Nat), ExprNIAt fuel prog L ∧ JoinLoopNIAt fuel prog L ∧ PlanNIAt fuel prog L
  | 0 =>
    ⟨by unfold ExprNIAt; intros; unfold eval at *; contradiction,
     by unfold JoinLoopNIAt; intros; unfold evalJoinLoop at *; contradiction,
     by unfold PlanNIAt; intros; unfold evalPlan at *; contradiction⟩
  | fuel' + 1 => by
    rcases eval_ni_all prog L fuel' with ⟨ihE, ihJL, ihP⟩
    exact ⟨expr_ni_step ihE ihJL ihP, joinLoop_ni_step ihE ihJL, plan_ni_step ihE ihP⟩


/-! ## Part 4B.6: Top-Level Entry Equivalence & Theorem 2 (Non-Interference & Redaction) -/

theorem mkEntryEnv_equiv (prog : Program) (L : TagSet) :
    ∀ (params : List (Ident × LTy)),
      (∀ p ∈ params, isCapabilityTy p.2.ty = true ∧ ltySinksAllowed L p.2 = true) →
      ∃ initEnv,
        mkEntryEnv prog params = some initEnv ∧
        EnvEquiv prog L initEnv initEnv ∧
        envToTyEnv initEnv = params ∧
        (∀ w, envClosureSafe prog L w initEnv)
  | [], _ => ⟨[], rfl, .nil, rfl, fun _ => trivial⟩
  | (pName, pLTy) :: rest, hall => by
    rcases hall (pName, pLTy) (.head _) with ⟨hcap, hsink⟩
    have hbuild : ∃ cv,
        buildEntryCapVal prog pLTy.ty = some cv ∧
        ValWf prog cv pLTy.ty ∧
        valSafeForNI L cv = true ∧
        ValPayloadEquiv prog L cv cv pLTy.ty ∧
        (∀ w, valClosureSafe prog L w cv) := by
      cases hty : pLTy.ty <;> rw [hty] at hcap <;> try simp [isCapabilityTy] at hcap
      · exact ⟨_, rfl, .capArgs, rfl, .capArgs, fun _ => trivial⟩
      · exact ⟨_, rfl, .capClock, rfl, .capClock, fun _ => trivial⟩
      · exact ⟨_, rfl, .capConsole .real _, rfl, .capConsole .real _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capReadFiles .real, rfl, .capReadFiles .real, fun _ => trivial⟩
      · exact ⟨_, rfl, .capWriteFiles .real _ _, rfl, .capWriteFiles .real _ _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capReadDB .real _, rfl, .capReadDB .real _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capWriteTable .real _ _ _ _ _, rfl, .capWriteTable .real _ _ _ _ _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capRawReadDB _, rfl, .capRawReadDB _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capHttpsAllow .real _ _, rfl, .capHttpsAllow .real _ _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capSecret .real _, rfl, .capSecret .real _, fun _ => trivial⟩
      · exact ⟨_, rfl, .capDeclassify _, rfl, .capDeclassify _, fun _ => trivial⟩
    rcases hbuild with ⟨cv, hcvEq, hcvWf, hcvSafe, hcvPay, hcvCl⟩
    rcases mkEntryEnv_equiv prog L rest (fun q hq => hall q (.tail _ hq)) with
      ⟨tlEnv, htlEq, htlEquiv, htlTy, htlCl⟩
    refine ⟨{ name := pName, lty := pLTy, val := cv } :: tlEnv,
      by simp [mkEntryEnv, hcvEq, htlEq],
      .cons hsink (ValEquiv.mk_smart hcvWf hcvWf hcvSafe hcvSafe (fun _ => hcvPay)) htlEquiv,
      congrArg ((pName, pLTy) :: ·) htlTy,
      fun w => ⟨hcvCl w, htlCl w⟩⟩

/-- **Theorem 2A (Expression Termination- and Error-Insensitive Non-Interference — TEINI):**
    For any well-typed Dana Core IR program (`checkProgram prog = .ok ()`) and observer
    clearance `L` (`progSafeForNI prog L = true`), whenever evaluating a well-typed
    `L`-safe expression `e` from `L`-equivalent environments and `World`s terminates
    normally (`.ok`) on both runs, it produces `L`-equivalent result values,
    `L`-equivalent post-worlds, and identical observable `ExecReport`s. -/
theorem theorem2_expr_noninterference_ok {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {env1 env2 : Env} {w1 w2 w1' w2' : World} {e : Expr} {lty : LTy} {v1 v2 : Val}
    (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (hw : WorldEquiv prog L w1 w2)
    (hpDB1 : progRespectsDB w1 prog)
    (hpDB2 : progRespectsDB w2 prog)
    (henvCl1 : envClosureSafe prog L w1 env1)
    (henvCl2 : envClosureSafe prog L w2 env2)
    (hesafe : exprSafeForNI L e = true)
    (hens : exprNoSpecCalls prog e = true)
    (hesup : exprSuppressSafe prog L (envToTyEnv env1) pc e = true)
    (her1 : exprRespectsDB w1 e)
    (her2 : exprRespectsDB w2 e)
    (hchk : checkExpr prog (envToTyEnv env1) [] pc inSpec e = .ok lty)
    (hev1 : eval fuel prog env1 pc w1 e = .ok v1 w1')
    (hev2 : eval fuel prog env2 pc w2 e = .ok v2 w2') :
    ValEquiv prog L v1 v2 lty ∧
    WorldEquiv prog L w1' w2' ∧
    extractReport (.ok v1 w1') = extractReport (.ok v2 w2') := by
  have h := (eval_ni_all prog L fuel).1 hprog hsafeProg env1 env2 [] pc inSpec w1 w2 e lty
    henv rfl (fun _ hm => nomatch hm) hw hpDB1 hpDB2 henvCl1 henvCl2 hesafe hens hesup her1 her2 hchk
    (by rw [hev1]; trivial) (by rw [hev2]; trivial)
  rw [hev1, hev2] at h
  exact ⟨h.2, h.1, h.1.extractReport_ok_eq⟩

/-- **Theorem 2B (Relational Plan TEINI):**
    Every well-typed `L`-safe relational `Plan` maps `L`-equivalent environments and
    worlds (including arbitrary high-column variations, high `row_tags` variations, and
    high `order_tags` row permutations) to `L`-equivalent output tables (`TableEquiv` /
    `DynamicTable`) and `L`-equivalent post-worlds whenever both runs complete normally
    (`.ok`). -/
theorem theorem2_plan_noninterference_ok {prog : Program} {L pc : TagSet} {inSpec : Bool}
    {env1 env2 : Env} {w1 w2 w1' w2' : World} {plan : Plan} {pTy : PlanTy} {v1 v2 : Val}
    (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (henv : EnvEquiv prog L env1 env2)
    (hw : WorldEquiv prog L w1 w2)
    (hpDB1 : progRespectsDB w1 prog)
    (hpDB2 : progRespectsDB w2 prog)
    (henvCl1 : envClosureSafe prog L w1 env1)
    (henvCl2 : envClosureSafe prog L w2 env2)
    (hpsafe : planSafeForNI L plan = true)
    (hpns : planNoSpecCalls prog plan = true)
    (hpsup : planSuppressSafe prog L (envToTyEnv env1) pc plan = true)
    (hpr1 : planRespectsDB w1 plan)
    (hpr2 : planRespectsDB w2 plan)
    (hchk : checkPlan prog (envToTyEnv env1) pc inSpec plan = .ok pTy)
    (hev1 : evalPlan fuel prog env1 pc w1 plan = .ok v1 w1')
    (hev2 : evalPlan fuel prog env2 pc w2 plan = .ok v2 w2') :
    ValEquiv prog L v1 v2 (pTy.toLTy pc) ∧
    WorldEquiv prog L w1' w2' ∧
    extractReport (.ok v1 w1') = extractReport (.ok v2 w2') := by
  rcases (eval_ni_all prog L fuel).2.2 hprog hsafeProg env1 env2 pc inSpec w1 w2 plan pTy v1 v2 w1' w2'
    henv hw hpDB1 hpDB2 henvCl1 henvCl2 hpsafe hpns hpsup hpr1 hpr2 hchk hev1 hev2 with ⟨hv, hw'⟩
  exact ⟨hv, hw', hw'.extractReport_ok_eq⟩

/-- **Theorem 2C (Whole-Program Termination- and Error-Insensitive Non-Interference — TEINI):**
    For any well-typed Dana Core IR program (`checkProgram prog = .ok ()`) and observer
    clearance `L` (`progSafeForNI prog L = true`), running `prog` on any two `L`-equivalent
    initial worlds (`WorldEquiv prog L w1 w2`) that both complete normally (`status = .ok`)
    produces byte-for-byte identical observable `ExecReport`s (`rep1 = rep2`).
    Termination and error channels (`ok` vs. runtime trap such as `divByZero` or
    `joinCardinality`) are outside this theorem's scope (TEINI). -/
theorem theorem2_program_noninterference_ok {prog : Program} {L : TagSet}
    {w1 w2 : World} {rep1 rep2 : ExecReport} (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog L = true)
    (hw : WorldEquiv prog L w1 w2)
    (hpDB1 : progRespectsDB w1 prog)
    (hpDB2 : progRespectsDB w2 prog)
    (hrun1 : runProgram fuel prog w1 = .ok rep1)
    (hrun2 : runProgram fuel prog w2 = .ok rep2)
    (hok1 : rep1.status = .ok)
    (hok2 : rep2.status = .ok) :
    rep1 = rep2 := by
  have hprogSave := hprog
  have hsafeSave := hsafeProg
  unfold runProgram at hrun1 hrun2
  simp only [hprogSave, bind, Except.bind] at hrun1 hrun2
  cases hent : prog.entry with
  | none =>
    rw [hent] at hrun1 hrun2
    dsimp only at hrun1 hrun2
    rw [hw.extractReport_ok_eq (v1 := .unit) (v2 := .unit)] at hrun1
    cases h1 : extractReport (.ok .unit w2) <;> rw [h1] at hrun1 hrun2 <;> try contradiction
    injection hrun1 with e1; injection hrun2 with e2; exact e1.symm.trans e2
  | some mainName =>
    rw [hent] at hrun1 hrun2; dsimp only at hrun1 hrun2
    simp only [checkProgram, bind, Except.bind] at hprog
    split at hprog <;> try contradiction
    split at hprog <;> try contradiction
    cases hp : checkPolicyWf prog <;> simp only [hp] at hprog <;> try contradiction
    cases hd : checkDataDecls prog <;> simp only [hd] at hprog <;> try contradiction
    cases hs : checkSchemaDecls prog <;> simp only [hs] at hprog <;> try contradiction
    cases hc : checkConstDecls prog <;> simp only [hc] at hprog <;> try contradiction
    split at hprog <;> try contradiction
    cases hf : checkFunDecls prog prog.funs <;> simp only [hf] at hprog <;> try contradiction
    rw [hent] at hprog; dsimp only at hprog
    cases hfind : prog.findFun? mainName with
    | none => rw [hfind] at hprog; simp at hprog
    | some mainFn =>
      rw [hfind] at hprog hrun1 hrun2; dsimp only at hprog hrun1 hrun2
      split at hprog <;> try contradiction
      rename_i hnotSpecRaw
      have hnotSpec : mainFn.kind.isSpec = false := Bool.eq_false_iff.mpr hnotSpecRaw
      split at hprog <;> try contradiction
      rename_i hpcNotNonEmpty
      split at hprog <;> try contradiction
      rename_i hcapParams
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true] at hpcNotNonEmpty hcapParams
      have hfnMem := List.mem_of_find?_eq_some hfind
      simp only [progSafeForNI, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hsafeProg
      have hmainSafe : ltyListSinksAllowed L (mainFn.params.map Prod.snd) = true ∧
          exprSafeForNI L mainFn.body = true ∧
          exprSuppressSafe prog L mainFn.params.reverse mainFn.pc mainFn.body = true := by
        rcases hsafeProg.2 mainFn hfnMem with hsp | hm
        · rw [hnotSpec] at hsp; nomatch hsp
        · exact ⟨hm.1.1.1, hm.1.2, hm.2⟩
      rcases hmainSafe with ⟨hpSinks, hbodySafe, hbodySup⟩
      rw [ltyListSinksAllowed_iff] at hpSinks
      have hrevProps : ∀ p ∈ mainFn.params.reverse, isCapabilityTy p.2.ty = true ∧ ltySinksAllowed L p.2 = true :=
        fun p hp =>
          have hpOrig := List.mem_reverse.mp hp
          ⟨(hcapParams p hpOrig).1, hpSinks p.2 (List.mem_map_of_mem hpOrig)⟩
      rcases mkEntryEnv_equiv prog L mainFn.params.reverse hrevProps with
        ⟨initEnv, hmkEq, hinitEquiv, hinitTy, hinitCl⟩
      rw [hmkEq] at hrun1 hrun2; dsimp only at hrun1 hrun2
      cases hg1 : checkEntryExportGate mainFn.params w1 with
      | some bug1 =>
        rw [hg1] at hrun1; dsimp only [extractReport] at hrun1
        injection hrun1 with e1; subst e1; nomatch hok1
      | none =>
      cases hg2 : checkEntryExportGate mainFn.params w2 with
      | some bug2 =>
        rw [hg2] at hrun2; dsimp only [extractReport] at hrun2
        injection hrun2 with e2; subst e2; nomatch hok2
      | none =>
      rw [hg1] at hrun1; rw [hg2] at hrun2; dsimp only at hrun1 hrun2
      rcases checkFunDecl_valid hprogSave hfind with ⟨bodyLTy, hbodyChk, _⟩
      have hbodyNs : exprNoSpecCalls prog mainFn.body = true :=
        checkExpr_noSpecCalls (hnotSpec ▸ hbodyChk)
      have hpcEmpty : mainFn.pc = TagSet.empty := by
        cases hpcMk : mainFn.pc with | mk elems inv =>
        simp only [TagSet.isEmpty, hpcMk, List.isEmpty_iff] at hpcNotNonEmpty
        subst hpcNotNonEmpty; rfl
      rw [hpcEmpty, ← hinitTy] at hbodyChk hbodySup
      cases ho1 : eval fuel prog initEnv TagSet.empty w1 mainFn.body with
      | outOfFuel | wrong | jumped _ _ _ => rw [ho1] at hrun1; contradiction
      | stopped _ _ =>
        rw [ho1] at hrun1; dsimp only [extractReport] at hrun1
        injection hrun1 with e1; subst e1; nomatch hok1
      | failed _ _ =>
        rw [ho1] at hrun1; dsimp only [extractReport] at hrun1
        injection hrun1 with e1; subst e1; nomatch hok1
      | ok v1 w1' =>
        cases ho2 : eval fuel prog initEnv TagSet.empty w2 mainFn.body with
        | outOfFuel | wrong | jumped _ _ _ => rw [ho2] at hrun2; contradiction
        | stopped _ _ =>
          rw [ho2] at hrun2; dsimp only [extractReport] at hrun2
          injection hrun2 with e2; subst e2; nomatch hok2
        | failed _ _ =>
          rw [ho2] at hrun2; dsimp only [extractReport] at hrun2
          injection hrun2 with e2; subst e2; nomatch hok2
        | ok v2 w2' =>
          rw [ho1] at hrun1; rw [ho2] at hrun2
          rcases theorem2_expr_noninterference_ok fuel hprogSave hsafeSave hinitEquiv hw hpDB1 hpDB2
            (hinitCl w1) (hinitCl w2) hbodySafe hbodyNs hbodySup
            (hpDB1 mainFn hfnMem hnotSpec) (hpDB2 mainFn hfnMem hnotSpec)
            hbodyChk ho1 ho2 with ⟨_, _, hrepEq⟩
          rw [hrepEq] at hrun1
          dsimp only [extractReport] at hrun1 hrun2
          injection hrun1 with e1; injection hrun2 with e2
          exact e1.symm.trans e2

/-- **Theorem 2D (Public-Observer TEINI — PII / FERPA / HIPAA / Secret Protection):**
    Specialization of Theorem 2C to `L = TagSet.empty`: for any well-typed program whose
    reachable non-spec sinks allow only public (`[]`) data and which performs no
    declassification of tags outside `[]`, arbitrary changes to any sensitive column,
    sensitive row presence (`row_tags ≠ []`), sensitive sort order (`order_tags ≠ []`),
    or secret key material never leak into any observable `ExecReport` channel (`stdout`,
    `stderr`, `writtenFiles`, `writtenTables`, `fakeConsoles`, `fakeFiles`) on any two
    normally terminating (`status = .ok`) executions. -/
theorem theorem2_public_noninterference {prog : Program}
    {w1 w2 : World} {rep1 rep2 : ExecReport} (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog TagSet.empty = true)
    (hw : WorldEquiv prog TagSet.empty w1 w2)
    (hpDB1 : progRespectsDB w1 prog)
    (hpDB2 : progRespectsDB w2 prog)
    (hrun1 : runProgram fuel prog w1 = .ok rep1)
    (hrun2 : runProgram fuel prog w2 = .ok rep2)
    (hok1 : rep1.status = .ok)
    (hok2 : rep2.status = .ok) :
    rep1 = rep2 :=
  theorem2_program_noninterference_ok fuel hprog hsafeProg hw hpDB1 hpDB2 hrun1 hrun2 hok1 hok2

private theorem tagSet_eq_empty_of_isEmpty {ts : TagSet} (h : ts.isEmpty = true) :
    ts = TagSet.empty := by
  cases ts with | mk elems inv =>
  simp only [TagSet.isEmpty, List.isEmpty_iff] at h
  subst h; rfl

/-- **Theorem 2E (Automatic Sensitive Diagnostic Redaction on Explicit `Stop` Nodes):**
    Whenever an explicit `.stop kind (some dExpr)` executes from publicly equivalent states
    (`L = TagSet.empty`) and its detail expression `dExpr` evaluates normally on both runs,
    regardless of whether `dExpr` or `pc` is public or carries sensitive tags (`pii`,
    `ferpa`, `secret`, etc.), both executions stop with the **exact same `Bug`** (redacting
    sensitive payloads to `[REDACTED:...]` without inspecting `dVal`), preserve
    `WorldEquiv`, and emit identical `ExecReport`s. -/
theorem theorem2_redacted_stop_noninterference {prog : Program} {pc : TagSet} {inSpec : Bool}
    {jenv : JoinEnv} {env1 env2 : Env} {w1 w2 w1' w2' : World}
    {kind : BugKind} {dExpr : Expr} {lty : LTy} {dVal1 dVal2 : Val}
    (fuel : Nat)
    (hprog : checkProgram prog = .ok ())
    (hsafeProg : progSafeForNI prog TagSet.empty = true)
    (henv : EnvEquiv prog TagSet.empty env1 env2)
    (hw : WorldEquiv prog TagSet.empty w1 w2)
    (hpDB1 : progRespectsDB w1 prog)
    (hpDB2 : progRespectsDB w2 prog)
    (henvCl1 : envClosureSafe prog TagSet.empty w1 env1)
    (henvCl2 : envClosureSafe prog TagSet.empty w2 env2)
    (hesafe : exprSafeForNI TagSet.empty (.stop kind (some dExpr)) = true)
    (hens : exprNoSpecCalls prog (.stop kind (some dExpr)) = true)
    (hesup : exprSuppressSafe prog TagSet.empty (envToTyEnv env1) pc (.stop kind (some dExpr)) = true)
    (her1 : exprRespectsDB w1 dExpr)
    (her2 : exprRespectsDB w2 dExpr)
    (hchk : checkExpr prog (envToTyEnv env1) jenv pc inSpec (.stop kind (some dExpr)) = .ok lty)
    (hevD1 : eval fuel prog env1 pc w1 dExpr = .ok dVal1 w1')
    (hevD2 : eval fuel prog env2 pc w2 dExpr = .ok dVal2 w2') :
    ∃ b : Bug,
      eval (fuel + 1) prog env1 pc w1 (.stop kind (some dExpr)) = .stopped b w1' ∧
      eval (fuel + 1) prog env2 pc w2 (.stop kind (some dExpr)) = .stopped b w2' ∧
      WorldEquiv prog TagSet.empty w1' w2' ∧
      extractReport (eval (fuel + 1) prog env1 pc w1 (.stop kind (some dExpr))) =
        extractReport (eval (fuel + 1) prog env2 pc w2 (.stop kind (some dExpr))) := by
  have hd : progDatasSortableForNI prog TagSet.empty = true := by
    simp only [progSafeForNI, Bool.and_eq_true] at hsafeProg; exact hsafeProg.1.1.1
  have hdSafe : exprSafeForNI TagSet.empty dExpr = true := hesafe
  have hdNs : exprNoSpecCalls prog dExpr = true := hens
  have hdSup : exprSuppressSafe prog TagSet.empty (envToTyEnv env1) pc dExpr = true := hesup
  unfold checkExpr at hchk; dsimp only at hchk
  split at hchk <;> try contradiction
  simp only [bind, Except.bind] at hchk
  cases hdChk1 : checkExpr prog (envToTyEnv env1) [] pc inSpec dExpr <;> rw [hdChk1] at hchk <;> try contradiction
  rename_i dLTy; dsimp only at hchk
  split at hchk <;> try contradiction
  rename_i hdEquat
  have hdChk2 : checkExpr prog (envToTyEnv env2) [] pc inSpec dExpr = .ok dLTy :=
    henv.envToTyEnv_eq ▸ hdChk1
  have hdTrue1 : checkExpr prog (envToTyEnv env1) [] pc true dExpr = .ok dLTy :=
    checkExpr_inSpec_true hdChk1
  have hdTrue2 : checkExpr prog (envToTyEnv env2) [] pc true dExpr = .ok dLTy :=
    checkExpr_inSpec_true hdChk2
  have hboth : WorldEquiv prog TagSet.empty w1' w2' ∧
      formatDiagDetail (dLTy.effectiveTags.union pc) dVal1 =
        formatDiagDetail (dLTy.effectiveTags.union pc) dVal2 := by
    cases hpc : pc.subset TagSet.empty
    · rcases (eval_safe_and_confined_all prog TagSet.empty fuel).1 hprog hsafeProg env1 [] pc inSpec w1 dExpr dLTy
        henv.wf_left henv.safe_left (envClosureSafe_imp_noSpecCalls henvCl1) rfl hw.wf1 hdSafe hdNs hdChk1 with ⟨_, _, hc1⟩
      rcases (eval_safe_and_confined_all prog TagSet.empty fuel).1 hprog hsafeProg env2 [] pc inSpec w2 dExpr dLTy
        henv.wf_right henv.safe_right (envClosureSafe_imp_noSpecCalls henvCl2) rfl hw.wf2 hdSafe hdNs hdChk2 with ⟨_, _, hc2⟩
      have hw1Eq : w1' = w1 := by have h := hc1 hpc; rw [hevD1] at h; exact h
      have hw2Eq : w2' = w2 := by have h := hc2 hpc; rw [hevD2] at h; exact h
      subst hw1Eq; subst hw2Eq
      have hne : (dLTy.effectiveTags.union pc).isEmpty = false := by
        cases he : (dLTy.effectiveTags.union pc).isEmpty; rfl
        have hsub : (dLTy.effectiveTags.union pc).subset TagSet.empty = true := by
          rw [tagSet_eq_empty_of_isEmpty he]; exact TagSet.empty_subset _
        rw [TagSet.union_subset_iff, Bool.and_eq_true] at hsub
        rw [hsub.2] at hpc; nomatch hpc
      exact ⟨hw, formatDiagDetail_redacted hne dVal1 dVal2⟩
    · rcases theorem2_expr_noninterference_ok fuel hprog hsafeProg henv hw hpDB1 hpDB2
        henvCl1 henvCl2 hdSafe hdNs hdSup her1 her2 hdChk1 hevD1 hevD2 with ⟨hdValEq, hw', _⟩
      refine ⟨hw', ?_⟩
      cases hemp : (dLTy.effectiveTags.union pc).isEmpty
      · exact formatDiagDetail_redacted hemp dVal1 dVal2
      · have hsub : (dLTy.effectiveTags.union pc).subset TagSet.empty = true := by
          rw [tagSet_eq_empty_of_isEmpty hemp]; exact TagSet.empty_subset _
        rw [TagSet.union_subset_iff, Bool.and_eq_true] at hsub
        simp only [formatDiagDetail, hemp, ↓reduceIte]
        exact hdValEq.effectiveTags_renderPublicVal hd hdEquat hsub.1
  rcases hboth with ⟨hw', hfmt⟩
  let b : Bug := {
    kind := kind
    message := reprStr kind ++ ": " ++ formatDiagDetail (dLTy.effectiveTags.union pc) dVal2
  }
  have hs1 : eval (fuel + 1) prog env1 pc w1 (.stop kind (some dExpr)) = .stopped b w1' := by
    unfold eval; dsimp only; rw [hdTrue1]; dsimp only; rw [hevD1]; dsimp only; rw [hfmt]
  have hs2 : eval (fuel + 1) prog env2 pc w2 (.stop kind (some dExpr)) = .stopped b w2' := by
    unfold eval; dsimp only; rw [hdTrue2]; dsimp only; rw [hevD2]
  exact ⟨b, hs1, hs2, hw', by rw [hs1, hs2]; exact hw'.extractReport_stopped_eq rfl⟩

end DanaCore



