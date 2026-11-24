/-
  DanaCore/Syntax.lean
  Dana Core IR v0.1 — Sensitivity algebra, types, expressions, pure relational
  plans, policies, programs, and lossless compiler metadata.
-/

namespace DanaCore

abbrev Ident := String
abbrev Tag := String

/-- Built-in sensitivity tags available in every Dana program without declaration. -/
def builtInTags : List Tag :=
  ["pii", "ferpa", "financial", "health", "secret"]

/-! ## Strict Total Order on Strings / Tags -/

/-- Lexicographic strict order on `List Char` by Unicode scalar value. -/
def charListLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | c1 :: r1, c2 :: r2 =>
    if c1.toNat < c2.toNat then true
    else if c2.toNat < c1.toNat then false
    else charListLt r1 r2

theorem charListLt_irrefl : ∀ (l : List Char), charListLt l l = false
  | [] => rfl
  | c :: cs => by
    simp only [charListLt, Nat.lt_irrefl, ↓reduceIte]
    exact charListLt_irrefl cs

theorem charListLt_trans :
    ∀ {l1 l2 l3 : List Char},
      charListLt l1 l2 = true → charListLt l2 l3 = true → charListLt l1 l3 = true
  | [], [], _ :: _, h12, _ => by simp [charListLt] at h12
  | [], _ :: _, [], _, h23 => by simp [charListLt] at h23
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h12, _ => by simp [charListLt] at h12
  | _ :: _, _ :: _, [], _, h23 => by simp [charListLt] at h23
  | c1 :: r1, c2 :: r2, c3 :: r3, h12, h23 => by
    simp only [charListLt] at h12 h23 ⊢
    by_cases h1 : c1.toNat < c2.toNat
    · simp only [h1, ↓reduceIte] at h12
      by_cases h2 : c2.toNat < c3.toNat
      · have h13 : c1.toNat < c3.toNat := Nat.lt_trans h1 h2
        simp [h13]
      · by_cases h2' : c3.toNat < c2.toNat
        · simp [h2, h2'] at h23
        · have heq23 : c2.toNat = c3.toNat := by omega
          have h13 : c1.toNat < c3.toNat := by omega
          simp [h13]
    · by_cases h1' : c2.toNat < c1.toNat
      · simp [h1, h1'] at h12
      · have heq12 : c1.toNat = c2.toNat := by omega
        simp only [h1, h1', ↓reduceIte] at h12
        by_cases h2 : c2.toNat < c3.toNat
        · have h13 : c1.toNat < c3.toNat := by omega
          simp [h13]
        · by_cases h2' : c3.toNat < c2.toNat
          · simp [h2, h2'] at h23
          · have heq23 : c2.toNat = c3.toNat := by omega
            have hn13 : ¬ (c1.toNat < c3.toNat) := by omega
            have hn31 : ¬ (c3.toNat < c1.toNat) := by omega
            simp only [h2, h2', ↓reduceIte] at h23
            simp only [hn13, hn31, ↓reduceIte]
            exact charListLt_trans h12 h23

private theorem char_eq_of_toNat_eq {c1 c2 : Char} (h : c1.toNat = c2.toNat) : c1 = c2 := by
  have h1 := Char.ofNat_toNat c1
  have h2 := Char.ofNat_toNat c2
  rw [← h1, ← h2, h]

theorem charListLt_trichotomy :
    ∀ (l1 l2 : List Char),
      charListLt l1 l2 = true ∨ l1 = l2 ∨ charListLt l2 l1 = true
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl rfl
  | _ :: _, [] => Or.inr (Or.inr rfl)
  | c1 :: r1, c2 :: r2 => by
    simp only [charListLt]
    by_cases h1 : c1.toNat < c2.toNat
    · exact Or.inl (by simp [h1])
    · by_cases h2 : c2.toNat < c1.toNat
      · have hn1 : ¬ (c1.toNat < c2.toNat) := h1
        exact Or.inr (Or.inr (by simp [h2]))
      · have heq : c1.toNat = c2.toNat := by omega
        have hceq : c1 = c2 := char_eq_of_toNat_eq heq
        subst hceq
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rcases charListLt_trichotomy r1 r2 with hlt | rfl | hgt
        · exact Or.inl hlt
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hgt)

/-- Canonical strict total order on sensitivity tags. -/
def tagLt (a b : Tag) : Bool :=
  charListLt a.toList b.toList

theorem tagLt_irrefl (a : Tag) : tagLt a a = false :=
  charListLt_irrefl a.toList

theorem tagLt_trans {a b c : Tag} (h1 : tagLt a b = true) (h2 : tagLt b c = true) :
    tagLt a c = true :=
  charListLt_trans h1 h2

theorem tagLt_asymm {a b : Tag} (h : tagLt a b = true) : tagLt b a = false := by
  cases hba : tagLt b a with
  | false => rfl
  | true =>
    have haa := tagLt_trans h hba
    rw [tagLt_irrefl] at haa
    contradiction

theorem tagLt_ne {a b : Tag} (h : tagLt a b = true) : a ≠ b := by
  intro heq
  subst heq
  rw [tagLt_irrefl] at h
  contradiction

theorem tagLt_trichotomy (a b : Tag) :
    tagLt a b = true ∨ a = b ∨ tagLt b a = true := by
  rcases charListLt_trichotomy a.toList b.toList with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr (Or.inl (String.ext heq))
  · exact Or.inr (Or.inr hgt)

/-! ## Canonical Sorted Unique `TagSet` & Semilattice Laws -/

/-- Canonical bounded join-semilattice of sensitivity tags `(Set(Tag), ∅, ∪, ⊆)`
    represented as a strictly sorted, duplicate-free list. -/
structure TagSet where
  elems  : List Tag
  sorted : elems.Pairwise (fun a b => tagLt a b = true)
  deriving DecidableEq

instance : Repr TagSet where
  reprPrec s n := reprPrec s.elems n

def insertTagList (t : Tag) : List Tag → List Tag
  | [] => [t]
  | x :: xs =>
    if tagLt t x then t :: x :: xs
    else if tagLt x t then x :: insertTagList t xs
    else x :: xs

theorem mem_insertTagList (y t : Tag) :
    ∀ (xs : List Tag), y ∈ insertTagList t xs ↔ y = t ∨ y ∈ xs
  | [] => by simp [insertTagList]
  | x :: xs => by
    simp only [insertTagList]
    by_cases h1 : tagLt t x = true
    · simp [h1]
    · by_cases h2 : tagLt x t = true
      · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2, List.mem_cons, mem_insertTagList]
        constructor
        · rintro (rfl | rfl | hmem)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hmem)
        · rintro (rfl | rfl | hmem)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hmem)
      · have htx : t = x := by
          rcases tagLt_trichotomy t x with hlt | heq | hgt
          · exact absurd hlt h1
          · exact heq
          · exact absurd hgt h2
        subst htx
        simp only [tagLt_irrefl, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        constructor
        · rintro (rfl | hmem)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hmem)
        · rintro (rfl | rfl | hmem)
          · exact Or.inl rfl
          · exact Or.inl rfl
          · exact Or.inr hmem

theorem pairwise_insertTagList (t : Tag) :
    ∀ {xs : List Tag},
      xs.Pairwise (fun a b => tagLt a b = true) →
      (insertTagList t xs).Pairwise (fun a b => tagLt a b = true)
  | [], _ => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | x :: xs, List.Pairwise.cons hx hxs => by
    simp only [insertTagList]
    by_cases h1 : tagLt t x = true
    · simp only [h1, ↓reduceIte]
      apply List.Pairwise.cons
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy'
        · exact h1
        · exact tagLt_trans h1 (hx y hy')
      · exact List.Pairwise.cons hx hxs
    · by_cases h2 : tagLt x t = true
      · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2]
        apply List.Pairwise.cons
        · intro y hy
          rw [mem_insertTagList] at hy
          rcases hy with rfl | hy'
          · exact h2
          · exact hx y hy'
        · exact pairwise_insertTagList t hxs
      · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2]
        exact List.Pairwise.cons hx hxs

theorem sorted_unique_ext :
    ∀ {l1 l2 : List Tag},
      l1.Pairwise (fun a b => tagLt a b = true) →
      l2.Pairwise (fun a b => tagLt a b = true) →
      (∀ t, t ∈ l1 ↔ t ∈ l2) →
      l1 = l2
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, hmem => by
    have hy : y ∈ ([] : List Tag) := (hmem y).mpr (List.Mem.head _)
    nomatch hy
  | x :: _, [], _, _, hmem => by
    have hx : x ∈ ([] : List Tag) := (hmem x).mp (List.Mem.head _)
    nomatch hx
  | x :: xs, y :: ys, List.Pairwise.cons hx hxs, List.Pairwise.cons hy hys, hmem => by
    have hx_in : x ∈ y :: ys := (hmem x).mp (List.Mem.head _)
    have hy_in : y ∈ x :: xs := (hmem y).mpr (List.Mem.head _)
    simp only [List.mem_cons] at hx_in hy_in
    have hxy : x = y := by
      rcases hx_in with rfl | hx_ys
      · rfl
      · rcases hy_in with rfl | hy_xs
        · rfl
        · exfalso
          have h1 := hy x hx_ys
          have h2 := hx y hy_xs
          have h3 := tagLt_trans h1 h2
          rw [tagLt_irrefl] at h3
          contradiction
    subst hxy
    congr 1
    apply sorted_unique_ext hxs hys
    intro t
    constructor
    · intro htxs
      have hne : t ≠ x := (tagLt_ne (hx t htxs)).symm
      have ht2 : t ∈ x :: ys := (hmem t).mp (List.Mem.tail _ htxs)
      simp only [List.mem_cons] at ht2
      rcases ht2 with rfl | htys
      · exact absurd rfl hne
      · exact htys
    · intro htys
      have hne : t ≠ x := (tagLt_ne (hy t htys)).symm
      have ht1 : t ∈ x :: xs := (hmem t).mpr (List.Mem.tail _ htys)
      simp only [List.mem_cons] at ht1
      rcases ht1 with rfl | htxs
      · exact absurd rfl hne
      · exact htxs

namespace TagSet

def empty : TagSet := ⟨[], List.Pairwise.nil⟩

instance : Inhabited TagSet := ⟨empty⟩

def isEmpty (s : TagSet) : Bool := s.elems.isEmpty

def mem (t : Tag) (s : TagSet) : Bool := decide (t ∈ s.elems)

def insert (t : Tag) (s : TagSet) : TagSet :=
  ⟨insertTagList t s.elems, pairwise_insertTagList t s.sorted⟩

def singleton (t : Tag) : TagSet := insert t empty

def ofList (ts : List Tag) : TagSet :=
  ts.foldr insert empty

def union (s1 s2 : TagSet) : TagSet :=
  s1.elems.foldr insert s2

def filterTags (p : Tag → Bool) (s : TagSet) : TagSet :=
  ⟨s.elems.filter p, s.sorted.filter p⟩

def remove (t : Tag) (s : TagSet) : TagSet :=
  s.filterTags (fun x => decide (x ≠ t))

def diff (s1 s2 : TagSet) : TagSet :=
  s1.filterTags (fun x => !s2.mem x)

def inter (s1 s2 : TagSet) : TagSet :=
  s1.filterTags (fun x => s2.mem x)

def subset (s1 s2 : TagSet) : Bool :=
  s1.elems.all (fun x => s2.mem x)

theorem mem_iff (t : Tag) (s : TagSet) : s.mem t = true ↔ t ∈ s.elems :=
  decide_eq_true_iff

theorem ext {s1 s2 : TagSet} (h : ∀ t, s1.mem t = s2.mem t) : s1 = s2 := by
  cases s1 with
  | mk e1 p1 =>
    cases s2 with
    | mk e2 p2 =>
      congr 1
      apply sorted_unique_ext p1 p2
      intro t
      rw [← mem_iff t ⟨e1, p1⟩, ← mem_iff t ⟨e2, p2⟩, h t]

theorem ext_iff {s1 s2 : TagSet} : s1 = s2 ↔ ∀ t, s1.mem t = s2.mem t :=
  ⟨fun h _ => h ▸ rfl, ext⟩

@[simp] theorem mem_empty (t : Tag) : empty.mem t = false := rfl

theorem isEmpty_iff (s : TagSet) : s.isEmpty = true ↔ s = empty := by
  cases s with
  | mk elems sorted =>
    cases elems with
    | nil => simp [isEmpty, empty]
    | cons x xs =>
      simp only [isEmpty, List.isEmpty, Bool.false_eq_true, false_iff]
      intro h
      injection h with he
      contradiction

@[simp] theorem mem_insert (y t : Tag) (s : TagSet) :
    (s.insert t).mem y = (decide (y = t) || s.mem y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [mem_iff, insert, mem_insertTagList, Bool.or_eq_true, decide_eq_true_eq]

@[simp] theorem mem_singleton (y t : Tag) :
    (singleton t).mem y = decide (y = t) := by
  simp [singleton]

theorem mem_ofList (y : Tag) : ∀ (ts : List Tag), (ofList ts).mem y = decide (y ∈ ts)
  | [] => rfl
  | t :: ts => by
    change (insert t (ofList ts)).mem y = decide (y ∈ t :: ts)
    rw [mem_insert, mem_ofList y ts]
    by_cases h : y = t <;> simp [h]

@[simp] theorem mem_union (t : Tag) (s1 s2 : TagSet) :
    (s1.union s2).mem t = (s1.mem t || s2.mem t) := by
  unfold union
  have aux : ∀ (xs : List Tag), (xs.foldr insert s2).mem t = (decide (t ∈ xs) || s2.mem t) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x rest ih =>
      simp only [List.foldr_cons, mem_insert, ih, List.mem_cons]
      by_cases h : t = x <;> simp [h]
  rw [aux]
  rfl

@[simp] theorem mem_filterTags (p : Tag → Bool) (t : Tag) (s : TagSet) :
    (s.filterTags p).mem t = (s.mem t && p t) := by
  apply Bool.eq_iff_iff.mpr
  simp [mem_iff, filterTags, List.mem_filter]

@[simp] theorem mem_remove (y t : Tag) (s : TagSet) :
    (s.remove t).mem y = (s.mem y && decide (y ≠ t)) := by
  simp [remove]

@[simp] theorem mem_diff (t : Tag) (s1 s2 : TagSet) :
    (s1.diff s2).mem t = (s1.mem t && !s2.mem t) := by
  simp [diff]

@[simp] theorem mem_inter (t : Tag) (s1 s2 : TagSet) :
    (s1.inter s2).mem t = (s1.mem t && s2.mem t) := by
  simp [inter]

theorem subset_iff (s1 s2 : TagSet) :
    s1.subset s2 = true ↔ ∀ t, s1.mem t = true → s2.mem t = true := by
  unfold subset
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    exact h t ((mem_iff t s1).mp ht)
  · intro h t ht
    exact h t ((mem_iff t s1).mpr ht)

@[simp] theorem subset_refl (s : TagSet) : s.subset s = true :=
  (subset_iff s s).mpr (fun _ h => h)

@[simp] theorem empty_subset (s : TagSet) : empty.subset s = true :=
  (subset_iff empty s).mpr (fun _ h => by simp at h)

theorem subset_trans {a b c : TagSet} (h1 : a.subset b = true) (h2 : b.subset c = true) :
    a.subset c = true :=
  (subset_iff a c).mpr fun t ht =>
    (subset_iff b c).mp h2 t ((subset_iff a b).mp h1 t ht)

theorem subset_antisymm {a b : TagSet} (h1 : a.subset b = true) (h2 : b.subset a = true) :
    a = b := by
  apply ext
  intro t
  apply Bool.eq_iff_iff.mpr
  exact ⟨(subset_iff a b).mp h1 t, (subset_iff b a).mp h2 t⟩

@[simp] theorem union_comm (a b : TagSet) : a.union b = b.union a := by
  apply ext; intro t; simp [Bool.or_comm]

@[simp] theorem union_assoc (a b c : TagSet) : (a.union b).union c = a.union (b.union c) := by
  apply ext; intro t; simp only [mem_union]; cases a.mem t <;> cases b.mem t <;> cases c.mem t <;> rfl

@[simp] theorem union_idem (a : TagSet) : a.union a = a := by
  apply ext; intro t; simp

@[simp] theorem empty_union (a : TagSet) : empty.union a = a := by
  apply ext; intro t; simp

@[simp] theorem union_empty (a : TagSet) : a.union empty = a := by
  apply ext; intro t; simp

theorem subset_union_left (a b : TagSet) : a.subset (a.union b) = true :=
  (subset_iff a (a.union b)).mpr fun t ht => by simp [ht]

theorem subset_union_right (a b : TagSet) : b.subset (a.union b) = true :=
  (subset_iff b (a.union b)).mpr fun t ht => by simp [ht]

@[simp] theorem union_subset_iff (a b c : TagSet) :
    (a.union b).subset c = (a.subset c && b.subset c) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, subset_iff, mem_union, Bool.or_eq_true]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨ha, hb⟩ t (ht | ht)
    · exact ha t ht
    · exact hb t ht

theorem diff_subset (a b : TagSet) : (a.diff b).subset a = true :=
  (subset_iff (a.diff b) a).mpr fun t ht => by
    simp only [mem_diff, Bool.and_eq_true] at ht
    exact ht.1

theorem remove_subset (t : Tag) (a : TagSet) : (a.remove t).subset a = true :=
  (subset_iff (a.remove t) a).mpr fun x hx => by
    simp only [mem_remove, Bool.and_eq_true] at hx
    exact hx.1

def unionList (ss : List TagSet) : TagSet :=
  ss.foldl union empty

theorem mem_unionList (t : Tag) (ss : List TagSet) :
    (unionList ss).mem t = ss.any (fun s => s.mem t) := by
  unfold unionList
  have aux : ∀ (acc : TagSet) (xs : List TagSet),
      (xs.foldl union acc).mem t = (acc.mem t || xs.any (fun s => s.mem t)) := by
    intro acc xs
    induction xs generalizing acc with
    | nil => simp
    | cons s rest ih =>
      simp only [List.foldl_cons, ih, mem_union, List.any_cons]
      cases acc.mem t <;> cases s.mem t <;> cases (rest.any fun s => s.mem t) <;> rfl
  rw [aux]
  simp

theorem subset_unionList_of_mem {s : TagSet} {ss : List TagSet} (h : s ∈ ss) :
    s.subset (unionList ss) = true := by
  rw [subset_iff]
  intro t ht
  rw [mem_unionList, List.any_eq_true]
  exact ⟨s, h, ht⟩

theorem unionList_subset_iff (ss : List TagSet) (L : TagSet) :
    (unionList ss).subset L = true ↔ ∀ s ∈ ss, s.subset L = true := by
  rw [subset_iff]
  constructor
  · intro h s hs
    exact subset_trans (subset_unionList_of_mem hs) ((subset_iff _ _).mpr h)
  · intro h t ht
    rw [mem_unionList, List.any_eq_true] at ht
    rcases ht with ⟨s, hs, hts⟩
    exact (subset_iff s L).mp (h s hs) t hts

end TagSet

/-! ## Column & Table Schema Metadata -/

inductive AggKind where
  | raw
  | groupKey
  | blending
  | nonBlending
  deriving DecidableEq, Repr, Inhabited

/-- Monomorphic scalar / cell types permitted inside `Table` columns. -/
inductive ScalarTy where
  | unit
  | bool
  | int
  | decimal
  | float
  | text
  | bytes
  | date
  | timestamp
  | duration
  | data (name : Ident)
  | option (inner : ScalarTy)
  deriving DecidableEq, Repr, Inhabited

structure ColSpec where
  name     : Ident
  ty       : ScalarTy
  tags     : TagSet := TagSet.empty
  bucketed : Bool := false
  aggKind  : AggKind := .raw
  deriving DecidableEq, Repr, Inhabited

structure TableTy where
  cols       : List ColSpec
  rowTags    : TagSet := TagSet.empty
  orderTags  : TagSet := TagSet.empty
  groupedBy  : Option (List Ident) := none
  summarized : Bool := false
  distinctBy : Option Ident := none
  deriving DecidableEq, Repr, Inhabited

namespace TableTy

def findCol? (tt : TableTy) (name : Ident) : Option ColSpec :=
  tt.cols.find? (fun c => c.name == name)

def colNames (tt : TableTy) : List Ident :=
  tt.cols.map ColSpec.name

def allColTags (tt : TableTy) : TagSet :=
  TagSet.unionList (tt.cols.map ColSpec.tags)

def totalTags (tt : TableTy) : TagSet :=
  (tt.rowTags.union tt.orderTags).union tt.allColTags

end TableTy

/-! ## Monomorphic Value & Capability Types (`Ty` and `LTy`) -/

mutual
inductive Ty where
  -- Primitives
  | unit
  | bool
  | int
  | decimal
  | float
  | text
  | bytes
  -- Time
  | date
  | timestamp
  | duration
  -- Missing & Errors
  | option (inner : Ty)
  | result (okTy : Ty) (errTy : Ty)
  -- Collections & Records
  | tuple (elems : List LTy)
  | list (elem : LTy)
  | map (key : LTy) (val : LTy)
  | data (name : Ident)
  -- Tables
  | table (schema : TableTy)
  | dynamicTable (tags : TagSet)
  -- Reporting & Statistics
  | chart (tags : TagSet)
  | report (tags : TagSet)
  | profile (tags : TagSet)
  | linearModel
  | statTest
  -- Functions
  | fn (params : List LTy) (pc : TagSet) (ret : LTy)
  -- Capabilities (first-class, zero ambient authority)
  | args
  | clock
  | console (allows : TagSet)
  | readFiles
  | writeFiles (root : String) (allows : TagSet)
  | readDB (db : Ident)
  | writeTable (db : Ident) (tableName : Ident) (destCols : List ColSpec)
      (destRowTags : TagSet) (allows : TagSet)
  | rawReadDB (db : Ident)
  | httpsAllow (host : String) (allows : TagSet)
  | secret (name : String)
  | declassify (allows : TagSet)
  deriving Repr

inductive LTy where
  | mk (ty : Ty) (tags : TagSet)
  deriving Repr
end

instance : Inhabited Ty := ⟨.unit⟩
instance : Inhabited LTy := ⟨.mk .unit TagSet.empty⟩

namespace LTy
def ty : LTy → Ty | .mk t _ => t
def tags : LTy → TagSet | .mk _ s => s
end LTy

/-! ### Structural `DecidableEq` for `Ty` and `LTy` -/

mutual
def beqTy : Ty → Ty → Bool
  | .unit, .unit => true
  | .bool, .bool => true
  | .int, .int => true
  | .decimal, .decimal => true
  | .float, .float => true
  | .text, .text => true
  | .bytes, .bytes => true
  | .date, .date => true
  | .timestamp, .timestamp => true
  | .duration, .duration => true
  | .option a1, .option b1 => beqTy a1 b1
  | .result a1 a2, .result b1 b2 => beqTy a1 b1 && beqTy a2 b2
  | .tuple as1, .tuple bs1 => beqLTyList as1 bs1
  | .list a1, .list b1 => beqLTy a1 b1
  | .map ak av, .map bk bv => beqLTy ak bk && beqLTy av bv
  | .data a1, .data b1 => decide (a1 = b1)
  | .table a1, .table b1 => decide (a1 = b1)
  | .dynamicTable a1, .dynamicTable b1 => decide (a1 = b1)
  | .chart a1, .chart b1 => decide (a1 = b1)
  | .report a1, .report b1 => decide (a1 = b1)
  | .profile a1, .profile b1 => decide (a1 = b1)
  | .linearModel, .linearModel => true
  | .statTest, .statTest => true
  | .fn ap apc ar, .fn bp bpc br => beqLTyList ap bp && decide (apc = bpc) && beqLTy ar br
  | .args, .args => true
  | .clock, .clock => true
  | .console a1, .console b1 => decide (a1 = b1)
  | .readFiles, .readFiles => true
  | .writeFiles ar aa, .writeFiles br ba => decide (ar = br) && decide (aa = ba)
  | .readDB a1, .readDB b1 => decide (a1 = b1)
  | .writeTable adb atbl acols art aa, .writeTable bdb btbl bcols brt ba =>
    decide (adb = bdb) && decide (atbl = btbl) && decide (acols = bcols) &&
    decide (art = brt) && decide (aa = ba)
  | .rawReadDB a1, .rawReadDB b1 => decide (a1 = b1)
  | .httpsAllow ah aa, .httpsAllow bh ba => decide (ah = bh) && decide (aa = ba)
  | .secret a1, .secret b1 => decide (a1 = b1)
  | .declassify a1, .declassify b1 => decide (a1 = b1)
  | _, _ => false

def beqLTy : LTy → LTy → Bool
  | .mk aty atags, .mk bty btags => beqTy aty bty && decide (atags = btags)

def beqLTyList : List LTy → List LTy → Bool
  | [], [] => true
  | a :: as1, b :: bs1 => beqLTy a b && beqLTyList as1 bs1
  | _, _ => false
end

mutual
theorem beqTy_refl : ∀ (a : Ty), beqTy a a = true
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .linearModel | .statTest
  | .args | .clock | .readFiles => rfl
  | .option a1 => beqTy_refl a1
  | .result a1 a2 => by simp [beqTy, beqTy_refl a1, beqTy_refl a2]
  | .tuple as1 => beqLTyList_refl as1
  | .list a1 => beqLTy_refl a1
  | .map ak av => by simp [beqTy, beqLTy_refl ak, beqLTy_refl av]
  | .data _ | .table _ | .dynamicTable _ | .chart _ | .report _ | .profile _
  | .console _ | .readDB _ | .rawReadDB _ | .secret _ | .declassify _ => by simp [beqTy]
  | .fn ap _ ar => by simp [beqTy, beqLTyList_refl ap, beqLTy_refl ar]
  | .writeFiles _ _ | .httpsAllow _ _ => by simp [beqTy]
  | .writeTable _ _ _ _ _ => by simp [beqTy]

theorem beqLTy_refl : ∀ (a : LTy), beqLTy a a = true
  | .mk aty _ => by simp [beqLTy, beqTy_refl aty]

theorem beqLTyList_refl : ∀ (as1 : List LTy), beqLTyList as1 as1 = true
  | [] => rfl
  | a :: as1 => by simp [beqLTyList, beqLTy_refl a, beqLTyList_refl as1]
end

mutual
theorem beqTy_eq : ∀ {a b : Ty}, beqTy a b = true → a = b
  | .unit, .unit, _ => rfl
  | .bool, .bool, _ => rfl
  | .int, .int, _ => rfl
  | .decimal, .decimal, _ => rfl
  | .float, .float, _ => rfl
  | .text, .text, _ => rfl
  | .bytes, .bytes, _ => rfl
  | .date, .date, _ => rfl
  | .timestamp, .timestamp, _ => rfl
  | .duration, .duration, _ => rfl
  | .option a1, .option b1, h => congrArg Ty.option (beqTy_eq h)
  | .result a1 a2, .result b1 b2, h => by
    simp only [beqTy, Bool.and_eq_true] at h
    rw [beqTy_eq h.1, beqTy_eq h.2]
  | .tuple as1, .tuple bs1, h => congrArg Ty.tuple (beqLTyList_eq h)
  | .list a1, .list b1, h => congrArg Ty.list (beqLTy_eq h)
  | .map ak av, .map bk bv, h => by
    simp only [beqTy, Bool.and_eq_true] at h
    rw [beqLTy_eq h.1, beqLTy_eq h.2]
  | .data a1, .data b1, h => by simp [beqTy] at h; subst h; rfl
  | .table a1, .table b1, h => by simp [beqTy] at h; subst h; rfl
  | .dynamicTable a1, .dynamicTable b1, h => by simp [beqTy] at h; subst h; rfl
  | .chart a1, .chart b1, h => by simp [beqTy] at h; subst h; rfl
  | .report a1, .report b1, h => by simp [beqTy] at h; subst h; rfl
  | .profile a1, .profile b1, h => by simp [beqTy] at h; subst h; rfl
  | .linearModel, .linearModel, _ => rfl
  | .statTest, .statTest, _ => rfl
  | .fn ap apc ar, .fn bp bpc br, h => by
    simp only [beqTy, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [beqLTyList_eq h.1.1, h.1.2, beqLTy_eq h.2]
  | .args, .args, _ => rfl
  | .clock, .clock, _ => rfl
  | .console a1, .console b1, h => by simp [beqTy] at h; subst h; rfl
  | .readFiles, .readFiles, _ => rfl
  | .writeFiles ar aa, .writeFiles br ba, h => by
    simp [beqTy] at h; rw [h.1, h.2]
  | .readDB a1, .readDB b1, h => by simp [beqTy] at h; subst h; rfl
  | .writeTable adb atbl acols art aa, .writeTable bdb btbl bcols brt ba, h => by
    simp only [beqTy, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    rw [h1, h2, h3, h4, h5]
  | .rawReadDB a1, .rawReadDB b1, h => by simp [beqTy] at h; subst h; rfl
  | .httpsAllow ah aa, .httpsAllow bh ba, h => by
    simp [beqTy] at h; rw [h.1, h.2]
  | .secret a1, .secret b1, h => by simp [beqTy] at h; subst h; rfl
  | .declassify a1, .declassify b1, h => by simp [beqTy] at h; subst h; rfl

theorem beqLTy_eq : ∀ {a b : LTy}, beqLTy a b = true → a = b
  | .mk aty atags, .mk bty btags, h => by
    simp only [beqLTy, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [beqTy_eq h.1, h.2]

theorem beqLTyList_eq : ∀ {as1 bs1 : List LTy}, beqLTyList as1 bs1 = true → as1 = bs1
  | [], [], _ => rfl
  | a :: as1, b :: bs1, h => by
    simp only [beqLTyList, Bool.and_eq_true] at h
    rw [beqLTy_eq h.1, beqLTyList_eq h.2]
end

instance : DecidableEq Ty := fun a b =>
  if h : beqTy a b = true then isTrue (beqTy_eq h)
  else isFalse (fun heq => h (heq ▸ beqTy_refl a))

instance : DecidableEq LTy := fun a b =>
  if h : beqLTy a b = true then isTrue (beqLTy_eq h)
  else isFalse (fun heq => h (heq ▸ beqLTy_refl a))

/-! ### Conversions & Tag Helpers on `Ty` and `LTy` -/

def ScalarTy.toTy : ScalarTy → Ty
  | .unit => .unit
  | .bool => .bool
  | .int => .int
  | .decimal => .decimal
  | .float => .float
  | .text => .text
  | .bytes => .bytes
  | .date => .date
  | .timestamp => .timestamp
  | .duration => .duration
  | .data n => .data n
  | .option inner => .option inner.toTy

def Ty.toScalarTy? : Ty → Option ScalarTy
  | .unit => some .unit
  | .bool => some .bool
  | .int => some .int
  | .decimal => some .decimal
  | .float => some .float
  | .text => some .text
  | .bytes => some .bytes
  | .date => some .date
  | .timestamp => some .timestamp
  | .duration => some .duration
  | .data n => some (.data n)
  | .option inner => (inner.toScalarTy?).map ScalarTy.option
  | _ => none

@[simp] theorem ScalarTy.toScalarTy?_toTy : ∀ (s : ScalarTy), s.toTy.toScalarTy? = some s
  | .unit | .bool | .int | .decimal | .float | .text | .bytes
  | .date | .timestamp | .duration | .data _ => rfl
  | .option inner => by simp [ScalarTy.toTy, Ty.toScalarTy?, ScalarTy.toScalarTy?_toTy inner]

theorem Ty.toScalarTy?_some_imp : ∀ {t : Ty} {s : ScalarTy}, t.toScalarTy? = some s → s.toTy = t
  | .unit, _, h => by injection h with h'; subst h'; rfl
  | .bool, _, h => by injection h with h'; subst h'; rfl
  | .int, _, h => by injection h with h'; subst h'; rfl
  | .decimal, _, h => by injection h with h'; subst h'; rfl
  | .float, _, h => by injection h with h'; subst h'; rfl
  | .text, _, h => by injection h with h'; subst h'; rfl
  | .bytes, _, h => by injection h with h'; subst h'; rfl
  | .date, _, h => by injection h with h'; subst h'; rfl
  | .timestamp, _, h => by injection h with h'; subst h'; rfl
  | .duration, _, h => by injection h with h'; subst h'; rfl
  | .data _, _, h => by injection h with h'; subst h'; rfl
  | .option inner, s, h => by
    cases hInner : inner.toScalarTy? with
    | none => simp [Ty.toScalarTy?, hInner] at h
    | some sInner =>
      simp only [Ty.toScalarTy?, hInner, Option.map_some, Option.some.injEq] at h
      subst h
      simp [ScalarTy.toTy, Ty.toScalarTy?_some_imp hInner]

mutual
/-- Union of all sensitivity tags appearing anywhere inside `Ty` (including nested
    tuple/list/map elements and table columns/rowTags/orderTags). -/
def Ty.allTags : Ty → TagSet
  | .unit | .bool | .int | .decimal | .float | .text | .bytes => TagSet.empty
  | .date | .timestamp | .duration => TagSet.empty
  | .option inner => inner.allTags
  | .result okTy errTy => okTy.allTags.union errTy.allTags
  | .tuple elems => LTy.allTagsList elems
  | .list elem => elem.allTags
  | .map k v => k.allTags.union v.allTags
  | .data _ => TagSet.empty
  | .table tt => tt.totalTags
  | .dynamicTable ts => ts
  | .chart ts => ts
  | .report ts => ts
  | .profile ts => ts
  | .linearModel | .statTest => TagSet.empty
  | .fn params pc ret => (LTy.allTagsList params).union (pc.union ret.allTags)
  | .args | .clock | .readFiles | .readDB _ | .rawReadDB _ => TagSet.empty
  | .secret _ => TagSet.singleton "secret"
  | .console allows => allows
  | .writeFiles _ allows => allows
  | .writeTable _ _ _ _ allows => allows
  | .httpsAllow _ allows => allows
  | .declassify allows => allows

def LTy.allTags : LTy → TagSet
  | .mk ty ts => ty.allTags.union ts

def LTy.allTagsList : List LTy → TagSet
  | [] => TagSet.empty
  | l :: ls => l.allTags.union (LTy.allTagsList ls)
end

/-- Add outer control-flow / taint tags to an `LTy`. -/
def LTy.addTags (extra : TagSet) : LTy → LTy
  | .mk ty ts => .mk ty (ts.union extra)

/-- Effective top-level sensitivity tags of a value of type `LTy` when emitted or inspected. -/
def LTy.effectiveTags : LTy → TagSet
  | .mk (.table tt) ts => tt.totalTags.union ts
  | .mk (.dynamicTable dt) ts => dt.union ts
  | .mk (.chart ct) ts => ct.union ts
  | .mk (.report rt) ts => rt.union ts
  | .mk (.profile pt) ts => pt.union ts
  | .mk (.secret _) ts => (TagSet.singleton "secret").union ts
  | .mk ty ts => ty.allTags.union ts

/-! ## Numeric Bounds, IEEE-754 Float64 Bits & Literals -/

def int64Min : Int := -9223372036854775808
def int64Max : Int := 9223372036854775807

def decScale : Int := 1000000000000000000
def decMax : Int := (2 ^ 127 : Int) - 1
def decMin : Int := -((2 ^ 127 : Int) - 1)

def inInt64Range (n : Int) : Bool :=
  decide (int64Min ≤ n ∧ n ≤ int64Max)

def inDecimalRange (d : Int) : Bool :=
  decide (decMin ≤ d ∧ d ≤ decMax)

/-- IEEE-754 binary64 bit pattern with transparent kernel equality. -/
structure Float64 where
  bits : UInt64
  deriving DecidableEq, Repr, Inhabited

namespace Float64
def zero : Float64 := ⟨0⟩
def isNaN (f : Float64) : Bool :=
  let exp := (f.bits >>> 52) &&& 0x7FF
  let mant := f.bits &&& 0x000FFFFFFFFFFFFF
  exp == 0x7FF && mant != 0
end Float64

inductive Literal where
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
  | noneLit (inner : Ty)
  deriving DecidableEq, Repr, Inhabited

/-! ## Pure Primitives (`PrimOp`), Host Operations (`HostOp`), and Bug Kinds -/

inductive ChartKind where
  | bar
  | line
  | scatter
  | histogram
  | heatmap
  deriving DecidableEq, Repr, Inhabited

inductive PrimOp where
  -- Unified Option & Result
  | someVal (inner : Ty)
  | isSome
  | isNone
  | unwrapOr
  | unwrapBang
  | okVal (errTy : Ty)
  | errVal (okTy : Ty)
  -- Checked Int64 arithmetic
  | addInt
  | subInt
  | mulInt
  | divInt
  | modInt
  | negInt
  -- Checked fixed-point Decimal arithmetic (10^-18 scale)
  | addDec
  | subDec
  | mulDec
  | divDec
  | negDec
  | intToDec
  | boolToDec
  -- Comparisons & Boolean logic
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | notBool
  | andBool
  | orBool
  -- Text & Time operations
  | concatText
  | trimText
  | lowerAsciiText
  | containsText
  | emptyText
  | intToText
  | decToText
  | dateTruncMonth
  | addDuration
  | diffTimestamp
  -- Collections (List & Map)
  | listLit (elemLTy : LTy)
  | listLen
  | listEmpty
  | listAppend
  | listConcat
  | mapLit (keyLTy : LTy) (valLTy : LTy)
  | mapGet
  -- Pure Table inspection, Profiling, Stats, Charts & Reports
  | tableCount
  | tableConcat (schema : TableTy)
  | tableProfile
  | statsCorr (colX : Ident) (colY : Ident)
  | statsLinReg (colX : Ident) (colY : Ident)
  | statsTTest (colX : Ident) (colY : Ident)
  | chartMake (kind : ChartKind) (cols : List Ident) (title : String)
  | reportNew
  | reportAddSummary
  | reportAddChart
  | reportAddTable
  deriving DecidableEq, Repr

inductive HostOp where
  -- Real / Polymorphic-handle capability operations
  | argsGet
  | clockNow
  | consolePrint
  | consoleError
  | consolePrintTable
  | readCsv (schema : Ident)
  | writeFile
  | writeReportHtml
  | writeTable
  | declassifyApprove (clearTags : TagSet)
  -- Documented `outside` host boundary operations (binary codecs & live wire protocols)
  | rawSqlQuery (db : Ident) (outSchema : TableTy)
  | httpsGetJson
  | readParquet (schema : TableTy)
  | writeParquet
  | writeXlsx
  -- Spec-only (`test` / `example` / `promise`) fake capability constructors
  | fakeConsole (allows : TagSet)
  | fakeFiles (allows : TagSet)
  | fakeDB (db : Ident)
  | fakeHttps (host : String) (allows : TagSet)
  | fakeSecret (name : String)
  deriving DecidableEq, Repr

inductive BugKind where
  | intOverflow
  | decimalOverflow
  | divByZero
  | unwrapNone
  | joinCardinality
  | promiseViolation
  | schemaConstraint
  | exportGateDenied
  | outsideBoundary
  | userStop
  deriving DecidableEq, Repr, Inhabited

/-! ## Pure Relational Plan Sub-Calculus (`RowExpr`, `Plan`) & Expressions (`Expr`) -/

inductive SortDir where
  | asc
  | desc
  deriving DecidableEq, Repr, Inhabited

inductive JoinKind where
  | innerOne
  | innerManyToOne
  | innerMany
  | leftOne
  | leftManyToOne
  | semi
  | anti
  deriving DecidableEq, Repr, Inhabited

inductive JoinOn where
  | sameKeys (keys : List Ident)
  | pairs (keys : List (Ident × Ident))
  deriving DecidableEq, Repr, Inhabited

inductive AggOp where
  -- Blending aggregates (cleared by `SuppressSmallGroups` when k >= min_group_size)
  | count
  | countDistinct
  | sum
  | mean
  | stddev
  | variance
  -- Non-blending single-record / order-statistic aggregates (NEVER cleared by `SuppressSmallGroups`)
  | median
  | percentile (p : Float64)
  | min
  | max
  | first
  | last
  deriving DecidableEq, Repr, Inhabited

namespace AggOp
def isBlending : AggOp → Bool
  | .count | .countDistinct | .sum | .mean
  | .stddev | .variance => true
  | .median | .percentile _ | .min | .max | .first | .last => false

def isOrderSensitive : AggOp → Bool
  | .first | .last => true
  | _ => false
end AggOp

inductive SuppressMode where
  | drop
  | maskComplementary
  deriving DecidableEq, Repr, Inhabited

/-- Pure scalar expression language inside relational operators (`Filter`, `Derive`,
    `Summarize`, `Window`). Strictly free of I/O and capabilities. -/
inductive RowExpr where
  | lit (v : Literal)
  | col (name : Ident)
  | outerVar (name : Ident)
  | constRef (name : Ident)
  | prim (op : PrimOp) (args : List RowExpr)
  | ifE (cond : RowExpr) (thenBr : RowExpr) (elseBr : RowExpr)
  | coalesce (optExpr : RowExpr) (defaultExpr : RowExpr)
  | callPure (fnName : Ident) (args : List RowExpr)
  deriving BEq, Repr, Inhabited

structure AggItem where
  name : Ident
  op   : AggOp
  arg  : Option RowExpr
  deriving BEq, Repr, Inhabited

inductive DeriveItem where
  | colExpr (name : Ident) (expr : RowExpr)
  | bucketCol (name : Ident) (source : Ident) (cuts : List Literal) (labels : List String)
  deriving BEq, Repr, Inhabited

inductive WindowFn where
  | lag (col : Ident) (offset : Nat)
  | lead (col : Ident) (offset : Nat)
  | rowNumber
  | rank (col : Ident)
  | runningSum (col : Ident)
  | rollingMean (col : Ident) (windowSize : Nat)
  deriving DecidableEq, Repr, Inhabited

structure WindowItem where
  name  : Ident
  fn    : WindowFn
  over  : List Ident
  order : List (Ident × SortDir)
  deriving DecidableEq, Repr, Inhabited

structure RowLit where
  cells : List Literal
  deriving DecidableEq, Repr, Inhabited

abbrev Suffixes := Option (String × String)

mutual
inductive CaseArm where
  | mk (ctor : Ident) (binders : List Ident) (body : Expr)
  deriving BEq, Repr

inductive Expr where
  | lit (v : Literal)
  | var (name : Ident)
  | constRef (name : Ident)
  | letE (name : Ident) (lty : LTy) (bound : Expr) (body : Expr)
  | ifE (cond : Expr) (thenBr : Expr) (elseBr : Expr)
  | caseE (scrut : Expr) (arms : List CaseArm)
  | lam (params : List (Ident × LTy)) (pc : TagSet) (ret : LTy) (body : Expr)
  | app (fnExpr : Expr) (args : List Expr)
  | call (fnName : Ident) (args : List Expr)
  | join (label : Ident) (params : List (Ident × LTy)) (rhs : Expr) (body : Expr)
  | jump (label : Ident) (args : List Expr)
  | tuple (elems : List Expr)
  | proj (tup : Expr) (idx : Nat)
  | ctor (typeName : Ident) (ctorName : Ident) (args : List Expr)
  | tableLit (schema : TableTy) (rows : List RowLit)
  | prim (op : PrimOp) (args : List Expr)
  | rel (plan : Plan)
  | host (op : HostOp) (args : List Expr)
  | stop (kind : BugKind) (detail : Option Expr)
  | fail (msg : Expr)
  deriving BEq, Repr

inductive Plan where
  | sourceExpr (e : Expr)
  | sourceDB (cap : Expr) (tableName : Ident) (schema : TableTy)
  | select (input : Plan) (cols : List Ident)
  | drop (input : Plan) (cols : List Ident)
  | rename (input : Plan) (pairs : List (Ident × Ident))
  | derive (input : Plan) (items : List DeriveItem)
  | filter (input : Plan) (pred : RowExpr)
  | distinct (input : Plan) (cols : List Ident)
  | sort (input : Plan) (keys : List (Ident × SortDir))
  | limit (input : Plan) (n : Nat)
  | join (kind : JoinKind) (left : Plan) (right : Plan) (on : JoinOn) (suffixes : Suffixes)
  | union (left : Plan) (right : Plan)
  | groupBy (input : Plan) (keys : List Ident)
  | summarize (input : Plan) (aggs : List AggItem) (distinctKey : Option Ident)
  | suppressSmallGroups (input : Plan) (minK : Nat) (distinctBy : Option Ident) (mode : SuppressMode)
  | window (input : Plan) (items : List WindowItem)
  | fillGaps (input : Plan) (col : Ident) (stepMicros : Int) (over : List Ident)
      (fill : List (Ident × Literal))
  | pivotWider (input : Plan) (namesFrom : Ident) (valuesFrom : Ident)
      (staticCols : List Ident) (fill : Literal)
  | crosstab (input : Plan) (rowsCol : Ident) (colsCol : Ident)
      (valuesCol : Ident) (fill : Literal)
  | redact (input : Plan) (col : Ident) (replacement : String)
  | pseudonymize (input : Plan) (col : Ident) (secret : Expr)
  deriving BEq, Repr
end

instance : Inhabited Expr := ⟨.lit .unit⟩
instance : Inhabited Plan := ⟨.sourceExpr (.lit .unit)⟩

/-! ## Policies (`dana.policy`), Top-Level Declarations, Metadata & `Program` -/

structure PolicyWriteRule where
  db    : Ident
  table : Ident
  tags  : TagSet
  deriving DecidableEq, Repr, Inhabited

/-- Parsed optional `dana.policy` repository upper bound. -/
structure Policy where
  minGroupSize           : Nat := 5
  forbidManualDeclassify : Bool := false
  forbidReplSensitive    : Bool := false
  allowConsole           : TagSet := TagSet.empty
  allowExport            : List (String × TagSet) := []
  allowHttps             : List (String × TagSet) := []
  allowWrite             : List PolicyWriteRule := []
  deriving DecidableEq, Repr, Inhabited

structure CtorDecl where
  name   : Ident
  fields : List LTy
  deriving DecidableEq, Repr, Inhabited

structure DataDecl where
  name  : Ident
  ctors : List CtorDecl
  deriving DecidableEq, Repr, Inhabited

structure SchemaDecl where
  name   : Ident
  schema : TableTy
  deriving DecidableEq, Repr, Inhabited

structure ConstDecl where
  name  : Ident
  lty   : LTy
  value : Literal
  deriving DecidableEq, Repr, Inhabited

inductive FunKind where
  | function
  | test
  | exampleDecl
  | promise
  deriving DecidableEq, Repr, Inhabited

namespace FunKind
def isSpec : FunKind → Bool
  | .function => false
  | .test | .exampleDecl | .promise => true
end FunKind

structure FunDecl where
  name   : Ident
  kind   : FunKind := .function
  isPure : Bool := false
  params : List (Ident × LTy)
  pc     : TagSet := TagSet.empty
  ret    : LTy
  body   : Expr
  deriving BEq, Repr, Inhabited

structure SourceSpan where
  file      : String
  startLine : Nat
  startCol  : Nat
  endLine   : Nat
  endCol    : Nat
  deriving DecidableEq, Repr, Inhabited

structure MetaEntry where
  nodeId   : Ident
  origName : Option String := none
  span     : Option SourceSpan := none
  deriving DecidableEq, Repr, Inhabited

/-- Lossless compiler diagnostic metadata. Never read by typing or evaluation. -/
structure CompilerMetadata where
  entries : List MetaEntry := []
  deriving DecidableEq, Repr, Inhabited

structure CoreVersion where
  major : Nat := 0
  minor : Nat := 1
  deriving DecidableEq, Repr, Inhabited

structure Program where
  version  : CoreVersion := { major := 0, minor := 1 }
  tags     : List Tag := []
  policy   : Option Policy := none
  datas    : List DataDecl := []
  schemas  : List SchemaDecl := []
  consts   : List ConstDecl := []
  funs     : List FunDecl := []
  entry    : Option Ident := none
  metadata : CompilerMetadata := {}
  deriving BEq, Repr, Inhabited

namespace Program

def findData? (prog : Program) (name : Ident) : Option DataDecl :=
  prog.datas.find? (fun d => d.name == name)

def findSchema? (prog : Program) (name : Ident) : Option SchemaDecl :=
  prog.schemas.find? (fun s => s.name == name)

def findConst? (prog : Program) (name : Ident) : Option ConstDecl :=
  prog.consts.find? (fun c => c.name == name)

def findFun? (prog : Program) (name : Ident) : Option FunDecl :=
  prog.funs.find? (fun f => f.name == name)

def minGroupFloor (prog : Program) : Nat :=
  match prog.policy with
  | none => 5
  | some p => Nat.max 5 p.minGroupSize

end Program

end DanaCore
