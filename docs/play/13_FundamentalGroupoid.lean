-- はじめての Lean — 13_FundamentalGroupoid（ブラウザ版・自動生成）
-- 先頭には、この章が使う前の章（05_MathematicalTools・06_Topology・11_Covering（解答）・07_Exercises（解答）・08_Real（解答）・12_CoveringSpace（解答））のコードをまとめてあります。
-- 本章は「ここから本章」の行から始まります（3753 行目。Ctrl+G で行番号へ移動できます）。
-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、
-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。

-- ════════ 前の章のコード（読まなくてよい） ════════
-- ─── 05_MathematicalTools ───
section

inductive MyPoint : Type where
  | mk (x y : Nat) : MyPoint

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | MyPoint.mk a _ => a

structure Point : Type where
  x : Nat
  y : Nat

def pointFromPair : Point := ⟨1, 2⟩
def pointFromDot : Point := .mk 1 2

def point_pair_eq_mk : (⟨1, 2⟩ : Point) = Point.mk 1 2 := rfl
def point_fields_eq_mk : ({ x := 1, y := 2 } : Point) = Point.mk 1 2 := rfl

def exists_two : ∃ n : Nat, n = 2 := ⟨2, rfl⟩

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

structure Pair (α β : Type) : Type where
  fst : α
  snd : β

def natBoolPair : Pair Nat Bool := Pair.mk 3 true

structure PointedType : Type 1 where
  carrier : Type
  point : carrier

def pointedNat : PointedType := ⟨Nat, 0⟩
def pointedBool : PointedType := ⟨Bool, true⟩

def IsEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

def EvenNat : Type := {n : Nat // IsEven n}

def evenFour : EvenNat := Subtype.mk 4 (Exists.intro 2 rfl)

def evenFourPlusFour : IsEven (evenFour.val + evenFour.val) :=
  Exists.intro 4 rfl

def lastFromProof : (n : Nat) → Fin (n + 1) :=
  fun n => Fin.mk n (Nat.lt_succ_self n)

def lastFromProof_val (n : Nat) : (lastFromProof n).val = n := rfl
def lastFromProof_eq_last (n : Nat) : lastFromProof n = Fin.last n := rfl

class Pointed (α : Type) : Type where
  point : α

instance : Pointed Nat where
  point := 0

def pointPair (α : Type) [Pointed α] : Pair α α := ⟨Pointed.point, Pointed.point⟩

instance : Pointed Point where
  point := ⟨0, 0⟩

def pointPair_fst (α : Type) [Pointed α] :
    (pointPair α).fst = Pointed.point := rfl

def pointPair_nat_fst : (pointPair Nat).fst = Pointed.point := pointPair_fst Nat
def pointPair_point_fst : (pointPair Point).fst = Pointed.point := pointPair_fst Point

instance {α β : Type} [Pointed α] [Pointed β] : Pointed (Pair α β) where
  point := ⟨Pointed.point, Pointed.point⟩

instance : Add Point where
  add p q := ⟨p.x + q.x, p.y + q.y⟩

def z : Prop := 2 < 3

def zFromLt (h : 2 < 3) : z := h

instance : Decidable z := inferInstanceAs (Decidable (2 < 3))

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

def Set (X : Type) : Type := X → Prop

def setOf {X : Type} (p : X → Prop) : Set X := p

syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

instance {X : Type} : Membership X (Set X) := ⟨fun s a => s a⟩

def one_mem_singleton : (1 : Nat) ∈ ({n | n = 1} : Set Nat) := rfl

instance {X : Type} : HasSubset (Set X) := ⟨fun s t => ∀ a, a ∈ s → a ∈ t⟩

def Set.subset_refl {X : Type} (s : Set X) : s ⊆ s := fun _ ha => ha

namespace Geometry

def origin : Point := ⟨0, 0⟩

end Geometry

end

-- ─── 06_Topology ───
section

def swapAnd {p q : Prop} : p ∧ q → q ∧ p :=
  fun h => And.intro h.right h.left

theorem swapAnd' {p q : Prop} : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.right, h.left⟩

namespace Set

variable {α : Type}

instance : Inter (Set α) := ⟨fun s t => {a | a ∈ s ∧ a ∈ t}⟩

instance : Union (Set α) := ⟨fun s t => {a | a ∈ s ∨ a ∈ t}⟩

instance : EmptyCollection (Set α) := ⟨{_a | False}⟩

def univ : Set α := {_a | True}

example : (0 : Nat) ∈ (univ : Set Nat) := trivial

def compl (s : Set α) : Set α := {a | a ∉ s}

postfix:max "ᶜ" => Set.compl

def image {β : Type} (f : α → β) (s : Set α) : Set β := {b | ∃ a, a ∈ s ∧ f a = b}

infixl:80 " '' " => Set.image

def sUnion (S : Set (Set α)) : Set α := {a | ∃ s, s ∈ S ∧ a ∈ s}

prefix:110 "⋃₀ " => Set.sUnion

def iUnion {I : Type} (U : I → Set α) : Set α := {a | ∃ i, a ∈ U i}

def biUnion {I : Type} (J : Set I) (U : I → Set α) : Set α := {a | ∃ i, i ∈ J ∧ a ∈ U i}

def preimage {β : Type} (f : α → β) (s : Set β) : Set α := {a | f a ∈ s}

infixl:80 " ⁻¹' " => Set.preimage

example : (fun n : Nat => n + 1) ⁻¹' {m | m = 3} = {n | n + 1 = 3} := rfl

example (f : Nat → Nat) (s t : Set Nat) : f '' s ∩ t = (f '' s) ∩ t := rfl
example (s t : Set Nat) : s ∩ tᶜ = s ∩ (tᶜ) := rfl
example (s t u : Set Nat) : s ∩ t ∪ u = (s ∩ t) ∪ u := rfl

def Finite (s : Set α) : Prop := ∃ (n : Nat) (f : Fin n → α), ∀ a ∈ s, ∃ i, f i = a

theorem Finite.empty : (∅ : Set α).Finite :=
  ⟨0, Fin.elim0, fun _ ha => False.elim ha⟩

theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

theorem compl_compl (s : Set α) : sᶜᶜ = s :=
  ext fun _ => ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

theorem union_eq_sUnion (s t : Set α) : s ∪ t = ⋃₀ {u | u = s ∨ u = t} := by
  apply ext
  intro a
  constructor
  · intro ha
    cases ha with
    | inl h => exact ⟨s, Or.inl rfl, h⟩
    | inr h => exact ⟨t, Or.inr rfl, h⟩
  · intro ha
    have ⟨u, hu, hau⟩ := ha
    cases hu with
    | inl h => exact Or.inl (h ▸ hau)
    | inr h => exact Or.inr (h ▸ hau)

example (s t : Set α) : s ∪ t = ⋃₀ {u | u = s ∨ u = t} :=
  ext fun _ =>
    ⟨fun ha =>
      match ha with
      | Or.inl h => ⟨s, Or.inl rfl, h⟩
      | Or.inr h => ⟨t, Or.inr rfl, h⟩,
     fun ⟨_, hu, hau⟩ =>
      match hu with
      | Or.inl h => Or.inl (h ▸ hau)
      | Or.inr h => Or.inr (h ▸ hau)⟩

def interFin : (n : Nat) → (Fin n → Set α) → Set α := fun n W =>
  match n with
  | 0 => univ
  | n + 1 => W 0 ∩ interFin n fun i => W i.succ

theorem mem_interFin : ∀ (n : Nat) (W : Fin n → Set α) (a : α), (∀ i, a ∈ W i) →
    a ∈ interFin n W := fun n W a h =>
  match n with
  | 0 => trivial
  | n + 1 => ⟨h 0, mem_interFin n (fun i => W i.succ) a fun i => h i.succ⟩

theorem interFin_mem : ∀ (n : Nat) (W : Fin n → Set α) (a : α), a ∈ interFin n W →
    ∀ i, a ∈ W i := fun n W a h i =>
  match n with
  | 0 => Fin.elim0 i
  | n + 1 => Fin.cases h.left (fun j => interFin_mem n (fun k => W k.succ) a h.right j) i

end Set

structure Function.Bijective {α β : Type} (f : α → β) : Prop where

  injective : Function.Injective f

  surjective : Function.Surjective f

syntax:110 "⋃ " ident ", " term : term

syntax:110 "⋃ " ident " ∈ " term:110 ", " term : term

macro_rules
  | `(⋃ $i, $U) => `(Set.iUnion fun $i => $U)
  | `(⋃ $i ∈ $J, $U) => `(Set.biUnion $J fun $i => $U)

class TopologicalSpace (X : Type) where

  IsOpen (s : Set X) : Prop

  isOpen_univ : IsOpen Set.univ

  isOpen_inter (s t : Set X) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t)

  isOpen_sUnion (S : Set (Set X)) (h : ∀ s ∈ S, IsOpen s) : IsOpen (⋃₀ S)

export TopologicalSpace (IsOpen isOpen_univ isOpen_inter isOpen_sUnion)

variable {X : Type} [TopologicalSpace X]

theorem isOpen_empty : IsOpen (∅ : Set X) := by
  have h : (⋃₀ (∅ : Set (Set X))) = (∅ : Set X) := by
    apply Set.ext
    intro a
    constructor
    · intro ⟨_, hs, _⟩
      exact False.elim hs
    · intro ha
      exact False.elim ha
  rw [← h]
  exact isOpen_sUnion _ fun _ hs => False.elim hs

example : IsOpen (∅ : Set X) :=
  have h : (⋃₀ (∅ : Set (Set X))) = (∅ : Set X) :=
    Set.ext fun _ => ⟨fun ⟨_, hs, _⟩ => False.elim hs, fun ha => False.elim ha⟩
  h ▸ isOpen_sUnion _ fun _ hs => False.elim hs

theorem isOpen_union {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  rw [Set.union_eq_sUnion]
  refine isOpen_sUnion _ fun u hu => ?_
  cases hu with
  | inl h =>
    rw [h]
    exact hs
  | inr h =>
    rw [h]
    exact ht

example {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) :=
  (Set.union_eq_sUnion s t) ▸ isOpen_sUnion _ fun _u hu =>
    match hu with
    | Or.inl h => h ▸ hs
    | Or.inr h => h ▸ ht

theorem isOpen_interFin : ∀ (n : Nat) (W : Fin n → Set X), (∀ i, IsOpen (W i)) →
    IsOpen (Set.interFin n W) := fun n W h =>
  match n with
  | 0 => isOpen_univ
  | n + 1 => isOpen_inter _ _ (h 0) (isOpen_interFin n (fun i => W i.succ) fun i => h i.succ)

def IsClosed (s : Set X) : Prop := IsOpen sᶜ

@[reducible] def discrete (X : Type) : TopologicalSpace X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ _ _ => trivial
  isOpen_sUnion := fun _ _ => trivial

variable {Y : Type} [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z]

def Continuous (f : X → Y) : Prop := ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

theorem continuous_id : Continuous (fun x : X => x) :=
  fun _ hs => hs

theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) :=
  fun s hs => hf _ (hg s hs)

class Hausdorff (X : Type) [TopologicalSpace X] : Prop where

  separate : ∀ x y : X, x ≠ y →
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

def IsCompact (K : Set X) : Prop :=
  ∀ {I : Type} (U : I → Set X), (∀ i, IsOpen (U i)) → K ⊆ (⋃ i, U i) →
    ∃ J : Set I, J.Finite ∧ K ⊆ (⋃ i ∈ J, U i)

class CompactSpace (X : Type) [TopologicalSpace X] : Prop where
  isCompact_univ : IsCompact (Set.univ : Set X)

theorem Set.subset_preimage_iUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i := by
  intro x hx
  have ⟨i, hi⟩ := h (f x) ⟨x, hx, rfl⟩
  exact ⟨i, hi⟩

example {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i :=
  fun x hx => h (f x) ⟨x, hx, rfl⟩

theorem Set.image_subset_biUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i := by
  intro b hb
  have ⟨x, hx, hfx⟩ := hb
  have ⟨i, hiJ, hxi⟩ := h x hx
  exact ⟨i, hiJ, hfx ▸ hxi⟩

example {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i :=
  fun _b hb =>
    match hb with
    | ⟨x, hx, hfx⟩ =>
      match h x hx with
      | ⟨i, hiJ, hxi⟩ => ⟨i, hiJ, hfx ▸ hxi⟩

theorem IsCompact.image {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) := by
  intro I U hU hcov
  have ⟨J, hJ, hsub⟩ := hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
      (Set.subset_preimage_iUnion hcov)
  exact ⟨J, hJ, Set.image_subset_biUnion hsub⟩

example {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) :=
  fun U hU hcov =>
    match hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
        (Set.subset_preimage_iUnion hcov) with
    | ⟨J, hJ, hsub⟩ => ⟨J, hJ, Set.image_subset_biUnion hsub⟩

theorem isOpen_of_nhds {s : Set X} (h : ∀ a ∈ s, ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) :
    IsOpen s := by
  have heq : s = ⋃₀ {W | IsOpen W ∧ W ⊆ s} := by
    apply Set.ext
    intro a
    constructor
    · intro ha
      have ⟨W, hW, haW, hWs⟩ := h a ha
      exact ⟨W, ⟨hW, hWs⟩, haW⟩
    · intro ⟨W, hW, haW⟩
      exact hW.right a haW
  rw [heq]
  exact isOpen_sUnion _ fun _ hW => hW.left

example {s : Set X} (h : ∀ a ∈ s, ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) :
    IsOpen s :=
  have heq : s = ⋃₀ {W | IsOpen W ∧ W ⊆ s} :=
    Set.ext fun a =>
      ⟨fun ha =>
        match h a ha with
        | ⟨W, hW, haW, hWs⟩ => ⟨W, ⟨hW, hWs⟩, haW⟩,
       fun ⟨_, hW, haW⟩ => hW.right a haW⟩
  heq ▸ isOpen_sUnion _ fun _ hW => hW.left

structure SeparatingPair (y : Y) where

  left : Set Y

  right : Set Y
  isOpen_left : IsOpen left
  isOpen_right : IsOpen right
  mem_right : y ∈ right
  disjoint : left ∩ right = ∅

theorem IsCompact.exists_disjoint_nhds [Hausdorff Y] {K : Set Y} (hK : IsCompact K)
    {y : Y} (hy : y ∉ K) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K := by

  have hcov : K ⊆ Set.iUnion fun i : SeparatingPair y => i.left := fun x hx => by
    have hne : x ≠ y := fun h => hy (h ▸ hx)
    have ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := Hausdorff.separate x y hne
    exact ⟨⟨U, V, hU, hV, hyV, hUV⟩, hxU⟩

  have ⟨J, hJ, hsub⟩ := hK (fun i : SeparatingPair y => i.left) (fun i => i.isOpen_left) hcov

  have ⟨n, g, hg⟩ := hJ
  refine ⟨Set.interFin n fun k => (g k).right, ?_, ?_, ?_⟩
  ·
    exact isOpen_interFin n _ fun k => (g k).isOpen_right
  ·
    exact Set.mem_interFin n _ y fun k => (g k).mem_right
  ·
    intro a ha haK
    have ⟨i, hiJ, hai⟩ := hsub a haK
    have ⟨k, hk⟩ := hg i hiJ
    have hav : a ∈ (g k).right := Set.interFin_mem n _ a ha k
    have hau : a ∈ (g k).left := by rw [hk]; exact hai
    have hmem : a ∈ (g k).left ∩ (g k).right := ⟨hau, hav⟩
    rw [(g k).disjoint] at hmem
    exact hmem

example [Hausdorff Y] {K : Set Y} (hK : IsCompact K)
    {y : Y} (hy : y ∉ K) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K :=
  have hcov : K ⊆ Set.iUnion fun i : SeparatingPair y => i.left := fun x hx =>
    have hne : x ≠ y := fun h => hy (h ▸ hx)
    match Hausdorff.separate x y hne with
    | ⟨U, V, hU, hV, hxU, hyV, hUV⟩ => ⟨⟨U, V, hU, hV, hyV, hUV⟩, hxU⟩
  match hK (fun i : SeparatingPair y => i.left) (fun i => i.isOpen_left) hcov with
  | ⟨_, hJ, hsub⟩ =>
    match hJ with
    | ⟨n, g, hg⟩ =>
      ⟨Set.interFin n fun k => (g k).right,
       isOpen_interFin n _ fun k => (g k).isOpen_right,
       Set.mem_interFin n _ y fun k => (g k).mem_right,
       fun a ha haK =>
         match hsub a haK with
         | ⟨i, hiJ, hai⟩ =>
           match hg i hiJ with
           | ⟨k, hk⟩ =>
             have hav : a ∈ (g k).right := Set.interFin_mem n _ a ha k
             have hau : a ∈ (g k).left := hk ▸ hai
             have hmem : a ∈ (g k).left ∩ (g k).right := ⟨hau, hav⟩
             ((g k).disjoint ▸ hmem : a ∈ (∅ : Set Y))⟩

theorem IsCompact.isClosed [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K := by
  show IsOpen (Kᶜ : Set Y)
  refine isOpen_of_nhds fun y hy => ?_
  have ⟨W, hW, hyW, hWK⟩ := hK.exists_disjoint_nhds hy
  exact ⟨W, hW, hyW, hWK⟩

example [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K :=
  isOpen_of_nhds fun _ hy => hK.exists_disjoint_nhds hy

theorem Set.univ_subset_iUnion_union_compl {α : Type} {C : Set α} {I : Type} {U : I → Set α}
    (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
    (Set.univ : Set α) ⊆ ⋃ i, U i ∪ Cᶜ := by
  intro x _
  by_cases hx : x ∈ C
  · have ⟨i, hi⟩ := hcov x hx
    exact ⟨i, Or.inl hi⟩
  · have ⟨i⟩ := hI
    exact ⟨i, Or.inr hx⟩

example {α : Type} {C : Set α} {I : Type} {U : I → Set α}
    (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
    (Set.univ : Set α) ⊆ ⋃ i, U i ∪ Cᶜ :=
  fun x _ =>
    (Classical.em (x ∈ C)).elim
      (fun hx => match hcov x hx with | ⟨i, hi⟩ => ⟨i, Or.inl hi⟩)
      (fun hx => match hI with | ⟨i⟩ => ⟨i, Or.inr hx⟩)

theorem Set.subset_biUnion_of_compl {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i := by
  intro x hx
  have ⟨i, hiJ, hi⟩ := hsub x trivial
  cases hi with
  | inl h => exact ⟨i, hiJ, h⟩
  | inr h => exact (h hx).elim

example {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i :=
  fun x hx =>
    match hsub x trivial with
    | ⟨i, hiJ, Or.inl h⟩ => ⟨i, hiJ, h⟩
    | ⟨_, _, Or.inr h⟩ => (h hx).elim

theorem IsClosed.isCompact [CompactSpace X] {C : Set X} (hC : IsClosed C) : IsCompact C := by
  intro I U hU hcov
  by_cases hI : Nonempty I
  · have ⟨J, hJ, hsub⟩ :=
      CompactSpace.isCompact_univ (fun i => U i ∪ Cᶜ)
        (fun i => isOpen_union (hU i) hC)
        (Set.univ_subset_iUnion_union_compl hcov hI)
    exact ⟨J, hJ, Set.subset_biUnion_of_compl hsub⟩
  ·
    refine ⟨∅, Set.Finite.empty, ?_⟩
    intro x hx
    have ⟨i, _⟩ := hcov x hx
    exact (hI ⟨i⟩).elim

example [CompactSpace X] {C : Set X} (hC : IsClosed C) : IsCompact C :=
  fun {I} U hU hcov =>
    (Classical.em (Nonempty I)).elim
      (fun hI =>
        match CompactSpace.isCompact_univ (fun i => U i ∪ Cᶜ)
            (fun i => isOpen_union (hU i) hC)
            (Set.univ_subset_iUnion_union_compl hcov hI) with
        | ⟨J, hJ, hsub⟩ => ⟨J, hJ, Set.subset_biUnion_of_compl hsub⟩)
      (fun hI =>
        ⟨∅, Set.Finite.empty, fun x hx =>
          match hcov x hx with
          | ⟨i, _⟩ => (hI ⟨i⟩).elim⟩)

structure Homeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun

theorem Set.preimage_eq_image {α β : Type} {f : α → β} {g : β → α}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (s : Set α) :
    g ⁻¹' s = f '' s := by
  apply Set.ext
  intro y
  constructor
  ·
    intro hy
    exact ⟨g y, hy, hfg y⟩
  ·
    intro ⟨x, hx, hfx⟩
    show g y ∈ s
    rw [← hfx, hgf]
    exact hx

example {α β : Type} {f : α → β} {g : β → α}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (s : Set α) :
    g ⁻¹' s = f '' s :=
  Set.ext fun y =>
    ⟨fun hy => ⟨g y, hy, hfg y⟩,
     fun ⟨x, hx, hfx⟩ =>
      have h1 : g (f x) ∈ s := (hgf x).symm ▸ hx
      (hfx ▸ h1 : g y ∈ s)⟩

theorem isClosed_compl {s : Set X} (hs : IsOpen s) : IsClosed sᶜ := by
  show IsOpen (sᶜᶜ : Set X)
  rw [Set.compl_compl]
  exact hs

example {s : Set X} (hs : IsOpen s) : IsClosed sᶜ :=
  ((Set.compl_compl s).symm ▸ hs : IsOpen sᶜᶜ)

theorem continuous_invFun [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g := by
  intro s hs

  have hcC : IsClosed (sᶜ : Set X) := isClosed_compl hs
  have hcpt : IsCompact (sᶜ : Set X) := hcC.isCompact
  have himg : IsCompact (f '' (sᶜ : Set X)) := hcpt.image hf
  have hcl : IsClosed (f '' (sᶜ : Set X)) := himg.isClosed

  have heq : g ⁻¹' s = (f '' (sᶜ : Set X))ᶜ := by
    rw [← Set.preimage_eq_image hgf hfg (sᶜ : Set X)]
    exact (Set.compl_compl _).symm
  rw [heq]
  exact hcl

example [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g :=
  fun s hs =>
    have hcC : IsClosed (sᶜ : Set X) := isClosed_compl hs
    have hcpt : IsCompact (sᶜ : Set X) := hcC.isCompact
    have himg : IsCompact (f '' (sᶜ : Set X)) := hcpt.image hf
    have hcl : IsClosed (f '' (sᶜ : Set X)) := himg.isClosed
    have h1 : g ⁻¹' (sᶜ : Set X) = f '' (sᶜ : Set X) :=
      Set.preimage_eq_image hgf hfg _
    have heq : g ⁻¹' s = (f '' (sᶜ : Set X))ᶜ :=
      (Set.compl_compl (g ⁻¹' s)).symm.trans (congrArg (·ᶜ) h1)
    heq ▸ hcl

noncomputable def Homeomorph.ofContinuousBijective [CompactSpace X] [Hausdorff Y]
    (f : X → Y) (hf : Continuous f) (hbij : Function.Bijective f) : Homeomorph X Y where
  toFun := f
  invFun := fun y => Classical.choose (hbij.surjective y)
  left_inv := fun x => hbij.injective (Classical.choose_spec (hbij.surjective (f x)))
  right_inv := fun y => Classical.choose_spec (hbij.surjective y)
  continuous_toFun := hf
  continuous_invFun :=
    _root_.continuous_invFun hf
      (fun x => hbij.injective (Classical.choose_spec (hbij.surjective (f x))))
      (fun y => Classical.choose_spec (hbij.surjective y))

end

-- ─── 11_Covering（解答） ───
section

structure SGraph where
  V : Type
  E : Type
  init : E → V
  bar : E → E
  bar_bar : ∀ e, bar (bar e) = e
  bar_ne : ∀ e, bar e ≠ e

namespace SGraph

variable {G : SGraph}

def term (G : SGraph) (e : G.E) : G.V := G.init (G.bar e)

theorem term_bar (e : G.E) : G.term (G.bar e) = G.init e := by
  rw [term, G.bar_bar]

inductive Wf (G : SGraph) : G.V → List G.E → G.V → Prop
  | nil (v : G.V) : Wf G v [] v
  | cons (e : G.E) {l : List G.E} {w : G.V} :
      Wf G (G.term e) l w → Wf G (G.init e) (e :: l) w

theorem Wf.nil_inv {v w : G.V} (h : Wf G v [] w) : v = w := by
  cases h with
  | nil => rfl

theorem Wf.cons_inv {v w : G.V} {e : G.E} {l : List G.E} (h : Wf G v (e :: l) w) :
    v = G.init e ∧ Wf G (G.term e) l w := by
  cases h with
  | cons _ h' => exact ⟨rfl, h'⟩

theorem Wf.append {v u w : G.V} : ∀ {l₁ l₂ : List G.E},
    Wf G v l₁ u → Wf G u l₂ w → Wf G v (l₁ ++ l₂) w
  | _, _, .nil _, h₂ => h₂
  | _, _, .cons e h₁, h₂ => .cons e (Wf.append h₁ h₂)

theorem Wf.end_unique : ∀ {y w₁ w₂ : G.V} {m : List G.E},
    Wf G y m w₁ → Wf G y m w₂ → w₁ = w₂
  | _, _, _, _, .nil _, h₂ => Wf.nil_inv h₂
  | _, _, _, _, .cons _ h₁, h₂ => Wf.end_unique h₁ (Wf.cons_inv h₂).2

theorem Wf.append_split : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E},
    Wf G v (l₁ ++ l₂) w → ∃ u, Wf G v l₁ u ∧ Wf G u l₂ w
  | _, _, [], _, h => ⟨_, .nil _, h⟩
  | _, _, e :: l₁, _, h => by
      have hi := Wf.cons_inv h
      match Wf.append_split l₁ hi.2 with
      | ⟨u, h₁, h₂⟩ =>
        refine ⟨u, ?_, h₂⟩
        rw [hi.1]
        exact Wf.cons e h₁

def revWord (G : SGraph) (l : List G.E) : List G.E := (l.map G.bar).reverse

theorem revWord_cons (e : G.E) (l : List G.E) :
    revWord G (e :: l) = revWord G l ++ [G.bar e] := by
  simp [revWord]

theorem revWord_append (l l' : List G.E) :
    revWord G (l ++ l') = revWord G l' ++ revWord G l := by
  simp [revWord]

theorem Wf.revWord : ∀ {v w : G.V} {l : List G.E},
    Wf G v l w → Wf G w (SGraph.revWord G l) v
  | _, _, _, .nil v => .nil v
  | _, _, _, .cons e h => by
      rw [revWord_cons]
      have s : Wf G (G.term e) [G.bar e] (G.term (G.bar e)) := Wf.cons (G.bar e) (.nil _)
      rw [term_bar] at s
      exact (Wf.revWord h).append s

end SGraph

def bouquet : SGraph where
  V := Unit
  E := Bool
  init _ := ()
  bar := Bool.not
  bar_bar := by decide
  bar_ne := by decide

instance : DecidableEq bouquet.E := inferInstanceAs (DecidableEq Bool)

def zcover : SGraph where
  V := Int
  E := Int × Bool
  init e := cond e.2 e.1 (e.1 + 1)
  bar e := (e.1, !e.2)
  bar_bar e := by cases e with | mk i b => simp
  bar_ne := by
    intro e h
    cases e with
    | mk i b => cases b <;> simp at h

namespace SGraph

variable {G : SGraph}

def IsReduced : List G.E → Prop
  | [] => True
  | [_] => True
  | e :: f :: l => f ≠ G.bar e ∧ IsReduced (f :: l)

theorem IsReduced.tail : ∀ {l : List G.E} {e : G.E}, IsReduced (e :: l) → IsReduced l
  | [], _, _ => trivial
  | _ :: _, _, h => h.2

inductive Homotopic (G : SGraph) : List G.E → List G.E → Prop
  | cancel (l₁ l₂ : List G.E) (e : G.E) :
      Homotopic G (l₁ ++ e :: G.bar e :: l₂) (l₁ ++ l₂)
  | refl (l : List G.E) : Homotopic G l l
  | symm {l l' : List G.E} : Homotopic G l l' → Homotopic G l' l
  | trans {l l' l'' : List G.E} :
      Homotopic G l l' → Homotopic G l' l'' → Homotopic G l l''

inductive Reduces (G : SGraph) : List G.E → List G.E → Prop
  | cancel (l₁ l₂ : List G.E) (e : G.E) :
      Reduces G (l₁ ++ e :: G.bar e :: l₂) (l₁ ++ l₂)
  | refl (l : List G.E) : Reduces G l l
  | trans {l l' l'' : List G.E} :
      Reduces G l l' → Reduces G l' l'' → Reduces G l l''

theorem Reduces.toHomotopic {l l' : List G.E} (h : Reduces G l l') :
    Homotopic G l l' := by
  induction h with
  | cancel l₁ l₂ e => exact .cancel l₁ l₂ e
  | refl l => exact .refl l
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Reduces.cons {l l' : List G.E} (e : G.E) (h : Reduces G l l') :
    Reduces G (e :: l) (e :: l') := by
  induction h with
  | cancel l₁ l₂ f => exact .cancel (e :: l₁) l₂ f
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

section Reduce

variable [DecidableEq G.E]

def rcons (e : G.E) : List G.E → List G.E
  | [] => [e]
  | f :: r => if f = G.bar e then r else e :: f :: r

theorem rcons_nil (e : G.E) : rcons e ([] : List G.E) = [e] := rfl

theorem rcons_cons (e f : G.E) (r : List G.E) :
    rcons e (f :: r) = if f = G.bar e then r else e :: f :: r := rfl

def reduce : List G.E → List G.E
  | [] => []
  | e :: l => rcons e (reduce l)

theorem reduce_cons (e : G.E) (l : List G.E) : reduce (e :: l) = rcons e (reduce l) := rfl

theorem isReduced_rcons {e : G.E} : ∀ {m : List G.E}, IsReduced m → IsReduced (rcons e m)
  | [], _ => trivial
  | f :: r, hm => by
      rw [rcons_cons]
      by_cases h : f = G.bar e
      · rw [if_pos h]; exact hm.tail
      · rw [if_neg h]; exact ⟨h, hm⟩

theorem reduce_isReduced : ∀ l : List G.E, IsReduced (reduce l)
  | [] => trivial
  | _ :: l => isReduced_rcons (reduce_isReduced l)

theorem rcons_rcons_bar (e : G.E) : ∀ (m : List G.E), IsReduced m →
    rcons e (rcons (G.bar e) m) = m
  | [], _ => by rw [rcons_nil, rcons_cons, if_pos rfl]
  | f :: r, hm => by
      rw [rcons_cons]
      by_cases h : f = G.bar (G.bar e)
      · rw [if_pos h]
        rw [G.bar_bar] at h
        subst h
        match r, hm with
        | [], _ => rw [rcons_nil]
        | g :: r', hm => rw [rcons_cons, if_neg hm.1]
      · rw [if_neg h, rcons_cons, if_pos rfl]

theorem reduce_append_cancel (e : G.E) : ∀ (l₁ l₂ : List G.E),
    reduce (l₁ ++ e :: G.bar e :: l₂) = reduce (l₁ ++ l₂)
  | [], l₂ => by
      rw [List.nil_append, List.nil_append, reduce_cons, reduce_cons]
      exact rcons_rcons_bar e (reduce l₂) (reduce_isReduced l₂)
  | x :: l₁, l₂ => by
      rw [List.cons_append, List.cons_append, reduce_cons, reduce_cons,
        reduce_append_cancel e l₁ l₂]

theorem reduces_cons_rcons (e : G.E) (m : List G.E) :
    Reduces G (e :: m) (rcons e m) := by
  match m with
  | [] => exact .refl _
  | f :: r =>
    by_cases h : f = G.bar e
    · subst h
      rw [rcons_cons, if_pos rfl]
      exact Reduces.cancel [] r e
    · rw [rcons_cons, if_neg h]
      exact .refl _

theorem reduces_reduce : ∀ l : List G.E, Reduces G l (reduce l)
  | [] => .refl _
  | e :: l => by
      rw [reduce_cons]
      exact .trans (Reduces.cons e (reduces_reduce l)) (reduces_cons_rcons e (reduce l))

theorem homotopic_iff_reduce_eq {l l' : List G.E} :
    Homotopic G l l' ↔ reduce l = reduce l' := by
  constructor
  · intro h
    induction h with
    | cancel l₁ l₂ e => exact reduce_append_cancel e l₁ l₂
    | refl l => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    have h₁ := (reduces_reduce l).toHomotopic
    have h₂ := (reduces_reduce l').toHomotopic
    rw [h] at h₁
    exact h₁.trans h₂.symm

theorem reduce_eq_self_of_isReduced : ∀ {l : List G.E}, IsReduced l → reduce l = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by
      rw [reduce_cons, reduce_eq_self_of_isReduced h.2, rcons_cons, if_neg h.1]

theorem eq_of_homotopic_of_isReduced {l l' : List G.E}
    (hl : IsReduced l) (hl' : IsReduced l') (h : Homotopic G l l') : l = l' := by
  rw [← reduce_eq_self_of_isReduced hl, ← reduce_eq_self_of_isReduced hl']
  exact homotopic_iff_reduce_eq.mp h

end Reduce

theorem Wf.of_append_cancel : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E} {e : G.E},
    Wf G v (l₁ ++ e :: G.bar e :: l₂) w → Wf G v (l₁ ++ l₂) w
  | _, _, [], _, _, h => by
      have h₁ := Wf.cons_inv h
      have h₂ := Wf.cons_inv h₁.2
      have h₃ := h₂.2
      rw [term_bar] at h₃
      rw [h₁.1]
      exact h₃
  | _, _, _ :: l₁, _, _, h => by
      have hi := Wf.cons_inv h
      rw [hi.1]
      exact .cons _ (Wf.of_append_cancel l₁ hi.2)

theorem Wf.of_reduces {v w : G.V} {l l' : List G.E} (h : Reduces G l l') :
    Wf G v l w → Wf G v l' w := by
  induction h with
  | cancel l₁ l₂ e => exact fun hw => Wf.of_append_cancel l₁ hw
  | refl l => exact id
  | trans _ _ ih₁ ih₂ => exact fun hw => ih₂ (ih₁ hw)

theorem Wf.reduce [DecidableEq G.E] {v w : G.V} {l : List G.E} (hw : Wf G v l w) :
    Wf G v (SGraph.reduce l) w :=
  Wf.of_reduces (reduces_reduce l) hw

end SGraph

example : SGraph.reduce (G := bouquet) [true, false, true] = [true] := rfl
example : SGraph.reduce (G := bouquet) [true, true, false, false] = [] := rfl

namespace SGraph

variable {G : SGraph}

theorem Homotopic.appendRight {l l' : List G.E} (r : List G.E)
    (h : Homotopic G l l') : Homotopic G (l ++ r) (l' ++ r) := by
  induction h with
  | cancel l₁ l₂ e =>
      rw [List.append_assoc, List.append_assoc]
      exact .cancel l₁ (l₂ ++ r) e
  | refl l => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Homotopic.appendLeft (r : List G.E) {l l' : List G.E}
    (h : Homotopic G l l') : Homotopic G (r ++ l) (r ++ l') := by
  induction h with
  | cancel l₁ l₂ e =>
      rw [← List.append_assoc, ← List.append_assoc]
      exact .cancel (r ++ l₁) l₂ e
  | refl l => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Homotopic.revWordCong {l l' : List G.E} (h : Homotopic G l l') :
    Homotopic G (revWord G l) (revWord G l') := by
  induction h with
  | cancel l₁ l₂ e =>
      have lhs : revWord G (l₁ ++ e :: G.bar e :: l₂) =
          revWord G l₂ ++ e :: G.bar e :: revWord G l₁ := by
        simp [revWord_append, revWord_cons, G.bar_bar, List.append_assoc]
      rw [lhs, revWord_append]
      exact .cancel (revWord G l₂) (revWord G l₁) e
  | refl l => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem homotopic_revWord_append : ∀ l : List G.E, Homotopic G (revWord G l ++ l) []
  | [] => .refl _
  | e :: l => by
      rw [revWord_cons, List.append_assoc]
      have step : Homotopic G (revWord G l ++ (G.bar e :: e :: l)) (revWord G l ++ l) := by
        have h := Homotopic.cancel (G := G) (revWord G l) l (G.bar e)
        rw [G.bar_bar] at h
        exact h
      exact .trans step (homotopic_revWord_append l)

theorem homotopic_append_revWord : ∀ l : List G.E, Homotopic G (l ++ revWord G l) []
  | [] => .refl _
  | e :: l => by
      rw [revWord_cons, ← List.append_assoc]
      have h1 : Homotopic G ((l ++ revWord G l) ++ [G.bar e]) ([] ++ [G.bar e]) :=
        Homotopic.appendRight _ (homotopic_append_revWord l)
      have h2 := Homotopic.appendLeft [e] h1
      exact .trans h2 (Homotopic.cancel [] [] e)

def PathClass (G : SGraph) (v w : G.V) : Type :=
  Quot (fun a b : {l : List G.E // Wf G v l w} => Homotopic G a.1 b.1)

namespace PathClass

def mk {v w : G.V} {l : List G.E} (hl : Wf G v l w) : PathClass G v w :=
  Quot.mk _ ⟨l, hl⟩

theorem mk_eq_of_eq {v w : G.V} {l l' : List G.E}
    (h : l = l') (hl : Wf G v l w) (hl' : Wf G v l' w) : mk hl = mk hl' := by
  subst h; rfl

theorem sound {v w : G.V} {l l' : List G.E}
    (hl : Wf G v l w) (hl' : Wf G v l' w) (h : Homotopic G l l') : mk hl = mk hl' :=
  Quot.sound h

def refl (v : G.V) : PathClass G v v := mk (Wf.nil v)

def comp {v u w : G.V} (φ : PathClass G v u) (ψ : PathClass G u w) : PathClass G v w :=
  Quot.lift
    (fun a => Quot.lift (fun b => mk (Wf.append a.2 b.2))
      (fun _ _ hb => Quot.sound (Homotopic.appendLeft a.1 hb)) ψ)
    (fun _ _ ha => by
      induction ψ using Quot.ind with
      | mk b =>
        apply Quot.sound
        exact Homotopic.appendRight b.1 ha)
    φ

def inv {v w : G.V} (φ : PathClass G v w) : PathClass G w v :=
  Quot.lift (fun a => mk a.2.revWord)
    (fun _ _ h => Quot.sound (Homotopic.revWordCong h)) φ

variable {v w : G.V}

theorem refl_comp (γ : PathClass G v w) : (refl v).comp γ = γ := by
  induction γ using Quot.ind with
  | mk a => exact mk_eq_of_eq (List.nil_append a.1) (Wf.append (.nil v) a.2) a.2

theorem comp_refl (γ : PathClass G v w) : γ.comp (refl w) = γ := by
  induction γ using Quot.ind with
  | mk a => exact mk_eq_of_eq (List.append_nil a.1) (Wf.append a.2 (.nil w)) a.2

theorem comp_assoc {u z : G.V} (γ : PathClass G v u) (δ : PathClass G u w)
    (ε : PathClass G w z) : (γ.comp δ).comp ε = γ.comp (δ.comp ε) := by
  induction γ using Quot.ind with
  | mk a =>
    induction δ using Quot.ind with
    | mk b =>
      induction ε using Quot.ind with
      | mk c =>
        exact mk_eq_of_eq (List.append_assoc a.1 b.1 c.1)
          (Wf.append (Wf.append a.2 b.2) c.2) (Wf.append a.2 (Wf.append b.2 c.2))

theorem inv_comp (γ : PathClass G v w) : γ.inv.comp γ = refl w := by
  induction γ using Quot.ind with
  | mk a =>
    exact sound (Wf.append a.2.revWord a.2) (.nil w) (homotopic_revWord_append a.1)

theorem comp_inv (γ : PathClass G v w) : γ.comp γ.inv = refl v := by
  induction γ using Quot.ind with
  | mk a =>
    exact sound (Wf.append a.2 a.2.revWord) (.nil v) (homotopic_append_revWord a.1)

end PathClass

end SGraph

namespace SGraph

structure GraphHom (Y X : SGraph) where
  toV : Y.V → X.V
  toE : Y.E → X.E
  init_toE : ∀ e, X.init (toE e) = toV (Y.init e)
  bar_toE : ∀ e, X.bar (toE e) = toE (Y.bar e)

variable {Y X : SGraph}

theorem GraphHom.term_toE (p : GraphHom Y X) (e : Y.E) :
    X.term (p.toE e) = p.toV (Y.term e) := by
  rw [term, p.bar_toE, p.init_toE]
  rfl

structure Covering (Y X : SGraph) extends GraphHom Y X where
  star_surj : ∀ (y : Y.V) (f : X.E), X.init f = toV y →
    ∃ e : Y.E, Y.init e = y ∧ toE e = f
  star_inj : ∀ e e' : Y.E, Y.init e = Y.init e' → toE e = toE e' → e = e'

def mapWord {A B : Type} (f : A → B) (m : List A) : List B := m.map f

theorem mapWord_nil {A B : Type} (f : A → B) : mapWord f [] = [] := rfl

theorem mapWord_cons {A B : Type} (f : A → B) (a : A) (m : List A) :
    mapWord f (a :: m) = f a :: mapWord f m := rfl

theorem mapWord_append {A B : Type} (f : A → B) (m m' : List A) :
    mapWord f (m ++ m') = mapWord f m ++ mapWord f m' := by
  simp [mapWord]

theorem mapWord_split {A B : Type} (f : A → B) : ∀ (l₁ : List B) {l₂ : List B}
    {m : List A}, mapWord f m = l₁ ++ l₂ →
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ mapWord f m₁ = l₁ ∧ mapWord f m₂ = l₂
  | [], _, m, h => ⟨[], m, rfl, rfl, h⟩
  | _ :: _, _, [], h => by simp [mapWord] at h
  | _ :: l₁, _, a :: _, h => by
      rw [mapWord_cons] at h
      injection h with h1 h2
      match mapWord_split f l₁ h2 with
      | ⟨m₁, m₂, hm, hmap₁, hmap₂⟩ =>
        refine ⟨a :: m₁, m₂, by rw [hm]; rfl, ?_, hmap₂⟩
        rw [mapWord_cons, h1, hmap₁]

end SGraph

open SGraph in

def zcoverCovering : Covering zcover bouquet where
  toV _ := ()
  toE e := e.2
  init_toE _ := rfl
  bar_toE _ := rfl
  star_surj := by
    intro y f _
    cases f with
    | true => exact ⟨(y, true), rfl, rfl⟩
    | false =>
        have key : ∀ j : Int, ∃ i : Int, i + 1 = j := fun j => ⟨j - 1, by omega⟩
        match key y with
        | ⟨i, hi⟩ => exact ⟨(i, false), hi, rfl⟩
  star_inj := by
    intro e e' hinit hmap
    cases e with
    | mk i b =>
      cases e' with
      | mk i' b' =>
        have hb : b = b' := hmap
        subst hb
        cases b with
        | true =>
            have h : i = i' := hinit
            rw [h]
        | false =>
            have h : i + 1 = i' + 1 := hinit
            have h' : i = i' := by omega
            rw [h']

namespace SGraph.Covering

variable {Y X : SGraph} (p : Covering Y X)

theorem exists_lift_word :
    ∀ (l : List X.E) (y : Y.V) {w : X.V}, Wf X (p.toV y) l w →
      ∃ w' : Y.V, ∃ m : List Y.E, Wf Y y m w' ∧ mapWord p.toE m = l ∧ p.toV w' = w
  | [], y, _, h => ⟨y, [], .nil y, rfl, Wf.nil_inv h⟩
  | f :: l, y, w, h => by
      have hi := Wf.cons_inv h
      match p.star_surj y f hi.1.symm with
      | ⟨e, he_init, he_map⟩ =>
        have hterm : p.toV (Y.term e) = X.term f := by
          rw [← p.term_toE, he_map]
        have h2 : Wf X (p.toV (Y.term e)) l w := by rw [hterm]; exact hi.2
        match exists_lift_word l (Y.term e) h2 with
        | ⟨w', m, hm, hmap, hw⟩ =>
          refine ⟨w', e :: m, ?_, ?_, hw⟩
          · rw [← he_init]
            exact Wf.cons e hm
          · rw [mapWord_cons, he_map, hmap]

theorem lift_word_unique :
    ∀ {m m' : List Y.E} {y w₁ w₂ : Y.V},
      Wf Y y m w₁ → Wf Y y m' w₂ → mapWord p.toE m = mapWord p.toE m' → m = m'
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, hmap => by simp [mapWord] at hmap
  | _ :: _, [], _, _, _, _, _, hmap => by simp [mapWord] at hmap
  | e :: _, e' :: _, _, _, _, h₁, h₂, hmap => by
      have hi₁ := Wf.cons_inv h₁
      have hi₂ := Wf.cons_inv h₂
      rw [mapWord_cons, mapWord_cons] at hmap
      injection hmap with hh ht
      have he : e = e' := p.star_inj e e' (hi₁.1.symm.trans hi₂.1) hh
      subst he
      rw [lift_word_unique hi₁.2 hi₂.2 ht]

theorem endpoint_of_reduces :
    ∀ {l l' : List X.E}, Reduces X l l' →
      ∀ {y b : Y.V} {m : List Y.E}, Wf Y y m b → mapWord p.toE m = l →
        ∃ m' : List Y.E, Wf Y y m' b ∧ mapWord p.toE m' = l'
  | _, _, .refl _, _, _, m, hm, hmap => ⟨m, hm, hmap⟩
  | _, _, .trans h₁ h₂, _, _, _, hm, hmap => by
      match endpoint_of_reduces h₁ hm hmap with
      | ⟨_, hm₁, hmap₁⟩ => exact endpoint_of_reduces h₂ hm₁ hmap₁
  | _, _, .cancel l₁ _ _, _, _, _, hm, hmap => by
      match mapWord_split p.toE l₁ hmap with
      | ⟨m₁, m₂, hmeq, hmap₁, hmap₂⟩ =>
        subst hmeq
        match m₂, hm, hmap₂ with
        | [], _, hmap₂ => simp [mapWord] at hmap₂
        | [_], _, hmap₂ => simp [mapWord] at hmap₂
        | ê :: g :: m₃, hm, hmap₂ =>
            rw [mapWord_cons, mapWord_cons] at hmap₂
            injection hmap₂ with h1 h2'
            injection h2' with h2 h3
            match Wf.append_split m₁ hm with
            | ⟨_, hu₁, hu₂⟩ =>
              have hi₁ := Wf.cons_inv hu₂
              have hi₂ := Wf.cons_inv hi₁.2
              have hg : g = Y.bar ê := by
                refine p.star_inj g (Y.bar ê) ?_ ?_
                · exact hi₂.1.symm
                · rw [h2, ← p.bar_toE, h1]
              subst hg
              have hdel := Wf.of_append_cancel [] hu₂
              exact ⟨m₁ ++ m₃, Wf.append hu₁ hdel,
                by rw [mapWord_append, hmap₁, h3]⟩

theorem endpoint_eq {l l' : List X.E}
    (hh : Homotopic X l l') {y b b' : Y.V} {m m' : List Y.E}
    (hm : Wf Y y m b) (hmapm : mapWord p.toE m = l)
    (hm' : Wf Y y m' b') (hmapm' : mapWord p.toE m' = l') : b = b' := by
  letI : DecidableEq X.E := fun _ _ => Classical.propDecidable _
  have hred : SGraph.reduce l = SGraph.reduce l' := homotopic_iff_reduce_eq.mp hh
  match p.endpoint_of_reduces (reduces_reduce l) hm hmapm,
        p.endpoint_of_reduces (reduces_reduce l') hm' hmapm' with
  | ⟨mr, hmr, hmapr⟩, ⟨mr', hmr', hmapr'⟩ =>
    have heq : mr = mr' := p.lift_word_unique hmr hmr' (by rw [hmapr, hmapr', hred])
    subst heq
    exact Wf.end_unique hmr hmr'

abbrev Fiber (v : X.V) : Type := {y : Y.V // p.toV y = v}

theorem fiberExt {v : X.V} {a b : p.Fiber v} (h : a.1 = b.1) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem fiber_wf {v w : X.V} (a : p.Fiber v) {l : List X.E}
    (hl : Wf X v l w) : Wf X (p.toV a.1) l w := by
  rw [a.2]; exact hl

noncomputable def liftEnd {v w : X.V} (a : p.Fiber v) (l : List X.E)
    (hl : Wf X v l w) : p.Fiber w :=
  ⟨Classical.choose (p.exists_lift_word l a.1 (p.fiber_wf a hl)),
   (Classical.choose_spec (Classical.choose_spec
     (p.exists_lift_word l a.1 (p.fiber_wf a hl)))).2.2⟩

theorem liftEnd_spec {v w : X.V} (a : p.Fiber v) {l : List X.E} (hl : Wf X v l w) :
    ∃ m, Wf Y a.1 m (p.liftEnd a l hl).1 ∧ mapWord p.toE m = l :=
  ⟨Classical.choose (Classical.choose_spec (p.exists_lift_word l a.1 (p.fiber_wf a hl))),
   (Classical.choose_spec (Classical.choose_spec
     (p.exists_lift_word l a.1 (p.fiber_wf a hl)))).1,
   (Classical.choose_spec (Classical.choose_spec
     (p.exists_lift_word l a.1 (p.fiber_wf a hl)))).2.1⟩

theorem liftEnd_eq {v w : X.V} (a : p.Fiber v) {l : List X.E} (hl : Wf X v l w)
    {b : Y.V} {m : List Y.E} (hm : Wf Y a.1 m b) (hmap : mapWord p.toE m = l) :
    (p.liftEnd a l hl).1 = b := by
  match p.liftEnd_spec a hl with
  | ⟨M, hM, hMmap⟩ =>
    have heq : M = m := p.lift_word_unique hM hm (by rw [hMmap, hmap])
    subst heq
    exact Wf.end_unique hM hm

noncomputable def transport {v w : X.V} (γ : PathClass X v w) (a : p.Fiber v) :
    p.Fiber w :=
  Quot.lift (fun l => p.liftEnd a l.1 l.2)
    (fun l l' hll' => by
      apply p.fiberExt
      match p.liftEnd_spec a l.2, p.liftEnd_spec a l'.2 with
      | ⟨_, hM, hMmap⟩, ⟨_, hM', hM'map⟩ =>
        exact p.endpoint_eq hll' hM hMmap hM' hM'map)
    γ

theorem transport_refl {v : X.V} (a : p.Fiber v) :
    p.transport (PathClass.refl v) a = a := by
  apply p.fiberExt
  exact p.liftEnd_eq a (.nil v) (.nil a.1) rfl

theorem transport_trans {v u w : X.V}
    (γ : PathClass X v u) (δ : PathClass X u w) (a : p.Fiber v) :
    p.transport (γ.comp δ) a = p.transport δ (p.transport γ a) := by
  induction γ using Quot.ind with
  | mk lg =>
    induction δ using Quot.ind with
    | mk ld =>
      apply p.fiberExt
      match p.liftEnd_spec a lg.2 with
      | ⟨m₁, hm₁, hmap₁⟩ =>
        match p.liftEnd_spec (p.liftEnd a lg.1 lg.2) ld.2 with
        | ⟨m₂, hm₂, hmap₂⟩ =>
          exact p.liftEnd_eq a (Wf.append lg.2 ld.2) (Wf.append hm₁ hm₂)
            (by rw [mapWord_append, hmap₁, hmap₂])

theorem transport_bijective {v w : X.V} (γ : PathClass X v w) :
    Function.Bijective (p.transport γ) where
  injective := by
    intro a b h
    have h' := congrArg (p.transport γ.inv) h
    rw [← p.transport_trans, ← p.transport_trans, PathClass.comp_inv,
      p.transport_refl, p.transport_refl] at h'
    exact h'
  surjective := by
    intro b
    refine ⟨p.transport γ.inv b, ?_⟩
    rw [← p.transport_trans, PathClass.inv_comp, p.transport_refl]

end SGraph.Covering

open SGraph

def loopWf : Wf bouquet () [true] () :=
  Wf.cons (G := bouquet) true (Wf.nil (bouquet.term true))

example (i : Int) :
    (zcoverCovering.transport (PathClass.mk loopWf) ⟨i, rfl⟩).1 = i + 1 :=
  zcoverCovering.liftEnd_eq ⟨i, rfl⟩ loopWf
    (Wf.cons (G := zcover) ((i, true) : Int × Bool) (Wf.nil (zcover.term (i, true)))) rfl

theorem mapWord_reduces {Y X : SGraph} (p : GraphHom Y X) {m m' : List Y.E}
    (h : Reduces Y m m') : Reduces X (mapWord p.toE m) (mapWord p.toE m') := by
  induction h with
  | cancel m₁ m₂ e =>
      rw [mapWord_append, mapWord_cons, mapWord_cons, ← p.bar_toE, mapWord_append]
      exact .cancel _ _ _
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem zc_drift : ∀ {m : List zcover.E} {e : zcover.E} {v w : Int},
    Wf zcover v (e :: m) w → IsReduced (e :: m) →
    (e.2 = true ∧ v < w) ∨ (e.2 = false ∧ w < v)
  | [], e, v, w, h, _ => by
      have hi := Wf.cons_inv h
      have hw := Wf.nil_inv hi.2
      cases e with
      | mk i b =>
        cases b with
        | true =>
            refine .inl ⟨rfl, ?_⟩
            have h1 : v = i := hi.1
            have h2 : (i + 1 : Int) = w := hw
            omega
        | false =>
            refine .inr ⟨rfl, ?_⟩
            have h1 : v = i + 1 := hi.1
            have h2 : (i : Int) = w := hw
            omega
  | f :: m, e, v, w, h, hr => by
      have hi := Wf.cons_inv h
      have hrf : f ≠ zcover.bar e := hr.1
      have hstep := zc_drift hi.2 hr.2
      cases e with
      | mk i b =>
        cases f with
        | mk j c =>
          cases b with
          | true =>
              refine .inl ⟨rfl, ?_⟩
              have h1 : v = i := hi.1
              cases hstep with
              | inl hrec =>
                  have h2 : (i + 1 : Int) < w := hrec.2
                  omega
              | inr hrec =>
                  exfalso
                  apply hrf
                  have hc : c = false := hrec.1
                  subst hc
                  have hadj := (Wf.cons_inv hi.2).1
                  have hj : (i + 1 : Int) = j + 1 := hadj
                  have hji : j = i := by omega
                  subst hji
                  rfl
          | false =>
              refine .inr ⟨rfl, ?_⟩
              have h1 : v = i + 1 := hi.1
              cases hstep with
              | inr hrec =>
                  have h2 : w < (i : Int) := hrec.2
                  omega
              | inl hrec =>
                  exfalso
                  apply hrf
                  have hc : c = true := hrec.1
                  subst hc
                  have hadj := (Wf.cons_inv hi.2).1
                  have hj : (i : Int) = j := hadj
                  have hji : j = i := by omega
                  subst hji
                  rfl

theorem zc_reduced_closed : ∀ {m : List zcover.E} {v : Int},
    Wf zcover v m v → IsReduced m → m = []
  | [], _, _, _ => rfl
  | _ :: _, v, h, hr => by
      exfalso
      cases zc_drift h hr with
      | inl h' =>
          have hlt : v < v := h'.2
          omega
      | inr h' =>
          have hlt : v < v := h'.2
          omega

def shiftWord (k : Int) (m : List zcover.E) : List zcover.E :=
  m.map (fun e => (e.1 + k, e.2))

theorem mapWord_shift (k : Int) : ∀ (m : List zcover.E),
    mapWord zcoverCovering.toE (shiftWord k m) = mapWord zcoverCovering.toE m
  | [] => rfl
  | e :: m => congrArg (fun t => e.2 :: t) (mapWord_shift k m)

theorem shift_wf (k : Int) : ∀ (m : List zcover.E) {v w : Int},
    Wf zcover v m w → Wf zcover (v + k) (shiftWord k m) (w + k)
  | [], v, w, h => by
      have hv : v = w := Wf.nil_inv h
      subst hv
      exact Wf.nil (G := zcover) (v + k)
  | e :: m, v, w, h => by
      have hi := Wf.cons_inv h
      have ih := shift_wf k m hi.2
      cases e with
      | mk i b =>
        cases b with
        | true =>
            have h1 : v = i := hi.1
            subst h1
            have ih' : Wf zcover ((v + 1 : Int) + k) (shiftWord k m) (w + k) := ih
            rw [show ((v + 1 : Int) + k) = v + k + 1 from by omega] at ih'
            exact Wf.cons (G := zcover) ((v + k, true) : Int × Bool) ih'
        | false =>
            have h1 : v = i + 1 := hi.1
            subst h1
            rw [show ((i + 1 : Int) + k) = i + k + 1 from by omega]
            have ih' : Wf zcover ((i : Int) + k) (shiftWord k m) (w + k) := ih
            exact Wf.cons (G := zcover) ((i + k, false) : Int × Bool) ih'

abbrev triv : PathClass bouquet () () := PathClass.refl (G := bouquet) ()

def basePt : zcoverCovering.Fiber () := ⟨(0 : Int), rfl⟩

noncomputable def deg (γ : PathClass bouquet () ()) : Int :=
  (zcoverCovering.transport γ basePt).1

theorem transport_apply (γ : PathClass bouquet () ()) (i : Int) :
    (zcoverCovering.transport γ ⟨i, rfl⟩).1 = deg γ + i := by
  induction γ using Quot.ind with
  | mk ld =>
    match zcoverCovering.liftEnd_spec basePt ld.2 with
    | ⟨m, hm, hmap⟩ =>
      have hm' : Wf zcover ((0 : Int) + i) (shiftWord i m)
          (deg (Quot.mk _ ld) + i) := shift_wf i m hm
      rw [show ((0 : Int) + i) = i from by omega] at hm'
      exact zcoverCovering.liftEnd_eq ⟨i, rfl⟩ ld.2 hm'
        ((mapWord_shift i m).trans hmap)

theorem deg_comp (γ δ : PathClass bouquet () ()) :
    deg (γ.comp δ) = deg γ + deg δ := by
  have hfix : zcoverCovering.transport γ basePt = ⟨deg γ, rfl⟩ :=
    zcoverCovering.fiberExt rfl
  have h : deg (γ.comp δ) = deg δ + deg γ := by
    show (zcoverCovering.transport (γ.comp δ) basePt).1 = _
    rw [zcoverCovering.transport_trans γ δ basePt, hfix, transport_apply]
  omega

theorem deg_refl : deg triv = 0 :=
  congrArg Subtype.val (zcoverCovering.transport_refl basePt)

theorem deg_inv (γ : PathClass bouquet () ()) : deg γ.inv = - deg γ := by
  have h := deg_comp γ.inv γ
  rw [PathClass.inv_comp γ, deg_refl] at h
  omega

def loop : PathClass bouquet () () := PathClass.mk loopWf

theorem deg_loop : deg loop = 1 := by
  have h : deg loop = (0 : Int) + 1 :=
    zcoverCovering.liftEnd_eq basePt loopWf
      (Wf.cons (G := zcover) ((0, true) : Int × Bool) (Wf.nil (zcover.term (0, true)))) rfl
  omega

def loopPow : Nat → PathClass bouquet () ()
  | 0 => triv
  | k + 1 => (loopPow k).comp loop

theorem deg_eq_zero {γ : PathClass bouquet () ()} (h : deg γ = 0) :
    γ = triv := by
  induction γ using Quot.ind with
  | mk ld =>
    match zcoverCovering.liftEnd_spec basePt ld.2 with
    | ⟨m, hm, hmap⟩ =>
      have h0 : (zcoverCovering.liftEnd basePt ld.1 ld.2).1 = (0 : Int) := h
      rw [h0] at hm
      have hm0 : Wf zcover (0 : Int) m (0 : Int) := hm
      letI : DecidableEq zcover.E := fun _ _ => Classical.propDecidable _
      have hred : Wf zcover (0 : Int) (SGraph.reduce m) (0 : Int) := Wf.reduce hm0
      have hnil : SGraph.reduce m = [] :=
        zc_reduced_closed hred (reduce_isReduced m)
      have hR : Reduces zcover m [] := hnil ▸ reduces_reduce m
      have hdown := (mapWord_reduces zcoverCovering.toGraphHom hR).toHomotopic
      rw [hmap, mapWord_nil] at hdown
      exact PathClass.sound ld.2 (Wf.nil (G := bouquet) ()) hdown

theorem deg_injective : Function.Injective deg := by
  intro γ δ h
  have hz : deg (γ.comp δ.inv) = 0 := by
    rw [deg_comp, deg_inv]
    omega
  have hker := deg_eq_zero hz
  calc γ = γ.comp triv := (PathClass.comp_refl γ).symm
    _ = γ.comp (δ.inv.comp δ) := congrArg γ.comp (PathClass.inv_comp δ).symm
    _ = (γ.comp δ.inv).comp δ := (PathClass.comp_assoc γ δ.inv δ).symm
    _ = triv.comp δ := by rw [hker]
    _ = δ := PathClass.refl_comp δ

theorem deg_loopPow : ∀ k : Nat, deg (loopPow k) = Int.ofNat k
  | 0 => deg_refl
  | k + 1 => by
      have h := deg_comp (loopPow k) loop
      rw [deg_loopPow k, deg_loop] at h
      exact h

theorem deg_surjective : Function.Surjective deg := by
  intro n
  match n with
  | Int.ofNat k => exact ⟨loopPow k, deg_loopPow k⟩
  | Int.negSucc k =>
      refine ⟨(loopPow (k + 1)).inv, ?_⟩
      rw [deg_inv, deg_loopPow]
      rfl

theorem pi1_bouquet :
    (∀ γ δ : PathClass bouquet () (), deg (γ.comp δ) = deg γ + deg δ) ∧
      Function.Bijective deg :=
  ⟨deg_comp, ⟨deg_injective, deg_surjective⟩⟩

end

-- ─── 07_Exercises（解答） ───
section

@[reducible] def indiscrete (X : Type) : TopologicalSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := by
    intro s t hs ht
    cases hs with
    | inl h =>
      left
      rw [h]
      apply Set.ext
      intro a
      exact ⟨fun h' => h'.1, False.elim⟩
    | inr h =>
      cases ht with
      | inl h' =>
        left
        rw [h, h']
        apply Set.ext
        intro a
        exact ⟨fun h'' => h''.2, False.elim⟩
      | inr h' =>
        right
        rw [h, h']
        apply Set.ext
        intro a
        exact ⟨fun h'' => h''.1, fun h'' => ⟨h'', h''⟩⟩
  isOpen_sUnion := by
    intro S hS
    by_cases h : ∃ s ∈ S, s = Set.univ
    · right
      have ⟨s, hsS, hs⟩ := h
      apply Set.ext
      intro a
      constructor
      · intro _
        trivial
      · intro _
        refine ⟨s, hsS, ?_⟩
        rw [hs]
        trivial
    · left
      apply Set.ext
      intro a
      constructor
      · intro ⟨s, hsS, has⟩
        cases hS s hsS with
        | inl he => rw [he] at has; exact has
        | inr hu => exact absurd ⟨s, hsS, hu⟩ h
      · exact False.elim

theorem continuous_from_discrete {X Y : Type} [tY : TopologicalSpace Y] (f : X → Y) :
    @Continuous X (discrete X) Y tY f :=
  fun _ _ => trivial

theorem continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
    @Continuous X tX Y (indiscrete Y) f := by
  intro s hs
  cases hs with
  | inl h => rw [h]; exact isOpen_empty
  | inr h => rw [h]; exact isOpen_univ

theorem indiscrete_bool_not_hausdorff : ¬ @Hausdorff Bool (indiscrete Bool) := by
  intro h
  have ⟨U, V, _hU, hV, htU, hfV, hUV⟩ := h.separate true false (by decide)

  have hVuniv : V = Set.univ := by
    cases hV with
    | inl he => rw [he] at hfV; exact False.elim hfV
    | inr hu => exact hu

  have htV : (true : Bool) ∈ V := by rw [hVuniv]; trivial
  have hmem : (true : Bool) ∈ U ∩ V := ⟨htU, htV⟩
  rw [hUV] at hmem
  exact hmem

namespace Cat

structure Category where

  Obj : Type 1

  Hom : Obj → Obj → Type

  id : (A : Obj) → Hom A A

  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C

  id_comp : ∀ {A B : Obj} (f : Hom A B), comp (id A) f = f

  comp_id : ∀ {A B : Obj} (f : Hom A B), comp f (id B) = f

  assoc : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp (comp f g) h = comp f (comp g h)

@[reducible] def TypeCat : Category where
  Obj := Type
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

structure TopSpace : Type 1 where

  carrier : Type

  str : TopologicalSpace carrier

attribute [instance] TopSpace.str

@[reducible] def TopCat : Category where
  Obj := TopSpace
  Hom A B := { f : A.carrier → B.carrier // Continuous f }
  id _ := ⟨fun a => a, continuous_id⟩
  comp f g := ⟨fun a => g.val (f.val a), g.property.comp f.property⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

structure Functor (C D : Category) where

  obj : C.Obj → D.Obj

  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)

  map_id : ∀ A : C.Obj, map (C.id A) = D.id (obj A)

  map_comp : ∀ {A B E : C.Obj} (f : C.Hom A B) (g : C.Hom B E),
    map (C.comp f g) = D.comp (map f) (map g)

@[reducible] def forgetful : Functor TopCat TypeCat where
  obj A := A.carrier
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

@[reducible] def discreteFunctor : Functor TypeCat TopCat where
  obj X := ⟨X, discrete X⟩

  map f := ⟨f, continuous_from_discrete (tY := discrete _) f⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

@[reducible] def indiscreteFunctor : Functor TypeCat TopCat where
  obj X := ⟨X, indiscrete X⟩
  map f := ⟨f, continuous_to_indiscrete (tX := indiscrete _) f⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

structure Equiv (α β : Type) where

  toFun : α → β

  invFun : β → α

  left_inv : ∀ a, invFun (toFun a) = a

  right_inv : ∀ b, toFun (invFun b) = b

structure Adjunction {C D : Category} (F : Functor C D) (G : Functor D C) where

  homEquiv : (A : C.Obj) → (B : D.Obj) → Equiv (D.Hom (F.obj A) B) (C.Hom A (G.obj B))

  naturality_left :
    ∀ {A' A : C.Obj} {B : D.Obj} (f : C.Hom A' A) (g : D.Hom (F.obj A) B),
      (homEquiv A' B).toFun (D.comp (F.map f) g) = C.comp f ((homEquiv A B).toFun g)

  naturality_right :
    ∀ {A : C.Obj} {B B' : D.Obj} (g : D.Hom (F.obj A) B) (h : D.Hom B B'),
      (homEquiv A B').toFun (D.comp g h) = C.comp ((homEquiv A B).toFun g) (G.map h)

def discreteAdj : Adjunction discreteFunctor forgetful where
  homEquiv _ _ :=
    { toFun := fun f => f.val
      invFun := fun f => ⟨f, continuous_from_discrete f⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  naturality_left _ _ := rfl
  naturality_right _ _ := rfl

def indiscreteAdj : Adjunction forgetful indiscreteFunctor where
  homEquiv _ _ :=
    { toFun := fun f => ⟨f, continuous_to_indiscrete f⟩
      invFun := fun f => f.val
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  naturality_left _ _ := Subtype.ext rfl
  naturality_right _ _ := Subtype.ext rfl

end Cat

theorem compactSpace_discrete_bool : @CompactSpace Bool (discrete Bool) := by
  refine @CompactSpace.mk Bool (discrete Bool) ?_
  intro I U _ hcov
  have ⟨i₁, h₁⟩ := hcov true trivial
  have ⟨i₂, h₂⟩ := hcov false trivial
  refine ⟨{j | j = i₁ ∨ j = i₂}, ⟨2, fun k => if k.val = 0 then i₁ else i₂, ?_⟩, ?_⟩
  · intro a ha
    cases ha with
    | inl h => exact ⟨⟨0, by omega⟩, by simp [h]⟩
    | inr h => exact ⟨⟨1, by omega⟩, by simp [h]⟩
  · intro b _
    cases b with
    | true => exact ⟨i₁, Or.inl rfl, h₁⟩
    | false => exact ⟨i₂, Or.inr rfl, h₂⟩

theorem not_continuous_id_indiscrete_to_discrete :
    ¬ @Continuous Bool (indiscrete Bool) Bool (discrete Bool) (fun b => b) := by
  intro h
  have hopen := h {b | b = true} trivial
  cases hopen with
  | inl he =>
    have hmem : (true : Bool) ∈ ((fun b : Bool => b) ⁻¹' {b | b = true}) := rfl
    rw [he] at hmem
    exact hmem
  | inr hu =>
    have hmem : (false : Bool) ∈ ((fun b : Bool => b) ⁻¹' {b | b = true}) := by
      rw [hu]
      trivial
    have : false = true := hmem
    exact Bool.noConfusion this

def Set.sInter {α : Type} (S : Set (Set α)) : Set α := {a | ∀ s ∈ S, a ∈ s}

prefix:110 "⋂₀ " => Set.sInter

theorem Set.subset_antisymm {α : Type} {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  Set.ext fun a => ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩

theorem TopologicalSpace.ext' {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : t₁.IsOpen = t₂.IsOpen) : t₁ = t₂ := by
  cases t₁; cases t₂; cases h; rfl

theorem Set.compl_univ {α : Type} : (Set.univ : Set α)ᶜ = ∅ :=
  Set.ext fun _ => ⟨fun h => h trivial, fun h => False.elim h⟩

theorem Set.compl_empty {α : Type} : (∅ : Set α)ᶜ = Set.univ :=
  Set.ext fun _ => ⟨fun _ => trivial, fun _ h => h⟩

theorem Set.compl_union {α : Type} (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  Set.ext fun _ => ⟨fun h => ⟨fun hs => h (Or.inl hs), fun ht => h (Or.inr ht)⟩,
    fun h hu => match hu with | Or.inl hs => h.1 hs | Or.inr ht => h.2 ht⟩

theorem Set.compl_inter {α : Type} (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  apply Set.ext
  intro a
  constructor
  · intro h
    by_cases hs : a ∈ s
    · exact Or.inr fun ht => h ⟨hs, ht⟩
    · exact Or.inl hs
  · intro h hc
    cases h with
    | inl h => exact h hc.1
    | inr h => exact h hc.2

theorem Set.compl_sUnion {α : Type} (S : Set (Set α)) :
    (⋃₀ S)ᶜ = ⋂₀ (Set.compl '' S) := by
  apply Set.ext
  intro a
  constructor
  · intro h u hu
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    intro has
    exact h ⟨s, hsS, has⟩
  · intro h ⟨s, hsS, has⟩
    exact h sᶜ ⟨s, hsS, rfl⟩ has

theorem Set.compl_sInter {α : Type} (S : Set (Set α)) :
    (⋂₀ S)ᶜ = ⋃₀ (Set.compl '' S) := by
  apply Set.ext
  intro a
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro s hsS
    apply Classical.byContradiction
    intro hns
    exact hne ⟨sᶜ, ⟨s, hsS, rfl⟩, hns⟩
  · intro ⟨u, hu, hau⟩ hmem
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu] at hau
    exact hau (hmem s hsS)

structure ClosedTopology (X : Type) where

  IsClosed (s : Set X) : Prop

  isClosed_empty : IsClosed ∅

  isClosed_union (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t)

  isClosed_sInter (S : Set (Set X)) (h : ∀ s ∈ S, IsClosed s) : IsClosed (⋂₀ S)

theorem ClosedTopology.ext' {X : Type} {c₁ c₂ : ClosedTopology X}
    (h : c₁.IsClosed = c₂.IsClosed) : c₁ = c₂ := by
  cases c₁; cases c₂; cases h; rfl

@[reducible] def ClosedTopology.toTop {X : Type} (c : ClosedTopology X) : TopologicalSpace X where
  IsOpen s := c.IsClosed sᶜ
  isOpen_univ := by rw [Set.compl_univ]; exact c.isClosed_empty
  isOpen_inter s t hs ht := by
    rw [Set.compl_inter]; exact c.isClosed_union _ _ hs ht
  isOpen_sUnion S h := by
    rw [Set.compl_sUnion]
    refine c.isClosed_sInter _ fun u hu => ?_
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    exact h s hsS

def TopologicalSpace.toClosed {X : Type} (t : TopologicalSpace X) : ClosedTopology X where
  IsClosed s := t.IsOpen sᶜ
  isClosed_empty := by rw [Set.compl_empty]; exact t.isOpen_univ
  isClosed_union s u hs hu := by
    rw [Set.compl_union]; exact t.isOpen_inter _ _ hs hu
  isClosed_sInter S h := by
    rw [Set.compl_sInter]
    refine t.isOpen_sUnion _ fun u hu => ?_
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    exact h s hsS

theorem toTop_toClosed {X : Type} (t : TopologicalSpace X) : t.toClosed.toTop = t := by
  apply TopologicalSpace.ext'
  funext s
  show t.IsOpen sᶜᶜ = t.IsOpen s
  rw [Set.compl_compl]

theorem toClosed_toTop {X : Type} (c : ClosedTopology X) : c.toTop.toClosed = c := by
  apply ClosedTopology.ext'
  funext s
  show c.IsClosed sᶜᶜ = c.IsClosed s
  rw [Set.compl_compl]

def topEquivClosed (X : Type) : Cat.Equiv (TopologicalSpace X) (ClosedTopology X) where
  toFun := TopologicalSpace.toClosed
  invFun := ClosedTopology.toTop
  left_inv := toTop_toClosed
  right_inv := toClosed_toTop

structure KuratowskiClosure (X : Type) where

  cl (s : Set X) : Set X

  cl_empty : cl ∅ = ∅

  subset_cl (s : Set X) : s ⊆ cl s

  cl_union (s t : Set X) : cl (s ∪ t) = cl s ∪ cl t

  cl_cl (s : Set X) : cl (cl s) = cl s

theorem KuratowskiClosure.ext' {X : Type} {k₁ k₂ : KuratowskiClosure X}
    (h : k₁.cl = k₂.cl) : k₁ = k₂ := by
  cases k₁; cases k₂; cases h; rfl

def TopologicalSpace.closure {X : Type} (t : TopologicalSpace X) (s : Set X) : Set X :=
  ⋂₀ {u | t.IsOpen uᶜ ∧ s ⊆ u}

theorem TopologicalSpace.subset_closure {X : Type} (t : TopologicalSpace X) (s : Set X) :
    s ⊆ t.closure s :=
  fun a ha _ hu => hu.2 a ha

theorem TopologicalSpace.closure_min {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (hu : t.IsOpen uᶜ) (hsu : s ⊆ u) : t.closure s ⊆ u :=
  fun _ ha => ha u ⟨hu, hsu⟩

theorem TopologicalSpace.closure_isClosed {X : Type} (t : TopologicalSpace X) (s : Set X) :
    t.IsOpen (t.closure s)ᶜ := by
  show t.IsOpen (⋂₀ {u | t.IsOpen uᶜ ∧ s ⊆ u})ᶜ
  rw [Set.compl_sInter]
  refine t.isOpen_sUnion _ fun v hv => ?_
  have ⟨u, hu, huv⟩ := hv
  rw [← huv]
  exact hu.1

theorem TopologicalSpace.closure_mono {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (h : s ⊆ u) : t.closure s ⊆ t.closure u :=
  t.closure_min (t.closure_isClosed u) fun a ha => t.subset_closure u a (h a ha)

theorem KuratowskiClosure.mono {X : Type} (k : KuratowskiClosure X) {s t : Set X}
    (h : s ⊆ t) : k.cl s ⊆ k.cl t := by
  have hst : s ∪ t = t :=
    Set.subset_antisymm
      (fun a ha => match ha with | Or.inl h' => h a h' | Or.inr h' => h')
      (fun a ha => Or.inr ha)
  have hu := k.cl_union s t
  rw [hst] at hu
  intro a ha
  rw [hu]
  exact Or.inl ha

@[reducible] def KuratowskiClosure.toTop {X : Type} (k : KuratowskiClosure X) : TopologicalSpace X where
  IsOpen s := k.cl sᶜ = sᶜ
  isOpen_univ := by rw [Set.compl_univ]; exact k.cl_empty
  isOpen_inter s t hs ht := by rw [Set.compl_inter, k.cl_union, hs, ht]
  isOpen_sUnion S h := by
    apply Set.subset_antisymm
    · intro a ha ⟨s, hsS, has⟩
      have hTs : (⋃₀ S)ᶜ ⊆ sᶜ := fun b hb hbs => hb ⟨s, hsS, hbs⟩
      have hcl := k.mono hTs a ha
      rw [h s hsS] at hcl
      exact hcl has
    · exact k.subset_cl _

def TopologicalSpace.toKur {X : Type} (t : TopologicalSpace X) : KuratowskiClosure X where
  cl := t.closure
  cl_empty := by
    apply Set.subset_antisymm
    · exact t.closure_min (by rw [Set.compl_empty]; exact t.isOpen_univ) fun a ha => ha
    · exact t.subset_closure ∅
  subset_cl := t.subset_closure
  cl_union s u := by
    apply Set.subset_antisymm
    · refine t.closure_min ?_ ?_
      · rw [Set.compl_union]
        exact t.isOpen_inter _ _ (t.closure_isClosed s) (t.closure_isClosed u)
      · intro a ha
        cases ha with
        | inl h => exact Or.inl (t.subset_closure s a h)
        | inr h => exact Or.inr (t.subset_closure u a h)
    · intro a ha
      cases ha with
      | inl h => exact t.closure_mono (fun b hb => Or.inl hb) a h
      | inr h => exact t.closure_mono (fun b hb => Or.inr hb) a h
  cl_cl s := by
    apply Set.subset_antisymm
    · exact t.closure_min (t.closure_isClosed s) fun a ha => ha
    · exact t.subset_closure _

theorem toKur_toTop {X : Type} (t : TopologicalSpace X) : t.toKur.toTop = t := by
  apply TopologicalSpace.ext'
  funext s
  show (t.closure sᶜ = sᶜ) = t.IsOpen s
  apply propext
  constructor
  · intro h
    have hc := t.closure_isClosed sᶜ
    rw [h, Set.compl_compl] at hc
    exact hc
  · intro h
    exact Set.subset_antisymm
      (t.closure_min (by rw [Set.compl_compl]; exact h) fun a ha => ha)
      (t.subset_closure _)

theorem toTop_toKur {X : Type} (k : KuratowskiClosure X) : k.toTop.toKur = k := by
  apply KuratowskiClosure.ext'
  funext s
  apply Set.subset_antisymm
  · intro a ha
    refine ha (k.cl s) ⟨?_, k.subset_cl s⟩
    show k.cl (k.cl s)ᶜᶜ = (k.cl s)ᶜᶜ
    rw [Set.compl_compl, k.cl_cl]
  · intro a ha u hu
    have h1 : k.cl uᶜᶜ = uᶜᶜ := hu.1
    rw [Set.compl_compl] at h1
    have hmem := k.mono hu.2 a ha
    rw [h1] at hmem
    exact hmem

def topEquivKur (X : Type) : Cat.Equiv (TopologicalSpace X) (KuratowskiClosure X) where
  toFun := TopologicalSpace.toKur
  invFun := KuratowskiClosure.toTop
  left_inv := toKur_toTop
  right_inv := toTop_toKur

structure NeighborhoodSystem (X : Type) where

  N (x : X) : Set (Set X)

  univ_mem (x : X) : Set.univ ∈ N x

  mem_of (x : X) (U : Set X) (h : U ∈ N x) : x ∈ U

  superset (x : X) (U V : Set X) (hU : U ∈ N x) (hUV : U ⊆ V) : V ∈ N x

  inter (x : X) (U V : Set X) (hU : U ∈ N x) (hV : V ∈ N x) : U ∩ V ∈ N x

  interior (x : X) (U : Set X) (h : U ∈ N x) : ∃ V ∈ N x, ∀ y ∈ V, U ∈ N y

theorem NeighborhoodSystem.ext' {X : Type} {n₁ n₂ : NeighborhoodSystem X}
    (h : n₁.N = n₂.N) : n₁ = n₂ := by
  cases n₁; cases n₂; cases h; rfl

@[reducible] def NeighborhoodSystem.toTop {X : Type} (n : NeighborhoodSystem X) : TopologicalSpace X where
  IsOpen s := ∀ x ∈ s, s ∈ n.N x
  isOpen_univ := fun x _ => n.univ_mem x
  isOpen_inter s t hs ht := fun x hx =>
    n.inter x s t (hs x hx.1) (ht x hx.2)
  isOpen_sUnion S h := fun x hx => by
    have ⟨s, hsS, hxs⟩ := hx
    exact n.superset x s _ (h s hsS x hxs) fun b hb => ⟨s, hsS, hb⟩

def TopologicalSpace.toNbhd {X : Type} (t : TopologicalSpace X) : NeighborhoodSystem X where
  N x := {U | ∃ V, t.IsOpen V ∧ x ∈ V ∧ V ⊆ U}
  univ_mem _x := ⟨Set.univ, t.isOpen_univ, trivial, fun _ _ => trivial⟩
  mem_of x _U h :=
    have ⟨_, _, hxV, hVU⟩ := h
    hVU x hxV
  superset _x _U _W hU hUW :=
    have ⟨V, hV, hxV, hVU⟩ := hU
    ⟨V, hV, hxV, fun b hb => hUW b (hVU b hb)⟩
  inter _x _U _W hU hW :=
    have ⟨V₁, h₁, hx₁, hs₁⟩ := hU
    have ⟨V₂, h₂, hx₂, hs₂⟩ := hW
    ⟨V₁ ∩ V₂, t.isOpen_inter _ _ h₁ h₂, ⟨hx₁, hx₂⟩, fun b hb => ⟨hs₁ b hb.1, hs₂ b hb.2⟩⟩
  interior _x _U hU :=
    have ⟨V, hV, hxV, hVU⟩ := hU
    ⟨V, ⟨V, hV, hxV, fun _ hb => hb⟩, fun _ hy => ⟨V, hV, hy, hVU⟩⟩

theorem toNbhd_toTop {X : Type} (t : TopologicalSpace X) : t.toNbhd.toTop = t := by
  apply TopologicalSpace.ext'
  funext s
  show (∀ x ∈ s, ∃ V, t.IsOpen V ∧ x ∈ V ∧ V ⊆ s) = t.IsOpen s
  apply propext
  constructor
  · intro h
    exact @isOpen_of_nhds X t s h
  · intro h x hx
    exact ⟨s, h, hx, fun _ hb => hb⟩

theorem toTop_toNbhd {X : Type} (n : NeighborhoodSystem X) : n.toTop.toNbhd = n := by
  apply NeighborhoodSystem.ext'
  funext x
  apply Set.subset_antisymm
  · intro U hU
    have ⟨V, hVopen, hxV, hVU⟩ := hU
    exact n.superset x V U (hVopen x hxV) hVU
  · intro U hU
    refine ⟨{y | U ∈ n.N y}, ?_, hU, ?_⟩
    · intro y hy
      have ⟨V, hVN, hall⟩ := n.interior y U hy
      exact n.superset y V _ hVN hall
    · exact fun y hy => n.mem_of y U hy

def topEquivNbhd (X : Type) : Cat.Equiv (TopologicalSpace X) (NeighborhoodSystem X) where
  toFun := TopologicalSpace.toNbhd
  invFun := NeighborhoodSystem.toTop
  left_inv := toNbhd_toTop
  right_inv := toTop_toNbhd

structure DirectedIndex : Type 1 where

  ι : Type

  le : ι → ι → Prop

  inhabited : Nonempty ι

  upper (i j : ι) : ∃ k, le i k ∧ le j k

def Converges {X : Type} (t : TopologicalSpace X) (D : DirectedIndex)
    (net : D.ι → X) (a : X) : Prop :=
  ∀ U, t.IsOpen U → a ∈ U → ∃ d, ∀ e, D.le d e → net e ∈ U

theorem nets_of_isClosed {X : Type} (t : TopologicalSpace X) {s : Set X}
    (hs : t.IsOpen sᶜ) (D : DirectedIndex) (net : D.ι → X)
    (hnet : ∀ e, net e ∈ s) {a : X} (hconv : Converges t D net a) : a ∈ s := by
  by_cases ha : a ∈ s
  · exact ha
  · have ⟨d, hd⟩ := hconv sᶜ hs ha
    have ⟨e, hde, _⟩ := D.upper d d
    exact absurd (hnet e) (hd e hde)

theorem isClosed_of_nets {X : Type} (t : TopologicalSpace X) {s : Set X}
    (h : ∀ (D : DirectedIndex) (net : D.ι → X), (∀ e, net e ∈ s) →
         ∀ a, Converges t D net a → a ∈ s) :
    t.IsOpen sᶜ := by
  refine @isOpen_of_nhds X t sᶜ fun a ha => ?_
  by_cases hex : ∃ W, t.IsOpen W ∧ a ∈ W ∧ W ⊆ sᶜ
  · exact hex
  · exfalso

    have hmeet : ∀ W : {W : Set X // t.IsOpen W ∧ a ∈ W}, ∃ b, b ∈ W.val ∩ s := by
      intro ⟨W, hW, haW⟩
      by_cases hb : ∃ b, b ∈ W ∩ s
      · exact hb
      · exact absurd ⟨W, hW, haW, fun b hbW hbs => hb ⟨b, hbW, hbs⟩⟩ hex

    let D : DirectedIndex := ⟨{W : Set X // t.IsOpen W ∧ a ∈ W},
      fun V W => W.val ⊆ V.val,
      ⟨⟨Set.univ, t.isOpen_univ, trivial⟩⟩,
      fun V W => ⟨⟨V.val ∩ W.val,
        t.isOpen_inter _ _ V.property.1 W.property.1,
        ⟨V.property.2, W.property.2⟩⟩,
        fun b hb => hb.1, fun b hb => hb.2⟩⟩

    let net : D.ι → X := fun W => Classical.choose (hmeet W)
    have hnet_s : ∀ W, net W ∈ s := fun W => (Classical.choose_spec (hmeet W)).2
    have hconv : Converges t D net a := by
      intro U hU haU
      refine ⟨⟨U, hU, haU⟩, ?_⟩
      intro E hE
      exact hE _ (Classical.choose_spec (hmeet E)).1
    exact ha (h D net hnet_s a hconv)

theorem Set.preimage_sUnion {α β : Type} (f : α → β) (S : Set (Set β)) :
    f ⁻¹' (⋃₀ S) = ⋃₀ (Set.preimage f '' S) := by
  apply Set.ext
  intro a
  constructor
  · intro ⟨s, hsS, hfa⟩
    exact ⟨f ⁻¹' s, ⟨s, hsS, rfl⟩, hfa⟩
  · intro ⟨u, hu, hau⟩
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu] at hau
    exact ⟨s, hsS, hau⟩

@[reducible] def TopologicalSpace.coinduced {X Y : Type} (tX : TopologicalSpace X) (f : X → Y) :
    TopologicalSpace Y where
  IsOpen s := tX.IsOpen (f ⁻¹' s)
  isOpen_univ := tX.isOpen_univ
  isOpen_inter _ _ hs ht := tX.isOpen_inter _ _ hs ht
  isOpen_sUnion S h := by
    show tX.IsOpen (f ⁻¹' (⋃₀ S))
    rw [Set.preimage_sUnion]
    refine tX.isOpen_sUnion _ fun u hu => ?_
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    exact h s hsS

@[reducible] def finalTopology {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X) :
    TopologicalSpace X where
  IsOpen s := ∀ i, (tY i).IsOpen (f i ⁻¹' s)
  isOpen_univ i := (tY i).isOpen_univ
  isOpen_inter _ _ hs ht i := (tY i).isOpen_inter _ _ (hs i) (ht i)
  isOpen_sUnion S h i := by
    show (tY i).IsOpen (f i ⁻¹' (⋃₀ S))
    rw [Set.preimage_sUnion]
    refine (tY i).isOpen_sUnion _ fun u hu => ?_
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    exact h s hsS i

@[reducible] def initialTopology {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i) :
    TopologicalSpace X where
  IsOpen s := ∀ t' : TopologicalSpace X,
    (∀ i u, (tY i).IsOpen u → t'.IsOpen (f i ⁻¹' u)) → t'.IsOpen s
  isOpen_univ t' _ := t'.isOpen_univ
  isOpen_inter s u hs hu t' hc := t'.isOpen_inter s u (hs t' hc) (hu t' hc)
  isOpen_sUnion S h t' hc := t'.isOpen_sUnion S fun s hs => h s hs t' hc

theorem continuous_toFinal {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X) (i : I) :
    @Continuous (Y i) (tY i) X (finalTopology tY f) (f i) :=
  fun _ hs => hs i

theorem final_finest {I : Type} {Y : I → Type} {X : Type}
    {tY : (i : I) → TopologicalSpace (Y i)} {f : (i : I) → Y i → X}
    {t' : TopologicalSpace X} (h : ∀ i, @Continuous (Y i) (tY i) X t' (f i)) :
    ∀ s, t'.IsOpen s → (finalTopology tY f).IsOpen s :=
  fun s hs i => h i s hs

theorem continuous_fromInitial {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i) (i : I) :
    @Continuous X (initialTopology tY f) (Y i) (tY i) (f i) :=
  fun u hu _t' hc => hc i u hu

theorem initial_coarsest {I : Type} {Y : I → Type} {X : Type}
    {tY : (i : I) → TopologicalSpace (Y i)} {f : (i : I) → X → Y i}
    {t' : TopologicalSpace X} (h : ∀ i, @Continuous X t' (Y i) (tY i) (f i)) :
    ∀ s, (initialTopology tY f).IsOpen s → t'.IsOpen s :=
  fun _s hs => hs t' fun i u hu => h i u hu

theorem continuous_fromCoinduced_iff {X Y Z : Type} (tX : TopologicalSpace X)
    (tZ : TopologicalSpace Z) (f : X → Y) (g : Y → Z) :
    @Continuous Y (tX.coinduced f) Z tZ g ↔ @Continuous X tX Z tZ (fun x => g (f x)) :=
  Iff.rfl

theorem continuous_fromFinal_iff {I : Type} {Y : I → Type} {X Z : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X)
    (tZ : TopologicalSpace Z) (g : X → Z) :
    @Continuous X (finalTopology tY f) Z tZ g ↔
      ∀ i, @Continuous (Y i) (tY i) Z tZ (fun y => g (f i y)) :=
  ⟨fun h i s hs => h s hs i, fun h s hs i => h i s hs⟩

theorem continuous_toInitial_iff {I : Type} {Y : I → Type} {X Z : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i)
    (tZ : TopologicalSpace Z) (g : Z → X) :
    @Continuous Z tZ X (initialTopology tY f) g ↔
      ∀ i, @Continuous Z tZ (Y i) (tY i) (fun z => f i (g z)) := by
  constructor
  · intro hg i u hu
    exact hg (f i ⁻¹' u) fun t' hc => hc i u hu
  · intro h s hs
    exact hs (tZ.coinduced g) fun i u hu => h i u hu

@[reducible] def TopologicalSpace.induced {X Y : Type} (f : X → Y) (t : TopologicalSpace Y) :
    TopologicalSpace X :=
  initialTopology (Y := fun _ : Unit => Y) (fun _ => t) (fun _ => f)

instance instTopSubtype {X : Type} [tX : TopologicalSpace X] (p : X → Prop) :
    TopologicalSpace (Subtype p) :=
  tX.induced Subtype.val

instance instTopPi {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : I) → Y i) :=
  initialTopology tY fun i g => g i

instance instTopProd {X Y : Type} [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  initialTopology (Y := fun b => cond b X Y)
    (fun b => match b with | true => t₁ | false => t₂)
    (fun b => match b with | true => Prod.fst | false => Prod.snd)

instance instTopSigma {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : I) × Y i) :=
  finalTopology tY fun i => Sigma.mk i

instance instTopQuot {X : Type} [tX : TopologicalSpace X] {r : X → X → Prop} :
    TopologicalSpace (Quot r) :=
  tX.coinduced (Quot.mk r)

theorem isOpen_subtype_iff {X : Type} [tX : TopologicalSpace X] {p : X → Prop}
    {s : Set (Subtype p)} :
    IsOpen s ↔ ∃ u, IsOpen u ∧ s = Subtype.val ⁻¹' u := by
  constructor
  · intro hs
    refine hs ⟨fun v => ∃ u, tX.IsOpen u ∧ v = Subtype.val ⁻¹' u, ?_, ?_, ?_⟩ ?_
    · exact ⟨Set.univ, tX.isOpen_univ, rfl⟩
    · intro v w ⟨u₁, hu₁, hv⟩ ⟨u₂, hu₂, hw⟩
      refine ⟨u₁ ∩ u₂, tX.isOpen_inter _ _ hu₁ hu₂, ?_⟩
      rw [hv, hw]
      rfl
    · intro S hS
      refine ⟨⋃₀ {u | tX.IsOpen u ∧ Subtype.val ⁻¹' u ∈ S}, ?_, ?_⟩
      · exact tX.isOpen_sUnion _ fun u hu => hu.1
      · apply Set.ext
        intro a
        constructor
        · intro ⟨v, hvS, hav⟩
          have ⟨u, hu, hvu⟩ := hS v hvS
          rw [hvu] at hav hvS
          exact ⟨u, ⟨hu, hvS⟩, hav⟩
        · intro ⟨u, hu, hau⟩
          exact ⟨Subtype.val ⁻¹' u, hu.2, hau⟩
    · exact fun _ u hu => ⟨u, hu, rfl⟩
  · intro ⟨u, hu, hsu⟩ t' hc
    rw [hsu]
    exact hc () u hu

theorem continuous_apply {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)]
    (i : I) : Continuous fun g : (j : I) → Y j => g i :=
  continuous_fromInitial tY (fun i (g : (j : I) → Y j) => g i) i

theorem continuous_pi_iff {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)]
    {Z : Type} [tZ : TopologicalSpace Z] (g : Z → (i : I) → Y i) :
    Continuous g ↔ ∀ i, Continuous fun z => g z i :=
  continuous_toInitial_iff tY (fun i (g : (j : I) → Y j) => g i) tZ g

theorem continuous_quotMk {X : Type} [tX : TopologicalSpace X] (r : X → X → Prop) :
    Continuous (Quot.mk r) :=
  fun _ hs => hs

theorem continuous_quotLift {X Z : Type} [tX : TopologicalSpace X] [tZ : TopologicalSpace Z]
    {r : X → X → Prop} {g : X → Z} (hg : ∀ a b, r a b → g a = g b) :
    Continuous (Quot.lift g hg) ↔ Continuous g :=
  continuous_fromCoinduced_iff tX tZ (Quot.mk r) (Quot.lift g hg)

theorem initialTopology_empty {X : Type} {Y : Empty → Type}
    (tY : (i : Empty) → TopologicalSpace (Y i)) (f : (i : Empty) → X → Y i) :
    initialTopology tY f = indiscrete X := by
  apply TopologicalSpace.ext'
  funext s
  apply propext
  constructor
  · intro h
    exact h (indiscrete X) fun i => i.elim
  · intro h t' _
    cases h with
    | inl he => rw [he]; exact @isOpen_empty X t'
    | inr hu => rw [hu]; exact t'.isOpen_univ

theorem finalTopology_empty {X : Type} {Y : Empty → Type}
    (tY : (i : Empty) → TopologicalSpace (Y i)) (f : (i : Empty) → Y i → X) :
    finalTopology tY f = discrete X := by
  apply TopologicalSpace.ext'
  funext s
  apply propext
  exact ⟨fun _ => trivial, fun _ i => i.elim⟩

theorem Set.image_preimage_of_surjective {α β : Type} {f : α → β}
    (hf : Function.Surjective f) (u : Set β) : f '' (f ⁻¹' u) = u := by
  apply Set.ext
  intro b
  constructor
  · intro ⟨a, ha, hab⟩
    rw [← hab]
    exact ha
  · intro hb
    have ⟨a, ha⟩ := hf b
    refine ⟨a, ?_, ha⟩
    show f a ∈ u
    rw [ha]
    exact hb

theorem coinduced_eq_of_surjective {X Y : Type}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    tX.coinduced f = tY := by
  apply TopologicalSpace.ext'
  funext s
  apply propext
  constructor
  · intro h
    have hcl : IsClosed ((f ⁻¹' s)ᶜ : Set X) := isClosed_compl h
    have hcpt : IsCompact ((f ⁻¹' s)ᶜ : Set X) := hcl.isCompact
    have himg : IsCompact (f '' (f ⁻¹' s)ᶜ) := hcpt.image hf
    have hclY : IsClosed (f '' (f ⁻¹' s)ᶜ) := himg.isClosed
    have heq : f '' ((f ⁻¹' s)ᶜ) = sᶜ := Set.image_preimage_of_surjective hsurj sᶜ
    rw [heq] at hclY
    show tY.IsOpen s
    rw [← Set.compl_compl s]
    exact hclY
  · intro h
    exact hf s h

example {X Y : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [CompactSpace X] [Hausdorff Y] {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g := by
  have hsurj : Function.Surjective f := fun y => ⟨g y, hfg y⟩
  rw [← coinduced_eq_of_surjective hf hsurj]
  refine (continuous_fromCoinduced_iff tX tX f g).mpr ?_
  have hid : (fun x => g (f x)) = fun x : X => x := funext hgf
  rw [hid]
  exact continuous_id

end

-- ─── 08_Real（解答） ───
section

class CompleteOrderedField (R : Type) extends Add R, Mul R, Neg R, Inv R, Zero R, One R,
    LE R, LT R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  zero_ne_one : (0 : R) ≠ 1
  mul_inv_cancel : ∀ a : R, a ≠ 0 → a * a⁻¹ = 1
  le_refl : ∀ a : R, a ≤ a
  le_trans : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : R, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : R, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : R, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c, c + a ≤ c + b
  mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  exists_lub : ∀ S : Set R, (∃ x, x ∈ S) → (∃ M, ∀ x ∈ S, x ≤ M) →
    ∃ s, (∀ x ∈ S, x ≤ s) ∧ ∀ M, (∀ x ∈ S, x ≤ M) → s ≤ M

namespace CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

instance : Sub R := ⟨fun a b => a + -b⟩
instance : Div R := ⟨fun a b => a * b⁻¹⟩
instance : OfNat R 2 := ⟨1 + 1⟩

instance : Std.Associative (α := R) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := R) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := R) (· * ·) := ⟨mul_assoc⟩
instance : Std.Commutative (α := R) (· * ·) := ⟨mul_comm⟩

theorem sub_def (a b : R) : a - b = a + -b := rfl

theorem div_def (a b : R) : a / b = a * b⁻¹ := rfl

theorem two_def : (2 : R) = 1 + 1 := rfl

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h' : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h'
  exact h'

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  rw [add_comm a, add_comm b] at h
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_neg (a : R) : -(-a) = a := neg_eq_of_add_eq_zero (neg_add_cancel a)

theorem neg_zero : -(0 : R) = 0 := neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc a + b + (-a + -b) = (a + -a) + (b + -b) := by ac_rfl
    _ = 0 := by rw [add_neg_cancel, add_neg_cancel, add_zero]

theorem sub_self (a : R) : a - a = 0 := add_neg_cancel a

theorem sub_zero (a : R) : a - 0 = a := by rw [sub_def, neg_zero, add_zero]

theorem zero_sub (a : R) : 0 - a = -a := by rw [sub_def, zero_add]

theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_def, add_assoc, neg_add_cancel, add_zero]

theorem add_sub_cancel (a b : R) : a + b - b = a := by
  rw [sub_def, add_assoc, add_neg_cancel, add_zero]

theorem sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' : a - b + b = 0 + b := congrArg (· + b) h
    rw [sub_add_cancel, zero_add] at h'
    exact h'
  · intro h; rw [h, sub_self]

theorem neg_sub (a b : R) : -(a - b) = b - a := by
  rw [sub_def, neg_add, neg_neg, sub_def, add_comm]

theorem sub_add_sub_cancel (a b c : R) : a - b + (b - c) = a - c := by
  rw [sub_def, sub_def, sub_def, add_assoc, ← add_assoc (-b), neg_add_cancel, zero_add]

theorem add_sub_add_right (a b c : R) : a + c - (b + c) = a - b := by
  rw [sub_def, sub_def, neg_add]
  calc a + c + (-b + -c) = a + -b + (c + -c) := by ac_rfl
    _ = a + -b := by rw [add_neg_cancel, add_zero]

theorem mul_one (a : R) : a * 1 = a := by rw [mul_comm, one_mul]

theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

theorem mul_zero (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← mul_add, zero_add, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]

theorem mul_neg (a b : R) : a * -b = -(a * b) := by
  apply Eq.symm
  apply neg_eq_of_add_eq_zero
  rw [← mul_add, add_neg_cancel, mul_zero]

theorem neg_mul (a b : R) : -a * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_def, sub_def, mul_add, mul_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [mul_comm, mul_sub, mul_comm c, mul_comm c]

theorem two_mul (a : R) : 2 * a = a + a := by rw [two_def, add_mul, one_mul]

theorem mul_eq_zero {a b : R} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact .inl ha
  · right
    calc b = a⁻¹ * a * b := by rw [mul_comm a⁻¹, mul_inv_cancel a ha, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]

theorem inv_mul_cancel {a : R} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_cancel a h]

theorem div_mul_cancel {a b : R} (h : b ≠ 0) : a / b * b = a := by
  rw [div_def, mul_assoc, inv_mul_cancel h, mul_one]

theorem mul_div_cancel {a b : R} (h : b ≠ 0) : a * b / b = a := by
  rw [div_def, mul_assoc, mul_inv_cancel b h, mul_one]

theorem mul_div_cancel_left {c : R} (e : R) (h : c ≠ 0) : c * (e / c) = e := by
  rw [mul_comm, div_mul_cancel h]

theorem inv_ne_zero {a : R} (h : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h'
  have := mul_inv_cancel a h
  rw [h', mul_zero] at this
  exact zero_ne_one this

theorem lt_irrefl (a : R) : ¬ a < a := fun h => ((lt_iff_le_not_le a a).mp h).2 (le_refl a)

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b := ((lt_iff_le_not_le a b).mp h).1

theorem not_le {a b : R} : ¬ a ≤ b ↔ b < a := by
  constructor
  · intro h
    rcases le_total a b with h' | h'
    · exact absurd h' h
    · exact (lt_iff_le_not_le b a).mpr ⟨h', h⟩
  · intro h h'
    exact ((lt_iff_le_not_le b a).mp h).2 h'

theorem not_lt {a b : R} : ¬ a < b ↔ b ≤ a := by
  constructor
  · intro h
    rcases le_total b a with h' | h'
    · exact h'
    · exact Classical.byContradiction fun h'' => h (not_le.mp h'')
  · intro h h'
    exact not_le.mpr h' h

theorem lt_of_le_of_lt {a b c : R} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  not_le.mp fun h => not_le.mpr h₂ (le_trans c a b h h₁)

theorem lt_of_lt_of_le {a b c : R} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  not_le.mp fun h => not_le.mpr h₁ (le_trans b c a h₂ h)

theorem lt_trans {a b c : R} (h₁ : a < b) (h₂ : b < c) : a < c :=
  lt_of_le_of_lt (le_of_lt h₁) h₂

instance : Trans (α := R) (β := R) (γ := R) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans _ _ _⟩
instance : Trans (α := R) (β := R) (γ := R) (· ≤ ·) (· < ·) (· < ·) := ⟨lt_of_le_of_lt⟩
instance : Trans (α := R) (β := R) (γ := R) (· < ·) (· ≤ ·) (· < ·) := ⟨lt_of_lt_of_le⟩
instance : Trans (α := R) (β := R) (γ := R) (· < ·) (· < ·) (· < ·) := ⟨lt_trans⟩

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := fun e => lt_irrefl b (e ▸ h)

theorem lt_of_le_of_ne {a b : R} (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b :=
  not_le.mp fun h => h₂ (le_antisymm a b h₁ h)

theorem lt_or_le (a b : R) : a < b ∨ b ≤ a := by
  by_cases h : b ≤ a
  · exact .inr h
  · exact .inl (not_le.mp h)

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a, add_comm b]; exact add_le_add_left a b h c

theorem le_of_add_le_add_left {a b c : R} (h : c + a ≤ c + b) : a ≤ b := by
  have := add_le_add_left _ _ h (-c)
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at this
  exact this

theorem add_lt_add_left {a b : R} (h : a < b) (c : R) : c + a < c + b :=
  not_le.mp fun h' => not_le.mpr h (le_of_add_le_add_left h')

theorem add_lt_add_right {a b : R} (h : a < b) (c : R) : a + c < b + c := by
  rw [add_comm a, add_comm b]; exact add_lt_add_left h c

theorem add_le_add {a b c d : R} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans _ _ _ (add_le_add_right h₁ c) (add_le_add_left _ _ h₂ b)

theorem add_lt_add {a b c d : R} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  lt_trans (add_lt_add_right h₁ c) (add_lt_add_left h₂ b)

theorem add_lt_add_of_lt_of_le {a b c d : R} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left _ _ h₂ b)

theorem sub_nonneg {a b : R} : 0 ≤ b - a ↔ a ≤ b := by
  constructor
  · intro h
    have := add_le_add_right h a
    rwa [zero_add, sub_add_cancel] at this
  · intro h
    have := add_le_add_right h (-a)
    rwa [add_neg_cancel] at this

theorem sub_pos {a b : R} : 0 < b - a ↔ a < b := by
  constructor
  · intro h; exact not_le.mp fun h' => not_le.mpr h (by
      have := add_le_add_right h' (-a); rwa [add_neg_cancel] at this)
  · intro h; exact not_le.mp fun h' => not_le.mpr h (by
      have := add_le_add_right h' a; rwa [zero_add, sub_add_cancel] at this)

theorem neg_le_neg {a b : R} (h : a ≤ b) : -b ≤ -a := by
  have := add_le_add_right (add_le_add_right h (-a)) (-b)
  rw [add_neg_cancel, zero_add, add_comm b, add_assoc, add_neg_cancel, add_zero] at this
  exact this

theorem neg_lt_neg {a b : R} (h : a < b) : -b < -a :=
  not_le.mp fun h' => not_le.mpr h (by have := neg_le_neg h'; rwa [neg_neg, neg_neg] at this)

theorem neg_nonneg {a : R} : 0 ≤ -a ↔ a ≤ 0 := by
  constructor
  · intro h; have := neg_le_neg h; rwa [neg_neg, neg_zero] at this
  · intro h; have := neg_le_neg h; rwa [neg_zero] at this

theorem neg_pos {a : R} : 0 < -a ↔ a < 0 := by
  constructor
  · intro h; have := neg_lt_neg h; rwa [neg_neg, neg_zero] at this
  · intro h; have := neg_lt_neg h; rwa [neg_zero] at this

theorem add_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have := add_lt_add ha hb; rwa [add_zero] at this

theorem add_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have := add_le_add ha hb; rwa [add_zero] at this

theorem lt_add_of_pos_right (a : R) {b : R} (h : 0 < b) : a < a + b := by
  have := add_lt_add_left h a; rwa [add_zero] at this

theorem sub_lt_self (a : R) {b : R} (h : 0 < b) : a - b < a := by
  have := add_lt_add_left (neg_lt_neg h) a
  rwa [neg_zero, add_zero] at this

theorem mul_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  refine lt_of_le_of_ne (mul_nonneg a b (le_of_lt ha) (le_of_lt hb)) ?_
  intro h
  rcases mul_eq_zero h.symm with h' | h'
  · exact ne_of_lt ha h'.symm
  · exact ne_of_lt hb h'.symm

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  have := mul_nonneg c (b - a) hc (sub_nonneg.mpr h)
  rw [mul_sub] at this
  exact sub_nonneg.mp this

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm a, mul_comm b]; exact mul_le_mul_of_nonneg_left h hc

theorem mul_lt_mul_of_pos_left {a b c : R} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  have := mul_pos hc (sub_pos.mpr h)
  rw [mul_sub] at this
  exact sub_pos.mp this

theorem mul_self_nonneg (a : R) : 0 ≤ a * a := by
  rcases le_total 0 a with h | h
  · exact mul_nonneg a a h h
  · have := mul_nonneg (-a) (-a) (neg_nonneg.mpr h) (neg_nonneg.mpr h)
    rwa [neg_mul_neg] at this

theorem zero_lt_one : (0 : R) < 1 := by
  have h := mul_self_nonneg (1 : R)
  rw [one_mul] at h
  exact lt_of_le_of_ne h zero_ne_one

theorem zero_lt_two : (0 : R) < 2 := add_pos zero_lt_one zero_lt_one

theorem inv_pos {a : R} (h : 0 < a) : 0 < a⁻¹ := by
  refine not_le.mp fun h' => ?_
  have := mul_le_mul_of_nonneg_left h' (le_of_lt h)
  rw [mul_inv_cancel a (ne_of_lt h).symm, mul_zero] at this
  exact not_le.mpr zero_lt_one this

theorem div_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := mul_pos ha (inv_pos hb)

theorem two_ne_zero : (2 : R) ≠ 0 := (ne_of_lt zero_lt_two).symm

theorem add_halves (a : R) : a / 2 + a / 2 = a := by
  rw [← two_mul, mul_comm, div_mul_cancel two_ne_zero]

theorem half_pos {a : R} (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

theorem half_lt_self {a : R} (h : 0 < a) : a / 2 < a := by
  have := lt_add_of_pos_right (a / 2) (half_pos h)
  rwa [add_halves] at this

theorem half_add_lt {c ε : R} (h : 0 < ε) : c + ε / 2 < c + ε :=
  add_lt_add_left (half_lt_self h) c

open Classical in

noncomputable def abs (a : R) : R := if 0 ≤ a then a else -a

theorem abs_of_nonneg {a : R} (h : 0 ≤ a) : abs a = a := by
  rw [abs, if_pos h]

theorem abs_of_neg {a : R} (h : a < 0) : abs a = -a := by
  rw [abs, if_neg (not_le.mpr h)]

theorem abs_zero : abs (0 : R) = 0 := abs_of_nonneg (le_refl 0)

theorem abs_of_nonpos {a : R} (h : a ≤ 0) : abs a = -a := by
  rcases lt_or_le a 0 with h' | h'
  · exact abs_of_neg h'
  · have : a = 0 := le_antisymm _ _ h h'
    rw [this, abs_zero, neg_zero]

theorem abs_nonneg (a : R) : 0 ≤ abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h]; exact le_of_lt (neg_pos.mpr h)
  · rw [abs_of_nonneg h]; exact h

theorem le_abs_self (a : R) : a ≤ abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h]; exact le_trans _ _ _ (le_of_lt h) (le_of_lt (neg_pos.mpr h))
  · rw [abs_of_nonneg h]; exact le_refl a

theorem abs_neg (a : R) : abs (-a) = abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h, abs_of_nonneg (le_of_lt (neg_pos.mpr h))]
  · rcases lt_or_le 0 a with h' | h'
    · rw [abs_of_nonneg h, abs_of_neg (neg_pos.mp (by rwa [neg_neg]))]
      exact neg_neg a
    · have : a = 0 := le_antisymm _ _ h' h
      rw [this, neg_zero]

theorem neg_abs_le (a : R) : -abs a ≤ a := by
  have := le_abs_self (-a)
  rw [abs_neg] at this
  have := neg_le_neg this
  rwa [neg_neg] at this

theorem abs_sub_comm (a b : R) : abs (a - b) = abs (b - a) := by
  rw [← neg_sub, abs_neg]

theorem abs_lt {a b : R} : abs a < b ↔ -b < a ∧ a < b := by
  constructor
  · intro h
    refine ⟨?_, lt_of_le_of_lt (le_abs_self a) h⟩
    have := neg_lt_neg h
    exact lt_of_lt_of_le this (neg_abs_le a)
  · intro ⟨h₁, h₂⟩
    rcases lt_or_le a 0 with h | h
    · rw [abs_of_neg h]
      have := neg_lt_neg h₁; rwa [neg_neg] at this
    · rw [abs_of_nonneg h]; exact h₂

theorem abs_add (a b : R) : abs (a + b) ≤ abs a + abs b := by
  rcases lt_or_le (a + b) 0 with h | h
  · rw [abs_of_neg h, neg_add]
    exact add_le_add (by have := neg_abs_le a; have := neg_le_neg this; rwa [neg_neg] at this)
      (by have := neg_abs_le b; have := neg_le_neg this; rwa [neg_neg] at this)
  · rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self a) (le_abs_self b)

theorem abs_sub_le (a b c : R) : abs (a - c) ≤ abs (a - b) + abs (b - c) := by
  rw [← sub_add_sub_cancel a b c]
  exact abs_add _ _

theorem abs_sub_self (a : R) : abs (a - a) = 0 := by rw [sub_self, abs_zero]

theorem abs_le_abs_add_abs_sub (a b : R) : abs a ≤ abs b + abs (a - b) := by
  have := abs_add b (a - b)
  rwa [sub_def, ← add_assoc, add_comm b a, add_assoc, add_neg_cancel, add_zero] at this

theorem abs_sub_lt_of {c y ε : R} (h₁ : c - ε < y) (h₂ : y < c + ε) : abs (y - c) < ε := by
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have := add_lt_add_right h₁ (-c)
    rw [sub_def, add_comm c, add_assoc, add_neg_cancel, add_zero] at this
    exact this
  · have := add_lt_add_right h₂ (-c)
    rw [add_comm c, add_assoc, add_neg_cancel, add_zero] at this
    exact this

theorem mul_nonpos_of_nonneg_of_nonpos {a b : R} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have := mul_nonneg a (-b) ha (neg_nonneg.mpr hb)
  rw [mul_neg] at this
  exact neg_nonneg.mp this

theorem abs_mul (a b : R) : abs (a * b) = abs a * abs b := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg a b ha hb)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hb),
      mul_neg]
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, mul_comm a b,
      abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hb ha), neg_mul, mul_comm]
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, neg_mul_neg,
      abs_of_nonneg (by have := mul_nonneg (-a) (-b) (neg_nonneg.mpr ha) (neg_nonneg.mpr hb)
                        rwa [neg_mul_neg] at this)]

open Classical in
noncomputable def min (a b : R) : R := if a ≤ b then a else b

theorem min_le_left (a b : R) : min a b ≤ a := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact le_refl a
  · rw [if_neg h]; exact le_of_lt (not_le.mp h)

theorem min_le_right (a b : R) : min a b ≤ b := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact le_refl b

theorem lt_min {a b c : R} (hb : a < b) (hc : a < c) : a < min b c := by
  unfold min
  by_cases h : b ≤ c
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact hc

theorem exists_mem_gt_of_lub {S : Set R} {s : R}
    (hlub : ∀ M, (∀ x ∈ S, x ≤ M) → s ≤ M) {ε : R} (hε : 0 < ε) :
    ∃ x, x ∈ S ∧ s - ε < x := by
  refine Classical.byContradiction fun h => ?_
  have hb : ∀ x ∈ S, x ≤ s - ε := fun x hx =>
    not_lt.mp fun h' => h ⟨x, hx, h'⟩
  exact not_le.mpr (sub_lt_self s hε) (hlub _ hb)

def natCast : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1

theorem natCast_zero : (natCast 0 : R) = 0 := rfl

theorem natCast_succ (n : Nat) : (natCast (n + 1) : R) = natCast n + 1 := rfl

theorem natCast_nonneg : ∀ n : Nat, (0 : R) ≤ natCast n
  | 0 => le_refl 0
  | n + 1 => add_nonneg (natCast_nonneg n) (le_of_lt zero_lt_one)

theorem natCast_add (m : Nat) : ∀ n : Nat, (natCast (m + n) : R) = natCast m + natCast n
  | 0 => (add_zero _).symm
  | n + 1 => by
      rw [← Nat.add_assoc, natCast_succ, natCast_succ, natCast_add m n, add_assoc]

theorem exists_nat_gt (x : R) : ∃ n : Nat, x < natCast n := by
  refine Classical.byContradiction fun h => ?_
  have hb : ∀ y ∈ ({y | ∃ n : Nat, y = natCast n} : Set R), y ≤ x := by
    intro y ⟨n, hn⟩
    rw [hn]
    exact not_lt.mp fun h' => h ⟨n, h'⟩
  obtain ⟨s, hs, hlub⟩ := exists_lub {y | ∃ n : Nat, y = natCast n} ⟨0, 0, rfl⟩ ⟨x, hb⟩
  obtain ⟨y, ⟨n, hn⟩, hy⟩ := exists_mem_gt_of_lub hlub zero_lt_one
  rw [hn] at hy
  have h1 := hs (natCast (n + 1)) ⟨n + 1, rfl⟩
  rw [natCast_succ] at h1
  have h2 := add_lt_add_right hy 1
  rw [sub_add_cancel] at h2
  exact not_le.mpr h2 h1

def intCast : Int → R
  | Int.ofNat n => natCast n
  | Int.negSucc n => -natCast (n + 1)

theorem intCast_natCast (n : Nat) : (intCast (n : Int) : R) = natCast n := rfl

theorem intCast_zero : (intCast 0 : R) = 0 := rfl

theorem intCast_sub_one : ∀ k : Int, (intCast (k - 1) : R) = intCast k - 1
  | Int.ofNat 0 => by
      rw [show Int.ofNat 0 - 1 = Int.negSucc 0 from rfl]
      show -(natCast 1 : R) = natCast 0 - 1
      rw [natCast_succ, natCast_zero, zero_add, zero_sub]
  | Int.ofNat (n + 1) => by
      rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp only [Int.ofNat_eq_natCast]; omega]
      show (natCast n : R) = natCast (n + 1) - 1
      rw [natCast_succ, add_sub_cancel]
  | Int.negSucc n => by
      rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) by simp only [Int.negSucc_eq]; omega]
      show -(natCast (n + 1 + 1) : R) = -natCast (n + 1) - 1
      rw [natCast_succ (n + 1), neg_add]; rfl

theorem intCast_add_one (k : Int) : (intCast (k + 1) : R) = intCast k + 1 := by
  have h := intCast_sub_one (R := R) (k + 1)
  rw [Int.add_sub_cancel] at h
  rw [h, sub_add_cancel]

theorem intCast_add_natCast (k : Int) : ∀ n : Nat,
    (intCast (k + n) : R) = intCast k + natCast n
  | 0 => by rw [Int.natCast_zero, Int.add_zero]; exact (add_zero _).symm
  | n + 1 => by
      rw [Int.natCast_add, Int.natCast_one, ← Int.add_assoc, intCast_add_one,
        intCast_add_natCast k n, natCast_succ, add_assoc]

theorem intCast_neg_natCast_add (N : Nat) : (intCast (-(N : Int)) : R) + natCast N = 0 := by
  rw [← intCast_add_natCast, Int.add_left_neg]; rfl

theorem intCast_sub_natCast (k : Int) : ∀ n : Nat,
    (intCast (k - n) : R) = intCast k - natCast n
  | 0 => by rw [Int.natCast_zero, Int.sub_zero, natCast_zero, sub_zero]
  | n + 1 => by
      rw [show k - ((n + 1 : Nat) : Int) = k - (n : Int) - 1 by omega, intCast_sub_one,
        intCast_sub_natCast k n, natCast_succ, sub_def, sub_def, sub_def, neg_add, add_assoc]

theorem intCast_add (m : Int) : ∀ n : Int, (intCast (m + n) : R) = intCast m + intCast n
  | Int.ofNat k => intCast_add_natCast m k
  | Int.negSucc k => by
      rw [show m + Int.negSucc k = m - ((k + 1 : Nat) : Int) by simp only [Int.negSucc_eq]; omega,
        intCast_sub_natCast]
      rfl

theorem intCast_neg (m : Int) : (intCast (-m) : R) = -intCast m := by
  apply Eq.symm
  apply neg_eq_of_add_eq_zero
  rw [← intCast_add, Int.add_right_neg]; rfl

theorem exists_int_floor (x : R) : ∃ n : Int, intCast n ≤ x ∧ x < intCast n + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-x)
  obtain ⟨M, hM⟩ := exists_nat_gt x
  have base : (intCast (-(N : Int)) : R) ≤ x := by
    have h1 := intCast_neg_natCast_add (R := R) N
    have h2 := neg_lt_neg hN
    rw [neg_neg] at h2
    have h3 : (intCast (-(N : Int)) : R) = -natCast N := by
      rw [← add_sub_cancel (intCast (-(N : Int)) : R) (natCast N), h1, zero_sub]
    rw [h3]; exact le_of_lt h2
  have key : ∀ m : Nat, ∀ a : Int, (intCast a : R) ≤ x → x < intCast a + natCast m →
      ∃ k : Nat, (intCast (a + k) : R) ≤ x ∧ x < intCast (a + k) + 1 := by
    intro m
    induction m with
    | zero =>
        intro a ha hx
        rw [natCast_zero, add_zero] at hx
        exact absurd ha (not_le.mpr hx)
    | succ m ih =>
        intro a ha hx
        by_cases hm : x < intCast a + natCast m
        · exact ih a ha hm
        · refine ⟨m, ?_, ?_⟩
          · rw [intCast_add_natCast]; exact not_lt.mp hm
          · rw [intCast_add_natCast, add_assoc, ← natCast_succ]; exact hx
  have top : x < intCast (-(N : Int)) + natCast (N + M) := by
    rw [natCast_add, ← add_assoc, intCast_neg_natCast_add, zero_add]; exact hM
  obtain ⟨k, hk⟩ := key (N + M) (-(N : Int)) base top
  exact ⟨_, hk⟩

instance : TopologicalSpace R where
  IsOpen s := ∀ x ∈ s, ∃ ε, 0 < ε ∧ ∀ y, abs (y - x) < ε → y ∈ s
  isOpen_univ := fun _ _ => ⟨1, zero_lt_one, fun _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht x ⟨hxs, hxt⟩
    obtain ⟨ε₁, h₁, hs'⟩ := hs x hxs
    obtain ⟨ε₂, h₂, ht'⟩ := ht x hxt
    refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun y hy => ⟨?_, ?_⟩⟩
    · exact hs' y (lt_of_lt_of_le hy (min_le_left _ _))
    · exact ht' y (lt_of_lt_of_le hy (min_le_right _ _))
  isOpen_sUnion := by
    intro S hS x ⟨s, hsS, hxs⟩
    obtain ⟨ε, hε, h⟩ := hS s hsS x hxs
    exact ⟨ε, hε, fun y hy => ⟨s, hsS, h y hy⟩⟩

theorem isOpen_iff {s : Set R} :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε, 0 < ε ∧ ∀ y, abs (y - x) < ε → y ∈ s := Iff.rfl

def ball (x ε : R) : Set R := {y | abs (y - x) < ε}

theorem isOpen_ball (x ε : R) : IsOpen (ball x ε) := by
  intro y hy
  refine ⟨ε - abs (y - x), sub_pos.mpr hy, fun z hz => ?_⟩
  show abs (z - x) < ε
  have := add_lt_add_right hz (abs (y - x))
  rw [sub_add_cancel] at this
  exact lt_of_le_of_lt (abs_sub_le z y x) this

theorem mem_ball_self {x ε : R} (h : 0 < ε) : x ∈ ball x ε := by
  show abs (x - x) < ε
  rw [abs_sub_self]; exact h

section Continuity

variable {X : Type} [TopologicalSpace X]

theorem continuous_of_forall {f : X → R}
    (h : ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (f y - f x) < ε) :
    Continuous f := by
  intro s hs
  have heq : f ⁻¹' s = ⋃₀ {U | IsOpen U ∧ U ⊆ f ⁻¹' s} := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      obtain ⟨ε, hε, hball⟩ := hs (f x) hx
      obtain ⟨U, hUo, hxU, hU⟩ := h x ε hε
      exact ⟨U, ⟨hUo, fun y hy => hball (f y) (hU y hy)⟩, hxU⟩
    · intro ⟨U, ⟨_, hsub⟩, hxU⟩
      exact hsub x hxU
  rw [heq]
  exact isOpen_sUnion _ fun U hU => hU.1

theorem forall_of_continuous {f : X → R} (hf : Continuous f) (x : X) {ε : R} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (f y - f x) < ε :=
  ⟨f ⁻¹' ball (f x) ε, hf _ (isOpen_ball _ _), mem_ball_self hε, fun _ hy => hy⟩

theorem continuous_id' : Continuous (fun x : R => x) :=
  continuous_of_forall fun x ε hε => ⟨ball x ε, isOpen_ball x ε, mem_ball_self hε, fun _ hy => hy⟩

theorem continuous_const (c : R) : Continuous (fun _ : X => c) :=
  continuous_of_forall fun _ _ hε =>
    ⟨Set.univ, isOpen_univ, trivial, fun _ _ => by rw [abs_sub_self]; exact hε⟩

theorem continuous_add {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := by
  apply continuous_of_forall
  intro x ε hε
  obtain ⟨U, hU, hxU, hfU⟩ := forall_of_continuous hf x (half_pos hε)
  obtain ⟨V, hV, hxV, hgV⟩ := forall_of_continuous hg x (half_pos hε)
  refine ⟨U ∩ V, isOpen_inter _ _ hU hV, ⟨hxU, hxV⟩, fun y ⟨hyU, hyV⟩ => ?_⟩
  have e : f y + g y - (f x + g x) = (f y - f x) + (g y - g x) := by
    rw [sub_def, sub_def, sub_def, neg_add]; ac_rfl
  rw [e]
  refine lt_of_le_of_lt (abs_add _ _) ?_
  have := add_lt_add (hfU y hyU) (hgV y hyV)
  rwa [add_halves] at this

theorem continuous_neg {f : X → R} (hf : Continuous f) : Continuous (fun x => -f x) := by
  apply continuous_of_forall
  intro x ε hε
  obtain ⟨U, hU, hxU, hfU⟩ := forall_of_continuous hf x hε
  refine ⟨U, hU, hxU, fun y hy => ?_⟩
  have e : -f y - -f x = -(f y - f x) := by rw [sub_def, sub_def, neg_add]
  rw [e, abs_neg]; exact hfU y hy

theorem continuous_sub {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) := continuous_add hf (continuous_neg hg)

theorem continuous_mul {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := by
  apply continuous_of_forall
  intro x ε hε
  have hA : 0 < abs (f x) + 1 := lt_of_le_of_lt (abs_nonneg _) (lt_add_of_pos_right _ zero_lt_one)
  have hB : 0 < abs (g x) + 1 := lt_of_le_of_lt (abs_nonneg _) (lt_add_of_pos_right _ zero_lt_one)
  obtain ⟨U, hU, hxU, hfU⟩ :=
    forall_of_continuous hf x (lt_min zero_lt_one (div_pos (half_pos hε) hB))
  obtain ⟨V, hV, hxV, hgV⟩ := forall_of_continuous hg x (div_pos (half_pos hε) hA)
  refine ⟨U ∩ V, isOpen_inter _ _ hU hV, ⟨hxU, hxV⟩, fun y ⟨hyU, hyV⟩ => ?_⟩
  have hf1 := lt_of_lt_of_le (hfU y hyU) (min_le_left _ _)
  have hf2 := lt_of_lt_of_le (hfU y hyU) (min_le_right _ _)
  have hg2 := hgV y hyV
  have e : f y * g y - f x * g x = f y * (g y - g x) + g x * (f y - f x) := by
    rw [mul_sub, mul_sub, mul_comm (g x) (f y), mul_comm (g x) (f x), sub_def, sub_def, sub_def]
    calc f y * g y + -(f x * g x)
        = f y * g y + -(f x * g x) + 0 := (add_zero _).symm
      _ = f y * g y + -(f x * g x) + (f y * g x + -(f y * g x)) := by rw [add_neg_cancel]
      _ = f y * g y + -(f y * g x) + (f y * g x + -(f x * g x)) := by ac_rfl

  have hfy : abs (f y) ≤ abs (f x) + 1 :=
    le_trans _ _ _ (abs_le_abs_add_abs_sub (f y) (f x)) (add_le_add_left _ _ (le_of_lt hf1) _)
  have t1 : abs (f y) * abs (g y - g x) < ε / 2 := by
    calc abs (f y) * abs (g y - g x)
        ≤ (abs (f x) + 1) * abs (g y - g x) := mul_le_mul_of_nonneg_right hfy (abs_nonneg _)
      _ < (abs (f x) + 1) * (ε / 2 / (abs (f x) + 1)) := mul_lt_mul_of_pos_left hg2 hA
      _ = ε / 2 := mul_div_cancel_left _ (ne_of_lt hA).symm
  have t2 : abs (g x) * abs (f y - f x) < ε / 2 := by
    calc abs (g x) * abs (f y - f x)
        ≤ (abs (g x) + 1) * abs (f y - f x) :=
          mul_le_mul_of_nonneg_right (le_of_lt (lt_add_of_pos_right _ zero_lt_one)) (abs_nonneg _)
      _ < (abs (g x) + 1) * (ε / 2 / (abs (g x) + 1)) := mul_lt_mul_of_pos_left hf2 hB
      _ = ε / 2 := mul_div_cancel_left _ (ne_of_lt hB).symm
  rw [e]
  refine lt_of_le_of_lt (abs_add _ _) ?_
  rw [abs_mul, abs_mul]
  have := add_lt_add t1 t2
  rwa [add_halves] at this

end Continuity

def Icc (a b : R) : Set R := {x | a ≤ x ∧ x ≤ b}

theorem finite_insert {I : Type} {J : Set I} (hJ : J.Finite) (i : I) :
    ({j | j ∈ J ∨ j = i} : Set I).Finite := by
  obtain ⟨n, f, hf⟩ := hJ
  refine ⟨n + 1, fun k => if h : k.val < n then f ⟨k.val, h⟩ else i, ?_⟩
  intro j hj
  rcases hj with hj | hj
  · obtain ⟨k, hk⟩ := hf j hj
    exact ⟨⟨k.val, Nat.lt_succ_of_lt k.isLt⟩, by simp only [dif_pos k.isLt]; exact hk⟩
  · exact ⟨⟨n, Nat.lt_succ_self n⟩, by simp only [Nat.lt_irrefl, dite_false]; exact hj.symm⟩

theorem finite_singleton {I : Type} (i : I) : ({j | j = i} : Set I).Finite :=
  ⟨1, fun _ => i, fun _ hj => ⟨⟨0, Nat.zero_lt_one⟩, hj.symm⟩⟩

theorem isCompact_Icc (a b : R) : IsCompact (Icc a b) := by
  intro I U hU hcover
  by_cases hab : a ≤ b
  case neg =>
    exact ⟨∅, Set.Finite.empty, fun x ⟨h₁, h₂⟩ => absurd (le_trans _ _ _ h₁ h₂) hab⟩

  let P : R → Prop := fun x => ∃ J : Set I, J.Finite ∧ Icc a x ⊆ (⋃ i ∈ J, U i)
  let S : Set R := {x | a ≤ x ∧ x ≤ b ∧ P x}
  have haS : a ∈ S := by
    obtain ⟨i₀, hi₀⟩ := hcover a ⟨le_refl a, hab⟩
    refine ⟨le_refl a, hab, {j | j = i₀}, finite_singleton i₀, fun y ⟨h₁, h₂⟩ => ?_⟩
    have : y = a := le_antisymm _ _ h₂ h₁
    exact ⟨i₀, rfl, this ▸ hi₀⟩
  obtain ⟨c, hs, hlub⟩ := exists_lub S ⟨a, haS⟩ ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ c := hs a haS
  have hcb : c ≤ b := hlub b fun x hx => hx.2.1
  obtain ⟨i₁, hi₁⟩ := hcover c ⟨hac, hcb⟩
  obtain ⟨ε, hε, hball⟩ := hU i₁ c hi₁
  obtain ⟨x, ⟨hax, _, J, hJ, hJcov⟩, hx⟩ := exists_mem_gt_of_lub hlub hε

  have ext : ∀ d, d ≤ c + ε / 2 → P d := by
    intro d hd
    refine ⟨{j | j ∈ J ∨ j = i₁}, finite_insert hJ i₁, fun y ⟨hy₁, hy₂⟩ => ?_⟩
    rcases le_total y x with hyx | hyx
    · obtain ⟨i, hi, hyi⟩ := hJcov y ⟨hy₁, hyx⟩
      exact ⟨i, .inl hi, hyi⟩
    · refine ⟨i₁, .inr rfl, hball y (abs_sub_lt_of ?_ ?_)⟩
      · exact lt_of_lt_of_le hx hyx
      · exact lt_of_le_of_lt (le_trans _ _ _ hy₂ hd) (half_add_lt hε)
  by_cases hb : b ≤ c + ε / 2
  · obtain ⟨J', hJ', hcov'⟩ := ext b hb
    exact ⟨J', hJ', hcov'⟩
  · have hd : c + ε / 2 ∈ S :=
      ⟨le_trans _ _ _ hac (le_of_lt (lt_add_of_pos_right c (half_pos hε))),
        le_of_lt (not_le.mp hb), ext _ (le_refl _)⟩
    exact absurd (hs _ hd) (not_le.mpr (lt_add_of_pos_right c (half_pos hε)))

theorem Icc_connected {a b : R} {U V : Set R} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : ∀ x ∈ Icc a b, x ∈ U ∨ x ∈ V) (hdisj : ∀ x ∈ Icc a b, x ∈ U → x ∈ V → False)
    (hab : a ≤ b) (ha : a ∈ U) : ∀ x ∈ Icc a b, x ∈ U := by
  let S : Set R := {x | a ≤ x ∧ x ≤ b ∧ ∀ y, a ≤ y → y ≤ x → y ∈ U}
  have haS : a ∈ S := ⟨le_refl a, hab, fun y h₁ h₂ => le_antisymm _ _ h₂ h₁ ▸ ha⟩
  obtain ⟨c, hs, hlub⟩ := exists_lub S ⟨a, haS⟩ ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ c := hs a haS
  have hcb : c ≤ b := hlub b fun x hx => hx.2.1

  have hcU : c ∈ U := by
    rcases hcov c ⟨hac, hcb⟩ with h | h
    · exact h
    · obtain ⟨ε, hε, hball⟩ := hV c h
      obtain ⟨x, ⟨hax, hxb, hxU⟩, hx⟩ := exists_mem_gt_of_lub hlub hε
      exact absurd (hball x (abs_sub_lt_of hx (lt_of_le_of_lt (hs x ⟨hax, hxb, hxU⟩)
        (lt_add_of_pos_right c hε)))) (hdisj x ⟨hax, hxb⟩ (hxU x hax (le_refl x)))
  obtain ⟨ε, hε, hball⟩ := hU c hcU
  obtain ⟨x, ⟨_, _, hxU⟩, hx⟩ := exists_mem_gt_of_lub hlub hε
  have ext : ∀ y, a ≤ y → y ≤ c + ε / 2 → y ∈ U := by
    intro y hy₁ hy₂
    rcases le_total y x with hyx | hyx
    · exact hxU y hy₁ hyx
    · exact hball y (abs_sub_lt_of (lt_of_lt_of_le hx hyx)
        (lt_of_le_of_lt hy₂ (half_add_lt hε)))
  by_cases hb : b ≤ c + ε / 2
  · exact fun y ⟨hy₁, hy₂⟩ => ext y hy₁ (le_trans _ _ _ hy₂ hb)
  · have hd : c + ε / 2 ∈ S :=
      ⟨le_trans _ _ _ hac (le_of_lt (lt_add_of_pos_right c (half_pos hε))),
        le_of_lt (not_le.mp hb), fun y hy₁ hy₂ => ext y hy₁ hy₂⟩
    exact absurd (hs _ hd) (not_le.mpr (lt_add_of_pos_right c (half_pos hε)))

noncomputable def finMin : (n : Nat) → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, g => min (g 0) (finMin n fun k => g k.succ)

theorem finMin_pos : ∀ (n : Nat) (g : Fin n → R), (∀ k, 0 < g k) → 0 < finMin n g
  | 0, _, _ => zero_lt_one
  | n + 1, _, h => lt_min (h 0) (finMin_pos n _ fun k => h k.succ)

theorem finMin_le : ∀ (n : Nat) (g : Fin n → R) (k : Fin n), finMin n g ≤ g k
  | n + 1, g, k => by
      cases k using Fin.cases with
      | zero => exact min_le_left _ _
      | succ k => exact le_trans _ _ _ (min_le_right _ _) (finMin_le n (fun k => g k.succ) k)

theorem lebesgue {a b : R} {I : Type} (U : I → Set R) (hU : ∀ i, IsOpen (U i))
    (hcov : Icc a b ⊆ (⋃ i, U i)) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ Icc a b, ∃ i, ∀ y, abs (y - x) < δ → y ∈ U i := by
  have hloc : ∀ q : {p // p ∈ Icc a b}, ∃ r, 0 < r ∧ ∃ i, ∀ y, abs (y - q.1) < r → y ∈ U i := by
    intro q
    obtain ⟨i, hi⟩ := hcov q.1 q.2
    obtain ⟨r, hr, hball⟩ := hU i q.1 hi
    exact ⟨r, hr, i, hball⟩
  let r : {p // p ∈ Icc a b} → R := fun q => Classical.choose (hloc q)
  have hr : ∀ q, 0 < r q ∧ ∃ i, ∀ y, abs (y - q.1) < r q → y ∈ U i :=
    fun q => Classical.choose_spec (hloc q)
  let W : {p // p ∈ Icc a b} → Set R := fun q => ball q.1 (r q / 2)
  have hWcov : Icc a b ⊆ (⋃ q, W q) := fun x hx =>
    ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr ⟨x, hx⟩).1)⟩
  obtain ⟨J, ⟨n, f, hf⟩, hJcov⟩ :=
    isCompact_Icc a b W (fun q => isOpen_ball _ _) hWcov
  refine ⟨finMin n fun k => r (f k) / 2, finMin_pos n _ fun k => half_pos (hr (f k)).1, ?_⟩
  intro x hx
  obtain ⟨q, hqJ, hxq⟩ := hJcov x hx
  obtain ⟨k, rfl⟩ := hf q hqJ
  obtain ⟨i, hi⟩ := (hr (f k)).2
  refine ⟨i, fun y hy => hi y ?_⟩
  have h1 : abs (y - x) < r (f k) / 2 := lt_of_lt_of_le hy (finMin_le n _ k)
  have h2 : abs (x - (f k).1) < r (f k) / 2 := hxq
  have := add_lt_add h1 h2
  rw [add_halves] at this
  exact lt_of_le_of_lt (abs_sub_le y x (f k).1) this

end CompleteOrderedField

end

-- ─── 12_CoveringSpace（解答） ───
section

namespace CovSpace

section

variable {X Y Z : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

instance instTopSubtypeSet (W : Set X) : TopologicalSpace (Subtype W) := instTopSubtype W

theorem continuous_subtype_val {p : X → Prop} : Continuous (Subtype.val : Subtype p → X) :=
  continuous_fromInitial (Y := fun _ : Unit => X) (fun _ => tX)
    (fun _ => Subtype.val) ()

theorem continuous_subtype_mk {p : X → Prop} {f : Z → X} (hf : Continuous f)
    (h : ∀ z, p (f z)) : Continuous (fun z => (⟨f z, h z⟩ : Subtype p)) :=
  (continuous_toInitial_iff (Y := fun _ : Unit => X) (fun _ => tX)
    (fun _ => Subtype.val) tZ _).mpr fun _ => hf

theorem continuous_restrict {p : X → Prop} {f : X → Y} (hf : Continuous f) :
    Continuous (fun a : Subtype p => f a.1) :=
  Continuous.comp hf continuous_subtype_val

theorem isOpen_of_subtype_open {W : Set X} (hW : IsOpen W) {s : Set (Subtype W)}
    (hs : IsOpen s) : IsOpen {x | ∃ h : x ∈ W, (⟨x, h⟩ : Subtype W) ∈ s} := by
  obtain ⟨u, hu, rfl⟩ := isOpen_subtype_iff.mp hs
  have : {x | ∃ h : x ∈ W, (⟨x, h⟩ : Subtype W) ∈ Subtype.val ⁻¹' u} = W ∩ u := by
    apply Set.ext
    intro x
    exact ⟨fun ⟨h, hx⟩ => ⟨h, hx⟩, fun ⟨h, hx⟩ => ⟨h, hx⟩⟩
  rw [this]
  exact isOpen_inter _ _ hW hu

theorem continuous_of_locally {f : X → Y}
    (h : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ Continuous (fun a : Subtype W => f a.1)) :
    Continuous f := by
  intro s hs
  apply isOpen_of_nhds
  intro x hx
  obtain ⟨W, hW, hxW, hf⟩ := h x
  refine ⟨{y | ∃ h : y ∈ W, (⟨y, h⟩ : Subtype W) ∈ (fun a : Subtype W => f a.1) ⁻¹' s},
    isOpen_of_subtype_open hW (hf s hs), ⟨hxW, hx⟩, fun y ⟨_, hy⟩ => hy⟩

section Prod

variable {A B C : Type} [tA : TopologicalSpace A] [tB : TopologicalSpace B] [tC : TopologicalSpace C]

theorem continuous_fst : Continuous (@Prod.fst A B) :=
  continuous_fromInitial (Y := fun b => cond b A B)
    (fun b => match b with | true => tA | false => tB)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) true

theorem continuous_snd : Continuous (@Prod.snd A B) :=
  continuous_fromInitial (Y := fun b => cond b A B)
    (fun b => match b with | true => tA | false => tB)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) false

theorem continuous_prod_mk {f : C → A} {g : C → B} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => (f z, g z)) :=
  (continuous_toInitial_iff (Y := fun b => cond b A B)
    (fun b => match b with | true => tA | false => tB)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) tC _).mpr fun b =>
    match b with
    | true => hf
    | false => hg

end Prod

@[reducible] def rectTop : TopologicalSpace (X × Y) where
  IsOpen W := ∀ p ∈ W, ∃ U V, IsOpen U ∧ IsOpen V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧
    ∀ q : X × Y, q.1 ∈ U → q.2 ∈ V → q ∈ W
  isOpen_univ := fun p _ => ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, trivial, trivial,
    fun _ _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht p ⟨hps, hpt⟩
    obtain ⟨U₁, V₁, hU₁, hV₁, h1, h2, hst⟩ := hs p hps
    obtain ⟨U₂, V₂, hU₂, hV₂, h3, h4, htt⟩ := ht p hpt
    exact ⟨U₁ ∩ U₂, V₁ ∩ V₂, isOpen_inter _ _ hU₁ hU₂, isOpen_inter _ _ hV₁ hV₂, ⟨h1, h3⟩,
      ⟨h2, h4⟩, fun q hq hq' => ⟨hst q hq.1 hq'.1, htt q hq.2 hq'.2⟩⟩
  isOpen_sUnion := by
    intro S hS p ⟨s, hsS, hps⟩
    obtain ⟨U, V, hU, hV, h1, h2, hs⟩ := hS s hsS p hps
    exact ⟨U, V, hU, hV, h1, h2, fun q hq hq' => ⟨s, hsS, hs q hq hq'⟩⟩

theorem exists_rect {W : Set (X × Y)} (hW : IsOpen W) {p : X × Y} (hp : p ∈ W) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ q : X × Y, q.1 ∈ U → q.2 ∈ V → q ∈ W := by
  have h1 : @Continuous (X × Y) rectTop X tX Prod.fst := fun s hs q hq =>
    ⟨s, Set.univ, hs, isOpen_univ, hq, trivial, fun r hr _ => hr⟩
  have h2 : @Continuous (X × Y) rectTop Y tY Prod.snd := fun s hs q hq =>
    ⟨Set.univ, s, isOpen_univ, hs, trivial, hq, fun r _ hr => hr⟩
  exact initial_coarsest (Y := fun b => cond b X Y)
    (tY := fun b => match b with | true => tX | false => tY)
    (f := fun b => match b with | true => Prod.fst | false => Prod.snd) (t' := @rectTop X Y tX tY)
    (fun b => match b with | true => h1 | false => h2) W hW p hp

end

section

open CompleteOrderedField

variable {X Y Z : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

theorem isClosed_inter {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ t) := by
  have e : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
    apply Set.ext; intro x
    constructor
    · intro h
      by_cases hs' : x ∈ s
      · exact .inr fun ht' => h ⟨hs', ht'⟩
      · exact .inl hs'
    · intro h ⟨h1, h2⟩
      rcases h with h | h
      · exact h h1
      · exact h h2
  show IsOpen (s ∩ t)ᶜ
  rw [e]; exact isOpen_union hs ht

theorem isClosed_union {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) := by
  have e : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
    apply Set.ext; intro x
    exact ⟨fun h => ⟨fun h' => h (.inl h'), fun h' => h (.inr h')⟩,
      fun ⟨h1, h2⟩ h => h.elim h1 h2⟩
  show IsOpen (s ∪ t)ᶜ
  rw [e]; exact isOpen_inter _ _ hs ht

theorem continuous_of_closed {f : X → Y} (h : ∀ s, IsClosed s → IsClosed (f ⁻¹' s)) :
    Continuous f := by
  intro s hs
  have hc : IsClosed sᶜ := by
    show IsOpen sᶜᶜ
    rw [Set.compl_compl]; exact hs
  have := h _ hc
  have e : f ⁻¹' s = (f ⁻¹' sᶜ)ᶜ := by
    apply Set.ext; intro x
    exact ⟨fun hx hx' => hx' hx, fun hx => Classical.byContradiction fun hx' => hx hx'⟩
  rw [e]; exact this

theorem isClosed_preimage {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) := hf _ hs

theorem isClosed_of_subtype_closed {A : Set X} (hA : IsClosed A) {s : Set (Subtype A)}
    (hs : IsClosed s) : IsClosed {x | ∃ h : x ∈ A, (⟨x, h⟩ : Subtype A) ∈ s} := by
  obtain ⟨u, hu, hsu⟩ := isOpen_subtype_iff.mp hs
  have e : {x | ∃ h : x ∈ A, (⟨x, h⟩ : Subtype A) ∈ s} = A ∩ uᶜ := by
    apply Set.ext; intro x
    constructor
    · intro ⟨h, hx⟩
      refine ⟨h, fun hxu => ?_⟩
      have : (⟨x, h⟩ : Subtype A) ∈ sᶜ := by rw [hsu]; exact hxu
      exact this hx
    · intro ⟨h, hxu⟩
      refine ⟨h, Classical.byContradiction fun hx => hxu ?_⟩
      have : (⟨x, h⟩ : Subtype A) ∈ sᶜ := hx
      rw [hsu] at this; exact this
  rw [e]
  refine isClosed_inter hA ?_
  show IsOpen uᶜᶜ
  rw [Set.compl_compl]; exact hu

theorem continuous_of_closed_cover {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) {f : X → Y}
    (hfA : Continuous (fun a : Subtype A => f a.1)) (hfB : Continuous (fun a : Subtype B => f a.1)) :
    Continuous f := by
  apply continuous_of_closed
  intro s hs
  have e : f ⁻¹' s = {x | ∃ h : x ∈ A, (⟨x, h⟩ : Subtype A) ∈ (fun a : Subtype A => f a.1) ⁻¹' s} ∪
      {x | ∃ h : x ∈ B, (⟨x, h⟩ : Subtype B) ∈ (fun a : Subtype B => f a.1) ⁻¹' s} := by
    apply Set.ext; intro x
    constructor
    · intro hx
      rcases hcov x with h | h
      · exact .inl ⟨h, hx⟩
      · exact .inr ⟨h, hx⟩
    · intro h
      rcases h with ⟨_, hx⟩ | ⟨_, hx⟩ <;> exact hx
  rw [e]
  exact isClosed_union (isClosed_of_subtype_closed hA (hfA _ hs))
    (isClosed_of_subtype_closed hB (hfB _ hs))

variable {R : Type} [CompleteOrderedField R]

theorem isClosed_le_const (c : R) : IsClosed ({x | x ≤ c} : Set R) := by
  intro x hx
  have hx' : c < x := not_le.mp hx
  refine ⟨x - c, sub_pos.mpr hx', fun y hy hyc => ?_⟩
  have h1 := add_lt_add_right (abs_lt.mp hy).1 (x - c)
  rw [neg_add_cancel, sub_add_sub_cancel] at h1
  exact not_le.mpr (sub_pos.mp h1) hyc

theorem isClosed_ge_const (c : R) : IsClosed ({x | c ≤ x} : Set R) := by
  intro x hx
  have hx' : x < c := not_le.mp hx
  refine ⟨c - x, sub_pos.mpr hx', fun y hy hyc => ?_⟩
  have h1 := add_lt_add_right (abs_lt.mp hy).2 x
  rw [sub_add_cancel, sub_add_cancel] at h1
  exact not_le.mpr h1 hyc

end

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

abbrev UI (R : Type) [CompleteOrderedField R] : Type := Subtype (fun t : R => t ∈ Icc (0 : R) 1)

theorem zero_le_one' : (0 : R) ≤ 1 := le_of_lt zero_lt_one

theorem le_of_eq' {a b : R} (h : a = b) : a ≤ b := h ▸ le_refl a

def ui0 : UI R := ⟨0, le_refl 0, zero_le_one'⟩
def ui1 : UI R := ⟨1, zero_le_one', le_refl 1⟩

theorem UI.ext {s t : UI R} (h : s.1 = t.1) : s = t := by
  cases s; cases t; cases h; rfl

theorem div_two_le_div_two {a b : R} (h : a ≤ b) : a / 2 ≤ b / 2 :=
  mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos zero_lt_two))

theorem zero_div_two : (0 : R) / 2 = 0 := zero_mul _

theorem two_div_two : (2 : R) / 2 = 1 := mul_inv_cancel 2 two_ne_zero

theorem two_mul_div_two (t : R) : 2 * t / 2 = t := by
  rw [mul_comm]; exact mul_div_cancel two_ne_zero

theorem two_mul_half : (2 : R) * (1 / 2) = 1 := mul_div_cancel_left 1 two_ne_zero

theorem half_nonneg' : (0 : R) ≤ 1 / 2 := le_of_lt (half_pos zero_lt_one)

theorem half_le_one : (1 : R) / 2 ≤ 1 := le_of_lt (half_lt_self zero_lt_one)

theorem add_div_two (a b : R) : (a + b) / 2 = a / 2 + b / 2 := add_mul a b _

theorem sub_div_two (a b : R) : (a - b) / 2 = a / 2 - b / 2 := sub_mul a b _

theorem abs_div_two (a : R) : abs (a / 2) = abs a / 2 := by
  rw [div_def, abs_mul, abs_of_nonneg (le_of_lt (inv_pos zero_lt_two))]; rfl

theorem two_mul_le_two_mul {a b : R} (h : a ≤ b) : 2 * a ≤ 2 * b :=
  mul_le_mul_of_nonneg_left h (le_of_lt zero_lt_two)

theorem two_mul_one : (2 : R) * 1 = 2 := mul_one 2

def halfL (t : UI R) : UI R :=
  ⟨t.1 / 2, le_trans _ _ _ (le_of_eq' zero_div_two.symm) (div_two_le_div_two t.2.1),
    le_trans _ _ _ (div_two_le_div_two t.2.2) half_le_one⟩

def halfR (t : UI R) : UI R :=
  ⟨(t.1 + 1) / 2,
    le_trans _ _ _ half_nonneg' (by
      have := div_two_le_div_two (add_le_add_right t.2.1 1)
      rwa [zero_add] at this),
    by
      have := div_two_le_div_two (add_le_add_right t.2.2 1)
      rwa [← two_def, two_div_two] at this⟩

theorem halfL_one : halfL (ui1 : UI R) = halfR ui0 := UI.ext (by show (1 : R) / 2 = (0 + 1) / 2; rw [zero_add])

theorem halfL_zero : halfL (ui0 : UI R) = ui0 := UI.ext zero_div_two

theorem continuous_halfL : Continuous (halfL : UI R → UI R) :=
  continuous_subtype_mk (continuous_mul continuous_subtype_val (continuous_const _)) _

theorem continuous_halfR : Continuous (halfR : UI R → UI R) :=
  continuous_subtype_mk (continuous_mul (continuous_add continuous_subtype_val (continuous_const _))
    (continuous_const _)) _

theorem two_mul_mem {t : R} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 2 * t ∈ Icc (0 : R) 1 :=
  ⟨by have := two_mul_le_two_mul h0; rwa [mul_zero] at this,
   by have := two_mul_le_two_mul h1; rwa [two_mul_half] at this⟩

theorem two_mul_sub_one_mem {t : R} (h0 : 1 / 2 ≤ t) (h1 : t ≤ 1) : 2 * t - 1 ∈ Icc (0 : R) 1 := by
  refine ⟨sub_nonneg.mpr ?_, ?_⟩
  · have := two_mul_le_two_mul h0; rwa [two_mul_half] at this
  · have := add_le_add_right (two_mul_le_two_mul h1) (-1)
    rw [two_mul_one, two_def, add_assoc, add_neg_cancel, add_zero] at this
    exact this

noncomputable def halfPow : Nat → R
  | 0 => 1
  | n + 1 => halfPow n / 2

theorem halfPow_pos : ∀ n : Nat, (0 : R) < halfPow n
  | 0 => zero_lt_one
  | n + 1 => half_pos (halfPow_pos n)

theorem halfPow_le_one : ∀ n : Nat, (halfPow n : R) ≤ 1
  | 0 => le_refl 1
  | n + 1 => le_trans _ _ _ (le_of_lt (half_lt_self (halfPow_pos n))) (halfPow_le_one n)

theorem natCast_mul_halfPow_le : ∀ n : Nat, natCast n * (halfPow n : R) ≤ 1
  | 0 => by rw [natCast_zero, zero_mul]; exact zero_le_one'
  | n + 1 => by
      show natCast (n + 1) * (halfPow n / 2) ≤ (1 : R)
      rw [natCast_succ, div_def, ← mul_assoc, add_mul, one_mul, ← div_def]
      have h := add_le_add (natCast_mul_halfPow_le n) (halfPow_le_one n)
      rw [← two_def] at h
      have h2 := div_two_le_div_two h
      rwa [two_div_two] at h2

theorem exists_halfPow_lt {δ : R} (hδ : 0 < δ) : ∃ n : Nat, (halfPow n : R) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt δ⁻¹
  refine ⟨n, not_le.mp fun h => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left h (natCast_nonneg n)
  have h2 : 1 < natCast n * δ := by
    have := mul_lt_mul_of_pos_left hn hδ
    rwa [mul_comm δ, mul_comm δ, inv_mul_cancel (ne_of_lt hδ).symm] at this
  exact not_le.mpr (lt_of_lt_of_le h2 h1) (natCast_mul_halfPow_le n)

end

section

open CompleteOrderedField

theorem continuous_const_map {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (b : B) :
    Continuous (fun _ : A => b) := by
  intro s _
  by_cases hb : b ∈ s
  · have : (fun _ : A => b) ⁻¹' s = Set.univ := Set.ext fun _ => ⟨fun _ => trivial, fun _ => hb⟩
    rw [this]; exact isOpen_univ
  · have : (fun _ : A => b) ⁻¹' s = ∅ := Set.ext fun _ => ⟨fun h => hb h, fun h => False.elim h⟩
    rw [this]; exact isOpen_empty

variable {R : Type} [CompleteOrderedField R]
variable {E X : Type} [tE : TopologicalSpace E] [tX : TopologicalSpace X]

def EvenlyCovered (p : E → X) (U : Set X) : Prop :=
  ∃ (ι : Type) (V : ι → Set E) (s : ι → X → E),
    (∀ i, IsOpen (V i)) ∧
    (∀ e, p e ∈ U → ∃ i, e ∈ V i) ∧
    (∀ i j e, e ∈ V i → e ∈ V j → i = j) ∧
    (∀ i x, x ∈ U → s i x ∈ V i ∧ p (s i x) = x) ∧
    (∀ i e, e ∈ V i → s i (p e) = e) ∧
    (∀ i, Continuous (fun x : Subtype U => s i x.1))

structure CoveringMap (E X : Type) [TopologicalSpace E] [TopologicalSpace X] where
  toFun : E → X
  continuous_toFun : Continuous toFun
  evenly : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ EvenlyCovered toFun U

theorem sub_halfR (a b : R) : (a + 1) / 2 - (b + 1) / 2 = (a - b) / 2 := by
  rw [← sub_div_two, add_sub_add_right]

theorem lift_local_zero (p : CoveringMap E X) (Y : Type) [TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (N : Set Y) (hN : IsOpen N)
    (F0 : Y → E) (hF0 : Continuous (fun y : Subtype N => F0 y.1))
    (h0 : ∀ y ∈ N, p.toFun (F0 y) = F (y, ui0))
    (hsmall : ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ 1 → F (y, t) ∈ U)
    (y0 : Y) (hy0 : y0 ∈ N) : ∃ N' : Set Y, IsOpen N' ∧ y0 ∈ N' ∧ N' ⊆ N ∧ ∃ G : Y × UI R → E,
      (∀ y ∈ N', ∀ t, p.toFun (G (y, t)) = F (y, t)) ∧ (∀ y ∈ N', G (y, ui0) = F0 y) ∧
      Continuous (fun q : Subtype (fun q : Y × UI R => q.1 ∈ N') => G q.1) := by
  obtain ⟨U, hU, hUF⟩ := hsmall ui0
  obtain ⟨ι, V, s, hV, hcov, _, hs, hsp, hscont⟩ := hU
  have hFU : ∀ y ∈ N, ∀ t, F (y, t) ∈ U := by
    intro y hy t
    refine hUF y hy t ?_
    show abs (t.1 - 0) ≤ 1
    rw [sub_zero, abs_of_nonneg t.2.1]; exact t.2.2
  obtain ⟨i, hi⟩ := hcov (F0 y0) (by rw [h0 y0 hy0]; exact hFU y0 hy0 ui0)
  refine ⟨{y | ∃ h : y ∈ N, (⟨y, h⟩ : Subtype N) ∈ (fun y : Subtype N => F0 y.1) ⁻¹' V i},
    isOpen_of_subtype_open hN (hF0 _ (hV i)), ⟨hy0, hi⟩, fun y ⟨h, _⟩ => h,
    fun q => s i (F q), ?_, ?_, ?_⟩
  · intro y ⟨hy, _⟩ t
    exact (hs i _ (hFU y hy t)).2
  · intro y ⟨hy, hyV⟩
    show s i (F (y, ui0)) = F0 y
    rw [← h0 y hy]; exact hsp i _ hyV
  · exact (hscont i).comp (continuous_subtype_mk (hF.comp continuous_subtype_val)
      (fun q => hFU q.1.1 q.2.1 q.1.2))

theorem lift_local (p : CoveringMap E X) : ∀ (n : Nat) (Y : Type) [TopologicalSpace Y]
    (F : Y × UI R → X), Continuous F → ∀ (N : Set Y), IsOpen N →
    ∀ (F0 : Y → E), Continuous (fun y : Subtype N => F0 y.1) →
    (∀ y ∈ N, p.toFun (F0 y) = F (y, ui0)) →
    (∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, t) ∈ U) →
    ∀ y0 ∈ N, ∃ N' : Set Y, IsOpen N' ∧ y0 ∈ N' ∧ N' ⊆ N ∧ ∃ G : Y × UI R → E,
      (∀ y ∈ N', ∀ t, p.toFun (G (y, t)) = F (y, t)) ∧ (∀ y ∈ N', G (y, ui0) = F0 y) ∧
      Continuous (fun q : Subtype (fun q : Y × UI R => q.1 ∈ N') => G q.1)
  | 0 => by
    intro Y _ F hF N hN F0 hF0 h0 hsmall y0 hy0
    exact lift_local_zero p Y F hF N hN F0 hF0 h0 hsmall y0 hy0
  | n + 1 => by
    classical
    intro Y _ F hF N hN F0 hF0 h0 hsmall y0 hy0

    have hF1 : Continuous (fun q : Y × UI R => F (q.1, halfL q.2)) :=
      hF.comp (continuous_prod_mk continuous_fst (continuous_halfL.comp continuous_snd))
    have hsmall1 : ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
        ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, halfL t) ∈ U := by
      intro τ
      obtain ⟨U, hU, hUF⟩ := hsmall (halfL τ)
      refine ⟨U, hU, fun y hy t ht => hUF y hy (halfL t) ?_⟩
      show abs (t.1 / 2 - τ.1 / 2) ≤ halfPow n / 2
      rw [← sub_div_two, abs_div_two]; exact div_two_le_div_two ht
    have h01 : ∀ y ∈ N, p.toFun (F0 y) = F (y, halfL ui0) := by
      intro y hy; rw [halfL_zero]; exact h0 y hy
    obtain ⟨N1, hN1, hy1, hN1N, G1, hG1p, hG10, hG1c⟩ :=
      lift_local p n Y (fun q => F (q.1, halfL q.2)) hF1 N hN F0 hF0 h01 hsmall1 y0 hy0

    have hF2 : Continuous (fun q : Y × UI R => F (q.1, halfR q.2)) :=
      hF.comp (continuous_prod_mk continuous_fst (continuous_halfR.comp continuous_snd))
    have hsmall2 : ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
        ∀ y ∈ N1, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, halfR t) ∈ U := by
      intro τ
      obtain ⟨U, hU, hUF⟩ := hsmall (halfR τ)
      refine ⟨U, hU, fun y hy t ht => hUF y (hN1N y hy) (halfR t) ?_⟩
      show abs ((t.1 + 1) / 2 - (τ.1 + 1) / 2) ≤ halfPow n / 2
      rw [sub_halfR, abs_div_two]; exact div_two_le_div_two ht
    have hF0' : Continuous (fun y : Subtype N1 => G1 (y.1, ui1)) :=
      hG1c.comp (continuous_subtype_mk
        (continuous_prod_mk continuous_subtype_val (continuous_const_map ui1)) (fun y => y.2))
    have h02 : ∀ y ∈ N1, p.toFun (G1 (y, ui1)) = F (y, halfR ui0) := by
      intro y hy; rw [hG1p y hy ui1, halfL_one]
    obtain ⟨N2, hN2, hy2, hN2N1, G2, hG2p, hG20, hG2c⟩ :=
      lift_local p n Y (fun q => F (q.1, halfR q.2)) hF2 N1 hN1 (fun y => G1 (y, ui1)) hF0' h02
        hsmall2 y0 hy1

    let G : Y × UI R → E := fun q =>
      if h : q.2.1 ≤ 1 / 2 then G1 (q.1, ⟨2 * q.2.1, two_mul_mem q.2.2.1 h⟩)
      else G2 (q.1, ⟨2 * q.2.1 - 1, two_mul_sub_one_mem (le_of_lt (not_le.mp h)) q.2.2.2⟩)
    refine ⟨N2, hN2, hy2, fun y hy => hN1N y (hN2N1 y hy), G, ?_, ?_, ?_⟩
    · intro y hy t
      by_cases h : t.1 ≤ 1 / 2
      · show p.toFun (if h : t.1 ≤ 1 / 2 then _ else _) = _
        rw [dif_pos h, hG1p y (hN2N1 y hy)]
        exact congrArg (fun s => F (y, s)) (UI.ext (two_mul_div_two t.1))
      · show p.toFun (if h : t.1 ≤ 1 / 2 then _ else _) = _
        rw [dif_neg h, hG2p y hy]
        exact congrArg (fun s => F (y, s))
          (UI.ext (show (2 * t.1 - 1 + 1) / 2 = t.1 by rw [sub_add_cancel, two_mul_div_two]))
    · intro y hy
      show (if h : (0 : R) ≤ 1 / 2 then _ else _) = _
      rw [dif_pos half_nonneg', ← hG10 y (hN2N1 y hy)]
      exact congrArg (fun s => G1 (y, s)) (UI.ext (mul_zero 2))
    ·
      let Z := Subtype (fun q : Y × UI R => q.1 ∈ N2)
      have hval : Continuous (fun z : Z => z.1.2.1) :=
        continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
      have hA : IsClosed ({z | z.1.2.1 ≤ 1 / 2} : Set Z) :=
        isClosed_preimage hval (isClosed_le_const (1 / 2 : R))
      have hB : IsClosed ({z | 1 / 2 ≤ z.1.2.1} : Set Z) :=
        isClosed_preimage hval (isClosed_ge_const (1 / 2 : R))
      refine continuous_of_closed_cover hA hB (fun z => le_total _ _) ?_ ?_
      · have e : (fun a : Subtype ({z | z.1.2.1 ≤ 1 / 2} : Set Z) => G a.1.1) =
            fun a => G1 (a.1.1.1, ⟨2 * a.1.1.2.1, two_mul_mem a.1.1.2.2.1 a.2⟩) := by
          funext a
          show (if h : a.1.1.2.1 ≤ 1 / 2 then _ else _) = _
          rw [dif_pos (show a.1.1.2.1 ≤ 1 / 2 from a.2)]
        rw [e]
        exact hG1c.comp (continuous_subtype_mk
          (continuous_prod_mk (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
            (continuous_subtype_mk (continuous_mul (continuous_const _)
              (hval.comp continuous_subtype_val)) _))
          (fun a => hN2N1 _ a.1.2))
      · have e : (fun a : Subtype ({z | 1 / 2 ≤ z.1.2.1} : Set Z) => G a.1.1) =
            fun a => G2 (a.1.1.1, ⟨2 * a.1.1.2.1 - 1, two_mul_sub_one_mem a.2 a.1.1.2.2.2⟩) := by
          funext a
          show (if h : a.1.1.2.1 ≤ 1 / 2 then _ else _) = _
          by_cases h : a.1.1.2.1 ≤ 1 / 2
          · rw [dif_pos h]
            have ht : a.1.1.2.1 = 1 / 2 := le_antisymm _ _ h a.2
            have e1 : (⟨2 * a.1.1.2.1, two_mul_mem a.1.1.2.2.1 h⟩ : UI R) = ui1 :=
              UI.ext (by show 2 * a.1.1.2.1 = 1; rw [ht, two_mul_half])
            have e2 : (⟨2 * a.1.1.2.1 - 1, two_mul_sub_one_mem a.2 a.1.1.2.2.2⟩ : UI R) = ui0 :=
              UI.ext (by show 2 * a.1.1.2.1 - 1 = 0; rw [ht, two_mul_half, sub_self])
            rw [e1, e2, hG20 _ a.1.2]
          · rw [dif_neg h]
        rw [e]
        exact hG2c.comp (continuous_subtype_mk
          (continuous_prod_mk (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
            (continuous_subtype_mk (continuous_sub (continuous_mul (continuous_const _)
              (hval.comp continuous_subtype_val)) (continuous_const _)) _))
          (fun a => a.1.2))

end

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {E X : Type} [tE : TopologicalSpace E] [tX : TopologicalSpace X]

theorem exists_small (p : CoveringMap E X) {Y : Type} [tY : TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (y0 : Y) :
    ∃ N : Set Y, IsOpen N ∧ y0 ∈ N ∧ ∃ n : Nat, ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, t) ∈ U := by
  have hloc : ∀ t : UI R, ∃ c : Set X × Set Y × Set R,
      EvenlyCovered p.toFun c.1 ∧ IsOpen c.2.1 ∧ y0 ∈ c.2.1 ∧ IsOpen c.2.2 ∧ t.1 ∈ c.2.2 ∧
      ∀ y ∈ c.2.1, ∀ s : UI R, s.1 ∈ c.2.2 → F (y, s) ∈ c.1 := by
    intro t
    obtain ⟨U, hU, hxU, hEC⟩ := p.evenly (F (y0, t))
    obtain ⟨Nt, J, hNt, hJ, hy0, htJ, hrect⟩ := exists_rect (hF _ hU) (p := (y0, t)) hxU
    obtain ⟨O, hO, hJO⟩ := isOpen_subtype_iff.mp hJ
    refine ⟨(U, Nt, O), hEC, hNt, hy0, hO, ?_, fun y hy s hs => hrect (y, s) hy ?_⟩
    · have : t ∈ Subtype.val ⁻¹' O := by rw [← hJO]; exact htJ
      exact this
    · rw [hJO]; exact hs
  let c : UI R → Set X × Set Y × Set R := fun t => Classical.choose (hloc t)
  have hc : ∀ t, _ := fun t => Classical.choose_spec (hloc t)
  obtain ⟨J, ⟨m, f, hf⟩, hJcov⟩ :=
    isCompact_Icc (0 : R) 1 (fun t : UI R => (c t).2.2) (fun t => (hc t).2.2.2.1)
      (fun x hx => ⟨⟨x, hx⟩, (hc ⟨x, hx⟩).2.2.2.2.1⟩)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue (fun k : Fin m => (c (f k)).2.2) (fun k => (hc (f k)).2.2.2.1)
    (by
      intro x hx
      obtain ⟨t, htJ, hxt⟩ := hJcov x hx
      obtain ⟨k, hk⟩ := hf t htJ
      exact ⟨k, by show x ∈ (c (f k)).2.2; rw [hk]; exact hxt⟩)
  obtain ⟨n, hn⟩ := exists_halfPow_lt hδ
  refine ⟨Set.interFin m fun k => (c (f k)).2.1, isOpen_interFin m _ fun k => (hc (f k)).2.1,
    Set.mem_interFin m _ y0 fun k => (hc (f k)).2.2.1, n, fun τ => ?_⟩
  obtain ⟨k, hk⟩ := hleb τ.1 τ.2
  refine ⟨(c (f k)).1, (hc (f k)).1, fun y hy t ht => ?_⟩
  exact (hc (f k)).2.2.2.2.2 y (Set.interFin_mem m _ y hy k) t (hk t.1 (lt_of_le_of_lt ht hn))

theorem lift_unique (p : CoveringMap E X) {f g : UI R → E} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, p.toFun (f t) = p.toFun (g t)) (h0 : f ui0 = g ui0) : f = g := by
  have hA : IsOpen ({t | f t = g t} : Set (UI R)) := by
    apply isOpen_of_nhds
    intro t ht
    obtain ⟨U, _, hxU, ι, V, s, hV, hcov, _, _, hsp, _⟩ := p.evenly (p.toFun (f t))
    obtain ⟨i, hi⟩ := hcov (f t) hxU
    refine ⟨f ⁻¹' V i ∩ g ⁻¹' V i, isOpen_inter _ _ (hf _ (hV i)) (hg _ (hV i)),
      ⟨hi, show g t ∈ V i from (show f t = g t from ht) ▸ hi⟩, fun r ⟨hr1, hr2⟩ => ?_⟩
    show f r = g r
    rw [← hsp i _ hr1, ← hsp i _ hr2, hfg r]
  have hB : IsOpen ({t | f t ≠ g t} : Set (UI R)) := by
    apply isOpen_of_nhds
    intro t ht
    obtain ⟨U, _, hxU, ι, V, s, hV, hcov, hdisj, _, hsp, _⟩ := p.evenly (p.toFun (f t))
    obtain ⟨i, hi⟩ := hcov (f t) hxU
    obtain ⟨j, hj⟩ := hcov (g t) (by rw [← hfg t]; exact hxU)
    refine ⟨f ⁻¹' V i ∩ g ⁻¹' V j, isOpen_inter _ _ (hf _ (hV i)) (hg _ (hV j)), ⟨hi, hj⟩,
      fun r ⟨hr1, hr2⟩ hr => ?_⟩
    have hij : i = j := hdisj i j (g r) (show g r ∈ V i from hr ▸ (show f r ∈ V i from hr1)) hr2
    subst hij
    exact ht (by rw [← hsp i _ hi, ← hsp i _ hj, hfg t])
  obtain ⟨OA, hOA, hA'⟩ := isOpen_subtype_iff.mp hA
  obtain ⟨OB, hOB, hB'⟩ := isOpen_subtype_iff.mp hB
  have memA : ∀ t : UI R, f t = g t ↔ t.1 ∈ OA := fun t => by
    constructor
    · intro h; have : t ∈ ({t | f t = g t} : Set (UI R)) := h; rw [hA'] at this; exact this
    · intro h; have : t ∈ Subtype.val ⁻¹' OA := h; rw [← hA'] at this; exact this
  have memB : ∀ t : UI R, f t ≠ g t ↔ t.1 ∈ OB := fun t => by
    constructor
    · intro h; have : t ∈ ({t | f t ≠ g t} : Set (UI R)) := h; rw [hB'] at this; exact this
    · intro h; have : t ∈ Subtype.val ⁻¹' OB := h; rw [← hB'] at this; exact this
  have hall := Icc_connected hOA hOB
    (fun x hx => by
      by_cases h : f ⟨x, hx⟩ = g ⟨x, hx⟩
      · exact .inl ((memA ⟨x, hx⟩).mp h)
      · exact .inr ((memB ⟨x, hx⟩).mp h))
    (fun x hx h1 h2 => (memB ⟨x, hx⟩).mpr h2 ((memA ⟨x, hx⟩).mpr h1))
    zero_le_one' ((memA ui0).mp h0)
  funext t
  exact (memA t).mpr (hall t.1 t.2)

instance instTopUnit : TopologicalSpace Unit where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

theorem exists_lift_path (p : CoveringMap E X) (γ : UI R → X) (hγ : Continuous γ) (e0 : E)
    (he : p.toFun e0 = γ ui0) :
    ∃ γ' : UI R → E, Continuous γ' ∧ (∀ t, p.toFun (γ' t) = γ t) ∧ γ' ui0 = e0 := by
  have hF : Continuous (fun q : Unit × UI R => γ q.2) := hγ.comp continuous_snd
  obtain ⟨N, hN, hyN, n, hsmall⟩ := exists_small p (fun q : Unit × UI R => γ q.2) hF ()
  obtain ⟨N', _, hy', _, G, hGp, hG0, hGc⟩ :=
    lift_local p n Unit (fun q => γ q.2) hF N hN (fun _ => e0) (continuous_const_map e0)
      (fun _ _ => he) hsmall () hyN
  refine ⟨fun t => G ((), t), ?_, fun t => hGp () hy' t, hG0 () hy'⟩
  exact hGc.comp (continuous_subtype_mk
    (continuous_prod_mk (continuous_const_map ()) continuous_id) (fun _ => hy'))

theorem exists_lift_homotopy (p : CoveringMap E X) {Y : Type} [tY : TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (F0 : Y → E) (hF0 : Continuous F0)
    (h0 : ∀ y, p.toFun (F0 y) = F (y, ui0)) :
    ∃ G : Y × UI R → E, Continuous G ∧ (∀ q, p.toFun (G q) = F q) ∧ ∀ y, G (y, ui0) = F0 y := by
  have hpath : ∀ y, ∃ γ' : UI R → E, Continuous γ' ∧ (∀ t, p.toFun (γ' t) = F (y, t)) ∧
      γ' ui0 = F0 y := fun y =>
    exists_lift_path p (fun t => F (y, t))
      (hF.comp (continuous_prod_mk (continuous_const_map y) continuous_id)) (F0 y) (h0 y)
  let L : Y → UI R → E := fun y => Classical.choose (hpath y)
  have hL : ∀ y, Continuous (L y) ∧ (∀ t, p.toFun (L y t) = F (y, t)) ∧ L y ui0 = F0 y :=
    fun y => Classical.choose_spec (hpath y)
  refine ⟨fun q => L q.1 q.2, ?_, fun q => (hL q.1).2.1 q.2, fun y => (hL y).2.2⟩
  apply continuous_of_locally
  intro q0
  obtain ⟨N, hN, hyN, n, hsmall⟩ := exists_small p F hF q0.1
  obtain ⟨N', hN', hy', hN'N, G, hGp, hG0, hGc⟩ :=
    lift_local p n Y F hF N hN F0 (continuous_restrict hF0) (fun y _ => h0 y) hsmall q0.1 hyN

  have heq : ∀ y ∈ N', L y = fun t => G (y, t) := by
    intro y hy
    refine lift_unique p (hL y).1 ?_ (fun t => by rw [(hL y).2.1 t, hGp y hy t]) ?_
    · exact hGc.comp (continuous_subtype_mk
        (continuous_prod_mk (continuous_const_map y) continuous_id) (fun _ => hy))
    · rw [(hL y).2.2, hG0 y hy]
  refine ⟨Prod.fst ⁻¹' N', continuous_fst _ hN', hy', ?_⟩
  have e : (fun a : Subtype (Prod.fst ⁻¹' N' : Set (Y × UI R)) => L a.1.1 a.1.2) =
      fun a => G a.1 := by
    funext a
    rw [heq a.1.1 a.2]
  rw [e]
  exact hGc

end

end CovSpace

end

-- ════════ ここから本章：13_FundamentalGroupoid ════════
-- # 発展演習: 基本亜群と円周

namespace CovSpace

-- ## Part A: 道

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

noncomputable def glue {A : Type} (f g : UI R → A) (s : UI R) : A :=
  open Classical in
  if h : s.1 ≤ 1 / 2 then f ⟨2 * s.1, two_mul_mem s.2.1 h⟩
  else g ⟨2 * s.1 - 1, two_mul_sub_one_mem (le_of_lt (not_le.mp h)) s.2.2⟩

theorem glue_of_le {A : Type} (f g : UI R → A) {s : UI R} (h : s.1 ≤ 1 / 2) :
    glue f g s = f ⟨2 * s.1, two_mul_mem s.2.1 h⟩ := by
  unfold glue; rw [dif_pos h]

theorem glue_of_ge {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) {s : UI R} (h : 1 / 2 ≤ s.1) :
    glue f g s = g ⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ :=
  sorry

theorem continuous_glue_param {Z A : Type} [TopologicalSpace Z] [TopologicalSpace A]
    (f g : Z × UI R → A) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, f (z, ui1) = g (z, ui0)) :
    Continuous (fun q : Z × UI R => glue (fun s => f (q.1, s)) (fun s => g (q.1, s)) q.2) :=
  sorry

theorem continuous_glue {A : Type} [TopologicalSpace A] {f g : UI R → A}
    (hf : Continuous f) (hg : Continuous g) (hfg : f ui1 = g ui0) : Continuous (glue f g) := by
  have := continuous_glue_param (Z := Unit) (fun q => f q.2) (fun q => g q.2)
    (hf.comp continuous_snd) (hg.comp continuous_snd) (fun _ => hfg)
  exact this.comp (continuous_prod_mk (continuous_const_map ()) continuous_id)

structure Path (x y : X) where
  toFun : UI R → X
  continuous_toFun : Continuous toFun
  source : toFun ui0 = x
  target : toFun ui1 = y

variable {x y z w : X}

theorem Path.ext {γ δ : Path (R := R) x y} (h : ∀ s, γ.toFun s = δ.toFun s) : γ = δ := by
  cases γ; cases δ
  have : _ := funext h
  subst this
  rfl

def Path.refl (x : X) : Path (R := R) x x :=
  ⟨fun _ => x, continuous_const_map x, rfl, rfl⟩

noncomputable def Path.trans (γ : Path (R := R) x y) (δ : Path (R := R) y z) : Path (R := R) x z :=
  ⟨glue γ.toFun δ.toFun, continuous_glue γ.continuous_toFun δ.continuous_toFun
      (by rw [γ.target, δ.source]),
    by rw [glue_of_le (s := ui0) _ _ half_nonneg']
       exact (congrArg γ.toFun (UI.ext (mul_zero 2))).trans γ.source,
    by rw [glue_of_ge (s := ui1) _ _ (by rw [γ.target, δ.source]) half_le_one]
       exact (congrArg δ.toFun (UI.ext (show 2 * 1 - 1 = (1 : R) by
         rw [two_mul_one, two_def, add_sub_cancel]))).trans δ.target⟩

def uiRev (s : UI R) : UI R :=
  ⟨1 - s.1, sub_nonneg.mpr s.2.2, by
    have := add_le_add_left _ _ (neg_le_neg s.2.1) 1
    rwa [neg_zero, add_zero] at this⟩

theorem continuous_uiRev : Continuous (uiRev : UI R → UI R) :=
  continuous_subtype_mk (continuous_sub (continuous_const _) continuous_subtype_val) _

theorem uiRev_zero : uiRev (ui0 : UI R) = ui1 := UI.ext (sub_zero 1)
theorem uiRev_one : uiRev (ui1 : UI R) = ui0 := UI.ext (sub_self 1)

def Path.symm (γ : Path (R := R) x y) : Path (R := R) y x :=
  ⟨fun s => γ.toFun (uiRev s), γ.continuous_toFun.comp continuous_uiRev,
    by show γ.toFun (uiRev ui0) = y; rw [uiRev_zero, γ.target],
    by show γ.toFun (uiRev ui1) = x; rw [uiRev_one, γ.source]⟩

def Path.Homotopic (γ δ : Path (R := R) x y) : Prop :=
  ∃ H : UI R × UI R → X, Continuous H ∧ (∀ s, H (s, ui0) = γ.toFun s) ∧
    (∀ s, H (s, ui1) = δ.toFun s) ∧ (∀ t, H (ui0, t) = x) ∧ (∀ t, H (ui1, t) = y)

-- ### 再パラメータ化の補題

def uiMix (a b t : UI R) : UI R :=
  ⟨(1 - t.1) * a.1 + t.1 * b.1,
    add_nonneg (mul_nonneg _ _ (sub_nonneg.mpr t.2.2) a.2.1) (mul_nonneg _ _ t.2.1 b.2.1),
    by
      have h1 := mul_le_mul_of_nonneg_left a.2.2 (sub_nonneg.mpr t.2.2)
      have h2 := mul_le_mul_of_nonneg_left b.2.2 t.2.1
      have := add_le_add h1 h2
      rwa [mul_one, mul_one, sub_add_cancel] at this⟩

theorem uiMix_zero (a b : UI R) : uiMix a b ui0 = a :=
  UI.ext (show (1 - 0) * a.1 + 0 * b.1 = a.1 by rw [sub_zero, one_mul, zero_mul, add_zero])

theorem uiMix_one (a b : UI R) : uiMix a b ui1 = b :=
  UI.ext (show (1 - 1) * a.1 + 1 * b.1 = b.1 by rw [sub_self, zero_mul, one_mul, zero_add])

theorem uiMix_self (a t : UI R) : uiMix a a t = a :=
  UI.ext (show (1 - t.1) * a.1 + t.1 * a.1 = a.1 by rw [← add_mul, sub_add_cancel, one_mul])

theorem continuous_uiMix {Z : Type} [TopologicalSpace Z] {a b t : Z → UI R}
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun z => uiMix (a z) (b z) (t z)) :=
  continuous_subtype_mk (continuous_add
    (continuous_mul (continuous_sub (continuous_const _) (continuous_subtype_val.comp ht))
      (continuous_subtype_val.comp ha))
    (continuous_mul (continuous_subtype_val.comp ht) (continuous_subtype_val.comp hb))) _

theorem homotopic_reparam (γ : UI R → X) (hγ : Continuous γ) {φ ψ : UI R → UI R}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h0 : φ ui0 = ψ ui0) (h1 : φ ui1 = ψ ui1)
    (P Q : Path (R := R) x y) (hP : ∀ s, P.toFun s = γ (φ s)) (hQ : ∀ s, Q.toFun s = γ (ψ s)) :
    P.Homotopic Q :=
  sorry

end

-- ## Part B: ホモトピーと亜群の法則

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]
variable {x y z w : X}

-- ### 貼り合わせの計算規則

theorem glue_comp {A B : Type} (h : A → B) (f g : UI R → A) (s : UI R) :
    h (glue f g s) = glue (fun u => h (f u)) (fun u => h (g u)) s :=
  sorry

theorem glue_congr {A : Type} {f f' g g' : UI R → A} (hf : ∀ u, f u = f' u) (hg : ∀ u, g u = g' u)
    (s : UI R) : glue f g s = glue f' g' s := by
  rw [funext hf, funext hg]

theorem glue_const {A : Type} {f g : UI R → A} {c : A} (hf : ∀ u, f u = c) (hg : ∀ u, g u = c)
    (s : UI R) : glue f g s = c := by
  unfold glue
  by_cases hs : s.1 ≤ 1 / 2
  · rw [dif_pos hs, hf]
  · rw [dif_neg hs, hg]

theorem glue_zero {A : Type} (f g : UI R → A) : glue f g ui0 = f ui0 := by
  rw [glue_of_le (s := ui0) _ _ half_nonneg']
  exact congrArg f (UI.ext (mul_zero 2))

theorem glue_one {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) : glue f g ui1 = g ui1 := by
  rw [glue_of_ge (s := ui1) _ _ hfg half_le_one]
  exact congrArg g (UI.ext (show 2 * 1 - 1 = (1 : R) by rw [two_mul_one, two_def, add_sub_cancel]))

theorem glue_halfL {A : Type} (f g : UI R → A) (u : UI R) : glue f g (halfL u) = f u :=
  sorry

theorem glue_halfR {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) (u : UI R) :
    glue f g (halfR u) = g u := by
  have h : (1 : R) / 2 ≤ (u.1 + 1) / 2 := by
    have := div_two_le_div_two (add_le_add_right u.2.1 1)
    rwa [zero_add] at this
  rw [glue_of_ge (s := halfR u) _ _ hfg h]
  exact congrArg g (UI.ext (show 2 * ((u.1 + 1) / 2) - 1 = u.1 by
    rw [mul_div_cancel_left _ two_ne_zero, add_sub_cancel]))

theorem Path.trans_halfL (γ : Path (R := R) x y) (δ : Path (R := R) y z) (u : UI R) :
    (γ.trans δ).toFun (halfL u) = γ.toFun u := glue_halfL _ _ u

theorem Path.trans_halfR (γ : Path (R := R) x y) (δ : Path (R := R) y z) (u : UI R) :
    (γ.trans δ).toFun (halfR u) = δ.toFun u :=
  glue_halfR _ _ (by rw [γ.target, δ.source]) u

-- ### 同値関係

theorem Path.Homotopic.refl' (γ : Path (R := R) x y) : γ.Homotopic γ :=
  ⟨fun q => γ.toFun q.1, γ.continuous_toFun.comp continuous_fst, fun _ => rfl, fun _ => rfl,
    fun _ => γ.source, fun _ => γ.target⟩

theorem Path.Homotopic.symm' {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : δ.Homotopic γ :=
  sorry

theorem Path.Homotopic.trans' {γ δ ε : Path (R := R) x y} (h : γ.Homotopic δ) (k : δ.Homotopic ε) :
    γ.Homotopic ε :=
  sorry

-- ### 連接・逆道との両立

theorem continuous_swap {A B : Type} [TopologicalSpace A] [TopologicalSpace B] :
    Continuous (fun q : A × B => (q.2, q.1)) := continuous_prod_mk continuous_snd continuous_fst

theorem Path.Homotopic.trans_congr {γ γ' : Path (R := R) x y} {δ δ' : Path (R := R) y z}
    (h : γ.Homotopic γ') (k : δ.Homotopic δ') : (γ.trans δ).Homotopic (γ'.trans δ') :=
  sorry

theorem Path.Homotopic.symm_congr {γ γ' : Path (R := R) x y} (h : γ.Homotopic γ') :
    γ.symm.Homotopic γ'.symm := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  refine ⟨fun q => H (uiRev q.1, q.2), hH.comp (continuous_prod_mk
    (continuous_uiRev.comp continuous_fst) continuous_snd), fun s => h0 _, fun s => h1 _,
    fun t => ?_, fun t => ?_⟩
  · show H (uiRev ui0, t) = y; rw [uiRev_zero, hy]
  · show H (uiRev ui1, t) = x; rw [uiRev_one, hx]

-- ### 亜群の法則（再パラメータ化の補題から）

theorem continuous_id' {A : Type} [TopologicalSpace A] : Continuous (fun a : A => a) :=
  continuous_id

theorem Path.refl_trans (γ : Path (R := R) x y) : ((Path.refl x).trans γ).Homotopic γ :=
  sorry

theorem Path.trans_refl (γ : Path (R := R) x y) : (γ.trans (Path.refl y)).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) (fun _ => ui1))
    (ψ := fun u => u) (continuous_glue continuous_id' (continuous_const_map _) rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue γ.toFun (fun _ => y) s = γ.toFun (glue (fun u => u) (fun _ => ui1) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => rfl) (fun _ => γ.target.symm) s

theorem Path.trans_assoc (γ : Path (R := R) x y) (δ : Path (R := R) y z) (ε : Path (R := R) z w) :
    ((γ.trans δ).trans ε).Homotopic (γ.trans (δ.trans ε)) :=
  sorry

theorem Path.symm_trans (γ : Path (R := R) x y) : (γ.symm.trans γ).Homotopic (Path.refl y) :=
  sorry

theorem Path.trans_symm (γ : Path (R := R) x y) : (γ.trans γ.symm).Homotopic (Path.refl x) := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) uiRev)
    (ψ := fun _ => ui0) (continuous_glue continuous_id' continuous_uiRev uiRev_zero.symm)
    (continuous_const_map _) (glue_zero _ _) (by rw [glue_one _ _ uiRev_zero.symm, uiRev_one]) _ _
    (fun s => ?_) (fun s => γ.source.symm)
  show glue γ.toFun (fun u => γ.toFun (uiRev u)) s = γ.toFun (glue (fun u => u) uiRev s)
  rw [glue_comp γ.toFun]

end

-- ## Part C: モノドロミー

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

def PathClass (R : Type) [CompleteOrderedField R] (x y : X) : Type :=
  Quot (fun γ δ : Path (R := R) x y => γ.Homotopic δ)

namespace PathClass

variable {x y z w : X}

def mk (γ : Path (R := R) x y) : PathClass R x y := Quot.mk _ γ

theorem sound {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : mk γ = mk δ := Quot.sound h

def refl (x : X) : PathClass R x x := mk (Path.refl x)

noncomputable def comp (φ : PathClass R x y) (ψ : PathClass R y z) : PathClass R x z :=
  Quot.lift (fun γ => Quot.lift (fun δ => mk (γ.trans δ))
      (fun _ _ h => sound (Path.Homotopic.trans_congr (Path.Homotopic.refl' γ) h)) ψ)
    (fun _ _ h => by
      induction ψ using Quot.ind with
      | mk δ => exact sound (Path.Homotopic.trans_congr h (Path.Homotopic.refl' δ)))
    φ

def inv (φ : PathClass R x y) : PathClass R y x :=
  Quot.lift (fun γ => mk γ.symm) (fun _ _ h => sound (Path.Homotopic.symm_congr h)) φ

theorem refl_comp (φ : PathClass R x y) : (refl x).comp φ = φ := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.refl_trans γ)

theorem comp_refl (φ : PathClass R x y) : φ.comp (refl y) = φ := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.trans_refl γ)

theorem comp_assoc (φ : PathClass R x y) (ψ : PathClass R y z) (χ : PathClass R z w) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  induction φ using Quot.ind with
  | mk γ =>
    induction ψ using Quot.ind with
    | mk δ =>
      induction χ using Quot.ind with
      | mk ε => exact sound (Path.trans_assoc γ δ ε)

theorem inv_comp (φ : PathClass R x y) : φ.inv.comp φ = refl y := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.symm_trans γ)

theorem comp_inv (φ : PathClass R x y) : φ.comp φ.inv = refl x := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.trans_symm γ)

end PathClass

-- ### モノドロミー

variable {E : Type} [tE : TopologicalSpace E]

namespace CoveringMap

variable (p : CoveringMap E X)

abbrev Fiber (x : X) : Type := {e : E // p.toFun e = x}

theorem fiberExt {x : X} {a b : p.Fiber x} (h : a.1 = b.1) : a = b := by
  cases a; cases b; cases h; rfl

variable {x y z : X}

theorem fiber_start (γ : Path (R := R) x y) (a : p.Fiber x) : p.toFun a.1 = γ.toFun ui0 := by
  rw [a.2, γ.source]

noncomputable def liftEnd (γ : Path (R := R) x y) (a : p.Fiber x) : p.Fiber y :=
  ⟨Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1 (p.fiber_start γ a)) ui1,
   by rw [(Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
      (p.fiber_start γ a))).2.1, γ.target]⟩

theorem liftEnd_eq (γ : Path (R := R) x y) (a : p.Fiber x) {f : UI R → E} (hf : Continuous f)
    (hfp : ∀ t, p.toFun (f t) = γ.toFun t) (hf0 : f ui0 = a.1) : (p.liftEnd γ a).1 = f ui1 :=
  sorry

theorem liftEnd_homotopic {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) (a : p.Fiber x) :
    p.liftEnd γ a = p.liftEnd δ a :=
  sorry

noncomputable def transport (φ : PathClass R x y) (a : p.Fiber x) : p.Fiber y :=
  Quot.lift (fun γ => p.liftEnd γ a) (fun _ _ h => p.liftEnd_homotopic h a) φ

theorem transport_refl (a : p.Fiber x) : p.transport (PathClass.refl (R := R) x) a = a :=
  p.fiberExt (p.liftEnd_eq (Path.refl x) a (continuous_const_map a.1) (fun _ => a.2) rfl)

theorem transport_trans (φ : PathClass R x y) (ψ : PathClass R y z) (a : p.Fiber x) :
    p.transport (φ.comp ψ) a = p.transport ψ (p.transport φ a) :=
  sorry

end CoveringMap

end

-- ## Part D: 共通の枠組み

section

structure PathSystem (V : Type) where
  Hom : V → V → Type
  refl : (x : V) → Hom x x
  trans : {x y z : V} → Hom x y → Hom y z → Hom x z
  symm : {x y : V} → Hom x y → Hom y x
  refl_trans : ∀ {x y : V} (γ : Hom x y), trans (refl x) γ = γ
  trans_refl : ∀ {x y : V} (γ : Hom x y), trans γ (refl y) = γ
  trans_assoc : ∀ {x y z w : V} (γ : Hom x y) (δ : Hom y z) (ε : Hom z w),
    trans (trans γ δ) ε = trans γ (trans δ ε)
  symm_trans : ∀ {x y : V} (γ : Hom x y), trans (symm γ) γ = refl y
  trans_symm : ∀ {x y : V} (γ : Hom x y), trans γ (symm γ) = refl x

structure LiftSystem {V : Type} (P : PathSystem V) (F : V → Type) where
  transport : {x y : V} → P.Hom x y → F x → F y
  transport_refl : ∀ (x : V) (a : F x), transport (P.refl x) a = a
  transport_trans : ∀ {x y z : V} (γ : P.Hom x y) (δ : P.Hom y z) (a : F x),
    transport (P.trans γ δ) a = transport δ (transport γ a)

namespace LiftSystem

variable {V : Type} {P : PathSystem V} {F : V → Type} (L : LiftSystem P F)

theorem transport_bijective {x y : V} (γ : P.Hom x y) : Function.Bijective (L.transport γ) where
  injective := sorry
  surjective := sorry

end LiftSystem

-- ### 実例 1: グラフの被覆（`11_Covering.lean`）

def graphPathSystem (G : SGraph) : PathSystem G.V where
  Hom := SGraph.PathClass G
  refl := SGraph.PathClass.refl
  trans φ ψ := φ.comp ψ
  symm φ := φ.inv
  refl_trans := SGraph.PathClass.refl_comp
  trans_refl := SGraph.PathClass.comp_refl
  trans_assoc := SGraph.PathClass.comp_assoc
  symm_trans := SGraph.PathClass.inv_comp
  trans_symm := SGraph.PathClass.comp_inv

noncomputable def graphLiftSystem {Y X : SGraph} (p : SGraph.Covering Y X) :
    LiftSystem (graphPathSystem X) p.Fiber where
  transport := p.transport
  transport_refl _ a := p.transport_refl a
  transport_trans := p.transport_trans

-- ### 実例 2: 位相空間の被覆

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

noncomputable def topPathSystem (R : Type) [CompleteOrderedField R] (X : Type)
    [TopologicalSpace X] : PathSystem X where
  Hom := PathClass R
  refl := PathClass.refl
  trans φ ψ := φ.comp ψ
  symm φ := φ.inv
  refl_trans := PathClass.refl_comp
  trans_refl := PathClass.comp_refl
  trans_assoc := PathClass.comp_assoc
  symm_trans := PathClass.inv_comp
  trans_symm := PathClass.comp_inv

noncomputable def topLiftSystem {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : CoveringMap E X) : LiftSystem (topPathSystem R X) p.Fiber where
  transport := p.transport
  transport_refl _ a := p.transport_refl a
  transport_trans := p.transport_trans

example {Y X : SGraph} (p : SGraph.Covering Y X) {v w : X.V} (γ : SGraph.PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  (graphLiftSystem p).transport_bijective γ

example {E X : Type} [TopologicalSpace E] [TopologicalSpace X] (p : CoveringMap E X) {x y : X}
    (γ : PathClass R x y) : Function.Bijective (p.transport γ) :=
  (topLiftSystem p).transport_bijective γ

end

-- ## Part E: 円周

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

-- ### 整数の計算

theorem natCast_succ_ge_one (k : Nat) : (1 : R) ≤ natCast (k + 1) := by
  rw [natCast_succ]
  have := add_le_add_right (natCast_nonneg (R := R) k) 1
  rwa [zero_add] at this

theorem int_eq_zero_of_abs_lt_one : ∀ {k : Int}, abs (intCast k : R) < 1 → k = 0 :=
  sorry

theorem intCast_sub (m n : Int) : (intCast (m - n) : R) = intCast m - intCast n := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg]; rfl

theorem intCast_injective {m n : Int} (h : (intCast m : R) = intCast n) : m = n := by
  have : m - n = 0 := int_eq_zero_of_abs_lt_one (R := R)
    (by rw [intCast_sub, h, sub_self, abs_zero]; exact zero_lt_one)
  omega

theorem eq_of_close {a r w : R} {m : Int} (hr : abs (r - a) < 1 / 2) (hw : abs (w - a) < 1 / 2)
    (hm : w = r + intCast m) : w = r :=
  sorry

-- ### 円周 `R / ℤ`

def circleSetoid (R : Type) [CompleteOrderedField R] : Setoid R where
  r a b := ∃ n : Int, b = a + intCast n
  iseqv := {
    refl := fun a => ⟨0, (add_zero a).symm⟩
    symm := fun {a b} ⟨n, h⟩ => ⟨-n, by rw [h, intCast_neg, add_assoc, add_neg_cancel, add_zero]⟩
    trans := fun {a b c} ⟨m, h₁⟩ ⟨n, h₂⟩ => ⟨m + n, by rw [h₂, h₁, intCast_add, add_assoc]⟩ }

def Circle (R : Type) [CompleteOrderedField R] : Type := Quotient (circleSetoid R)

instance : TopologicalSpace (Circle R) :=
  inferInstanceAs (TopologicalSpace (Quot (circleSetoid R).r))

def proj (r : R) : Circle R := Quotient.mk _ r

theorem proj_eq_iff {a b : R} : proj a = proj b ↔ ∃ n : Int, b = a + intCast n :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem proj_add_int (a : R) (n : Int) : proj (a + intCast n) = proj a :=
  (proj_eq_iff.mpr ⟨n, rfl⟩).symm

theorem continuous_proj : Continuous (proj : R → Circle R) :=
  continuous_quotMk (circleSetoid R).r

theorem isOpen_circle_iff {s : Set (Circle R)} : IsOpen s ↔ IsOpen (proj ⁻¹' s) := Iff.rfl

theorem isOpen_image_proj {W : Set R} (hW : IsOpen W) :
    IsOpen ({z | ∃ w, w ∈ W ∧ proj w = z} : Set (Circle R)) :=
  sorry

-- ### `R → R/ℤ` は被覆

noncomputable def circleSec (a : R) (n : Int) (z : Circle R) : R :=
  open Classical in
  if h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z then Classical.choose h + intCast n else 0

theorem circleSec_spec {a : R} {z : Circle R} (h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z) (n : Int) :
    ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z ∧ circleSec a n z = r + intCast n := by
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  unfold circleSec; rw [dif_pos h]

theorem circleSec_proj {a r : R} (hr : abs (r - a) < 1 / 2) (n : Int) :
    circleSec a n (proj r) = r + intCast n := by
  obtain ⟨r', hr', hpr', hs⟩ := circleSec_spec ⟨r, hr, rfl⟩ n
  obtain ⟨m, hm⟩ := proj_eq_iff.mp hpr'
  rw [hs, ← eq_of_close hr' hr hm]

theorem abs_shift (r a : R) (n : Int) : abs (r + intCast n - (a + intCast n)) = abs (r - a) := by
  rw [add_sub_add_right]

theorem evenlyCovered_circle (a : R) :
    EvenlyCovered (proj : R → Circle R) {z | ∃ r, r ∈ ball a (1 / 2) ∧ proj r = z} :=
  sorry

def circleCovering : CoveringMap R (Circle R) where
  toFun := proj
  continuous_toFun := continuous_proj
  evenly := by
    intro x
    induction x using Quotient.ind with
    | _ a =>
      exact ⟨_, isOpen_image_proj (isOpen_ball a (1 / 2)), ⟨a, mem_ball_self (half_pos zero_lt_one),
        rfl⟩, evenlyCovered_circle a⟩

end

-- ## Part F: π₁(S¹) ≃ ℤ

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

def base : Circle R := proj 0

theorem proj_intCast (m : Int) : proj (intCast m : R) = base := by
  have := proj_add_int (0 : R) m
  rw [zero_add] at this
  exact this

def fibInt (m : Int) : circleCovering.Fiber (base : Circle R) := ⟨intCast m, proj_intCast m⟩

theorem fiber_int (a : circleCovering.Fiber (base : Circle R)) : ∃ n : Int, a.1 = intCast n :=
  sorry

theorem transport_fibInt (φ : PathClass R (base : Circle R) base) (m : Int) :
    (circleCovering.transport φ (fibInt m)).1 = (circleCovering.transport φ (fibInt 0)).1 + intCast m :=
  sorry

noncomputable def deg (φ : PathClass R (base : Circle R) base) : Int :=
  Classical.choose (fiber_int (circleCovering.transport φ (fibInt 0)))

theorem deg_spec (φ : PathClass R (base : Circle R) base) :
    circleCovering.transport φ (fibInt 0) = fibInt (deg φ) :=
  circleCovering.fiberExt (Classical.choose_spec (fiber_int (circleCovering.transport φ (fibInt 0))))

theorem deg_comp (φ ψ : PathClass R (base : Circle R) base) :
    deg (φ.comp ψ) = deg φ + deg ψ :=
  sorry

theorem deg_refl : deg (PathClass.refl (R := R) (base : Circle R)) = 0 := by
  apply intCast_injective (R := R)
  have h := congrArg Subtype.val (deg_spec (PathClass.refl (R := R) (base : Circle R)))
  rw [circleCovering.transport_refl] at h
  exact h.symm

theorem deg_inv (φ : PathClass R (base : Circle R) base) : deg φ.inv = -deg φ := by
  have h := deg_comp φ.inv φ
  rw [PathClass.inv_comp, deg_refl] at h
  omega

theorem deg_eq_zero {φ : PathClass R (base : Circle R) base} (h : deg φ = 0) :
    φ = PathClass.refl base :=
  sorry

theorem deg_injective : Function.Injective (deg (R := R)) :=
  sorry

def loopN (n : Int) : Path (R := R) (base : Circle R) base where
  toFun t := proj (intCast n * t.1)
  continuous_toFun := continuous_proj.comp (continuous_mul (continuous_const _) continuous_subtype_val)
  source := by show proj (intCast n * 0) = base; rw [mul_zero]; rfl
  target := by show proj (intCast n * 1) = base; rw [mul_one]; exact proj_intCast n

theorem deg_surjective : Function.Surjective (deg (R := R)) :=
  sorry

theorem pi1_circle :
    (∀ φ ψ : PathClass R (base : Circle R) base, deg (φ.comp ψ) = deg φ + deg ψ) ∧
      Function.Bijective (deg (R := R)) :=
  sorry

end

end CovSpace

#print axioms CovSpace.pi1_circle
