-- はじめての Lean — 11_Covering（ブラウザ版・自動生成）
-- 先頭には、この章が使う前の章（05_MathematicalTools・06_Topology）のコードをまとめてあります。
-- 本章は「ここから本章」の行から始まります（598 行目。Ctrl+G で行番号へ移動できます）。
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

-- ════════ ここから本章：11_Covering ════════
-- # 発展演習: グラフの被覆

-- ## Part A: Serre グラフと道

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

theorem term_bar (e : G.E) : G.term (G.bar e) = G.init e :=
  sorry

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
    Wf G v l₁ u → Wf G u l₂ w → Wf G v (l₁ ++ l₂) w :=
  sorry

theorem Wf.end_unique : ∀ {y w₁ w₂ : G.V} {m : List G.E},
    Wf G y m w₁ → Wf G y m w₂ → w₁ = w₂ :=
  sorry

theorem Wf.append_split : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E},
    Wf G v (l₁ ++ l₂) w → ∃ u, Wf G v l₁ u ∧ Wf G u l₂ w :=
  sorry

def revWord (G : SGraph) (l : List G.E) : List G.E := (l.map G.bar).reverse

theorem revWord_cons (e : G.E) (l : List G.E) :
    revWord G (e :: l) = revWord G l ++ [G.bar e] := by
  simp [revWord]

theorem revWord_append (l l' : List G.E) :
    revWord G (l ++ l') = revWord G l' ++ revWord G l := by
  simp [revWord]

theorem Wf.revWord : ∀ {v w : G.V} {l : List G.E},
    Wf G v l w → Wf G w (SGraph.revWord G l) v :=
  sorry

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

-- ## Part B: ホモトピーと正規形定理

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

theorem isReduced_rcons {e : G.E} : ∀ {m : List G.E}, IsReduced m → IsReduced (rcons e m) :=
  sorry

theorem reduce_isReduced : ∀ l : List G.E, IsReduced (reduce l) :=
  sorry

theorem rcons_rcons_bar (e : G.E) : ∀ (m : List G.E), IsReduced m →
    rcons e (rcons (G.bar e) m) = m :=
  sorry

theorem reduce_append_cancel (e : G.E) : ∀ (l₁ l₂ : List G.E),
    reduce (l₁ ++ e :: G.bar e :: l₂) = reduce (l₁ ++ l₂) :=
  sorry

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

theorem reduces_reduce : ∀ l : List G.E, Reduces G l (reduce l) :=
  sorry

theorem homotopic_iff_reduce_eq {l l' : List G.E} :
    Homotopic G l l' ↔ reduce l = reduce l' :=
  sorry

theorem reduce_eq_self_of_isReduced : ∀ {l : List G.E}, IsReduced l → reduce l = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by
      rw [reduce_cons, reduce_eq_self_of_isReduced h.2, rcons_cons, if_neg h.1]

theorem eq_of_homotopic_of_isReduced {l l' : List G.E}
    (hl : IsReduced l) (hl' : IsReduced l') (h : Homotopic G l l') : l = l' :=
  sorry

end Reduce

theorem Wf.of_append_cancel : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E} {e : G.E},
    Wf G v (l₁ ++ e :: G.bar e :: l₂) w → Wf G v (l₁ ++ l₂) w :=
  sorry

theorem Wf.of_reduces {v w : G.V} {l l' : List G.E} (h : Reduces G l l') :
    Wf G v l w → Wf G v l' w := by
  induction h with
  | cancel l₁ l₂ e => exact fun hw => Wf.of_append_cancel l₁ hw
  | refl l => exact id
  | trans _ _ ih₁ ih₂ => exact fun hw => ih₂ (ih₁ hw)

theorem Wf.reduce [DecidableEq G.E] {v w : G.V} {l : List G.E} (hw : Wf G v l w) :
    Wf G v (SGraph.reduce l) w :=
  sorry

end SGraph

example : SGraph.reduce (G := bouquet) [true, false, true] = [true] := rfl
example : SGraph.reduce (G := bouquet) [true, true, false, false] = [] := rfl

-- ## Part C: π₁ 亜群

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
    Homotopic G (revWord G l) (revWord G l') :=
  sorry

theorem homotopic_revWord_append : ∀ l : List G.E, Homotopic G (revWord G l ++ l) [] :=
  sorry

theorem homotopic_append_revWord : ∀ l : List G.E, Homotopic G (l ++ revWord G l) [] :=
  sorry

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

theorem refl_comp (γ : PathClass G v w) : (refl v).comp γ = γ :=
  sorry

theorem comp_refl (γ : PathClass G v w) : γ.comp (refl w) = γ :=
  sorry

theorem comp_assoc {u z : G.V} (γ : PathClass G v u) (δ : PathClass G u w)
    (ε : PathClass G w z) : (γ.comp δ).comp ε = γ.comp (δ.comp ε) :=
  sorry

theorem inv_comp (γ : PathClass G v w) : γ.inv.comp γ = refl w :=
  sorry

theorem comp_inv (γ : PathClass G v w) : γ.comp γ.inv = refl v :=
  sorry

end PathClass

end SGraph

-- ## Part D: 被覆と持ち上げ

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
  star_surj := sorry
  star_inj := sorry

namespace SGraph.Covering

variable {Y X : SGraph} (p : Covering Y X)

theorem exists_lift_word :
    ∀ (l : List X.E) (y : Y.V) {w : X.V}, Wf X (p.toV y) l w →
      ∃ w' : Y.V, ∃ m : List Y.E, Wf Y y m w' ∧ mapWord p.toE m = l ∧ p.toV w' = w :=
  sorry

theorem lift_word_unique :
    ∀ {m m' : List Y.E} {y w₁ w₂ : Y.V},
      Wf Y y m w₁ → Wf Y y m' w₂ → mapWord p.toE m = mapWord p.toE m' → m = m' :=
  sorry

theorem endpoint_of_reduces :
    ∀ {l l' : List X.E}, Reduces X l l' →
      ∀ {y b : Y.V} {m : List Y.E}, Wf Y y m b → mapWord p.toE m = l →
        ∃ m' : List Y.E, Wf Y y m' b ∧ mapWord p.toE m' = l' :=
  sorry

theorem endpoint_eq {l l' : List X.E}
    (hh : Homotopic X l l') {y b b' : Y.V} {m m' : List Y.E}
    (hm : Wf Y y m b) (hmapm : mapWord p.toE m = l)
    (hm' : Wf Y y m' b') (hmapm' : mapWord p.toE m' = l') : b = b' :=
  sorry

-- ## Part E: モノドロミー

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
    p.transport (PathClass.refl v) a = a :=
  sorry

theorem transport_trans {v u w : X.V}
    (γ : PathClass X v u) (δ : PathClass X u w) (a : p.Fiber v) :
    p.transport (γ.comp δ) a = p.transport δ (p.transport γ a) :=
  sorry

theorem transport_bijective {v w : X.V} (γ : PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  sorry

end SGraph.Covering

open SGraph

def loopWf : Wf bouquet () [true] () :=
  Wf.cons (G := bouquet) true (Wf.nil (bouquet.term true))

example (i : Int) :
    (zcoverCovering.transport (PathClass.mk loopWf) ⟨i, rfl⟩).1 = i + 1 :=
  zcoverCovering.liftEnd_eq ⟨i, rfl⟩ loopWf
    (Wf.cons (G := zcover) ((i, true) : Int × Bool) (Wf.nil (zcover.term (i, true)))) rfl

-- ## Part F: π₁(花束) ≃ ℤ

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
    (e.2 = true ∧ v < w) ∨ (e.2 = false ∧ w < v) :=
  sorry

theorem zc_reduced_closed : ∀ {m : List zcover.E} {v : Int},
    Wf zcover v m v → IsReduced m → m = [] :=
  sorry

def shiftWord (k : Int) (m : List zcover.E) : List zcover.E :=
  m.map (fun e => (e.1 + k, e.2))

theorem mapWord_shift (k : Int) : ∀ (m : List zcover.E),
    mapWord zcoverCovering.toE (shiftWord k m) = mapWord zcoverCovering.toE m
  | [] => rfl
  | e :: m => congrArg (fun t => e.2 :: t) (mapWord_shift k m)

theorem shift_wf (k : Int) : ∀ (m : List zcover.E) {v w : Int},
    Wf zcover v m w → Wf zcover (v + k) (shiftWord k m) (w + k) :=
  sorry

abbrev triv : PathClass bouquet () () := PathClass.refl (G := bouquet) ()

def basePt : zcoverCovering.Fiber () := ⟨(0 : Int), rfl⟩

noncomputable def deg (γ : PathClass bouquet () ()) : Int :=
  (zcoverCovering.transport γ basePt).1

theorem transport_apply (γ : PathClass bouquet () ()) (i : Int) :
    (zcoverCovering.transport γ ⟨i, rfl⟩).1 = deg γ + i :=
  sorry

theorem deg_comp (γ δ : PathClass bouquet () ()) :
    deg (γ.comp δ) = deg γ + deg δ :=
  sorry

theorem deg_refl : deg triv = 0 :=
  congrArg Subtype.val (zcoverCovering.transport_refl basePt)

theorem deg_inv (γ : PathClass bouquet () ()) : deg γ.inv = - deg γ :=
  sorry

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
    γ = triv :=
  sorry

theorem deg_injective : Function.Injective deg :=
  sorry

theorem deg_loopPow : ∀ k : Nat, deg (loopPow k) = Int.ofNat k
  | 0 => deg_refl
  | k + 1 => by
      have h := deg_comp (loopPow k) loop
      rw [deg_loopPow k, deg_loop] at h
      exact h

theorem deg_surjective : Function.Surjective deg :=
  sorry

theorem pi1_bouquet :
    (∀ γ δ : PathClass bouquet () (), deg (γ.comp δ) = deg γ + deg δ) ∧
      Function.Bijective deg :=
  sorry

#print axioms pi1_bouquet
