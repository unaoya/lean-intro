-- はじめての Lean — 09_Ascoli（ブラウザ版・自動生成）
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

-- ════════ ここから本章：09_Ascoli ════════
-- # 発展演習: Ascoli の定理（ブルバキ流）

-- ## Part A: 一様構造

namespace Set

variable {α : Type}

theorem subset_antisymm {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  ext fun a => ⟨h₁ a, h₂ a⟩

def compRel (V W : Set (α × α)) : Set (α × α) := {p | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W}

def swapRel (V : Set (α × α)) : Set (α × α) := {p | (p.2, p.1) ∈ V}

theorem finite_of_list (L : List α) : Set.Finite {a | a ∈ L} :=
  ⟨L.length, L.get, fun _ ha => List.get_of_mem ha⟩

theorem Finite.exists_list {s : Set α} (hs : s.Finite) : ∃ L : List α, ∀ a ∈ s, a ∈ L :=
  have ⟨_, f, hf⟩ := hs
  ⟨List.ofFn f, fun a ha => List.mem_ofFn.mpr (hf a ha)⟩

end Set

class UniformSpace (α : Type) where
  /-- 近縁の全体。 -/
  Entourage : Set (Set (α × α))
  /-- 全体の関係は近縁。 -/
  univ_mem : Set.univ ∈ Entourage
  /-- 近縁より大きい関係は近縁。 -/
  mono : ∀ {V W : Set (α × α)}, V ∈ Entourage → V ⊆ W → W ∈ Entourage
  /-- 2つの近縁の共通部分は近縁。 -/
  inter_mem : ∀ {V W : Set (α × α)}, V ∈ Entourage → W ∈ Entourage → V ∩ W ∈ Entourage
  /-- 近縁は対角線を含む。 -/
  refl : ∀ {V : Set (α × α)}, V ∈ Entourage → ∀ a, (a, a) ∈ V
  /-- 近縁の逆関係は近縁。 -/
  symm : ∀ {V : Set (α × α)}, V ∈ Entourage → Set.swapRel V ∈ Entourage
  /-- 「半分」の近縁がある。 -/
  comp : ∀ {V : Set (α × α)}, V ∈ Entourage → ∃ W, W ∈ Entourage ∧ Set.compRel W W ⊆ V

notation "𝓤 " α:max => @UniformSpace.Entourage α _

namespace UniformSpace

variable {α : Type} [UniformSpace α]

theorem exists_half {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c, (a, b) ∈ W → (b, c) ∈ W → (a, c) ∈ V :=
  sorry

theorem exists_third {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c d, (a, b) ∈ W → (b, c) ∈ W → (c, d) ∈ W → (a, d) ∈ V :=
  sorry

instance toTopologicalSpace : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, ∃ V ∈ 𝓤 α, ∀ b, (a, b) ∈ V → b ∈ s
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

theorem exists_open_ball {V : Set (α × α)} (hV : V ∈ 𝓤 α) (a : α) :
    ∃ O : Set α, IsOpen O ∧ a ∈ O ∧ ∀ b ∈ O, (a, b) ∈ V :=
  sorry

end UniformSpace

open UniformSpace

-- ## Part B: 一様収束の一様構造と等連続性

section FunctionSpace

variable {X Y : Type} [UniformSpace Y]

def unifRel (V : Set (Y × Y)) : Set ((X → Y) × (X → Y)) := {p | ∀ x, (p.1 x, p.2 x) ∈ V}

instance uniformFun : UniformSpace (X → Y) where
  Entourage := {𝒱 | ∃ V ∈ 𝓤 Y, unifRel V ⊆ 𝒱}
  univ_mem := sorry
  mono := sorry
  inter_mem := sorry
  refl := sorry
  symm := sorry
  comp := sorry

variable [TopologicalSpace X]

def EquicontinuousAt (H : Set (X → Y)) (x : X) : Prop :=
  ∀ V ∈ 𝓤 Y, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ V

def Equicontinuous (H : Set (X → Y)) : Prop := ∀ x, EquicontinuousAt H x

theorem Equicontinuous.mono {H H' : Set (X → Y)} (hH : Equicontinuous H) (h : H' ⊆ H) :
    Equicontinuous H' :=
  sorry

theorem equicontinuous_singleton {f : X → Y} (hf : Continuous f) :
    Equicontinuous {g | g = f} :=
  sorry

-- ## Part C: 核心補題（Théorème 1 の有限版）

theorem Equicontinuous.finite_control [CompactSpace X] {H : Set (X → Y)}
    (hH : Equicontinuous H) {V : Set (Y × Y)} (hV : V ∈ 𝓤 Y) :
    ∃ W ∈ 𝓤 Y, ∃ P : List X, ∀ f ∈ H, ∀ g ∈ H,
      (∀ p ∈ P, (f p, g p) ∈ W) → ∀ x, (f x, g x) ∈ V :=
  sorry

end FunctionSpace

-- ## Part D: 全有界性と主定理

section TotallyBounded

variable {α : Type}

def Small (V : Set (α × α)) (A : Set α) : Prop := ∀ a ∈ A, ∀ b ∈ A, (a, b) ∈ V

def TotallyBounded [UniformSpace α] (s : Set α) : Prop :=
  ∀ V ∈ 𝓤 α, ∃ L : List (Set α), (∀ A ∈ L, Small V A) ∧ ∀ a ∈ s, ∃ A ∈ L, a ∈ A

def List.interCover (L M : List (Set α)) : List (Set α) :=
  L.flatMap fun A => M.map fun B => A ∩ B

theorem List.mem_interCover {L M : List (Set α)} {C : Set α} (h : C ∈ List.interCover L M) :
    ∃ A ∈ L, ∃ B ∈ M, C = A ∩ B := by
  have ⟨A, hA, hC⟩ := List.mem_flatMap.mp h
  have ⟨B, hB, hAB⟩ := List.mem_map.mp hC
  exact ⟨A, hA, B, hB, hAB.symm⟩

theorem List.interCover_covers {s : Set α} {L M : List (Set α)}
    (hL : ∀ a ∈ s, ∃ A ∈ L, a ∈ A) (hM : ∀ a ∈ s, ∃ B ∈ M, a ∈ B) :
    ∀ a ∈ s, ∃ C ∈ List.interCover L M, a ∈ C := by
  intro a ha
  have ⟨A, hA, haA⟩ := hL a ha
  have ⟨B, hB, haB⟩ := hM a ha
  exact ⟨A ∩ B, List.mem_flatMap.mpr ⟨A, hA, List.mem_map_of_mem hB⟩, haA, haB⟩

theorem TotallyBounded.subset [UniformSpace α] {s t : Set α} (hs : TotallyBounded s)
    (h : t ⊆ s) : TotallyBounded t :=
  sorry

variable {X Y : Type} [UniformSpace Y]

theorem finite_points_cover {H : Set (X → Y)}
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) {W : Set (Y × Y)} (hW : W ∈ 𝓤 Y) :
    ∀ P : List X, ∃ C : List (Set (X → Y)),
      (∀ S ∈ C, ∀ f ∈ S, ∀ g ∈ S, ∀ p ∈ P, (f p, g p) ∈ W) ∧ ∀ f ∈ H, ∃ S ∈ C, f ∈ S :=
  sorry

variable [TopologicalSpace X]

theorem ascoli [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) : TotallyBounded H :=
  sorry

end TotallyBounded

-- ## Part E: 反例——等連続性の仮定は外せない

namespace Counterexample

instance : TopologicalSpace (Option Nat) where
  IsOpen s := none ∈ s → ∃ N, ∀ n, N ≤ n → some n ∈ s
  isOpen_univ := fun _ => ⟨0, fun _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht ⟨h₁, h₂⟩
    have ⟨N₁, hN₁⟩ := hs h₁
    have ⟨N₂, hN₂⟩ := ht h₂
    exact ⟨N₁ + N₂, fun n hn =>
      ⟨hN₁ n (Nat.le_trans (Nat.le_add_right N₁ N₂) hn),
       hN₂ n (Nat.le_trans (Nat.le_add_left N₂ N₁) hn)⟩⟩
  isOpen_sUnion := by
    intro S hS ⟨s, hsS, hs⟩
    have ⟨N, hN⟩ := hS s hsS hs
    exact ⟨N, fun n hn => ⟨s, hsS, hN n hn⟩⟩

instance : CompactSpace (Option Nat) where
  isCompact_univ := sorry

def diagonal (α : Type) : Set (α × α) := {p | p.1 = p.2}

@[reducible] def discreteUniformity (α : Type) : UniformSpace α where
  Entourage := {V | ∀ a, (a, a) ∈ V}
  univ_mem := fun _ => trivial
  mono := fun hV h a => h _ (hV a)
  inter_mem := fun hV hW a => ⟨hV a, hW a⟩
  refl := fun hV => hV
  symm := fun hV a => hV a
  comp := fun hV =>
    ⟨diagonal α, fun _ => rfl, fun ⟨a, b⟩ ⟨z, (h₁ : a = z), (h₂ : z = b)⟩ => by
      rw [← h₂, ← h₁]
      exact hV a⟩

instance : UniformSpace Bool := discreteUniformity Bool

def δ (n : Nat) : Option Nat → Bool
  | none => false
  | some m => decide (m = n)

def H : Set (Option Nat → Bool) := {f | ∃ n, f = δ n}

theorem totallyBounded_bool (s : Set Bool) : TotallyBounded s :=
  sorry

theorem not_equicontinuousAt : ¬ EquicontinuousAt H none :=
  sorry

theorem exists_avoid (L : List (Set (Option Nat → Bool)))
    (hL : ∀ A ∈ L, Small (unifRel (diagonal Bool)) A) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ A ∈ L, δ n ∉ A :=
  sorry

theorem not_totallyBounded : ¬ TotallyBounded H :=
  sorry

end Counterexample

-- ## Part F: 逆向き——全有界なら等連続

section Converse

variable {X Y : Type} [UniformSpace Y]

theorem TotallyBounded.eval {H : Set (X → Y)} (hH : TotallyBounded H) (x : X) :
    TotallyBounded ((fun f => f x) '' H) :=
  sorry

variable [TopologicalSpace X]

theorem TotallyBounded.equicontinuous {H : Set (X → Y)} (hc : ∀ f ∈ H, Continuous f)
    (hH : TotallyBounded H) : Equicontinuous H :=
  sorry

end Converse

-- ## Part G: フィルターと Zorn の補題

structure Filter (α : Type) where
  /-- 属する集合の全体。 -/
  sets : Set (Set α)
  /-- 全体集合は属する。 -/
  univ_mem : Set.univ ∈ sets
  /-- 属する集合より大きい集合は属する。 -/
  mono : ∀ {s t : Set α}, s ∈ sets → s ⊆ t → t ∈ sets
  /-- 2つの共通部分も属する。 -/
  inter_mem : ∀ {s t : Set α}, s ∈ sets → t ∈ sets → s ∩ t ∈ sets

namespace Filter

variable {α β : Type}

instance : Membership (Set α) (Filter α) := ⟨fun F s => s ∈ F.sets⟩

structure IsUltra (F : Filter α) : Prop where
  /-- 空集合は属さない。 -/
  empty_not_mem : (∅ : Set α) ∉ F
  /-- どの集合も、それ自身か補集合が属する。 -/
  mem_or_compl_mem : ∀ s : Set α, s ∈ F ∨ sᶜ ∈ F

theorem IsUltra.compl_mem {F : Filter α} (hF : F.IsUltra) {s : Set α} (hs : s ∉ F) : sᶜ ∈ F :=
  (hF.mem_or_compl_mem s).resolve_left hs

theorem nonempty_of_mem {F : Filter α} (hF : (∅ : Set α) ∉ F) {s : Set α} (hs : s ∈ F) :
    ∃ a, a ∈ s :=
  Classical.byContradiction fun h => hF (F.mono hs fun a ha => h ⟨a, ha⟩)

def map (f : α → β) (F : Filter α) : Filter β where
  sets := {s | f ⁻¹' s ∈ F}
  univ_mem := F.univ_mem
  mono := fun hs h => F.mono hs fun a ha => h (f a) ha
  inter_mem := fun hs ht => F.inter_mem hs ht

theorem IsUltra.map {F : Filter α} (hF : F.IsUltra) (f : α → β) : (F.map f).IsUltra :=
  sorry

theorem mem_list_inter (F : Filter α) {I : Type} (s : I → Set α) :
    ∀ L : List I, (∀ i ∈ L, s i ∈ F) → {a | ∀ i ∈ L, a ∈ s i} ∈ F :=
  sorry

end Filter

-- ### Zorn の補題（包含順序の集合族版）

namespace Zorn

variable {β : Type}

def IsChain (c : Set (Set β)) : Prop := ∀ s ∈ c, ∀ t ∈ c, s ⊆ t ∨ t ⊆ s

open Classical in

noncomputable def next (𝔉 : Set (Set β)) (S : Set β) : Set β :=
  if h : ∃ T, T ∈ 𝔉 ∧ S ⊆ T ∧ T ≠ S then Classical.choose h else S

inductive Tower (𝔉 : Set (Set β)) (A : Set β) : Set β → Prop
  | base : Tower 𝔉 A A
  | next {S : Set β} : Tower 𝔉 A S → Tower 𝔉 A (next 𝔉 S)
  | sup (c : Set (Set β)) : (∀ S ∈ c, Tower 𝔉 A S) → IsChain c → (∃ S, S ∈ c) →
      Tower 𝔉 A (⋃₀ c)

variable {𝔉 : Set (Set β)} {A : Set β}

theorem subset_next (S : Set β) : S ⊆ next 𝔉 S := by
  unfold next
  split
  · next h => exact (Classical.choose_spec h).2.1
  · exact Set.subset_refl S

theorem next_mem {S : Set β} (hS : S ∈ 𝔉) : next 𝔉 S ∈ 𝔉 := by
  unfold next
  split
  · next h => exact (Classical.choose_spec h).1
  · exact hS

theorem Tower.mem (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {S : Set β} (hS : Tower 𝔉 A S) : S ∈ 𝔉 ∧ A ⊆ S :=
  sorry

def Extreme (𝔉 : Set (Set β)) (A C : Set β) : Prop :=
  ∀ T, Tower 𝔉 A T → T ⊆ C → T ≠ C → next 𝔉 T ⊆ C

theorem Extreme.dichotomy (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hCT : Tower 𝔉 A C) (hC : Extreme 𝔉 A C) {T : Set β}
    (hT : Tower 𝔉 A T) : T ⊆ C ∨ next 𝔉 C ⊆ T :=
  sorry

theorem Tower.extreme (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hC : Tower 𝔉 A C) : Extreme 𝔉 A C :=
  sorry

theorem Tower.isChain (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : IsChain {S | Tower 𝔉 A S} :=
  sorry

theorem exists_maximal (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : ∃ M, M ∈ 𝔉 ∧ A ⊆ M ∧ ∀ N, N ∈ 𝔉 → M ⊆ N → N = M :=
  sorry

end Zorn

namespace Filter

variable {α : Type}

theorem exists_ultra (F : Filter α) (hF : (∅ : Set α) ∉ F) :
    ∃ G : Filter α, G.IsUltra ∧ F.sets ⊆ G.sets :=
  sorry

end Filter

-- ## Part H: 主定理のコンパクト版

section Compact

def Filter.ConvergesTo {X : Type} [TopologicalSpace X] (F : Filter X) (a : X) : Prop :=
  ∀ U, IsOpen U → a ∈ U → U ∈ F

variable {X : Type} [TopologicalSpace X]

theorem isCompact_of_ultra {K : Set X}
    (h : ∀ F : Filter X, F.IsUltra → K ∈ F → ∃ a, a ∈ K ∧ F.ConvergesTo a) : IsCompact K :=
  sorry

theorem IsCompact.ultra_converges {K : Set X} (hK : IsCompact K) {F : Filter X}
    (hF : F.IsUltra) (hKF : K ∈ F) : ∃ a, a ∈ K ∧ F.ConvergesTo a :=
  sorry

theorem Filter.IsUltra.mem_of_cover {α : Type} {F : Filter α} (hF : F.IsUltra) :
    ∀ (L : List (Set α)) (s : Set α), s ∈ F → (∀ a ∈ s, ∃ A ∈ L, a ∈ A) → ∃ A ∈ L, A ∈ F :=
  sorry

variable {α : Type} [UniformSpace α]

theorem IsCompact.totallyBounded {K : Set α} (hK : IsCompact K) : TotallyBounded K :=
  sorry

def Filter.Cauchy (F : Filter α) : Prop := ∀ V ∈ 𝓤 α, ∃ A, A ∈ F ∧ Small V A

theorem Filter.IsUltra.cauchy {F : Filter α} (hF : F.IsUltra) {s : Set α}
    (hs : TotallyBounded s) (hsF : s ∈ F) : F.Cauchy :=
  sorry

end Compact

section AscoliCompact

variable {X Y : Type} [UniformSpace Y]

theorem Filter.Cauchy.convergesTo_of_pointwise {F : Filter (X → Y)} (hF : F.Cauchy)
    (hne : (∅ : Set (X → Y)) ∉ F) (φ : X → Y)
    (hφ : ∀ x, (F.map fun f => f x).ConvergesTo (φ x)) : F.ConvergesTo φ :=
  sorry

variable [TopologicalSpace X]

theorem ascoli_compact [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, ∃ K : Set Y, IsCompact K ∧ (fun f => f x) '' H ⊆ K) (hcl : IsClosed H) :
    IsCompact H :=
  sorry

end AscoliCompact

-- できたら確認: 主定理（全有界版・コンパクト版）が使う公理
-- #print axioms ascoli
-- #print axioms ascoli_compact
