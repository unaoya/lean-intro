-- はじめての Lean — 10_AscoliReal（ブラウザ版・自動生成）
-- 先頭には、この章が使う前の章（05_MathematicalTools・06_Topology・08_Real（解答）・09_Ascoli（解答））のコードをまとめてあります。
-- 本章は「ここから本章」の行から始まります（2181 行目。Ctrl+G で行番号へ移動できます）。
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

-- ─── 09_Ascoli（解答） ───
section

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
  Entourage : Set (Set (α × α))
  univ_mem : Set.univ ∈ Entourage
  mono : ∀ {V W : Set (α × α)}, V ∈ Entourage → V ⊆ W → W ∈ Entourage
  inter_mem : ∀ {V W : Set (α × α)}, V ∈ Entourage → W ∈ Entourage → V ∩ W ∈ Entourage
  refl : ∀ {V : Set (α × α)}, V ∈ Entourage → ∀ a, (a, a) ∈ V
  symm : ∀ {V : Set (α × α)}, V ∈ Entourage → Set.swapRel V ∈ Entourage
  comp : ∀ {V : Set (α × α)}, V ∈ Entourage → ∃ W, W ∈ Entourage ∧ Set.compRel W W ⊆ V

notation "𝓤 " α:max => @UniformSpace.Entourage α _

namespace UniformSpace

variable {α : Type} [UniformSpace α]

theorem exists_half {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c, (a, b) ∈ W → (b, c) ∈ W → (a, c) ∈ V := by
  have ⟨W, hW, hWV⟩ := comp hV
  refine ⟨W ∩ Set.swapRel W, inter_mem hW (symm hW), ?_, ?_⟩
  · intro a b ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩
  · intro a b c ⟨h₁, _⟩ ⟨h₂, _⟩
    exact hWV _ ⟨b, h₁, h₂⟩

theorem exists_third {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c d, (a, b) ∈ W → (b, c) ∈ W → (c, d) ∈ W → (a, d) ∈ V := by
  have ⟨W₁, hW₁, _, h₁⟩ := exists_half hV
  have ⟨W₂, hW₂, hsymm, h₂⟩ := exists_half hW₁
  refine ⟨W₂, hW₂, hsymm, fun a b c d hab hbc hcd => ?_⟩
  exact h₁ a c d (h₂ a b c hab hbc) (h₂ c d d hcd (refl hW₂ d))

instance toTopologicalSpace : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, ∃ V ∈ 𝓤 α, ∀ b, (a, b) ∈ V → b ∈ s
  isOpen_univ := fun _ _ => ⟨Set.univ, univ_mem, fun _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht a ⟨has, hat⟩
    have ⟨V, hV, hVs⟩ := hs a has
    have ⟨W, hW, hWt⟩ := ht a hat
    exact ⟨V ∩ W, inter_mem hV hW, fun b ⟨hb₁, hb₂⟩ => ⟨hVs b hb₁, hWt b hb₂⟩⟩
  isOpen_sUnion := by
    intro S hS a ⟨s, hsS, has⟩
    have ⟨V, hV, hVs⟩ := hS s hsS a has
    exact ⟨V, hV, fun b hb => ⟨s, hsS, hVs b hb⟩⟩

theorem exists_open_ball {V : Set (α × α)} (hV : V ∈ 𝓤 α) (a : α) :
    ∃ O : Set α, IsOpen O ∧ a ∈ O ∧ ∀ b ∈ O, (a, b) ∈ V := by
  refine ⟨{y | ∃ W ∈ 𝓤 α, ∀ z, (y, z) ∈ W → (a, z) ∈ V}, ?_, ⟨V, hV, fun _ h => h⟩, ?_⟩
  · intro y ⟨W, hW, hWV⟩
    have ⟨W', hW', hW'W⟩ := comp hW
    exact ⟨W', hW', fun y' hy' => ⟨W', hW', fun z hz => hWV z (hW'W _ ⟨y', hy', hz⟩)⟩⟩
  · intro b ⟨W, hW, hWV⟩
    exact hWV b (refl hW b)

end UniformSpace

open UniformSpace

section FunctionSpace

variable {X Y : Type} [UniformSpace Y]

def unifRel (V : Set (Y × Y)) : Set ((X → Y) × (X → Y)) := {p | ∀ x, (p.1 x, p.2 x) ∈ V}

instance uniformFun : UniformSpace (X → Y) where
  Entourage := {𝒱 | ∃ V ∈ 𝓤 Y, unifRel V ⊆ 𝒱}
  univ_mem := ⟨Set.univ, univ_mem, fun _ _ => trivial⟩
  mono := fun ⟨V, hV, hV𝒱⟩ h𝒱𝒲 => ⟨V, hV, fun p hp => h𝒱𝒲 p (hV𝒱 p hp)⟩
  inter_mem := fun ⟨V, hV, hV𝒱⟩ ⟨W, hW, hW𝒲⟩ =>
    ⟨V ∩ W, inter_mem hV hW, fun p hp =>
      ⟨hV𝒱 p fun x => (hp x).1, hW𝒲 p fun x => (hp x).2⟩⟩
  refl := fun ⟨_, hV, hV𝒱⟩ f => hV𝒱 (f, f) fun x => refl hV (f x)
  symm := fun ⟨V, hV, hV𝒱⟩ =>
    ⟨Set.swapRel V, symm hV, fun p hp => hV𝒱 (p.2, p.1) fun x => hp x⟩
  comp := fun ⟨_, hV, hV𝒱⟩ =>
    have ⟨W, hW, hWV⟩ := comp hV
    ⟨unifRel W, ⟨W, hW, fun _ h => h⟩, fun _ ⟨g, h₁, h₂⟩ =>
      hV𝒱 _ fun x => hWV _ ⟨g x, h₁ x, h₂ x⟩⟩

variable [TopologicalSpace X]

def EquicontinuousAt (H : Set (X → Y)) (x : X) : Prop :=
  ∀ V ∈ 𝓤 Y, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ V

def Equicontinuous (H : Set (X → Y)) : Prop := ∀ x, EquicontinuousAt H x

theorem Equicontinuous.mono {H H' : Set (X → Y)} (hH : Equicontinuous H) (h : H' ⊆ H) :
    Equicontinuous H' := fun x V hV =>
  have ⟨U, hU, hxU, hUV⟩ := hH x V hV
  ⟨U, hU, hxU, fun f hf => hUV f (h f hf)⟩

theorem equicontinuous_singleton {f : X → Y} (hf : Continuous f) :
    Equicontinuous {g | g = f} := by
  intro x V hV
  have ⟨O, hO, hxO, hOV⟩ := exists_open_ball hV (f x)
  refine ⟨f ⁻¹' O, hf O hO, hxO, ?_⟩
  intro g hg x' hx'
  rw [hg]
  exact hOV (f x') hx'

theorem Equicontinuous.finite_control [CompactSpace X] {H : Set (X → Y)}
    (hH : Equicontinuous H) {V : Set (Y × Y)} (hV : V ∈ 𝓤 Y) :
    ∃ W ∈ 𝓤 Y, ∃ P : List X, ∀ f ∈ H, ∀ g ∈ H,
      (∀ p ∈ P, (f p, g p) ∈ W) → ∀ x, (f x, g x) ∈ V := by
  have ⟨W, hW, hsymm, h3⟩ := exists_third hV
  have hU : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ W :=
    fun x => hH x W hW
  let U := fun x => Classical.choose (hU x)
  have hUspec := fun x => Classical.choose_spec (hU x)
  have ⟨J, hJ, hcov⟩ := CompactSpace.isCompact_univ U (fun x => (hUspec x).1)
    (fun x _ => ⟨x, (hUspec x).2.1⟩)
  have ⟨P, hP⟩ := hJ.exists_list
  refine ⟨W, hW, P, fun f hf g hg hfg x => ?_⟩
  have ⟨y, hyJ, hxy⟩ := hcov x trivial
  have hfy := hsymm _ _ ((hUspec y).2.2 f hf x hxy)
  have hgy := (hUspec y).2.2 g hg x hxy
  exact h3 _ _ _ _ hfy (hfg y (hP y hyJ)) hgy

end FunctionSpace

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
    (h : t ⊆ s) : TotallyBounded t := fun V hV =>
  have ⟨L, hsmall, hcov⟩ := hs V hV
  ⟨L, hsmall, fun a ha => hcov a (h a ha)⟩

variable {X Y : Type} [UniformSpace Y]

theorem finite_points_cover {H : Set (X → Y)}
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) {W : Set (Y × Y)} (hW : W ∈ 𝓤 Y) :
    ∀ P : List X, ∃ C : List (Set (X → Y)),
      (∀ S ∈ C, ∀ f ∈ S, ∀ g ∈ S, ∀ p ∈ P, (f p, g p) ∈ W) ∧ ∀ f ∈ H, ∃ S ∈ C, f ∈ S
  | [] => by
    refine ⟨[Set.univ], ?_, ?_⟩
    · intro _ _ _ _ _ _ p hp
      exact nomatch hp
    · intro f _
      exact ⟨Set.univ, List.mem_cons_self, trivial⟩
  | x :: P => by
    have ⟨C, hCsmall, hCcov⟩ := finite_points_cover hpt hW P
    have ⟨L, hLsmall, hLcov⟩ := hpt x W hW
    refine ⟨List.interCover C (L.map fun A => (fun f => f x) ⁻¹' A), ?_, ?_⟩
    · intro S hS f hf g hg p hp
      have ⟨S', hS', B, hB, hSeq⟩ := List.mem_interCover hS
      have ⟨A, hA, hBeq⟩ := List.mem_map.mp hB
      rw [hSeq, ← hBeq] at hf hg
      cases List.mem_cons.mp hp with
      | inl h => rw [h]; exact hLsmall A hA _ hf.2 _ hg.2
      | inr h => exact hCsmall S' hS' f hf.1 g hg.1 p h
    · refine List.interCover_covers hCcov fun f hf => ?_
      have ⟨A, hA, hfA⟩ := hLcov (f x) ⟨f, hf, rfl⟩
      exact ⟨_, List.mem_map_of_mem hA, hfA⟩

variable [TopologicalSpace X]

theorem ascoli [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) : TotallyBounded H := by
  intro 𝒱 ⟨V, hV, hV𝒱⟩
  have ⟨W, hW, P, hctrl⟩ := hH.finite_control hV
  have ⟨C, hCsmall, hCcov⟩ := finite_points_cover hpt hW P
  refine ⟨C.map fun S => S ∩ H, ?_, ?_⟩
  · intro A hA
    have ⟨S, hS, hSA⟩ := List.mem_map.mp hA
    rw [← hSA]
    intro f ⟨hfS, hfH⟩ g ⟨hgS, hgH⟩
    exact hV𝒱 (f, g) (hctrl f hfH g hgH (hCsmall S hS f hfS g hgS))
  · intro f hf
    have ⟨S, hS, hfS⟩ := hCcov f hf
    exact ⟨S ∩ H, List.mem_map_of_mem hS, hfS, hf⟩

end TotallyBounded

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
  isCompact_univ := by
    intro I U hU hcov
    have ⟨i₀, hi₀⟩ := hcov none trivial
    have ⟨N, hN⟩ := hU i₀ hi₀
    let c := fun k : Nat => Classical.choose (hcov (some k) trivial)
    have hc := fun k : Nat => Classical.choose_spec (hcov (some k) trivial)
    let p : Fin (N + 1) → I := fun k =>
      match k with
      | ⟨0, _⟩ => i₀
      | ⟨k + 1, _⟩ => c k
    refine ⟨{i | ∃ k, p k = i}, ⟨N + 1, p, fun _ h => h⟩, ?_⟩
    intro o _
    match o with
    | none => exact ⟨i₀, ⟨⟨0, Nat.succ_pos N⟩, rfl⟩, hi₀⟩
    | some n =>
      by_cases h : N ≤ n
      · exact ⟨i₀, ⟨⟨0, Nat.succ_pos N⟩, rfl⟩, hN n h⟩
      · exact ⟨c n, ⟨⟨n + 1, Nat.succ_lt_succ (Nat.lt_of_not_le h)⟩, rfl⟩, hc n⟩

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

theorem totallyBounded_bool (s : Set Bool) : TotallyBounded s := by
  intro V hV
  refine ⟨[{b | b = true}, {b | b = false}], ?_, ?_⟩
  · intro A hA a ha b hb
    cases List.mem_cons.mp hA with
    | inl h =>
      rw [h] at ha hb
      rw [show a = b from ha.trans hb.symm]
      exact hV b
    | inr h =>
      rw [List.mem_singleton.mp h] at ha hb
      rw [show a = b from ha.trans hb.symm]
      exact hV b
  · intro a _
    cases a with
    | true => exact ⟨_, List.mem_cons_self, rfl⟩
    | false => exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

theorem not_equicontinuousAt : ¬ EquicontinuousAt H none := by
  intro h
  have ⟨U, hU, hnone, hUV⟩ := h (diagonal Bool) (fun _ => rfl)
  have ⟨N, hN⟩ := hU hnone
  have h' : δ N none = δ N (some N) := hUV (δ N) ⟨N, rfl⟩ (some N) (hN N (Nat.le_refl N))
  simp [δ] at h'

theorem exists_avoid (L : List (Set (Option Nat → Bool)))
    (hL : ∀ A ∈ L, Small (unifRel (diagonal Bool)) A) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ A ∈ L, δ n ∉ A := by
  induction L with
  | nil => exact fun N => ⟨N, Nat.le_refl N, fun _ h => nomatch h⟩
  | cons A L ih =>
    intro N
    have ih := ih fun B hB => hL B (List.mem_cons_of_mem _ hB)
    have ⟨n, hn, hnL⟩ := ih N
    have ⟨m, hm, hmL⟩ := ih (n + 1)
    by_cases hnA : δ n ∈ A
    · refine ⟨m, Nat.le_trans hn (Nat.le_trans (Nat.le_succ n) hm), ?_⟩
      intro B hB hmB
      cases List.mem_cons.mp hB with
      | inl h =>
        rw [h] at hmB
        have h' : δ n (some n) = δ m (some n) := hL A List.mem_cons_self _ hnA _ hmB (some n)
        have hne : n ≠ m := Nat.ne_of_lt hm
        simp [δ, hne] at h'
      | inr h => exact hmL B h hmB
    · refine ⟨n, hn, fun B hB hnB => ?_⟩
      cases List.mem_cons.mp hB with
      | inl h => rw [h] at hnB; exact hnA hnB
      | inr h => exact hnL B h hnB

theorem not_totallyBounded : ¬ TotallyBounded H := by
  intro h
  have ⟨L, hsmall, hcov⟩ :=
    h (unifRel (diagonal Bool)) ⟨_, fun _ => rfl, fun _ hp => hp⟩
  have ⟨n, _, hn⟩ := exists_avoid L hsmall 0
  have ⟨A, hA, hnA⟩ := hcov (δ n) ⟨n, rfl⟩
  exact hn A hA hnA

end Counterexample

section Converse

variable {X Y : Type} [UniformSpace Y]

theorem TotallyBounded.eval {H : Set (X → Y)} (hH : TotallyBounded H) (x : X) :
    TotallyBounded ((fun f => f x) '' H) := by
  intro V hV
  have ⟨L, hsmall, hcov⟩ := hH (unifRel V) ⟨V, hV, fun _ h => h⟩
  refine ⟨L.map fun S => (fun f => f x) '' S, ?_, ?_⟩
  · intro A hA
    have ⟨S, hS, hSA⟩ := List.mem_map.mp hA
    rw [← hSA]
    intro a ⟨f, hf, hfa⟩ b ⟨g, hg, hgb⟩
    rw [← hfa, ← hgb]
    exact hsmall S hS f hf g hg x
  · intro a ⟨f, hf, hfa⟩
    have ⟨S, hS, hfS⟩ := hcov f hf
    exact ⟨_, List.mem_map_of_mem hS, f, hfS, hfa⟩

variable [TopologicalSpace X]

theorem TotallyBounded.equicontinuous {H : Set (X → Y)} (hc : ∀ f ∈ H, Continuous f)
    (hH : TotallyBounded H) : Equicontinuous H := by
  intro x V hV
  have ⟨W, hW, _, h3⟩ := exists_third hV
  have ⟨C, hsmall, hcov⟩ := hH (unifRel W) ⟨W, hW, fun _ h => h⟩
  have key : ∀ C : List (Set (X → Y)), (∀ S ∈ C, Small (unifRel W) S) →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ S ∈ C, ∀ f ∈ S, f ∈ H → ∀ x' ∈ U, (f x, f x') ∈ V := by
    intro C
    induction C with
    | nil => exact fun _ => ⟨Set.univ, isOpen_univ, trivial, fun _ h => nomatch h⟩
    | cons S C ih =>
      intro hC
      have ⟨U, hU, hxU, hUV⟩ := ih fun S' hS' => hC S' (List.mem_cons_of_mem _ hS')
      by_cases hS : ∃ g, g ∈ S ∧ g ∈ H
      · have ⟨g, hgS, hgH⟩ := hS
        have ⟨O, hO, hgO, hOW⟩ := exists_open_ball hW (g x)
        refine ⟨U ∩ g ⁻¹' O, isOpen_inter _ _ hU (hc g hgH O hO), ⟨hxU, hgO⟩, ?_⟩
        intro S' hS' f hfS' hfH x' ⟨hx'U, hx'O⟩
        cases List.mem_cons.mp hS' with
        | inl h =>
          rw [h] at hfS'
          have hS := hC S List.mem_cons_self
          exact h3 _ _ _ _ (hS f hfS' g hgS x) (hOW _ hx'O) (hS g hgS f hfS' x')
        | inr h => exact hUV S' h f hfS' hfH x' hx'U
      · refine ⟨U, hU, hxU, fun S' hS' f hfS' hfH => ?_⟩
        cases List.mem_cons.mp hS' with
        | inl h => rw [h] at hfS'; exact absurd ⟨f, hfS', hfH⟩ hS
        | inr h => exact hUV S' h f hfS' hfH
  have ⟨U, hU, hxU, hUV⟩ := key C hsmall
  refine ⟨U, hU, hxU, fun f hf => ?_⟩
  have ⟨S, hS, hfS⟩ := hcov f hf
  exact hUV S hS f hfS hf

end Converse

structure Filter (α : Type) where
  sets : Set (Set α)
  univ_mem : Set.univ ∈ sets
  mono : ∀ {s t : Set α}, s ∈ sets → s ⊆ t → t ∈ sets
  inter_mem : ∀ {s t : Set α}, s ∈ sets → t ∈ sets → s ∩ t ∈ sets

namespace Filter

variable {α β : Type}

instance : Membership (Set α) (Filter α) := ⟨fun F s => s ∈ F.sets⟩

structure IsUltra (F : Filter α) : Prop where
  empty_not_mem : (∅ : Set α) ∉ F
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

theorem IsUltra.map {F : Filter α} (hF : F.IsUltra) (f : α → β) : (F.map f).IsUltra where
  empty_not_mem := hF.empty_not_mem
  mem_or_compl_mem := fun s => hF.mem_or_compl_mem (f ⁻¹' s)

theorem mem_list_inter (F : Filter α) {I : Type} (s : I → Set α) :
    ∀ L : List I, (∀ i ∈ L, s i ∈ F) → {a | ∀ i ∈ L, a ∈ s i} ∈ F
  | [], _ => F.mono F.univ_mem fun _ _ _ h => nomatch h
  | i :: L, h =>
    F.mono (F.inter_mem (h i List.mem_cons_self)
        (mem_list_inter F s L fun j hj => h j (List.mem_cons_of_mem _ hj)))
      fun a ⟨hai, haL⟩ j hj => by
        cases List.mem_cons.mp hj with
        | inl e => rw [e]; exact hai
        | inr e => exact haL j e

end Filter

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
    (hA : A ∈ 𝔉) {S : Set β} (hS : Tower 𝔉 A S) : S ∈ 𝔉 ∧ A ⊆ S := by
  induction hS with
  | base => exact ⟨hA, Set.subset_refl A⟩
  | next _ ih => exact ⟨next_mem ih.1, fun a ha => subset_next _ a (ih.2 a ha)⟩
  | sup c _ hc hne ih =>
    have ⟨S, hS⟩ := hne
    exact ⟨hchain c (fun T hT => (ih T hT).1) hc hne, fun a ha => ⟨S, hS, (ih S hS).2 a ha⟩⟩

def Extreme (𝔉 : Set (Set β)) (A C : Set β) : Prop :=
  ∀ T, Tower 𝔉 A T → T ⊆ C → T ≠ C → next 𝔉 T ⊆ C

theorem Extreme.dichotomy (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hCT : Tower 𝔉 A C) (hC : Extreme 𝔉 A C) {T : Set β}
    (hT : Tower 𝔉 A T) : T ⊆ C ∨ next 𝔉 C ⊆ T := by
  induction hT with
  | base => exact Or.inl (Tower.mem hchain hA hCT).2
  | @next T hT ih =>
    cases ih with
    | inl h =>
      by_cases he : T = C
      · rw [he]; exact Or.inr (Set.subset_refl _)
      · exact Or.inl (hC T hT h he)
    | inr h => exact Or.inr fun a ha => subset_next T a (h a ha)
  | sup c _ _ _ ih =>
    by_cases h : ∀ S ∈ c, S ⊆ C
    · exact Or.inl fun a ⟨S, hS, haS⟩ => h S hS a haS
    · have ⟨S, hS, hSC⟩ : ∃ S, S ∈ c ∧ ¬ S ⊆ C := Classical.byContradiction fun h' =>
        h fun S hS => Classical.byContradiction fun hSC => h' ⟨S, hS, hSC⟩
      cases ih S hS with
      | inl h => exact absurd h hSC
      | inr h => exact Or.inr fun a ha => ⟨S, hS, h a ha⟩

theorem Tower.extreme (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hC : Tower 𝔉 A C) : Extreme 𝔉 A C := by
  induction hC with
  | base =>
    intro T hT hTA hne
    exact absurd (Set.subset_antisymm hTA (Tower.mem hchain hA hT).2) hne
  | @next C hC ih =>
    intro T hT hTC hne
    cases Extreme.dichotomy hchain hA hC ih hT with
    | inl h =>
      by_cases he : T = C
      · rw [he]; exact Set.subset_refl _
      · exact fun a ha => subset_next C a (ih T hT h he a ha)
    | inr h => exact absurd (Set.subset_antisymm hTC h) hne
  | sup c hc _ _ ih =>
    intro T hT hTc hne
    have ⟨S, hS, hST⟩ : ∃ S, S ∈ c ∧ ¬ S ⊆ T := Classical.byContradiction fun h =>
      hne (Set.subset_antisymm hTc fun a ⟨S, hS, haS⟩ =>
        Classical.byContradiction fun haT => h ⟨S, hS, fun hST => haT (hST a haS)⟩)
    cases Extreme.dichotomy hchain hA (hc S hS) (ih S hS) hT with
    | inl h =>
      have hne' : T ≠ S := fun e => hST (e ▸ Set.subset_refl T)
      exact fun a ha => ⟨S, hS, ih S hS T hT h hne' a ha⟩
    | inr h => exact absurd (fun a ha => h a (subset_next S a ha)) hST

theorem Tower.isChain (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : IsChain {S | Tower 𝔉 A S} := by
  intro S hS T hT
  cases Extreme.dichotomy hchain hA hS (Tower.extreme hchain hA hS) hT with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl fun a ha => h a (subset_next S a ha)

theorem exists_maximal (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : ∃ M, M ∈ 𝔉 ∧ A ⊆ M ∧ ∀ N, N ∈ 𝔉 → M ⊆ N → N = M := by
  let M := ⋃₀ {S | Tower 𝔉 A S}
  have hM : Tower 𝔉 A M :=
    Tower.sup _ (fun _ h => h) (Tower.isChain hchain hA) ⟨A, Tower.base⟩
  have hnext : next 𝔉 M ⊆ M := fun a ha => ⟨_, Tower.next hM, ha⟩
  refine ⟨M, (Tower.mem hchain hA hM).1, (Tower.mem hchain hA hM).2, ?_⟩
  intro N hN hMN
  apply Classical.byContradiction
  intro hne
  have h : ∃ T, T ∈ 𝔉 ∧ M ⊆ T ∧ T ≠ M := ⟨N, hN, hMN, hne⟩
  have hspec := Classical.choose_spec h
  have heq : next 𝔉 M = Classical.choose h := by
    unfold next
    rw [dif_pos h]
  rw [← heq] at hspec
  exact hspec.2.2 (Set.subset_antisymm hnext hspec.2.1)

end Zorn

namespace Filter

variable {α : Type}

theorem exists_ultra (F : Filter α) (hF : (∅ : Set α) ∉ F) :
    ∃ G : Filter α, G.IsUltra ∧ F.sets ⊆ G.sets := by
  let P : Set (Set (Set α)) := {𝒮 | Set.univ ∈ 𝒮 ∧
    (∀ s t, s ∈ 𝒮 → s ⊆ t → t ∈ 𝒮) ∧ (∀ s t, s ∈ 𝒮 → t ∈ 𝒮 → s ∩ t ∈ 𝒮) ∧ ∅ ∉ 𝒮}
  have hchain : ∀ c, c ⊆ P → Zorn.IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ P := by
    intro c hcP hc ⟨S, hS⟩
    refine ⟨⟨S, hS, (hcP S hS).1⟩, ?_, ?_, ?_⟩
    · intro s t ⟨T, hT, hsT⟩ hst
      exact ⟨T, hT, (hcP T hT).2.1 s t hsT hst⟩
    · intro s t ⟨T₁, hT₁, hs⟩ ⟨T₂, hT₂, ht⟩
      cases hc T₁ hT₁ T₂ hT₂ with
      | inl h => exact ⟨T₂, hT₂, (hcP T₂ hT₂).2.2.1 s t (h s hs) ht⟩
      | inr h => exact ⟨T₁, hT₁, (hcP T₁ hT₁).2.2.1 s t hs (h t ht)⟩
    · intro ⟨T, hT, he⟩
      exact (hcP T hT).2.2.2 he
  have hFP : F.sets ∈ P :=
    ⟨F.univ_mem, fun _ _ hs h => F.mono hs h, fun _ _ hs ht => F.inter_mem hs ht, hF⟩
  have ⟨M, ⟨huniv, hmono, hinter, hempty⟩, hFM, hmax⟩ := Zorn.exists_maximal hchain hFP
  let G : Filter α :=
    { sets := M, univ_mem := huniv, mono := fun hs h => hmono _ _ hs h,
      inter_mem := fun hs ht => hinter _ _ hs ht }
  refine ⟨G, ⟨hempty, fun s => ?_⟩, hFM⟩
  apply Classical.byContradiction
  intro hs
  have hs₁ : s ∉ M := fun h => hs (Or.inl h)
  have hs₂ : sᶜ ∉ M := fun h => hs (Or.inr h)
  let M' : Set (Set α) := {t | ∃ m, m ∈ M ∧ m ∩ s ⊆ t}
  have hM' : M' ∈ P := by
    refine ⟨⟨Set.univ, huniv, fun _ _ => trivial⟩, ?_, ?_, ?_⟩
    · intro t u ⟨m, hm, hmt⟩ htu
      exact ⟨m, hm, fun a ha => htu a (hmt a ha)⟩
    · intro t u ⟨m₁, hm₁, h₁⟩ ⟨m₂, hm₂, h₂⟩
      exact ⟨m₁ ∩ m₂, hinter _ _ hm₁ hm₂, fun a ⟨⟨ha₁, ha₂⟩, has⟩ =>
        ⟨h₁ a ⟨ha₁, has⟩, h₂ a ⟨ha₂, has⟩⟩⟩
    · intro ⟨m, hm, hms⟩
      exact hs₂ (hmono _ _ hm fun a ham has => hms a ⟨ham, has⟩)
  have hMM' : M ⊆ M' := fun m hm => ⟨m, hm, fun a ha => ha.1⟩
  have heq := hmax M' hM' hMM'
  have : s ∈ M' := ⟨Set.univ, huniv, fun a ha => ha.2⟩
  rw [heq] at this
  exact hs₁ this

end Filter

section Compact

def Filter.ConvergesTo {X : Type} [TopologicalSpace X] (F : Filter X) (a : X) : Prop :=
  ∀ U, IsOpen U → a ∈ U → U ∈ F

variable {X : Type} [TopologicalSpace X]

theorem isCompact_of_ultra {K : Set X}
    (h : ∀ F : Filter X, F.IsUltra → K ∈ F → ∃ a, a ∈ K ∧ F.ConvergesTo a) : IsCompact K := by
  intro I U hU hcov
  apply Classical.byContradiction
  intro hnot
  let F : Filter X :=
    { sets := {s | ∃ L : List I, {a | a ∈ K ∧ ∀ i ∈ L, a ∉ U i} ⊆ s}
      univ_mem := ⟨[], fun _ _ => trivial⟩
      mono := fun ⟨L, hL⟩ hst => ⟨L, fun a ha => hst a (hL a ha)⟩
      inter_mem := fun ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ =>
        ⟨L₁ ++ L₂, fun a ⟨haK, haL⟩ =>
          ⟨h₁ a ⟨haK, fun i hi => haL i (List.mem_append.mpr (Or.inl hi))⟩,
           h₂ a ⟨haK, fun i hi => haL i (List.mem_append.mpr (Or.inr hi))⟩⟩⟩ }
  have hF : (∅ : Set X) ∉ F := by
    intro ⟨L, hL⟩
    apply hnot
    refine ⟨{i | i ∈ L}, Set.finite_of_list L, fun a haK => ?_⟩
    apply Classical.byContradiction
    intro hna
    exact hL a ⟨haK, fun i hi hai => hna ⟨i, hi, hai⟩⟩
  have ⟨G, hG, hFG⟩ := F.exists_ultra hF
  have ⟨a, haK, hconv⟩ := h G hG (hFG _ ⟨[], fun _ ha => ha.1⟩)
  have ⟨i, hai⟩ := hcov a haK
  have h₁ : U i ∈ G := hconv (U i) (hU i) hai
  have h₂ : (U i)ᶜ ∈ G :=
    hFG _ ⟨[i], fun _ ⟨_, hb⟩ => hb i List.mem_cons_self⟩
  exact hG.empty_not_mem (G.mono (G.inter_mem h₁ h₂) fun _ ⟨hb₁, hb₂⟩ => hb₂ hb₁)

theorem IsCompact.ultra_converges {K : Set X} (hK : IsCompact K) {F : Filter X}
    (hF : F.IsUltra) (hKF : K ∈ F) : ∃ a, a ∈ K ∧ F.ConvergesTo a := by
  apply Classical.byContradiction
  intro hno
  have hbad : ∀ a : {a // a ∈ K}, ∃ U, IsOpen U ∧ a.1 ∈ U ∧ U ∉ F := by
    intro ⟨a, haK⟩
    apply Classical.byContradiction
    intro h
    exact hno ⟨a, haK, fun U hU haU =>
      Classical.byContradiction fun hUF => h ⟨U, hU, haU, hUF⟩⟩
  let U := fun a => Classical.choose (hbad a)
  have hUspec := fun a => Classical.choose_spec (hbad a)
  have ⟨J, hJ, hJcov⟩ :=
    hK U (fun a => (hUspec a).1) fun a haK => ⟨⟨a, haK⟩, (hUspec ⟨a, haK⟩).2.1⟩
  have ⟨L, hL⟩ := hJ.exists_list
  have hmem := F.mem_list_inter (fun i => (U i)ᶜ) L fun i _ => hF.compl_mem (hUspec i).2.2
  apply hF.empty_not_mem
  refine F.mono (F.inter_mem hKF hmem) fun a ⟨haK, haL⟩ => ?_
  have ⟨i, hiJ, hai⟩ := hJcov a haK
  exact haL i (hL i hiJ) hai

theorem Filter.IsUltra.mem_of_cover {α : Type} {F : Filter α} (hF : F.IsUltra) :
    ∀ (L : List (Set α)) (s : Set α), s ∈ F → (∀ a ∈ s, ∃ A ∈ L, a ∈ A) → ∃ A ∈ L, A ∈ F
  | [], s, hs, hcov =>
    absurd (F.mono hs fun a ha => nomatch (hcov a ha)) hF.empty_not_mem
  | A :: L, s, hs, hcov => by
    by_cases hA : A ∈ F
    · exact ⟨A, List.mem_cons_self, hA⟩
    · have ⟨B, hB, hBF⟩ := hF.mem_of_cover L (s ∩ Aᶜ) (F.inter_mem hs (hF.compl_mem hA))
        fun a ⟨has, haA⟩ => by
          have ⟨B, hB, haB⟩ := hcov a has
          cases List.mem_cons.mp hB with
          | inl h => rw [h] at haB; exact absurd haB haA
          | inr h => exact ⟨B, h, haB⟩
      exact ⟨B, List.mem_cons_of_mem _ hB, hBF⟩

variable {α : Type} [UniformSpace α]

theorem IsCompact.totallyBounded {K : Set α} (hK : IsCompact K) : TotallyBounded K := by
  intro V hV
  have ⟨W, hW, hsymm, h2⟩ := exists_half hV
  let O := fun a => Classical.choose (exists_open_ball hW a)
  have hO := fun a => Classical.choose_spec (exists_open_ball hW a)
  have ⟨J, hJ, hcov⟩ := hK O (fun a => (hO a).1) fun a _ => ⟨a, (hO a).2.1⟩
  have ⟨P, hP⟩ := hJ.exists_list
  refine ⟨P.map O, ?_, ?_⟩
  · intro A hA
    have ⟨a, _, haA⟩ := List.mem_map.mp hA
    rw [← haA]
    intro b hb c hc
    exact h2 b a c (hsymm _ _ ((hO a).2.2 b hb)) ((hO a).2.2 c hc)
  · intro b hb
    have ⟨a, haJ, hba⟩ := hcov b hb
    exact ⟨O a, List.mem_map_of_mem (hP a haJ), hba⟩

def Filter.Cauchy (F : Filter α) : Prop := ∀ V ∈ 𝓤 α, ∃ A, A ∈ F ∧ Small V A

theorem Filter.IsUltra.cauchy {F : Filter α} (hF : F.IsUltra) {s : Set α}
    (hs : TotallyBounded s) (hsF : s ∈ F) : F.Cauchy := by
  intro V hV
  have ⟨L, hsmall, hcov⟩ := hs V hV
  have ⟨A, hA, hAF⟩ := hF.mem_of_cover L s hsF hcov
  exact ⟨A, hAF, hsmall A hA⟩

end Compact

section AscoliCompact

variable {X Y : Type} [UniformSpace Y]

theorem Filter.Cauchy.convergesTo_of_pointwise {F : Filter (X → Y)} (hF : F.Cauchy)
    (hne : (∅ : Set (X → Y)) ∉ F) (φ : X → Y)
    (hφ : ∀ x, (F.map fun f => f x).ConvergesTo (φ x)) : F.ConvergesTo φ := by
  intro 𝒪 h𝒪 hφ𝒪
  have ⟨𝒱, ⟨V, hV, hV𝒱⟩, h𝒱𝒪⟩ := h𝒪 φ hφ𝒪
  have ⟨W, hW, hWV⟩ := comp hV
  have ⟨A, hAF, hAsmall⟩ := hF (unifRel W) ⟨W, hW, fun _ h => h⟩
  refine F.mono hAF fun f hfA => h𝒱𝒪 f (hV𝒱 (φ, f) fun x => ?_)
  have ⟨O, hO, hφO, hOW⟩ := exists_open_ball hW (φ x)
  have ⟨g, hgO, hgA⟩ := Filter.nonempty_of_mem hne (F.inter_mem (hφ x O hO hφO) hAF)
  exact hWV _ ⟨g x, hOW _ hgO, hAsmall g hgA f hfA x⟩

variable [TopologicalSpace X]

theorem ascoli_compact [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, ∃ K : Set Y, IsCompact K ∧ (fun f => f x) '' H ⊆ K) (hcl : IsClosed H) :
    IsCompact H := by
  have hTB : TotallyBounded H := ascoli hH fun x =>
    have ⟨_, hK, hsub⟩ := hpt x
    hK.totallyBounded.subset hsub
  apply isCompact_of_ultra
  intro F hF hHF
  have hlim : ∀ x, ∃ y, (F.map fun f => f x).ConvergesTo y := fun x =>
    have ⟨K, hK, hsub⟩ := hpt x
    have ⟨y, _, hy⟩ := hK.ultra_converges (hF.map _) (F.mono hHF fun f hf => hsub _ ⟨f, hf, rfl⟩)
    ⟨y, hy⟩
  let φ := fun x => Classical.choose (hlim x)
  have hconv := (hF.cauchy hTB hHF).convergesTo_of_pointwise hF.empty_not_mem φ
    fun x => Classical.choose_spec (hlim x)
  refine ⟨φ, Classical.byContradiction fun hφ => ?_, hconv⟩
  exact hF.empty_not_mem
    (F.mono (F.inter_mem hHF (hconv _ hcl hφ)) fun _ ⟨h₁, h₂⟩ => h₂ h₁)

end AscoliCompact

end

-- ════════ ここから本章：10_AscoliReal ════════
-- # 発展演習: 実数版 Arzelà–Ascoli の定理

open CompleteOrderedField UniformSpace

variable {R : Type} [CompleteOrderedField R]

-- ## Part A: 実数の一様構造

instance realUniformSpace : UniformSpace R where
  Entourage := {V | ∃ ε, 0 < ε ∧ ∀ a b : R, abs (a - b) < ε → (a, b) ∈ V}
  univ_mem := sorry
  mono := sorry
  inter_mem := sorry
  refl := sorry
  symm := sorry
  comp := sorry

def distLt (ε : R) : Set (R × R) := {p | abs (p.1 - p.2) < ε}

theorem distLt_mem {ε : R} (hε : 0 < ε) : distLt ε ∈ 𝓤 R := ⟨ε, hε, fun _ _ h => h⟩

-- ## Part B: 2つの位相の一致

theorem TopologicalSpace.ext_iff_isOpen {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : ∀ s, t₁.IsOpen s ↔ t₂.IsOpen s) : t₁ = t₂ := by
  cases t₁
  cases t₂
  congr
  funext s
  exact propext (h s)

theorem uniform_topology_eq :
    (UniformSpace.toTopologicalSpace : TopologicalSpace R) =
      CompleteOrderedField.instTopologicalSpace :=
  sorry

theorem isCompact_Icc' (a b : R) : IsCompact (Icc a b) :=
  sorry

-- ## Part C: 用語の対応

section Dictionary

variable {X : Type} [TopologicalSpace X]

def EquicontinuousR (H : Set (X → R)) : Prop :=
  ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ y ∈ U, abs (f y - f x) < ε

def UniformlyBounded (H : Set (X → R)) : Prop := ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M

theorem equicontinuousR_iff {H : Set (X → R)} : EquicontinuousR H ↔ Equicontinuous H :=
  sorry

theorem mem_Icc_of_abs_le {a M : R} (h : abs a ≤ M) : a ∈ Icc (-M) M :=
  sorry

omit [TopologicalSpace X] in

theorem UniformlyBounded.pointwise {H : Set (X → R)} (h : UniformlyBounded H) (x : X) :
    ∃ K : Set R, IsCompact K ∧ (fun f => f x) '' H ⊆ K :=
  sorry

-- ## Part D: 実数版 Ascoli（閉集合版）

theorem arzela_ascoli_closed [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) (hcl : IsClosed H) : IsCompact H :=
  sorry

-- ## Part E: 逆向き——コンパクトなら一様有界かつ等連続

theorem bounded_of_cover {β : Type} (B : β → R → Prop)
    (hB : ∀ y M M', B y M → M ≤ M' → B y M') {s : Set β} :
    ∀ L : List (Set β), (∀ A ∈ L, ∃ M, ∀ y ∈ A, y ∈ s → B y M) →
      (∀ y ∈ s, ∃ A ∈ L, y ∈ A) → ∃ M, ∀ y ∈ s, B y M :=
  sorry

theorem TotallyBounded.bounded {s : Set R} (hs : TotallyBounded s) :
    ∃ M, ∀ y ∈ s, abs y ≤ M :=
  sorry

theorem bounded_of_continuous [CompactSpace X] {f : X → R} (hf : Continuous f) :
    ∃ M, ∀ x, abs (f x) ≤ M :=
  sorry

theorem arzela_ascoli_converse [CompactSpace X] {H : Set (X → R)}
    (hc : ∀ f ∈ H, Continuous f) (hH : IsCompact H) :
    UniformlyBounded H ∧ EquicontinuousR H :=
  sorry

-- ## Part F: 相対コンパクト版（閉包）

def closure {α : Type} [TopologicalSpace α] (s : Set α) : Set α :=
  {a | ∀ U, IsOpen U → a ∈ U → ∃ b, b ∈ U ∧ b ∈ s}

theorem subset_closure {α : Type} [TopologicalSpace α] (s : Set α) : s ⊆ closure s :=
  sorry

theorem isClosed_closure {α : Type} [TopologicalSpace α] (s : Set α) : IsClosed (closure s) :=
  sorry

theorem exists_near_of_mem_closure {X : Type} {H : Set (X → R)} {f : X → R}
    (hf : f ∈ closure H) {ε : R} (hε : 0 < ε) : ∃ g, g ∈ H ∧ ∀ x, abs (f x - g x) < ε := by
  have hV : unifRel (distLt ε) ∈ 𝓤 (X → R) := ⟨_, distLt_mem hε, fun _ h => h⟩
  have ⟨O, hO, hfO, hOV⟩ := exists_open_ball hV f
  have ⟨g, hgO, hgH⟩ := hf O hO hfO
  exact ⟨g, hgH, hOV g hgO⟩

omit [TopologicalSpace X] in

theorem UniformlyBounded.closure {H : Set (X → R)} (h : UniformlyBounded H) :
    UniformlyBounded (closure H) :=
  sorry

theorem add_three_lt {a b c ε : R} (ha : a < ε / 2 / 2) (hb : b < ε / 2) (hc : c < ε / 2 / 2) :
    a + b + c < ε := by
  have h₁ := add_lt_add ha hc
  rw [add_halves] at h₁
  have h₂ := add_lt_add h₁ hb
  rw [add_halves] at h₂
  have e : a + b + c = a + c + b := by ac_rfl
  rw [e]
  exact h₂

theorem EquicontinuousR.closure {H : Set (X → R)} (h : EquicontinuousR H) :
    EquicontinuousR (closure H) :=
  sorry

theorem arzela_ascoli_closure [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) : IsCompact (closure H) :=
  sorry

-- ## Part G: 点列版（一様収束する部分列）

theorem IsCompact.exists_clusterPt {α : Type} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) {u : Nat → α} (hu : ∀ n, u n ∈ K) :
    ∃ g, g ∈ K ∧ ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U :=
  sorry

theorem lt_of_mul_natCast_lt_one {d ε n : R} (hε : 0 < ε) (hn : ε⁻¹ < n)
    (h : abs d * n < 1) : abs d < ε :=
  sorry

theorem natCast_succ_pos (k : Nat) : (0 : R) < natCast (k + 1) := by
  rw [natCast_succ]
  exact lt_of_le_of_lt (natCast_nonneg k) (lt_add_of_pos_right _ zero_lt_one)

theorem natCast_le_natCast {m n : Nat} (h : m ≤ n) : (natCast m : R) ≤ natCast n := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, natCast_add]
  have := add_le_add_left _ _ (natCast_nonneg k) (natCast m : R)
  rw [add_zero] at this
  exact this

def distInv (k : Nat) : Set (R × R) := {p | abs (p.1 - p.2) * natCast (k + 1) < 1}

theorem distInv_mem (k : Nat) : distInv (R := R) k ∈ 𝓤 R := by
  have hk := natCast_succ_pos (R := R) k
  refine ⟨(natCast (k + 1))⁻¹, inv_pos hk, fun a b h => ?_⟩
  have := mul_lt_mul_of_pos_left h hk
  rw [mul_comm (natCast (k + 1)) (natCast (k + 1))⁻¹, inv_mul_cancel (ne_of_lt hk).symm,
    mul_comm] at this
  exact this

theorem exists_subseq_tendsto {X : Type} {u : Nat → X → R} {g : X → R}
    (hg : ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

theorem arzela_ascoli_seq [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) {u : Nat → X → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : X → R,
      (∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (g y - g x) < ε) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

end Dictionary

-- ## Part H: 閉区間上の関数（古典的な Arzelà–Ascoli の定理）

instance subspaceTopology {α : Type} [TopologicalSpace α] (p : α → Prop) :
    TopologicalSpace (Subtype p) where
  IsOpen s := ∃ U : Set α, IsOpen U ∧ ∀ x : Subtype p, x ∈ s ↔ x.1 ∈ U
  isOpen_univ := ⟨Set.univ, isOpen_univ, fun _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  isOpen_inter := fun _ _ ⟨U, hU, hsU⟩ ⟨V, hV, htV⟩ =>
    ⟨U ∩ V, isOpen_inter _ _ hU hV, fun x =>
      ⟨fun ⟨h₁, h₂⟩ => ⟨(hsU x).mp h₁, (htV x).mp h₂⟩,
       fun ⟨h₁, h₂⟩ => ⟨(hsU x).mpr h₁, (htV x).mpr h₂⟩⟩⟩
  isOpen_sUnion := fun S hS =>
    ⟨⋃₀ {U | IsOpen U ∧ ∀ x : Subtype p, x.1 ∈ U → x ∈ ⋃₀ S},
     isOpen_sUnion _ fun _ hU => hU.1, fun x =>
      ⟨fun ⟨s, hsS, hxs⟩ =>
        have ⟨U, hU, hsU⟩ := hS s hsS
        ⟨U, ⟨hU, fun y hy => ⟨s, hsS, (hsU y).mpr hy⟩⟩, (hsU x).mp hxs⟩,
       fun ⟨_, ⟨_, hU⟩, hxU⟩ => hU x hxU⟩⟩

instance (a b : R) : CompactSpace {x // x ∈ Icc a b} where
  isCompact_univ := sorry

theorem equicontinuousR_of_uniform {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε) :
    EquicontinuousR H :=
  sorry

theorem arzela_ascoli {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (hb : ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M)
    (heq : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε)
    {u : Nat → {x // x ∈ Icc a b} → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : {x // x ∈ Icc a b} → R,
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

#print axioms arzela_ascoli
