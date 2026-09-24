-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Solutions.«07_Exercises»
import LeanIntro.Solutions.«08_Real»

-- # 発展演習: 位相空間の被覆（解答）

namespace CovSpace

-- ## 部分空間と積

section

variable {X Y Z : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

-- ### 部分空間

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

-- ### 積

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

-- ## 閉集合と貼り合わせ

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

-- ## 実数の閉集合

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

-- ## 単位区間

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

-- ### 半分と 2 倍の計算

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

-- ### 2 のべき

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

-- ## 被覆と局所的な持ち上げ

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
    -- 前半 `F₁(y, t) = F(y, t/2)` を持ち上げる
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
    -- 後半 `F₂(y, t) = F(y, (t+1)/2)` を、前半の終点から持ち上げる
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
    -- 貼り合わせる
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
    · -- 閉集合 `t ≤ 1/2` と `1/2 ≤ t` で貼り合わせる
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

-- ## 持ち上げ定理

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
  -- `N'` の上では、`L y` は `G (y, ·)` に一致する（道の持ち上げの一意性）
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

#print axioms CovSpace.exists_lift_homotopy
