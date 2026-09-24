-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。
-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。

import LeanIntro.Solutions.«07_Exercises»
import LeanIntro.Solutions.«08_Real»

-- # 発展演習: 位相空間の被覆

namespace CovSpace

-- ## Part A: 部分空間と積

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
    (hs : IsOpen s) : IsOpen {x | ∃ h : x ∈ W, (⟨x, h⟩ : Subtype W) ∈ s} :=
  sorry

theorem continuous_of_locally {f : X → Y}
    (h : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ Continuous (fun a : Subtype W => f a.1)) :
    Continuous f :=
  sorry

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
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

theorem exists_rect {W : Set (X × Y)} (hW : IsOpen W) {p : X × Y} (hp : p ∈ W) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ q : X × Y, q.1 ∈ U → q.2 ∈ V → q ∈ W :=
  sorry

end

-- ## Part B: 閉集合と貼り合わせ

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

theorem isClosed_union {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) :=
  sorry

theorem continuous_of_closed {f : X → Y} (h : ∀ s, IsClosed s → IsClosed (f ⁻¹' s)) :
    Continuous f :=
  sorry

theorem isClosed_preimage {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) := hf _ hs

theorem isClosed_of_subtype_closed {A : Set X} (hA : IsClosed A) {s : Set (Subtype A)}
    (hs : IsClosed s) : IsClosed {x | ∃ h : x ∈ A, (⟨x, h⟩ : Subtype A) ∈ s} :=
  sorry

theorem continuous_of_closed_cover {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) {f : X → Y}
    (hfA : Continuous (fun a : Subtype A => f a.1)) (hfB : Continuous (fun a : Subtype B => f a.1)) :
    Continuous f :=
  sorry

-- ### 実数の閉集合

variable {R : Type} [CompleteOrderedField R]

theorem isClosed_le_const (c : R) : IsClosed ({x | x ≤ c} : Set R) :=
  sorry

theorem isClosed_ge_const (c : R) : IsClosed ({x | c ≤ x} : Set R) := by
  intro x hx
  have hx' : x < c := not_le.mp hx
  refine ⟨c - x, sub_pos.mpr hx', fun y hy hyc => ?_⟩
  have h1 := add_lt_add_right (abs_lt.mp hy).2 x
  rw [sub_add_cancel, sub_add_cancel] at h1
  exact not_le.mpr h1 hyc

end

-- ## Part C: 単位区間

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
  sorry

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

theorem natCast_mul_halfPow_le : ∀ n : Nat, natCast n * (halfPow n : R) ≤ 1 :=
  sorry

theorem exists_halfPow_lt {δ : R} (hδ : 0 < δ) : ∃ n : Nat, (halfPow n : R) < δ :=
  sorry

end

-- ## Part D: 被覆と局所的な持ち上げ

section

open CompleteOrderedField

theorem continuous_const_map {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (b : B) :
    Continuous (fun _ : A => b) :=
  sorry

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
      Continuous (fun q : Subtype (fun q : Y × UI R => q.1 ∈ N') => G q.1) :=
  sorry

theorem lift_local (p : CoveringMap E X) : ∀ (n : Nat) (Y : Type) [TopologicalSpace Y]
    (F : Y × UI R → X), Continuous F → ∀ (N : Set Y), IsOpen N →
    ∀ (F0 : Y → E), Continuous (fun y : Subtype N => F0 y.1) →
    (∀ y ∈ N, p.toFun (F0 y) = F (y, ui0)) →
    (∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, t) ∈ U) →
    ∀ y0 ∈ N, ∃ N' : Set Y, IsOpen N' ∧ y0 ∈ N' ∧ N' ⊆ N ∧ ∃ G : Y × UI R → E,
      (∀ y ∈ N', ∀ t, p.toFun (G (y, t)) = F (y, t)) ∧ (∀ y ∈ N', G (y, ui0) = F0 y) ∧
      Continuous (fun q : Subtype (fun q : Y × UI R => q.1 ∈ N') => G q.1) :=
  sorry

end

-- ## Part E: 持ち上げ定理

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {E X : Type} [tE : TopologicalSpace E] [tX : TopologicalSpace X]

theorem exists_small (p : CoveringMap E X) {Y : Type} [tY : TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (y0 : Y) :
    ∃ N : Set Y, IsOpen N ∧ y0 ∈ N ∧ ∃ n : Nat, ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, t) ∈ U :=
  sorry

theorem lift_unique (p : CoveringMap E X) {f g : UI R → E} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, p.toFun (f t) = p.toFun (g t)) (h0 : f ui0 = g ui0) : f = g :=
  sorry

instance instTopUnit : TopologicalSpace Unit where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

theorem exists_lift_path (p : CoveringMap E X) (γ : UI R → X) (hγ : Continuous γ) (e0 : E)
    (he : p.toFun e0 = γ ui0) :
    ∃ γ' : UI R → E, Continuous γ' ∧ (∀ t, p.toFun (γ' t) = γ t) ∧ γ' ui0 = e0 :=
  sorry

theorem exists_lift_homotopy (p : CoveringMap E X) {Y : Type} [tY : TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (F0 : Y → E) (hF0 : Continuous F0)
    (h0 : ∀ y, p.toFun (F0 y) = F (y, ui0)) :
    ∃ G : Y × UI R → E, Continuous G ∧ (∀ q, p.toFun (G q) = F q) ∧ ∀ y, G (y, ui0) = F0 y :=
  sorry

end

end CovSpace

#print axioms CovSpace.exists_lift_homotopy
