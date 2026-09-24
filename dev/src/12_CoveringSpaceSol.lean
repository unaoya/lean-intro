import «07_ExercisesSol»
import «11_CoveringSol»
import «08_RealSol»

/-! # 発展演習: 位相空間の被覆（解答・下書き）

試作をまとめたもの。章の構成はこれから決める。
-/

namespace CovSpace

section


variable {X Y Z : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

/-! ## 部分空間 -/

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

/-- 開集合への制限で連続なら、そこで開集合の逆像は開。 -/
theorem isOpen_of_subtype_open {W : Set X} (hW : IsOpen W) {s : Set (Subtype W)}
    (hs : IsOpen s) : IsOpen {x | ∃ h : x ∈ W, (⟨x, h⟩ : Subtype W) ∈ s} := by
  obtain ⟨u, hu, rfl⟩ := isOpen_subtype_iff.mp hs
  have : {x | ∃ h : x ∈ W, (⟨x, h⟩ : Subtype W) ∈ Subtype.val ⁻¹' u} = W ∩ u := by
    apply Set.ext
    intro x
    exact ⟨fun ⟨h, hx⟩ => ⟨h, hx⟩, fun ⟨h, hx⟩ => ⟨h, hx⟩⟩
  rw [this]
  exact isOpen_inter _ _ hW hu

/-- **連続性は局所的**: 各点に、そこへの制限が連続になる開近傍があれば連続。 -/
theorem continuous_of_locally {f : X → Y}
    (h : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ Continuous (fun a : Subtype W => f a.1)) :
    Continuous f := by
  intro s hs
  apply isOpen_of_nhds
  intro x hx
  obtain ⟨W, hW, hxW, hf⟩ := h x
  refine ⟨{y | ∃ h : y ∈ W, (⟨y, h⟩ : Subtype W) ∈ (fun a : Subtype W => f a.1) ⁻¹' s},
    isOpen_of_subtype_open hW (hf s hs), ⟨hxW, hx⟩, fun y ⟨_, hy⟩ => hy⟩

/-! ## 積 -/

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

/-- 開集合の直積の合併で書ける集合の全体は位相をなす。 -/
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

/-- **積の開集合は、各点のまわりに開集合の直積を含む**。 -/
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

/-! ## 閉集合と貼り合わせ -/

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

/-- 逆像で閉集合が閉なら連続。 -/
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

/-- 閉集合の部分空間で閉な集合は、全体でも閉。 -/
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

/-- **貼り合わせ補題**: 2 つの閉集合で覆われた空間上の写像は、それぞれへの制限が連続なら連続。 -/
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

/-! ## 実数の閉集合 -/

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

/-! ## 単位区間 -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

/-- 単位区間 `[0, 1]`（実数の部分空間）。 -/
abbrev UI (R : Type) [CompleteOrderedField R] : Type := Subtype (fun t : R => t ∈ Icc (0 : R) 1)

theorem zero_le_one' : (0 : R) ≤ 1 := le_of_lt zero_lt_one

theorem le_of_eq' {a b : R} (h : a = b) : a ≤ b := h ▸ le_refl a

def ui0 : UI R := ⟨0, le_refl 0, zero_le_one'⟩
def ui1 : UI R := ⟨1, zero_le_one', le_refl 1⟩

theorem UI.ext {s t : UI R} (h : s.1 = t.1) : s = t := by
  cases s; cases t; cases h; rfl

/-! ### 半分と 2 倍の計算 -/

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

/-- `t / 2 ∈ [0, 1]`。 -/
def halfL (t : UI R) : UI R :=
  ⟨t.1 / 2, le_trans _ _ _ (le_of_eq' zero_div_two.symm) (div_two_le_div_two t.2.1),
    le_trans _ _ _ (div_two_le_div_two t.2.2) half_le_one⟩

/-- `(t + 1) / 2 ∈ [0, 1]`。 -/
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

/-! ### 2 のべき -/

/-- `2⁻ⁿ`。 -/
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

/-- 十分大きい `n` で `2⁻ⁿ < δ`。 -/
theorem exists_halfPow_lt {δ : R} (hδ : 0 < δ) : ∃ n : Nat, (halfPow n : R) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt δ⁻¹
  refine ⟨n, not_le.mp fun h => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left h (natCast_nonneg n)
  have h2 : 1 < natCast n * δ := by
    have := mul_lt_mul_of_pos_left hn hδ
    rwa [mul_comm δ, mul_comm δ, inv_mul_cancel (ne_of_lt hδ).symm] at this
  exact not_le.mpr (lt_of_lt_of_le h2 h1) (natCast_mul_halfPow_le n)

end

/-! ## 被覆と局所的な持ち上げ -/

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

/-- 開集合 `U` が `p` で**均等に被覆される**: `p ⁻¹' U` は互いに交わらない開集合（シート）`V i` に
分かれ、各シートは `p` で `U` と同相に写る。`s i` はその逆写像（`U` の上だけで意味を持つ）。 -/
def EvenlyCovered (p : E → X) (U : Set X) : Prop :=
  ∃ (ι : Type) (V : ι → Set E) (s : ι → X → E),
    (∀ i, IsOpen (V i)) ∧
    (∀ e, p e ∈ U → ∃ i, e ∈ V i) ∧
    (∀ i j e, e ∈ V i → e ∈ V j → i = j) ∧
    (∀ i x, x ∈ U → s i x ∈ V i ∧ p (s i x) = x) ∧
    (∀ i e, e ∈ V i → s i (p e) = e) ∧
    (∀ i, Continuous (fun x : Subtype U => s i x.1))

/-- **被覆**: 連続写像であって、底のどの点にも均等に被覆される開近傍があるもの。 -/
structure CoveringMap (E X : Type) [TopologicalSpace E] [TopologicalSpace X] where
  toFun : E → X
  continuous_toFun : Continuous toFun
  evenly : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ EvenlyCovered toFun U

theorem sub_halfR (a b : R) : (a + 1) / 2 - (b + 1) / 2 = (a - b) / 2 := by
  rw [← sub_div_two, add_sub_add_right]

/-- **局所的な持ち上げ**（2 等分の帰納法）。`y₀` の近傍 `N` の上で、長さ `2⁻ⁿ` の区間ごとに
`F` の像が均等被覆近傍に収まるなら、`y₀` のより小さい近傍の上に連続な持ち上げがある。 -/
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

/-! ## 持ち上げ定理 -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {E X : Type} [tE : TopologicalSpace E] [tX : TopologicalSpace X]

/-- 小ささの条件: `y₀` のある近傍と `n` について、長さ `2⁻ⁿ` の区間ごとに像が均等被覆近傍に収まる。
区間のコンパクト性とルベーグ数から出る。 -/
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

/-- **道の持ち上げの一意性**: 同じ道の 2 つの持ち上げは、始点が一致すれば一致する。 -/
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

/-- 1 点の空間の位相（開集合はすべて）。 -/
instance instTopUnit : TopologicalSpace Unit where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

/-- **道の持ち上げの存在**: 始点の持ち上げを決めれば、道は持ち上がる。 -/
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

/-- **ホモトピーの持ち上げ**: `F : Y × [0,1] → X` と、`F(·, 0)` の連続な持ち上げが与えられれば、
`F` 全体の連続な持ち上げがある。 -/
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

/-! ## 道とホモトピー -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

/-- 単位区間どうしの半分の貼り合わせ: `s ≤ 1/2` なら `f (2s)`、そうでなければ `g (2s - 1)`。 -/
noncomputable def glue {A : Type} (f g : UI R → A) (s : UI R) : A :=
  open Classical in
  if h : s.1 ≤ 1 / 2 then f ⟨2 * s.1, two_mul_mem s.2.1 h⟩
  else g ⟨2 * s.1 - 1, two_mul_sub_one_mem (le_of_lt (not_le.mp h)) s.2.2⟩

theorem glue_of_le {A : Type} (f g : UI R → A) {s : UI R} (h : s.1 ≤ 1 / 2) :
    glue f g s = f ⟨2 * s.1, two_mul_mem s.2.1 h⟩ := by
  unfold glue; rw [dif_pos h]

theorem glue_of_ge {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) {s : UI R} (h : 1 / 2 ≤ s.1) :
    glue f g s = g ⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ := by
  unfold glue
  by_cases h' : s.1 ≤ 1 / 2
  · rw [dif_pos h']
    have ht : s.1 = 1 / 2 := le_antisymm _ _ h' h
    have e1 : (⟨2 * s.1, two_mul_mem s.2.1 h'⟩ : UI R) = ui1 :=
      UI.ext (by show 2 * s.1 = 1; rw [ht, two_mul_half])
    have e2 : (⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ : UI R) = ui0 :=
      UI.ext (by show 2 * s.1 - 1 = 0; rw [ht, two_mul_half, sub_self])
    rw [e1, e2, hfg]
  · rw [dif_neg h']

/-- 貼り合わせは連続（パラメータつき版: `Z × [0,1]` の第 2 成分で貼る）。 -/
theorem continuous_glue_param {Z A : Type} [TopologicalSpace Z] [TopologicalSpace A]
    (f g : Z × UI R → A) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, f (z, ui1) = g (z, ui0)) :
    Continuous (fun q : Z × UI R => glue (fun s => f (q.1, s)) (fun s => g (q.1, s)) q.2) := by
  have hval : Continuous (fun q : Z × UI R => q.2.1) := continuous_subtype_val.comp continuous_snd
  refine continuous_of_closed_cover (isClosed_preimage hval (isClosed_le_const (1 / 2 : R)))
    (isClosed_preimage hval (isClosed_ge_const (1 / 2 : R))) (fun q => le_total _ _) ?_ ?_
  · have e : (fun a : Subtype ({q | q.2.1 ≤ 1 / 2} : Set (Z × UI R)) =>
        glue (fun s => f (a.1.1, s)) (fun s => g (a.1.1, s)) a.1.2) =
        fun a => f (a.1.1, ⟨2 * a.1.2.1, two_mul_mem a.1.2.2.1 a.2⟩) := by
      funext a; exact glue_of_le _ _ a.2
    have hc := hf.comp (continuous_prod_mk (continuous_fst.comp continuous_subtype_val)
      (continuous_subtype_mk (continuous_mul (continuous_const _) (hval.comp continuous_subtype_val))
        (fun a : Subtype ({q | q.2.1 ≤ 1 / 2} : Set (Z × UI R)) => two_mul_mem a.1.2.2.1 a.2)))
    rw [← e] at hc
    exact hc
  · have e : (fun a : Subtype ({q | 1 / 2 ≤ q.2.1} : Set (Z × UI R)) =>
        glue (fun s => f (a.1.1, s)) (fun s => g (a.1.1, s)) a.1.2) =
        fun a => g (a.1.1, ⟨2 * a.1.2.1 - 1, two_mul_sub_one_mem a.2 a.1.2.2.2⟩) := by
      funext a; exact glue_of_ge _ _ (hfg a.1.1) a.2
    have hc := hg.comp (continuous_prod_mk (continuous_fst.comp continuous_subtype_val)
      (continuous_subtype_mk (continuous_sub (continuous_mul (continuous_const _)
        (hval.comp continuous_subtype_val)) (continuous_const _))
        (fun a : Subtype ({q | 1 / 2 ≤ q.2.1} : Set (Z × UI R)) =>
          two_mul_sub_one_mem a.2 a.1.2.2.2)))
    rw [← e] at hc
    exact hc

theorem continuous_glue {A : Type} [TopologicalSpace A] {f g : UI R → A}
    (hf : Continuous f) (hg : Continuous g) (hfg : f ui1 = g ui0) : Continuous (glue f g) := by
  have := continuous_glue_param (Z := Unit) (fun q => f q.2) (fun q => g q.2)
    (hf.comp continuous_snd) (hg.comp continuous_snd) (fun _ => hfg)
  exact this.comp (continuous_prod_mk (continuous_const_map ()) continuous_id)

/-- `x` から `y` への道。 -/
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

/-- 定数道。 -/
def Path.refl (x : X) : Path (R := R) x x :=
  ⟨fun _ => x, continuous_const_map x, rfl, rfl⟩

/-- 連接。 -/
noncomputable def Path.trans (γ : Path (R := R) x y) (δ : Path (R := R) y z) : Path (R := R) x z :=
  ⟨glue γ.toFun δ.toFun, continuous_glue γ.continuous_toFun δ.continuous_toFun
      (by rw [γ.target, δ.source]),
    by rw [glue_of_le (s := ui0) _ _ half_nonneg']
       exact (congrArg γ.toFun (UI.ext (mul_zero 2))).trans γ.source,
    by rw [glue_of_ge (s := ui1) _ _ (by rw [γ.target, δ.source]) half_le_one]
       exact (congrArg δ.toFun (UI.ext (show 2 * 1 - 1 = (1 : R) by
         rw [two_mul_one, two_def, add_sub_cancel]))).trans δ.target⟩

/-- 区間の反転 `s ↦ 1 - s`。 -/
def uiRev (s : UI R) : UI R :=
  ⟨1 - s.1, sub_nonneg.mpr s.2.2, by
    have := add_le_add_left _ _ (neg_le_neg s.2.1) 1
    rwa [neg_zero, add_zero] at this⟩

theorem continuous_uiRev : Continuous (uiRev : UI R → UI R) :=
  continuous_subtype_mk (continuous_sub (continuous_const _) continuous_subtype_val) _

theorem uiRev_zero : uiRev (ui0 : UI R) = ui1 := UI.ext (sub_zero 1)
theorem uiRev_one : uiRev (ui1 : UI R) = ui0 := UI.ext (sub_self 1)

/-- 逆道。 -/
def Path.symm (γ : Path (R := R) x y) : Path (R := R) y x :=
  ⟨fun s => γ.toFun (uiRev s), γ.continuous_toFun.comp continuous_uiRev,
    by show γ.toFun (uiRev ui0) = y; rw [uiRev_zero, γ.target],
    by show γ.toFun (uiRev ui1) = x; rw [uiRev_one, γ.source]⟩

/-- 道のホモトピー（端点を止める）。`H (s, t)` の `s` が道のパラメータ、`t` が変形のパラメータ。 -/
def Path.Homotopic (γ δ : Path (R := R) x y) : Prop :=
  ∃ H : UI R × UI R → X, Continuous H ∧ (∀ s, H (s, ui0) = γ.toFun s) ∧
    (∀ s, H (s, ui1) = δ.toFun s) ∧ (∀ t, H (ui0, t) = x) ∧ (∀ t, H (ui1, t) = y)

/-! ### 再パラメータ化の補題 -/

/-- 凸結合 `(1 - t) a + t b` は区間に入る。 -/
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

/-- **再パラメータ化の補題**: 端点で一致する 2 つの `φ, ψ : [0,1] → [0,1]` について、
`γ ∘ φ` と `γ ∘ ψ` は（端点を止めて）ホモトピック。直線ホモトピーで示す。 -/
theorem homotopic_reparam (γ : UI R → X) (hγ : Continuous γ) {φ ψ : UI R → UI R}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h0 : φ ui0 = ψ ui0) (h1 : φ ui1 = ψ ui1)
    (P Q : Path (R := R) x y) (hP : ∀ s, P.toFun s = γ (φ s)) (hQ : ∀ s, Q.toFun s = γ (ψ s)) :
    P.Homotopic Q := by
  refine ⟨fun q => γ (uiMix (φ q.1) (ψ q.1) q.2), ?_, fun s => ?_, fun s => ?_, fun t => ?_,
    fun t => ?_⟩
  · exact hγ.comp (continuous_uiMix (hφ.comp continuous_fst) (hψ.comp continuous_fst) continuous_snd)
  · show γ (uiMix _ _ ui0) = _; rw [uiMix_zero, hP]
  · show γ (uiMix _ _ ui1) = _; rw [uiMix_one, hQ]
  · show γ (uiMix (φ ui0) (ψ ui0) t) = x
    rw [h0, uiMix_self, ← hQ, Q.source]
  · show γ (uiMix (φ ui1) (ψ ui1) t) = y
    rw [h1, uiMix_self, ← hQ, Q.target]

end

/-! ## ホモトピーの同値性と亜群の法則 -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]
variable {x y z w : X}

/-! ### 貼り合わせの計算規則 -/

theorem glue_comp {A B : Type} (h : A → B) (f g : UI R → A) (s : UI R) :
    h (glue f g s) = glue (fun u => h (f u)) (fun u => h (g u)) s := by
  unfold glue
  by_cases hs : s.1 ≤ 1 / 2
  · rw [dif_pos hs, dif_pos hs]
  · rw [dif_neg hs, dif_neg hs]

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

theorem glue_halfL {A : Type} (f g : UI R → A) (u : UI R) : glue f g (halfL u) = f u := by
  rw [glue_of_le (s := halfL u) _ _ (le_trans _ _ _ (div_two_le_div_two u.2.2) (le_refl _))]
  exact congrArg f (UI.ext (show 2 * (u.1 / 2) = u.1 from mul_div_cancel_left _ two_ne_zero))

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

/-! ### 同値関係 -/

theorem Path.Homotopic.refl' (γ : Path (R := R) x y) : γ.Homotopic γ :=
  ⟨fun q => γ.toFun q.1, γ.continuous_toFun.comp continuous_fst, fun _ => rfl, fun _ => rfl,
    fun _ => γ.source, fun _ => γ.target⟩

theorem Path.Homotopic.symm' {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : δ.Homotopic γ := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  refine ⟨fun q => H (q.1, uiRev q.2), hH.comp (continuous_prod_mk continuous_fst
    (continuous_uiRev.comp continuous_snd)), fun s => ?_, fun s => ?_, fun t => hx _, fun t => hy _⟩
  · show H (s, uiRev ui0) = _; rw [uiRev_zero, h1]
  · show H (s, uiRev ui1) = _; rw [uiRev_one, h0]

theorem Path.Homotopic.trans' {γ δ ε : Path (R := R) x y} (h : γ.Homotopic δ) (k : δ.Homotopic ε) :
    γ.Homotopic ε := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  obtain ⟨K, hK, k0, k1, kx, ky⟩ := k
  have hHK : ∀ s, H (s, ui1) = K (s, ui0) := fun s => by rw [h1, k0]
  refine ⟨fun q => glue (fun t => H (q.1, t)) (fun t => K (q.1, t)) q.2,
    continuous_glue_param H K hH hK hHK, fun s => ?_, fun s => ?_, fun t => ?_, fun t => ?_⟩
  · show glue _ _ ui0 = _; rw [glue_zero, h0]
  · show glue _ _ ui1 = _; rw [glue_one _ _ (hHK s), k1]
  · exact glue_const (fun _ => hx _) (fun _ => kx _) t
  · exact glue_const (fun _ => hy _) (fun _ => ky _) t

/-! ### 連接・逆道との両立 -/

theorem continuous_swap {A B : Type} [TopologicalSpace A] [TopologicalSpace B] :
    Continuous (fun q : A × B => (q.2, q.1)) := continuous_prod_mk continuous_snd continuous_fst

theorem Path.Homotopic.trans_congr {γ γ' : Path (R := R) x y} {δ δ' : Path (R := R) y z}
    (h : γ.Homotopic γ') (k : δ.Homotopic δ') : (γ.trans δ).Homotopic (γ'.trans δ') := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  obtain ⟨K, hK, k0, k1, kx, ky⟩ := k
  have hHK : ∀ t, H (ui1, t) = K (ui0, t) := fun t => by rw [hy, kx]
  have hc := continuous_glue_param (fun q : UI R × UI R => H (q.2, q.1))
    (fun q => K (q.2, q.1)) (hH.comp continuous_swap) (hK.comp continuous_swap) hHK
  refine ⟨fun q => glue (fun s => H (s, q.2)) (fun s => K (s, q.2)) q.1,
    hc.comp continuous_swap, fun s => ?_, fun s => ?_, fun t => ?_, fun t => ?_⟩
  · exact glue_congr (fun u => h0 u) (fun u => k0 u) s
  · exact glue_congr (fun u => h1 u) (fun u => k1 u) s
  · show glue _ _ ui0 = x; rw [glue_zero, hx]
  · show glue _ _ ui1 = z; rw [glue_one _ _ (hHK t), ky]

theorem Path.Homotopic.symm_congr {γ γ' : Path (R := R) x y} (h : γ.Homotopic γ') :
    γ.symm.Homotopic γ'.symm := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  refine ⟨fun q => H (uiRev q.1, q.2), hH.comp (continuous_prod_mk
    (continuous_uiRev.comp continuous_fst) continuous_snd), fun s => h0 _, fun s => h1 _,
    fun t => ?_, fun t => ?_⟩
  · show H (uiRev ui0, t) = y; rw [uiRev_zero, hy]
  · show H (uiRev ui1, t) = x; rw [uiRev_one, hx]

/-! ### 亜群の法則（再パラメータ化の補題から） -/

theorem continuous_id' {A : Type} [TopologicalSpace A] : Continuous (fun a : A => a) :=
  continuous_id

theorem Path.refl_trans (γ : Path (R := R) x y) : ((Path.refl x).trans γ).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun _ => ui0) (fun u => u))
    (ψ := fun u => u) (continuous_glue (continuous_const_map _) continuous_id' rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue (fun _ => x) γ.toFun s = γ.toFun (glue (fun _ => ui0) (fun u => u) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => γ.source.symm) (fun _ => rfl) s

theorem Path.trans_refl (γ : Path (R := R) x y) : (γ.trans (Path.refl y)).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) (fun _ => ui1))
    (ψ := fun u => u) (continuous_glue continuous_id' (continuous_const_map _) rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue γ.toFun (fun _ => y) s = γ.toFun (glue (fun u => u) (fun _ => ui1) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => rfl) (fun _ => γ.target.symm) s

theorem Path.trans_assoc (γ : Path (R := R) x y) (δ : Path (R := R) y z) (ε : Path (R := R) z w) :
    ((γ.trans δ).trans ε).Homotopic (γ.trans (δ.trans ε)) := by
  let Γ := γ.trans (δ.trans ε)
  let α : UI R → UI R := glue halfL (fun u => halfR (halfL u))
  let β : UI R → UI R := fun u => halfR (halfR u)
  have hα1 : halfL (ui1 : UI R) = halfR (halfL ui0) := by rw [halfL_zero, halfL_one]
  have hαc : Continuous α := continuous_glue continuous_halfL
    (continuous_halfR.comp continuous_halfL) hα1
  have hαβ : α ui1 = β ui0 := by
    show glue _ _ ui1 = halfR (halfR ui0)
    rw [glue_one _ _ hα1, halfL_one]
  refine homotopic_reparam Γ.toFun Γ.continuous_toFun (φ := glue α β) (ψ := fun u => u)
    (continuous_glue hαc (continuous_halfR.comp continuous_halfR) hαβ) continuous_id' ?_ ?_ _ _
    (fun s => ?_) (fun s => rfl)
  · show glue α β ui0 = ui0
    rw [glue_zero]
    show glue _ _ ui0 = ui0
    rw [glue_zero, halfL_zero]
  · show glue α β ui1 = ui1
    rw [glue_one _ _ hαβ]
    show halfR (halfR ui1) = ui1
    exact UI.ext (show ((((1 : R) + 1) / 2) + 1) / 2 = 1 by rw [← two_def, two_div_two, ← two_def,
      two_div_two])
  · show glue (glue γ.toFun δ.toFun) ε.toFun s = Γ.toFun (glue α β s)
    rw [glue_comp Γ.toFun]
    refine glue_congr (fun u => ?_) (fun u => ?_) s
    · show glue γ.toFun δ.toFun u = Γ.toFun (glue halfL (fun u => halfR (halfL u)) u)
      rw [glue_comp Γ.toFun]
      exact glue_congr (fun v => (Path.trans_halfL _ _ v).symm)
        (fun v => by
          show δ.toFun v = Γ.toFun (halfR (halfL v))
          rw [Path.trans_halfR, Path.trans_halfL]) u
    · show ε.toFun u = Γ.toFun (halfR (halfR u))
      rw [Path.trans_halfR, Path.trans_halfR]

theorem Path.symm_trans (γ : Path (R := R) x y) : (γ.symm.trans γ).Homotopic (Path.refl y) := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue uiRev (fun u => u))
    (ψ := fun _ => ui1) (continuous_glue continuous_uiRev continuous_id' uiRev_one)
    (continuous_const_map _) (by rw [glue_zero, uiRev_zero]) (glue_one _ _ uiRev_one) _ _
    (fun s => ?_) (fun s => γ.target.symm)
  show glue (fun u => γ.toFun (uiRev u)) γ.toFun s = γ.toFun (glue uiRev (fun u => u) s)
  rw [glue_comp γ.toFun]

theorem Path.trans_symm (γ : Path (R := R) x y) : (γ.trans γ.symm).Homotopic (Path.refl x) := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) uiRev)
    (ψ := fun _ => ui0) (continuous_glue continuous_id' continuous_uiRev uiRev_zero.symm)
    (continuous_const_map _) (glue_zero _ _) (by rw [glue_one _ _ uiRev_zero.symm, uiRev_one]) _ _
    (fun s => ?_) (fun s => γ.source.symm)
  show glue γ.toFun (fun u => γ.toFun (uiRev u)) s = γ.toFun (glue (fun u => u) uiRev s)
  rw [glue_comp γ.toFun]

end

/-! ## 基本亜群とモノドロミー -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

/-- 道のホモトピー類。 -/
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

/-! ### モノドロミー -/

variable {E : Type} [tE : TopologicalSpace E]

namespace CoveringMap

variable (p : CoveringMap E X)

/-- 点 `x` の上のファイバー。 -/
abbrev Fiber (x : X) : Type := {e : E // p.toFun e = x}

theorem fiberExt {x : X} {a b : p.Fiber x} (h : a.1 = b.1) : a = b := by
  cases a; cases b; cases h; rfl

variable {x y z : X}

theorem fiber_start (γ : Path (R := R) x y) (a : p.Fiber x) : p.toFun a.1 = γ.toFun ui0 := by
  rw [a.2, γ.source]

/-- 道の持ち上げの終点。 -/
noncomputable def liftEnd (γ : Path (R := R) x y) (a : p.Fiber x) : p.Fiber y :=
  ⟨Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1 (p.fiber_start γ a)) ui1,
   by rw [(Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
      (p.fiber_start γ a))).2.1, γ.target]⟩

/-- `liftEnd` の特徴づけ: 持ち上げを 1 つ示せば終点が決まる。 -/
theorem liftEnd_eq (γ : Path (R := R) x y) (a : p.Fiber x) {f : UI R → E} (hf : Continuous f)
    (hfp : ∀ t, p.toFun (f t) = γ.toFun t) (hf0 : f ui0 = a.1) : (p.liftEnd γ a).1 = f ui1 := by
  have spec := Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
    (p.fiber_start γ a))
  have := lift_unique p spec.1 hf (fun t => by rw [spec.2.1, hfp]) (by rw [spec.2.2, hf0])
  exact congrFun this ui1

/-- ホモトピックな道の持ち上げは、同じ点に着く（ホモトピーの持ち上げから）。 -/
theorem liftEnd_homotopic {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) (a : p.Fiber x) :
    p.liftEnd γ a = p.liftEnd δ a := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  have spec := Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
    (p.fiber_start γ a))
  let γ' := Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1 (p.fiber_start γ a))
  obtain ⟨G, hG, hGp, hG0⟩ := exists_lift_homotopy p H hH γ' spec.1 (fun s => by
    show p.toFun (γ' s) = H (s, ui0); rw [spec.2.1, h0])
  -- `G (0, ·)` は定数道 `x` の持ち上げなので定数
  have hleft : (fun t => G (ui0, t)) = fun _ => a.1 := by
    refine lift_unique p (hG.comp (continuous_prod_mk (continuous_const_map _) continuous_id'))
      (continuous_const_map _) (fun t => by
        show p.toFun (G (ui0, t)) = p.toFun a.1; rw [hGp, hx, a.2]) ?_
    show G (ui0, ui0) = a.1; rw [hG0]; exact spec.2.2
  have hright : (fun t => G (ui1, t)) = fun _ => γ' ui1 := by
    refine lift_unique p (hG.comp (continuous_prod_mk (continuous_const_map _) continuous_id'))
      (continuous_const_map _) (fun t => by
        show p.toFun (G (ui1, t)) = p.toFun (γ' ui1); rw [hGp, hy, spec.2.1, γ.target]) ?_
    show G (ui1, ui0) = γ' ui1; rw [hG0]
  apply p.fiberExt
  have e1 : (p.liftEnd δ a).1 = G (ui1, ui1) :=
    p.liftEnd_eq δ a (hG.comp (continuous_prod_mk continuous_id' (continuous_const_map _)))
      (fun t => by show p.toFun (G (t, ui1)) = _; rw [hGp, h1])
      (congrFun hleft ui1)
  rw [e1, congrFun hright ui1]
  rfl

/-- ホモトピー類に沿った輸送（モノドロミー）。 -/
noncomputable def transport (φ : PathClass R x y) (a : p.Fiber x) : p.Fiber y :=
  Quot.lift (fun γ => p.liftEnd γ a) (fun _ _ h => p.liftEnd_homotopic h a) φ

theorem transport_refl (a : p.Fiber x) : p.transport (PathClass.refl (R := R) x) a = a :=
  p.fiberExt (p.liftEnd_eq (Path.refl x) a (continuous_const_map a.1) (fun _ => a.2) rfl)

theorem transport_trans (φ : PathClass R x y) (ψ : PathClass R y z) (a : p.Fiber x) :
    p.transport (φ.comp ψ) a = p.transport ψ (p.transport φ a) := by
  induction φ using Quot.ind with
  | mk γ =>
    induction ψ using Quot.ind with
    | mk δ =>
      show p.liftEnd (γ.trans δ) a = p.liftEnd δ (p.liftEnd γ a)
      have sγ := Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
        (p.fiber_start γ a))
      let γ' := Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1
        (p.fiber_start γ a))
      let b := p.liftEnd γ a
      have sδ := Classical.choose_spec (exists_lift_path p δ.toFun δ.continuous_toFun b.1
        (p.fiber_start δ b))
      let δ' := Classical.choose (exists_lift_path p δ.toFun δ.continuous_toFun b.1
        (p.fiber_start δ b))
      have hjoin : γ' ui1 = δ' ui0 := sδ.2.2.symm
      apply p.fiberExt
      rw [p.liftEnd_eq (γ.trans δ) a (continuous_glue sγ.1 sδ.1 hjoin)
        (fun t => by
          show p.toFun (glue γ' δ' t) = glue γ.toFun δ.toFun t
          rw [glue_comp p.toFun]
          exact glue_congr sγ.2.1 sδ.2.1 t)
        (by rw [glue_zero]; exact sγ.2.2), glue_one _ _ hjoin]
      rfl

theorem transport_bijective (φ : PathClass R x y) : Function.Bijective (p.transport φ) where
  injective := by
    intro a b h
    have h' := congrArg (p.transport φ.inv) h
    rw [← p.transport_trans, ← p.transport_trans, PathClass.comp_inv, p.transport_refl,
      p.transport_refl] at h'
    exact h'
  surjective := by
    intro b
    refine ⟨p.transport φ.inv b, ?_⟩
    rw [← p.transport_trans, PathClass.inv_comp, p.transport_refl]

end CoveringMap

end

/-! ## 共通の枠組み: グラフの被覆と位相空間の被覆 -/

section

/-- 道のホモトピー類の連接構造（亜群）の抽象化。 -/
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

/-- 被覆の抽象化: ファイバーの族と、道のホモトピー類に沿った輸送。 -/
structure LiftSystem {V : Type} (P : PathSystem V) (F : V → Type) where
  transport : {x y : V} → P.Hom x y → F x → F y
  transport_refl : ∀ (x : V) (a : F x), transport (P.refl x) a = a
  transport_trans : ∀ {x y z : V} (γ : P.Hom x y) (δ : P.Hom y z) (a : F x),
    transport (P.trans γ δ) a = transport δ (transport γ a)

namespace LiftSystem

variable {V : Type} {P : PathSystem V} {F : V → Type} (L : LiftSystem P F)

/-- **共通の定理**: モノドロミーはファイバーの間の全単射。 -/
theorem transport_bijective {x y : V} (γ : P.Hom x y) : Function.Bijective (L.transport γ) where
  injective := by
    intro a b h
    have h' := congrArg (L.transport (P.symm γ)) h
    rw [← L.transport_trans, ← L.transport_trans, P.trans_symm, L.transport_refl,
      L.transport_refl] at h'
    exact h'
  surjective := by
    intro b
    refine ⟨L.transport (P.symm γ) b, ?_⟩
    rw [← L.transport_trans, P.symm_trans, L.transport_refl]

end LiftSystem

/-! ### 実例 1: グラフの被覆（`11_Covering.lean`） -/

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

/-! ### 実例 2: 位相空間の被覆 -/

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

/-- 同じ定理の 2 つの実例。 -/
example {Y X : SGraph} (p : SGraph.Covering Y X) {v w : X.V} (γ : SGraph.PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  (graphLiftSystem p).transport_bijective γ

example {E X : Type} [TopologicalSpace E] [TopologicalSpace X] (p : CoveringMap E X) {x y : X}
    (γ : PathClass R x y) : Function.Bijective (p.transport γ) :=
  (topLiftSystem p).transport_bijective γ

end

/-! ## 円周 -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

/-! ### 整数の計算 -/

theorem natCast_succ_ge_one (k : Nat) : (1 : R) ≤ natCast (k + 1) := by
  rw [natCast_succ]
  have := add_le_add_right (natCast_nonneg (R := R) k) 1
  rwa [zero_add] at this

/-- 絶対値が 1 未満の整数は 0。 -/
theorem int_eq_zero_of_abs_lt_one : ∀ {k : Int}, abs (intCast k : R) < 1 → k = 0
  | Int.ofNat 0, _ => rfl
  | Int.ofNat (k + 1), h => by
      exfalso
      have h' : abs (natCast (k + 1) : R) < 1 := h
      rw [abs_of_nonneg (natCast_nonneg _)] at h'
      exact not_le.mpr h' (natCast_succ_ge_one k)
  | Int.negSucc k, h => by
      exfalso
      have h' : abs (-natCast (k + 1) : R) < 1 := h
      rw [abs_neg, abs_of_nonneg (natCast_nonneg _)] at h'
      exact not_le.mpr h' (natCast_succ_ge_one k)

theorem intCast_sub (m n : Int) : (intCast (m - n) : R) = intCast m - intCast n := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg]; rfl

theorem intCast_injective {m n : Int} (h : (intCast m : R) = intCast n) : m = n := by
  have : m - n = 0 := int_eq_zero_of_abs_lt_one (R := R)
    (by rw [intCast_sub, h, sub_self, abs_zero]; exact zero_lt_one)
  omega

/-- 実数の差が整数で、どちらも `a` から `1/2` 未満の距離にあれば、2 数は等しい。 -/
theorem eq_of_close {a r w : R} {m : Int} (hr : abs (r - a) < 1 / 2) (hw : abs (w - a) < 1 / 2)
    (hm : w = r + intCast m) : w = r := by
  have hm0 : m = 0 := by
    apply int_eq_zero_of_abs_lt_one (R := R)
    have e : (intCast m : R) = (w - a) + (a - r) := by
      rw [hm, sub_add_sub_cancel]
      rw [sub_def, add_comm r, add_assoc, add_neg_cancel, add_zero]
    rw [e]
    refine lt_of_le_of_lt (abs_add _ _) ?_
    have hr' : abs (a - r) < 1 / 2 := by rw [abs_sub_comm]; exact hr
    have := add_lt_add hw hr'
    rwa [add_halves] at this
  rw [hm, hm0]; exact add_zero r

/-! ### 円周 `R / ℤ` -/

/-- 整数だけずれた 2 数を同一視する。 -/
def circleSetoid (R : Type) [CompleteOrderedField R] : Setoid R where
  r a b := ∃ n : Int, b = a + intCast n
  iseqv := {
    refl := fun a => ⟨0, (add_zero a).symm⟩
    symm := fun {a b} ⟨n, h⟩ => ⟨-n, by rw [h, intCast_neg, add_assoc, add_neg_cancel, add_zero]⟩
    trans := fun {a b c} ⟨m, h₁⟩ ⟨n, h₂⟩ => ⟨m + n, by rw [h₂, h₁, intCast_add, add_assoc]⟩ }

/-- 円周。 -/
def Circle (R : Type) [CompleteOrderedField R] : Type := Quotient (circleSetoid R)

instance : TopologicalSpace (Circle R) :=
  inferInstanceAs (TopologicalSpace (Quot (circleSetoid R).r))

/-- 射影 `R → R/ℤ`。 -/
def proj (r : R) : Circle R := Quotient.mk _ r

theorem proj_eq_iff {a b : R} : proj a = proj b ↔ ∃ n : Int, b = a + intCast n :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem proj_add_int (a : R) (n : Int) : proj (a + intCast n) = proj a :=
  (proj_eq_iff.mpr ⟨n, rfl⟩).symm

theorem continuous_proj : Continuous (proj : R → Circle R) :=
  continuous_quotMk (circleSetoid R).r

theorem isOpen_circle_iff {s : Set (Circle R)} : IsOpen s ↔ IsOpen (proj ⁻¹' s) := Iff.rfl

/-- `proj` は開写像。 -/
theorem isOpen_image_proj {W : Set R} (hW : IsOpen W) :
    IsOpen ({z | ∃ w, w ∈ W ∧ proj w = z} : Set (Circle R)) := by
  rw [isOpen_circle_iff]
  intro r ⟨w, hwW, hwr⟩
  obtain ⟨n, hn⟩ := proj_eq_iff.mp hwr
  obtain ⟨ε, hε, hball⟩ := hW w hwW
  refine ⟨ε, hε, fun r' hr' => ⟨r' - intCast n, hball _ ?_, ?_⟩⟩
  · have e : r' - intCast n - w = r' - r := by
      rw [hn, sub_def, sub_def, sub_def, neg_add]; ac_rfl
    rw [e]; exact hr'
  · show proj (r' - intCast n) = proj r'
    rw [← proj_add_int (r' - intCast n) n, sub_add_cancel]

/-! ### `R → R/ℤ` は被覆 -/

/-- 点 `a` のまわりの均等被覆近傍の、シート `n` の逆写像。 -/
noncomputable def circleSec (a : R) (n : Int) (z : Circle R) : R :=
  open Classical in
  if h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z then Classical.choose h + intCast n else 0

theorem circleSec_spec {a : R} {z : Circle R} (h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z) (n : Int) :
    ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z ∧ circleSec a n z = r + intCast n := by
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  unfold circleSec; rw [dif_pos h]

/-- `a` から `1/2` 未満の点 `r` の類については、逆写像の値は `r + n`。 -/
theorem circleSec_proj {a r : R} (hr : abs (r - a) < 1 / 2) (n : Int) :
    circleSec a n (proj r) = r + intCast n := by
  obtain ⟨r', hr', hpr', hs⟩ := circleSec_spec ⟨r, hr, rfl⟩ n
  obtain ⟨m, hm⟩ := proj_eq_iff.mp hpr'
  rw [hs, ← eq_of_close hr' hr hm]

theorem abs_shift (r a : R) (n : Int) : abs (r + intCast n - (a + intCast n)) = abs (r - a) := by
  rw [add_sub_add_right]

theorem evenlyCovered_circle (a : R) :
    EvenlyCovered (proj : R → Circle R) {z | ∃ r, r ∈ ball a (1 / 2) ∧ proj r = z} := by
  refine ⟨Int, fun n => ball (a + intCast n) (1 / 2), circleSec a, fun n => isOpen_ball _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- `p⁻¹ U` はシートの合併
    intro e ⟨r, hr, hre⟩
    obtain ⟨n, hn⟩ := proj_eq_iff.mp hre
    refine ⟨n, ?_⟩
    show abs (e - (a + intCast n)) < 1 / 2
    rw [hn, abs_shift]; exact hr
  · -- シートは互いに交わらない
    intro m n e hm hn
    apply intCast_injective (R := R)
    have h1 : abs (e - (a + intCast m)) < 1 / 2 := hm
    have h2 : abs (e - (a + intCast n)) < 1 / 2 := hn
    have e1 : (intCast m : R) = a + intCast m - a := by rw [add_comm a, add_sub_cancel]
    have e2 : (intCast n : R) = a + intCast n - a := by rw [add_comm a, add_sub_cancel]
    refine Classical.byContradiction fun hne => ?_
    have := eq_of_close (a := e) (r := a + intCast m) (w := a + intCast n) (m := n - m)
      (by rw [abs_sub_comm]; exact h1) (by rw [abs_sub_comm]; exact h2)
      (by rw [intCast_sub, add_assoc, sub_def, add_comm (intCast n), ← add_assoc (intCast m),
            add_neg_cancel, zero_add])
    exact hne (by
      have h3 := congrArg (fun t => t - a) this
      simp only at h3
      rw [← e1, ← e2] at h3
      exact h3.symm)
  · -- 逆写像はシートに入り、`p` で戻る
    intro n z ⟨r, hr, hrz⟩
    rw [← hrz, circleSec_proj hr n]
    refine ⟨?_, proj_add_int r n⟩
    show abs (r + intCast n - (a + intCast n)) < 1 / 2
    rw [abs_shift]; exact hr
  · -- シートの点 `e` については `s (p e) = e`
    intro n e he
    have he' : abs (e - (a + intCast n)) < 1 / 2 := he
    have hr : abs (e - intCast n - a) < 1 / 2 := by
      have : e - intCast n - a = e - (a + intCast n) := by
        rw [sub_def, sub_def, sub_def, neg_add]; ac_rfl
      rw [this]; exact he'
    have hpe : proj e = proj (e - intCast n) := by
      rw [← proj_add_int (e - intCast n) n, sub_add_cancel]
    rw [hpe, circleSec_proj hr n, sub_add_cancel]
  · -- 逆写像は連続（`proj` が開写像であることから）
    intro n
    intro O hO
    let W : Set R := {r | abs (r - a) < 1 / 2 ∧ r + intCast n ∈ O}
    have hWo : IsOpen W :=
      isOpen_inter _ _ (isOpen_ball a (1 / 2))
        (continuous_add continuous_id' (continuous_const _) O hO)
    refine isOpen_subtype_iff.mpr ⟨_, isOpen_image_proj hWo, ?_⟩
    apply Set.ext
    intro z
    constructor
    · intro hz
      obtain ⟨r, hr, hrz⟩ := z.2
      refine ⟨r, ⟨hr, ?_⟩, hrz⟩
      have hz' : circleSec a n z.1 ∈ O := hz
      rw [← hrz, circleSec_proj hr n] at hz'
      exact hz'
    · intro ⟨w, ⟨hw, hwO⟩, hwz⟩
      show circleSec a n z.1 ∈ O
      rw [← hwz, circleSec_proj hw n]; exact hwO

/-- **`R → R/ℤ` は被覆**。 -/
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

/-! ## π₁(S¹) ≃ ℤ -/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

/-- 円周の基点 `[0]`。 -/
def base : Circle R := proj 0

theorem proj_intCast (m : Int) : proj (intCast m : R) = base := by
  have := proj_add_int (0 : R) m
  rw [zero_add] at this
  exact this

/-- 基点の上のファイバーの点 `m`（整数）。 -/
def fibInt (m : Int) : circleCovering.Fiber (base : Circle R) := ⟨intCast m, proj_intCast m⟩

/-- 基点の上のファイバーの点は整数。 -/
theorem fiber_int (a : circleCovering.Fiber (base : Circle R)) : ∃ n : Int, a.1 = intCast n := by
  obtain ⟨n, hn⟩ := proj_eq_iff.mp a.2
  refine ⟨-n, ?_⟩
  rw [intCast_neg]
  have h : a.1 + intCast n = 0 := hn.symm
  have := neg_eq_of_add_eq_zero h
  rw [← this, neg_neg]

/-- **デッキ変換**: 整数 `m` から持ち上げると、`0` から持ち上げた終点を `m` だけずらした点に着く。 -/
theorem transport_fibInt (φ : PathClass R (base : Circle R) base) (m : Int) :
    (circleCovering.transport φ (fibInt m)).1 = (circleCovering.transport φ (fibInt 0)).1 + intCast m := by
  induction φ using Quot.ind with
  | mk γ =>
    show (circleCovering.liftEnd γ (fibInt m)).1 = (circleCovering.liftEnd γ (fibInt 0)).1 + intCast m
    have spec := Classical.choose_spec (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
      (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0)))
    rw [circleCovering.liftEnd_eq γ (fibInt m)
      (f := fun t => Classical.choose (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
        (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0))) t + intCast m)
      (continuous_add spec.1 (continuous_const _))
      (fun t => by
        show proj (_ + intCast m) = γ.toFun t
        rw [proj_add_int]; exact spec.2.1 t)
      (by show _ + intCast m = intCast m; rw [spec.2.2]; exact zero_add _)]
    rfl

/-- **モノドロミー次数**: ループを `0` から持ち上げた終点の整数。 -/
noncomputable def deg (φ : PathClass R (base : Circle R) base) : Int :=
  Classical.choose (fiber_int (circleCovering.transport φ (fibInt 0)))

theorem deg_spec (φ : PathClass R (base : Circle R) base) :
    circleCovering.transport φ (fibInt 0) = fibInt (deg φ) :=
  circleCovering.fiberExt (Classical.choose_spec (fiber_int (circleCovering.transport φ (fibInt 0))))

theorem deg_comp (φ ψ : PathClass R (base : Circle R) base) :
    deg (φ.comp ψ) = deg φ + deg ψ := by
  apply intCast_injective (R := R)
  have h := congrArg Subtype.val (deg_spec (φ.comp ψ))
  rw [circleCovering.transport_trans, deg_spec φ, transport_fibInt, deg_spec ψ] at h
  have h' : (intCast (deg (φ.comp ψ)) : R) = intCast (deg ψ) + intCast (deg φ) := h.symm
  rw [h', intCast_add, add_comm]

theorem deg_refl : deg (PathClass.refl (R := R) (base : Circle R)) = 0 := by
  apply intCast_injective (R := R)
  have h := congrArg Subtype.val (deg_spec (PathClass.refl (R := R) (base : Circle R)))
  rw [circleCovering.transport_refl] at h
  exact h.symm

theorem deg_inv (φ : PathClass R (base : Circle R) base) : deg φ.inv = -deg φ := by
  have h := deg_comp φ.inv φ
  rw [PathClass.inv_comp, deg_refl] at h
  omega

/-- 核は自明: 次数 0 のループは定数ループにホモトピック（`R` の直線ホモトピーを押し出す）。 -/
theorem deg_eq_zero {φ : PathClass R (base : Circle R) base} (h : deg φ = 0) :
    φ = PathClass.refl base := by
  induction φ using Quot.ind with
  | mk γ =>
    have spec := Classical.choose_spec (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
      (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0)))
    let γ' := Classical.choose (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
      (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0)))
    have h0 : γ' ui0 = 0 := spec.2.2
    have h1 : γ' ui1 = 0 := by
      have := congrArg Subtype.val (deg_spec (PathClass.mk γ))
      rw [show deg (PathClass.mk γ) = 0 from h] at this
      exact this
    refine PathClass.sound ⟨fun q => proj ((1 - q.2.1) * γ' q.1), ?_, fun s => ?_, fun s => ?_,
      fun t => ?_, fun t => ?_⟩
    · exact continuous_proj.comp (continuous_mul
        (continuous_sub (continuous_const _) (continuous_subtype_val.comp continuous_snd))
        (spec.1.comp continuous_fst))
    · show proj ((1 - 0) * γ' s) = γ.toFun s
      rw [sub_zero, one_mul]; exact spec.2.1 s
    · show proj ((1 - 1) * γ' s) = base
      rw [sub_self, zero_mul]; rfl
    · show proj ((1 - t.1) * γ' ui0) = base
      rw [h0, mul_zero]; rfl
    · show proj ((1 - t.1) * γ' ui1) = base
      rw [h1, mul_zero]; rfl

theorem deg_injective : Function.Injective (deg (R := R)) := by
  intro φ ψ h
  have hz : deg (φ.comp ψ.inv) = 0 := by
    rw [deg_comp, deg_inv]; omega
  have hk := deg_eq_zero hz
  calc φ = φ.comp (PathClass.refl base) := (PathClass.comp_refl φ).symm
    _ = φ.comp (ψ.inv.comp ψ) := congrArg φ.comp (PathClass.inv_comp ψ).symm
    _ = (φ.comp ψ.inv).comp ψ := (PathClass.comp_assoc φ ψ.inv ψ).symm
    _ = (PathClass.refl base).comp ψ := by rw [hk]
    _ = ψ := PathClass.refl_comp ψ

/-- `n` 周するループ `t ↦ [n t]`。 -/
def loopN (n : Int) : Path (R := R) (base : Circle R) base where
  toFun t := proj (intCast n * t.1)
  continuous_toFun := continuous_proj.comp (continuous_mul (continuous_const _) continuous_subtype_val)
  source := by show proj (intCast n * 0) = base; rw [mul_zero]; rfl
  target := by show proj (intCast n * 1) = base; rw [mul_one]; exact proj_intCast n

theorem deg_surjective : Function.Surjective (deg (R := R)) := by
  intro n
  refine ⟨PathClass.mk (loopN n), intCast_injective (R := R) ?_⟩
  have h := congrArg Subtype.val (deg_spec (PathClass.mk (loopN (R := R) n)))
  refine (show (intCast (deg (PathClass.mk (loopN (R := R) n))) : R) = _ from h.symm).trans ?_
  show (circleCovering.liftEnd (loopN n) (fibInt 0)).1 = intCast n
  rw [circleCovering.liftEnd_eq (loopN n) (fibInt 0) (f := fun t => intCast n * t.1)
    (continuous_mul (continuous_const _) continuous_subtype_val) (fun _ => rfl)
    (show intCast n * 0 = intCast 0 by rw [mul_zero]; rfl)]
  show intCast n * 1 = intCast n
  rw [mul_one]

/-- **主定理 π₁(S¹) ≃ ℤ**: モノドロミー次数は、連接を和に写す全単射である。 -/
theorem pi1_circle :
    (∀ φ ψ : PathClass R (base : Circle R) base, deg (φ.comp ψ) = deg φ + deg ψ) ∧
      Function.Bijective (deg (R := R)) :=
  ⟨deg_comp, ⟨deg_injective, deg_surjective⟩⟩

end

end CovSpace

#print axioms CovSpace.pi1_circle
