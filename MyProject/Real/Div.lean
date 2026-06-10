import MyProject.Real.Order

noncomputable section

open Real Classical

-- 乗法の順序と除法

theorem mul_nonneg (a b : Real) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b :=
  LinearOrderedField.mul_pos a b h h'

theorem nonmul_neg_le (a b c : Real) (hc : 0 ≤ c) (hab : 0 ≤ b - a) :
    0 ≤ b * c - a * c := by
  rw [show b * c - a * c = b * c + -(a * c) from rfl,
      show -(a * c) = (-a) * c from (neg_mul a c).symm,
      show b * c + (-a) * c = (b + -a) * c from (CommRing.right_distrib b (-a) c).symm]
  exact LinearOrderedField.mul_pos (b + -a) c hab hc

theorem nonneg_mul_nonneg (a b c : Real) (h : 0 ≤ c) : a ≤ b → a * c ≤ b * c := by
  intro hab; rw [nonneg_iff_le] at hab ⊢
  exact nonmul_neg_le a b c h hab

theorem mul_right_lt (a b c : Real) : 0 < c → a < b → a * c < b * c := by
  intro ⟨hc, hnc⟩ ⟨hab, hne⟩
  constructor
  · exact nonneg_mul_nonneg a b c hc hab
  · intro heq; apply hne
    have hcne : c ≠ (0 : Real) := hnc.symm
    calc a = a * c * Field.inv c := by
          rw [mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]
      _ = b * c * Field.inv c := by rw [heq]
      _ = b := by rw [mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]

theorem zero_lt_one : (0 : Real) < 1 := by
  cases LinearOrderedField.le_total (0 : Real) 1 with
  | inl h => exact ⟨h, fun heq => Field.nontrivial heq⟩
  | inr h =>
    have h0 : (0 : Real) ≤ -1 := neg_neg_nonneg 1 h
    have h1 : (0 : Real) ≤ (-1) * (-1) := LinearOrderedField.mul_pos (-1) (-1) h0 h0
    have h2 : (-1 : Real) * (-1) = 1 := by
      calc (-1 : Real) * (-1) = -(1 * (-1)) := neg_mul 1 (-1)
        _ = -(-(1 * 1)) := by rw [mul_neg]
        _ = 1 * 1 := neg_neg _
        _ = 1 := one_mul_b 1
    rw [h2] at h1
    exact absurd (LinearOrderedField.le_asymm (0 : Real) (1 : Real) h1 h) Field.nontrivial

theorem zero_lt_two : (0 : Real) < 2 := by
  have h1 := add_left_lt 1 0 1 zero_lt_one
  rw [add_zero'] at h1
  exact lt_trans 0 1 (1 + 1) zero_lt_one h1

theorem two_ne_zero : (2 : Real) ≠ 0 := zero_lt_two.2.symm

-- ============================================================
-- §5. Inverse positivity
-- ============================================================

theorem pos_inv (b : Real) (hb : 0 < b) : 0 < Field.inv b := by
  have hbne : b ≠ (0 : Real) := hb.2.symm
  constructor
  · cases LinearOrderedField.le_total (0 : Real) (Field.inv b) with
    | inl h => exact h
    | inr h =>
      exfalso
      have h0 : (0 : Real) ≤ -(Field.inv b) := neg_neg_nonneg _ h
      have h1 : (0 : Real) ≤ b * -(Field.inv b) :=
        LinearOrderedField.mul_pos b (-(Field.inv b)) hb.1 h0
      rw [mul_neg, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne] at h1
      have h2 : (1 : Real) ≤ 0 := by
        have := LinearOrderedField.add_le_add (0 : Real) (-(1 : Real)) (1 : Real) h1
        rw [zero_add', neg_add'] at this; exact this
      exact zero_lt_one.2 (LinearOrderedField.le_asymm (0 : Real) (1 : Real) zero_lt_one.1 h2)
  · intro h
    exact Field.nontrivial (show (0 : Real) = 1 from by
      calc (0 : Real) = b * 0 := (mul_zero' b).symm
        _ = b * Field.inv b := by rw [h]
        _ = 1 := Field.mul_inv b hbne)

theorem nonneg_inv (b : Real) (hb : 0 ≤ b) (hbne : b ≠ 0) : 0 ≤ Field.inv b :=
  (pos_inv b ⟨hb, hbne.symm⟩).1

-- ============================================================
-- §6. Division theorems
-- ============================================================

theorem pos_mul_pos (a b : Real) : 0 < a → 0 < b → 0 < a * b := by
  intro ha hb
  exact ⟨LinearOrderedField.mul_pos a b ha.1 hb.1, fun h =>
    ha.2 (by
      calc (0 : Real) = 0 * Field.inv b := (zero_mul_r _).symm
        _ = (a * b) * Field.inv b := by rw [h]
        _ = a * (b * Field.inv b) := mul_assoc _ _ _
        _ = a * 1 := by rw [show b * Field.inv b = (1 : Real) from Field.mul_inv b hb.2.symm]
        _ = a := mul_one_b a)⟩

theorem mul_div_cancel (a b : Real) (hb : b ≠ (0 : Real)) : a * b / b = a := by
  show a * b * Field.inv b = a
  rw [mul_assoc, show b * Field.inv b = (1 : Real) from Field.mul_inv b hb, mul_one_b]

theorem mul_div_cancel' (a b : Real) (ha : a ≠ (0 : Real)) : a * b / a = b := by
  show a * b * Field.inv a = b
  calc a * b * Field.inv a = b * a * Field.inv a := by rw [mul_comm a b]
    _ = b * (a * Field.inv a) := mul_assoc b a (Field.inv a)
    _ = b * 1 := by rw [show a * Field.inv a = (1 : Real) from Field.mul_inv a ha]
    _ = b := mul_one_b b

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by
  show a * Field.inv c + -(b * Field.inv c) = (a + -b) * Field.inv c
  rw [show -(b * Field.inv c) = (-b) * Field.inv c from by rw [neg_mul]]
  exact (CommRing.right_distrib a (-b) (Field.inv c)).symm

theorem half_add (a : Real) : a / 2 + a / 2 = a := by
  show a * Field.inv (2 : Real) + a * Field.inv (2 : Real) = a
  rw [← CommRing.left_distrib]
  suffices h : Field.inv (2 : Real) + Field.inv (2 : Real) = (1 : Real) by rw [h, mul_one_b]
  have h1 : ((1 : Real) + 1) * Field.inv (2 : Real) = (1 : Real) := Field.mul_inv 2 two_ne_zero
  rw [CommRing.right_distrib, one_mul_b] at h1; exact h1

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / 2 :=
  pos_mul_pos a (Field.inv 2) h (pos_inv 2 zero_lt_two)

theorem pos_div_pos (a b : Real) : 0 < a → 0 < b → 0 < a / b :=
  fun ha hb => pos_mul_pos a (Field.inv b) ha (pos_inv b hb)

theorem nonneg_div_nonneg (a b : Real) : 0 ≤ a → 0 < b → 0 ≤ a / b :=
  fun ha hb => LinearOrderedField.mul_pos a (Field.inv b) ha (pos_inv b hb).1

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c :=
  fun hc hab => mul_right_lt a b (Field.inv c) (pos_inv c hc) hab

theorem div_right_le (a b c : Real) : 0 ≤ c → a ≤ b → a / c ≤ b / c := by
  intro hc hab
  cases Classical.em (c = 0) with
  | inl heq =>
    show a * Field.inv c ≤ b * Field.inv c
    have hinv : Field.inv c = (0 : Real) := by rw [heq]; exact Real.inv_zero
    rw [hinv, mul_zero', mul_zero']; exact le_refl 0
  | inr hne => exact nonneg_mul_nonneg a b (Field.inv c) (nonneg_inv c hc hne) hab

-- ============================================================
-- §7. More order
-- ============================================================

theorem aux (a b c : Real) (hc : c ≠ (0 : Real)) : a * (b + c - b) / c = a := by
  rw [add_sub_cancel b c]; exact mul_div_cancel a c hc

theorem div_lt_iff (a b c : Real) (bpos : 0 < b) (cpos : 0 < c) : a / b < c ↔ a / c < b := by
  have hbne := bpos.2.symm
  have hcne := cpos.2.symm
  constructor
  · intro h
    -- a * inv b < c → (a * inv b) * b < c * b → a < c * b
    have h1 := mul_right_lt (a * Field.inv b) c b bpos h
    rw [mul_assoc, show Field.inv b * b = (1 : Real) from Field.inv_mul b hbne,
        mul_one_b] at h1
    -- a < c * b → a * inv c < c * b * inv c = b
    have h2 := mul_right_lt a (c * b) (Field.inv c) (pos_inv c cpos) h1
    rw [show c * b = b * c from mul_comm c b,
        mul_assoc, show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne,
        mul_one_b] at h2
    exact h2
  · intro h
    have h1 := mul_right_lt (a * Field.inv c) b c cpos h
    rw [mul_assoc, show Field.inv c * c = (1 : Real) from Field.inv_mul c hcne,
        mul_one_b] at h1
    have h2 := mul_right_lt a (b * c) (Field.inv b) (pos_inv b bpos) h1
    rw [show b * c = c * b from mul_comm b c,
        mul_assoc, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne,
        mul_one_b] at h2
    exact h2

-- 乗法・除法
theorem mul_le_mul_left (c x y : Real) (hc : 0 ≤ c) (h : x ≤ y) : c * x ≤ c * y := by
  rw [mul_comm c x, mul_comm c y]
  exact nonneg_mul_nonneg x y c hc h

theorem mul_div_assoc (a b c : Real) : a * b / c = a * (b / c) := by
  show a * b * Field.inv c = a * (b * Field.inv c)
  exact mul_assoc a b (Field.inv c)

theorem div_mul_cancel' (a b : Real) (hb : b ≠ 0) : a / b * b = a := by
  show a * Field.inv b * b = a
  rw [mul_assoc, Field.inv_mul b hb, MulCommMonoid.mul_one]

theorem div_add_div (a b c : Real) : a / c + b / c = (a + b) / c := by
  show a * Field.inv c + b * Field.inv c = (a + b) * Field.inv c
  exact (add_mul a b (Field.inv c)).symm

theorem neg_div (a b : Real) : -a / b = -(a / b) := by
  show -a * Field.inv b = -(a * Field.inv b)
  exact neg_mul a (Field.inv b)

theorem half_lt {ε : Real} (hε : 0 < ε) : ε / 2 < ε := by
  have h1 := add_left_lt (ε / 2) 0 (ε / 2) (pos_half ε hε)
  rw [add_zero] at h1; rw [half_add] at h1; exact h1

-- ε-論法
theorem le_of_forall_le_add {A B : Real} (h : ∀ γ, 0 < γ → A ≤ B + γ) : A ≤ B := by
  cases LinearOrderedField.le_total A B with
  | inl hle => exact hle
  | inr hge =>
    cases Classical.em (A = B) with
    | inl heq => rw [heq]; exact le_refl B
    | inr hne =>
      exfalso
      have hBA : B < A := ⟨hge, fun h0 => hne h0.symm⟩
      have hpos : 0 < A - B := (pos_iff_lt B A).mp hBA
      have h1 := h ((A - B) / 2) (pos_half _ hpos)
      have h2 : B + (A - B) / 2 < B + (A - B) := add_left_lt B _ _ (half_lt hpos)
      rw [add_sub_cancel' B A] at h2
      exact (le_lt_trans h1 h2).2 rfl
