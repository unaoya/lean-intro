import MyProject.Real.Div

noncomputable section

open Real Classical

-- 絶対値

theorem le_abs (a : Real) : a ≤ abs a := by
  show a ≤ (if a ≤ -a then -a else a); split
  · rename_i h; exact h
  · exact le_refl a

theorem neg_le_abs (a : Real) : -a ≤ abs a := by
  show -a ≤ (if a ≤ -a then -a else a); split
  · exact le_refl (-a)
  · rename_i h; exact (ne_le_lt a (-a) h).1

theorem abs_le (a b : Real) (h₀ : -a ≤ b) (h₁ : a ≤ b) : abs a ≤ b := by
  show (if a ≤ -a then -a else a) ≤ b; split <;> assumption

theorem abs_zero : (0 : Real).abs = 0 := by
  show (if (0 : Real) ≤ -(0 : Real) then -(0 : Real) else (0 : Real)) = 0
  rw [neg_zero, if_pos (le_refl (0 : Real))]

theorem pos_abs {x : Real} (h : 0 < x) : x.abs = x := by
  show (if x ≤ -x then -x else x) = x
  have hneg_le : -x ≤ 0 := by
    have := LinearOrderedField.add_le_add (0 : Real) x (-x) h.1
    rw [zero_add', add_neg'] at this; exact this
  rw [if_neg (fun hle => h.2 (LinearOrderedField.le_asymm (0 : Real) x h.1
    (LinearOrderedField.le_trans x (-x) 0 hle hneg_le)))]

theorem nonneg_abs {x : Real} (hx : 0 ≤ x) : x.abs = x := by
  cases Classical.em (x = 0) with
  | inl heq => rw [heq]; exact abs_zero
  | inr hne => exact pos_abs ⟨hx, fun h => hne h.symm⟩

theorem nonpos_abs {x : Real} (hx : x ≤ 0) : x.abs = -x := by
  show (if x ≤ -x then -x else x) = -x
  rw [if_pos (LinearOrderedField.le_trans x 0 (-x) hx (neg_neg_nonneg x hx))]

theorem abs_nonneg {x : Real} : 0 ≤ x.abs := by
  cases LinearOrderedField.le_total (0 : Real) x with
  | inl h => exact LinearOrderedField.le_trans 0 x x.abs h (le_abs x)
  | inr h => exact LinearOrderedField.le_trans 0 (-x) x.abs (neg_neg_nonneg x h) (neg_le_abs x)

theorem abs_neg (z : Real) : Real.abs (-z) = Real.abs z := by
  show (if -z ≤ -(-z) then -(-z) else -z) = (if z ≤ -z then -z else z)
  rw [neg_neg]
  cases Classical.em (z ≤ -z) with
  | inl h =>
    rw [if_pos h]
    cases Classical.em (-z ≤ z) with
    | inl h' => rw [if_pos h']; exact LinearOrderedField.le_asymm z (-z) h h'
    | inr h' => rw [if_neg h']
  | inr h =>
    rw [if_neg h]
    rw [if_pos (by cases LinearOrderedField.le_total z (-z) with
      | inl h' => exact absurd h' h
      | inr h' => exact h')]

theorem abs_triangle (a b : Real) : abs (a + b) ≤ abs a + abs b := by
  apply abs_le
  · -- -(a+b) ≤ abs a + abs b
    rw [show -(a + b) = -a + -b from neg_add_distrib a b]
    exact LinearOrderedField.le_trans _ _ _
      (LinearOrderedField.add_le_add (-a) (Real.abs a) (-b) (neg_le_abs a))
      (add_left_le (Real.abs a) (-b) (Real.abs b) (neg_le_abs b))
  · exact LinearOrderedField.le_trans _ _ _
      (LinearOrderedField.add_le_add a (Real.abs a) b (le_abs a))
      (add_left_le (Real.abs a) b (Real.abs b) (le_abs b))

theorem neg_sub_neg_abs (a b : Real) : abs (-a - -b) = abs (a - b) := by
  show Real.abs (-a + -(-b)) = Real.abs (a + -b)
  rw [neg_neg]
  have h : -a + b = -(a + -b) := by
    rw [show -(a + -b) = -a + -(-b) from neg_add_distrib a (-b), neg_neg]
  rw [h, abs_neg]

@[simp]

theorem sub_zero_abs (x : Real) : (x - 0).abs = x.abs := by
  show Real.abs (x + -(0 : Real)) = Real.abs x
  rw [neg_zero, add_zero']

-- abs multiplicativity for nonneg right factor
theorem abs_mul_nonneg {x y : Real} (hy : 0 ≤ y) : Real.abs (x * y) = Real.abs x * y := by
  cases Classical.em (y = 0) with
  | inl heq => rw [heq, mul_zero', abs_zero, mul_zero']
  | inr hyne =>
    cases LinearOrderedField.le_total (0 : Real) x with
    | inl hx => rw [nonneg_abs (LinearOrderedField.mul_pos x y hx hy), nonneg_abs hx]
    | inr hx =>
      have hnx : (0 : Real) ≤ -x := neg_neg_nonneg x hx
      have hxy_neg : x * y ≤ 0 := by
        have h1 : (0 : Real) ≤ (-x) * y := LinearOrderedField.mul_pos (-x) y hnx hy
        rw [neg_mul] at h1
        have := LinearOrderedField.add_le_add (0 : Real) (-(x * y)) (x * y) h1
        rw [zero_add', neg_add'] at this; exact this
      rw [nonpos_abs hxy_neg, nonpos_abs hx, neg_mul]

-- Full abs_mul
theorem abs_mul' (x y : Real) : Real.abs (x * y) = Real.abs x * Real.abs y := by
  cases LinearOrderedField.le_total (0 : Real) y with
  | inl hy => rw [abs_mul_nonneg hy, nonneg_abs hy]
  | inr hy =>
    have hny : (0 : Real) ≤ -y := neg_neg_nonneg y hy
    rw [show x * y = -(x * (-y)) from by rw [mul_neg, neg_neg],
        abs_neg, abs_mul_nonneg hny, nonpos_abs hy]

theorem div_abs_le {a b c : Real} (h : a.abs ≤ b.abs) : (a / c).abs ≤ (b / c).abs := by
  show Real.abs (a * Field.inv c) ≤ Real.abs (b * Field.inv c)
  rw [abs_mul' a (Field.inv c), abs_mul' b (Field.inv c)]
  exact nonneg_mul_nonneg (Real.abs a) (Real.abs b) (Real.abs (Field.inv c)) abs_nonneg h

-- Reverse triangle inequality: ||a| - |b|| ≤ |a - b|
theorem abs_sub_abs_le (a b : Real) : (a.abs - b.abs).abs ≤ (a - b).abs := by
  apply abs_le
  · -- -(|a| - |b|) = |b| - |a| ≤ |a - b|
    have h1 : b.abs ≤ (b - a).abs + a.abs := by
      calc b.abs = ((b - a) + a).abs := by
            congr 1; show b = (b + -a) + a
            rw [add_assoc, AddCommGroup.neg_add, AddCommGroup.add_zero]
        _ ≤ (b - a).abs + a.abs := abs_triangle (b - a) a
    have h2 : b.abs - a.abs ≤ (b - a).abs := by
      have h1' := LinearOrderedField.add_le_add _ _ (-a.abs) h1
      rw [show (b - a).abs + a.abs + -a.abs = (b - a).abs from by
        rw [add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1'
      exact h1'
    have h3 : -(a.abs - b.abs) = b.abs - a.abs := by
      show -(a.abs + -b.abs) = b.abs + -a.abs
      rw [neg_add_distrib, neg_neg, add_comm]
    rw [h3]
    calc b.abs - a.abs ≤ (b - a).abs := h2
      _ = (a - b).abs := by
        have : b - a = -(a - b) := by
          show b + -a = -(a + -b)
          rw [neg_add_distrib, neg_neg, add_comm]
        rw [this, abs_neg]
  · -- |a| - |b| ≤ |a - b|
    have h1 : a.abs ≤ (a - b).abs + b.abs := by
      calc a.abs = ((a - b) + b).abs := by
            congr 1; show a = (a + -b) + b
            rw [add_assoc, AddCommGroup.neg_add, AddCommGroup.add_zero]
        _ ≤ (a - b).abs + b.abs := abs_triangle (a - b) b
    have h1' := LinearOrderedField.add_le_add _ _ (-b.abs) h1
    rw [show (a - b).abs + b.abs + -b.abs = (a - b).abs from by
      rw [add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1'
    exact h1'

-- ============================================================
-- §9. Summation
-- ============================================================

theorem nez_of_abs_pos {x : Real} (h : 0 < x.abs) : x ≠ 0 := by
  intro heq; rw [heq, abs_zero] at h; exact h.2 rfl

theorem right_le_pos_add_pos (a b : Real) : 0 ≤ a → 0 ≤ b → b ≤ (a + b).abs := by
  intro ha _
  exact LinearOrderedField.le_trans b (a + b) (a + b).abs
    (by have := LinearOrderedField.add_le_add (0 : Real) a b ha; rw [zero_add'] at this; exact this)
    (le_abs (a + b))

-- ============================================================
-- §13. NatCast
-- ============================================================

-- 絶対値
theorem abs_sub_comm (a b : Real) : (a - b).abs = (b - a).abs := by
  rw [← neg_sub a b, abs_neg]

theorem abs_sub_le_add (x y z : Real) : (x - z).abs ≤ (x - y).abs + (y - z).abs := by
  calc (x - z).abs
      = ((y - z) + (x - y)).abs := by rw [telescope_2 z x y]
    _ ≤ (y - z).abs + (x - y).abs := abs_triangle _ _
    _ = (x - y).abs + (y - z).abs := add_comm _ _

theorem abs_sub_le_of_mem {P Q s t : Real}
    (hsP : P ≤ s) (hsQ : s ≤ Q) (htP : P ≤ t) (htQ : t ≤ Q) :
    (s - t).abs ≤ Q - P := by
  have hnegt : -t ≤ -P := neg_le_swap (show -(-P) ≤ t from by rw [neg_neg]; exact htP)
  have hnegs : -s ≤ -P := neg_le_swap (show -(-P) ≤ s from by rw [neg_neg]; exact hsP)
  apply abs_le
  · rw [neg_sub]
    exact le_trans (LinearOrderedField.add_le_add t Q (-s) htQ) (add_left_le Q _ _ hnegs)
  · exact le_trans (LinearOrderedField.add_le_add s Q (-t) hsQ) (add_left_le Q _ _ hnegt)
