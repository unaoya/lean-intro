import MyProject.Real.Summation

noncomputable section

open Real Classical
open Range

-- 自然数のキャストと ceil

theorem succ_ofNat (n : Nat) : Real.ofNat (n + 1) = Real.ofNat n + (1 : Real) := by
  cases n with
  | zero => show (1 : Real) = (0 : Real) + 1; exact (zero_add' 1).symm
  | succ m => rfl

theorem cast_nonneg (n : Nat) : (0 : Real) ≤ Real.ofNat n := by
  induction n with
  | zero => exact le_refl 0
  | succ m ih =>
    rw [succ_ofNat]
    calc (0 : Real) = 0 + 0 := (add_zero' 0).symm
      _ ≤ Real.ofNat m + 0 := LinearOrderedField.add_le_add 0 (Real.ofNat m) 0 ih
      _ ≤ Real.ofNat m + 1 := add_left_le _ 0 1 zero_lt_one.1

theorem cast_pos_succ (n : Nat) : (0 : Real) < Real.ofNat (n + 1) := by
  rw [succ_ofNat]
  exact lt_le_trans 0 1 (Real.ofNat n + 1) zero_lt_one
    (by calc (1 : Real) = 0 + 1 := (zero_add' 1).symm
        _ ≤ Real.ofNat n + 1 := LinearOrderedField.add_le_add 0 (Real.ofNat n) 1 (cast_nonneg n))

theorem cast_add (n m : Nat) : (Nat.cast : Nat → Real) n + (Nat.cast m) = (Nat.cast (n + m)) := by
  show Real.ofNat n + Real.ofNat m = Real.ofNat (n + m)
  induction m with
  | zero => rw [Nat.add_zero]; exact add_zero' _
  | succ m ih =>
    have eq1 : Real.ofNat m.succ = Real.ofNat m + 1 := succ_ofNat m
    have eq2 : n + m.succ = (n + m).succ := Nat.add_succ n m
    have eq3 : Real.ofNat (n + m).succ = Real.ofNat (n + m) + 1 := succ_ofNat (n + m)
    rw [eq1, eq2, eq3]
    calc Real.ofNat n + (Real.ofNat m + 1)
      = (Real.ofNat n + Real.ofNat m) + 1 := (AddCommGroup.add_assoc _ _ _).symm
      _ = Real.ofNat (n + m) + 1 := by rw [ih]

theorem cast_lt (a b : Nat) : a < b → (a : Real) < b := by
  show a < b → (Real.ofNat a : Real) < Real.ofNat b
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt h
  -- hd : b = a + d + 1, i.e. b = (a + d) + 1
  have hassoc : a + d + 1 = a + (d + 1) := Nat.add_assoc a d 1
  rw [hd, hassoc]
  have h_eq : Real.ofNat (a + (d + 1)) = Real.ofNat a + Real.ofNat (d + 1) :=
    (cast_add a (d + 1)).symm
  rw [h_eq]
  have hpos : (0 : Real) < Real.ofNat (d + 1) := cast_pos_succ d
  have h1 := add_left_lt (Real.ofNat a) 0 (Real.ofNat (d + 1)) hpos
  rw [add_zero'] at h1; exact h1

theorem lt_cast (n m : Nat) : n < m → (n : Real) < m := cast_lt n m

-- ============================================================
-- §14. Ceil
-- ============================================================

def ceil (a : Real) : Nat := min (fun n => a < n) (archimedean a)

theorem ceil_spec (a : Real) :
    a < ↑(ceil a) ∧ ∀ x : Nat, a < ↑x → ¬(x < ceil a) :=
  Classical.choose_spec (has_min (fun n => a < ↑n) (archimedean a))

theorem ceil_lt (a : Real) : a < ↑(ceil a) := (ceil_spec a).1

theorem ceil_nonneg (a : Real) : (0 : Real) ≤ ↑(ceil a) := cast_nonneg (ceil a)

theorem pos_ceil_pos (a : Real) : 0 < a → (0 : Real) < ↑(ceil a) :=
  fun h => lt_trans 0 a ↑(ceil a) h (ceil_lt a)

-- ============================================================
-- §15. Range value theorems
-- ============================================================

theorem zero_val (n : Nat) (hn : 0 < n) : (⟨0, hn⟩ : Range n).val = (0 : Real) := rfl

theorem range_val (n k : Nat) (hk : k < n) : (⟨k, hk⟩ : Range n).val = (k : Real) := rfl

theorem cast_one_mul (x : Real) : (Nat.cast 1) * x = x := by
  show Real.ofNat 1 * x = x; exact one_mul_b x

open Range

theorem cast_incl_val (n : Nat) (k : Range n) : ((incl k).val : Real) = (k.val : Real) := rfl

theorem cast_addone_val (n : Nat) (k : Range n) : ((addone k).val : Real) = (k.val : Real) + 1 := by
  show (Nat.cast (k.val + 1) : Real) = (Nat.cast k.val : Real) + 1
  show Real.ofNat (k.val + 1) = Real.ofNat k.val + 1
  exact succ_ofNat k.val

theorem incl_lt_addone (n : Nat) (i : Range n) : (incl i).val < (addone i).val :=
  Nat.lt_succ_self i.val

-- ============================================================
-- §16. InInterval
-- ============================================================
