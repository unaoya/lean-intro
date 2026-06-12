-- Text/Proto/Cast.lean — M2: cast 補題・sup の近似・アルキメデス・ceil
import Text.Proto.Lemmas

noncomputable section

open Classical

-- ofNat の定義（| 0 | n+1）により再帰方程式は rfl
theorem succ_ofNat (n : Nat) : Real.ofNat (n + 1) = Real.ofNat n + (1 : Real) := rfl

theorem cast_nonneg (n : Nat) : (0 : Real) ≤ (n : Real) := by
  show (0 : Real) ≤ Real.ofNat n
  induction n with
  | zero => exact le_refl 0
  | succ m ih =>
    rw [succ_ofNat]
    calc (0 : Real) = 0 + 0 := (add_zero' 0).symm
      _ ≤ Real.ofNat m + 0 := add_le_add_right 0 (Real.ofNat m) 0 ih
      _ ≤ Real.ofNat m + 1 := add_left_le _ 0 1 zero_lt_one.1

theorem cast_pos_succ (n : Nat) : (0 : Real) < ((n + 1 : Nat) : Real) := by
  show (0 : Real) < Real.ofNat (n + 1)
  rw [succ_ofNat]
  exact lt_le_trans 0 1 (Real.ofNat n + 1) zero_lt_one
    (by calc (1 : Real) = 0 + 1 := (zero_add' 1).symm
        _ ≤ Real.ofNat n + 1 := add_le_add_right 0 (Real.ofNat n) 1 (cast_nonneg n))

theorem cast_add (n m : Nat) : (n : Real) + (m : Real) = ((n + m : Nat) : Real) := by
  show Real.ofNat n + Real.ofNat m = Real.ofNat (n + m)
  induction m with
  | zero => rw [Nat.add_zero]; exact add_zero' _
  | succ m ih =>
    have eq2 : n + (m + 1) = (n + m) + 1 := Nat.add_succ n m
    rw [succ_ofNat, eq2, succ_ofNat]
    calc Real.ofNat n + (Real.ofNat m + 1)
      = (Real.ofNat n + Real.ofNat m) + 1 := (add_assoc _ _ _).symm
      _ = Real.ofNat (n + m) + 1 := by rw [ih]

theorem cast_lt (a b : Nat) : a < b → (a : Real) < (b : Real) := by
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt h
  have hassoc : a + d + 1 = a + (d + 1) := Nat.add_assoc a d 1
  rw [hd, hassoc]
  have h_eq : ((a + (d + 1) : Nat) : Real) = (a : Real) + ((d + 1 : Nat) : Real) :=
    (cast_add a (d + 1)).symm
  rw [h_eq]
  have hpos : (0 : Real) < ((d + 1 : Nat) : Real) := cast_pos_succ d
  have h1 := add_left_lt (a : Real) 0 ((d + 1 : Nat) : Real) hpos
  rw [add_zero'] at h1; exact h1

theorem cast_le_succ (n : Nat) : (n : Real) ≤ ((n + 1 : Nat) : Real) :=
  le_of_lt (cast_lt n (n + 1) (Nat.lt_succ_self n))

theorem cast_pos_of_ne (m : Nat) (hm : m ≠ 0) : (0 : Real) < (m : Real) := by
  cases m with
  | zero => exact absurd rfl hm
  | succ k => exact cast_pos_succ k

theorem nat_ne_zero_of_nonneg_lt (x : Real) (m : Nat) (hx : 0 ≤ x)
    (hlt : x < (m : Real)) : m ≠ 0 := by
  intro hm; subst hm; exact (le_lt_trans hx hlt).2 rfl

-- ============================================================
-- 上限の近似（sup 公理の初稼働）
-- ============================================================

theorem sup_near (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ B, ∀ x, S x → x ≤ B)
    (γ : Real) (hγ : 0 < γ) : ∃ x, S x ∧ Real.sup S hne hbdd - γ < x := by
  cases Classical.em (∃ x, S x ∧ Real.sup S hne hbdd - γ < x) with
  | inl hex => exact hex
  | inr hnex =>
    exfalso
    have hub : ∀ x, S x → x ≤ Real.sup S hne hbdd - γ := fun x hx =>
      (Classical.em (Real.sup S hne hbdd - γ < x)).elim
        (fun hlt => absurd ⟨x, hx, hlt⟩ hnex) not_lt_imp_le
    have hle := Real.sup_lub S hne hbdd _ hub
    have h1 := add_le_add_right (Real.sup S hne hbdd)
      (Real.sup S hne hbdd - γ) (-(Real.sup S hne hbdd)) hle
    rw [AddCommGroup.add_neg] at h1
    rw [show Real.sup S hne hbdd - γ + -(Real.sup S hne hbdd) = -γ from by
          show Real.sup S hne hbdd + -γ + -(Real.sup S hne hbdd) = -γ
          rw [add_comm (Real.sup S hne hbdd) (-γ),
              add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1
    have h2 : γ ≤ 0 :=
      calc γ = 0 + γ := (AddCommGroup.zero_add γ).symm
        _ ≤ -γ + γ := add_le_add_right 0 (-γ) γ h1
        _ = 0 := AddCommGroup.neg_add γ
    exact hγ.2 (le_antisymm 0 γ hγ.1 h2)

-- ============================================================
-- アルキメデス（上限公理から導かれるため公理ではなく定理）
-- ============================================================

theorem archimedean (a : Real) : ∃ n : Nat, a < (n : Real) := by
  cases Classical.em (∃ n : Nat, a < (n : Real)) with
  | inl h => exact h
  | inr h =>
    exfalso
    have hub : ∀ n : Nat, (n : Real) ≤ a := fun n =>
      not_lt_imp_le (fun hlt => h ⟨n, hlt⟩)
    have hS_ne : ∃ x : Real, ∃ n : Nat, x = (n : Real) := ⟨(0 : Real), 0, rfl⟩
    have hS_bdd : ∃ M, ∀ x : Real, (∃ n : Nat, x = (n : Real)) → x ≤ M :=
      ⟨a, fun x hx => by obtain ⟨n, rfl⟩ := hx; exact hub n⟩
    obtain ⟨x, hxS, hgt⟩ := sup_near _ hS_ne hS_bdd 1 zero_lt_one
    obtain ⟨n, rfl⟩ := hxS
    have h1 : Real.sup _ hS_ne hS_bdd < (1 : Real) + (n : Real) := by
      have h2 := add_left_lt 1 (Real.sup _ hS_ne hS_bdd - 1) (n : Real) hgt
      rwa [add_sub_cancel' 1 (Real.sup _ hS_ne hS_bdd)] at h2
    have h3 : (1 : Real) + (n : Real) = ((n + 1 : Nat) : Real) := by
      rw [add_comm]; exact (succ_ofNat n).symm
    have h4 : ((n + 1 : Nat) : Real) ≤ Real.sup _ hS_ne hS_bdd :=
      Real.sup_ub _ hS_ne hS_bdd _ ⟨n + 1, rfl⟩
    rw [h3] at h1
    exact (lt_le_trans _ _ _ h1 h4).2 rfl

-- ============================================================
-- Nat 述語の最小値と ceil
-- ============================================================

theorem has_min (p : Nat → Prop) (hp : ∃ n, p n) :
    ∃ a, p a ∧ ∀ x, p x → ¬(x < a) := by
  rcases hp with ⟨a, ha⟩
  revert ha
  induction a using Nat.strongRecOn with
  | ind n IH =>
    intro hn
    by_cases h' : ∃ m, m < n ∧ p m
    · rcases h' with ⟨m, hm, hpm⟩
      exact IH m hm hpm
    · exact ⟨n, hn, fun x hpx hxn => h' ⟨x, hxn, hpx⟩⟩

noncomputable def natMin (p : Nat → Prop) (hp : ∃ n, p n) : Nat :=
  Classical.choose (has_min p hp)

noncomputable def ceil (a : Real) : Nat := natMin (fun n => a < (n : Real)) (archimedean a)

theorem ceil_lt (a : Real) : a < ((ceil a : Nat) : Real) :=
  (Classical.choose_spec (has_min (fun n => a < (n : Real)) (archimedean a))).1
