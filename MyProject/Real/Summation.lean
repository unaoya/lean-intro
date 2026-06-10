import MyProject.Real.MinMax

noncomputable section

open Real Classical
open Range

-- 有限和 Summation とその性質

-- ============================================================
-- §0. Bridge lemmas
-- ============================================================

theorem summation_smul (n : Nat) (f : Range n → Real) (c : Real) :
  Summation n (fun i ↦ c * f i) = c * Summation n f := by
  induction n with
  | zero => simp [Summation]; exact (mul_zero' c).symm
  | succ n ih =>
    simp only [Summation] at ih ⊢
    rw [ih]; exact (CommRing.left_distrib c _ _).symm

theorem add_four_comm (a b c d : Real) : (a + b) + (c + d) = (a + c) + (b + d) := by
  ac_rfl

theorem additive_summation (n : Nat) (f g : Range n → Real) :
  Summation n (fun i ↦ f i + g i) = Summation n f + Summation n g := by
  induction n with
  | zero => simp [Summation]; exact (zero_add' 0).symm
  | succ n ih =>
    simp only [Summation] at ih ⊢
    rw [ih]
    exact add_four_comm _ _ _ _

theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
  Summation n f = Summation n g := congrArg _ (funext h)

theorem neg_summation (n : Nat) (f : Range n → Real) :
  -Summation n f = Summation n (fun i ↦ -f i) := by
  induction n with
  | zero => simp [Summation]; exact neg_zero
  | succ n ih => simp only [Summation]; rw [neg_add_distrib, ih]

theorem summation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
  0 ≤ Summation n f := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    simp only [Summation]
    let f' : Range n → Real := fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩
    have h1 : (0 : Real) ≤ Summation n f' :=
      ih f' (fun i => h ⟨i.val, Nat.lt_of_lt_of_le i.property (Nat.le_succ n)⟩)
    have h2 := h ⟨n, Nat.lt_add_one n⟩
    have h3 := LinearOrderedField.add_le_add (0 : Real) (Summation n f') (0 : Real) h1
    rw [add_zero'] at h3
    exact LinearOrderedField.le_trans _ _ _ h3 (add_left_le _ 0 _ h2)

theorem summation_le (n : Nat) (f g : Range n → Real) (h : ∀ i, f i ≤ g i) :
    Summation n f ≤ Summation n g := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    simp only [Summation]
    let f' : Range n → Real := fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩
    let g' : Range n → Real := fun k => g ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩
    have ih' : Summation n f' ≤ Summation n g' :=
      ih f' g' (fun i => h ⟨i.val, Nat.lt_of_lt_of_le i.property (Nat.le_succ n)⟩)
    have hn := h ⟨n, Nat.lt_add_one n⟩
    exact le_trans
      (LinearOrderedField.add_le_add _ _ (f ⟨n, Nat.lt_add_one n⟩) ih')
      (add_left_le (Summation n g') _ _ hn)

-- ============================================================
-- §10. fmax'
-- ============================================================

theorem summation_zero (f : Range 0 → Real) : Summation 0 f = 0 := rfl

theorem summation_succ (n : Nat) (f : Range n.succ → Real) :
  Summation n.succ f = Summation n (fun i ↦ f (incl i)) + f ⟨n, by exact Nat.lt_add_one n⟩ := rfl

theorem telescope_sum (n : Nat) (f : Range n.succ → Real) :
  Summation n (fun i ↦ f (addone i) - f (incl i)) = f ⟨n, by exact Nat.lt_add_one n⟩ - f ⟨0, by simp⟩ :=
  match n with
  | Nat.zero => by rw [summation_zero, sub_self]
  | Nat.succ n => by
    rw [summation_succ]
    let f' : Range n.succ → Real := fun i => f (incl i)
    have (i : Range n) : addone (incl i) = incl (addone i) := by rw [addone_incl_comm n i]
    have : (fun i ↦ f (addone (incl i)) - f (incl (incl i))) = fun i ↦ f (incl (addone i)) - f (incl (incl i)) := by
      apply funext; intro i; rw [this]
    rw [this, telescope_sum n f']
    dsimp [f']
    rw [← telescope_2]; rfl

-- Σ of zero function = 0
theorem summation_all_zero (n : Nat) : Summation n (fun _ : Range n => (0 : Real)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Summation m (fun _ : Range m => (0 : Real)) + (0 : Real) = 0
    rw [ih, zero_add']

-- Σ of function nonzero at one point = that value
theorem summation_one_term (m : Nat) (k : Range m) (h : Range m → Real)
    (hzero : ∀ i : Range m, i.val ≠ k.val → h i = 0) :
    Summation m h = h k := by
  induction m with
  | zero => exact absurd k.property (Nat.not_lt_zero _)
  | succ n ih =>
    rw [summation_succ]
    by_cases hkn : k.val = n
    · -- k is the last element: all incl terms are 0
      have hall : ∀ i : Range n, h (incl i) = 0 := by
        intro i; apply hzero; show (incl i).val ≠ k.val
        have := i.property; simp only [incl_val]; omega
      rw [summation_congr n _ _ hall, summation_all_zero, zero_add']
      have : (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) = k := Subtype.ext hkn.symm
      rw [this]
    · -- k.val < n: last term is 0
      have hklt : k.val < n := by have := k.property; omega
      have hlast : h ⟨n, Nat.lt_succ_self n⟩ = 0 := by
        apply hzero; show n ≠ k.val; omega
      rw [hlast, add_zero]
      have h_ih := ih ⟨k.val, hklt⟩ (fun i => h (incl i)) (by
        intro i hne; apply hzero (incl i)
        show (incl i).val ≠ k.val; simp only [incl_val]; exact hne)
      rw [h_ih]; rfl

-- k番目の項を2つに分割しても和は変わらない
theorem summation_split_term (n : Nat) (k : Range n) (f : Range n → Real)
    (g : Range (n + 1) → Real)
    (h_low : ∀ (i : Range (n + 1)) (hi : i.val < k.val),
      g i = f ⟨i.val, Nat.lt_trans hi k.property⟩)
    (h_split : g ⟨k.val, Nat.lt_succ_of_lt k.property⟩ +
      g ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ = f k)
    (h_high : ∀ (i : Range (n + 1)) (hi : k.val + 1 < i.val),
      g i = f ⟨i.val - 1, by have := i.property; omega⟩) :
    Summation (n + 1) g = Summation n f := by
  induction n with
  | zero => exact absurd k.property (Nat.not_lt_zero _)
  | succ n ih =>
    have hk := k.property  -- k.val < n + 1
    rw [summation_succ, summation_succ]
    by_cases hkn : k.val = n
    · -- k is last: rewrite h_split to match the goal
      rw [summation_succ]
      have hcongr : ∀ i : Range n, g (incl (incl i)) = f (incl i) := by
        intro i; have := i.property
        exact h_low (incl (incl i)) (by simp only [incl_val]; omega)
      rw [summation_congr n _ _ hcongr, add_assoc]; congr 1
      -- Goal: g (incl ⟨n, _⟩) + g ⟨n+1, _⟩ = f ⟨n, _⟩
      -- h_split: g ⟨k.val, _⟩ + g ⟨k.val+1, _⟩ = f k
      have e1 : (⟨k.val, Nat.lt_succ_of_lt k.property⟩ : Range (n + 2)) =
                 incl (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) :=
        Subtype.ext (by simp [incl_val]; omega)
      have e2 : (⟨k.val + 1, Nat.succ_lt_succ k.property⟩ : Range (n + 2)) =
                 (⟨n + 1, by omega⟩ : Range (n + 2)) :=
        Subtype.ext (by show k.val + 1 = n + 1; omega)
      have e3 : k = (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) :=
        Subtype.ext hkn
      rw [e1, e2, e3] at h_split; exact h_split
    · -- k < n: last terms match
      have hklt : k.val < n := by omega
      have hlast : g ⟨n + 1, by omega⟩ = f ⟨n, Nat.lt_succ_self n⟩ :=
        h_high ⟨n + 1, by omega⟩ (by show k.val + 1 < n + 1; omega)
      rw [hlast]; congr 1
      exact ih ⟨k.val, hklt⟩ (fun i => f (incl i)) (fun i => g (incl i))
        (fun i hi => h_low (incl i) (by simp only [incl_val]; exact hi))
        h_split
        (fun i hi => h_high (incl i) (by simp only [incl_val]; exact hi))

-- ============================================================
-- §17. 集約補題（Integral 以下の重複 private を統合）
-- ============================================================

theorem abs_summation_le (n : Nat) (h : Range n → Real) :
    (Summation n h).abs ≤ Summation n (fun i => (h i).abs) := by
  induction n with
  | zero =>
    rw [show Summation 0 h = 0 from rfl, abs_zero]
    exact le_refl 0
  | succ m ih =>
    rw [summation_succ m h, summation_succ m (fun i => (h i).abs)]
    apply le_trans (abs_triangle _ _)
    exact LinearOrderedField.add_le_add _ _ _ (ih (fun i => h (Range.incl i)))

theorem sub_summation (n : Nat) (F G : Range n → Real) :
    Summation n F - Summation n G = Summation n (fun i => F i - G i) := by
  calc Summation n F - Summation n G
      = Summation n F + Summation n (fun i => -G i) := by
        show Summation n F + -Summation n G = _
        rw [neg_summation]
    _ = Summation n (fun i => F i + -G i) := (additive_summation n F (fun i => -G i)).symm
    _ = Summation n (fun i => F i - G i) := rfl

-- 総和を前後 2 ブロックに分割
theorem summation_split_at (c d : Nat) (g : Range (c + d) → Real) :
    Summation (c + d) g =
    Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
    Summation d (fun j => g ⟨c + j.val, by have := j.property; omega⟩) := by
  induction d with
  | zero =>
    rw [summation_zero, add_zero]
    apply summation_congr
    intro i
    rfl
  | succ d ih =>
    calc Summation (c + (d + 1)) g
        = Summation (c + d) (fun i => g (Range.incl i)) +
          g ⟨c + d, Nat.lt_succ_self (c + d)⟩ := summation_succ (c + d) g
      _ = (Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
           Summation d (fun j => g ⟨c + j.val, by have := j.property; omega⟩)) +
          g ⟨c + d, Nat.lt_succ_self (c + d)⟩ :=
          congrArg (fun s => s + g ⟨c + d, Nat.lt_succ_self (c + d)⟩)
            (ih (fun i => g (Range.incl i)))
      _ = Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
          (Summation d (fun j => g ⟨c + j.val, by have := j.property; omega⟩) +
           g ⟨c + d, Nat.lt_succ_self (c + d)⟩) := add_assoc _ _ _
      _ = Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
          Summation (d + 1) (fun j => g ⟨c + j.val, by have := j.property; omega⟩) :=
          congrArg (fun s => Summation c (fun i =>
              g ⟨i.val, by have := i.property; omega⟩) + s)
            (summation_succ d (fun j : Range (d + 1) =>
              g ⟨c + j.val, by have := j.property; omega⟩)).symm

-- 総和の先頭 1 項を取り出す
theorem summation_first (m : Nat) (h : Range (m + 1) → Real) :
    Summation (m + 1) h = h ⟨0, Nat.zero_lt_succ m⟩ +
      Summation m (fun j => h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩) := by
  induction m with
  | zero =>
    calc Summation (0 + 1) h
        = Summation 0 (fun i => h (Range.incl i)) + h ⟨0, Nat.zero_lt_succ 0⟩ :=
          summation_succ 0 h
      _ = 0 + h ⟨0, Nat.zero_lt_succ 0⟩ := rfl
      _ = h ⟨0, Nat.zero_lt_succ 0⟩ := AddCommGroup.zero_add _
      _ = h ⟨0, Nat.zero_lt_succ 0⟩ +
          Summation 0 (fun j => h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩) :=
          (add_zero _).symm
  | succ m ih =>
    calc Summation (m + 1 + 1) h
        = Summation (m + 1) (fun i => h (Range.incl i)) +
          h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ := summation_succ (m + 1) h
      _ = (h ⟨0, Nat.zero_lt_succ (m + 1)⟩ +
           Summation m (fun j => h ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt j.property)⟩)) +
          h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ :=
          congrArg (fun s => s + h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
            (ih (fun i => h (Range.incl i)))
      _ = h ⟨0, Nat.zero_lt_succ (m + 1)⟩ +
          (Summation m (fun j => h ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt j.property)⟩) +
           h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) := add_assoc _ _ _
      _ = h ⟨0, Nat.zero_lt_succ (m + 1)⟩ +
          Summation (m + 1) (fun j => h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩) :=
          congrArg (fun s => h ⟨0, Nat.zero_lt_succ (m + 1)⟩ + s)
            (summation_succ m (fun j : Range (m + 1) =>
              h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩)).symm

-- ============================================================
-- §18. 上限の近似
-- ============================================================
