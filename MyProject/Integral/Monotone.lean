import MyProject.Integral.Linearity
import MyProject.Integral.Interval

noncomputable section

open Real Classical

-- 積分の単調性

-- 極限の単調性を使いたい

theorem add_left_le (a b c : Real) : b ≤ c → a + b ≤ a + c := by sorry

theorem div_right_le (a b c : Real) : 0 ≤ c → a ≤ b → a / c ≤  b / c := by sorry

theorem ceil_nonneg (a : Real) : (0 : Real) ≤ ↑(ceil a) := by sorry

theorem nonneg_mul_nonneg (a b c : Real) (h : 0 ≤ c) : a ≤ b → a * c ≤ b * c := by sorry

theorem nonneg_sub_iff (a b : Real) : a ≤ b ↔ 0 ≤ b - a := by sorry

theorem cast_lt (a b : Nat) : a < b → (a : Real) < b := by sorry

theorem le_lt_trans' (a b c : Real) : a ≤ b → b < c → a < c := by sorry

theorem nonneg_div_nonneg (a b : Real) : 0 ≤ a → 0 < b → 0 ≤ a / b := by sorry

theorem integral_nonneg (f : Real → Real) (a b : Real)
    (h : a ≤ b) (h' : ∀ x, InInterval a b x → 0 ≤ f x)
    (h'' : IsIntegrable f a b) : 0 ≤ Integral f a b := by
  rcases h'' with ⟨i, h''⟩
  have h₀ : 0 ≤ i := by
    rw [IsIntegral] at h''
    false_or_by_contra
    rename_i h₁
    have : i < 0 := by apply ne_le_lt; exact h₁
    let ε := -i
    have εpos : 0 < ε := by dsimp [ε]; exact neg_neg_pos i this
    rcases h'' ε εpos with ⟨δ, hδ⟩
    let n := ceil ((b - a) / δ)
    let Δ : Partition n a b := by
      apply Partition.mk (fun i => a + i.val * (b - a) / n)
      · intro i
        apply add_left_le
        apply div_right_le
        dsimp [n]
        apply ceil_nonneg
        apply nonneg_mul_nonneg
        rw [← nonneg_sub_iff]
        exact h
        apply le_of_lt
        apply cast_lt
        apply incl_lt_addone
      · rw [zero_val, zero_mul', zero_div, add_zero]
      · rw [range_val n n, mul_div_cancel',add_sub_cancel']
    let ξ : Range n → Real := fun i => Δ.points (incl i)
    have h₁ : Δ.IsRepr a b n ξ := by
      intro i
      constructor
      apply le_refl
      apply Δ.increase
    have h₂ : Partition.diam n a b Δ < δ := by
      apply fmax'_lt
      intro i
      dsimp [Partition.length]
      rw [add_sub_add', div_sub_div, mul_sub_mul]
      rw [cast_incl_val, cast_addone_val]
      rw [add_sub_cancel, one_mul]
      have : (b - a) / δ < n := by
        apply ceil_lt
      rw [div_lt_iff]
      · exact this
      · apply le_lt_trans' _ _ _ _ this
        apply nonneg_div_nonneg
        rw [← nonneg_sub_iff]
        exact h
        exact hδ.1
      · exact hδ.1
    have h₃ : abs (RiemannSum f a b n Δ ξ - i) < ε := by
      apply hδ.2
      exact h₁
      exact h₂
    have h₄ : 0 ≤ RiemannSum f a b n Δ ξ := by
      apply RiemannSum_nonneg
      exact h'
      exact h₁
    have h₅ : ε ≤ (RiemannSum f a b n Δ ξ - i).abs := by
      dsimp [ε]
      rw [sub_add_neg]
      apply right_le_pos_add_pos
      exact h₄
      apply neg_neg_nonneg
      apply le_of_lt
      exact this
    have h₆ : ε < ε := by exact le_lt_trans h₅ h₃
    have : ε ≠ ε := by apply lt_neq; exact h₆
    exact this rfl
  have h₁ : i = Integral f a b := by
    symm
    rw [← IsIntegral_iff]
    exact h''
  rw [← h₁]
  exact h₀

theorem integral_monotone (f g : Real → Real) (a b : Real)
    (h : a ≤ b) (h' : ∀ x, InInterval a b x → f x ≤ g x)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    Integral f a b ≤ Integral g a b := by
  rw [← le_sub]
  rw [← sub_integral]
  apply integral_nonneg _ _ _ h
  · intro x hx
    rw [le_sub]
    exact h' x hx
  · apply integrable_sub
    exact hf
    exact hg
