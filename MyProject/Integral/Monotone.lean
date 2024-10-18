import MyProject.Integral.Linearity
import MyProject.Integral.Interval

noncomputable section

open Real Classical

-- 積分の単調性

-- 極限の単調性を使いたい

theorem integral_nonneg (f : Real → Real) (a b : Real) (h : a < b) (h' : ∀ x, a ≤ x → x ≤ b → 0 ≤ f x) (h'' : ∃ i, HasIntegral f a b i) :
  0 ≤ Integral f a b := by
  rcases h'' with ⟨i, h''⟩
  have h₀ : 0 ≤ i := by
    rw [HasIntegral] at h''
    false_or_by_contra
    rename_i h₁
    have : i < 0 := by apply ne_le_lt; exact h₁
    let ε := -i
    have εpos : 0 < ε := by dsimp [ε]; exact neg_neg_pos i this
    rcases h'' ε εpos with ⟨δ, hδ⟩
    let n := ceil ((b - a) / δ)
    let Δ : Partition n a b := by
      apply Partition.mk (fun i => a + i.val * (b - a) / n)
      intro i
      apply add_left_lt
      apply div_right_lt
      dsimp [n]
      apply pos_ceil_pos
      apply pos_mul_pos
      rw [← pos_sub_iff]
      exact h
      exact hδ.1
      apply mul_right_lt
      rw [← pos_sub_iff]
      exact h
      apply lt_cast
      apply incl_lt_addone
      rw [zero_val, zero_mul', zero_div, add_zero]
      rw [range_val n n, mul_div_cancel',add_sub_cancel']
    let ξ : Range n → Real := fun i => Δ.points (incl i)
    have h₁ : Δ.IsRepr a b n ξ := by
      intro i
      constructor
      apply le_refl
      apply le_of_lt
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
      exact this
      apply lt_trans _ _ _ _ this
      apply pos_div_pos
      rw [← pos_sub_iff]
      exact h
      exact hδ.1
      exact hδ.1
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
    rw [← HasIntegral_iff]
    exact h''
  rw [← h₁]
  exact h₀

theorem integral_monotone (f g : Real → Real) (a b : Real)
    (h : a < b) (h' : ∀ x, a ≤ x → x ≤ b → f x ≤ g x)
    (hf : ∃ i, HasIntegral f a b i)
    (hg : ∃ i, HasIntegral f a b i) :
    Integral f a b ≤ Integral g a b := by
  rw [← le_sub]
  rw [← sub_integral]
  apply integral_nonneg _ _ _ h
  intro x ha hb
  rw [le_sub]
  exact h' x ha hb
  apply integrable_sub _ _ _ _ hf hg
