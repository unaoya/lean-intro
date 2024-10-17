import MyProject.Real
import MyProject.NatNum
import MyProject.Lemmas
import MyProject.Limit
import MyProject.Integral.Def
import MyProject.Integral.Linearity
import MyProject.Integral.Interval

noncomputable section

open Real Classical

-- 積分の単調性

def ceil (a : Real) : Nat := sorry

theorem ne_le_lt (a b : Real) : ¬a ≤ b → b < a := by
  sorry

theorem neg_neg (a : Real) : -(-a) = a := by
  sorry

theorem neg_neg_pos (a : Real) : a < 0 → 0 < -a := by
  sorry

theorem neg_neg_nonneg (a : Real) : a ≤ 0 → 0 ≤ -a := by
  sorry

theorem zero_val (n : Nat) : (⟨0, sorry⟩ : Range n).val = (0 : Real) := by
  sorry

theorem range_val (n k : Nat) : (⟨k, sorry⟩ : Range n).val = (k : Real) := by
  sorry

theorem zero_mul' (a : Real) : 0 * a = 0 := by
  sorry

theorem zero_div (a : Real) : 0 / a = 0 := by
  sorry

theorem add_zero (a : Real) : a + 0 = a := by
  sorry

theorem lt_neq (a b : Real) : a < b → a ≠ b := by
  sorry

theorem sub_add_neg (a b : Real) : a - b = a + -b := by
  sorry

theorem right_le_pos_add_pos (a b : Real) : 0 ≤ a → 0 ≤ b → b ≤ (a + b).abs := by
  sorry

theorem add_left_lt (a b c : Real) : b < c → a + b < a + c := by
  sorry

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c := by
  sorry

theorem mul_right_lt (a b c : Real) : 0 < c → a < b → a * c < b * c := by
  sorry

theorem pos_ceil_pos (a : Real) : 0 < a → (0 : Real) < ceil a := by
  sorry

theorem pos_sub_iff (a b : Real) : a < b ↔ 0 < b - a := by
  sorry

theorem lt_cast (n m : Nat) : n < m → (n : Real) < m := by
  sorry

theorem incl_lt_addone (n : Nat) (i : Range n) : (incl i).val < (addone i).val := by
  sorry

theorem pos_mul_pos (a b : Real) : 0 < a → 0 < b → 0 < a * b := by
  sorry

theorem zero_lt_two : (0 : Real) < 2 := by
  sorry

theorem mul_div_cancel' (a b : Real) : a * b / a = b := by
  sorry

theorem add_sub_cancel' (a b : Real) : a + (b - a) = b := by
  sorry

theorem le_refl (a : Real) : a ≤ a := by
  sorry

theorem add_sub_add' (a b c : Real) : a + b - (a + c) = (b - c) := by
  sorry

theorem mul_sub_mul (a b c : Real) : a * b - c * b = (a - c) * b := by
  sorry

theorem cast_incl_val (n : Nat) (k : Range n) : ((incl k).val : Real) = (k.val : Real) := by
  sorry

theorem cast_addone_val (n : Nat) (k : Range n) : ((addone k).val : Real) = (k.val : Real) + 1 := by
  sorry

theorem one_mul (a : Real) : 1 * a = a := by
  sorry

theorem ceil_lt (a : Real) : a < ceil a := by
  sorry

theorem div_lt_iff (a b c : Real) (bpos : 0 < b) (cpos : 0 < c) : a / b < c ↔ a / c < b := by
  sorry

theorem lt_trans (a b c : Real) : a < b → b < c → a < c := by
  sorry

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
    have h₁ : IsRepr a b n Δ ξ := by
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
    have h₆ : ε < ε := by exact le_lt_trans ε (RiemannSum f a b n Δ ξ - i).abs ε h₅ h₃
    have : ε ≠ ε := by apply lt_neq; exact h₆
    exact this rfl
  have h₁ : i = Integral f a b := by
    symm
    rw [← HasIntegral_iff]
    exact h''
  rw [← h₁]
  exact h₀

theorem integral_monotone (f g : Real → Real) (a b : Real) (h : a < b) (h' : ∀ x, a ≤ x → x ≤ b → f x ≤ g x) (h'' : ∃ i, HasIntegral f a b i) :
  Integral f a b ≤ Integral g a b := by
  rw [← le_sub]
  rw [← sub_integral]
  apply integral_nonneg _ _ _ h
  intro x ha hb
  rw [le_sub]
  exact h' x ha hb
  sorry
