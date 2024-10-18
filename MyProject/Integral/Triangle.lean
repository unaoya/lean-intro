import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 三角不等式

theorem int_triangle_ineq (f : Real → Real) (a b : Real) (h : a < b) (h'' : ∃ i, HasIntegral f a b i) :
  abs (Integral f a b) ≤ Integral (fun x ↦ abs (f x)) a b := by
  apply abs_le
  sorry
  sorry
  -- · rw [← neg_integral]
  --   have h₁ : ∀ x, a ≤ x → x ≤ b → -f x ≤ abs (f x) := fun x _ _ ↦ neg_le_abs (f x)
  --   apply integral_monotone (fun x ↦ -(f x)) (fun x ↦ abs (f x)) a b h h₁
  -- · have h₀ : ∀ x, a ≤ x → x ≤ b → f x ≤ abs (f x) := fun x _ _ ↦ le_abs (f x)
  --   apply integral_monotone f (fun x ↦ abs (f x)) a b h h₀

theorem oint_triangle_ineq (f : Real → Real) (a b : Real) (h'' : ∃ i, HasIntegral f a b i) :
  abs (Integral f a b) ≤ abs (Integral (fun x ↦ abs (f x)) a b) := by
  -- apply abs_le
  -- · rw [← neg_integral]
  --   have h₁ : ∀ x, a ≤ x → x ≤ b → -f x ≤ abs (f x) := fun x _ _ ↦ neg_le_abs (f x)
  --   apply integral_monotone (fun x ↦ -(f x)) (fun x ↦ abs (f x)) a b h h₁
  -- · have h₀ : ∀ x, a ≤ x → x ≤ b → f x ≤ abs (f x) := fun x _ _ ↦ le_abs (f x)
  --   apply integral_monotone f (fun x ↦ abs (f x)) a b h h₀
  sorry
