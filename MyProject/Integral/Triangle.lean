import MyProject.Integral.Def
import MyProject.Integral.Linearity
import MyProject.Integral.Monotone

noncomputable section

open Real Classical

-- 三角不等式

theorem int_triangle_ineq (f : Real → Real) (a b : Real) (h : a ≤ b)
    (h'' : IsIntegrable f a b) :
    abs (Integral f a b) ≤ Integral (fun x ↦ abs (f x)) a b := by
  apply abs_le
  · rw [← neg_integral]
    have h₁ : ∀ x, InInterval a b x → -f x ≤ abs (f x) := fun x _ ↦ neg_le_abs (f x)
    apply integral_monotone (fun x ↦ -(f x)) (fun x ↦ abs (f x)) a b h h₁
    apply neg_integrable _ _ _ h h''
    apply abs_integrable _ _ _ h h''
  · have h₀ : ∀ x, InInterval a b x → f x ≤ abs (f x) := fun x _ ↦ le_abs (f x)
    apply integral_monotone f (fun x ↦ abs (f x)) a b h h₀
    exact h''
    apply abs_integrable _ _ _ h h''
