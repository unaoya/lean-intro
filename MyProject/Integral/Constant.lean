import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 定数関数の積分

theorem const_has_integral (c a b : Real) (_ : a ≤ b) : IsIntegral (fun _ ↦ c) a b (c * (b - a)) := by
  intro ε hε
  apply Exists.intro 1
  constructor
  · exact zero_lt_one
  · intros n Δ ξ _ _
    rw [const_riemann_sum, sub_self, abs_zero]
    exact hε

theorem const_integral (c a b : Real) (h : a ≤ b) : Integral (fun _ ↦ c) a b = c * (b - a) := by
  exact (IsIntegral_iff _ _ _ _).1 (const_has_integral c a b h)
