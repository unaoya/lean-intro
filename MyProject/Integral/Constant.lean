import MyProject.Real
import MyProject.NatNum
import MyProject.Lemmas
import MyProject.Limit
import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 定数関数の積分

theorem const_integral (c a b : Real) : Integral (fun _ ↦ c) a b = c * (b - a) := by
  rw [← HasIntegral_iff]
  intro ε hε
  apply Exists.intro 1
  constructor
  · exact zero_lt_one
  · intros n Δ ξ _ _
    rw [const_riemann_sum]
    rw [sub_self]
    rw [abs_zero]
    exact hε
