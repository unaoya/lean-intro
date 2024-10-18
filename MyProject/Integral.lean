import MyProject.Integral.Constant
import MyProject.Integral.Monotone
import MyProject.Integral.Triangle

-- 向き付き積分を定義し、それらに対する基本定理を示す。

theorem integral_sub_interval (f : Real → Real) (a b c : Real) :
    Integral f a b - Integral f a c = Integral f c b := by
  apply integral_sub_interval'

theorem integral_triangle_ineq {f : Real → Real} {a b: Real} (h :∃ i, IsIntegral f a b i) :
    (Integral f a b).abs ≤ (Integral (fun t ↦ (f t).abs) a b).abs := by
  apply oint_triangle_ineq _ _ _ h

theorem integral_const (a b c : Real) : Integral (fun t ↦ c) a b = c * (b - a) := by
  apply const_integral
  sorry

theorem integral_sub (f g : Real → Real) (a b : Real) :
    Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by
  apply sub_integral

theorem integral_monotone' (f g : Real → Real) (a b : Real)
    (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x)
    (h : ∀ x, InInterval a b x → f x ≤ g x) :
    (Integral f a b).abs ≤ (Integral g a b).abs := by sorry

theorem continuous_integrable (f : Real → Real) (a x : Real) (hf : Continuous f) :
  ∃ i, IsIntegral f a x i := by sorry
