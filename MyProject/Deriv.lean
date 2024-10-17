import MyProject.Real
import MyProject.NatNum
import MyProject.Lemmas
import MyProject.Limit

noncomputable section

open Real Classical

-- 微分係数の定義
def HasDerivAt (f : Real → Real) (f' : Real) (a : Real) : Prop :=
  IsLimAt (fun h ↦ (f (a + h) - f a) / h) f' a

def deriv (f : Real → Real) (a : Real) : Real :=
  if h : ∃ f', HasDerivAt f f' a then Classical.choose h else 0

theorem deriv_eq (f : Real → Real) (a : Real) (f' : Real) (h : HasDerivAt f f' a) : deriv f a = f' := by
  rw [deriv]
  rw [dif_pos]
  -- exact Exists.intro f' h
  sorry
  sorry

theorem deriv_iff (x f' : Real) (f : Real → Real) : deriv f x = f' ↔ limit (fun h ↦ (f (x + h) - f x) / h) 0 = f' := sorry

-- -- 微分係数の具体例
-- example (n : Nat) : HasDerivAt (fun x ↦ x ^ n) (n * a ^ (n - 1)) a := by
--   sorry
