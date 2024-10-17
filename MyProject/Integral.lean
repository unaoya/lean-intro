import MyProject.Real
import MyProject.NatNum
import MyProject.Lemmas
import MyProject.Limit
import MyProject.Integral.Def
import MyProject.Integral.Constant
import MyProject.Integral.Interval
import MyProject.Integral.Linearity
import MyProject.Integral.Monotone
import MyProject.Integral.Triangle

noncomputable section

open Real Classical


theorem interval_sub_integral (f : Real → Real) (a b c : Real) : True := sorry

@[simp]
theorem sub_zero_abs (x : Real) : (x - 0).abs = x.abs := sorry

instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le := sorry

instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt := sorry

instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt := sorry
