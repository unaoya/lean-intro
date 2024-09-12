import mathlib

#check intervalIntegral.integral_hasStrictDerivAt_right

-- ∀ {E : Type u_3}
-- [inst : NormedAddCommGroup E]
-- [inst_1 : NormedSpace ℝ E]
-- [inst_2 : CompleteSpace E]
-- {f : ℝ → E}
-- {a b : ℝ},
-- IntervalIntegrable f MeasureTheory.volume a b →
-- StronglyMeasurableAtFilter f (nhds b) MeasureTheory.volume →
-- ContinuousAt f b →
-- HasStrictDerivAt (fun u ↦ ∫ (x : ℝ) in a..u, f x) (f b) b

#check HasStrictDerivAt
#print HasStrictDerivAt

variable (f : ℝ → ℝ) (h : Continuous f)

noncomputable
def F : ℝ → ℝ := fun u ↦ ∫ x in (0 : ℝ)..u, f x

example : HasStrictDerivAt (F f) (f b) b := by
  apply intervalIntegral.integral_hasStrictDerivAt_right
  · apply Continuous.intervalIntegrable h
  · exact Continuous.stronglyMeasurableAtFilter h MeasureTheory.volume (nhds b)
  · exact Continuous.continuousAt h
