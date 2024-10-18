-- ライブラリの読み込み
import mathlib

-- 変数の導入。
-- Continuous fはfが連続であるという命題。
-- Continuous fが型、この型を持つ項（変数）がh
-- hがfが連続であるという命題の証明と解釈できる。
variable (f : ℝ → ℝ) (h : Continuous f)

-- 不定積分（原始関数？）の定義
noncomputable
def F : ℝ → ℝ := fun u ↦ ∫ x in (0 : ℝ)..u, f x

-- 定理の主張とその証明
example : HasStrictDerivAt (F f) (f b) b :=
  intervalIntegral.integral_hasStrictDerivAt_right
    (Continuous.intervalIntegrable h 0 b)
    (Continuous.stronglyMeasurableAtFilter h MeasureTheory.volume (nhds b))
    (Continuous.continuousAt h)

-- intervalIntegral.integral_hasStrictDerivAt_right.{u_3}
--   {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
--   {f : ℝ → E} {a b : ℝ}
--   (hf : IntervalIntegrable f MeasureTheory.volume a b)
--   (hmeas : StronglyMeasurableAtFilter f (nhds b) MeasureTheory.volume)
--   (hb : ContinuousAt f b) :
--   HasStrictDerivAt (fun u ↦ ∫ (x : ℝ) in a..u, f x) (f b) b

-- Continuous.intervalIntegrable.{u_3} {E : Type u_3} [NormedAddCommGroup E]
--   {μ : MeasureTheory.Measure ℝ}
--   [MeasureTheory.IsLocallyFiniteMeasure μ] {u : ℝ → E} (hu : Continuous u)
--   (a b : ℝ) :
--   IntervalIntegrable u μ a b

-- Continuous.stronglyMeasurableAtFilter.{u_1, u_2} {α : Type u_1} {β : Type u_2}
--   [MeasurableSpace α] [TopologicalSpace α]
--   [OpensMeasurableSpace α] [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
--   [SecondCountableTopologyEither α β] {f : α → β} (hf : Continuous f)
--   (μ : MeasureTheory.Measure α) (l : Filter α) :
--   StronglyMeasurableAtFilter f l μ

-- Continuous.continuousAt.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
--   [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
--   {x : X} (h : Continuous f) :
--   ContinuousAt f x

-- タクティックを使うバージョン

example : HasStrictDerivAt (F f) (f b) b := by
  apply intervalIntegral.integral_hasStrictDerivAt_right
  · apply Continuous.intervalIntegrable h
  · exact Continuous.stronglyMeasurableAtFilter h MeasureTheory.volume (nhds b)
  · exact Continuous.continuousAt h

-- コードを詳しく見る

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
