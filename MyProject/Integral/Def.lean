import MyProject.Integral.Partition
import MyProject.Limit

noncomputable section

open Real Classical

-- リーマン和の定義
def RiemannSum (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) : Real :=
    Sumation n (fun i ↦ f (ξ i) * Δ.length i)

theorem const_riemann_sum (c a b : Real) (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun _ ↦ c) a b n Δ ξ = c * (b - a) := by
  rw [RiemannSum]
  rw [summation_smul]
  rw [Partition.length_sum]

theorem additive_riemann_sum (f g : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun t ↦ f t + g t) a b n Δ ξ = RiemannSum f a b n Δ ξ + RiemannSum g a b n Δ ξ := by
  rw [RiemannSum, RiemannSum, RiemannSum]
  rw [← addtive_summation]
  rw [summation_congr]
  intro i
  rw [add_mul]

theorem neg_riemann_sum (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun t ↦ -f t) a b n Δ ξ = -RiemannSum f a b n Δ ξ := by
  rw [RiemannSum, RiemannSum, neg_summation]
  apply summation_congr
  intro i
  rw [neg_mul]

theorem RiemannSum_nonneg (f : Real → Real) (a b : Real) (n : Nat)
    (Δ : Partition n a b) (ξ : Range n → Real)
    (h' : ∀ x, InInterval a b x → 0 ≤ f x) (h : Δ.IsRepr a b n ξ) :
    0 ≤ RiemannSum f a b n Δ ξ := by
  apply sumation_nonneg
  intro i
  apply mul_nonneg
  · apply h' (ξ i)
    have := h i
    have := Δ.increase
    have := Δ.left
    sorry
  · apply Partition.length_nonneg n a b Δ i

-- 積分の定義
def IsIntegral (f : Real → Real) (a b : Real) (i : Real) : Prop :=
  ∀ (ε : Real), 0 < ε → ∃ (δ : Real), 0 < δ ∧ ∀ n : Nat, ∀ Δ : Partition n a b, ∀ ξ : Range n → Real,
    Δ.IsRepr a b n ξ → (Partition.diam n a b Δ) < δ →
    abs (RiemannSum f a b n Δ ξ - i) < ε

def IsIntegrable (f : Real → Real) (a b : Real) : Prop :=
  ∃ i, IsIntegral f a b i

-- 向きなし積分。本当はa ≤ bを仮定する必要あり
def Integral (f : Real → Real) (a b : Real) : Real :=
  if h : IsIntegrable f a b then Classical.choose h else 0

theorem IsIntegral_iff (f : Real → Real) (a b : Real) (i : Real) :
  IsIntegral f a b i ↔ Integral f a b = i := by
  sorry

theorem integral_congr (f g : Real → Real) (a b : Real) (h : ∀ x, f x = g x) :
  Integral f a b = Integral g a b := by
  sorry
