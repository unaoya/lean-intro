import MyProject.Real
import MyProject.NatNum
import MyProject.Lemmas
import MyProject.Limit

noncomputable section

open Real Classical

-- 分割を定義
structure Partition (n : Nat) (a b : Real) where
  points : Range n.succ → Real
  increase : ∀ i : Range n, points (incl i) < points (addone i)
  left : points ⟨0, by simp⟩ = a
  right : points ⟨n, by simp⟩ = b

-- 代表点を定義
def IsRepr (a b : Real) (n : Nat) (Δ : Partition n a b)
  (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)

def Partition.length (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

theorem Partition.length_pos (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) :
  0 < Partition.length n a b Δ i := by
  simp [Partition.length]
  rw [← pos_iff_lt]
  exact Δ.increase i

theorem Partition.zero (a b : Real) (Δ : Partition 0 a b) : a = b := by
  have ha : Δ.points ⟨0, by simp⟩ = a := by rw [Δ.left]
  have hb : Δ.points ⟨0, by simp⟩ = b := by rw [Δ.right]
  rw [← ha, hb]

theorem summation_zero (f : Range 0 → Real) : Sumation 0 f = 0 := rfl

theorem summation_succ (n : Nat) (f : Range n.succ → Real) :
  Sumation n.succ f = Sumation n (fun i ↦ f (incl i)) + f ⟨n, by exact Nat.lt_add_one n⟩ := by
  rfl

theorem telescope_2 (a b c : Real) : b - a = (c - a) + (b - c) := by
  sorry

theorem telescope_sum (n : Nat) (f : Range n.succ → Real) :
  Sumation n (fun i ↦ f (addone i) - f (incl i)) = f ⟨n, by exact Nat.lt_add_one n⟩ - f ⟨0, by simp⟩ :=
  match n with
  | Nat.zero => by
    rw [summation_zero]
    rw [sub_self]
  | Nat.succ n => by
    rw [summation_succ]
    let f' : Range n.succ → Real := fun i => f (incl i)
    have (i : Range n) : addone (incl i) = incl (addone i) := by sorry
    have : (fun i ↦ f (addone (incl i)) - f (incl (incl i))) = fun i ↦ f (incl (addone i)) - f (incl (incl i)) := by
      apply funext
      intro i
      rw [this]
    rw [this]
    rw [telescope_sum n f']
    sorry

theorem Partition.length_sum (n : Nat) (a b : Real) (Δ : Partition n a b) :
  Sumation n (Partition.length n a b Δ) = b - a := by
  sorry

def Partition.diam (n : Nat) (a b : Real) (Δ : Partition n a b) : Real :=
  fmax' n Δ.length

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
  (Δ : Partition n a b) (ξ : Range n → Real) (h' : ∀ x, a ≤ x → x ≤ b → 0 ≤ f x) (h : IsRepr a b n Δ ξ) :
  0 ≤ RiemannSum f a b n Δ ξ := by
  apply sumation_nonneg
  intro i
  apply mul_nonneg
  apply h' (ξ i)
  have := h i
  have := Δ.increase
  have := Δ.left
  sorry
  sorry
  apply le_of_lt
  apply Partition.length_pos n a b Δ i

-- 積分の定義
def HasIntegral (f : Real → Real) (a b : Real) (i : Real) : Prop :=
  ∀ (ε : Real), 0 < ε → ∃ (δ : Real), 0 < δ ∧ ∀ n : Nat, ∀ Δ : Partition n a b, ∀ ξ : Range n → Real,
    IsRepr a b n Δ ξ → (Partition.diam n a b Δ) < δ →
    abs (RiemannSum f a b n Δ ξ - i) < ε

def Integral (f : Real → Real) (a b : Real) : Real :=
  if h : ∃ i, HasIntegral f a b i then Classical.choose h else 0

theorem HasIntegral_iff (f : Real → Real) (a b : Real) (i : Real) :
  HasIntegral f a b i ↔ Integral f a b = i := by
  sorry

theorem integral_congr (f g : Real → Real) (a b : Real) (h : ∀ x, f x = g x) :
  Integral f a b = Integral g a b := by
  sorry
