import MyProject.Lemmas

noncomputable section

open Real Classical

-- 分割を定義
structure Partition (n : Nat) (a b : Real) where
  points : Range n.succ → Real
  increase : ∀ i : Range n, points (incl i) < points (addone i)
  left : points ⟨0, by simp⟩ = a
  right : points ⟨n, by simp⟩ = b

namespace Partition

-- 代表点を定義
def IsRepr (a b : Real) (n : Nat) (Δ : Partition n a b)
  (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)

def length (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

theorem length_pos (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) :
  0 < Δ.length n a b i := by
  simp [length]
  rw [← pos_iff_lt]
  exact Δ.increase i

theorem zero (a b : Real) (Δ : Partition 0 a b) : a = b := by
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

theorem length_sum (n : Nat) (a b : Real) (Δ : Partition n a b) :
  Sumation n (Δ.length n a b) = b - a := by
  sorry

def diam (n : Nat) (a b : Real) (Δ : Partition n a b) : Real :=
  fmax' n Δ.length

end Partition
