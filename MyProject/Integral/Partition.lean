import MyProject.Lemmas
import Init.Data.Nat.Basic

noncomputable section

open Real Classical Range

-- 分割を定義
structure Partition (n : Nat) (a b : Real) where
  points : Range n.succ → Real
  increase : ∀ i : Range n, points (incl i) ≤ points (addone i)
  left : points ⟨0, by simp⟩ = a
  right : points ⟨n, by simp⟩ = b

namespace Partition

theorem zero (a b : Real) (Δ : Partition 0 a b) : a = b := by
  have ha : Δ.points ⟨0, by simp⟩ = a := by rw [Δ.left]
  have hb : Δ.points ⟨0, by simp⟩ = b := by rw [Δ.right]
  rw [← ha, hb]

theorem zero_point (a b : Real) (Δ : Partition 0 a b) :
    Δ.points ⟨0, Nat.one_pos⟩ = a := Δ.left

theorem range_one (n : Nat) (hn : n = 0) (i : Range n.succ) : i = ⟨0, Nat.zero_lt_succ n⟩ := by
  rw [ext]
  simp
  have := i.property
  rw [Nat.lt_succ_iff] at this
  rw [← Nat.le_zero_eq]
  exact le_of_le_of_eq this hn

theorem left_le_point (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n.succ) :
  a ≤ Δ.points i := by
  apply induction n.succ (fun i => a ≤ Δ.points i)
  intro x IH
  by_cases h : x = ⟨0, by simp⟩
  · rw [h, Δ.left]
    apply le_refl a
  · have h₀ : ¬x.val = 0 := fun h' => h (Subtype.ext_iff.2 h')
    let y : Range n := ⟨x.val.pred, Nat.pred_lt_pred h₀ x.property⟩
    calc
      a ≤ Δ.points y.incl := (IH y.incl (Nat.pred_lt h₀))
      _ ≤ Δ.points y.addone := Δ.increase y
      _ = Δ.points x := congrArg Δ.points (Subtype.ext_iff.2 (Nat.succ_pred_eq_of_ne_zero h₀))

theorem sub_lt_self (m n : Nat) (hm : 0 < m) (hn : 0 < n) : n - m < n := Nat.sub_lt hn hm

theorem left_le_right (n : Nat) (a b : Real) (Δ : Partition n a b) :
    a ≤ b := by
  rw [← Δ.right]
  exact Δ.left_le_point ⟨n, by simp⟩

theorem sub_add_eq_sub_sub (n m : Nat) (h : m ≤ n) (h' : 0 < m) : n - m + 1 = n - (m - 1) := by
  have h₀ : m - 1 < n := by exact Nat.sub_one_lt_of_le h' h
  have h₁ : 0 < n - (m - 1) := by exact Nat.zero_lt_sub_of_lt h₀
  rw [← Nat.succ_eq_add_one, ← Nat.succ_pred_eq_of_pos h₁, Nat.succ_inj']
  simp
  rw [Nat.sub_sub, ← Nat.pred_eq_sub_one, ← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos h']

theorem point_le_right (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n.succ) :
  Δ.points i ≤ b := by
  by_cases hn : n = 0
  · rw [range_one n hn i, Δ.left]
    exact Δ.left_le_right n a b
  · let P : Range n.succ → Prop := fun i => Δ.points ⟨n - i.val, Nat.sub_lt_succ n i.val⟩ ≤ b
    have hP : ∀ i, P i := by
      apply induction n.succ P
      intro x IH
      by_cases h : x = ⟨0, by simp⟩
      · rw [h]
        dsimp [P]
        rw [Δ.right]
        apply le_refl b
      · have h₀ : ¬x.val = 0 := fun h' => h (Subtype.ext_iff.2 h')
        let y : Range n := ⟨x.val.pred, Nat.pred_lt_pred h₀ x.property⟩
        have h₁ : n - x.val < n :=
          Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) (Nat.zero_lt_of_ne_zero h₀)
        have h₂ : n - x.val < n.succ :=
          Nat.sub_lt_succ n x.val
        have h₃ : n - y.val < n.succ :=
          Nat.sub_lt_succ n y.val
        calc
          Δ.points ⟨n - x.val, h₂⟩ ≤ Δ.points ⟨n - y.val, h₃⟩ := by
            have : incl ⟨n - x.val, h₁⟩ = ⟨n - x.val, h₂⟩ := rfl
            rw [← this]
            have : addone ⟨n - x.val, h₁⟩ = ⟨n - y.val, h₃⟩ := by
              simp [ext]
              exact sub_add_eq_sub_sub n x.val (Nat.lt_succ.1 x.property) (Nat.zero_lt_of_ne_zero h₀)
            rw [← this]
            apply Δ.increase
          _ ≤ b := IH y.incl (Nat.pred_lt h₀)
    let j : Range n.succ := ⟨n - i.val, Nat.sub_lt_succ n i.val⟩
    have : ⟨n - j.val, Nat.sub_lt_succ n j.val⟩ = i := by
      rw [ext]
      exact Nat.sub_sub_self (Nat.le_of_lt_succ i.property)
    rw [← this]
    exact hP j

theorem points_in_interval (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n.succ) :
    InInterval a b (Δ.points i) := by
  have := Δ.left_le_right n a b
  dsimp [InInterval]
  rw [if_pos this]
  constructor
  · exact Δ.left_le_point i
  · exact Δ.point_le_right i

-- 代表点を定義
def IsRepr (a b : Real) (n : Nat) (Δ : Partition n a b)
  (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, InInterval (Δ.points i.incl) (Δ.points i.addone) (ξ i)

theorem repr_in_interval (a b : Real) (n : Nat) (Δ : Partition n a b)
  (ξ : Range n → Real) (h : IsRepr a b n Δ ξ) :
    ∀ i : Range n, InInterval a b (ξ i) := by
  intro i
  have : InInterval (Δ.points i.incl) (Δ.points i.addone) (ξ i) := h i
  dsimp [InInterval] at *
  rw [if_pos (left_le_right n a b Δ)]
  rw [if_pos (Δ.increase i)] at this
  constructor
  · apply le_trans (Δ.left_le_point i.incl) this.left
  · apply le_trans this.right (Δ.point_le_right i.addone)

def length (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

theorem length_nonneg (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) :
  0 ≤ Δ.length n a b i := by
  simp [length]
  rw [← nonneg_iff_le]
  exact Δ.increase i

theorem length_sum (n : Nat) (a b : Real) (Δ : Partition n a b) :
  Sumation n (Δ.length n a b) = b - a := by
  have : Sumation n (Δ.length n a b) = Sumation n (fun i ↦ Δ.points (addone i) - Δ.points (incl i)) := by rfl
  rw [this, telescope_sum n (Δ.points)]
  simp [Δ.left, Δ.right]

def diam (n : Nat) (a b : Real) (Δ : Partition n a b) : Real :=
  fmax' n Δ.length

end Partition
