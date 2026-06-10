import MyProject.Real.Cast

noncomputable section

open Real Classical
open Range

-- 閉区間 InInterval

def InInterval (a b : Real) (x : Real) : Prop :=
  if a ≤ b then a ≤ x ∧ x ≤ b else b ≤ x ∧ x ≤ a

def InInterval_abs {x h t : Real} : InInterval x (x + h) t → (t - x).abs ≤ h.abs := by
  intro hint
  dsimp [InInterval] at hint
  split at hint
  · -- x ≤ x + h
    rename_i hle
    have hh : (0 : Real) ≤ h := by
      have := add_le_add_right x (x + h) (-x) hle
      rw [add_neg', show (x + h) + -x = h from add_sub_cancel x h] at this; exact this
    have htx : (0 : Real) ≤ t + -x := by
      have := add_le_add_right x t (-x) hint.1
      rw [add_neg'] at this; exact this
    have htxh : t + -x ≤ h := by
      have := add_le_add_right t (x + h) (-x) hint.2
      rw [show (x + h) + -x = h from add_sub_cancel x h] at this; exact this
    show Real.abs (t + -x) ≤ Real.abs h
    rw [nonneg_abs htx, nonneg_abs hh]; exact htxh
  · -- ¬(x ≤ x + h)
    rename_i hnle
    have hh : h ≤ 0 := by
      have hlt := ne_le_lt x (x + h) hnle
      have := add_le_add_right (x + h) x (-x) hlt.1
      rw [show (x + h) + -x = h from add_sub_cancel x h, add_neg'] at this; exact this
    have htx : t + -x ≤ 0 := by
      have := add_le_add_right t x (-x) hint.2
      rw [add_neg'] at this; exact this
    have hhtx : h ≤ t + -x := by
      have := add_le_add_right (x + h) t (-x) hint.1
      rw [show (x + h) + -x = h from add_sub_cancel x h] at this; exact this
    show Real.abs (t + -x) ≤ Real.abs h
    rw [nonpos_abs htx, nonpos_abs hh]
    exact neg_le_neg h (t + -x) hhtx

-- ============================================================
-- §17. Remaining
-- ============================================================

-- InInterval の展開
theorem in_interval_iff {a b t : Real} (hab : a ≤ b) :
    InInterval a b t ↔ a ≤ t ∧ t ≤ b := by
  dsimp [InInterval]
  rw [if_pos hab]

theorem in_interval_pair {a b t : Real} (hab : a ≤ b) (h : InInterval a b t) :
    a ≤ t ∧ t ≤ b := (in_interval_iff hab).mp h
