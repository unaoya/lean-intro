-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«06_Topology»

-- ✏ 練習 72 の解答

theorem swapOrTac {p q : Prop} : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

#print swapOrTac

-- ✏ 練習 73 の解答

theorem idTac {p : Prop} : p → p := by
  intro h
  exact h

#print idTac

-- ✏ 練習 74 の解答

example : (2 : Nat) ∈ ({n | n < 5} : Set Nat) :=
  Nat.le.step (Nat.le.step Nat.le.refl)

-- ✏ 練習 75 の解答

#print axioms Set.compl_compl

-- ✏ 練習 76 の解答

example : Function.Bijective (fun n : Nat => n) :=
  ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩

-- ✏ 練習 77 の解答

example : (discrete Nat).IsOpen {n | n = 0} := trivial

-- ✏ 練習 78 の解答

#check @Continuous

-- ✏ 練習 79 の解答

#print axioms Set.subset_preimage_iUnion

-- ✏ 練習 80 の解答

#print axioms isOpen_empty

-- ✏ 練習 81 の解答

example : TopologicalSpace Bool := discrete Bool

-- ✏ 練習 82 の解答
