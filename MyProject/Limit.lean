import MyProject.Real
import MyProject.NatNum
import MyProject.Lemmas

-- 古典論理、選択公理（無限直積が空でない、とは違う、型理論的な何か？）を使う
-- 全ての命題に真偽が決まるか？排中律？

noncomputable section

open Real Classical

-- 解析入門の実数の公理が全て成立することを確認し、名前をつける

-- 極限の定義

-- 関数の極限（HasLimAtの方がいい？）
def IsLimAt (f : Real → Real) (l : Real) (a : Real) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) < ε

def limit (f : Real → Real) (a : Real) : Real :=
  if h : ∃ l, IsLimAt f l a then Classical.choose h else 0

theorem limit_eq (f : Real → Real) (a : Real) (l : Real) (h : IsLimAt f l a) : limit f a = l := by
  rw [limit]
  rw [dif_pos]
  sorry
  exact Exists.intro l h

theorem limit_eq_iff (f : Real → Real) (a : Real) (l : Real) : IsLimAt f l a ↔ limit f a = l := by
  rw [limit]
  rw [dif_pos]
  sorry
  sorry

theorem limit_iff_le (f : Real → Real) (a : Real) (l : Real) : IsLimAt f l a ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) ≤ ε := by sorry

def Continuous (f : Real → Real) : Prop :=
  ∀ a, ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε
