import MyProject.Lemmas

-- 古典論理、選択公理（無限直積が空でない、とは違う、型理論的な何か？）を使う
-- 全ての命題に真偽が決まるか？排中律？

noncomputable section

open Real Classical

-- 解析入門の実数の公理が全て成立することを確認し、名前をつける

-- 極限の定義

-- 関数の極限
def IsLimAt (f : Real → Real) (l : Real) (a : Real) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) < ε

-- PROOF 4: limit_iff_le
theorem limit_iff_le (f : Real → Real) (a : Real) (l : Real)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) ≤ ε) : IsLimAt f l a := by
  intro ε hε
  have hε2 := pos_half ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h (ε / 2) hε2
  exact ⟨δ, hδ_pos, fun x hx => by
    have hle := hδ x hx
    exact le_lt_trans hle (half_lt hε)⟩

-- PROOF 5: limit_at0_iff_le
theorem limit_at0_iff_le (f : Real → Real) (l : Real)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x) ∧ abs (x) < δ → abs (f x - l) ≤ ε) : IsLimAt f l 0 := by
  apply limit_iff_le
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
  exact ⟨δ, hδ_pos, fun x hx => by
    have : abs (x - 0) = abs x := sub_zero_abs x
    rw [this] at hx
    exact hδ x hx⟩
