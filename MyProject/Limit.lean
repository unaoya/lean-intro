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

def Continuous (f : Real → Real) : Prop :=
  ∀ a, ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

-- PROOF 6: continuous_sub
theorem continuous_sub (f g : Real → Real) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun t ↦ f t - g t) := by
  intro a ε hε
  have hε2 := pos_half ε hε
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hf a (ε / 2) hε2
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hg a (ε / 2) hε2
  refine ⟨min δ₁ δ₂, min_pos δ₁ δ₂ hδ₁_pos hδ₂_pos, fun x hx => ?_⟩
  have hx1 : abs (x - a) < δ₁ :=
    lt_le_trans (abs (x - a)) (min δ₁ δ₂) δ₁ hx (min_left_le δ₁ δ₂)
  have hx2 : abs (x - a) < δ₂ :=
    lt_le_trans (abs (x - a)) (min δ₁ δ₂) δ₂ hx (min_right_le δ₁ δ₂)
  have hf_bound := hδ₁ x hx1
  have hg_bound := hδ₂ x hx2
  -- f x - g x - (f a - g a) = (f x - f a) + (-(g x) - -(g a))
  have hsplit : (fun t ↦ f t - g t) x - (fun t ↦ f t - g t) a = (f x - f a) + (-(g x) - -(g a)) :=
    show f x + -(g x) - (f a + -(g a)) = (f x - f a) + (-(g x) - -(g a)) from
    add_sub_add (f x) (-(g x)) (f a) (-(g a))
  rw [hsplit]
  have habs_neg_g : abs (-(g x) - -(g a)) = abs (g x - g a) := neg_sub_neg_abs (g x) (g a)
  have htri := abs_triangle (f x - f a) (-(g x) - -(g a))
  calc abs ((f x - f a) + (-(g x) - -(g a)))
      ≤ abs (f x - f a) + abs (-(g x) - -(g a)) := htri
    _ = abs (f x - f a) + abs (g x - g a) := by rw [habs_neg_g]
    _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ hf_bound hg_bound
    _ = ε := half_add ε

-- PROOF 7: continuous_const
theorem continuous_const (c : Real) : Continuous (fun _ ↦ c) := by
  intro a ε hε
  exact ⟨1, zero_lt_one, fun x _ => by
    show abs (c - c) < ε
    rw [sub_self c, abs_zero]
    exact hε⟩
