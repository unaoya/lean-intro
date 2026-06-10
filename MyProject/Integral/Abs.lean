import MyProject.Integral.Oscillation
import MyProject.Integral.Criterion
import MyProject.Integral.Bounded
import MyProject.Integral.Monotone

-- |f| の可積分性と積分の三角不等式

-- 可積分なら |f| も可積分（a ≤ b 版）
theorem abs_integrable (f : Real → Real) (a b : Real) (h : a ≤ b)
    (h'' : IsIntegrable f a b) : IsIntegrable (fun x ↦ (f x).abs) a b := by
  cases Classical.em (b ≤ a) with
  | inl hba =>
    -- a = b : RS は常に 0
    have heq : a = b := LinearOrderedField.le_asymm a b h hba
    subst heq
    exact ⟨0, isintegral_self _ a⟩
  | inr hba =>
    -- a < b : f の可積分性（積分値 If への収束）からコーシー型条件を導く
    have hab' : a < b := ne_le_lt b a hba
    obtain ⟨M₀, hM₀⟩ := integrable_bounded f a b h h''
    have ha_in : InInterval a b a := (in_interval_iff h).mpr ⟨le_refl a, h⟩
    have hM₀_nn : (0 : Real) ≤ M₀ := le_trans abs_nonneg (hM₀ a ha_in)
    have hM_pos : (0 : Real) < M₀ + 1 := by
      apply lt_le_trans 0 1 (M₀ + 1) zero_lt_one
      have h1 := LinearOrderedField.add_le_add 0 M₀ 1 hM₀_nn
      calc (1 : Real) = 0 + 1 := (AddCommGroup.zero_add 1).symm
        _ ≤ M₀ + 1 := h1
    have hM : ∀ t, InInterval a b t → (f t).abs ≤ M₀ + 1 := by
      intro t ht
      apply le_trans (hM₀ t ht)
      have h1 := add_left_le M₀ 0 1 zero_lt_one.1
      rwa [add_zero] at h1
    have hMg : ∀ t, InInterval a b t → ((f t).abs).abs ≤ M₀ + 1 := fun t ht => by
      rw [nonneg_abs abs_nonneg]; exact hM t ht
    obtain ⟨If, hIf⟩ := h''
    apply integrable_of_cauchy _ a b h (M₀ + 1) hMg
    intro ε hε
    obtain ⟨δf, hδf_pos, hδf⟩ := hIf (ε / 2 / 2) (pos_half _ (pos_half ε hε))
    refine ⟨δf, hδf_pos, ?_⟩
    intro n Δ ξ hr hd
    obtain ⟨δ', hδ'_pos, hcomp⟩ := abs_rs_compare f a b (M₀ + 1) If hM hM_pos hab'
      (ε / 2 / 2) (ε / 2) (pos_half ε hε) δf hδf n Δ ξ hr hd
    refine ⟨δ', hδ'_pos, ?_⟩
    intro n' Δ' ξ' hr' hd'
    have h1 := hcomp n' Δ' ξ' hr' hd'
    -- (ε/4 + ε/4) + ε/2 = ε/2 + ε/2 = ε
    rwa [half_add (ε / 2), half_add ε] at h1

-- 積分の三角不等式（Triangle.lean から移設）
theorem int_triangle_ineq (f : Real → Real) (a b : Real) (h : a ≤ b)
    (h'' : IsIntegrable f a b) :
    (Integral f a b).abs ≤ Integral (fun x ↦ (f x).abs) a b := by
  apply abs_le
  · rw [← neg_integral f a b h h'']
    have h₁ : ∀ x, InInterval a b x → -f x ≤ (f x).abs := fun x _ ↦ neg_le_abs (f x)
    apply integral_monotone (fun x ↦ -(f x)) (fun x ↦ (f x).abs) a b h h₁
    apply neg_integrable _ _ _ h''
    apply abs_integrable _ _ _ h h''
  · have h₀ : ∀ x, InInterval a b x → f x ≤ (f x).abs := fun x _ ↦ le_abs (f x)
    apply integral_monotone f (fun x ↦ (f x).abs) a b h h₀
    exact h''
    apply abs_integrable _ _ _ h h''

theorem integrable_abs_integrable (f : Real → Real) (a b : Real)
    (h : IsIntegrable f a b) :
    IsIntegrable (fun x ↦ (f x).abs) a b := by
  cases Classical.em (a ≤ b) with
  | inl hab => exact abs_integrable f a b hab h
  | inr hab => exact ⟨0, isintegral_of_not_le _ hab⟩

-- 積分の三角不等式（右辺に .abs を付けた形）
theorem integral_triangle_ineq {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (h : ∃ i, IsIntegral f a b i) :
    (Integral f a b).abs ≤ (Integral (fun t ↦ (f t).abs) a b).abs := by
  have habs : IsIntegrable (fun t ↦ (f t).abs) a b := integrable_abs_integrable f a b h
  have hnn : 0 ≤ Integral (fun t ↦ (f t).abs) a b :=
    integral_nonneg (fun t ↦ (f t).abs) a b hab (fun t _ => abs_nonneg) habs
  rw [nonneg_abs hnn]
  exact int_triangle_ineq f a b hab h
