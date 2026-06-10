import MyProject.Deriv
import MyProject.Integral

open Real Classical

-- ============================================================
-- 補助補題
-- ============================================================

private theorem neg_x_sub_x_add (x h : Real) : x - (x + h) = -h := by
  show x + -(x + h) = -h
  rw [neg_add_distrib, ← add_assoc, AddCommGroup.add_neg, AddCommGroup.zero_add]

-- ============================================================
-- 微積分学の基本定理
-- F(x) = ∫ₐˣ f（向き付き積分）は任意の点 x で微分可能で F'(x) = f(x)
-- ============================================================

/-- 微積分学の基本定理：連続関数 f の不定積分 F(x) = ∫ₐˣ f（向き付き積分）は
任意の点 x で微分可能で F′(x) = f(x)。基点 a と x の位置関係に制約はない。 -/
theorem main' (f : Real → Real) (a x : Real) (hf : Continuous f) :
    let F := fun x ↦ (OIntegral f a x); HasDerivAt F (f x) x := by
  let F := fun x ↦ (OIntegral f a x)
  have hint : ∀ u v, IsIntegrable f u v := fun u v => continuous_integrable f u v hf
  have h₄ : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ h, (0 < h.abs ∧ h.abs < δ) → ((F (x + h) - F x) / h - f x).abs ≤ ε := by
    intro ε hε
    rcases hf x ε hε with ⟨δf, hδf_pos, hδf⟩
    refine ⟨δf, hδf_pos, ?_⟩
    intro h ⟨hgt, hlt⟩
    have hne : h ≠ 0 := nez_of_abs_pos hgt
    -- 向き付き積分の区間差
    have hFdiff0 : F (x + h) - F x = OIntegral f x (x + h) :=
      oint_sub_interval f hint a (x + h) x
    cases le_total 0 h with
    | inl hpos =>
      -- h ≥ 0 の場合
      have hxxh : x ≤ x + h := by
        have h1 := add_left_le x 0 h hpos
        rwa [add_zero] at h1
      have hFdiff : F (x + h) - F x = Integral f x (x + h) := by
        rw [hFdiff0, OIntegral_of_le f hxxh]
      calc ((F (x + h) - F x) / h - f x).abs
          = (Integral f x (x + h) / h - f x).abs := by rw [hFdiff]
        _ = (Integral f x (x + h) / h - f x * (x + h - x) / h).abs := by
            rw [aux (f x) x h hne]
        _ = (Integral f x (x + h) / h - Integral (fun _ ↦ f x) x (x + h) / h).abs := by
            rw [const_integral (f x) x (x + h) hxxh]
        _ ≤ ((Integral (fun t ↦ (f t - f x).abs) x (x + h)) / h).abs := by
            rw [div_sub_div, ← sub_integral f (fun _ ↦ f x) x (x + h) hxxh
              (continuous_integrable f x (x + h) hf) (constant_integrable x (x + h) (f x))]
            exact div_abs_le (integral_triangle_ineq hxxh
              (continuous_integrable _ x (x + h)
                (continuous_sub f (fun _ ↦ f x) hf (continuous_const (f x)))))
        _ ≤ ((Integral (fun _ ↦ ε) x (x + h)) / h).abs := by
            apply div_abs_le
            apply integral_monotone'
            · exact hxxh
            · apply integrable_abs_integrable
              apply integrable_sub
              · apply continuous_integrable _ _ _ hf
              · apply constant_integrable
            · apply constant_integrable
            · intro t; apply abs_nonneg
            · exact fun _ ↦ le_of_lt hε
            · exact fun t ht ↦ le_of_lt (hδf _ (le_lt_trans (InInterval_abs ht) hlt))
        _ = ε := by
            rw [const_integral _ _ _ hxxh, add_sub_cancel, mul_div_cancel _ _ hne]
            apply pos_abs hε
    | inr hneg =>
      -- h ≤ 0 の場合
      have hxhx : x + h ≤ x := by
        have h1 := add_left_le x h 0 hneg
        rwa [add_zero] at h1
      have hFdiff : F (x + h) - F x = -(Integral f (x + h) x) := by
        rw [hFdiff0, OIntegral_of_ge f hxhx]
      have hnle : ¬(x ≤ x + h) := by
        intro hle
        have heq : x = x + h := le_antisymm x (x + h) hle hxhx
        apply hne
        have h2 := add_sub_cancel x h
        rw [← heq] at h2
        rw [← h2]
        exact sub_self x
      have hconv : ∀ t, InInterval (x + h) x t → InInterval x (x + h) t := by
        intro t ht
        dsimp [InInterval] at ht ⊢
        rw [if_pos hxhx] at ht
        rw [if_neg hnle]
        exact ht
      calc ((F (x + h) - F x) / h - f x).abs
          = ((-(Integral f (x + h) x)) / h - f x).abs := by rw [hFdiff]
        _ = (-(Integral f (x + h) x / h + f x)).abs := by
            rw [neg_div, show -(Integral f (x + h) x / h) - f x =
                  -(Integral f (x + h) x / h + f x) from by
                show -(Integral f (x + h) x / h) + -(f x) = _
                rw [← neg_add_distrib]]
        _ = (Integral f (x + h) x / h + f x).abs := abs_neg _
        _ = (Integral f (x + h) x / h + f x * (x + h - x) / h).abs := by
            rw [aux (f x) x h hne]
        _ = ((Integral f (x + h) x + f x * (x + h - x)) / h).abs := by
            rw [div_add_div]
        _ = ((Integral f (x + h) x + -(f x * (x - (x + h)))) / h).abs := by
            rw [show f x * (x + h - x) = -(f x * (x - (x + h))) from by
                  rw [neg_x_sub_x_add, mul_neg, neg_neg, add_sub_cancel]]
        _ = ((Integral f (x + h) x - Integral (fun _ ↦ f x) (x + h) x) / h).abs := by
            rw [const_integral (f x) (x + h) x hxhx]
            rfl
        _ = ((Integral (fun t ↦ f t - f x) (x + h) x) / h).abs := by
            rw [← sub_integral f (fun _ ↦ f x) (x + h) x hxhx
              (continuous_integrable f (x + h) x hf)
              (constant_integrable (x + h) x (f x))]
        _ ≤ ((Integral (fun t ↦ (f t - f x).abs) (x + h) x) / h).abs :=
            div_abs_le (integral_triangle_ineq hxhx
              (continuous_integrable _ (x + h) x
                (continuous_sub f (fun _ ↦ f x) hf (continuous_const (f x)))))
        _ ≤ ((Integral (fun _ ↦ ε) (x + h) x) / h).abs := by
            apply div_abs_le
            apply integral_monotone'
            · exact hxhx
            · apply integrable_abs_integrable
              apply integrable_sub
              · apply continuous_integrable _ _ _ hf
              · apply constant_integrable
            · apply constant_integrable
            · intro t; apply abs_nonneg
            · exact fun _ ↦ le_of_lt hε
            · exact fun t ht ↦ le_of_lt (hδf _ (le_lt_trans (InInterval_abs (hconv t ht)) hlt))
        _ = ε := by
            rw [const_integral _ _ _ hxhx, neg_x_sub_x_add, mul_neg, neg_div,
                mul_div_cancel _ _ hne, abs_neg]
            apply pos_abs hε
  exact limit_at0_iff_le _ _ h₄

theorem main (f : Real → Real) (a x : Real) (hf : Continuous f) :
    let F := fun x ↦ (OIntegral f a x);
    deriv F x (main' f a x hf) = f x := rfl
