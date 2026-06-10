import MyProject.Continuity
import MyProject.Integral.Refine
import MyProject.Integral.Criterion

-- 連続関数の可積分性

theorem continuous_integrable (f : Real → Real) (a x : Real) (hf : Continuous f) :
    ∃ i, IsIntegral f a x i := by
  cases Classical.em (a ≤ x) with
  | inr h =>
    -- a > x: 分割が存在しないため空虚に成立
    exact ⟨0, isintegral_of_not_le f h⟩
  | inl hab =>
    cases Classical.em (a = x) with
    | inl heq =>
      -- a = x: RS は常に 0
      subst heq
      exact ⟨0, isintegral_self f a⟩
    | inr hne =>
      -- a < x: 一様連続性からコーシー型条件を導く
      have hab' : a < x := lt_of_le_of_ne hab hne
      have hxa_pos : 0 < x - a := (pos_iff_lt a x).mp hab'
      have hxa_ne : x - a ≠ 0 := ne_of_gt hxa_pos
      rcases continuous_bounded f a x hab' hf with ⟨M, hM_pos, hM_bound⟩
      apply integrable_of_cauchy f a x hab M hM_bound
      intro ε hε
      rcases continuous_unif_cont f a x hab' hf (ε / 2 / (x - a))
          (pos_div_pos _ _ (pos_half ε hε) hxa_pos)
        with ⟨δ_uc, hδ_uc_pos, hδ_uc⟩
      refine ⟨δ_uc, hδ_uc_pos, ?_⟩
      intro ⟨n, Δ, ξ, hr⟩ hd
      obtain ⟨δ', hδ'_pos, hcomp⟩ := rs_compare f a x M hM_bound hM_pos hab'
        (ε / 2 / (x - a)) (ε / 2) (pos_half ε hε) δ_uc hδ_uc n Δ ξ hr hd
      refine ⟨δ', hδ'_pos, ?_⟩
      intro P' hd'
      have h1 := hcomp P' hd'
      -- ε'(x−a) + ε/2 = ε/2 + ε/2 = ε
      have hdmc : ε / 2 / (x - a) * (x - a) = ε / 2 := by
        rw [mul_comm, ← mul_div_assoc,
            mul_comm (x - a) (ε / 2), mul_div_cancel _ _ hxa_ne]
      rwa [hdmc, half_add ε] at h1
