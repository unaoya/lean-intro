import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 積分の線形性

-- ======================================================
-- 1. add_integrable
-- ======================================================
theorem add_integrable (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x + g x) a b := by
  rcases hf with ⟨if_, hif⟩
  rcases hg with ⟨ig, hig⟩
  refine ⟨if_ + ig, fun ε hε => ?_⟩
  rcases hif (ε / 2) (pos_half ε hε) with ⟨δf, hδf_pos, hδf⟩
  rcases hig (ε / 2) (pos_half ε hε) with ⟨δg, hδg_pos, hδg⟩
  refine ⟨min δf δg, min_pos δf δg hδf_pos hδg_pos, fun ⟨n, Δ, ξ, hr⟩ hd => ?_⟩
  have hdf : Partition.diam Δ < δf :=
    lt_le_trans _ _ _ hd (min_left_le δf δg)
  have hdg : Partition.diam Δ < δg :=
    lt_le_trans _ _ _ hd (min_right_le δf δg)
  rw [additive_riemann_sum, add_sub_add]
  calc abs (RiemannSum f Δ ξ - if_ + (RiemannSum g Δ ξ - ig))
      ≤ abs (RiemannSum f Δ ξ - if_) + abs (RiemannSum g Δ ξ - ig) :=
        abs_triangle _ _
    _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ (hδf ⟨n, Δ, ξ, hr⟩ hdf) (hδg ⟨n, Δ, ξ, hr⟩ hdg)
    _ = ε := half_add ε

-- ======================================================
-- 2. neg_integrable (no a ≤ b hypothesis needed)
-- ======================================================
theorem neg_integrable (f : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b) : IsIntegrable (fun x ↦ -(f x)) a b := by
  rcases hf with ⟨i, hi⟩
  refine ⟨-i, fun ε hε => ?_⟩
  rcases hi ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun ⟨n, Δ, ξ, hr⟩ hd => ?_⟩
  rw [neg_riemann_sum]
  have : -RiemannSum f Δ ξ - -i = -(RiemannSum f Δ ξ - i) := by
    show -RiemannSum f Δ ξ + -(-i) = -(RiemannSum f Δ ξ + -i)
    rw [neg_add_distrib, neg_neg]
  rw [this, abs_neg]
  exact hδ ⟨n, Δ, ξ, hr⟩ hd

-- ======================================================
-- 3. integrable_sub
-- ======================================================
theorem integrable_sub (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x - g x) a b := by
  have hng := neg_integrable g a b hg
  have := add_integrable f (fun x ↦ -g x) a b hf hng
  exact this

-- ======================================================
-- 4. additive_integral (with integrability hypotheses)
-- ======================================================
theorem additive_integral (f g : Real → Real) (a b : Real)
    (hab : a ≤ b) (hf : IsIntegrable f a b) (hg : IsIntegrable g a b) :
    Integral (fun t ↦ f t + g t) a b = Integral f a b + Integral g a b := by
  rcases hf with ⟨if_, hif⟩
  rcases hg with ⟨ig, hig⟩
  have hfg : IsIntegral (fun t ↦ f t + g t) a b (if_ + ig) := by
    intro ε hε
    rcases hif (ε / 2) (pos_half ε hε) with ⟨δf, hδf_pos, hδf⟩
    rcases hig (ε / 2) (pos_half ε hε) with ⟨δg, hδg_pos, hδg⟩
    refine ⟨min δf δg, min_pos δf δg hδf_pos hδg_pos, fun ⟨n, Δ, ξ, hr⟩ hd => ?_⟩
    have hdf : Partition.diam Δ < δf :=
      lt_le_trans _ _ _ hd (min_left_le δf δg)
    have hdg : Partition.diam Δ < δg :=
      lt_le_trans _ _ _ hd (min_right_le δf δg)
    rw [additive_riemann_sum, add_sub_add]
    calc abs (RiemannSum f Δ ξ - if_ + (RiemannSum g Δ ξ - ig))
        ≤ abs (RiemannSum f Δ ξ - if_) + abs (RiemannSum g Δ ξ - ig) :=
          abs_triangle _ _
      _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ (hδf ⟨n, Δ, ξ, hr⟩ hdf) (hδg ⟨n, Δ, ξ, hr⟩ hdg)
      _ = ε := half_add ε
  rw [IsIntegral_iff _ _ _ _ hab hfg, IsIntegral_iff _ _ _ _ hab hif, IsIntegral_iff _ _ _ _ hab hig]

-- ======================================================
-- 5. neg_integral (with integrability hypothesis)
-- ======================================================
theorem neg_integral (f : Real → Real) (a b : Real)
    (hab : a ≤ b) (hf : IsIntegrable f a b) :
    Integral (fun t ↦ -f t) a b = -Integral f a b := by
  rcases hf with ⟨i, hi⟩
  have hni : IsIntegral (fun t ↦ -f t) a b (-i) := by
    intro ε hε
    rcases hi ε hε with ⟨δ, hδ_pos, hδ⟩
    refine ⟨δ, hδ_pos, fun ⟨n, Δ, ξ, hr⟩ hd => ?_⟩
    rw [neg_riemann_sum]
    have : -RiemannSum f Δ ξ - -i = -(RiemannSum f Δ ξ - i) := by
      show -RiemannSum f Δ ξ + -(-i) = -(RiemannSum f Δ ξ + -i)
      rw [neg_add_distrib, neg_neg]
    rw [this, abs_neg]
    exact hδ ⟨n, Δ, ξ, hr⟩ hd
  rw [IsIntegral_iff _ _ _ _ hab hni, IsIntegral_iff _ _ _ _ hab hi]

-- ======================================================
-- 6. sub_integral (with integrability hypotheses)
-- ======================================================
theorem sub_integral (f g : Real → Real) (a b : Real)
    (hab : a ≤ b) (hf : IsIntegrable f a b) (hg : IsIntegrable g a b) :
    Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by
  rw [← add_neg_sub]
  rw [← neg_integral g a b hab hg]
  rw [← additive_integral f (fun t ↦ -g t) a b hab hf (neg_integrable g a b hg)]
  apply integral_congr
  · exact hab
  · intro x
    rw [add_neg_sub]

-- abs_integrable は補題の依存関係の都合で Integral.lean に移動した
