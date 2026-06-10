import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 積分の線形性

/-- 積分値の加法性（核補題）。 -/
theorem isintegral_add {f g : Real → Real} {a b if_ ig : Real}
    (hif : IsIntegral f a b if_) (hig : IsIntegral g a b ig) :
    IsIntegral (fun x ↦ f x + g x) a b (if_ + ig) := by
  intro ε hε
  rcases hif (ε / 2) (pos_half ε hε) with ⟨δf, hδf_pos, hδf⟩
  rcases hig (ε / 2) (pos_half ε hε) with ⟨δg, hδg_pos, hδg⟩
  refine ⟨min δf δg, min_pos δf δg hδf_pos hδg_pos, fun ⟨n, Δ, ξ, hr⟩ hd => ?_⟩
  have hdf : Partition.diam Δ < δf :=
    lt_le_trans _ _ _ hd (min_left_le δf δg)
  have hdg : Partition.diam Δ < δg :=
    lt_le_trans _ _ _ hd (min_right_le δf δg)
  show abs (RiemannSum (fun x ↦ f x + g x) Δ ξ - _) < _
  rw [additive_riemann_sum, add_sub_add]
  calc abs (RiemannSum f Δ ξ - if_ + (RiemannSum g Δ ξ - ig))
      ≤ abs (RiemannSum f Δ ξ - if_) + abs (RiemannSum g Δ ξ - ig) :=
        abs_triangle _ _
    _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ (hδf ⟨n, Δ, ξ, hr⟩ hdf) (hδg ⟨n, Δ, ξ, hr⟩ hdg)
    _ = ε := half_add ε

/-- 積分値の符号反転（核補題）。 -/
theorem isintegral_neg {f : Real → Real} {a b i : Real}
    (hi : IsIntegral f a b i) : IsIntegral (fun x ↦ -(f x)) a b (-i) := by
  intro ε hε
  rcases hi ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun ⟨n, Δ, ξ, hr⟩ hd => ?_⟩
  show abs (RiemannSum (fun x ↦ -(f x)) Δ ξ - _) < _
  rw [neg_riemann_sum]
  rw [show -RiemannSum f Δ ξ - -i = -(RiemannSum f Δ ξ - i) from by
        show -RiemannSum f Δ ξ + -(-i) = -(RiemannSum f Δ ξ + -i)
        rw [neg_add_distrib, neg_neg],
      abs_neg]
  exact hδ ⟨n, Δ, ξ, hr⟩ hd

theorem add_integrable (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x + g x) a b := by
  rcases hf with ⟨if_, hif⟩
  rcases hg with ⟨ig, hig⟩
  exact ⟨if_ + ig, isintegral_add hif hig⟩

theorem neg_integrable (f : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b) : IsIntegrable (fun x ↦ -(f x)) a b := by
  rcases hf with ⟨i, hi⟩
  exact ⟨-i, isintegral_neg hi⟩

theorem integrable_sub (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x - g x) a b :=
  add_integrable f (fun x ↦ -(g x)) a b hf (neg_integrable g a b hg)

theorem additive_integral (f g : Real → Real) (a b : Real)
    (hab : a ≤ b) (hf : IsIntegrable f a b) (hg : IsIntegrable g a b) :
    Integral (fun t ↦ f t + g t) a b = Integral f a b + Integral g a b := by
  rcases hf with ⟨if_, hif⟩
  rcases hg with ⟨ig, hig⟩
  rw [IsIntegral_iff _ _ _ _ hab (isintegral_add hif hig),
      IsIntegral_iff _ _ _ _ hab hif, IsIntegral_iff _ _ _ _ hab hig]

theorem neg_integral (f : Real → Real) (a b : Real)
    (hab : a ≤ b) (hf : IsIntegrable f a b) :
    Integral (fun t ↦ -f t) a b = -Integral f a b := by
  rcases hf with ⟨i, hi⟩
  rw [IsIntegral_iff _ _ _ _ hab (isintegral_neg hi), IsIntegral_iff _ _ _ _ hab hi]

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
