import MyProject.Integral.Constant
import MyProject.Integral.Monotone
import MyProject.Integral.Triangle

-- 向き付き積分を定義し、それらに対する基本定理を示す。

-- integral_sub_interval は向きなし積分では一般に成立しないため削除した
-- （区間の加法性は interval_add_integral を使う）
-- integral_triangle_ineq はファイル末尾で証明する

theorem integral_const (a b c : Real) (hab : a ≤ b) : Integral (fun t ↦ c) a b = c * (b - a) := by
  exact IsIntegral_iff _ _ _ _ hab (fun ε hε =>
    ⟨1, zero_lt_one, fun n Δ ξ _ _ => by rw [const_riemann_sum, sub_self, abs_zero]; exact hε⟩)

theorem integral_sub (f g : Real → Real) (a b : Real)
    (hab : a ≤ b) (hf : IsIntegrable f a b) (hg : IsIntegrable g a b) :
    Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by
  exact sub_integral f g a b hab hf hg

theorem integral_monotone' (f g : Real → Real) (a b : Real)
    (hab : a ≤ b)
    (hf : ∃ i, IsIntegral f a b i)
    (hg : ∃ i, IsIntegral g a b i)
    (fnonneg : ∀ x, 0 ≤ f x)
    (gnonneg : ∀ x, 0 ≤ g x)
    (h : ∀ x, InInterval a b x → f x ≤ g x) :
    (Integral f a b).abs ≤ (Integral g a b).abs := by
  have hf_nn : 0 ≤ Integral f a b :=
    integral_nonneg f a b hab (fun x _ => fnonneg x) hf
  have hg_nn : 0 ≤ Integral g a b :=
    integral_nonneg g a b hab (fun x _ => gnonneg x) hg
  rw [nonneg_abs hf_nn, nonneg_abs hg_nn]
  exact integral_monotone f g a b hab h hf hg

-- Helpers for continuous_unif_cont
private theorem abs_lt_of_nonneg_lt {x y : Real} (hx : 0 ≤ x) (hxy : x < y) : x.abs < y := by
  cases Classical.em (x = 0) with
  | inl heq => subst heq; rw [abs_zero]; exact hxy
  | inr hne => rw [pos_abs ⟨hx, fun h => hne h.symm⟩]; exact hxy

private theorem close_to_c_half {s c δ : Real} (hs_le : s ≤ c)
    (hs_gt : c - δ / 2 < s) (hδ : 0 < δ) : (s - c).abs < δ / 2 := by
  have hcs_nn : 0 ≤ c - s := (nonneg_sub_iff s c).mp hs_le
  calc (s - c).abs = (-(c - s)).abs := by rw [neg_sub c s]
    _ = (c - s).abs := abs_neg _
    _ < δ / 2 := abs_lt_of_nonneg_lt hcs_nn (sub_lt_swap hs_gt)

-- Helper: continuous on [a,b] implies uniformly continuous on [a,b]
-- Uses sup axiom: define S(t) = "f is ε-unif cont on [a,t]", show sup S = b
private theorem continuous_unif_cont (f : Real → Real) (a b : Real)
    (hab : a < b) (hf : Continuous f) (ε : Real) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ s t, (a ≤ s ∧ s ≤ b) → (a ≤ t ∧ t ≤ b) →
      (s - t).abs < δ → (f s - f t).abs < ε := by
  -- S(t) := f is ε-uniformly continuous on [a, t]
  let S : Real → Prop := fun t =>
    a ≤ t ∧ t ≤ b ∧ ∃ δ, 0 < δ ∧ ∀ s₁ s₂, (a ≤ s₁ ∧ s₁ ≤ t) → (a ≤ s₂ ∧ s₂ ≤ t) →
      (s₁ - s₂).abs < δ → (f s₁ - f s₂).abs < ε
  have Sa : S a := ⟨le_refl a, hab.1, 1, zero_lt_one, fun s₁ s₂ hs₁ hs₂ _ => by
    rw [show s₁ = a from (LinearOrderedField.le_asymm s₁ a hs₁.2 hs₁.1),
        show s₂ = a from (LinearOrderedField.le_asymm s₂ a hs₂.2 hs₂.1),
        sub_self, abs_zero]; exact hε⟩
  have hne : ∃ x, S x := ⟨a, Sa⟩
  have hbdd : ∃ M, ∀ x, S x → x ≤ M := ⟨b, fun x hx => hx.2.1⟩
  let c := Real.sup S hne hbdd
  have hca : a ≤ c := Real.sup_ub S hne hbdd a Sa
  have hcb : c ≤ b := Real.sup_lub S hne hbdd b (fun x hx => hx.2.1)
  -- Continuity at c gives δ_c
  obtain ⟨δ_c, hδc_pos, hδc⟩ := hf c (ε / 2) (pos_half ε hε)
  -- ∃ t₀ ∈ S close to c (c - δ_c/2 is not an upper bound)
  have ⟨t₀, ht₀S, ht₀_close⟩ : ∃ t₀, S t₀ ∧ ¬(t₀ ≤ c - δ_c / 2) := by
    cases Classical.em (∃ t₀, S t₀ ∧ ¬(t₀ ≤ c - δ_c / 2)) with
    | inl h => exact h
    | inr h =>
      exfalso
      have hall : ∀ t₀, S t₀ → t₀ ≤ c - δ_c / 2 := fun t₀ ht₀ =>
        (Classical.em (t₀ ≤ c - δ_c / 2)).elim id (fun hn => absurd ⟨t₀, ht₀, hn⟩ h)
      have hle := Real.sup_lub S hne hbdd (c - δ_c / 2) hall
      have h0 := (nonneg_iff_le c (c - δ_c / 2)).mp hle
      have hsub : (c - δ_c / 2) - c = -(δ_c / 2) := by
        show (c + -(δ_c / 2)) + -c = -(δ_c / 2)
        calc (c + -(δ_c / 2)) + -c
            = (-(δ_c / 2) + c) + -c := by rw [AddCommGroup.add_comm c (-(δ_c / 2))]
          _ = -(δ_c / 2) + (c + -c) := AddCommGroup.add_assoc _ _ _
          _ = -(δ_c / 2) := by rw [AddCommGroup.add_neg, AddCommGroup.add_zero]
      rw [hsub] at h0
      have : δ_c / 2 ≤ 0 := by
        have h1 := LinearOrderedField.add_le_add (0 : Real) (-(δ_c / 2)) (δ_c / 2) h0
        calc δ_c / 2 = (0 : Real) + δ_c / 2 := (AddCommGroup.zero_add _).symm
          _ ≤ -(δ_c / 2) + δ_c / 2 := h1
          _ = 0 := AddCommGroup.neg_add _
      exact (pos_half δ_c hδc_pos).2 (LinearOrderedField.le_asymm _ _ (pos_half δ_c hδc_pos).1 this)
  have ht₀c : t₀ ≤ c := Real.sup_ub S hne hbdd t₀ ht₀S
  have ht₀_gt : c - δ_c / 2 < t₀ := ne_le_lt _ _ ht₀_close
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := ht₀S.2.2
  let δ' := min δ₀ (δ_c / 2)
  have hδ'_pos : 0 < δ' := min_pos δ₀ (δ_c / 2) hδ₀_pos (pos_half δ_c hδc_pos)
  -- Key: for s₁ s₂ ∈ [a, c] with |s₁-s₂| < δ', |f s₁ - f s₂| < ε
  have unif_on_c : ∀ s₁ s₂, (a ≤ s₁ ∧ s₁ ≤ c) → (a ≤ s₂ ∧ s₂ ≤ c) →
      (s₁ - s₂).abs < δ' → (f s₁ - f s₂).abs < ε := by
    intro s₁ s₂ hs₁ hs₂ hdist
    -- Case split: both ≤ t₀, or at least one > t₀
    cases Classical.em (s₁ ≤ t₀ ∧ s₂ ≤ t₀) with
    | inl hboth =>
      -- Both in [a, t₀]: use δ₀
      exact hδ₀ s₁ s₂ ⟨hs₁.1, hboth.1⟩ ⟨hs₂.1, hboth.2⟩
        (lt_le_trans _ _ _ hdist (min_left_le δ₀ (δ_c / 2)))
    | inr hnotboth =>
      -- At least one > t₀: both within δ_c of c, use triangle through f(c)
      -- First show both s₁, s₂ are within δ_c of c
      have hdist_le : (s₁ - s₂).abs < δ_c / 2 :=
        lt_le_trans _ _ _ hdist (min_right_le δ₀ (δ_c / 2))
      -- At least one of s₁, s₂ > t₀. That one is close to c.
      -- The other is close to it (by hdist), hence close to c.
      -- Both within δ_c of c.
      have h_s1_close : (s₁ - c).abs < δ_c := by
        cases Classical.em (s₁ ≤ t₀) with
        | inr hs₁_gt =>
          -- s₁ > t₀ > c - δ_c/2, so close to c
          exact lt_trans _ _ _ (close_to_c_half hs₁.2
            (lt_trans _ _ _ ht₀_gt (ne_le_lt _ _ hs₁_gt)) hδc_pos) (half_lt hδc_pos)
        | inl hs₁_le =>
          -- s₂ > t₀ (since ¬both ≤ t₀)
          have hs₂_gt : ¬(s₂ ≤ t₀) := fun h => hnotboth ⟨hs₁_le, h⟩
          have h_s2_half := close_to_c_half hs₂.2
            (lt_trans _ _ _ ht₀_gt (ne_le_lt _ _ hs₂_gt)) hδc_pos
          -- |s₁ - c| ≤ |s₁ - s₂| + |s₂ - c| < δ_c/2 + δ_c/2 = δ_c
          calc (s₁ - c).abs = ((s₂ - c) + (s₁ - s₂)).abs := by rw [telescope_2 c s₁ s₂]
            _ ≤ (s₂ - c).abs + (s₁ - s₂).abs := abs_triangle _ _
            _ < δ_c / 2 + δ_c / 2 := lt_add_lt _ _ _ _ h_s2_half hdist_le
            _ = δ_c := half_add δ_c
      have h_s2_close : (s₂ - c).abs < δ_c := by
        cases Classical.em (s₂ ≤ t₀) with
        | inr hs₂_gt =>
          exact lt_trans _ _ _ (close_to_c_half hs₂.2
            (lt_trans _ _ _ ht₀_gt (ne_le_lt _ _ hs₂_gt)) hδc_pos) (half_lt hδc_pos)
        | inl hs₂_le =>
          have hs₁_gt : ¬(s₁ ≤ t₀) := fun h => hnotboth ⟨h, hs₂_le⟩
          have h_s1_half := close_to_c_half hs₁.2
            (lt_trans _ _ _ ht₀_gt (ne_le_lt _ _ hs₁_gt)) hδc_pos
          calc (s₂ - c).abs = ((s₁ - c) + (s₂ - s₁)).abs := by rw [telescope_2 c s₂ s₁]
            _ ≤ (s₁ - c).abs + (s₂ - s₁).abs := abs_triangle _ _
            _ = (s₁ - c).abs + (s₁ - s₂).abs := by
                rw [show s₂ - s₁ = -(s₁ - s₂) from (neg_sub s₁ s₂).symm, abs_neg]
            _ < δ_c / 2 + δ_c / 2 := lt_add_lt _ _ _ _ h_s1_half hdist_le
            _ = δ_c := half_add δ_c
      -- Triangle: f s₁ - f s₂ = (f s₁ - f c) + (f c - f s₂)
      have hf1 := hδc s₁ h_s1_close
      have hf2 := hδc s₂ h_s2_close
      have hsplit : f s₁ - f s₂ = (f s₁ - f c) + (f c - f s₂) := by
        rw [show f c - f s₂ = -(f s₂ - f c) from (neg_sub (f s₂) (f c)).symm]
        rw [show f s₁ - f c + -(f s₂ - f c) = f s₁ - f c - (f s₂ - f c) from rfl]
        rw [show f s₁ - f s₂ = (f s₁ - f c) - (f s₂ - f c) from by
          show f s₁ + -(f s₂) = (f s₁ + -(f c)) + -((f s₂) + -(f c))
          rw [neg_add_distrib, neg_neg,
              show f s₁ + -(f c) + (-(f s₂) + f c) =
                   f s₁ + (-(f c) + (-(f s₂) + f c)) from AddCommGroup.add_assoc _ _ _,
              show -(f c) + (-(f s₂) + f c) = -(f s₂) from by
                rw [AddCommGroup.add_comm (-(f s₂)) (f c),
                    show -(f c) + (f c + -(f s₂)) = (-(f c) + f c) + -(f s₂) from
                      (AddCommGroup.add_assoc _ _ _).symm,
                    AddCommGroup.neg_add, AddCommGroup.zero_add]]]
      calc (f s₁ - f s₂).abs
          = ((f s₁ - f c) + (f c - f s₂)).abs := by rw [hsplit]
          _ ≤ (f s₁ - f c).abs + (f c - f s₂).abs := abs_triangle _ _
          _ = (f s₁ - f c).abs + (f s₂ - f c).abs := by
              rw [show f c - f s₂ = -(f s₂ - f c) from (neg_sub (f s₂) (f c)).symm, abs_neg]
          _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ hf1 hf2
          _ = ε := half_add ε
  -- Helper: a < b, c ≤ d → a + c < b + d
  have lt_add_le' : ∀ {a' b' c' d' : Real}, a' < b' → c' ≤ d' → a' + c' < b' + d' := by
    intro a' b' c' d' hab' hcd'
    calc a' + c' ≤ a' + d' := add_left_le a' c' d' hcd'
      _ < b' + d' := by
        rw [AddCommGroup.add_comm a' d', AddCommGroup.add_comm b' d']
        exact add_left_lt d' a' b' hab'
  -- Show c = b by contradiction
  have hcb_eq : c = b := by
    cases Classical.em (c = b) with
    | inl h => exact h
    | inr hne_cb =>
      exfalso
      have hclt : c < b := ⟨hcb, hne_cb⟩
      have hbc_pos : 0 < b - c := (pos_sub_iff c b).mp hclt
      let η := min δ' (min (δ_c / 2) ((b - c) / 2))
      have hη_pos : 0 < η :=
        min_pos _ _ hδ'_pos (min_pos _ _ (pos_half δ_c hδc_pos) (pos_half (b - c) hbc_pos))
      have hη_le_δc2 : η ≤ δ_c / 2 :=
        le_trans (min_right_le δ' _) (min_left_le _ _)
      have hδ'_le_δc2 : δ' ≤ δ_c / 2 := min_right_le δ₀ (δ_c / 2)
      -- (c + η) + -c = η (avoids HSub/HAdd mismatch in rw)
      have add_neg_cancel_η : (c + η) + -c = η := by
        calc (c + η) + -c = c + (η + -c) := AddCommGroup.add_assoc c η (-c)
          _ = c + (-c + η) := by rw [AddCommGroup.add_comm η (-c)]
          _ = (c + -c) + η := (AddCommGroup.add_assoc c (-c) η).symm
          _ = η := by rw [AddCommGroup.add_neg, AddCommGroup.zero_add]
      -- c + η ≤ b
      have hcη_le_b : c + η ≤ b := by
        have hη_le_bc : η ≤ b - c :=
          le_trans (le_trans (min_right_le δ' _) (min_right_le _ _)) (half_lt hbc_pos).1
        have h1 := add_left_le c η (b - c) hη_le_bc
        rw [add_sub_cancel' c b] at h1; exact h1
      -- a ≤ c + η
      have ha_le_cη : a ≤ c + η := le_trans hca (by
        have := add_left_le c 0 η hη_pos.1
        rw [add_zero c] at this; exact this)
      -- Helper: s ∈ [c, c+η] → |s - c| ≤ δ_c / 2
      have close_ext : ∀ s, c ≤ s → s ≤ c + η → (s - c).abs ≤ δ_c / 2 := by
        intro s hsc hscη
        have hnn : 0 ≤ s - c := (nonneg_sub_iff c s).mp hsc
        have hle : s - c ≤ η := by
          have h1 := LinearOrderedField.add_le_add s (c + η) (-c) hscη
          rw [add_neg_cancel_η] at h1; exact h1
        rw [nonneg_abs hnn]
        exact le_trans hle hη_le_δc2
      -- S(c + η) holds
      have hSext : S (c + η) := ⟨ha_le_cη, hcη_le_b, δ', hδ'_pos, fun s₁ s₂ hs₁ hs₂ hdist => by
        cases Classical.em (s₁ ≤ c ∧ s₂ ≤ c) with
        | inl hboth =>
          exact unif_on_c s₁ s₂ ⟨hs₁.1, hboth.1⟩ ⟨hs₂.1, hboth.2⟩ hdist
        | inr hnotboth =>
          -- At least one > c: both within δ_c of c, triangle through f(c)
          have h_s1_close : (s₁ - c).abs < δ_c := by
            cases Classical.em (s₁ ≤ c) with
            | inr hs₁_gt =>
              have hc_le := not_lt_imp_le (fun hlt => hs₁_gt hlt.1)
              calc (s₁ - c).abs ≤ δ_c / 2 := close_ext s₁ hc_le hs₁.2
                _ < δ_c := half_lt hδc_pos
            | inl hs₁_le =>
              have hs₂_gt : ¬(s₂ ≤ c) := fun h => hnotboth ⟨hs₁_le, h⟩
              have hc_le_s₂ := not_lt_imp_le (fun hlt => hs₂_gt hlt.1)
              calc (s₁ - c).abs
                  = ((s₂ - c) + (s₁ - s₂)).abs := by rw [telescope_2 c s₁ s₂]
                _ ≤ (s₂ - c).abs + (s₁ - s₂).abs := abs_triangle _ _
                _ < δ_c / 2 + δ_c / 2 := by
                    rw [AddCommGroup.add_comm ((s₂ - c).abs) ((s₁ - s₂).abs)]
                    exact lt_add_le' (lt_le_trans _ _ _ hdist hδ'_le_δc2)
                      (close_ext s₂ hc_le_s₂ hs₂.2)
                _ = δ_c := half_add δ_c
          have h_s2_close : (s₂ - c).abs < δ_c := by
            cases Classical.em (s₂ ≤ c) with
            | inr hs₂_gt =>
              have hc_le := not_lt_imp_le (fun hlt => hs₂_gt hlt.1)
              calc (s₂ - c).abs ≤ δ_c / 2 := close_ext s₂ hc_le hs₂.2
                _ < δ_c := half_lt hδc_pos
            | inl hs₂_le =>
              have hs₁_gt : ¬(s₁ ≤ c) := fun h => hnotboth ⟨h, hs₂_le⟩
              have hc_le_s₁ := not_lt_imp_le (fun hlt => hs₁_gt hlt.1)
              calc (s₂ - c).abs
                  = ((s₁ - c) + (s₂ - s₁)).abs := by rw [telescope_2 c s₂ s₁]
                _ ≤ (s₁ - c).abs + (s₂ - s₁).abs := abs_triangle _ _
                _ = (s₁ - c).abs + (s₁ - s₂).abs := by
                    rw [show s₂ - s₁ = -(s₁ - s₂) from (neg_sub s₁ s₂).symm, abs_neg]
                _ < δ_c / 2 + δ_c / 2 := by
                    rw [AddCommGroup.add_comm ((s₁ - c).abs) ((s₁ - s₂).abs)]
                    exact lt_add_le' (lt_le_trans _ _ _ hdist hδ'_le_δc2)
                      (close_ext s₁ hc_le_s₁ hs₁.2)
                _ = δ_c := half_add δ_c
          -- Triangle: |f s₁ - f s₂| ≤ |f s₁ - f c| + |f c - f s₂| < ε
          have hf1 := hδc s₁ h_s1_close
          have hf2 := hδc s₂ h_s2_close
          calc (f s₁ - f s₂).abs
              = ((f c - f s₂) + (f s₁ - f c)).abs := by rw [telescope_2 (f s₂) (f s₁) (f c)]
            _ ≤ (f c - f s₂).abs + (f s₁ - f c).abs := abs_triangle _ _
            _ = (f s₂ - f c).abs + (f s₁ - f c).abs := by
                rw [show f c - f s₂ = -(f s₂ - f c) from (neg_sub (f s₂) (f c)).symm, abs_neg]
            _ = (f s₁ - f c).abs + (f s₂ - f c).abs := by
                rw [AddCommGroup.add_comm ((f s₂ - f c).abs) ((f s₁ - f c).abs)]
            _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ hf1 hf2
            _ = ε := half_add ε⟩
      -- c + η ≤ sup S = c, but c + η > c: contradiction
      have hle_sup := Real.sup_ub S hne hbdd (c + η) hSext
      have hlt : c < c + η := by
        have := add_left_lt c 0 η hη_pos
        rw [add_zero c] at this; exact this
      exact hlt.2 (LinearOrderedField.le_asymm c (c + η) hlt.1 hle_sup)
  -- Conclude
  exact ⟨δ', hδ'_pos, fun s t hs ht hdist =>
    unif_on_c s t ⟨hs.1, hcb_eq ▸ hs.2⟩ ⟨ht.1, hcb_eq ▸ ht.2⟩ hdist⟩

-- Helper: continuous on [a,b] implies bounded on [a,b]
-- Uses uniform continuity + chain induction
private theorem continuous_bounded (f : Real → Real) (a b : Real)
    (hab : a < b) (hf : Continuous f) :
    ∃ M : Real, 0 < M ∧ ∀ t, InInterval a b t → (f t).abs ≤ M := by
  obtain ⟨δ, hδ_pos, huc⟩ := continuous_unif_cont f a b hab hf 1 zero_lt_one
  have hδ2_pos : 0 < δ / 2 := pos_half δ hδ_pos
  have hδ2_ne : δ / 2 ≠ 0 := fun h => hδ2_pos.2 h.symm
  have hab' : a ≤ b := hab.1
  have hba_pos : 0 < b - a := (pos_sub_iff a b).mp hab
  let N := ceil ((b - a) / (δ / 2))
  have hN_lt : (b - a) / (δ / 2) < (N : Real) := ceil_lt _
  -- b - a < N * (δ/2) via div cancellation
  have hdiv_cancel : (b - a) / (δ / 2) * (δ / 2) = b - a := by
    show (b - a) * Field.inv (δ / 2) * (δ / 2) = b - a
    rw [MulCommMonoid.mul_assoc]
    have : Field.inv (δ / 2) * (δ / 2) = (1 : Real) := by
      rw [MulCommMonoid.mul_comm]; exact Field.mul_inv _ hδ2_ne
    rw [this]
    exact MulCommMonoid.mul_one _
  have hba_lt : b - a < (N : Real) * (δ / 2) := by
    have h := mul_right_lt _ (↑N) (δ / 2) hδ2_pos hN_lt
    rw [hdiv_cancel] at h; exact h
  have hN_bound : b ≤ a + (N : Real) * (δ / 2) := by
    have h := add_left_lt a _ _ hba_lt
    rw [show a + (b - a) = b from add_sub_cancel' a b] at h; exact h.1
  -- Chain induction: t ≤ a + k*(δ/2) → |f(t) - f(a)| ≤ k
  have chain : ∀ (k : Nat), ∀ t, a ≤ t → t ≤ b →
      t ≤ a + (k : Real) * (δ / 2) → (f t - f a).abs ≤ (k : Real) := by
    intro k; induction k with
    | zero =>
      intro t hat _htb htk
      rw [show ((0 : Nat) : Real) = (0 : Real) from rfl, zero_mul', add_zero] at htk
      have heq : t = a := LinearOrderedField.le_asymm _ _ htk hat
      subst heq; rw [sub_self, abs_zero]; exact le_refl 0
    | succ k ih =>
      intro t hat htb htk1
      have hsucc : ((k + 1 : Nat) : Real) = (k : Real) + 1 := by
        show (Nat.cast (k + 1) : Real) = (Nat.cast k : Real) + 1
        show Real.ofNat (k + 1) = Real.ofNat k + 1
        exact succ_ofNat k
      cases Classical.em (t ≤ a + (k : Real) * (δ / 2)) with
      | inl hle =>
        exact le_trans (ih t hat htb hle)
          (Real.le_of_lt (cast_lt k (k + 1) (Nat.lt_succ_self k)))
      | inr hgt =>
        have hs_lt_t : a + (k : Real) * (δ / 2) < t := by
          cases LinearOrderedField.le_total t (a + (k : Real) * (δ / 2)) with
          | inl h => exact absurd h hgt
          | inr h => exact ⟨h, fun heq => hgt (heq ▸ le_refl _)⟩
        have has : a ≤ a + (k : Real) * (δ / 2) := by
          have h := add_left_le a 0 ((k : Real) * (δ / 2))
            (mul_nonneg _ _ (cast_nonneg k) hδ2_pos.1)
          rw [add_zero] at h; exact h
        have hsb : a + (k : Real) * (δ / 2) ≤ b := le_trans hs_lt_t.1 htb
        -- |t - s| ≤ δ/2 < δ
        have hts_nn : 0 ≤ t - (a + (k : Real) * (δ / 2)) :=
          (nonneg_sub_iff _ t).mp hs_lt_t.1
        have hts_le : t - (a + (k : Real) * (δ / 2)) ≤ δ / 2 := by
          rw [hsucc, add_mul, one_mul,
              (AddCommGroup.add_assoc a ((k : Real) * (δ / 2)) (δ / 2)).symm] at htk1
          have h := LinearOrderedField.add_le_add t _
            (-(a + (k : Real) * (δ / 2))) htk1
          have hc : a + (k : Real) * (δ / 2) + δ / 2 + -(a + (k : Real) * (δ / 2)) = δ / 2 :=
            add_sub_cancel (a + (k : Real) * (δ / 2)) (δ / 2)
          rw [hc] at h; exact h
        have hdist : (t - (a + (k : Real) * (δ / 2))).abs < δ :=
          le_lt_trans (by rw [nonneg_abs hts_nn]; exact hts_le) (half_lt hδ_pos)
        -- UC + IH + triangle
        have h_uc := huc t (a + (k : Real) * (δ / 2)) ⟨hat, htb⟩ ⟨has, hsb⟩ hdist
        have h_ih := ih (a + (k : Real) * (δ / 2)) has hsb (le_refl _)
        have h_tri : (f t - f a).abs ≤
            (f (a + (k : Real) * (δ / 2)) - f a).abs +
            (f t - f (a + (k : Real) * (δ / 2))).abs := by
          rw [telescope_2 (f a) (f t) (f (a + (k : Real) * (δ / 2)))]
          exact abs_triangle _ _
        have h_lt : (f (a + (k : Real) * (δ / 2)) - f a).abs +
            (f t - f (a + (k : Real) * (δ / 2))).abs < (k : Real) + 1 :=
          le_lt_trans
            (LinearOrderedField.add_le_add _ _
              (f t - f (a + (k : Real) * (δ / 2))).abs h_ih)
            (add_left_lt (k : Real) _ _ h_uc)
        rw [hsucc.symm] at h_lt
        exact (le_lt_trans h_tri h_lt).1
  -- Conclude: M = N + |f(a)| + 1
  refine ⟨(N : Real) + (f a).abs + 1, ?_, ?_⟩
  · have h_nn : (0 : Real) ≤ (N : Real) + (f a).abs := by
      have h := add_left_le (N : Real) 0 (f a).abs abs_nonneg
      rw [add_zero] at h; exact le_trans (cast_nonneg N) h
    exact le_lt_trans h_nn (by
      have h := add_left_lt ((N : Real) + (f a).abs) 0 1 zero_lt_one
      rw [add_zero] at h; exact h)
  · intro t ht
    have ht' : a ≤ t ∧ t ≤ b := by
      unfold InInterval at ht; rw [if_pos hab'] at ht; exact ht
    have hchain := chain N t ht'.1 ht'.2 (le_trans ht'.2 hN_bound)
    have h_split : (f t).abs ≤ (f t - f a).abs + (f a).abs := by
      have h1 : (f t).abs = ((f t - f a) + f a).abs := by
        congr 1
        have h := add_sub_cancel' (f a) (f t)
        rw [AddCommGroup.add_comm] at h; exact h.symm
      rw [h1]; exact abs_triangle _ _
    exact (le_lt_trans
      (le_trans h_split (LinearOrderedField.add_le_add _ _ _ hchain))
      (by have h := add_left_lt ((N : Real) + (f a).abs) 0 1 zero_lt_one
          rw [add_zero] at h; exact h)).1

-- Helper: RS with same partition but different repr points differ by at most C*(b-a)
private theorem same_partition_bound (f : Real → Real) (a b C : Real)
    (n : Nat) (Δ : Partition n a b) (ξ ξ' : Range n → Real)
    (hclose : ∀ i, (f (ξ i) - f (ξ' i)).abs ≤ C) :
    (RiemannSum f a b n Δ ξ - RiemannSum f a b n Δ ξ').abs ≤ C * (b - a) := by
  -- Step 1: for each i, f(ξ_i)*len_i ≤ f(ξ'_i)*len_i + C*len_i
  have h_term : ∀ i : Range n,
      f (ξ i) * Δ.length i ≤ f (ξ' i) * Δ.length i + C * Δ.length i := by
    intro i
    have h1 : f (ξ i) ≤ f (ξ' i) + C := by
      have h2 := le_trans (le_abs _) (hclose i)
      have h3 := add_left_le (f (ξ' i)) (f (ξ i) - f (ξ' i)) C h2
      rw [add_sub_cancel' (f (ξ' i)) (f (ξ i))] at h3; exact h3
    have h4 := nonneg_mul_nonneg _ _ _ (Δ.length_nonneg n a b i) h1
    rw [add_mul] at h4; exact h4
  -- Step 2: sum gives RS(ξ) ≤ RS(ξ') + C*(b-a)
  have h_upper : RiemannSum f a b n Δ ξ ≤ RiemannSum f a b n Δ ξ' + C * (b - a) := by
    have h5 := summation_le n _ _ h_term
    rw [addtive_summation, summation_smul, Partition.length_sum] at h5
    exact h5
  -- Step 3: symmetric bound gives RS(ξ') ≤ RS(ξ) + C*(b-a)
  have h_term' : ∀ i : Range n,
      f (ξ' i) * Δ.length i ≤ f (ξ i) * Δ.length i + C * Δ.length i := by
    intro i
    have h1 : f (ξ' i) ≤ f (ξ i) + C := by
      have h2 : (f (ξ' i) - f (ξ i)).abs ≤ C := by
        rw [show f (ξ' i) - f (ξ i) = -(f (ξ i) - f (ξ' i)) from (neg_sub _ _).symm,
            abs_neg]; exact hclose i
      have h3 := le_trans (le_abs _) h2
      have h4 := add_left_le (f (ξ i)) (f (ξ' i) - f (ξ i)) C h3
      rw [add_sub_cancel' (f (ξ i)) (f (ξ' i))] at h4; exact h4
    have h5 := nonneg_mul_nonneg _ _ _ (Δ.length_nonneg n a b i) h1
    rw [add_mul] at h5; exact h5
  have h_lower : RiemannSum f a b n Δ ξ' ≤ RiemannSum f a b n Δ ξ + C * (b - a) := by
    have h6 := summation_le n _ _ h_term'
    rw [addtive_summation, summation_smul, Partition.length_sum] at h6; exact h6
  -- Step 4: combine using abs_le
  apply abs_le
  -- -(RS(ξ) - RS(ξ')) ≤ C*(b-a), i.e., RS(ξ') - RS(ξ) ≤ C*(b-a)
  · rw [neg_sub (RiemannSum f a b n Δ ξ) (RiemannSum f a b n Δ ξ')]
    have h7 := add_left_le (-(RiemannSum f a b n Δ ξ)) (RiemannSum f a b n Δ ξ')
        (RiemannSum f a b n Δ ξ + C * (b - a)) h_lower
    have h8 : -(RiemannSum f a b n Δ ξ) + (RiemannSum f a b n Δ ξ + C * (b - a))
        = C * (b - a) := by
      rw [← AddCommGroup.add_assoc, AddCommGroup.add_comm (-(RiemannSum f a b n Δ ξ))
          (RiemannSum f a b n Δ ξ), AddCommGroup.add_neg, AddCommGroup.zero_add]
    rw [AddCommGroup.add_comm, h8] at h7; exact h7
  -- RS(ξ) - RS(ξ') ≤ C*(b-a)
  · have h7 := add_left_le (-(RiemannSum f a b n Δ ξ')) (RiemannSum f a b n Δ ξ)
        (RiemannSum f a b n Δ ξ' + C * (b - a)) h_upper
    have h8 : -(RiemannSum f a b n Δ ξ') + (RiemannSum f a b n Δ ξ' + C * (b - a))
        = C * (b - a) := by
      rw [← AddCommGroup.add_assoc, AddCommGroup.add_comm (-(RiemannSum f a b n Δ ξ'))
          (RiemannSum f a b n Δ ξ'), AddCommGroup.add_neg, AddCommGroup.zero_add]
    rw [AddCommGroup.add_comm, h8] at h7; exact h7

-- Helper: |RS(f)| ≤ M*(b-a) when |f| ≤ M on [a,b]
private theorem rs_abs_bound (f : Real → Real) (a b M : Real)
    (hbound : ∀ t, InInterval a b t → (f t).abs ≤ M)
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr a b n ξ) :
    (RiemannSum f a b n Δ ξ).abs ≤ M * (b - a) := by
  apply abs_le
  · -- -(RS f) ≤ M*(b-a)
    have h0 : -(RiemannSum f a b n Δ ξ) = RiemannSum (fun t => -f t) a b n Δ ξ :=
      (neg_riemann_sum f a b n Δ ξ).symm
    rw [h0]
    have h1 : RiemannSum (fun t => -f t) a b n Δ ξ ≤ RiemannSum (fun _ => M) a b n Δ ξ := by
      apply summation_le; intro i
      apply nonneg_mul_nonneg _ _ _ (Δ.length_nonneg n a b i)
      exact le_trans (neg_le_abs _) (hbound (ξ i) (Δ.repr_in_interval a b n ξ hr i))
    rw [const_riemann_sum] at h1; exact h1
  · -- RS f ≤ M*(b-a)
    have h1 : RiemannSum f a b n Δ ξ ≤ RiemannSum (fun _ => M) a b n Δ ξ := by
      apply summation_le; intro i
      apply nonneg_mul_nonneg _ _ _ (Δ.length_nonneg n a b i)
      exact le_trans (le_abs _) (hbound (ξ i) (Δ.repr_in_interval a b n ξ hr i))
    rw [const_riemann_sum] at h1; exact h1

-- ============================================================
-- continuous_integrable 用の細分比較補題群
-- ============================================================

-- 区分定数関数の原始関数：G(t) = Σ_i f(ξ_i)·(min t p_{i+1} − min t p_i)
private noncomputable def stepAnti (f : Real → Real) (n : Nat) (a b : Real)
    (Δ : Partition n a b) (ξ : Range n → Real) (t : Real) : Real :=
  Sumation n (fun i => f (ξ i) *
    (min t (Δ.points (Range.addone i)) - min t (Δ.points (Range.incl i))))

-- 同一小区間 [p_σ, p_{σ+1}] 内の c ≤ d に対する増分
private theorem stepAnti_inc (f : Real → Real) (n : Nat) (a b : Real)
    (Δ : Partition n a b) (ξ : Range n → Real) (σ : Range n) (c d : Real)
    (hc : Δ.points (Range.incl σ) ≤ c) (hcd : c ≤ d)
    (hd : d ≤ Δ.points (Range.addone σ)) :
    stepAnti f n a b Δ ξ d - stepAnti f n a b Δ ξ c = f (ξ σ) * (d - c) := by
  have hterm : ∀ i : Range n,
      f (ξ i) * (min d (Δ.points (Range.addone i)) - min d (Δ.points (Range.incl i))) -
      f (ξ i) * (min c (Δ.points (Range.addone i)) - min c (Δ.points (Range.incl i))) =
      (if i.val = σ.val then f (ξ σ) * (d - c) else 0) := by
    intro i
    by_cases hiσ : i.val = σ.val
    · rw [if_pos hiσ]
      have hi : i = σ := Subtype.ext hiσ
      rw [hi, min_eq_left hd, min_eq_right (le_trans hc hcd),
          min_eq_left (le_trans hcd hd), min_eq_right hc,
          MulCommMonoid.mul_comm (f (ξ σ)) (d - Δ.points (Range.incl σ)),
          MulCommMonoid.mul_comm (f (ξ σ)) (c - Δ.points (Range.incl σ)),
          mul_sub_mul,
          show d - Δ.points (Range.incl σ) - (c - Δ.points (Range.incl σ)) = d - c from by
            show d + -Δ.points (Range.incl σ) - (c + -Δ.points (Range.incl σ)) = d - c
            rw [add_sub_add, sub_self, add_zero],
          MulCommMonoid.mul_comm]
    · rw [if_neg hiσ]
      by_cases hlt : i.val < σ.val
      · -- 小区間 i は [P,Q] の左側
        have h1 : Δ.points (Range.addone i) ≤ c :=
          le_trans (Partition.points_mono n a b Δ (Range.addone i) (Range.incl σ)
            (by simp only [Range.addone_val, Range.incl_val]; omega)) hc
        have h2 : Δ.points (Range.incl i) ≤ c := le_trans (Δ.increase i) h1
        have h1d : Δ.points (Range.addone i) ≤ d := le_trans h1 hcd
        have h2d : Δ.points (Range.incl i) ≤ d := le_trans h2 hcd
        rw [min_eq_right h1d, min_eq_right h2d, min_eq_right h1, min_eq_right h2,
            sub_self]
      · -- 小区間 i は [P,Q] の右側
        have h1 : d ≤ Δ.points (Range.incl i) :=
          le_trans hd (Partition.points_mono n a b Δ (Range.addone σ) (Range.incl i)
            (by simp only [Range.addone_val, Range.incl_val]; omega))
        have h2 : d ≤ Δ.points (Range.addone i) := le_trans h1 (Δ.increase i)
        have h1c : c ≤ Δ.points (Range.incl i) := le_trans hcd h1
        have h2c : c ≤ Δ.points (Range.addone i) := le_trans hcd h2
        rw [min_eq_left h2, min_eq_left h1, min_eq_left h2c, min_eq_left h1c,
            sub_self d, sub_self c,
            show f (ξ i) * (0 : Real) = 0 from by
              rw [MulCommMonoid.mul_comm]; exact zero_mul' _,
            sub_self]
  calc stepAnti f n a b Δ ξ d - stepAnti f n a b Δ ξ c
      = Sumation n (fun i =>
          f (ξ i) * (min d (Δ.points (Range.addone i)) - min d (Δ.points (Range.incl i))) -
          f (ξ i) * (min c (Δ.points (Range.addone i)) - min c (Δ.points (Range.incl i)))) :=
        sub_summation n _ _
    _ = Sumation n (fun i => if i.val = σ.val then f (ξ σ) * (d - c) else 0) :=
        summation_congr n _ _ hterm
    _ = (if σ.val = σ.val then f (ξ σ) * (d - c) else 0) :=
        summation_one_term n σ _ (fun i hne => if_neg hne)
    _ = f (ξ σ) * (d - c) := if_pos rfl

-- 細分上で親区間の代表点を使った RS は元の RS に等しい
private theorem rs_refine_eq (f : Real → Real) (a b : Real)
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (N : Nat) (Δ' : Partition N a b) (σ : Range N → Range n)
    (hσ : ∀ j : Range N,
      Δ.points (Range.incl (σ j)) ≤ Δ'.points (Range.incl j) ∧
      Δ'.points (Range.addone j) ≤ Δ.points (Range.addone (σ j))) :
    RiemannSum f a b N Δ' (fun j => ξ (σ j)) = RiemannSum f a b n Δ ξ := by
  have hGb : stepAnti f n a b Δ ξ b = RiemannSum f a b n Δ ξ := by
    apply summation_congr
    intro i
    rw [min_eq_right (Partition.point_le_right n a b Δ (Range.addone i)),
        min_eq_right (Partition.point_le_right n a b Δ (Range.incl i))]
    rfl
  have hGa : stepAnti f n a b Δ ξ a = 0 := by
    have hz : ∀ i : Range n, f (ξ i) *
        (min a (Δ.points (Range.addone i)) - min a (Δ.points (Range.incl i))) = 0 := by
      intro i
      rw [min_eq_left (Partition.left_le_point n a b Δ (Range.addone i)),
          min_eq_left (Partition.left_le_point n a b Δ (Range.incl i)), sub_self,
          MulCommMonoid.mul_comm]
      exact zero_mul' _
    calc stepAnti f n a b Δ ξ a
        = Sumation n (fun _ => (0 : Real)) := summation_congr n _ _ hz
      _ = 0 := summation_all_zero n
  have hjterm : ∀ j : Range N,
      f (ξ (σ j)) * Partition.length N a b Δ' j =
      stepAnti f n a b Δ ξ (Δ'.points (Range.addone j)) -
      stepAnti f n a b Δ ξ (Δ'.points (Range.incl j)) := fun j =>
    (stepAnti_inc f n a b Δ ξ (σ j) (Δ'.points (Range.incl j)) (Δ'.points (Range.addone j))
      (hσ j).1 (Δ'.increase j) (hσ j).2).symm
  calc RiemannSum f a b N Δ' (fun j => ξ (σ j))
      = Sumation N (fun j => stepAnti f n a b Δ ξ (Δ'.points (Range.addone j)) -
                             stepAnti f n a b Δ ξ (Δ'.points (Range.incl j))) :=
        summation_congr N _ _ hjterm
    _ = stepAnti f n a b Δ ξ (Δ'.points ⟨N, Nat.lt_add_one N⟩) -
        stepAnti f n a b Δ ξ (Δ'.points ⟨0, Nat.zero_lt_succ N⟩) :=
        telescope_sum N (fun r => stepAnti f n a b Δ ξ (Δ'.points r))
    _ = stepAnti f n a b Δ ξ b - stepAnti f n a b Δ ξ a := by rw [Δ'.right, Δ'.left]
    _ = RiemannSum f a b n Δ ξ - 0 := by rw [hGb, hGa]
    _ = RiemannSum f a b n Δ ξ := sub_zero _

-- Δ の全分点が Δ'' の分点に含まれるなら、Δ'' の各小区間は Δ のある小区間に含まれる
private theorem refine_parent (a b : Real) (n N : Nat) (hn : 0 < n)
    (Δ : Partition n a b) (Δ'' : Partition N a b)
    (hpts : ∀ i : Range n.succ, ∃ p : Range N.succ, Δ''.points p = Δ.points i) :
    ∀ j : Range N, ∃ k : Range n,
      Δ.points (Range.incl k) ≤ Δ''.points (Range.incl j) ∧
      Δ''.points (Range.addone j) ≤ Δ.points (Range.addone k) := by
  intro j
  let p : Nat → Prop := fun i =>
    ∃ h : i < n, Δ''.points (Range.addone j) ≤ Δ.points ⟨i + 1, Nat.succ_lt_succ h⟩
  have hp : ∃ i, p i := by
    have hn' : n - 1 < n := Nat.pred_lt (Nat.not_eq_zero_of_lt hn)
    refine ⟨n - 1, hn', ?_⟩
    have heq : (⟨n - 1 + 1, Nat.succ_lt_succ hn'⟩ : Range n.succ) = ⟨n, Nat.lt_succ_self n⟩ :=
      Subtype.ext (Nat.succ_pred_eq_of_pos hn)
    rw [heq, Δ.right]
    exact Partition.point_le_right N a b Δ'' (Range.addone j)
  rcases has_min p hp with ⟨k, ⟨hkn, hkle⟩, hmin⟩
  refine ⟨⟨k, hkn⟩, ?_, hkle⟩
  show Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ ≤ Δ''.points (Range.incl j)
  cases Classical.em (k = 0) with
  | inl hk0 =>
    subst hk0
    rw [Δ.left]
    exact Partition.left_le_point N a b Δ'' (Range.incl j)
  | inr hk_ne =>
    have hk_pos : 0 < k := Nat.zero_lt_of_ne_zero hk_ne
    have hkm1_lt : k - 1 < n := Nat.lt_of_lt_of_le (Nat.pred_lt hk_ne) (Nat.le_of_lt hkn)
    have not_pk : ¬ p (k - 1) := fun hpk => hmin (k - 1) hpk (Nat.pred_lt hk_ne)
    have hlt : Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ < Δ''.points (Range.addone j) := by
      have h1 : ¬ (Δ''.points (Range.addone j) ≤
          Δ.points ⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩) :=
        fun hle => not_pk ⟨hkm1_lt, hle⟩
      have heq : (⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩ : Range n.succ) =
          ⟨k, Nat.lt_succ_of_lt hkn⟩ := Subtype.ext (Nat.succ_pred_eq_of_pos hk_pos)
      rw [heq] at h1
      exact ne_le_lt _ _ h1
    obtain ⟨r, hr⟩ := hpts ⟨k, Nat.lt_succ_of_lt hkn⟩
    cases Nat.lt_or_ge j.val r.val with
    | inl hjr =>
      exfalso
      have h2 : Δ''.points (Range.addone j) ≤ Δ''.points r :=
        Partition.points_mono N a b Δ'' (Range.addone j) r hjr
      rw [hr] at h2
      exact (le_lt_trans h2 hlt).2 rfl
    | inr hrj =>
      rw [← hr]
      exact Partition.points_mono N a b Δ'' r (Range.incl j) hrj

-- 核心補題：固定した細かい分割 Δ に対し、十分細かい任意の Δ' の RS は RS(Δ) に近い
private theorem rs_compare (f : Real → Real) (a b M : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (hM_pos : 0 < M)
    (hab : a < b) (ε' θ : Real) (hε' : 0 < ε') (hθ : 0 < θ)
    (δuc : Real) (hδuc : 0 < δuc)
    (huc : ∀ s t, (a ≤ s ∧ s ≤ b) → (a ≤ t ∧ t ≤ b) → (s - t).abs < δuc →
      (f s - f t).abs < ε')
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr a b n ξ) (hd : Partition.diam n a b Δ < δuc) :
    ∃ δ', 0 < δ' ∧ ∀ (n' : Nat) (Δ' : Partition n' a b) (ξ' : Range n' → Real),
      Δ'.IsRepr a b n' ξ' → Partition.diam n' a b Δ' < δ' →
      (RiemannSum f a b n' Δ' ξ' - RiemannSum f a b n Δ ξ).abs ≤ ε' * (b - a) + θ := by
  have hab_le : a ≤ b := hab.1
  have hofn_pos : (0 : Real) < Real.ofNat (n + 1) := cast_lt 0 (n + 1) (Nat.zero_lt_succ n)
  have h2M_pos : (0 : Real) < 2 * M := pos_mul_pos 2 M zero_lt_two hM_pos
  have hK_pos : (0 : Real) < Real.ofNat (n + 1) * (2 * M) :=
    pos_mul_pos _ _ hofn_pos h2M_pos
  have hK_ne : Real.ofNat (n + 1) * (2 * M) ≠ 0 := fun h0 => hK_pos.2 h0.symm
  refine ⟨θ / (Real.ofNat (n + 1) * (2 * M)), pos_div_pos _ _ hθ hK_pos, ?_⟩
  intro n' Δ' ξ' hr' hd'
  have hn' : 0 < n' := by
    cases n' with
    | zero => exact absurd (Partition.zero a b Δ') hab.2
    | succ m => exact Nat.zero_lt_succ m
  -- Δ の全分点を Δ' に挿入
  obtain ⟨Δp, ξp, hrp, hlenp, hptsp, hbdp⟩ :=
    rs_multi_insert_bound f a b M hM (Real.le_of_lt hM_pos) n' hn' Δ' ξ' hr'
      (n + 1) (fun j => Δ.points ⟨j.val, j.property⟩)
      (fun j => Partition.points_in_interval n a b Δ ⟨j.val, j.property⟩)
  have hpts_all : ∀ i : Range n.succ,
      ∃ q : Range (n' + (n + 1)).succ, Δp.points q = Δ.points i := by
    intro i
    obtain ⟨q, hq⟩ := hptsp ⟨i.val, i.property⟩
    exact ⟨q, hq⟩
  have hn_pos : 0 < n := by
    cases n with
    | zero => exact absurd (Partition.zero a b Δ) hab.2
    | succ m => exact Nat.zero_lt_succ m
  have hσex := refine_parent a b n (n' + (n + 1)) hn_pos Δ Δp hpts_all
  have hσ : ∀ j : Range (n' + (n + 1)),
      Δ.points (Range.incl (Classical.choose (hσex j))) ≤ Δp.points (Range.incl j) ∧
      Δp.points (Range.addone j) ≤ Δ.points (Range.addone (Classical.choose (hσex j))) :=
    fun j => Classical.choose_spec (hσex j)
  -- 細分比較：|RS(Δp) − RS(Δ)| ≤ ε'(b−a)
  have hRCL : (RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n Δ ξ).abs ≤
      ε' * (b - a) := by
    rw [← rs_refine_eq f a b n Δ ξ (n' + (n + 1)) Δp (fun j => Classical.choose (hσex j)) hσ]
    apply same_partition_bound
    intro j
    apply Real.le_of_lt
    apply huc
    · exact in_interval_pair hab_le
        (Partition.repr_in_interval a b (n' + (n + 1)) Δp ξp hrp j)
    · exact in_interval_pair hab_le
        (Partition.repr_in_interval a b n Δ ξ hr (Classical.choose (hσex j)))
    · have hb1 := hrp j
      dsimp [Partition.IsRepr, InInterval] at hb1
      rw [if_pos (Δp.increase j)] at hb1
      have hb2 := hr (Classical.choose (hσex j))
      dsimp [Partition.IsRepr, InInterval] at hb2
      rw [if_pos (Δ.increase (Classical.choose (hσex j)))] at hb2
      have habs := abs_sub_le_of_mem
        (le_trans (hσ j).1 hb1.1) (le_trans hb1.2 (hσ j).2) hb2.1 hb2.2
      exact le_lt_trans
        (le_trans habs (le_fmax' n (Partition.length n a b Δ) (Classical.choose (hσex j)))) hd
  -- 挿入誤差 ≤ θ
  have hins : (RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n' Δ' ξ').abs ≤ θ := by
    apply le_trans hbdp
    rw [show Real.ofNat (n + 1) * (2 * M * Partition.diam n' a b Δ') =
          Real.ofNat (n + 1) * (2 * M) * Partition.diam n' a b Δ' from
          (MulCommMonoid.mul_assoc _ _ _).symm]
    apply le_trans (mul_le_mul_left (Real.ofNat (n + 1) * (2 * M)) _ _
      (Real.le_of_lt hK_pos) (Real.le_of_lt hd'))
    rw [← mul_div_assoc, MulCommMonoid.mul_comm (Real.ofNat (n + 1) * (2 * M)) θ,
        mul_div_cancel θ _ hK_ne]
    exact le_refl θ
  -- 三角不等式で合成
  calc (RiemannSum f a b n' Δ' ξ' - RiemannSum f a b n Δ ξ).abs
      = ((RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n Δ ξ) +
         (RiemannSum f a b n' Δ' ξ' - RiemannSum f a b (n' + (n + 1)) Δp ξp)).abs := by
        rw [telescope_2 (RiemannSum f a b n Δ ξ) (RiemannSum f a b n' Δ' ξ')
            (RiemannSum f a b (n' + (n + 1)) Δp ξp)]
    _ ≤ (RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n Δ ξ).abs +
        (RiemannSum f a b n' Δ' ξ' - RiemannSum f a b (n' + (n + 1)) Δp ξp).abs :=
        abs_triangle _ _
    _ = (RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n Δ ξ).abs +
        (RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n' Δ' ξ').abs := by
        rw [show RiemannSum f a b n' Δ' ξ' - RiemannSum f a b (n' + (n + 1)) Δp ξp =
              -(RiemannSum f a b (n' + (n + 1)) Δp ξp - RiemannSum f a b n' Δ' ξ') from
              (neg_sub _ _).symm, abs_neg]
    _ ≤ ε' * (b - a) + θ :=
        le_trans (LinearOrderedField.add_le_add _ _ _ hRCL) (add_left_le _ _ _ hins)

-- ============================================================
-- abs_integrable 用の補題群（振動和による評価）
-- ============================================================

private theorem add_add_swap (p x y : Real) : (p + x) + (p + y) = (x + y) + (p + p) := by
  rw [AddCommGroup.add_comm p x, AddCommGroup.add_assoc x p (p + y),
      ← AddCommGroup.add_assoc p p y, AddCommGroup.add_comm (p + p) y,
      ← AddCommGroup.add_assoc x y (p + p)]

-- 核心補題（|f| 版）：固定した細かい分割 Δ に対し、十分細かい任意の Δ' で
-- |RS_{|f|}(Δ') − RS_{|f|}(Δ)| ≤ (ε' + ε') + θ
private theorem abs_rs_compare (f : Real → Real) (a b M If : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (hM_pos : 0 < M)
    (hab : a < b) (ε' θ : Real) (hε' : 0 < ε') (hθ : 0 < θ)
    (δf : Real) (hδf_pos : 0 < δf)
    (hδf : ∀ (k : Nat) (Δk : Partition k a b) (ξk : Range k → Real),
      Δk.IsRepr a b k ξk → Partition.diam k a b Δk < δf →
      (RiemannSum f a b k Δk ξk - If).abs < ε')
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr a b n ξ) (hd : Partition.diam n a b Δ < δf) :
    ∃ δ', 0 < δ' ∧ ∀ (n' : Nat) (Δ' : Partition n' a b) (ξ' : Range n' → Real),
      Δ'.IsRepr a b n' ξ' → Partition.diam n' a b Δ' < δ' →
      (RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
       RiemannSum (fun x => (f x).abs) a b n Δ ξ).abs ≤ (ε' + ε') + θ := by
  have hab_le : a ≤ b := hab.1
  have hba_pos : 0 < b - a := (pos_iff_lt a b).mp hab
  have hba_ne : b - a ≠ 0 := fun h0 => hba_pos.2 h0.symm
  -- 各小区間の点は [a,b] に入る
  have hmem_ab : ∀ (i : Range n) (t : Real),
      Δ.points (Range.incl i) ≤ t → t ≤ Δ.points (Range.addone i) → InInterval a b t := by
    intro i t h1 h2
    dsimp [InInterval]
    rw [if_pos hab_le]
    exact ⟨le_trans (Partition.left_le_point n a b Δ (Range.incl i)) h1,
           le_trans h2 (Partition.point_le_right n a b Δ (Range.addone i))⟩
  -- 各小区間上の f の上限と (−f) の上限
  have hSne : ∀ i : Range n, ∃ v, (∃ t, (Δ.points (Range.incl i) ≤ t ∧
      t ≤ Δ.points (Range.addone i)) ∧ v = f t) :=
    fun i => ⟨f (Δ.points (Range.incl i)), Δ.points (Range.incl i),
      ⟨le_refl _, Δ.increase i⟩, rfl⟩
  have hSbdd : ∀ i : Range n, ∃ B, ∀ v, (∃ t, (Δ.points (Range.incl i) ≤ t ∧
      t ≤ Δ.points (Range.addone i)) ∧ v = f t) → v ≤ B :=
    fun i => ⟨M, fun v hv => by
      obtain ⟨t, ⟨h1, h2⟩, hveq⟩ := hv
      rw [hveq]
      exact le_trans (le_abs (f t)) (hM t (hmem_ab i t h1 h2))⟩
  have hNne : ∀ i : Range n, ∃ v, (∃ t, (Δ.points (Range.incl i) ≤ t ∧
      t ≤ Δ.points (Range.addone i)) ∧ v = -(f t)) :=
    fun i => ⟨-(f (Δ.points (Range.incl i))), Δ.points (Range.incl i),
      ⟨le_refl _, Δ.increase i⟩, rfl⟩
  have hNbdd : ∀ i : Range n, ∃ B, ∀ v, (∃ t, (Δ.points (Range.incl i) ≤ t ∧
      t ≤ Δ.points (Range.addone i)) ∧ v = -(f t)) → v ≤ B :=
    fun i => ⟨M, fun v hv => by
      obtain ⟨t, ⟨h1, h2⟩, hveq⟩ := hv
      rw [hveq]
      exact le_trans (neg_le_abs (f t)) (hM t (hmem_ab i t h1 h2))⟩
  let SupF : Range n → Real := fun i =>
    Real.sup (fun v => ∃ t, (Δ.points (Range.incl i) ≤ t ∧
      t ≤ Δ.points (Range.addone i)) ∧ v = f t) (hSne i) (hSbdd i)
  let SupN : Range n → Real := fun i =>
    Real.sup (fun v => ∃ t, (Δ.points (Range.incl i) ≤ t ∧
      t ≤ Δ.points (Range.addone i)) ∧ v = -(f t)) (hNne i) (hNbdd i)
  let Osc : Range n → Real := fun i => SupF i + SupN i
  have hF1 : ∀ (i : Range n) (t : Real), Δ.points (Range.incl i) ≤ t →
      t ≤ Δ.points (Range.addone i) → f t ≤ SupF i :=
    fun i t h1 h2 => Real.sup_ub _ (hSne i) (hSbdd i) (f t) ⟨t, ⟨h1, h2⟩, rfl⟩
  have hF2 : ∀ (i : Range n) (t : Real), Δ.points (Range.incl i) ≤ t →
      t ≤ Δ.points (Range.addone i) → -(f t) ≤ SupN i :=
    fun i t h1 h2 => Real.sup_ub _ (hNne i) (hNbdd i) (-(f t)) ⟨t, ⟨h1, h2⟩, rfl⟩
  -- 同一小区間内の 2 点での |f| の振れは Osc 以下
  have hosc : ∀ (i : Range n) (s t : Real),
      Δ.points (Range.incl i) ≤ s → s ≤ Δ.points (Range.addone i) →
      Δ.points (Range.incl i) ≤ t → t ≤ Δ.points (Range.addone i) →
      ((f s).abs - (f t).abs).abs ≤ Osc i := by
    intro i s t hs1 hs2 ht1 ht2
    apply le_trans (abs_sub_abs_le (f s) (f t))
    apply abs_le
    · rw [neg_sub]
      exact le_trans (LinearOrderedField.add_le_add (f t) (SupF i) (-(f s))
        (hF1 i t ht1 ht2)) (add_left_le (SupF i) _ _ (hF2 i s hs1 hs2))
    · exact le_trans (LinearOrderedField.add_le_add (f s) (SupF i) (-(f t))
        (hF1 i s hs1 hs2)) (add_left_le (SupF i) _ _ (hF2 i t ht1 ht2))
  -- 振動和の評価：Σ Osc·len ≤ ε' + ε'
  have hosc_sum : Sumation n (fun i => Osc i * Partition.length n a b Δ i) ≤ ε' + ε' := by
    apply le_of_forall_le_add
    intro γ hγ
    have hγ2 : 0 < γ / 2 / (b - a) := pos_div_pos _ _ (pos_half γ hγ) hba_pos
    -- γ-近似する代表点 u, v を選ぶ
    have hu : ∀ i : Range n, ∃ t, ((Δ.points (Range.incl i) ≤ t ∧
        t ≤ Δ.points (Range.addone i)) ∧ SupF i - γ / 2 / (b - a) < f t) := by
      intro i
      obtain ⟨v, ⟨t, ht, hveq⟩, hlt⟩ := sup_near _ (hSne i) (hSbdd i) _ hγ2
      exact ⟨t, ht, hveq ▸ hlt⟩
    have hv : ∀ i : Range n, ∃ t, ((Δ.points (Range.incl i) ≤ t ∧
        t ≤ Δ.points (Range.addone i)) ∧ SupN i - γ / 2 / (b - a) < -(f t)) := by
      intro i
      obtain ⟨v, ⟨t, ht, hveq⟩, hlt⟩ := sup_near _ (hNne i) (hNbdd i) _ hγ2
      exact ⟨t, ht, hveq ▸ hlt⟩
    have hu_spec := fun i => Classical.choose_spec (hu i)
    have hv_spec := fun i => Classical.choose_spec (hv i)
    have hu_repr : Δ.IsRepr a b n (fun i => Classical.choose (hu i)) :=
      Partition.le_isrepr a b n Δ _ (fun i => (hu_spec i).1)
    have hv_repr : Δ.IsRepr a b n (fun i => Classical.choose (hv i)) :=
      Partition.le_isrepr a b n Δ _ (fun i => (hv_spec i).1)
    -- 各項の評価
    have hterm : ∀ i : Range n, Osc i * Partition.length n a b Δ i ≤
        ((f (Classical.choose (hu i)) - f (Classical.choose (hv i))) +
         (γ / 2 / (b - a) + γ / 2 / (b - a))) * Partition.length n a b Δ i := by
      intro i
      apply nonneg_mul_nonneg _ _ _ (Partition.length_nonneg n a b Δ i)
      have h1 : SupF i ≤ γ / 2 / (b - a) + f (Classical.choose (hu i)) :=
        le_add_of_sub_le (Real.le_of_lt (hu_spec i).2)
      have h2 : SupN i ≤ γ / 2 / (b - a) + -(f (Classical.choose (hv i))) :=
        le_add_of_sub_le (Real.le_of_lt (hv_spec i).2)
      apply le_trans (le_trans (LinearOrderedField.add_le_add _ _ (SupN i) h1)
        (add_left_le (γ / 2 / (b - a) + f (Classical.choose (hu i))) _ _ h2))
      rw [add_add_swap (γ / 2 / (b - a)) (f (Classical.choose (hu i)))
            (-(f (Classical.choose (hv i))))]
      exact le_refl _
    have hsum := summation_le n _ _ hterm
    -- 右辺を整理
    have hRHS : Sumation n (fun i => ((f (Classical.choose (hu i)) -
        f (Classical.choose (hv i))) + (γ / 2 / (b - a) + γ / 2 / (b - a))) *
        Partition.length n a b Δ i) =
        (RiemannSum f a b n Δ (fun i => Classical.choose (hu i)) -
         RiemannSum f a b n Δ (fun i => Classical.choose (hv i))) + γ := by
      calc Sumation n (fun i => ((f (Classical.choose (hu i)) -
              f (Classical.choose (hv i))) + (γ / 2 / (b - a) + γ / 2 / (b - a))) *
              Partition.length n a b Δ i)
          = Sumation n (fun i => (f (Classical.choose (hu i)) -
              f (Classical.choose (hv i))) * Partition.length n a b Δ i +
              (γ / 2 / (b - a) + γ / 2 / (b - a)) * Partition.length n a b Δ i) :=
            summation_congr n _ _ (fun i => add_mul _ _ _)
        _ = Sumation n (fun i => (f (Classical.choose (hu i)) -
              f (Classical.choose (hv i))) * Partition.length n a b Δ i) +
            Sumation n (fun i => (γ / 2 / (b - a) + γ / 2 / (b - a)) *
              Partition.length n a b Δ i) := addtive_summation n _ _
        _ = (RiemannSum f a b n Δ (fun i => Classical.choose (hu i)) -
             RiemannSum f a b n Δ (fun i => Classical.choose (hv i))) + γ := by
            rw [summation_smul, Partition.length_sum]
            congr 1
            · calc Sumation n (fun i => (f (Classical.choose (hu i)) -
                    f (Classical.choose (hv i))) * Partition.length n a b Δ i)
                  = Sumation n (fun i =>
                      f (Classical.choose (hu i)) * Partition.length n a b Δ i -
                      f (Classical.choose (hv i)) * Partition.length n a b Δ i) :=
                    summation_congr n _ _ (fun i => (mul_sub_mul _ _ _).symm)
                _ = RiemannSum f a b n Δ (fun i => Classical.choose (hu i)) -
                    RiemannSum f a b n Δ (fun i => Classical.choose (hv i)) :=
                    (sub_summation n _ _).symm
            · rw [add_mul, div_mul_cancel' (γ / 2) (b - a) hba_ne, half_add]
    rw [hRHS] at hsum
    -- RS の差を If 経由で評価
    have hu_close := hδf n Δ (fun i => Classical.choose (hu i)) hu_repr hd
    have hv_close := hδf n Δ (fun i => Classical.choose (hv i)) hv_repr hd
    have hdiff : RiemannSum f a b n Δ (fun i => Classical.choose (hu i)) -
        RiemannSum f a b n Δ (fun i => Classical.choose (hv i)) ≤ ε' + ε' := by
      have heq : RiemannSum f a b n Δ (fun i => Classical.choose (hu i)) -
          RiemannSum f a b n Δ (fun i => Classical.choose (hv i)) =
          (If - RiemannSum f a b n Δ (fun i => Classical.choose (hv i))) +
          (RiemannSum f a b n Δ (fun i => Classical.choose (hu i)) - If) :=
        telescope_2 _ _ _
      rw [heq]
      apply Real.le_of_lt
      apply lt_add_lt
      · rw [show If - RiemannSum f a b n Δ (fun i => Classical.choose (hv i)) =
              -(RiemannSum f a b n Δ (fun i => Classical.choose (hv i)) - If) from
              (neg_sub _ _).symm]
        exact le_lt_trans (le_abs _) (by rw [abs_neg]; exact hv_close)
      · exact le_lt_trans (le_abs _) hu_close
    exact le_trans hsum (LinearOrderedField.add_le_add _ _ γ hdiff)
  -- ここから細分比較
  have hofn_pos : (0 : Real) < Real.ofNat (n + 1) := cast_lt 0 (n + 1) (Nat.zero_lt_succ n)
  have h2M_pos : (0 : Real) < 2 * M := pos_mul_pos 2 M zero_lt_two hM_pos
  have hK_pos : (0 : Real) < Real.ofNat (n + 1) * (2 * M) :=
    pos_mul_pos _ _ hofn_pos h2M_pos
  have hK_ne : Real.ofNat (n + 1) * (2 * M) ≠ 0 := fun h0 => hK_pos.2 h0.symm
  refine ⟨θ / (Real.ofNat (n + 1) * (2 * M)), pos_div_pos _ _ hθ hK_pos, ?_⟩
  intro n' Δ' ξ' hr' hd'
  have hn' : 0 < n' := by
    cases n' with
    | zero => exact absurd (Partition.zero a b Δ') hab.2
    | succ m => exact Nat.zero_lt_succ m
  have hMg : ∀ t, InInterval a b t → ((fun x => (f x).abs) t).abs ≤ M := by
    intro t ht
    rw [nonneg_abs abs_nonneg]
    exact hM t ht
  obtain ⟨Δp, ξp, hrp, hlenp, hptsp, hbdp⟩ :=
    rs_multi_insert_bound (fun x => (f x).abs) a b M hMg (Real.le_of_lt hM_pos)
      n' hn' Δ' ξ' hr' (n + 1) (fun j => Δ.points ⟨j.val, j.property⟩)
      (fun j => Partition.points_in_interval n a b Δ ⟨j.val, j.property⟩)
  have hpts_all : ∀ i : Range n.succ,
      ∃ q : Range (n' + (n + 1)).succ, Δp.points q = Δ.points i := by
    intro i
    obtain ⟨q, hq⟩ := hptsp ⟨i.val, i.property⟩
    exact ⟨q, hq⟩
  have hn_pos : 0 < n := by
    cases n with
    | zero => exact absurd (Partition.zero a b Δ) hab.2
    | succ m => exact Nat.zero_lt_succ m
  have hσex := refine_parent a b n (n' + (n + 1)) hn_pos Δ Δp hpts_all
  have hσ : ∀ j : Range (n' + (n + 1)),
      Δ.points (Range.incl (Classical.choose (hσex j))) ≤ Δp.points (Range.incl j) ∧
      Δp.points (Range.addone j) ≤ Δ.points (Range.addone (Classical.choose (hσex j))) :=
    fun j => Classical.choose_spec (hσex j)
  -- 細分比較：|RS_g(Δp) − RS_g(Δ)| ≤ ε' + ε'
  have hRCL : (RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
      RiemannSum (fun x => (f x).abs) a b n Δ ξ).abs ≤ ε' + ε' := by
    rw [← rs_refine_eq (fun x => (f x).abs) a b n Δ ξ (n' + (n + 1)) Δp
        (fun j => Classical.choose (hσex j)) hσ]
    have hsub : RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
        RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp
          (fun j => ξ (Classical.choose (hσex j))) =
        Sumation (n' + (n + 1)) (fun j =>
          ((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
          Partition.length (n' + (n + 1)) a b Δp j) := by
      calc RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
            RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp
              (fun j => ξ (Classical.choose (hσex j)))
          = Sumation (n' + (n + 1)) (fun j =>
              (f (ξp j)).abs * Partition.length (n' + (n + 1)) a b Δp j -
              (f (ξ (Classical.choose (hσex j)))).abs *
                Partition.length (n' + (n + 1)) a b Δp j) := sub_summation _ _ _
        _ = Sumation (n' + (n + 1)) (fun j =>
              ((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
              Partition.length (n' + (n + 1)) a b Δp j) :=
            summation_congr _ _ _ (fun j => mul_sub_mul _ _ _)
    rw [hsub]
    have hperj : ∀ j : Range (n' + (n + 1)),
        ((((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
          Partition.length (n' + (n + 1)) a b Δp j)).abs ≤
        Osc (Classical.choose (hσex j)) * Partition.length (n' + (n + 1)) a b Δp j := by
      intro j
      rw [abs_mul_nonneg (Partition.length_nonneg (n' + (n + 1)) a b Δp j)]
      apply nonneg_mul_nonneg _ _ _ (Partition.length_nonneg (n' + (n + 1)) a b Δp j)
      have hb1 := hrp j
      dsimp [Partition.IsRepr, InInterval] at hb1
      rw [if_pos (Δp.increase j)] at hb1
      have hb2 := hr (Classical.choose (hσex j))
      dsimp [Partition.IsRepr, InInterval] at hb2
      rw [if_pos (Δ.increase (Classical.choose (hσex j)))] at hb2
      exact hosc (Classical.choose (hσex j)) (ξp j) (ξ (Classical.choose (hσex j)))
        (le_trans (hσ j).1 hb1.1) (le_trans hb1.2 (hσ j).2) hb2.1 hb2.2
    calc (Sumation (n' + (n + 1)) (fun j =>
            ((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
            Partition.length (n' + (n + 1)) a b Δp j)).abs
        ≤ Sumation (n' + (n + 1)) (fun j =>
            ((((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
              Partition.length (n' + (n + 1)) a b Δp j)).abs) := abs_summation_le _ _
      _ ≤ Sumation (n' + (n + 1)) (fun j =>
            Osc (Classical.choose (hσex j)) * Partition.length (n' + (n + 1)) a b Δp j) :=
          summation_le _ _ _ hperj
      _ = Sumation n (fun i => Osc i * Partition.length n a b Δ i) :=
          rs_refine_eq (fun t => t) a b n Δ Osc (n' + (n + 1)) Δp
            (fun j => Classical.choose (hσex j)) hσ
      _ ≤ ε' + ε' := hosc_sum
  -- 挿入誤差 ≤ θ
  have hins : (RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
      RiemannSum (fun x => (f x).abs) a b n' Δ' ξ').abs ≤ θ := by
    apply le_trans hbdp
    rw [show Real.ofNat (n + 1) * (2 * M * Partition.diam n' a b Δ') =
          Real.ofNat (n + 1) * (2 * M) * Partition.diam n' a b Δ' from
          (MulCommMonoid.mul_assoc _ _ _).symm]
    apply le_trans (mul_le_mul_left (Real.ofNat (n + 1) * (2 * M)) _ _
      (Real.le_of_lt hK_pos) (Real.le_of_lt hd'))
    rw [← mul_div_assoc, MulCommMonoid.mul_comm (Real.ofNat (n + 1) * (2 * M)) θ,
        mul_div_cancel θ _ hK_ne]
    exact le_refl θ
  -- 三角不等式で合成
  calc (RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
        RiemannSum (fun x => (f x).abs) a b n Δ ξ).abs
      = ((RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
          RiemannSum (fun x => (f x).abs) a b n Δ ξ) +
         (RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
          RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp)).abs := by
        rw [telescope_2 (RiemannSum (fun x => (f x).abs) a b n Δ ξ)
            (RiemannSum (fun x => (f x).abs) a b n' Δ' ξ')
            (RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp)]
    _ ≤ (RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
         RiemannSum (fun x => (f x).abs) a b n Δ ξ).abs +
        (RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
         RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp).abs :=
        abs_triangle _ _
    _ = (RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
         RiemannSum (fun x => (f x).abs) a b n Δ ξ).abs +
        (RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
         RiemannSum (fun x => (f x).abs) a b n' Δ' ξ').abs := by
        rw [show RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
              RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp =
              -(RiemannSum (fun x => (f x).abs) a b (n' + (n + 1)) Δp ξp -
                RiemannSum (fun x => (f x).abs) a b n' Δ' ξ') from
              (neg_sub _ _).symm, abs_neg]
    _ ≤ (ε' + ε') + θ :=
        le_trans (LinearOrderedField.add_le_add _ _ _ hRCL) (add_left_le _ _ _ hins)

theorem continuous_integrable (f : Real → Real) (a x : Real) (hf : Continuous f) :
  ∃ i, IsIntegral f a x i := by
  cases Classical.em (a ≤ x) with
  | inr h =>
    -- a > x: no partition exists, IsIntegral is vacuously true
    exact ⟨0, fun ε hε => ⟨1, zero_lt_one, fun n Δ ξ _ _ =>
      absurd (Partition.left_le_right n a x Δ) h⟩⟩
  | inl hab =>
    cases Classical.em (a = x) with
    | inl heq =>
      -- a = x: all partition points = a, RS = 0
      subst heq
      exact ⟨0, fun ε hε => ⟨1, zero_lt_one, fun n Δ ξ hr _ => by
        have hpts : ∀ (i : Range n.succ), Δ.points i = a :=
          fun i => (LinearOrderedField.le_asymm _ _ (Δ.left_le_point i) (Δ.point_le_right i)).symm
        have hxi : ∀ (i : Range n), ξ i = a := by
          intro i
          have hi := hr i
          dsimp [InInterval] at hi
          rw [hpts (Range.incl i), hpts (Range.addone i), if_pos (le_refl a)] at hi
          exact (LinearOrderedField.le_asymm _ _ hi.1 hi.2).symm
        have hRS : RiemannSum f a a n Δ ξ = RiemannSum (fun _ => f a) a a n Δ ξ := by
          unfold RiemannSum; apply summation_congr; intro i; rw [hxi i]
        rw [hRS, const_riemann_sum, sub_self,
            show f a * (0 : Real) = 0 from by rw [MulCommMonoid.mul_comm]; exact zero_mul' _,
            sub_self, abs_zero]
        exact hε⟩⟩
    | inr hne =>
      -- a < x: continuous on [a,x] implies integrable
      have hab' : a < x := ⟨hab, hne⟩
      -- Get bound M and uniform continuity delta
      rcases continuous_bounded f a x hab' hf with ⟨M, hM_pos, hM_bound⟩
      have hM_nn : (0 : Real) ≤ M := Real.le_of_lt hM_pos
      -- Define S = { y | ∃ δ > 0, ∀ RS with mesh < δ, y ≤ RS }
      let S : Real → Prop := fun y =>
        ∃ δ, 0 < δ ∧ ∀ n (Δ : Partition n a x) (ξ : Range n → Real),
          Δ.IsRepr a x n ξ → Partition.diam n a x Δ < δ → y ≤ RiemannSum f a x n Δ ξ
      -- S is nonempty: -(M*(x-a)) ∈ S
      have hS_ne : ∃ y, S y := by
        refine ⟨-(M * (x - a)), 1, zero_lt_one, fun n Δ ξ hr _ => ?_⟩
        have h_rs := rs_abs_bound f a x M hM_bound n Δ ξ hr
        -- |RS| ≤ M*(x-a) → -(M*(x-a)) ≤ RS via neg_le_swap
        have h1 : -(RiemannSum f a x n Δ ξ) ≤ M * (x - a) :=
          le_trans (neg_le_abs _) h_rs
        exact neg_le_swap h1
      -- S is bounded above: M*(x-a) is an upper bound
      have hS_bdd : ∃ ub, ∀ y, S y → y ≤ ub := by
        refine ⟨M * (x - a), fun y ⟨δ, hδ, hy⟩ => ?_⟩
        -- Build a partition with mesh < δ, then y ≤ RS ≤ M*(x-a)
        have hba_nn : 0 ≤ x - a := (nonneg_iff_le a x).mp hab
        have hba_div_nn : 0 ≤ (x - a) / δ := nonneg_div_nonneg (x - a) δ hba_nn hδ
        let m := ceil ((x - a) / δ)
        have hm_lt : (x - a) / δ < (m : Real) := ceil_lt _
        have hm_ne : m ≠ 0 := by
          intro hm; rw [hm] at hm_lt; exact (le_lt_trans hba_div_nn hm_lt).2 rfl
        let Δ := equalPartition m a x hm_ne hab
        let ξ := equalPartitionRepr m a x hm_ne hab
        have h_repr := equalPartitionRepr_isrepr m a x hm_ne hab
        have h_diam := equalPartition_diam_lt m a x δ hm_ne hab hδ hm_lt
        have h_le := hy m Δ ξ h_repr h_diam
        exact le_trans h_le (le_trans (le_abs _) (rs_abs_bound f a x M hM_bound m Δ ξ h_repr))
      -- Define I = sup S
      let I := Real.sup S hS_ne hS_bdd
      refine ⟨I, fun ε hε => ?_⟩
      -- Get uniform continuity delta
      have hxa_pos : 0 < x - a :=
        ⟨(nonneg_sub_iff a x).mp hab, fun h => by
          apply hne; apply LinearOrderedField.le_asymm a x hab
          have : x - a = 0 := h.symm
          have := (sub_zero_eq x a).mp this
          exact this ▸ le_refl a⟩
      rcases continuous_unif_cont f a x hab' hf (ε / 2 / (x - a))
          (pos_div_pos _ _ (pos_half ε hε) hxa_pos)
        with ⟨δ_uc, hδ_uc_pos, hδ_uc⟩
      refine ⟨δ_uc, hδ_uc_pos, ?_⟩
      intro n Δ ξ hr hd
      have hxa_ne : x - a ≠ 0 := fun h0 => hxa_pos.2 h0.symm
      have hθ : 0 < ε / 2 / 2 := pos_half (ε / 2) (pos_half ε hε)
      obtain ⟨δ', hδ'_pos, hcomp⟩ := rs_compare f a x M hM_bound hM_pos hab'
        (ε / 2 / (x - a)) (ε / 2 / 2)
        (pos_div_pos _ _ (pos_half ε hε) hxa_pos) hθ
        δ_uc hδ_uc_pos hδ_uc n Δ ξ hr hd
      -- ε'(x−a) = ε/2
      have hdmc : ε / 2 / (x - a) * (x - a) = ε / 2 := by
        rw [MulCommMonoid.mul_comm, ← mul_div_assoc,
            MulCommMonoid.mul_comm (x - a) (ε / 2), mul_div_cancel _ _ hxa_ne]
      have hbound : ∀ (n' : Nat) (Δ' : Partition n' a x) (ξ' : Range n' → Real),
          Partition.IsRepr a x n' Δ' ξ' → Partition.diam n' a x Δ' < δ' →
          (RiemannSum f a x n' Δ' ξ' - RiemannSum f a x n Δ ξ).abs ≤
            ε / 2 + ε / 2 / 2 := by
        intro n' Δ' ξ' hr' hd'
        have h := hcomp n' Δ' ξ' hr' hd'
        rwa [hdmc] at h
      -- 下から：RS − (ε/2 + ε/4) ∈ S
      have hmem : S (RiemannSum f a x n Δ ξ - (ε / 2 + ε / 2 / 2)) := by
        refine ⟨δ', hδ'_pos, fun n' Δ' ξ' hr' hd' => ?_⟩
        have h := hbound n' Δ' ξ' hr' hd'
        have h2 : RiemannSum f a x n Δ ξ - RiemannSum f a x n' Δ' ξ' ≤
            ε / 2 + ε / 2 / 2 := by
          apply le_trans (le_abs _)
          rw [show RiemannSum f a x n Δ ξ - RiemannSum f a x n' Δ' ξ' =
                -(RiemannSum f a x n' Δ' ξ' - RiemannSum f a x n Δ ξ) from
                (neg_sub _ _).symm, abs_neg]
          exact h
        exact sub_le_swap h2
      have h_lower := Real.sup_ub S hS_ne hS_bdd _ hmem
      -- 上から：I ≤ RS + (ε/2 + ε/4)
      have h_upper : I ≤ RiemannSum f a x n Δ ξ + (ε / 2 + ε / 2 / 2) := by
        apply Real.sup_lub S hS_ne hS_bdd
        intro y hy
        obtain ⟨δy, hδy_pos, hy_le⟩ := hy
        have hδm_pos : 0 < min δy δ' := min_pos δy δ' hδy_pos hδ'_pos
        have hba_nn : 0 ≤ x - a := (nonneg_iff_le a x).mp hab
        have hdiv_nn : 0 ≤ (x - a) / min δy δ' :=
          nonneg_div_nonneg _ _ hba_nn hδm_pos
        have hm_lt : (x - a) / min δy δ' < ((ceil ((x - a) / min δy δ')) : Real) := ceil_lt _
        have hm_ne : ceil ((x - a) / min δy δ') ≠ 0 := by
          intro h0
          rw [h0] at hm_lt
          exact (le_lt_trans hdiv_nn hm_lt).2 rfl
        have hEr := equalPartitionRepr_isrepr (ceil ((x - a) / min δy δ')) a x hm_ne hab
        have hEd : Partition.diam (ceil ((x - a) / min δy δ')) a x
            (equalPartition (ceil ((x - a) / min δy δ')) a x hm_ne hab) < min δy δ' :=
          equalPartition_diam_lt _ a x (min δy δ') hm_ne hab hδm_pos hm_lt
        have h1 := hy_le (ceil ((x - a) / min δy δ'))
          (equalPartition _ a x hm_ne hab) (equalPartitionRepr _ a x hm_ne hab)
          hEr (lt_le_trans _ _ _ hEd (min_left_le δy δ'))
        have h2 := hbound (ceil ((x - a) / min δy δ'))
          (equalPartition _ a x hm_ne hab) (equalPartitionRepr _ a x hm_ne hab)
          hEr (lt_le_trans _ _ _ hEd (min_right_le δy δ'))
        have h3 := le_add_of_sub_le (le_trans (le_abs _) h2)
        exact le_trans h1 h3
      -- |RS − I| ≤ 3ε/4 < ε
      have habs : (RiemannSum f a x n Δ ξ - I).abs ≤ ε / 2 + ε / 2 / 2 := by
        apply abs_le
        · rw [neg_sub]
          exact sub_le_of_le_add h_upper
        · exact sub_le_swap h_lower
      have hBlt : ε / 2 + ε / 2 / 2 < ε := by
        have h := add_left_lt (ε / 2) (ε / 2 / 2) (ε / 2) (half_lt (pos_half ε hε))
        rwa [half_add ε] at h
      exact le_lt_trans habs hBlt

-- 可積分なら |f| も可積分（a ≤ b 版）
theorem abs_integrable (f : Real → Real) (a b : Real) (h : a ≤ b)
    (h'' : IsIntegrable f a b) : IsIntegrable (fun x ↦ (f x).abs) a b := by
  cases Classical.em (b ≤ a) with
  | inl hba =>
    -- a = b : RS は常に 0
    have heq : a = b := LinearOrderedField.le_asymm a b h hba
    subst heq
    exact ⟨0, fun ε hε => ⟨1, zero_lt_one, fun n Δ ξ hr _ => by
      have hpts : ∀ (i : Range n.succ), Δ.points i = a :=
        fun i => (LinearOrderedField.le_asymm _ _ (Δ.left_le_point i)
          (Δ.point_le_right i)).symm
      have hxi : ∀ (i : Range n), ξ i = a := by
        intro i
        have hi := hr i
        dsimp [InInterval] at hi
        rw [hpts (Range.incl i), hpts (Range.addone i), if_pos (le_refl a)] at hi
        exact (LinearOrderedField.le_asymm _ _ hi.1 hi.2).symm
      have hRS : RiemannSum (fun x => (f x).abs) a a n Δ ξ =
          RiemannSum (fun _ => (f a).abs) a a n Δ ξ := by
        unfold RiemannSum; apply summation_congr; intro i; rw [hxi i]
      rw [hRS, const_riemann_sum, sub_self,
          show (f a).abs * (0 : Real) = 0 from by
            rw [MulCommMonoid.mul_comm]; exact zero_mul' _,
          sub_self, abs_zero]
      exact hε⟩⟩
  | inr hba =>
    have hab' : a < b := ne_le_lt b a hba
    -- f の有界性
    obtain ⟨M₀, hM₀⟩ := integrable_bounded f a b h h''
    have ha_in : InInterval a b a := by
      dsimp [InInterval]; rw [if_pos h]; exact ⟨le_refl a, h⟩
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
    -- S = 「十分細かい分割では常に RS_{|f|} 以下」となる y の集合
    let S : Real → Prop := fun y =>
      ∃ δ, 0 < δ ∧ ∀ n (Δ : Partition n a b) (ξ : Range n → Real),
        Δ.IsRepr a b n ξ → Partition.diam n a b Δ < δ →
        y ≤ RiemannSum (fun x => (f x).abs) a b n Δ ξ
    have hS_ne : ∃ y, S y :=
      ⟨0, 1, zero_lt_one, fun n Δ ξ hr _ =>
        RiemannSum_nonneg _ a b n Δ ξ (fun x _ => abs_nonneg) hr⟩
    have hS_bdd : ∃ ub, ∀ y, S y → y ≤ ub := by
      refine ⟨(M₀ + 1) * (b - a), fun y hy => ?_⟩
      obtain ⟨δ, hδ, hy_le⟩ := hy
      have hba_nn : 0 ≤ b - a := (nonneg_iff_le a b).mp h
      have hdiv_nn : 0 ≤ (b - a) / δ := nonneg_div_nonneg (b - a) δ hba_nn hδ
      have hm_lt : (b - a) / δ < ((ceil ((b - a) / δ)) : Real) := ceil_lt _
      have hm_ne : ceil ((b - a) / δ) ≠ 0 := by
        intro h0; rw [h0] at hm_lt; exact (le_lt_trans hdiv_nn hm_lt).2 rfl
      have h_repr := equalPartitionRepr_isrepr (ceil ((b - a) / δ)) a b hm_ne h
      have h_diam := equalPartition_diam_lt (ceil ((b - a) / δ)) a b δ hm_ne h hδ hm_lt
      have h_le := hy_le _ _ _ h_repr h_diam
      exact le_trans h_le (le_trans (le_abs _)
        (rs_abs_bound (fun x => (f x).abs) a b (M₀ + 1) hMg _ _ _ h_repr))
    refine ⟨Real.sup S hS_ne hS_bdd, fun ε hε => ?_⟩
    have hε8 : 0 < ε / 2 / 2 / 2 := pos_half _ (pos_half _ (pos_half ε hε))
    obtain ⟨δf, hδf_pos, hδf⟩ := hIf (ε / 2 / 2 / 2) hε8
    refine ⟨δf, hδf_pos, ?_⟩
    intro n Δ ξ hr hd
    obtain ⟨δ', hδ'_pos, hcomp⟩ := abs_rs_compare f a b (M₀ + 1) If hM hM_pos hab'
      (ε / 2 / 2 / 2) (ε / 2 / 2) hε8 (pos_half _ (pos_half ε hε))
      δf hδf_pos hδf n Δ ξ hr hd
    have hbound : ∀ (n' : Nat) (Δ' : Partition n' a b) (ξ' : Range n' → Real),
        Partition.IsRepr a b n' Δ' ξ' → Partition.diam n' a b Δ' < δ' →
        (RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
         RiemannSum (fun x => (f x).abs) a b n Δ ξ).abs ≤ ε / 2 := by
      intro n' Δ' ξ' hr' hd'
      have h1 := hcomp n' Δ' ξ' hr' hd'
      rwa [half_add (ε / 2 / 2), half_add (ε / 2)] at h1
    -- 下から：RS − ε/2 ∈ S
    have hmem : S (RiemannSum (fun x => (f x).abs) a b n Δ ξ - ε / 2) := by
      refine ⟨δ', hδ'_pos, fun n' Δ' ξ' hr' hd' => ?_⟩
      have h1 := hbound n' Δ' ξ' hr' hd'
      have h2 : RiemannSum (fun x => (f x).abs) a b n Δ ξ -
          RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' ≤ ε / 2 := by
        apply le_trans (le_abs _)
        rw [show RiemannSum (fun x => (f x).abs) a b n Δ ξ -
              RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' =
              -(RiemannSum (fun x => (f x).abs) a b n' Δ' ξ' -
                RiemannSum (fun x => (f x).abs) a b n Δ ξ) from
              (neg_sub _ _).symm, abs_neg]
        exact h1
      exact sub_le_swap h2
    have h_lower := Real.sup_ub S hS_ne hS_bdd _ hmem
    -- 上から：sup ≤ RS + ε/2
    have h_upper : Real.sup S hS_ne hS_bdd ≤
        RiemannSum (fun x => (f x).abs) a b n Δ ξ + ε / 2 := by
      apply Real.sup_lub S hS_ne hS_bdd
      intro y hy
      obtain ⟨δy, hδy_pos, hy_le⟩ := hy
      have hδm_pos : 0 < min δy δ' := min_pos δy δ' hδy_pos hδ'_pos
      have hba_nn : 0 ≤ b - a := (nonneg_iff_le a b).mp h
      have hdiv_nn : 0 ≤ (b - a) / min δy δ' := nonneg_div_nonneg _ _ hba_nn hδm_pos
      have hm_lt : (b - a) / min δy δ' <
          ((ceil ((b - a) / min δy δ')) : Real) := ceil_lt _
      have hm_ne : ceil ((b - a) / min δy δ') ≠ 0 := by
        intro h0; rw [h0] at hm_lt; exact (le_lt_trans hdiv_nn hm_lt).2 rfl
      have hEr := equalPartitionRepr_isrepr (ceil ((b - a) / min δy δ')) a b hm_ne h
      have hEd := equalPartition_diam_lt (ceil ((b - a) / min δy δ')) a b
        (min δy δ') hm_ne h hδm_pos hm_lt
      have h1 := hy_le _ _ _ hEr (lt_le_trans _ _ _ hEd (min_left_le δy δ'))
      have h2 := hbound _ _ _ hEr (lt_le_trans _ _ _ hEd (min_right_le δy δ'))
      exact le_trans h1 (le_add_of_sub_le (le_trans (le_abs _) h2))
    have habs : (RiemannSum (fun x => (f x).abs) a b n Δ ξ -
        Real.sup S hS_ne hS_bdd).abs ≤ ε / 2 := by
      apply abs_le
      · rw [neg_sub]
        exact sub_le_of_le_add h_upper
      · exact sub_le_swap h_lower
    exact le_lt_trans habs (half_lt hε)

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
  | inr hab =>
    exact ⟨0, fun ε hε => ⟨1, zero_lt_one, fun n Δ ξ _ _ =>
      absurd (Partition.left_le_right n a b Δ) hab⟩⟩

theorem integrable_sub_integrable (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x - g x) a b := by
  exact integrable_sub f g a b hf hg

-- 積分の三角不等式（右辺に .abs を付けた形）
theorem integral_triangle_ineq {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (h : ∃ i, IsIntegral f a b i) :
    (Integral f a b).abs ≤ (Integral (fun t ↦ (f t).abs) a b).abs := by
  have habs : IsIntegrable (fun t ↦ (f t).abs) a b := integrable_abs_integrable f a b h
  have hnn : 0 ≤ Integral (fun t ↦ (f t).abs) a b :=
    integral_nonneg (fun t ↦ (f t).abs) a b hab (fun t _ => abs_nonneg) habs
  rw [nonneg_abs hnn]
  exact int_triangle_ineq f a b hab h

-- ============================================================
-- 向き付き積分
-- ============================================================

-- [a,a] 上の積分は 0
theorem isintegral_self (f : Real → Real) (a : Real) : IsIntegral f a a 0 := by
  intro ε hε
  refine ⟨1, zero_lt_one, fun n Δ ξ hr _ => ?_⟩
  have hpts : ∀ (i : Range n.succ), Δ.points i = a :=
    fun i => (LinearOrderedField.le_asymm _ _ (Δ.left_le_point i) (Δ.point_le_right i)).symm
  have hxi : ∀ (i : Range n), ξ i = a := by
    intro i
    have hi := hr i
    dsimp [InInterval] at hi
    rw [hpts (Range.incl i), hpts (Range.addone i), if_pos (le_refl a)] at hi
    exact (LinearOrderedField.le_asymm _ _ hi.1 hi.2).symm
  have hRS : RiemannSum f a a n Δ ξ = RiemannSum (fun _ => f a) a a n Δ ξ := by
    unfold RiemannSum; apply summation_congr; intro i; rw [hxi i]
  rw [hRS, const_riemann_sum, sub_self,
      show f a * (0 : Real) = 0 from by
        rw [MulCommMonoid.mul_comm]; exact zero_mul' _,
      sub_self, abs_zero]
  exact hε

theorem integral_self (f : Real → Real) (a : Real) : Integral f a a = 0 :=
  IsIntegral_iff f a a 0 (le_refl a) (isintegral_self f a)

-- 向き付き積分の定義：a > b のときは符号を反転する
noncomputable def OIntegral (f : Real → Real) (a b : Real) : Real :=
  if a ≤ b then Integral f a b else -(Integral f b a)

theorem OIntegral_of_le (f : Real → Real) {a b : Real} (h : a ≤ b) :
    OIntegral f a b = Integral f a b := by
  show (if a ≤ b then Integral f a b else -(Integral f b a)) = Integral f a b
  rw [if_pos h]

theorem OIntegral_of_ge (f : Real → Real) {a b : Real} (h : b ≤ a) :
    OIntegral f a b = -(Integral f b a) := by
  cases Classical.em (a ≤ b) with
  | inl hab =>
    have heq : a = b := LinearOrderedField.le_asymm a b hab h
    subst heq
    show (if a ≤ a then Integral f a a else -(Integral f a a)) = -(Integral f a a)
    rw [if_pos (le_refl a), integral_self, neg_zero]
  | inr hnab =>
    show (if a ≤ b then Integral f a b else -(Integral f b a)) = -(Integral f b a)
    rw [if_neg hnab]

-- 向きの反転
theorem OIntegral_swap (f : Real → Real) (a b : Real) :
    OIntegral f a b = -(OIntegral f b a) := by
  cases LinearOrderedField.le_total a b with
  | inl h => rw [OIntegral_of_le f h, OIntegral_of_ge f h, neg_neg]
  | inr h => rw [OIntegral_of_ge f h, OIntegral_of_le f h]

theorem OIntegral_self (f : Real → Real) (a : Real) : OIntegral f a a = 0 := by
  rw [OIntegral_of_le f (le_refl a)]
  exact integral_self f a

-- 向き付き積分の加法性（a, b, c の順序によらず成立）
theorem oint_add_integral (f : Real → Real) (hint : ∀ u v, IsIntegrable f u v)
    (a b c : Real) :
    OIntegral f a b + OIntegral f b c = OIntegral f a c := by
  cases LinearOrderedField.le_total a b with
  | inl hab =>
    cases LinearOrderedField.le_total b c with
    | inl hbc =>
      -- a ≤ b ≤ c
      rw [OIntegral_of_le f hab, OIntegral_of_le f hbc, OIntegral_of_le f (le_trans hab hbc)]
      exact interval_add_integral f a b c hab hbc (hint a b) (hint b c)
    | inr hcb =>
      cases LinearOrderedField.le_total a c with
      | inl hac =>
        -- a ≤ c ≤ b
        rw [OIntegral_of_le f hab, OIntegral_of_ge f hcb, OIntegral_of_le f hac,
            ← interval_add_integral f a c b hac hcb (hint a c) (hint c b)]
        exact add_neg_cancel_right _ _
      | inr hca =>
        -- c ≤ a ≤ b
        rw [OIntegral_of_le f hab, OIntegral_of_ge f hcb, OIntegral_of_ge f hca,
            ← interval_add_integral f c a b hca hab (hint c a) (hint a b), neg_add_distrib]
        exact add_neg_neg_cancel _ _
  | inr hba =>
    cases LinearOrderedField.le_total b c with
    | inl hbc =>
      cases LinearOrderedField.le_total a c with
      | inl hac =>
        -- b ≤ a ≤ c
        rw [OIntegral_of_ge f hba, OIntegral_of_le f hbc, OIntegral_of_le f hac,
            ← interval_add_integral f b a c hba hac (hint b a) (hint a c)]
        exact neg_add_cancel_left _ _
      | inr hca =>
        -- b ≤ c ≤ a
        rw [OIntegral_of_ge f hba, OIntegral_of_le f hbc, OIntegral_of_ge f hca,
            ← interval_add_integral f b c a hbc hca (hint b c) (hint c a), neg_add_distrib]
        exact neg_neg_cancel_left _ _
    | inr hcb =>
      -- c ≤ b ≤ a
      rw [OIntegral_of_ge f hba, OIntegral_of_ge f hcb,
          OIntegral_of_ge f (le_trans hcb hba),
          ← interval_add_integral f c b a hcb hba (hint c b) (hint b a), neg_add_distrib]
      exact AddCommGroup.add_comm _ _

-- 区間の差：削除した integral_sub_interval の向き付き版（順序の仮定なしで成立）
theorem oint_sub_interval (f : Real → Real) (hint : ∀ u v, IsIntegrable f u v)
    (a b c : Real) :
    OIntegral f a b - OIntegral f a c = OIntegral f c b := by
  rw [← oint_add_integral f hint a c b]
  exact add_sub_cancel _ _
