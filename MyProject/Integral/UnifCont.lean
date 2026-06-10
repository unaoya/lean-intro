import MyProject.Limit

-- 連続関数の一様連続性と有界性（sup 公理を使用）

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
theorem continuous_unif_cont (f : Real → Real) (a b : Real)
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
theorem continuous_bounded (f : Real → Real) (a b : Real)
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

