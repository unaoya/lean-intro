import MyProject.Integral.Def

-- コーシー型判定条件による可積分性：
-- 「十分細かい任意の分割を固定すると、さらに細かい任意の分割の RS が ε-近傍に入る」
-- なら可積分（積分値は sup で構成する）

theorem integrable_of_cauchy (g : Real → Real) (a b : Real) (hab : a ≤ b)
    (M : Real) (hM : ∀ t, InInterval a b t → (g t).abs ≤ M)
    (hcauchy : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ P : TaggedPartition a b, Partition.diam P.Δ < δ →
        ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition a b, Partition.diam P'.Δ < δ' →
          (RiemannSum g P'.Δ P'.ξ - RiemannSum g P.Δ P.ξ).abs ≤ ε) :
    IsIntegrable g a b := by
  -- S = 「十分細かい分割では常に RS 以下」となる y の集合
  let S : Real → Prop := fun y =>
    ∃ δ, 0 < δ ∧ ∀ P : TaggedPartition a b,
      Partition.diam P.Δ < δ → y ≤ RiemannSum g P.Δ P.ξ
  have hS_ne : ∃ y, S y := by
    refine ⟨-(M * (b - a)), 1, zero_lt_one, fun ⟨n, Δ, ξ, hr⟩ _ => ?_⟩
    exact neg_le_swap (le_trans (neg_le_abs _) (rs_abs_bound g M hM Δ ξ hr))
  have hS_bdd : ∃ ub, ∀ y, S y → y ≤ ub := by
    refine ⟨M * (b - a), fun y hy => ?_⟩
    obtain ⟨δ, hδ, hy_le⟩ := hy
    obtain ⟨⟨m, Δm, ξm, hrm⟩, hdm⟩ := exists_fine_partition a b δ hab hδ
    exact le_trans (hy_le ⟨m, Δm, ξm, hrm⟩ hdm)
      (le_trans (le_abs _) (rs_abs_bound g M hM Δm ξm hrm))
  refine ⟨Real.sup S hS_ne hS_bdd, fun ε hε => ?_⟩
  obtain ⟨δ, hδ_pos, hδ⟩ := hcauchy (ε / 2) (pos_half ε hε)
  refine ⟨δ, hδ_pos, ?_⟩
  intro ⟨n, Δ, ξ, hr⟩ hd
  obtain ⟨δ', hδ'_pos, hcomp⟩ := hδ ⟨n, Δ, ξ, hr⟩ hd
  -- 下から：RS − ε/2 ∈ S
  have hmem : S (RiemannSum g Δ ξ - ε / 2) := by
    refine ⟨δ', hδ'_pos, fun ⟨n', Δ', ξ', hr'⟩ hd' => ?_⟩
    have h2 : RiemannSum g Δ ξ - RiemannSum g Δ' ξ' ≤ ε / 2 := by
      apply le_trans (le_abs _)
      rw [abs_sub_comm]
      exact hcomp ⟨n', Δ', ξ', hr'⟩ hd'
    exact sub_le_swap h2
  have h_lower := Real.sup_ub S hS_ne hS_bdd _ hmem
  -- 上から：sup ≤ RS + ε/2
  have h_upper : Real.sup S hS_ne hS_bdd ≤ RiemannSum g Δ ξ + ε / 2 := by
    apply Real.sup_lub S hS_ne hS_bdd
    intro y hy
    obtain ⟨δy, hδy_pos, hy_le⟩ := hy
    have hδm_pos : 0 < min δy δ' := min_pos δy δ' hδy_pos hδ'_pos
    obtain ⟨⟨m, Δm, ξm, hrm⟩, hdm⟩ := exists_fine_partition a b (min δy δ') hab hδm_pos
    have h1 := hy_le ⟨m, Δm, ξm, hrm⟩ (lt_le_trans _ _ _ hdm (min_left_le δy δ'))
    have h2 := hcomp ⟨m, Δm, ξm, hrm⟩ (lt_le_trans _ _ _ hdm (min_right_le δy δ'))
    exact le_trans h1 (le_add_of_sub_le (le_trans (le_abs _) h2))
  have habs : (RiemannSum g Δ ξ - Real.sup S hS_ne hS_bdd).abs ≤ ε / 2 := by
    apply abs_le
    · rw [neg_sub]
      exact sub_le_of_le_add h_upper
    · exact sub_le_swap h_lower
  exact le_lt_trans habs (half_lt hε)
