import MyProject.Integral.Def

-- 可積分関数の有界性

noncomputable section

open Real Classical

-- 積分の区間についての加法性

-- リーマン可積分なら有界であることを示し、それを用いる。
theorem integrable_bounded (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (h : IsIntegrable f a b) : ∃ M, ∀ x, InInterval a b x → abs (f x) ≤ M := by
  cases Classical.em (b ≤ a) with
  | inl hba =>
    -- a = b : 区間は一点のみ
    have heq : a = b := LinearOrderedField.le_asymm a b hab hba
    subst heq
    refine ⟨(f a).abs, fun x hx => ?_⟩
    dsimp [InInterval] at hx
    rw [if_pos (le_refl a)] at hx
    rw [LinearOrderedField.le_asymm x a hx.2 hx.1]
    exact le_refl _
  | inr hba =>
    have hba_pos : 0 < b - a := (pos_iff_lt a b).mp (ne_le_lt b a hba)
    obtain ⟨I, hI⟩ := h
    obtain ⟨δ, hδ, hbound⟩ := hI 1 zero_lt_one
    have hba_div_nn : 0 ≤ (b - a) / δ :=
      nonneg_div_nonneg (b - a) δ ((nonneg_iff_le a b).mp hab) hδ
    -- 等分割を構成
    obtain ⟨m, hm_lt, hm_ne, hm_pos_r⟩ :
        ∃ m : Nat, (b - a) / δ < (m : Real) ∧ m ≠ 0 ∧ (0 : Real) < (m : Real) := by
      refine ⟨ceil ((b - a) / δ), ceil_lt _, ?_, le_lt_trans hba_div_nn (ceil_lt _)⟩
      intro hm0
      have hc := ceil_lt ((b - a) / δ)
      rw [hm0] at hc
      exact (le_lt_trans hba_div_nn hc).2 rfl
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
    let Δ := equalPartition m a b hm_ne hab
    let ξ := equalPartitionRepr m a b hm_ne hab
    have h_repr : Δ.IsRepr ξ := equalPartitionRepr_isrepr m a b hm_ne hab
    have h_diam : Partition.diam Δ < δ :=
      equalPartition_diam_lt m a b δ hm_ne hab hδ hm_lt
    have hL_pos : 0 < (b - a) / (m : Real) := pos_div_pos _ _ hba_pos hm_pos_r
    have hL_ne : (b - a) / (m : Real) ≠ 0 := fun h0 => hL_pos.2 h0.symm
    -- 各点 x で、x を含む小区間の代表点だけ x に取り替えた代表点列と比較する
    refine ⟨2 / ((b - a) / (m : Real)) + fmax' m (fun j => (f (ξ j)).abs), ?_⟩
    intro x hx
    obtain ⟨k, hkL, hkR⟩ := Partition.find_interval Δ x hm_pos hx
    let ξ' : Range m → Real := fun i => if i.val = k.val then x else ξ i
    have hr_bounds : ∀ j : Range m,
        Δ.points j.incl ≤ ξ j ∧ ξ j ≤ Δ.points j.addone := by
      intro j
      have hj := h_repr j
      dsimp [InInterval] at hj
      rwa [if_pos (Δ.increase j)] at hj
    have h_repr' : Δ.IsRepr ξ' := by
      apply Partition.le_isrepr
      intro i
      by_cases hi : i.val = k.val
      · have hik : i = k := Subtype.ext hi
        rw [show ξ' i = x from if_pos hi, hik]
        exact ⟨hkL, hkR⟩
      · rw [show ξ' i = ξ i from if_neg hi]
        exact hr_bounds i
    -- 一点だけ代表点を変えた RS の差 = (f x - f (ξ k)) * length k
    have hdiff : RiemannSum f Δ ξ' - RiemannSum f Δ ξ =
        (f x - f (ξ k)) * Partition.length Δ k := by
      show Summation m (fun i => f (ξ' i) * Partition.length Δ i) -
          Summation m (fun i => f (ξ i) * Partition.length Δ i) = _
      have hterm : ∀ i : Range m, f (ξ' i) * Partition.length Δ i =
          f (ξ i) * Partition.length Δ i +
          (if i.val = k.val then (f x - f (ξ k)) * Partition.length Δ k
           else 0) := by
        intro i
        by_cases hi : i.val = k.val
        · have hik : i = k := Subtype.ext hi
          rw [show ξ' i = x from if_pos hi, if_pos hi, hik, ← add_mul, add_sub_cancel']
        · rw [show ξ' i = ξ i from if_neg hi, if_neg hi, add_zero]
      rw [summation_congr m _ _ hterm, additive_summation,
          summation_one_term m k _ (fun i hne => if_neg hne),
          if_pos (show k.val = k.val from rfl), add_sub_cancel]
    have hRS : (RiemannSum f Δ ξ - I).abs < 1 := hbound m Δ ξ h_repr h_diam
    have hRS' : (RiemannSum f Δ ξ' - I).abs < 1 := hbound m Δ ξ' h_repr' h_diam
    have h2 : ((f x - f (ξ k)) * Partition.length Δ k).abs < 2 := by
      rw [← hdiff]
      have hns : I - RiemannSum f Δ ξ = -(RiemannSum f Δ ξ - I) := by
        show I + -RiemannSum f Δ ξ = -(RiemannSum f Δ ξ + -I)
        rw [neg_add_distrib, neg_neg, add_comm]
      calc (RiemannSum f Δ ξ' - RiemannSum f Δ ξ).abs
          = ((I - RiemannSum f Δ ξ) + (RiemannSum f Δ ξ' - I)).abs := by
            rw [telescope_2 (RiemannSum f Δ ξ) (RiemannSum f Δ ξ') I]
        _ ≤ (I - RiemannSum f Δ ξ).abs + (RiemannSum f Δ ξ' - I).abs :=
            abs_triangle _ _
        _ = (RiemannSum f Δ ξ - I).abs + (RiemannSum f Δ ξ' - I).abs := by
            rw [hns, abs_neg]
        _ < 1 + 1 := lt_add_lt _ _ _ _ hRS hRS'
        _ = 2 := rfl
    have hlen : Partition.length Δ k = (b - a) / (m : Real) :=
      equalPartition_length m a b hm_ne hab k
    rw [hlen, abs_mul_nonneg hL_pos.1] at h2
    -- |f x - f (ξ k)| < 2 / L
    have hfk : (f x - f (ξ k)).abs < 2 / ((b - a) / (m : Real)) := by
      rw [← mul_div_cancel ((f x - f (ξ k)).abs) ((b - a) / (m : Real)) hL_ne]
      exact div_right_lt _ _ _ hL_pos h2
    calc (f x).abs
        = ((f x - f (ξ k)) + f (ξ k)).abs := by
          rw [show f x - f (ξ k) + f (ξ k) = f (ξ k) + (f x - f (ξ k)) from
                add_comm _ _,
              add_sub_cancel' (f (ξ k)) (f x)]
      _ ≤ (f x - f (ξ k)).abs + (f (ξ k)).abs := abs_triangle _ _
      _ ≤ 2 / ((b - a) / (m : Real)) + (f (ξ k)).abs :=
          LinearOrderedField.add_le_add _ _ _ (Real.le_of_lt hfk)
      _ ≤ 2 / ((b - a) / (m : Real)) + fmax' m (fun j => (f (ξ j)).abs) :=
          add_left_le _ _ _ (le_fmax' m (fun j => (f (ξ j)).abs) k)
