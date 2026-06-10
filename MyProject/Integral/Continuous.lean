import MyProject.Integral.UnifCont
import MyProject.Integral.Refine
import MyProject.Integral.Def

-- 連続関数の可積分性

theorem continuous_integrable (f : Real → Real) (a x : Real) (hf : Continuous f) :
  ∃ i, IsIntegral f a x i := by
  cases Classical.em (a ≤ x) with
  | inr h =>
    -- a > x: no partition exists, IsIntegral is vacuously true
    exact ⟨0, fun ε hε => ⟨1, zero_lt_one, fun n Δ ξ _ _ =>
      absurd (Partition.left_le_right Δ) h⟩⟩
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
        have hRS : RiemannSum f Δ ξ = RiemannSum (fun _ => f a) Δ ξ := by
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
          Δ.IsRepr ξ → Partition.diam Δ < δ → y ≤ RiemannSum f Δ ξ
      -- S is nonempty: -(M*(x-a)) ∈ S
      have hS_ne : ∃ y, S y := by
        refine ⟨-(M * (x - a)), 1, zero_lt_one, fun n Δ ξ hr _ => ?_⟩
        have h_rs := rs_abs_bound f M hM_bound Δ ξ hr
        -- |RS| ≤ M*(x-a) → -(M*(x-a)) ≤ RS via neg_le_swap
        have h1 : -(RiemannSum f Δ ξ) ≤ M * (x - a) :=
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
        exact le_trans h_le (le_trans (le_abs _) (rs_abs_bound f M hM_bound Δ ξ h_repr))
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
          Partition.IsRepr Δ' ξ' → Partition.diam Δ' < δ' →
          (RiemannSum f Δ' ξ' - RiemannSum f Δ ξ).abs ≤
            ε / 2 + ε / 2 / 2 := by
        intro n' Δ' ξ' hr' hd'
        have h := hcomp n' Δ' ξ' hr' hd'
        rwa [hdmc] at h
      -- 下から：RS − (ε/2 + ε/4) ∈ S
      have hmem : S (RiemannSum f Δ ξ - (ε / 2 + ε / 2 / 2)) := by
        refine ⟨δ', hδ'_pos, fun n' Δ' ξ' hr' hd' => ?_⟩
        have h := hbound n' Δ' ξ' hr' hd'
        have h2 : RiemannSum f Δ ξ - RiemannSum f Δ' ξ' ≤
            ε / 2 + ε / 2 / 2 := by
          apply le_trans (le_abs _)
          rw [show RiemannSum f Δ ξ - RiemannSum f Δ' ξ' =
                -(RiemannSum f Δ' ξ' - RiemannSum f Δ ξ) from
                (neg_sub _ _).symm, abs_neg]
          exact h
        exact sub_le_swap h2
      have h_lower := Real.sup_ub S hS_ne hS_bdd _ hmem
      -- 上から：I ≤ RS + (ε/2 + ε/4)
      have h_upper : I ≤ RiemannSum f Δ ξ + (ε / 2 + ε / 2 / 2) := by
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
        have hEd : Partition.diam
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
      have habs : (RiemannSum f Δ ξ - I).abs ≤ ε / 2 + ε / 2 / 2 := by
        apply abs_le
        · rw [neg_sub]
          exact sub_le_of_le_add h_upper
        · exact sub_le_swap h_lower
      have hBlt : ε / 2 + ε / 2 / 2 < ε := by
        have h := add_left_lt (ε / 2) (ε / 2 / 2) (ε / 2) (half_lt (pos_half ε hε))
        rwa [half_add ε] at h
      exact le_lt_trans habs hBlt

