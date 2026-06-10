import MyProject.Integral.Refine

noncomputable section

-- 振動和（区間ごとの sup f + sup(−f)）による |f| のリーマン和の比較評価

private theorem add_add_swap (p x y : Real) : (p + x) + (p + y) = (x + y) + (p + p) := by
  ac_rfl

-- 核心補題（|f| 版）：固定した細かい分割 Δ に対し、十分細かい任意の Δ' で
-- |RS_{|f|}(Δ') − RS_{|f|}(Δ)| ≤ (ε' + ε') + θ
theorem abs_rs_compare (f : Real → Real) (a b M If : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (hM_pos : 0 < M)
    (hab : a < b) (ε' θ : Real) (hθ : 0 < θ) (δf : Real)
    (hδf : ∀ (k : Nat) (Δk : Partition k a b) (ξk : Range k → Real),
      Δk.IsRepr ξk → Partition.diam Δk < δf →
      (RiemannSum f Δk ξk - If).abs < ε')
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) (hd : Partition.diam Δ < δf) :
    ∃ δ', 0 < δ' ∧ ∀ (n' : Nat) (Δ' : Partition n' a b) (ξ' : Range n' → Real),
      Δ'.IsRepr ξ' → Partition.diam Δ' < δ' →
      (RiemannSum (fun x => (f x).abs) Δ' ξ' -
       RiemannSum (fun x => (f x).abs) Δ ξ).abs ≤ (ε' + ε') + θ := by
  have hab_le : a ≤ b := hab.1
  have hba_pos : 0 < b - a := (pos_iff_lt a b).mp hab
  have hba_ne : b - a ≠ 0 := fun h0 => hba_pos.2 h0.symm
  -- 各小区間の点は [a,b] に入る
  have hmem_ab : ∀ (i : Range n) (t : Real),
      Δ.points (Range.incl i) ≤ t → t ≤ Δ.points (Range.addone i) → InInterval a b t := by
    intro i t h1 h2
    dsimp [InInterval]
    rw [if_pos hab_le]
    exact ⟨le_trans (Partition.left_le_point Δ (Range.incl i)) h1,
           le_trans h2 (Partition.point_le_right Δ (Range.addone i))⟩
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
  have hosc_sum : Summation n (fun i => Osc i * Partition.length Δ i) ≤ ε' + ε' := by
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
    have hu_repr : Δ.IsRepr (fun i => Classical.choose (hu i)) :=
      Partition.le_isrepr Δ _ (fun i => (hu_spec i).1)
    have hv_repr : Δ.IsRepr (fun i => Classical.choose (hv i)) :=
      Partition.le_isrepr Δ _ (fun i => (hv_spec i).1)
    -- 各項の評価
    have hterm : ∀ i : Range n, Osc i * Partition.length Δ i ≤
        ((f (Classical.choose (hu i)) - f (Classical.choose (hv i))) +
         (γ / 2 / (b - a) + γ / 2 / (b - a))) * Partition.length Δ i := by
      intro i
      apply nonneg_mul_nonneg _ _ _ (Partition.length_nonneg Δ i)
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
    have hRHS : Summation n (fun i => ((f (Classical.choose (hu i)) -
        f (Classical.choose (hv i))) + (γ / 2 / (b - a) + γ / 2 / (b - a))) *
        Partition.length Δ i) =
        (RiemannSum f Δ (fun i => Classical.choose (hu i)) -
         RiemannSum f Δ (fun i => Classical.choose (hv i))) + γ := by
      calc Summation n (fun i => ((f (Classical.choose (hu i)) -
              f (Classical.choose (hv i))) + (γ / 2 / (b - a) + γ / 2 / (b - a))) *
              Partition.length Δ i)
          = Summation n (fun i => (f (Classical.choose (hu i)) -
              f (Classical.choose (hv i))) * Partition.length Δ i +
              (γ / 2 / (b - a) + γ / 2 / (b - a)) * Partition.length Δ i) :=
            summation_congr n _ _ (fun i => add_mul _ _ _)
        _ = Summation n (fun i => (f (Classical.choose (hu i)) -
              f (Classical.choose (hv i))) * Partition.length Δ i) +
            Summation n (fun i => (γ / 2 / (b - a) + γ / 2 / (b - a)) *
              Partition.length Δ i) := additive_summation n _ _
        _ = (RiemannSum f Δ (fun i => Classical.choose (hu i)) -
             RiemannSum f Δ (fun i => Classical.choose (hv i))) + γ := by
            rw [summation_smul, Partition.length_sum]
            congr 1
            · calc Summation n (fun i => (f (Classical.choose (hu i)) -
                    f (Classical.choose (hv i))) * Partition.length Δ i)
                  = Summation n (fun i =>
                      f (Classical.choose (hu i)) * Partition.length Δ i -
                      f (Classical.choose (hv i)) * Partition.length Δ i) :=
                    summation_congr n _ _ (fun i => (mul_sub_mul _ _ _).symm)
                _ = RiemannSum f Δ (fun i => Classical.choose (hu i)) -
                    RiemannSum f Δ (fun i => Classical.choose (hv i)) :=
                    (sub_summation n _ _).symm
            · rw [add_mul, div_mul_cancel' (γ / 2) (b - a) hba_ne, half_add]
    rw [hRHS] at hsum
    -- RS の差を If 経由で評価
    have hu_close := hδf n Δ (fun i => Classical.choose (hu i)) hu_repr hd
    have hv_close := hδf n Δ (fun i => Classical.choose (hv i)) hv_repr hd
    have hdiff : RiemannSum f Δ (fun i => Classical.choose (hu i)) -
        RiemannSum f Δ (fun i => Classical.choose (hv i)) ≤ ε' + ε' := by
      have heq : RiemannSum f Δ (fun i => Classical.choose (hu i)) -
          RiemannSum f Δ (fun i => Classical.choose (hv i)) =
          (If - RiemannSum f Δ (fun i => Classical.choose (hv i))) +
          (RiemannSum f Δ (fun i => Classical.choose (hu i)) - If) :=
        telescope_2 _ _ _
      rw [heq]
      apply Real.le_of_lt
      apply lt_add_lt
      · rw [show If - RiemannSum f Δ (fun i => Classical.choose (hv i)) =
              -(RiemannSum f Δ (fun i => Classical.choose (hv i)) - If) from
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
    | zero => exact absurd (Partition.zero Δ') hab.2
    | succ m => exact Nat.zero_lt_succ m
  have hMg : ∀ t, InInterval a b t → ((fun x => (f x).abs) t).abs ≤ M := by
    intro t ht
    rw [nonneg_abs abs_nonneg]
    exact hM t ht
  obtain ⟨Δp, ξp, hrp, hlenp, hptsp, hbdp⟩ :=
    rs_multi_insert_bound (fun x => (f x).abs) M hMg (Real.le_of_lt hM_pos)
      hn' Δ' ξ' hr' (n + 1) (fun j => Δ.points ⟨j.val, j.property⟩)
      (fun j => Partition.points_in_interval Δ ⟨j.val, j.property⟩)
  have hpts_all : ∀ i : Range n.succ,
      ∃ q : Range (n' + (n + 1)).succ, Δp.points q = Δ.points i := by
    intro i
    obtain ⟨q, hq⟩ := hptsp ⟨i.val, i.property⟩
    exact ⟨q, hq⟩
  have hn_pos : 0 < n := by
    cases n with
    | zero => exact absurd (Partition.zero Δ) hab.2
    | succ m => exact Nat.zero_lt_succ m
  have hσex := refine_parent a b n (n' + (n + 1)) hn_pos Δ Δp hpts_all
  have hσ : ∀ j : Range (n' + (n + 1)),
      Δ.points (Range.incl (Classical.choose (hσex j))) ≤ Δp.points (Range.incl j) ∧
      Δp.points (Range.addone j) ≤ Δ.points (Range.addone (Classical.choose (hσex j))) :=
    fun j => Classical.choose_spec (hσex j)
  -- 細分比較：|RS_g(Δp) − RS_g(Δ)| ≤ ε' + ε'
  have hRCL : (RiemannSum (fun x => (f x).abs) Δp ξp -
      RiemannSum (fun x => (f x).abs) Δ ξ).abs ≤ ε' + ε' := by
    rw [← rs_refine_eq (fun x => (f x).abs) a b n Δ ξ (n' + (n + 1)) Δp
        (fun j => Classical.choose (hσex j)) hσ]
    have hsub : RiemannSum (fun x => (f x).abs) Δp ξp -
        RiemannSum (fun x => (f x).abs) Δp
          (fun j => ξ (Classical.choose (hσex j))) =
        Summation (n' + (n + 1)) (fun j =>
          ((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
          Partition.length Δp j) := by
      calc RiemannSum (fun x => (f x).abs) Δp ξp -
            RiemannSum (fun x => (f x).abs) Δp
              (fun j => ξ (Classical.choose (hσex j)))
          = Summation (n' + (n + 1)) (fun j =>
              (f (ξp j)).abs * Partition.length Δp j -
              (f (ξ (Classical.choose (hσex j)))).abs *
                Partition.length Δp j) :=
            sub_summation (n' + (n + 1))
              (fun j => (f (ξp j)).abs * Partition.length Δp j)
              (fun j => (f (ξ (Classical.choose (hσex j)))).abs *
                Partition.length Δp j)
        _ = Summation (n' + (n + 1)) (fun j =>
              ((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
              Partition.length Δp j) :=
            summation_congr _ _ _ (fun j => mul_sub_mul _ _ _)
    rw [hsub]
    have hperj : ∀ j : Range (n' + (n + 1)),
        ((((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
          Partition.length Δp j)).abs ≤
        Osc (Classical.choose (hσex j)) * Partition.length Δp j := by
      intro j
      rw [abs_mul_nonneg (Partition.length_nonneg Δp j)]
      apply nonneg_mul_nonneg _ _ _ (Partition.length_nonneg Δp j)
      have hb1 := hrp j
      dsimp [Partition.IsRepr, InInterval] at hb1
      rw [if_pos (Δp.increase j)] at hb1
      have hb2 := hr (Classical.choose (hσex j))
      dsimp [Partition.IsRepr, InInterval] at hb2
      rw [if_pos (Δ.increase (Classical.choose (hσex j)))] at hb2
      exact hosc (Classical.choose (hσex j)) (ξp j) (ξ (Classical.choose (hσex j)))
        (le_trans (hσ j).1 hb1.1) (le_trans hb1.2 (hσ j).2) hb2.1 hb2.2
    calc (Summation (n' + (n + 1)) (fun j =>
            ((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
            Partition.length Δp j)).abs
        ≤ Summation (n' + (n + 1)) (fun j =>
            ((((f (ξp j)).abs - (f (ξ (Classical.choose (hσex j)))).abs) *
              Partition.length Δp j)).abs) := abs_summation_le _ _
      _ ≤ Summation (n' + (n + 1)) (fun j =>
            Osc (Classical.choose (hσex j)) * Partition.length Δp j) :=
          summation_le _ _ _ hperj
      _ = Summation n (fun i => Osc i * Partition.length Δ i) :=
          rs_refine_eq (fun t => t) a b n Δ Osc (n' + (n + 1)) Δp
            (fun j => Classical.choose (hσex j)) hσ
      _ ≤ ε' + ε' := hosc_sum
  -- 挿入誤差 ≤ θ
  have hins : (RiemannSum (fun x => (f x).abs) Δp ξp -
      RiemannSum (fun x => (f x).abs) Δ' ξ').abs ≤ θ := by
    apply le_trans hbdp
    rw [show Real.ofNat (n + 1) * (2 * M * Partition.diam Δ') =
          Real.ofNat (n + 1) * (2 * M) * Partition.diam Δ' from
          (mul_assoc _ _ _).symm]
    apply le_trans (mul_le_mul_left (Real.ofNat (n + 1) * (2 * M)) _ _
      (Real.le_of_lt hK_pos) (Real.le_of_lt hd'))
    rw [← mul_div_assoc, mul_comm (Real.ofNat (n + 1) * (2 * M)) θ,
        mul_div_cancel θ _ hK_ne]
    exact le_refl θ
  -- 三角不等式で合成
  calc (RiemannSum (fun x => (f x).abs) Δ' ξ' -
        RiemannSum (fun x => (f x).abs) Δ ξ).abs
      = ((RiemannSum (fun x => (f x).abs) Δp ξp -
          RiemannSum (fun x => (f x).abs) Δ ξ) +
         (RiemannSum (fun x => (f x).abs) Δ' ξ' -
          RiemannSum (fun x => (f x).abs) Δp ξp)).abs := by
        rw [telescope_2 (RiemannSum (fun x => (f x).abs) Δ ξ)
            (RiemannSum (fun x => (f x).abs) Δ' ξ')
            (RiemannSum (fun x => (f x).abs) Δp ξp)]
    _ ≤ (RiemannSum (fun x => (f x).abs) Δp ξp -
         RiemannSum (fun x => (f x).abs) Δ ξ).abs +
        (RiemannSum (fun x => (f x).abs) Δ' ξ' -
         RiemannSum (fun x => (f x).abs) Δp ξp).abs :=
        abs_triangle _ _
    _ = (RiemannSum (fun x => (f x).abs) Δp ξp -
         RiemannSum (fun x => (f x).abs) Δ ξ).abs +
        (RiemannSum (fun x => (f x).abs) Δp ξp -
         RiemannSum (fun x => (f x).abs) Δ' ξ').abs := by
        rw [show RiemannSum (fun x => (f x).abs) Δ' ξ' -
              RiemannSum (fun x => (f x).abs) Δp ξp =
              -(RiemannSum (fun x => (f x).abs) Δp ξp -
                RiemannSum (fun x => (f x).abs) Δ' ξ') from
              (neg_sub _ _).symm, abs_neg]
    _ ≤ (ε' + ε') + θ :=
        le_trans (LinearOrderedField.add_le_add _ _ _ hRCL) (add_left_le _ _ _ hins)
