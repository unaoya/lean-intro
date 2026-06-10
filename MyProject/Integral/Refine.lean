import MyProject.Integral.RiemannSum

noncomputable section

-- リーマン和の細分比較（ステップ関数の原始関数による）

-- Helper: RS with same partition but different repr points differ by at most C*(b-a)
private theorem same_partition_bound (f : Real → Real) (a b C : Real)
    (n : Nat) (Δ : Partition n a b) (ξ ξ' : Range n → Real)
    (hclose : ∀ i, (f (ξ i) - f (ξ' i)).abs ≤ C) :
    (RiemannSum f Δ ξ - RiemannSum f Δ ξ').abs ≤ C * (b - a) := by
  have hsub : RiemannSum f Δ ξ - RiemannSum f Δ ξ' =
      Summation n (fun i => (f (ξ i) - f (ξ' i)) * Partition.length Δ i) := by
    calc RiemannSum f Δ ξ - RiemannSum f Δ ξ'
        = Summation n (fun i => f (ξ i) * Partition.length Δ i -
            f (ξ' i) * Partition.length Δ i) := sub_summation n _ _
      _ = Summation n (fun i => (f (ξ i) - f (ξ' i)) * Partition.length Δ i) :=
          summation_congr n _ _ (fun i => mul_sub_mul _ _ _)
  rw [hsub]
  apply le_trans (abs_summation_le _ _)
  have hterm : ∀ i, ((f (ξ i) - f (ξ' i)) * Partition.length Δ i).abs ≤
      C * Partition.length Δ i := by
    intro i
    rw [abs_mul_nonneg (Δ.length_nonneg i)]
    exact nonneg_mul_nonneg _ _ _ (Δ.length_nonneg i) (hclose i)
  apply le_trans (summation_le n _ _ hterm)
  rw [summation_smul, Partition.length_sum]
  exact le_refl _

-- ============================================================
-- continuous_integrable 用の細分比較補題群
-- ============================================================

-- 区分定数関数の原始関数：G(t) = Σ_i f(ξ_i)·(min t p_{i+1} − min t p_i)
private noncomputable def stepAnti (f : Real → Real) (n : Nat) (a b : Real)
    (Δ : Partition n a b) (ξ : Range n → Real) (t : Real) : Real :=
  Summation n (fun i => f (ξ i) *
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
          mul_comm (f (ξ σ)) (d - Δ.points (Range.incl σ)),
          mul_comm (f (ξ σ)) (c - Δ.points (Range.incl σ)),
          mul_sub_mul,
          show d - Δ.points (Range.incl σ) - (c - Δ.points (Range.incl σ)) = d - c from by
            show d + -Δ.points (Range.incl σ) - (c + -Δ.points (Range.incl σ)) = d - c
            rw [add_sub_add, sub_self, add_zero],
          mul_comm]
    · rw [if_neg hiσ]
      by_cases hlt : i.val < σ.val
      · -- 小区間 i は [P,Q] の左側
        have h1 : Δ.points (Range.addone i) ≤ c :=
          le_trans (Partition.points_mono Δ (Range.addone i) (Range.incl σ)
            (by simp only [Range.addone_val, Range.incl_val]; omega)) hc
        have h2 : Δ.points (Range.incl i) ≤ c := le_trans (Δ.increase i) h1
        have h1d : Δ.points (Range.addone i) ≤ d := le_trans h1 hcd
        have h2d : Δ.points (Range.incl i) ≤ d := le_trans h2 hcd
        rw [min_eq_right h1d, min_eq_right h2d, min_eq_right h1, min_eq_right h2,
            sub_self]
      · -- 小区間 i は [P,Q] の右側
        have h1 : d ≤ Δ.points (Range.incl i) :=
          le_trans hd (Partition.points_mono Δ (Range.addone σ) (Range.incl i)
            (by simp only [Range.addone_val, Range.incl_val]; omega))
        have h2 : d ≤ Δ.points (Range.addone i) := le_trans h1 (Δ.increase i)
        have h1c : c ≤ Δ.points (Range.incl i) := le_trans hcd h1
        have h2c : c ≤ Δ.points (Range.addone i) := le_trans hcd h2
        rw [min_eq_left h2, min_eq_left h1, min_eq_left h2c, min_eq_left h1c,
            sub_self d, sub_self c,
            show f (ξ i) * (0 : Real) = 0 from by
              rw [mul_comm]; exact zero_mul' _,
            sub_self]
  calc stepAnti f n a b Δ ξ d - stepAnti f n a b Δ ξ c
      = Summation n (fun i =>
          f (ξ i) * (min d (Δ.points (Range.addone i)) - min d (Δ.points (Range.incl i))) -
          f (ξ i) * (min c (Δ.points (Range.addone i)) - min c (Δ.points (Range.incl i)))) :=
        sub_summation n _ _
    _ = Summation n (fun i => if i.val = σ.val then f (ξ σ) * (d - c) else 0) :=
        summation_congr n _ _ hterm
    _ = (if σ.val = σ.val then f (ξ σ) * (d - c) else 0) :=
        summation_one_term n σ _ (fun i hne => if_neg hne)
    _ = f (ξ σ) * (d - c) := if_pos rfl

-- 細分上で親区間の代表点を使った RS は元の RS に等しい
theorem rs_refine_eq (f : Real → Real) (a b : Real)
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (N : Nat) (Δ' : Partition N a b) (σ : Range N → Range n)
    (hσ : ∀ j : Range N,
      Δ.points (Range.incl (σ j)) ≤ Δ'.points (Range.incl j) ∧
      Δ'.points (Range.addone j) ≤ Δ.points (Range.addone (σ j))) :
    RiemannSum f Δ' (fun j => ξ (σ j)) = RiemannSum f Δ ξ := by
  have hGb : stepAnti f n a b Δ ξ b = RiemannSum f Δ ξ := by
    apply summation_congr
    intro i
    rw [min_eq_right (Partition.point_le_right Δ (Range.addone i)),
        min_eq_right (Partition.point_le_right Δ (Range.incl i))]
    rfl
  have hGa : stepAnti f n a b Δ ξ a = 0 := by
    have hz : ∀ i : Range n, f (ξ i) *
        (min a (Δ.points (Range.addone i)) - min a (Δ.points (Range.incl i))) = 0 := by
      intro i
      rw [min_eq_left (Partition.left_le_point Δ (Range.addone i)),
          min_eq_left (Partition.left_le_point Δ (Range.incl i)), sub_self,
          mul_comm]
      exact zero_mul' _
    calc stepAnti f n a b Δ ξ a
        = Summation n (fun _ => (0 : Real)) := summation_congr n _ _ hz
      _ = 0 := summation_all_zero n
  have hjterm : ∀ j : Range N,
      f (ξ (σ j)) * Partition.length Δ' j =
      stepAnti f n a b Δ ξ (Δ'.points (Range.addone j)) -
      stepAnti f n a b Δ ξ (Δ'.points (Range.incl j)) := fun j =>
    (stepAnti_inc f n a b Δ ξ (σ j) (Δ'.points (Range.incl j)) (Δ'.points (Range.addone j))
      (hσ j).1 (Δ'.increase j) (hσ j).2).symm
  calc RiemannSum f Δ' (fun j => ξ (σ j))
      = Summation N (fun j => stepAnti f n a b Δ ξ (Δ'.points (Range.addone j)) -
                             stepAnti f n a b Δ ξ (Δ'.points (Range.incl j))) :=
        summation_congr N _ _ hjterm
    _ = stepAnti f n a b Δ ξ (Δ'.points ⟨N, Nat.lt_add_one N⟩) -
        stepAnti f n a b Δ ξ (Δ'.points ⟨0, Nat.zero_lt_succ N⟩) :=
        telescope_sum N (fun r => stepAnti f n a b Δ ξ (Δ'.points r))
    _ = stepAnti f n a b Δ ξ b - stepAnti f n a b Δ ξ a := by rw [Δ'.right, Δ'.left]
    _ = RiemannSum f Δ ξ - 0 := by rw [hGb, hGa]
    _ = RiemannSum f Δ ξ := sub_zero _

-- Δ の全分点が Δ'' の分点に含まれるなら、Δ'' の各小区間は Δ のある小区間に含まれる
theorem refine_parent (a b : Real) (n N : Nat) (hn : 0 < n)
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
    exact Partition.point_le_right Δ'' (Range.addone j)
  rcases has_min p hp with ⟨k, ⟨hkn, hkle⟩, hmin⟩
  refine ⟨⟨k, hkn⟩, ?_, hkle⟩
  show Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ ≤ Δ''.points (Range.incl j)
  cases Classical.em (k = 0) with
  | inl hk0 =>
    subst hk0
    rw [Δ.left]
    exact Partition.left_le_point Δ'' (Range.incl j)
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
        Partition.points_mono Δ'' (Range.addone j) r hjr
      rw [hr] at h2
      exact (le_lt_trans h2 hlt).2 rfl
    | inr hrj =>
      rw [← hr]
      exact Partition.points_mono Δ'' r (Range.incl j) hrj

-- 核心補題：固定した細かい分割 Δ に対し、十分細かい任意の Δ' の RS は RS(Δ) に近い
-- 共通エンベロープ：固定した分割 Δ の全分点を任意の細かい分割 Δ' に挿入し、
-- 細分上の比較（hcore）と挿入誤差 θ を合成する
theorem rs_refine_compare (g : Real → Real) {a b : Real} (M : Real)
    (hMg : ∀ t, InInterval a b t → (g t).abs ≤ M) (hM_pos : 0 < M)
    (hab : a < b) {n : Nat} (Δ : Partition n a b) (ξ : Range n → Real)
    (B θ : Real) (hθ : 0 < θ)
    (hcore : ∀ (N : Nat) (Δp : Partition N a b) (ξp : Range N → Real),
      Δp.IsRepr ξp → ∀ (σ : Range N → Range n),
      (∀ j, Δ.points (Range.incl (σ j)) ≤ Δp.points (Range.incl j) ∧
            Δp.points (Range.addone j) ≤ Δ.points (Range.addone (σ j))) →
      (RiemannSum g Δp ξp - RiemannSum g Δ ξ).abs ≤ B) :
    ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition a b, Partition.diam P'.Δ < δ' →
      (RiemannSum g P'.Δ P'.ξ - RiemannSum g Δ ξ).abs ≤ B + θ := by
  have hofn_pos : (0 : Real) < Real.ofNat (n + 1) := cast_lt 0 (n + 1) (Nat.zero_lt_succ n)
  have hK_pos : (0 : Real) < Real.ofNat (n + 1) * (2 * M) :=
    pos_mul_pos _ _ hofn_pos (pos_mul_pos 2 M zero_lt_two hM_pos)
  have hK_ne : Real.ofNat (n + 1) * (2 * M) ≠ 0 := fun h0 => hK_pos.2 h0.symm
  refine ⟨θ / (Real.ofNat (n + 1) * (2 * M)), pos_div_pos _ _ hθ hK_pos, ?_⟩
  intro ⟨n', Δ', ξ', hr'⟩ hd'
  have hn' : 0 < n' := Δ'.pos_of_lt hab
  -- Δ の全分点を Δ' に挿入
  obtain ⟨Δp, ξp, hrp, _, hptsp, hbdp⟩ :=
    rs_multi_insert_bound g M hMg (Real.le_of_lt hM_pos) hn' Δ' ξ' hr'
      (n + 1) (fun j => Δ.points ⟨j.val, j.property⟩)
      (fun j => Partition.points_in_interval Δ ⟨j.val, j.property⟩)
  have hpts_all : ∀ i : Range n.succ,
      ∃ q : Range (n' + (n + 1)).succ, Δp.points q = Δ.points i := by
    intro i
    obtain ⟨q, hq⟩ := hptsp ⟨i.val, i.property⟩
    exact ⟨q, hq⟩
  have hσex := refine_parent a b n (n' + (n + 1)) (Δ.pos_of_lt hab) Δ Δp hpts_all
  -- 細分上の比較（核心評価）
  have hRCL := hcore (n' + (n + 1)) Δp ξp hrp (fun j => Classical.choose (hσex j))
    (fun j => Classical.choose_spec (hσex j))
  -- 挿入誤差 ≤ θ
  have hins : (RiemannSum g Δp ξp - RiemannSum g Δ' ξ').abs ≤ θ := by
    apply le_trans hbdp
    rw [show Real.ofNat (n + 1) * (2 * M * Partition.diam Δ') =
          Real.ofNat (n + 1) * (2 * M) * Partition.diam Δ' from (mul_assoc _ _ _).symm]
    apply le_trans (mul_le_mul_left (Real.ofNat (n + 1) * (2 * M)) _ _
      (Real.le_of_lt hK_pos) (Real.le_of_lt hd'))
    rw [← mul_div_assoc, mul_comm (Real.ofNat (n + 1) * (2 * M)) θ,
        mul_div_cancel θ _ hK_ne]
    exact le_refl θ
  -- 三角不等式で合成
  calc (RiemannSum g Δ' ξ' - RiemannSum g Δ ξ).abs
      ≤ (RiemannSum g Δ' ξ' - RiemannSum g Δp ξp).abs +
        (RiemannSum g Δp ξp - RiemannSum g Δ ξ).abs := abs_sub_le_add _ _ _
    _ = (RiemannSum g Δp ξp - RiemannSum g Δ' ξ').abs +
        (RiemannSum g Δp ξp - RiemannSum g Δ ξ).abs := by
        rw [abs_sub_comm (RiemannSum g Δ' ξ')]
    _ ≤ θ + B :=
        le_trans (LinearOrderedField.add_le_add _ _ _ hins) (add_left_le _ _ _ hRCL)
    _ = B + θ := add_comm θ B

-- 核心補題：固定した細かい分割 Δ に対し、十分細かい任意の Δ' の RS は RS(Δ) に近い
-- （一様連続性で細分上の比較を評価する）
theorem rs_compare (f : Real → Real) (a b M : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (hM_pos : 0 < M)
    (hab : a < b) (ε' θ : Real) (hθ : 0 < θ) (δuc : Real)
    (huc : ∀ s t, (a ≤ s ∧ s ≤ b) → (a ≤ t ∧ t ≤ b) → (s - t).abs < δuc →
      (f s - f t).abs < ε')
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) (hd : Partition.diam Δ < δuc) :
    ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition a b, Partition.diam P'.Δ < δ' →
      (RiemannSum f P'.Δ P'.ξ - RiemannSum f Δ ξ).abs ≤ ε' * (b - a) + θ := by
  apply rs_refine_compare f M hM hM_pos hab Δ ξ (ε' * (b - a)) θ hθ
  intro N Δp ξp hrp σ hσ
  rw [← rs_refine_eq f a b n Δ ξ N Δp σ hσ]
  apply same_partition_bound
  intro j
  apply Real.le_of_lt
  apply huc
  · exact in_interval_pair hab.1 (Partition.repr_in_interval Δp ξp hrp j)
  · exact in_interval_pair hab.1 (Partition.repr_in_interval Δ ξ hr (σ j))
  · have hb1 := Partition.repr_bounds hrp j
    have hb2 := Partition.repr_bounds hr (σ j)
    have habs := abs_sub_le_of_mem
      (le_trans (hσ j).1 hb1.1) (le_trans hb1.2 (hσ j).2) hb2.1 hb2.2
    exact le_lt_trans
      (le_trans habs (le_fmax' n (Partition.length Δ) (σ j))) hd
