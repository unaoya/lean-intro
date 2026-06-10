import MyProject.Integral.RiemannSum

noncomputable section

-- リーマン和の細分比較（ステップ関数の原始関数による）

-- Helper: RS with same partition but different repr points differ by at most C*(b-a)
private theorem same_partition_bound (f : Real → Real) (a b C : Real)
    (n : Nat) (Δ : Partition n a b) (ξ ξ' : Range n → Real)
    (hclose : ∀ i, (f (ξ i) - f (ξ' i)).abs ≤ C) :
    (RiemannSum f Δ ξ - RiemannSum f Δ ξ').abs ≤ C * (b - a) := by
  -- Step 1: for each i, f(ξ_i)*len_i ≤ f(ξ'_i)*len_i + C*len_i
  have h_term : ∀ i : Range n,
      f (ξ i) * Δ.length i ≤ f (ξ' i) * Δ.length i + C * Δ.length i := by
    intro i
    have h1 : f (ξ i) ≤ f (ξ' i) + C := by
      have h2 := le_trans (le_abs _) (hclose i)
      have h3 := add_left_le (f (ξ' i)) (f (ξ i) - f (ξ' i)) C h2
      rw [add_sub_cancel' (f (ξ' i)) (f (ξ i))] at h3; exact h3
    have h4 := nonneg_mul_nonneg _ _ _ (Δ.length_nonneg i) h1
    rw [add_mul] at h4; exact h4
  -- Step 2: sum gives RS(ξ) ≤ RS(ξ') + C*(b-a)
  have h_upper : RiemannSum f Δ ξ ≤ RiemannSum f Δ ξ' + C * (b - a) := by
    have h5 := summation_le n _ _ h_term
    rw [additive_summation, summation_smul, Partition.length_sum] at h5
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
    have h5 := nonneg_mul_nonneg _ _ _ (Δ.length_nonneg i) h1
    rw [add_mul] at h5; exact h5
  have h_lower : RiemannSum f Δ ξ' ≤ RiemannSum f Δ ξ + C * (b - a) := by
    have h6 := summation_le n _ _ h_term'
    rw [additive_summation, summation_smul, Partition.length_sum] at h6; exact h6
  -- Step 4: combine using abs_le
  apply abs_le
  -- -(RS(ξ) - RS(ξ')) ≤ C*(b-a), i.e., RS(ξ') - RS(ξ) ≤ C*(b-a)
  · rw [neg_sub (RiemannSum f Δ ξ) (RiemannSum f Δ ξ')]
    have h7 := add_left_le (-(RiemannSum f Δ ξ)) (RiemannSum f Δ ξ')
        (RiemannSum f Δ ξ + C * (b - a)) h_lower
    have h8 : -(RiemannSum f Δ ξ) + (RiemannSum f Δ ξ + C * (b - a))
        = C * (b - a) := by
      rw [← add_assoc, add_comm (-(RiemannSum f Δ ξ))
          (RiemannSum f Δ ξ), AddCommGroup.add_neg, AddCommGroup.zero_add]
    rw [add_comm, h8] at h7; exact h7
  -- RS(ξ) - RS(ξ') ≤ C*(b-a)
  · have h7 := add_left_le (-(RiemannSum f Δ ξ')) (RiemannSum f Δ ξ)
        (RiemannSum f Δ ξ' + C * (b - a)) h_upper
    have h8 : -(RiemannSum f Δ ξ') + (RiemannSum f Δ ξ' + C * (b - a))
        = C * (b - a) := by
      rw [← add_assoc, add_comm (-(RiemannSum f Δ ξ'))
          (RiemannSum f Δ ξ'), AddCommGroup.add_neg, AddCommGroup.zero_add]
    rw [add_comm, h8] at h7; exact h7

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
theorem rs_compare (f : Real → Real) (a b M : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (hM_pos : 0 < M)
    (hab : a < b) (ε' θ : Real) (hθ : 0 < θ) (δuc : Real)
    (huc : ∀ s t, (a ≤ s ∧ s ≤ b) → (a ≤ t ∧ t ≤ b) → (s - t).abs < δuc →
      (f s - f t).abs < ε')
    (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) (hd : Partition.diam Δ < δuc) :
    ∃ δ', 0 < δ' ∧ ∀ (n' : Nat) (Δ' : Partition n' a b) (ξ' : Range n' → Real),
      Δ'.IsRepr ξ' → Partition.diam Δ' < δ' →
      (RiemannSum f Δ' ξ' - RiemannSum f Δ ξ).abs ≤ ε' * (b - a) + θ := by
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
    | zero => exact absurd (Partition.zero Δ') hab.2
    | succ m => exact Nat.zero_lt_succ m
  -- Δ の全分点を Δ' に挿入
  obtain ⟨Δp, ξp, hrp, hlenp, hptsp, hbdp⟩ :=
    rs_multi_insert_bound f M hM (Real.le_of_lt hM_pos) hn' Δ' ξ' hr'
      (n + 1) (fun j => Δ.points ⟨j.val, j.property⟩)
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
  -- 細分比較：|RS(Δp) − RS(Δ)| ≤ ε'(b−a)
  have hRCL : (RiemannSum f Δp ξp - RiemannSum f Δ ξ).abs ≤
      ε' * (b - a) := by
    rw [← rs_refine_eq f a b n Δ ξ (n' + (n + 1)) Δp (fun j => Classical.choose (hσex j)) hσ]
    apply same_partition_bound
    intro j
    apply Real.le_of_lt
    apply huc
    · exact in_interval_pair hab_le
        (Partition.repr_in_interval Δp ξp hrp j)
    · exact in_interval_pair hab_le
        (Partition.repr_in_interval Δ ξ hr (Classical.choose (hσex j)))
    · have hb1 := hrp j
      dsimp [Partition.IsRepr, InInterval] at hb1
      rw [if_pos (Δp.increase j)] at hb1
      have hb2 := hr (Classical.choose (hσex j))
      dsimp [Partition.IsRepr, InInterval] at hb2
      rw [if_pos (Δ.increase (Classical.choose (hσex j)))] at hb2
      have habs := abs_sub_le_of_mem
        (le_trans (hσ j).1 hb1.1) (le_trans hb1.2 (hσ j).2) hb2.1 hb2.2
      exact le_lt_trans
        (le_trans habs (le_fmax' n (Partition.length Δ) (Classical.choose (hσex j)))) hd
  -- 挿入誤差 ≤ θ
  have hins : (RiemannSum f Δp ξp - RiemannSum f Δ' ξ').abs ≤ θ := by
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
  calc (RiemannSum f Δ' ξ' - RiemannSum f Δ ξ).abs
      = ((RiemannSum f Δp ξp - RiemannSum f Δ ξ) +
         (RiemannSum f Δ' ξ' - RiemannSum f Δp ξp)).abs := by
        rw [telescope_2 (RiemannSum f Δ ξ) (RiemannSum f Δ' ξ')
            (RiemannSum f Δp ξp)]
    _ ≤ (RiemannSum f Δp ξp - RiemannSum f Δ ξ).abs +
        (RiemannSum f Δ' ξ' - RiemannSum f Δp ξp).abs :=
        abs_triangle _ _
    _ = (RiemannSum f Δp ξp - RiemannSum f Δ ξ).abs +
        (RiemannSum f Δp ξp - RiemannSum f Δ' ξ').abs := by
        rw [show RiemannSum f Δ' ξ' - RiemannSum f Δp ξp =
              -(RiemannSum f Δp ξp - RiemannSum f Δ' ξ') from
              (neg_sub _ _).symm, abs_neg]
    _ ≤ ε' * (b - a) + θ :=
        le_trans (LinearOrderedField.add_le_add _ _ _ hRCL) (add_left_le _ _ _ hins)
