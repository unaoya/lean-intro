-- Text/E3_Refine.lean — 発展部 §3: 細分比較（σ 写像とエンベロープ）
-- 固定した分割 Δ の全分点を任意の細かい分割 Δ' に挿入して共通細分 Δp を作り、
--   ・細分上で親の代表点を使った RS は元の RS に等しい（rs_refine_eq、ステップ原始関数）
--   ・挿入誤差は B2 の評価で θ 以下に抑えられる
-- を合成して rs_compare（コーシー条件の素材）を得る。
-- 注意: 証明装置 stepAnti は rmin（Ch11 の素朴 if 定義の min）を使う——
-- これを使う定理の公理監査には choice が現れる（素朴定義実験の実戦版）。
import Text.E2_InsertBound

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 小物（NearLe の対称性・同一区間の 2 点の近さ・分割の非退化）
-- ============================================================

theorem nearle_symm {c x y : Real} (h : NearLe c x y) : NearLe c y x := by
  constructor
  · have h1 := sub_le_sub_right h.2 c
    rwa [add_sub_cancel_right] at h1
  · have h1 := add_le_add_right (x - c) y c h.1
    rwa [sub_add_cancel] at h1

-- 同じ区間 [A, B] に属する 2 点は B − A < δ なら δ-近い
theorem near_of_mem {A B s t δ : Real} (hsA : A ≤ s) (hsB : s ≤ B)
    (htA : A ≤ t) (htB : t ≤ B) (hlen : B - A < δ) : Near δ s t := by
  constructor
  · have h1 : s - t ≤ B - A := add_le_add' hsB (neg_le_neg' htA)
    exact sub_lt_swap (le_lt_trans h1 hlen)
  · have h1 : t - s ≤ B - A := add_le_add' htB (neg_le_neg' hsA)
    have h2 := lt_add_of_sub_lt (le_lt_trans h1 hlen)
    rwa [add_comm δ s] at h2

-- u < v なら分割は空でない（n = 0 だと左右の端点公理が衝突する）
theorem Partition.pos_of_lt {n : Nat} {u v : Real} (Δ : Partition n u v)
    (huv : u < v) : 0 < n := by
  cases Nat.eq_zero_or_pos n with
  | inl h0 =>
    exfalso
    subst h0
    exact huv.2 (Δ.left.symm.trans Δ.right)
  | inr h => exact h

-- ============================================================
-- §2 同一分割・別タグの RS の差: NearLe (C·(v−u))
-- ============================================================

theorem same_partition_bound (f : Real → Real) {u v : Real} (C : Real)
    {n : Nat} (Δ : Partition n u v) (ξ ξ' : Range n → Real)
    (hclose : ∀ i, -C ≤ f (ξ' i) - f (ξ i) ∧ f (ξ' i) - f (ξ i) ≤ C) :
    NearLe (C * (v - u)) (RiemannSum f Δ ξ) (RiemannSum f Δ ξ') := by
  have hD : RiemannSum f Δ ξ' - RiemannSum f Δ ξ
      = Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i) := by
    calc RiemannSum f Δ ξ' - RiemannSum f Δ ξ
        = Summation n (fun i => f (ξ' i) * Δ.length i - f (ξ i) * Δ.length i) :=
          sub_summation n _ _
      _ = Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i) :=
          summation_congr n _ _ (fun i => mul_sub_mul _ _ _)
  have hhi : Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i) ≤ C * (v - u) := by
    have h1 : Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i)
        ≤ Summation n (fun i => C * Δ.length i) :=
      summation_le n _ _ (fun i =>
        nonneg_mul_nonneg _ _ _ (length_nonneg Δ i) (hclose i).2)
    rw [summation_mul_left n (fun i => Δ.length i) C, length_sum Δ] at h1
    exact h1
  have hlo : -(C * (v - u)) ≤ Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i) := by
    have h1 : Summation n (fun i => (-C) * Δ.length i)
        ≤ Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i) :=
      summation_le n _ _ (fun i =>
        nonneg_mul_nonneg _ _ _ (length_nonneg Δ i) (hclose i).1)
    rw [summation_mul_left n (fun i => Δ.length i) (-C), length_sum Δ, neg_mul] at h1
    exact h1
  have hsum : RiemannSum f Δ ξ' = RiemannSum f Δ ξ
      + Summation n (fun i => (f (ξ' i) - f (ξ i)) * Δ.length i) := by
    rw [← hD]
    exact (add_sub_cancel' _ _).symm
  rw [hsum]
  exact nearle_of_add hlo hhi

-- ============================================================
-- §3 ステップ原始関数（証明装置。rmin の if が choice の源）
-- ============================================================

-- 区分定数関数の原始関数: G(t) = Σᵢ f(ξᵢ)·(min t pᵢ₊₁ − min t pᵢ)
noncomputable def stepAnti (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) (t : Real) : Real :=
  Summation n (fun i => f (ξ i) *
    (rmin t (Δ.points (addone i)) - rmin t (Δ.points (incl i))))

-- 同一小区間 [p_σ, p_{σ+1}] 内の c ≤ d に対する増分
theorem stepAnti_inc (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) (σ : Range n) (c d : Real)
    (hc : Δ.points (incl σ) ≤ c) (hcd : c ≤ d) (hd : d ≤ Δ.points (addone σ)) :
    stepAnti f Δ ξ d - stepAnti f Δ ξ c = f (ξ σ) * (d - c) := by
  have hterm : ∀ i : Range n,
      f (ξ i) * (rmin d (Δ.points (addone i)) - rmin d (Δ.points (incl i))) -
      f (ξ i) * (rmin c (Δ.points (addone i)) - rmin c (Δ.points (incl i))) =
      (if i.val = σ.val then f (ξ σ) * (d - c) else 0) := by
    intro i
    by_cases hiσ : i.val = σ.val
    · rw [if_pos hiσ]
      have hi : i = σ := Subtype.ext hiσ
      rw [hi, rmin_eq_left hd, rmin_eq_right (le_trans hc hcd),
          rmin_eq_left (le_trans hcd hd), rmin_eq_right hc,
          mul_comm (f (ξ σ)) (d - Δ.points (incl σ)),
          mul_comm (f (ξ σ)) (c - Δ.points (incl σ)),
          mul_sub_mul,
          show d - Δ.points (incl σ) - (c - Δ.points (incl σ)) = d - c from by
            show d + -Δ.points (incl σ) - (c + -Δ.points (incl σ)) = d - c
            rw [add_sub_add, sub_self, add_zero],
          mul_comm]
    · rw [if_neg hiσ]
      by_cases hlt : i.val < σ.val
      · -- 小区間 i は [c, d] の左側: すべての min が右側で確定
        have h1 : Δ.points (addone i) ≤ c :=
          le_trans (points_mono Δ (addone i) σ.val (Nat.lt_succ_of_lt σ.property)
            (by show i.val + 1 ≤ σ.val; omega)) hc
        have h2 : Δ.points (incl i) ≤ c := le_trans (Δ.increase i) h1
        have h1d : Δ.points (addone i) ≤ d := le_trans h1 hcd
        have h2d : Δ.points (incl i) ≤ d := le_trans h2 hcd
        rw [rmin_eq_right h1d, rmin_eq_right h2d, rmin_eq_right h1, rmin_eq_right h2,
            sub_self]
      · -- 小区間 i は [c, d] の右側: すべての min が左側で確定
        have h1 : d ≤ Δ.points (incl i) :=
          le_trans hd (points_mono Δ (addone σ) i.val (Nat.lt_succ_of_lt i.property)
            (by show σ.val + 1 ≤ i.val; omega))
        have h2 : d ≤ Δ.points (addone i) := le_trans h1 (Δ.increase i)
        have h1c : c ≤ Δ.points (incl i) := le_trans hcd h1
        have h2c : c ≤ Δ.points (addone i) := le_trans hcd h2
        rw [rmin_eq_left h2, rmin_eq_left h1, rmin_eq_left h2c, rmin_eq_left h1c,
            sub_self d, sub_self c, mul_zero', sub_self]
  calc stepAnti f Δ ξ d - stepAnti f Δ ξ c
      = Summation n (fun i =>
          f (ξ i) * (rmin d (Δ.points (addone i)) - rmin d (Δ.points (incl i))) -
          f (ξ i) * (rmin c (Δ.points (addone i)) - rmin c (Δ.points (incl i)))) :=
        sub_summation n _ _
    _ = Summation n (fun i => if i.val = σ.val then f (ξ σ) * (d - c) else 0) :=
        summation_congr n _ _ hterm
    _ = (if σ.val = σ.val then f (ξ σ) * (d - c) else 0) :=
        summation_one_term n σ _ (fun i hne => if_neg hne)
    _ = f (ξ σ) * (d - c) := if_pos rfl

-- ============================================================
-- §4 細分上で親区間の代表点を使った RS は元の RS に等しい
-- ============================================================

theorem rs_refine_eq (f : Real → Real) {u v : Real}
    {n : Nat} (Δ : Partition n u v) (ξ : Range n → Real)
    {N : Nat} (Δ' : Partition N u v) (σ : Range N → Range n)
    (hσ : ∀ j : Range N,
      Δ.points (incl (σ j)) ≤ Δ'.points (incl j) ∧
      Δ'.points (addone j) ≤ Δ.points (addone (σ j))) :
    RiemannSum f Δ' (fun j => ξ (σ j)) = RiemannSum f Δ ξ := by
  -- G(v) = RS、G(u) = 0、各小区間の増分は stepAnti_inc → 望遠鏡和
  have hGb : stepAnti f Δ ξ v = RiemannSum f Δ ξ := by
    apply summation_congr
    intro i
    rw [rmin_eq_right (point_le_right Δ (addone i)),
        rmin_eq_right (point_le_right Δ (incl i))]
    rfl
  have hGa : stepAnti f Δ ξ u = 0 := by
    have hz : ∀ i : Range n, f (ξ i) *
        (rmin u (Δ.points (addone i)) - rmin u (Δ.points (incl i))) = 0 := by
      intro i
      rw [rmin_eq_left (left_le_point Δ (addone i)),
          rmin_eq_left (left_le_point Δ (incl i)), sub_self, mul_zero']
    calc stepAnti f Δ ξ u
        = Summation n (fun _ => (0 : Real)) := summation_congr n _ _ hz
      _ = 0 := summation_all_zero n
  have hjterm : ∀ j : Range N,
      f (ξ (σ j)) * Δ'.length j =
      stepAnti f Δ ξ (Δ'.points (addone j)) -
      stepAnti f Δ ξ (Δ'.points (incl j)) := fun j =>
    (stepAnti_inc f Δ ξ (σ j) (Δ'.points (incl j)) (Δ'.points (addone j))
      (hσ j).1 (Δ'.increase j) (hσ j).2).symm
  calc RiemannSum f Δ' (fun j => ξ (σ j))
      = Summation N (fun j => stepAnti f Δ ξ (Δ'.points (addone j)) -
          stepAnti f Δ ξ (Δ'.points (incl j))) :=
        summation_congr N _ _ hjterm
    _ = stepAnti f Δ ξ (Δ'.points ⟨N, Nat.lt_succ_self N⟩) -
        stepAnti f Δ ξ (Δ'.points ⟨0, Nat.succ_pos N⟩) :=
        summation_telescope N (fun r => stepAnti f Δ ξ (Δ'.points r))
    _ = stepAnti f Δ ξ v - stepAnti f Δ ξ u := by rw [Δ'.right, Δ'.left]
    _ = RiemannSum f Δ ξ - 0 := by rw [hGb, hGa]
    _ = RiemannSum f Δ ξ := sub_zero _

-- ============================================================
-- §5 Δ の全分点が Δp の分点に含まれるなら、Δp の各小区間は
--    Δ のある小区間に含まれる（σ 写像の存在。has_min の応用）
-- ============================================================

theorem refine_parent {u v : Real} (n N : Nat) (hn : 0 < n)
    (Δ : Partition n u v) (Δp : Partition N u v)
    (hpts : ∀ i : Range (n + 1), ∃ p : Range (N + 1), Δp.points p = Δ.points i) :
    ∀ j : Range N, ∃ k : Range n,
      Δ.points (incl k) ≤ Δp.points (incl j) ∧
      Δp.points (addone j) ≤ Δ.points (addone k) := by
  intro j
  -- 「Δp の小区間 j の右端を覆う最小の Δ 区間」を探索する
  let p : Nat → Prop := fun i =>
    ∃ h : i < n, Δp.points (addone j) ≤ Δ.points ⟨i + 1, Nat.succ_lt_succ h⟩
  have hp : ∃ i, p i := by
    have hn' : n - 1 < n := by omega
    refine ⟨n - 1, hn', ?_⟩
    have heq : (⟨n - 1 + 1, Nat.succ_lt_succ hn'⟩ : Range (n + 1))
        = ⟨n, Nat.lt_succ_self n⟩ :=
      Subtype.ext (Nat.succ_pred_eq_of_pos hn)
    rw [heq, Δ.right]
    exact point_le_right Δp (addone j)
  rcases has_min p hp with ⟨k, ⟨hkn, hkle⟩, hmin⟩
  refine ⟨⟨k, hkn⟩, ?_, hkle⟩
  show Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ ≤ Δp.points (incl j)
  cases Classical.em (k = 0) with
  | inl hk0 =>
    subst hk0
    rw [Δ.left]
    exact left_le_point Δp (incl j)
  | inr hk_ne =>
    have hk_pos : 0 < k := Nat.zero_lt_of_ne_zero hk_ne
    have hkm1_lt : k - 1 < n := by omega
    have not_pk : ¬ p (k - 1) := fun hpk => hmin (k - 1) hpk (Nat.pred_lt hk_ne)
    -- 最小性から p_k < Δp の右端
    have hlt : Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ < Δp.points (addone j) := by
      have h1 : ¬ (Δp.points (addone j) ≤
          Δ.points ⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩) :=
        fun hle => not_pk ⟨hkm1_lt, hle⟩
      have heq : (⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩ : Range (n + 1)) =
          ⟨k, Nat.lt_succ_of_lt hkn⟩ := Subtype.ext (Nat.succ_pred_eq_of_pos hk_pos)
      rw [heq] at h1
      exact not_le_imp_lt h1
    -- p_k は Δp の分点 r。r が j の右端より先なら矛盾、手前なら単調性
    obtain ⟨r, hr⟩ := hpts ⟨k, Nat.lt_succ_of_lt hkn⟩
    cases Nat.lt_or_ge j.val r.val with
    | inl hjr =>
      exfalso
      have h2 : Δp.points (addone j) ≤ Δp.points r :=
        points_mono Δp (addone j) r.val r.property (by show j.val + 1 ≤ r.val; omega)
      rw [hr] at h2
      exact (le_lt_trans h2 hlt).2 rfl
    | inr hrj =>
      rw [← hr]
      exact points_mono Δp r j.val (Nat.lt_succ_of_lt j.property) hrj

-- ============================================================
-- §6 エンベロープ: 固定した Δ に対し、十分細かい任意の P' の RS は
--    RS(Δ) の (B + θ)-近傍に入る（挿入誤差 θ ＋ 細分比較 B の合成）
-- ============================================================

theorem rs_refine_compare (g : Real → Real) {u v : Real} (M : Real)
    (hMlo : ∀ t, u ≤ t → t ≤ v → -M ≤ g t)
    (hMhi : ∀ t, u ≤ t → t ≤ v → g t ≤ M)
    (hM_pos : 0 < M) (hab : u < v)
    {n : Nat} (Δ : Partition n u v) (ξ : Range n → Real)
    (B θ : Real) (hθ : 0 < θ)
    (hcore : ∀ (N : Nat) (Δp : Partition N u v) (ξp : Range N → Real),
      Δp.IsRepr ξp → ∀ σ : Range N → Range n,
      (∀ j, Δ.points (incl (σ j)) ≤ Δp.points (incl j) ∧
            Δp.points (addone j) ≤ Δ.points (addone (σ j))) →
      NearLe B (RiemannSum g Δ ξ) (RiemannSum g Δp ξp)) :
    ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition u v, P'.Fine δ' →
      NearLe (B + θ) (RiemannSum g Δ ξ) (P'.sum g) := by
  -- 挿入誤差の上限 K = (n+1)·(M+M) で θ を割って δ' とする
  have hofn_pos : (0 : Real) < Real.ofNat (n + 1) := cast_pos_succ n
  have h2M_pos : (0 : Real) < M + M := by
    have h1 : (0 : Real) + M < M + M := add_lt_add_right 0 M M hM_pos
    rw [zero_add'] at h1
    exact lt_trans 0 M (M + M) hM_pos h1
  have hK_pos : (0 : Real) < Real.ofNat (n + 1) * (M + M) :=
    pos_mul_pos _ _ hofn_pos h2M_pos
  have hK_ne : Real.ofNat (n + 1) * (M + M) ≠ 0 := ne_of_gt hK_pos
  refine ⟨θ / (Real.ofNat (n + 1) * (M + M)), pos_div_pos _ _ hθ hK_pos, ?_⟩
  intro ⟨n', Δ', ξ', hr'⟩ hd'
  have hn' : 0 < n' := Δ'.pos_of_lt hab
  -- Δ の全分点 (n+1 個) を Δ' に挿入して共通細分 Δp を作る
  obtain ⟨Δp, ξp, hrp, _, hptsp, hbdp⟩ :=
    rs_multi_insert_bound g M hMlo hMhi (le_of_lt hM_pos) hn' Δ' ξ' hr' hd'
      (n + 1) (fun j => Δ.points j)
      (fun j => ⟨left_le_point Δ j, point_le_right Δ j⟩)
  -- σ 写像（refine_parent の選択）で細分比較 hcore を適用
  have hσex := refine_parent n (n' + (n + 1)) (Δ.pos_of_lt hab) Δ Δp hptsp
  have hRCL := hcore (n' + (n + 1)) Δp ξp hrp
    (fun j => Classical.choose (hσex j)) (fun j => Classical.choose_spec (hσex j))
  -- 挿入誤差 ≤ θ（K·(θ/K) = θ）
  have hKθ : Real.ofNat (n + 1) * ((M + M) * (θ / (Real.ofNat (n + 1) * (M + M)))) = θ := by
    rw [(mul_assoc (Real.ofNat (n + 1)) (M + M)
          (θ / (Real.ofNat (n + 1) * (M + M)))).symm,
        mul_comm (Real.ofNat (n + 1) * (M + M)) (θ / (Real.ofNat (n + 1) * (M + M)))]
    exact div_mul_cancel θ _ hK_ne
  have hins : NearLe θ (RiemannSum g Δ' ξ') (RiemannSum g Δp ξp) := by
    apply nearle_mono hbdp
    rw [hKθ]
    exact le_refl θ
  -- 合成: RS(Δ) —B— RS(Δp) —θ— RS(Δ')
  exact nearle_trans hRCL (nearle_symm hins)

-- ============================================================
-- §7 一様連続性（仮定）の下での 2 分割比較（コーシー条件の素材）
-- ============================================================

theorem rs_compare (f : Real → Real) {u v : Real} (M : Real)
    (hMlo : ∀ t, u ≤ t → t ≤ v → -M ≤ f t)
    (hMhi : ∀ t, u ≤ t → t ≤ v → f t ≤ M)
    (hM_pos : 0 < M) (hab : u < v)
    (ε' θ : Real) (hθ : 0 < θ) (δuc : Real)
    (huc : ∀ s t, u ≤ s → s ≤ v → u ≤ t → t ≤ v →
      Near δuc s t → Near ε' (f s) (f t))
    (P : TaggedPartition u v) (hd : P.Fine δuc) :
    ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition u v, P'.Fine δ' →
      NearLe (ε' * (v - u) + θ) (P.sum f) (P'.sum f) := by
  obtain ⟨n, Δ, ξ, hr⟩ := P
  apply rs_refine_compare f M hMlo hMhi hM_pos hab Δ ξ (ε' * (v - u)) θ hθ
  -- hcore: 細分 Δp 上の比較。代表点を親のものに取り替え（rs_refine_eq）、
  -- 同一分割・別タグの差を一様連続性で評価（same_partition_bound）
  intro N Δp ξp hrp σ hσ
  rw [← rs_refine_eq f Δ ξ Δp σ hσ]
  apply same_partition_bound
  intro j
  have hsmem := tag_mem' Δ ξ hr (σ j)
  have htmem := tag_mem' Δp ξp hrp j
  have hb1 := hrp j
  have hb2 := hr (σ j)
  -- 両タグは親区間 [p_{σj}, p_{σj+1}] に属し、その幅は δuc 未満
  have hnear : Near δuc (ξ (σ j)) (ξp j) :=
    near_of_mem hb2.1 hb2.2 (le_trans (hσ j).1 hb1.1) (le_trans hb1.2 (hσ j).2)
      (hd (σ j))
  have hN := huc (ξ (σ j)) (ξp j) hsmem.1 hsmem.2 htmem.1 htmem.2 hnear
  constructor
  · -- -ε' ≤ f (ξp j) − f (ξ (σ j))
    have h2 : f (ξ (σ j)) - f (ξp j) < ε' := sub_lt_swap hN.1
    have h3 := neg_lt_neg h2
    rw [neg_sub] at h3
    exact le_of_lt h3
  · exact le_of_lt (sub_lt_of_lt_add hN.2)

#print axioms rs_refine_eq
#print axioms rs_compare
