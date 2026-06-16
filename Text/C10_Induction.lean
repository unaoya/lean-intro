-- Text/C10_Induction.lean — Ch10 帰納法・加群・Σ コーパス・リーマン和の性質（到達点③）
-- induction で Σ の基本性質コーパス＋Partition の大域単調性を獲得する。等式（Ch6/7）・
-- 自動化（Ch8）・順序と ≤/< 混在 calc（Ch9）は獲得済みで、ここで帰納法に組み込む。
-- 注意: この章まで古典論理ゼロ（not_lt_imp_le 等の古典補題は第 II 部）
import Text.C09_Order

open Range

-- ============================================================
-- Σ 補題コーパス（帰納法の訓練場。添字の付け替え fun k => f ⟨k.val, …⟩ が主役）
--   合同 summation_congr と全零 summation_all_zero は Ch4 で予告済み（再帰＝帰納の
--   最初の一手）。ここからは `induction` タクティクで本格コーパスを積む。
-- ============================================================

theorem additive_summation (n : Nat) (f g : Range n → Real) :
    Summation n (fun i => f i + g i) = Summation n f + Summation n g := by
  induction n with
  | zero => exact (zero_add' 0).symm
  | succ n ih =>
    show Summation n (fun k => f (incl k) + g (incl k))
        + (f ⟨n, Nat.lt_succ_self n⟩ + g ⟨n, Nat.lt_succ_self n⟩)
      = (Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩)
        + (Summation n (fun k => g (incl k)) + g ⟨n, Nat.lt_succ_self n⟩)
    rw [ih (fun k => f (incl k)) (fun k => g (incl k))]
    exact add_four_comm _ _ _ _

theorem summation_mul_left : ∀ (n : Nat) (f : Range n → Real) (c : Real),
    Summation n (fun i => c * f i) = c * Summation n f := by
  intro n
  induction n with
  | zero => intro f c; exact (mul_zero' c).symm
  | succ m ih =>
    intro f c
    show Summation m (fun k => c * f (Range.incl k)) + c * f ⟨m, Nat.lt_succ_self m⟩
        = c * (Summation m (fun k => f (Range.incl k)) + f ⟨m, Nat.lt_succ_self m⟩)
    rw [ih (fun k => f (Range.incl k)) c, CommRing.left_distrib]

theorem neg_summation (n : Nat) (f : Range n → Real) :
    -Summation n f = Summation n (fun i => -f i) := by
  induction n with
  | zero => exact neg_zero
  | succ m ih =>
    show -(Summation m (fun k => f (incl k)) + f ⟨m, Nat.lt_succ_self m⟩)
        = Summation m (fun k => -(f (incl k))) + -(f ⟨m, Nat.lt_succ_self m⟩)
    rw [neg_add_distrib, ih (fun k => f (incl k))]

/-- Σ レベルの差: `Σ F - Σ G = Σ (F - G)`（加法＋符号の系）。 -/
theorem sub_summation (n : Nat) (F G : Range n → Real) :
    Summation n F - Summation n G = Summation n (fun i => F i - G i) := by
  show Summation n F + -Summation n G = Summation n (fun i => F i - G i)
  rw [neg_summation n G]
  exact (additive_summation n F (fun i => -G i)).symm

-- 数列空間 Range n → Real の点ごと半順序（線形でない＝le_total 無し）。これで
-- Σ・重みつき Σ の単調性を f ≤ g の中置で述べる（線形性の f + g と並行）。
instance {n : Nat} : LE (Range n → Real) := ⟨fun f g => ∀ i, f i ≤ g i⟩

theorem summation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
    0 ≤ Summation n f := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    show (0 : Real) ≤ Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩
    exact add_nonneg' (ih (fun k => f (incl k)) (fun i => h (incl i)))
      (h ⟨n, Nat.lt_succ_self n⟩)

theorem summation_le : ∀ (n : Nat) (f g : Range n → Real),
    f ≤ g → Summation n f ≤ Summation n g := by
  intro n
  induction n with
  | zero => intro f g _; exact le_refl 0
  | succ m ih =>
    intro f g h
    exact add_le_add' (ih _ _ (fun k => h (Range.incl k))) (h ⟨m, Nat.lt_succ_self m⟩)

-- ボス戦: 望遠鏡和（最初の本格的帰納法証明）
theorem summation_telescope : ∀ (n : Nat) (g : Range (n + 1) → Real),
    Summation n (fun i => g (Range.addone i) - g (Range.incl i))
      = g ⟨n, Nat.lt_succ_self n⟩ - g ⟨0, Nat.succ_pos n⟩ := by
  intro n
  induction n with
  | zero => intro g; exact (sub_self _).symm
  | succ m ih =>
    intro g
    show Summation m (fun k =>
          g (Range.addone (Range.incl k)) - g (Range.incl (Range.incl k)))
        + (g (Range.addone ⟨m, Nat.lt_succ_self m⟩)
            - g (Range.incl ⟨m, Nat.lt_succ_self m⟩)) = _
    have h := ih (fun j => g (Range.incl j))
    rw [show (fun k : Range m =>
          g (Range.addone (Range.incl k)) - g (Range.incl (Range.incl k)))
        = (fun k : Range m =>
          g (Range.incl (Range.addone k)) - g (Range.incl (Range.incl k))) from rfl]
    rw [h]
    exact (telescope_2 (g ⟨0, Nat.succ_pos (m + 1)⟩)
      (g ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
      (g ⟨m, Nat.lt_succ_of_lt (Nat.lt_succ_self m)⟩)).symm

/-- Σ_{i<n} i の閉じた式（**純粋に Nat の恒等式**）: `(1+1)·Σ i + n = n·n`
（⟺ `Σ_{i<n} i = n(n−1)/2`）。Summation は和があれば定義でき Nat でも使える——
これは Real ではなく Nat の式。減算を避けた形にして cast がきれいに通るようにしてある。 -/
theorem sum_id_nat (n : Nat) :
    (1 + 1) * Summation n (fun i => i.val) + n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsucc : Summation (n + 1) (fun i => i.val) = Summation n (fun i => i.val) + n := rfl
    rw [hsucc, show (n + 1) * (n + 1) = n * n + (1 + 1) * n + 1 from by
      rw [Nat.succ_mul, Nat.mul_succ]; omega]
    omega

-- ============================================================
-- Σ は線形写像（加群 Module は Ch4 で定義済み——ここで Σ がその射であることを証明する）
--    additive_summation と summation_mul_left の 2 本が「Range n → Real 上の線形形式」という
--    1 つの主張に束ねられる（概念の定義が既証明を束ねる・class 設計の応用）。
-- ============================================================

-- ANCHOR: summation_linear
-- Σ は線形形式（証明は corpus の 2 本がそのまま——「線形」という 1 概念に束ねられる）
theorem summation_isLinear (n : Nat) :
    IsLinearMap (fun f : Range n → Real => Summation n f) :=
  ⟨fun f g => additive_summation n f g,
   fun c f => summation_mul_left n f c⟩
-- ANCHOR_END: summation_linear

-- ============================================================
-- 線形性を積み上げる: Σ → 重みつき Σ → （引き戻し）→ リーマン和（Ch13 で帰着）
--    各層が「線形写像」で、合成・特殊化として次の層が出てくる。
-- ============================================================

-- 関数空間 Real → Real も上の funModule で自動的に加群（f + g・-f・c • f が中置で書ける）。
-- precompose（引き戻し）の定義域になり、RS の線形性帰着（Ch13）に使う。

-- ANCHOR: weighted_summation
-- 線形写像の合成は線形（U → V → W）——「線形性は合成で保たれる」道具
theorem isLinear_comp {U V W : Type} [Module U] [Module V] [Module W]
    {T : V → W} {S : U → V} (hT : IsLinearMap T) (hS : IsLinearMap S) :
    IsLinearMap (fun u => T (S u)) :=
  ⟨fun u v => by show T (S (u + v)) = T (S u) + T (S v); rw [hS.1, hT.1],
   fun c u => by show T (S (c • u)) = c • T (S u); rw [hS.2, hT.2]⟩

-- 重みつき有限和（重み w・被加数 g）: Σ に対角重み w を入れた線形形式。
-- リーマン和はこの特殊化（重み = 小区間の長さ・被加数 = タグでの値）。
noncomputable def WeightedSum {n : Nat} (w g : Range n → Real) : Real :=
  Summation n (fun i => g i * w i)

/-- 重みつき Σ は被加数について加法的（分配 → additive_summation）。 -/
theorem weightedSum_add {n : Nat} (w g h : Range n → Real) :
    WeightedSum w (g + h) = WeightedSum w g + WeightedSum w h := by
  show Summation n (fun i => (g i + h i) * w i)
      = Summation n (fun i => g i * w i) + Summation n (fun i => h i * w i)
  rw [summation_congr n _ _ (fun i => CommRing.right_distrib (g i) (h i) (w i)),
      additive_summation]

/-- 重みつき Σ はスカラー倍と可換（結合 → summation_mul_left）。 -/
theorem weightedSum_smul {n : Nat} (w : Range n → Real) (c : Real) (g : Range n → Real) :
    WeightedSum w (c • g) = c * WeightedSum w g := by
  show Summation n (fun i => (c * g i) * w i) = c * Summation n (fun i => g i * w i)
  rw [summation_congr n _ _ (fun i => mul_assoc c (g i) (w i)), summation_mul_left]

/-- **重みつき Σ は線形形式**（重み w を固定して被加数 g について）。Σ の線形性の重み版。 -/
theorem weightedSum_isLinear {n : Nat} (w : Range n → Real) :
    IsLinearMap (fun g : Range n → Real => WeightedSum w g) :=
  ⟨weightedSum_add w, weightedSum_smul w⟩

/-- **タグでの引き戻し `f ↦ (i ↦ f (ξ i))` は線形写像**（関数空間 → 数列空間）。
RS の線形性はこれと重みつき Σ の線形性の合成。 -/
theorem precompose_isLinear {n : Nat} (ξ : Range n → Real) :
    IsLinearMap (fun f : Real → Real => ((fun i => f (ξ i)) : Range n → Real)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **重みつき Σ は被加数について単調**（重みが非負なら）。線形性に対する順序版——
各成分で `nonneg_mul_nonneg`（Real の乗法順序）→ `summation_le`。RS の単調性の土台。 -/
theorem weightedSum_le {n : Nat} (w g h : Range n → Real)
    (hw : ∀ i, 0 ≤ w i) (hgh : g ≤ h) : WeightedSum w g ≤ WeightedSum w h := by
  apply summation_le
  intro i
  exact nonneg_mul_nonneg (g i) (h i) (w i) (hw i) (hgh i)
-- ANCHOR_END: weighted_summation

-- ============================================================
-- Partition の基本性質（induction を読者自身の構造に適用する実地）
--    隣接単調（公理 increase）→ 大域単調（points_mono・induction）→ 端点評価・
--    タグの所属。すべて Ch13 の性質証明が消費する。
-- ============================================================

/-- 各小区間の長さは非負（分点が広義単調だから）。 -/
theorem length_nonneg {n : Nat} {u v : Real} (Δ : Partition n u v) (i : Range n) :
    0 ≤ Δ.length i :=
  (nonneg_iff_le _ _).mp (Δ.increase i)

/-- 長さの総和は区間幅: `Σ length = v - u`。望遠鏡和（`summation_telescope`）で潰れる。 -/
theorem length_sum {n : Nat} {u v : Real} (Δ : Partition n u v) :
    Summation n (fun i => Δ.length i) = v - u := by
  show Summation n (fun i => Δ.points (Range.addone i) - Δ.points (Range.incl i)) = v - u
  rw [summation_telescope n Δ.points, Δ.right, Δ.left]

/-- 分点列の単調性: 添字 `k.val ≤ lv` なら `points k ≤ points ⟨lv,_⟩`。隣接単調（公理
`increase`）から **induction** で大域単調を導く（well-founded 再帰は不要）。 -/
theorem points_mono {n : Nat} {u v : Real} (Δ : Partition n u v) (k : Range (n + 1)) :
    ∀ (lv : Nat) (hl : lv < n + 1), k.val ≤ lv → Δ.points k ≤ Δ.points ⟨lv, hl⟩ := by
  intro lv
  induction lv with
  | zero =>
    intro hl hk
    have hke : k = ⟨0, hl⟩ := Subtype.ext (Nat.le_zero.mp hk)
    rw [hke]; exact le_refl _
  | succ m ih =>
    intro hl hk
    rcases Nat.lt_or_ge k.val (m + 1) with hlt | hge
    · have hm : m < n + 1 := Nat.lt_of_succ_lt hl
      have hmn : m < n := Nat.lt_of_succ_lt_succ hl
      exact le_trans (ih hm (Nat.le_of_lt_succ hlt)) (Δ.increase ⟨m, hmn⟩)
    · have hke : k = ⟨m + 1, hl⟩ := Subtype.ext (Nat.le_antisymm hk hge)
      rw [hke]; exact le_refl _

/-- すべての分点は左端 `u` 以上（単調性＋`Δ.left`）。 -/
theorem left_le_point {n : Nat} {u v : Real} (Δ : Partition n u v)
    (i : Range (n + 1)) : u ≤ Δ.points i := by
  have h := points_mono Δ ⟨0, Nat.succ_pos n⟩ i.val i.property (Nat.zero_le _)
  rw [Δ.left] at h
  exact h

/-- すべての分点は右端 `v` 以下（単調性＋`Δ.right`）。 -/
theorem point_le_right {n : Nat} {u v : Real} (Δ : Partition n u v)
    (i : Range (n + 1)) : Δ.points i ≤ v := by
  have h := points_mono Δ i n (Nat.lt_succ_self n) (Nat.le_of_lt_succ i.property)
  rw [Δ.right] at h
  exact h

/-- 代表点系のタグは区間 `[u, v]` 内にある（IsRepr＝小区間内・端点評価から区間全体へ。
raw 版。`TaggedPartition` に束ねた版は Ch15）。 -/
theorem tag_mem' {n : Nat} {u v : Real} (Δ : Partition n u v) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) (i : Range n) : u ≤ ξ i ∧ ξ i ≤ v := by
  have h1 : Δ.points ⟨0, Nat.succ_pos n⟩ ≤ Δ.points (Range.incl i) :=
    points_mono Δ ⟨0, Nat.succ_pos n⟩ i.val (Nat.lt_succ_of_lt i.property) (Nat.zero_le _)
  have h2 : Δ.points (Range.addone i) ≤ Δ.points ⟨n, Nat.lt_succ_self n⟩ :=
    points_mono Δ (Range.addone i) n (Nat.lt_succ_self n) i.property
  constructor
  · calc u = Δ.points ⟨0, Nat.succ_pos n⟩ := Δ.left.symm
      _ ≤ Δ.points (Range.incl i) := h1
      _ ≤ ξ i := (hr i).1
  · calc ξ i ≤ Δ.points (Range.addone i) := (hr i).2
      _ ≤ Δ.points ⟨n, Nat.lt_succ_self n⟩ := h2
      _ = v := Δ.right

-- ============================================================
-- リーマン和の性質（旧 Ch13・到達点③）: 線形性・単調性・const・nonneg・両側評価
--   いずれも Σ コーパス（線形性=合成／単調性=weightedSum_le）の RS への持ち上げ。
-- ============================================================
-- 関数空間 Real → Real のベクトル空間（f + g・-f・c • f が中置）は Ch10 で導入済。
-- ここでは差 f - g を中置で書けるよう Sub だけ足す（Real と同じ流儀 a - b = a + -b）。
noncomputable instance : Sub (Real → Real) := ⟨fun f g => f + -g⟩

/-- **RS は f について線形写像**。Ch10 の線形性の塔を合成して帰着する:
`RiemannSum f Δ ξ = WeightedSum Δ.length (i ↦ f (ξ i))`（定義的に等しい＝重みつき和）なので、
**重みつき Σ の線形性 `weightedSum_isLinear` と引き戻し `precompose_isLinear` の合成**で出る。
線形性が Σ → 重みつき Σ →（引き戻し）→ RS と積み上がる——以下の加法・符号・差はその系。 -/
theorem riemann_sum_isLinear {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) :
    IsLinearMap (fun f : Real → Real => RiemannSum f Δ ξ) :=
  -- RS f Δ ξ = WeightedSum Δ.length (i ↦ f (ξ i)) は defeq。型注釈で合成の T・S を固定する
  (isLinear_comp (weightedSum_isLinear Δ.length) (precompose_isLinear ξ) :
    IsLinearMap fun f : Real → Real => WeightedSum Δ.length ((fun i => f (ξ i)) : Range n → Real))

/-- 線形性（加法）: `RS(f + g) = RS f + RS g`。線形写像の加法保存（`isLinear` の射影 .1）。 -/
theorem riemann_sum_add (f g : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (f + g) Δ ξ = RiemannSum f Δ ξ + RiemannSum g Δ ξ :=
  (riemann_sum_isLinear Δ ξ).1 f g

/-- 線形性（スカラー倍）: `RS(c • f) = c · RS f`。線形写像のスカラー保存（`isLinear` の射影 .2）。 -/
theorem riemann_sum_smul (c : Real) (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (c • f) Δ ξ = c * RiemannSum f Δ ξ :=
  (riemann_sum_isLinear Δ ξ).2 c f

/-- 系（符号）: `RS(-f) = -RS f`。スカラー倍の `c = -1` の場合。`-f` は点ごとの符号反転。 -/
theorem riemann_sum_neg (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (-f) Δ ξ = -(RiemannSum f Δ ξ) := by
  have h := riemann_sum_smul (-1) f Δ ξ
  rw [show ((-1 : Real) • f) = -f from funext fun x => by
        show (-1 : Real) * f x = -(f x); rw [neg_mul, one_mul_b],
      show (-1 : Real) * RiemannSum f Δ ξ = -(RiemannSum f Δ ξ) from by
        rw [neg_mul, one_mul_b]] at h
  exact h

/-- 系（差）: `RS(f - g) = RS f - RS g`。加法と符号から。`f - g` は点ごとの差（= f + -g）。 -/
theorem riemann_sum_sub (f g : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (f - g) Δ ξ = RiemannSum f Δ ξ - RiemannSum g Δ ξ := by
  have h := riemann_sum_add f (-g) Δ ξ
  rw [riemann_sum_neg g Δ ξ] at h
  exact h

-- ============================================================
-- §2 性質 3: const（望遠鏡和の快感。length_sum は C07）
-- ============================================================

/-- 性質 3（定数）: 定数関数のリーマン和は `c·(v-u)`。`length_sum`（C07）を消費する。 -/
theorem riemann_sum_const {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) (c : Real) :
    RiemannSum (fun _ => c) Δ ξ = c * (v - u) := by
  show Summation n (fun i => c * Δ.length i) = c * (v - u)
  rw [summation_mul_left n (fun i => Δ.length i) c, length_sum Δ]

-- ============================================================
-- §2.5 単調性: 区間上 f ≤ g なら RS f ≤ RS g（IsRepr 必須）。nonneg・両側評価はこの系。
--    Ch10 の重みつき Σ の単調性 weightedSum_le に帰着（重み=length≥0・タグ∈区間）。
--    線形性が「合成で帰着」だったのと並行に、単調性も Σ→重みつきΣ→RS と積み上がる。
-- ============================================================

/-- **RS の単調性**: 区間上 `f ≤ g`（タグが区間内＝`IsRepr`）なら `RS f ≤ RS g`。
重みつき Σ の単調性 `weightedSum_le`（重み = length ≥ 0）への帰着。
**`IsRepr` が必須**——タグが区間外なら各項の符号が保証されず崩れる。
以下の非負性・両側評価はすべてこの特殊化。 -/
theorem riemann_sum_le {n : Nat} {u v : Real} (Δ : Partition n u v) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) {f g : Real → Real}
    (hfg : ∀ t, u ≤ t → t ≤ v → f t ≤ g t) :
    RiemannSum f Δ ξ ≤ RiemannSum g Δ ξ := by
  apply weightedSum_le Δ.length (fun i => f (ξ i)) (fun i => g (ξ i)) (length_nonneg Δ)
  intro i
  obtain ⟨hu, hv⟩ := tag_mem' Δ ξ hr i
  exact hfg (ξ i) hu hv

-- ============================================================
-- §3 性質 4: nonneg（単調性の系——下を定数 0 で抑える）
-- ============================================================

/-- 性質 4（非負性）: 区間上 `0 ≤ f` なら `0 ≤ RS f`。**単調性 `riemann_sum_le` の系**
（`f' = const 0` との比較・`RS(const 0) = 0`）。IsRepr が効く最初の場面。 -/
theorem riemann_sum_nonneg (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) (hr : Δ.IsRepr ξ)
    (hf : ∀ t, u ≤ t → t ≤ v → 0 ≤ f t) : 0 ≤ RiemannSum f Δ ξ := by
  have h := riemann_sum_le Δ ξ hr (f := fun _ => 0) (g := f) hf
  rwa [riemann_sum_const Δ ξ 0, show (0 : Real) * (v - u) = 0 from by my_ring] at h

-- ============================================================
-- §4 性質 5: 両側評価（abs を使わない。生の不等式 2 本——述語 NearLe への昇格は発展部）
-- ============================================================

/-- 性質 5（上側）: 区間上 `f ≤ c` なら `RS f ≤ c·(v-u)`。**単調性の系**（上を定数 `c` で抑える・
`RS(const c) = c·(v-u)`）。abs を使わない両側評価の片割れ（後段の sup 構成が消費する形）。 -/
theorem rs_le_const {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) (hr : Δ.IsRepr ξ) {f : Real → Real} {c : Real}
    (hb : ∀ t, u ≤ t → t ≤ v → f t ≤ c) :
    RiemannSum f Δ ξ ≤ c * (v - u) := by
  have h := riemann_sum_le Δ ξ hr (f := f) (g := fun _ => c) hb
  rwa [riemann_sum_const Δ ξ c] at h

/-- 性質 5（下側）: 区間上 `c ≤ f` なら `c·(v-u) ≤ RS f`。上側 `rs_le_const` と対（下を定数で抑える）。 -/
theorem const_le_rs {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) (hr : Δ.IsRepr ξ) {f : Real → Real} {c : Real}
    (hb : ∀ t, u ≤ t → t ≤ v → c ≤ f t) :
    c * (v - u) ≤ RiemannSum f Δ ξ := by
  have h := riemann_sum_le Δ ξ hr (f := fun _ => c) (g := f) hb
  rwa [riemann_sum_const Δ ξ c] at h

-- 章末監査: 第 I 部の総決算（Classical.choice はどこにも現れない）
#print axioms riemann_sum_const
#print axioms riemann_sum_nonneg
#print axioms rs_le_const

-- 代表点系であること（旧 C05 の証明部・順序 le_refl を要するのでここ＝Ch9 に置く）。
namespace Partition

/-- 左端タグは代表点系（左端は自分の小区間の左端そのもの・右端は increase で）。 -/
theorem leftRepr_isRepr {n : Nat} {a b : Real} (Δ : Partition n a b) :
    Δ.IsRepr Δ.leftRepr :=
  fun i => ⟨OrderedAddCommMonoid.le_refl _, Δ.increase i⟩

/-- 右端タグは代表点系。 -/
theorem rightRepr_isRepr {n : Nat} {a b : Real} (Δ : Partition n a b) :
    Δ.IsRepr Δ.rightRepr :=
  fun i => ⟨Δ.increase i, OrderedAddCommMonoid.le_refl _⟩

end Partition
