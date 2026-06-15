-- Text/C13_Properties.lean — Ch13 リーマン和の性質 5 本（到達点③）
-- additive / neg / const / nonneg / 両側評価。abs は使わない（理由は Ch14 の素朴定義実験）。
-- 章末監査: 第 I 部は古典公理ゼロ。
-- IsRepr は C05（定義）・分割の幾何（points_mono 等）と tag_mem' は C07・
-- equalPartitionRepr_isrepr は C08 に配置済（ここでは性質の証明に使うだけ）。
import Text.C12_Example

noncomputable section

open Range

-- ============================================================
-- §1 性質 1: 線形性（f について加法＋スカラー倍。RS は f に関して線形写像）
--    Σ の線形性（C07 の summation_isLinear）の RS への持ち上げ。
--    符号（neg）と差（sub）はここから「出てくる」系。
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
-- §3 性質 4: nonneg（IsRepr が初めて仕事をする）
-- ============================================================

/-- 性質 4（非負性）: 区間上 `0 ≤ f` なら `0 ≤ RS f`。**`IsRepr` が必須**——タグが区間外なら
各項の符号が保証されず、これは成り立たない（IsRepr 導入の動機）。 -/
theorem riemann_sum_nonneg (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) (hr : Δ.IsRepr ξ)
    (hf : ∀ t, u ≤ t → t ≤ v → 0 ≤ f t) : 0 ≤ RiemannSum f Δ ξ :=
  summation_nonneg n _ (fun i =>
    mul_nonneg _ _ (hf _ (tag_mem' Δ ξ hr i).1 (tag_mem' Δ ξ hr i).2)
      (length_nonneg Δ i))

-- ============================================================
-- §4 性質 5: 両側評価（abs を使わない。生の不等式 2 本——述語 NearLe への昇格は発展部）
-- ============================================================

/-- 性質 5（上側）: 区間上 `f ≤ c` なら `RS f ≤ c·(v-u)`。abs を使わない両側評価の片割れ
（後段の sup 構成が消費する形）。 -/
theorem rs_le_const {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) (hr : Δ.IsRepr ξ) {f : Real → Real} {c : Real}
    (hb : ∀ t, u ≤ t → t ≤ v → f t ≤ c) :
    RiemannSum f Δ ξ ≤ c * (v - u) := by
  rw [← riemann_sum_const Δ ξ c]
  show Summation n (fun i => f (ξ i) * Δ.length i)
      ≤ Summation n (fun i => c * Δ.length i)
  apply summation_le
  intro i
  obtain ⟨hu, hv⟩ := tag_mem' Δ ξ hr i
  exact nonneg_mul_nonneg _ _ _ (length_nonneg Δ i) (hb _ hu hv)

/-- 性質 5（下側）: 区間上 `c ≤ f` なら `c·(v-u) ≤ RS f`。上側 `rs_le_const` と対。 -/
theorem const_le_rs {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) (hr : Δ.IsRepr ξ) {f : Real → Real} {c : Real}
    (hb : ∀ t, u ≤ t → t ≤ v → c ≤ f t) :
    c * (v - u) ≤ RiemannSum f Δ ξ := by
  rw [← riemann_sum_const Δ ξ c]
  show Summation n (fun i => c * Δ.length i)
      ≤ Summation n (fun i => f (ξ i) * Δ.length i)
  apply summation_le
  intro i
  obtain ⟨hu, hv⟩ := tag_mem' Δ ξ hr i
  exact nonneg_mul_nonneg _ _ _ (length_nonneg Δ i) (hb _ hu hv)

-- 章末監査: 第 I 部の総決算（Classical.choice はどこにも現れない）
#print axioms riemann_sum_const
#print axioms riemann_sum_nonneg
#print axioms rs_le_const
