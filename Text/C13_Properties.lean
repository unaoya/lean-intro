-- Text/C13_Properties.lean — Ch13 リーマン和の性質 5 本（到達点③）
-- additive / neg / const / nonneg / 両側評価。abs は使わない（理由は Ch11 の素朴定義実験）。
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

/-- 線形性（加法）: `RS(f+g) = RS f + RS g`。Σ の `additive_summation` の持ち上げ。 -/
theorem riemann_sum_add (f g : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => f x + g x) Δ ξ = RiemannSum f Δ ξ + RiemannSum g Δ ξ := by
  show Summation n (fun i => (f (ξ i) + g (ξ i)) * Δ.length i)
      = Summation n (fun i => f (ξ i) * Δ.length i)
        + Summation n (fun i => g (ξ i) * Δ.length i)
  rw [summation_congr n _ _
        (fun i => CommRing.right_distrib (f (ξ i)) (g (ξ i)) (Δ.length i)),
      additive_summation]

/-- 線形性（スカラー倍）: `RS(c·f) = c·RS f`。Σ の `summation_mul_left` の持ち上げ。 -/
theorem riemann_sum_smul (c : Real) (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => c * f x) Δ ξ = c * RiemannSum f Δ ξ := by
  show Summation n (fun i => (c * f (ξ i)) * Δ.length i)
      = c * Summation n (fun i => f (ξ i) * Δ.length i)
  rw [summation_congr n _ _ (fun i => mul_assoc c (f (ξ i)) (Δ.length i)),
      summation_mul_left]

-- 関数空間 Real → Real のベクトル空間構造（各点演算）——RS の線形性を IsLinearMap で
-- 述べるため。Ch7 の VectorSpace (Range n → Real) と同型の作り。
noncomputable instance : VectorSpace (Real → Real) where
  add := fun f g => fun x => f x + g x
  neg := fun f => fun x => -(f x)
  zero := fun _ => 0
  smul := fun c f => fun x => c * f x
  add_assoc := fun f g h => funext fun x => add_assoc (f x) (g x) (h x)
  add_comm := fun f g => funext fun x => add_comm (f x) (g x)
  add_zero := fun f => funext fun x => add_zero' (f x)
  add_neg := fun f => funext fun x => add_neg' (f x)
  one_smul := fun f => funext fun x => one_mul_b (f x)
  mul_smul := fun a b f => funext fun x => mul_assoc a b (f x)
  smul_add := fun a f g => funext fun x => CommRing.left_distrib a (f x) (g x)
  add_smul := fun a b f => funext fun x => CommRing.right_distrib a b (f x)

/-- **RS は f について線形写像**（加法＋スカラー倍）。Ch7 の `summation_isLinear` の RS 版。
これが線形性の本体——以下の符号・差はこの 2 本から出てくる系。 -/
theorem riemann_sum_isLinear {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) :
    IsLinearMap (fun f : Real → Real => RiemannSum f Δ ξ) :=
  ⟨fun f g => riemann_sum_add f g Δ ξ, fun c f => riemann_sum_smul c f Δ ξ⟩

/-- 系（符号）: `RS(-f) = -RS f`。スカラー倍の `c = -1` の場合。 -/
theorem riemann_sum_neg (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => -(f x)) Δ ξ = -(RiemannSum f Δ ξ) := by
  have h := riemann_sum_smul (-1) f Δ ξ
  rw [show (fun x => (-1 : Real) * f x) = (fun x => -(f x)) from
        funext (fun x => by rw [neg_mul, one_mul_b]),
      show (-1 : Real) * RiemannSum f Δ ξ = -(RiemannSum f Δ ξ) from by
        rw [neg_mul, one_mul_b]] at h
  exact h

/-- 系（差）: `RS(f-g) = RS f - RS g`。加法と符号から。 -/
theorem riemann_sum_sub (f g : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => f x - g x) Δ ξ = RiemannSum f Δ ξ - RiemannSum g Δ ξ := by
  have h := riemann_sum_add f (fun x => -(g x)) Δ ξ
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
