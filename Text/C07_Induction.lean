-- Text/C07_Induction.lean — Ch7 sorry を埋める道具 II（等しさは2種類・帰納法）
-- defeq と rw の構文性（rfl/show）を掴み、帰納法で Σ 補題コーパス＋Partition の大域
-- 単調性を獲得する。順序・等式のスカラー代数と ≤/< 混在 calc は Ch6（C06）で獲得済み。
-- 注意: この章まで古典論理ゼロ（not_lt_imp_le 等の古典補題は C11）
import Text.C06_Tactics

open Range

-- ============================================================
-- Σ 補題コーパス（帰納法の訓練場。添字の付け替え fun k => f ⟨k.val, …⟩ が主役）
-- ============================================================

theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
    Summation n f = Summation n g := congrArg (Summation n) (funext h)

theorem summation_all_zero (n : Nat) :
    Summation n (fun _ : Range n => (0 : Real)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Summation m (fun _ : Range m => (0 : Real)) + (0 : Real) = 0
    rw [ih, zero_add']

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

theorem summation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
    0 ≤ Summation n f := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    show (0 : Real) ≤ Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩
    have h1 : (0 : Real) ≤ Summation n (fun k => f (incl k)) :=
      ih (fun k => f (incl k)) (fun i => h (incl i))
    calc (0 : Real) = 0 + 0 := (add_zero' 0).symm
      _ ≤ Summation n (fun k => f (incl k)) + 0 := add_le_add_right 0 _ 0 h1
      _ ≤ Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩ :=
          add_left_le _ 0 _ (h ⟨n, Nat.lt_succ_self n⟩)

theorem summation_le : ∀ (n : Nat) (f g : Range n → Real),
    (∀ i, f i ≤ g i) → Summation n f ≤ Summation n g := by
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
-- 脇道: Σ は線形形式である
--    additive_summation と summation_mul_left の 2 本は、数学者の言葉では
--    「有限数列のなすベクトル空間 (Range n → Real) 上の線形形式」という 1 つの主張。
--    ベクトル空間の公理と線形写像を class で自作して、そう言い直してみる
--    （class 設計の応用・関数型へのインスタンス・funext の活躍どころ）
-- ============================================================

-- ANCHOR: vector_space
-- Real 上のベクトル空間（• は core の SMul の記法）
class VectorSpace (V : Type) extends Add V, Neg V, Zero V, SMul Real V where
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  add_comm : ∀ u v : V, u + v = v + u
  add_zero : ∀ v : V, v + 0 = v
  add_neg : ∀ v : V, v + -v = 0
  one_smul : ∀ v : V, (1 : Real) • v = v
  mul_smul : ∀ (a b : Real) (v : V), (a * b) • v = a • (b • v)
  smul_add : ∀ (a : Real) (u v : V), a • (u + v) = a • u + a • v
  add_smul : ∀ (a b : Real) (v : V), (a + b) • v = a • v + b • v

-- 線形写像（線形形式は W = Real の場合）
def IsLinearMap {V W : Type} [VectorSpace V] [VectorSpace W] (T : V → W) : Prop :=
  (∀ u v : V, T (u + v) = T u + T v) ∧
  (∀ (c : Real) (v : V), T (c • v) = c • T v)
-- ANCHOR_END: vector_space

-- Real 自身は Real 上のベクトル空間（• は単なる積）
noncomputable instance : VectorSpace Real where
  smul := fun c x => c * x
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero'
  add_neg := add_neg'
  one_smul := one_mul_b
  mul_smul := mul_assoc
  smul_add := CommRing.left_distrib
  add_smul := CommRing.right_distrib

-- 有限数列の空間 Range n → Real（演算はすべて各点で——funext の出番）
noncomputable instance (n : Nat) : VectorSpace (Range n → Real) where
  add := fun f g => fun i => f i + g i
  neg := fun f => fun i => -(f i)
  zero := fun _ => 0
  smul := fun c f => fun i => c * f i
  add_assoc := fun f g h => funext fun i => add_assoc (f i) (g i) (h i)
  add_comm := fun f g => funext fun i => add_comm (f i) (g i)
  add_zero := fun f => funext fun i => add_zero' (f i)
  add_neg := fun f => funext fun i => add_neg' (f i)
  one_smul := fun f => funext fun i => one_mul_b (f i)
  mul_smul := fun a b f => funext fun i => mul_assoc a b (f i)
  smul_add := fun a f g => funext fun i => CommRing.left_distrib a (f i) (g i)
  add_smul := fun a b f => funext fun i => CommRing.right_distrib a b (f i)

-- ANCHOR: summation_linear
-- Σ は線形形式（証明は corpus の 2 本がそのまま——「線形」という 1 概念に束ねられる）
theorem summation_isLinear (n : Nat) :
    IsLinearMap (fun f : Range n → Real => Summation n f) :=
  ⟨fun f g => additive_summation n f g,
   fun c f => summation_mul_left n f c⟩
-- ANCHOR_END: summation_linear

-- ============================================================
-- Partition の基本性質（induction を読者自身の構造に適用する実地）
--    隣接単調（公理 increase）→ 大域単調（points_mono・induction）→ 端点評価・
--    タグの所属。すべて Ch9 の性質証明が消費する。
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
raw 版。`TaggedPartition` に束ねた版は Ch12）。 -/
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
