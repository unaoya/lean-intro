-- Text/C09_Properties.lean — Ch9 リーマン和の性質 5 本（到達点③）
-- additive / neg / const / nonneg / 両側評価。nonneg の反例から IsRepr が必然として登場。
-- abs は使わない（理由は Ch11 の素朴定義実験で明かす）。章末監査: 第 I 部は古典公理ゼロ
--
-- 各宣言の `/-- … -/` は docstring（hover・#check・#print・生成ドキュメントに表示される
-- 説明）。`--` の行コメントと違い、直後の宣言に「紐づく」。
import Text.C08_Numbers

noncomputable section

open Range

-- ============================================================
-- §1 タグの所属: IsRepr（「タグが区間内になければ非負にならない」反例が要求）
-- ============================================================

namespace Partition

-- ANCHOR: is_repr
/-- 代表点系 `IsRepr`: タグ `ξ i` が各小区間 `[points (incl i), points (addone i)]` に
属すること。性質 4（非負性）の反例から「タグが区間内にある」ことが必然として要求される。 -/
def IsRepr {n : Nat} {a b : Real} (Δ : Partition n a b) (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)
-- ANCHOR_END: is_repr

end Partition

/-- 等分割の左端タグ（`equalPartitionRepr`）は代表点系である。 -/
theorem equalPartitionRepr_isrepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    (equalPartition m a b hm hab).IsRepr (equalPartitionRepr m a b hm hab) :=
  fun i => ⟨le_refl _, (equalPartition m a b hm hab).increase i⟩

-- ============================================================
-- §2 分割の幾何（長さの非負性・分点の単調性・端点評価・タグの所属）
-- ============================================================

/-- 各小区間の長さは非負（分点が広義単調だから）。 -/
theorem length_nonneg {n : Nat} {u v : Real} (Δ : Partition n u v) (i : Range n) :
    0 ≤ Δ.length i :=
  (nonneg_iff_le _ _).mp (Δ.increase i)

/-- 分点列の単調性: 添字 `k.val ≤ lv` なら `points k ≤ points ⟨lv,_⟩`。
素朴な Nat 帰納法で証明できる（well-founded 再帰は不要）。 -/
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

/-- 代表点系のタグは区間 `[u, v]` 内にある（raw 版。`TaggedPartition` に束ねた版は Ch12）。 -/
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
-- §3 性質 1–2: 線形性（Σ の線形性の持ち上げ）
-- ============================================================

/-- 性質 1（加法）: `RS(f+g) = RS f + RS g`。Σ の線形性（`additive_summation`）の持ち上げ。 -/
theorem riemann_sum_add (f g : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => f x + g x) Δ ξ = RiemannSum f Δ ξ + RiemannSum g Δ ξ := by
  show Summation n (fun i => (f (ξ i) + g (ξ i)) * Δ.length i)
      = Summation n (fun i => f (ξ i) * Δ.length i)
        + Summation n (fun i => g (ξ i) * Δ.length i)
  rw [summation_congr n _ _
        (fun i => CommRing.right_distrib (f (ξ i)) (g (ξ i)) (Δ.length i)),
      additive_summation]

/-- 性質 2（符号）: `RS(-f) = -(RS f)`。 -/
theorem riemann_sum_neg (f : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => -(f x)) Δ ξ = -(RiemannSum f Δ ξ) := by
  show Summation n (fun i => -(f (ξ i)) * Δ.length i)
      = -(Summation n (fun i => f (ξ i) * Δ.length i))
  rw [summation_congr n _ _ (fun i => neg_mul (f (ξ i)) (Δ.length i)),
      ← neg_summation]

/-- 系（差）: `RS(f-g) = RS f - RS g`。加法と符号から。 -/
theorem riemann_sum_sub (f g : Real → Real) {n : Nat} {u v : Real}
    (Δ : Partition n u v) (ξ : Range n → Real) :
    RiemannSum (fun x => f x - g x) Δ ξ = RiemannSum f Δ ξ - RiemannSum g Δ ξ := by
  have h := riemann_sum_add f (fun x => -(g x)) Δ ξ
  rw [riemann_sum_neg g Δ ξ] at h
  exact h

/-- Σ レベルの差: `Σ F - Σ G = Σ (F - G)`（加法＋符号の系）。 -/
theorem sub_summation (n : Nat) (F G : Range n → Real) :
    Summation n F - Summation n G = Summation n (fun i => F i - G i) := by
  show Summation n F + -Summation n G = Summation n (fun i => F i - G i)
  rw [neg_summation n G]
  exact (additive_summation n F (fun i => -G i)).symm

-- ============================================================
-- §4 性質 3: const（望遠鏡和の快感）
-- ============================================================

/-- 長さの総和は区間幅: `Σ length = v - u`。望遠鏡和（`summation_telescope`）で潰れる。 -/
theorem length_sum {n : Nat} {u v : Real} (Δ : Partition n u v) :
    Summation n (fun i => Δ.length i) = v - u := by
  show Summation n (fun i => Δ.points (Range.addone i) - Δ.points (Range.incl i)) = v - u
  rw [summation_telescope n Δ.points, Δ.right, Δ.left]

/-- 性質 3（定数）: 定数関数のリーマン和は `c·(v-u)`。`length_sum` を消費する。 -/
theorem riemann_sum_const {n : Nat} {u v : Real} (Δ : Partition n u v)
    (ξ : Range n → Real) (c : Real) :
    RiemannSum (fun _ => c) Δ ξ = c * (v - u) := by
  show Summation n (fun i => c * Δ.length i) = c * (v - u)
  rw [summation_mul_left n (fun i => Δ.length i) c, length_sum Δ]

-- ============================================================
-- §5 性質 4: nonneg（IsRepr が初めて仕事をする）
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
-- §6 性質 5: 両側評価（abs を使わない。生の不等式 2 本——述語 NearLe への昇格は発展部）
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
