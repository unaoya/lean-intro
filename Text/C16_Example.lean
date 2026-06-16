-- Text/C16_Example.lean — Ch16 直接証明 ∫x = (b²−a²)/2
-- f = id は定義から直接可積分性を示せる稀有な例。中点和が望遠鏡和になり、
-- 任意のタグとの差は各小区間 ±len/2 → 合計 ±(δ/2)(b−a)。
-- 監査: sup なし（「定義から直接」は完備性不要——どこで sup が要るのかの対照実験）
import Text.C15_Unique

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 代数の小物（my_ring の活躍どころ——Ch8 の道具で短縮する演習）
-- ============================================================

-- 和と差の積（平方の差）
theorem add_mul_sub (x y : Real) : (x + y) * (x - y) = x * x - y * y := by
  calc (x + y) * (x - y)
      = x * (x - y) + y * (x - y) := CommRing.right_distrib x y (x - y)
    _ = (x * x - x * y) + (y * x - y * y) := by rw [mul_sub x x y, mul_sub y x y]
    _ = (x * x - x * y) + (x * y - y * y) := by rw [mul_comm y x]
    _ = x * x - y * y := by
        show (x * x + -(x * y)) + (x * y + -(y * y)) = x * x + -(y * y)
        rw [add_assoc, (add_assoc (-(x * y)) (x * y) (-(y * y))).symm,
            neg_add', zero_add']

theorem div_mul_eq (a b c : Real) : (a / c) * b = a * b / c := by
  show a * Field.inv c * b = a * b * Field.inv c
  rw [mul_assoc a (Field.inv c) b, mul_comm (Field.inv c) b,
      (mul_assoc a b (Field.inv c)).symm]

theorem neg_div (a c : Real) : (-a) / c = -(a / c) := neg_mul a (Field.inv c)

-- (a/c/d)·c = a/d（c で約分）
theorem div_div_mul_cancel (a c d : Real) (hc : c ≠ 0) : a / c / d * c = a / d := by
  show a * Field.inv c * Field.inv d * c = a * Field.inv d
  rw [mul_assoc (a * Field.inv c) (Field.inv d) c, mul_comm (Field.inv d) c,
      (mul_assoc (a * Field.inv c) c (Field.inv d)).symm,
      mul_assoc a (Field.inv c) c, Field.inv_mul c hc]
  exact congrArg (· * Field.inv d) (mul_one_b a)

-- 端点と中点の距離は半区間（rw のパターン捕獲を避けるため独立補題にする——Ch7 の罠②）
theorem half_dist_hi (p q : Real) : q - (p + q) / (1 + 1) = (q - p) / (1 + 1) := by
  rw [show q - (p + q) / (1 + 1) = (q + q) / (1 + 1) - (p + q) / (1 + 1) from by
        rw [double_half],
      div_sub_div]
  congr 1
  rw [add_sub_add, sub_self, add_zero]

theorem half_dist_lo (p q : Real) : p - (p + q) / (1 + 1) = -((q - p) / (1 + 1)) := by
  rw [show p - (p + q) / (1 + 1) = (p + p) / (1 + 1) - (p + q) / (1 + 1) from by
        rw [double_half],
      div_sub_div, (neg_div _ _).symm]
  congr 1
  rw [add_sub_add, sub_self, zero_add', (neg_sub q p).symm]

-- ============================================================
-- §2 退化区間の RS は 0（[u,u] では全分点が u に潰れる）
-- ============================================================

theorem degenerate_sum {u : Real} (P : TaggedPartition u u) (f : Real → Real) :
    P.sum f = 0 := by
  have hz : ∀ i : Range P.n, f (P.ξ i) * P.Δ.length i = 0 := by
    intro i
    have hlen : P.Δ.length i = 0 := by
      show P.Δ.points (addone i) - P.Δ.points (incl i) = 0
      rw [le_antisymm _ _ (point_le_right P.Δ (addone i)) (left_le_point P.Δ (addone i)),
          le_antisymm _ _ (point_le_right P.Δ (incl i)) (left_le_point P.Δ (incl i))]
      exact sub_self u
    rw [hlen, mul_zero']
  show Summation P.n (fun i => f (P.ξ i) * P.Δ.length i) = 0
  rw [summation_congr P.n _ _ hz]
  exact summation_all_zero P.n

-- ============================================================
-- §3 isintegral_id: 中点和の望遠鏡和による直接証明
--    中点タグなら RS は厳密に (b²−a²)/2。任意のタグとの差は
--    各小区間で ±len/2、合計 ±(δ/2)(b−a) に収まる。
--    （仕上げは両側のまま——NearLe 述語への昇格は発展部）
-- ============================================================

-- ANCHOR: isintegral_id
theorem isintegral_id (a b : Real) (hab : a ≤ b) :
    IsIntegral (fun x => x) a b ((b * b - a * a) / (1 + 1)) := by
  cases Classical.em (a = b) with
  | inl he =>
    subst he
    intro ε hε
    refine ⟨1, zero_lt_one, fun P _ => ?_⟩
    have h0 : (a * a - a * a) / (1 + 1) = 0 := by
      rw [sub_self]
      exact zero_div _
    rw [h0, degenerate_sum P _]
    exact near_self hε
  | inr hne =>
    have hab' : a < b := lt_of_le_of_ne hab hne
    have hba_pos : 0 < b - a := sub_pos_of_lt hab'
    have hba_ne : b - a ≠ 0 := ne_of_gt hba_pos
    intro ε hε
    refine ⟨ε / (b - a), pos_div_pos _ _ hε hba_pos, fun P hP => ?_⟩
    -- 中点和は望遠鏡和: Σ midᵢ·lenᵢ = (b²−a²)/2
    have hmid_term : ∀ i : Range P.n,
        (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1) * P.Δ.length i
        = P.Δ.points (addone i) * P.Δ.points (addone i) / (1 + 1)
          - P.Δ.points (incl i) * P.Δ.points (incl i) / (1 + 1) := by
      intro i
      show (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1)
            * (P.Δ.points (addone i) - P.Δ.points (incl i)) = _
      rw [add_comm (P.Δ.points (incl i)) (P.Δ.points (addone i)),
          div_mul_eq, add_mul_sub, (div_sub_div _ _ _).symm]
    have hmid_sum : Summation P.n (fun i =>
        (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1) * P.Δ.length i)
        = (b * b - a * a) / (1 + 1) := by
      rw [summation_congr P.n _ _ hmid_term,
          summation_telescope P.n (fun r => P.Δ.points r * P.Δ.points r / (1 + 1)),
          P.Δ.right, P.Δ.left]
      exact div_sub_div _ _ _
    -- RS − 中点和 = Σ (ξᵢ − midᵢ)·lenᵢ
    have hdiff : P.sum (fun x => x) - Summation P.n (fun i =>
        (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1) * P.Δ.length i)
        = Summation P.n (fun i =>
            (P.ξ i - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
            * P.Δ.length i) := by
      show Summation P.n (fun i => P.ξ i * P.Δ.length i) - _ = _
      rw [sub_summation]
      exact summation_congr P.n _ _ (fun i => mul_sub_mul _ _ _)
    -- 各タグは中点から ±lenᵢ/2 の範囲（代表点の両側評価）
    have hhalf_hi : ∀ i : Range P.n,
        P.Δ.points (addone i)
          - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1)
        = P.Δ.length i / (1 + 1) :=
      fun i => half_dist_hi (P.Δ.points (incl i)) (P.Δ.points (addone i))
    have hhalf_lo : ∀ i : Range P.n,
        P.Δ.points (incl i)
          - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1)
        = -(P.Δ.length i / (1 + 1)) :=
      fun i => half_dist_lo (P.Δ.points (incl i)) (P.Δ.points (addone i))
    -- 各項の両側評価: ±(δ/2)·lenᵢ（δ = ε/(b−a)）
    have hterm_hi : ∀ i : Range P.n,
        (P.ξ i - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
          * P.Δ.length i
        ≤ (ε / (b - a) / (1 + 1)) * P.Δ.length i := by
      intro i
      apply nonneg_mul_nonneg _ _ _ (length_nonneg P.Δ i)
      have h1 := sub_le_sub_right (P.repr i).2
        ((P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
      rw [hhalf_hi i] at h1
      exact le_trans h1 (div_right_le _ _ _ zero_lt_one_one (le_of_lt (hP i)))
    have hterm_lo : ∀ i : Range P.n,
        (-(ε / (b - a) / (1 + 1))) * P.Δ.length i
        ≤ (P.ξ i - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
          * P.Δ.length i := by
      intro i
      apply nonneg_mul_nonneg _ _ _ (length_nonneg P.Δ i)
      have h1 := sub_le_sub_right (P.repr i).1
        ((P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
      rw [hhalf_lo i] at h1
      have h2 : -(ε / (b - a) / (1 + 1)) ≤ -(P.Δ.length i / (1 + 1)) :=
        neg_le_neg' (div_right_le _ _ _ zero_lt_one_one (le_of_lt (hP i)))
      exact le_trans h2 h1
    -- 和の両側評価: ±(δ/2)·(b−a) = ±ε/2
    have hC : ε / (b - a) / (1 + 1) * (b - a) = ε / (1 + 1) :=
      div_div_mul_cancel ε (b - a) (1 + 1) hba_ne
    have hsum_hi : Summation P.n (fun i =>
        (P.ξ i - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
        * P.Δ.length i) ≤ ε / (1 + 1) := by
      have h1 := summation_le P.n _ _ hterm_hi
      rw [summation_mul_left P.n (fun i => P.Δ.length i) (ε / (b - a) / (1 + 1)),
          length_sum P.Δ, hC] at h1
      exact h1
    have hsum_lo : -(ε / (1 + 1)) ≤ Summation P.n (fun i =>
        (P.ξ i - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
        * P.Δ.length i) := by
      have h1 := summation_le P.n _ _ hterm_lo
      rw [summation_mul_left P.n (fun i => P.Δ.length i) (-(ε / (b - a) / (1 + 1))),
          length_sum P.Δ, neg_mul, hC] at h1
      exact h1
    -- 仕上げ: RS = 中点和 + D、D ∈ ±ε/2 → 両側のまま Near ε へ
    have hsum_eq : P.sum (fun x => x)
        = Summation P.n (fun i =>
            (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1) * P.Δ.length i)
          + Summation P.n (fun i =>
            (P.ξ i - (P.Δ.points (incl i) + P.Δ.points (addone i)) / (1 + 1))
            * P.Δ.length i) := by
      rw [← hdiff]
      exact (add_sub_cancel' _ _).symm
    rw [← hmid_sum, hsum_eq]
    exact ⟨lt_le_trans _ _ _ (sub_lt_sub_left (half_lt hε) _) (add_left_le _ _ _ hsum_lo),
           le_lt_trans (add_left_le _ _ _ hsum_hi) (add_left_lt _ _ _ (half_lt hε))⟩
-- ANCHOR_END: isintegral_id

-- ============================================================
-- §4 橋の 2 回目: Integral 関数の値として（Ch12 の (n+1)/(2n) と接続して具体例が閉じる）
-- ============================================================

theorem integral_id (a b : Real) (hab : a ≤ b) :
    Integral (fun x => x) a b = (b * b - a * a) / (1 + 1) :=
  integral_eq_of_isIntegral _ a b _ hab (isintegral_id a b hab)

-- 監査: isintegral_id に sup は現れない（完備性不要）。integral_id で初めて sup が付く
#print axioms isintegral_id
#print axioms integral_id
