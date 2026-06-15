-- Text/C12_Example.lean — Ch12 具体例 y = x の n 等分（到達点②）
-- n 等分割 equalPartition と、[0,1] 上の y=x のリーマン和（(1+1)n²·RS = n²−n）。
-- Ch11 の cast（射）と自作タクティク my_ring/my_abel（Ch8）で貫通する。
import Text.C10_Numbers

noncomputable section

open Range

-- ============================================================
-- §4 n 等分: points i = a + i * (b−a) / m
-- ============================================================

-- ANCHOR: equal_partition
noncomputable def equalPartition (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    Partition m a b where
  points := fun i => a + ((i.val : Nat) : Real) * (b - a) / (m : Real)
  increase := by
    intro i
    apply add_left_le
    apply div_right_le _ _ _ (cast_pos_of_ne m hm)
    exact nonneg_mul_nonneg _ _ _ ((nonneg_iff_le a b).mp hab) (cast_le_succ i.val)
  left := by
    show a + ((0 : Nat) : Real) * (b - a) / (m : Real) = a
    show a + (0 : Real) * (b - a) / (m : Real) = a
    rw [zero_mul', zero_div, add_zero]
  right := by
    show a + ((m : Nat) : Real) * (b - a) / (m : Real) = b
    have hm' : ((m : Nat) : Real) ≠ (0 : Real) := ne_of_gt (cast_pos_of_ne m hm)
    rw [mul_div_cancel' (m : Real) (b - a) hm']
    exact add_sub_cancel' a b
-- ANCHOR_END: equal_partition

theorem equalPartition_length (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b)
    (i : Range m) :
    (equalPartition m a b hm hab).length i = (b - a) / (m : Real) := by
  show (a + (((i.val + 1 : Nat)) : Real) * (b - a) / (m : Real)) -
       (a + ((i.val : Nat) : Real) * (b - a) / (m : Real)) = (b - a) / (m : Real)
  rw [add_sub_add' a, div_sub_div, mul_sub_mul]
  show ((((i.val + 1 : Nat)) : Real) - ((i.val : Nat) : Real)) * (b - a) / (m : Real)
      = (b - a) / (m : Real)
  rw [show (((i.val + 1 : Nat)) : Real) = ((i.val : Nat) : Real) + 1 from succ_ofNat i.val]
  rw [add_sub_cancel ((i.val : Nat) : Real) 1, one_mul]

/-- 代表点 = 各小区間の左端（一般の `Partition.leftRepr` を等分割に適用したもの）。 -/
noncomputable def equalPartitionRepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    Range m → Real :=
  (equalPartition m a b hm hab).leftRepr

/-- 等分割の左端タグは代表点系——一般の `Partition.leftRepr_isRepr` の特例（等分割固有の
計算は不要）。 -/
theorem equalPartitionRepr_isrepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    (equalPartition m a b hm hab).IsRepr (equalPartitionRepr m a b hm hab) :=
  (equalPartition m a b hm hab).leftRepr_isRepr

-- ============================================================
-- §5 到達点②: y = x のリーマン和（[0,1] の n 等分・左端タグ）
--    Σ_{i<n} i の Nat 恒等式 sum_id_nat を cast（射）で Real に運び、
--    各小区間の寄与を my_ring で畳んで閉じる。
-- ============================================================

/-- `sum_id_nat`（Nat）を cast（準同型）で Real に運ぶ: `(1+1)·Σ i + n = n·n`。
Σ と可換（`cast_summation`）・積と和を保つ（`cast_mul`/`cast_add`）ことの帰結。 -/
theorem sum_id_real (n : Nat) :
    (1 + 1) * Summation n (fun i => ((i.val : Nat) : Real)) + (n : Real)
      = (n : Real) * (n : Real) := by
  have hcast := congrArg (fun k : Nat => (k : Real)) (sum_id_nat n)
  simp only [] at hcast
  rw [← cast_add, cast_mul, cast_mul, cast_summation,
      show ((1 + 1 : Nat) : Real) = (1 : Real) + 1 from by rw [← cast_add, cast_one]] at hcast
  exact hcast

-- ANCHOR: rs_id
/-- **到達点②**: [0,1] の n 等分・左端タグでの y=x のリーマン和。分母を払った形
`(1+1)·n²·RS = n² − n`（⟺ RS = (n−1)/(2n)。割り算で割った形は将来の field タクティクで）。
証明: 各小区間の寄与 `ξ_i · length_i = (1/n²)·i` を my_ring で畳み、Σ を `sum_id_real`
で閉じ、`n²·(1/n²)=1` を Field.mul_inv で相殺する。「n→∞ で 1/2 に見える——だが極限は
まだ定義していない」（第 II 部への遠い引き）。 -/
theorem riemann_sum_id (n : Nat) (hn : n ≠ 0) :
    (1 + 1) * ((n : Real) * n)
      * RiemannSum (fun x => x) (equalPartition n 0 1 hn (le_of_lt zero_lt_one))
          (equalPartition n 0 1 hn (le_of_lt zero_lt_one)).leftRepr
      = (n : Real) * n - n := by
  have hnR : (n : Real) ≠ 0 := ne_of_gt (cast_pos_of_ne n hn)
  -- 各小区間の寄与: ξ_i · length_i = (1/n)²·i
  have hterm : ∀ i : Range n,
      (equalPartition n 0 1 hn (le_of_lt zero_lt_one)).leftRepr i
        * (equalPartition n 0 1 hn (le_of_lt zero_lt_one)).length i
      = (Field.inv (n : Real) * Field.inv (n : Real)) * ((i.val : Nat) : Real) := by
    intro i
    rw [equalPartition_length n 0 1 hn (le_of_lt zero_lt_one) i]
    show (0 + ((i.val : Nat) : Real) * ((1 : Real) - 0) / (n : Real)) * (((1 : Real) - 0) / (n : Real))
       = (Field.inv (n : Real) * Field.inv (n : Real)) * ((i.val : Nat) : Real)
    my_ring
  -- RS = (1/n)² · Σ i
  have hRS : RiemannSum (fun x => x) (equalPartition n 0 1 hn (le_of_lt zero_lt_one))
        (equalPartition n 0 1 hn (le_of_lt zero_lt_one)).leftRepr
      = (Field.inv (n : Real) * Field.inv (n : Real))
          * Summation n (fun i => ((i.val : Nat) : Real)) := by
    show Summation n (fun i => (equalPartition n 0 1 hn (le_of_lt zero_lt_one)).leftRepr i
            * (equalPartition n 0 1 hn (le_of_lt zero_lt_one)).length i)
        = (Field.inv (n : Real) * Field.inv (n : Real))
            * Summation n (fun i => ((i.val : Nat) : Real))
    rw [summation_congr n _ (fun i => (Field.inv (n : Real) * Field.inv (n : Real))
          * ((i.val : Nat) : Real)) hterm,
        summation_mul_left n (fun i => ((i.val : Nat) : Real))
          (Field.inv (n : Real) * Field.inv (n : Real))]
  -- n² · (1/n)² = 1: my_ring で (n·inv n)·(n·inv n) に並べ替え、mul_inv で相殺し my_ring で締める
  have hnn : (n : Real) * n * (Field.inv (n : Real) * Field.inv (n : Real)) = 1 := by
    rw [show (n : Real) * n * (Field.inv (n : Real) * Field.inv (n : Real))
          = ((n : Real) * Field.inv (n : Real)) * ((n : Real) * Field.inv (n : Real)) from by my_ring,
        Field.mul_inv (n : Real) hnR]
    my_ring
  rw [hRS,
      show (1 + 1) * ((n : Real) * n)
            * (Field.inv (n : Real) * Field.inv (n : Real) * Summation n (fun i => ((i.val : Nat) : Real)))
          = (1 + 1) * ((n : Real) * n * (Field.inv (n : Real) * Field.inv (n : Real)))
              * Summation n (fun i => ((i.val : Nat) : Real)) from by my_ring,
      hnn, mul_one_b,
      show (n : Real) * n - n = (1 + 1) * Summation n (fun i => ((i.val : Nat) : Real)) from by
        rw [← sum_id_real n]; my_abel]
-- ANCHOR_END: rs_id

-- 章末監査: 古典論理ゼロ（[Real, Real.instLOF] のみ・cast の射性も構成的）
#print axioms riemann_sum_id
#print axioms equalPartition
