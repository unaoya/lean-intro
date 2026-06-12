-- Text/Proto/EqualPartition.lean — M2: n 等分の構成と「任意の細かさの分割の存在」
import Text.Proto.Cast
import Text.Proto.Partition

noncomputable section

open Range

theorem cast_addone_val {n : Nat} (k : Range n) :
    (((addone k).val : Nat) : Real) = ((k.val : Nat) : Real) + 1 := by
  show Real.ofNat (k.val + 1) = Real.ofNat k.val + 1
  exact succ_ofNat k.val

-- n 等分: points i = a + i * (b−a) / m
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

-- 代表点 = 各小区間の左端
noncomputable def equalPartitionRepr (m : Nat) (a b : Real) (_hm : m ≠ 0) (_hab : a ≤ b) :
    Range m → Real :=
  fun i => a + ((i.val : Nat) : Real) * (b - a) / (m : Real)

theorem equalPartitionRepr_isrepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    (equalPartition m a b hm hab).IsRepr (equalPartitionRepr m a b hm hab) :=
  fun i => ⟨le_refl _, (equalPartition m a b hm hab).increase i⟩

-- 等分割の細かさ（∀ 形——diam を使わない）
theorem equalPartition_fine (m : Nat) (a b δ : Real) (hm : m ≠ 0) (hab : a ≤ b)
    (hδ : 0 < δ) (hlt : (b - a) / δ < (m : Real)) :
    ∀ i : Range m, (equalPartition m a b hm hab).length i < δ := by
  intro i
  rw [equalPartition_length m a b hm hab i]
  have hm_pos : 0 < ((m : Nat) : Real) := cast_pos_of_ne m hm
  have h1 : (b - a) / δ * δ < (m : Real) * δ := mul_right_lt _ _ δ hδ hlt
  rw [div_mul_cancel _ _ (ne_of_gt hδ)] at h1
  have h2 : (b - a) / (m : Real) < ((m : Real) * δ) / (m : Real) :=
    div_right_lt _ _ _ hm_pos h1
  rwa [mul_div_cancel' _ _ (ne_of_gt hm_pos)] at h2

-- 任意の細かさのタグ付き分割の存在（一意性＝ネットの非空性、の値段）
theorem exists_fine_partition (a b δ : Real) (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ P : TaggedPartition a b, P.Fine δ := by
  have hba_nn : 0 ≤ b - a := (nonneg_iff_le a b).mp hab
  have hba_div_nn : 0 ≤ (b - a) / δ := nonneg_div_nonneg (b - a) δ hba_nn hδ
  have hm_lt : (b - a) / δ < ((ceil ((b - a) / δ) : Nat) : Real) := ceil_lt _
  have hm_ne : ceil ((b - a) / δ) ≠ 0 :=
    nat_ne_zero_of_nonneg_lt _ _ hba_div_nn hm_lt
  exact ⟨⟨ceil ((b - a) / δ), equalPartition _ a b hm_ne hab,
    equalPartitionRepr _ a b hm_ne hab,
    equalPartitionRepr_isrepr _ a b hm_ne hab⟩,
    equalPartition_fine _ a b δ hm_ne hab hδ hm_lt⟩
