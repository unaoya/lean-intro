-- Text/Proto/Criterion.lean — M5(ii): コーシー型可積分判定（sup 構成・脱 abs 版）
import Text.Proto.FTCCore

noncomputable section

open Classical

-- リーマン和の両側評価（M4 の比較を和のレベルで切り出したもの）
theorem sum_le_const {u v : Real} (P : TaggedPartition u v) {g : Real → Real} {c : Real}
    (hb : ∀ t, u ≤ t → t ≤ v → g t ≤ c) : P.sum g ≤ c * (v - u) := by
  rw [← const_sum P c]
  show Summation P.n (fun i => g (P.ξ i) * P.Δ.length i)
      ≤ Summation P.n (fun i => c * P.Δ.length i)
  apply summation_le
  intro i
  obtain ⟨hu, hv⟩ := tag_mem P i
  exact nonneg_mul_nonneg _ _ _ (length_nonneg P.Δ i) (hb _ hu hv)

theorem const_le_sum {u v : Real} (P : TaggedPartition u v) {g : Real → Real} {c : Real}
    (hb : ∀ t, u ≤ t → t ≤ v → c ≤ g t) : c * (v - u) ≤ P.sum g := by
  rw [← const_sum P c]
  show Summation P.n (fun i => c * P.Δ.length i)
      ≤ Summation P.n (fun i => g (P.ξ i) * P.Δ.length i)
  apply summation_le
  intro i
  obtain ⟨hu, hv⟩ := tag_mem P i
  exact nonneg_mul_nonneg _ _ _ (length_nonneg P.Δ i) (hb _ hu hv)

-- 移項の小物
theorem sub_lt_self (z : Real) {h : Real} (hh : 0 < h) : z - h < z := by
  have hneg : -h < (0 : Real) := by
    have := neg_lt_neg hh; rwa [neg_zero] at this
  have := add_left_lt z (-h) 0 hneg
  rwa [add_zero'] at this

theorem le_add_of_sub_le {a b c : Real} (h : a - b ≤ c) : a ≤ c + b := by
  have h1 := add_le_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

-- (z + h) − (h + h) = z − h
theorem add_half_sub_full (z h : Real) : (z + h) - (h + h) = z - h := by
  show z + h + -(h + h) = z + -h
  rw [neg_add_distrib]
  calc z + h + (-h + -h) = z + (h + (-h + -h)) := add_assoc _ _ _
    _ = z + ((h + -h) + -h) := by rw [add_assoc h (-h) (-h)]
    _ = z + (0 + -h) := by rw [add_neg']
    _ = z + -h := by rw [zero_add']

-- ============================================================
-- コーシー型判定: 「十分細かい分割を固定すると、さらに細かい分割の
-- リーマン和がその ε-近傍に入る」なら可積分（値は sup で構成）
-- ============================================================

theorem integrable_of_cauchy (g : Real → Real) (u v : Real) (huv : u ≤ v)
    (lo hi : Real)
    (hlo : ∀ t, u ≤ t → t ≤ v → lo ≤ g t)
    (hhi : ∀ t, u ≤ t → t ≤ v → g t ≤ hi)
    (hcauchy : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ P : TaggedPartition u v, P.Fine δ →
        ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition u v, P'.Fine δ' →
          Near ε (P.sum g) (P'.sum g)) :
    IsIntegrable g u v := by
  -- S = 「最終的にリーマン和の下界になる値」（M1 で定義済みの LowerRS）
  have hS_ne : ∃ y, LowerRS g u v y :=
    ⟨lo * (v - u), 1, zero_lt_one, fun P _ => const_le_sum P hlo⟩
  have hS_bdd : ∃ M, ∀ y, LowerRS g u v y → y ≤ M := by
    refine ⟨hi * (v - u), fun y hy => ?_⟩
    obtain ⟨δy, hδy, Hy⟩ := hy
    obtain ⟨P, hP⟩ := exists_fine_partition u v δy huv hδy
    exact le_trans (Hy P hP) (sum_le_const P hhi)
  refine ⟨Real.sup (LowerRS g u v) hS_ne hS_bdd, ?_⟩
  intro ε hε
  have hh : 0 < ε / (1 + 1) := pos_half ε hε
  obtain ⟨δ, hδ, H⟩ := hcauchy _ hh
  refine ⟨δ, hδ, fun P hP => ?_⟩
  obtain ⟨δ', hδ', H'⟩ := H P hP
  -- (a) P.sum − ε/2 は S の元 → P.sum − ε/2 ≤ i
  have hmem : LowerRS g u v (P.sum g - ε / (1 + 1)) := by
    refine ⟨δ', hδ', fun P' hP' => ?_⟩
    exact le_of_lt (H' P' hP').1
  have hlo_i : P.sum g - ε / (1 + 1) ≤ Real.sup (LowerRS g u v) hS_ne hS_bdd :=
    Real.sup_ub (LowerRS g u v) hS_ne hS_bdd _ hmem
  -- (b) S の任意の元は P.sum + ε/2 以下 → i ≤ P.sum + ε/2
  have hhi_i : Real.sup (LowerRS g u v) hS_ne hS_bdd ≤ P.sum g + ε / (1 + 1) := by
    apply Real.sup_lub (LowerRS g u v) hS_ne hS_bdd
    intro y hy
    obtain ⟨δy, hδy, Hy⟩ := hy
    -- δy と δ' の小さい方で細かい分割を取る
    have hPP : ∃ P'' : TaggedPartition u v, P''.Fine δy ∧ P''.Fine δ' := by
      cases le_total δy δ' with
      | inl hle =>
        obtain ⟨Q, hQ⟩ := exists_fine_partition u v δy huv hδy
        exact ⟨Q, hQ, fine_mono hQ hle⟩
      | inr hle =>
        obtain ⟨Q, hQ⟩ := exists_fine_partition u v δ' huv hδ'
        exact ⟨Q, fine_mono hQ hle, hQ⟩
    obtain ⟨P'', hPy, hP'⟩ := hPP
    have h1 : y ≤ P''.sum g := Hy P'' hPy
    have h2 : P''.sum g < P.sum g + ε / (1 + 1) := (H' P'' hP').2
    exact le_of_lt (le_lt_trans h1 h2)
  -- 仕上げ: Near ε i (P.sum g)
  constructor
  · -- i − ε < P.sum: i − ε ≤ (P.sum + ε/2) − ε = P.sum − ε/2 < P.sum
    have h1 : Real.sup (LowerRS g u v) hS_ne hS_bdd - ε ≤ (P.sum g + ε / (1 + 1)) - ε := sub_le_sub_right hhi_i ε
    have heq : (P.sum g + ε / (1 + 1)) - ε = P.sum g - ε / (1 + 1) :=
      (congrArg (fun z => (P.sum g + ε / (1 + 1)) - z) (half_add ε).symm).trans
        (add_half_sub_full (P.sum g) (ε / (1 + 1)))
    rw [heq] at h1
    exact le_lt_trans h1 (sub_lt_self _ hh)
  · -- P.sum < i + ε: P.sum ≤ i + ε/2 < i + ε
    have h1 : P.sum g ≤ Real.sup (LowerRS g u v) hS_ne hS_bdd + ε / (1 + 1) := le_add_of_sub_le hlo_i
    exact le_lt_trans h1 (add_left_lt _ _ _ (half_lt hε))

#print axioms integrable_of_cauchy
