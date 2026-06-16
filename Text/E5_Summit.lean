-- Text/E5_Summit.lean — 発展部 §5: 存在定理——連続なら可積分
-- 本編の FTC（可積分仮定版）に可積分性を供給する古典解析のハイライト。
-- 部品: (ii) コーシー型判定（sup 構成）・(iv) 組み立て。(i) 一様連続性は E4、
-- (iii) 細分比較は E1–E3。sum_le_const / const_le_sum は本編 C15_FTC §2 にある
import Text.E4_UnifCont

noncomputable section

open Classical

-- ============================================================
-- §2 部品 (ii): コーシー型判定——「十分細かい分割を固定すると、さらに細かい分割の
--    リーマン和がその ε-近傍に入る」なら可積分（値は sup で構成）
-- ============================================================

-- ANCHOR: integrable_of_cauchy
theorem integrable_of_cauchy (g : Real → Real) (u v : Real) (huv : u ≤ v)
    (lo hi : Real)
    (hlo : ∀ t, u ≤ t → t ≤ v → lo ≤ g t)
    (hhi : ∀ t, u ≤ t → t ≤ v → g t ≤ hi)
    (hcauchy : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ P : TaggedPartition u v, P.Fine δ →
        ∃ δ', 0 < δ' ∧ ∀ P' : TaggedPartition u v, P'.Fine δ' →
          Near ε (P.sum g) (P'.sum g)) :
    IsIntegrable g u v := by
  -- S = 「最終的にリーマン和の下界になる値」（Ch16 で定義済みの LowerRS）
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
    -- δy と δ' の小さい方で細かい分割を取る（min-free 合流）
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
    have h1 : Real.sup (LowerRS g u v) hS_ne hS_bdd - ε
        ≤ (P.sum g + ε / (1 + 1)) - ε := sub_le_sub_right hhi_i ε
    have heq : (P.sum g + ε / (1 + 1)) - ε = P.sum g - ε / (1 + 1) :=
      (congrArg (fun z => (P.sum g + ε / (1 + 1)) - z) (half_add ε).symm).trans
        (add_half_sub_full (P.sum g) (ε / (1 + 1)))
    rw [heq] at h1
    exact le_lt_trans h1 (sub_lt_self _ hh)
  · -- P.sum < i + ε: P.sum ≤ i + ε/2 < i + ε
    have h1 : P.sum g ≤ Real.sup (LowerRS g u v) hS_ne hS_bdd + ε / (1 + 1) :=
      le_add_of_sub_le hlo_i
    exact le_lt_trans h1 (add_left_lt _ _ _ (half_lt hε))
-- ANCHOR_END: integrable_of_cauchy

-- ============================================================
-- §3 部品 (iv): 組み立て——連続 ⇒ 可積分（本文完全精読）
-- ============================================================

-- ANCHOR: continuous_integrable
theorem continuous_integrable (f : Real → Real) {u v : Real} (huv : u ≤ v)
    (hf : ∀ x, u ≤ x → x ≤ v → ContinuousAt f x) : IsIntegrable f u v := by
  cases Classical.em (u = v) with
  | inl he =>
    -- 退化区間 [u, u]: すべての分点が u に潰れ、どの RS も 0（Ch17 の補題）
    subst he
    refine ⟨0, fun ε hε => ⟨1, zero_lt_one, fun P _ => ?_⟩⟩
    rw [degenerate_sum P f]
    exact near_self hε
  | inr hne =>
    have hab : u < v := lt_of_le_of_ne huv hne
    have hvu_pos : 0 < v - u := sub_pos_of_lt hab
    have hvu_ne : v - u ≠ 0 := ne_of_gt hvu_pos
    -- 有界性（付録 A）と判定法（§2）に細分比較（付録 B）を渡す
    obtain ⟨M, hM_pos, hMlo, hMhi⟩ := continuous_bounded f huv hf
    apply integrable_of_cauchy f u v huv (-M) M hMlo hMhi
    intro ε hε
    -- 誤差の配分: ε'·(v−u) = ε/4、θ = ε/4、合計 ε/2 < ε
    have hε2 : 0 < ε / (1 + 1) := pos_half ε hε
    have hε4 : 0 < ε / (1 + 1) / (1 + 1) := pos_half _ hε2
    have hε' : 0 < ε / (1 + 1) / (1 + 1) / (v - u) := pos_div_pos _ _ hε4 hvu_pos
    obtain ⟨δuc, hδuc_pos, huc⟩ := continuous_unif_cont f huv hf
      (ε / (1 + 1) / (1 + 1) / (v - u)) hε'
    refine ⟨δuc, hδuc_pos, fun P hP => ?_⟩
    obtain ⟨δ', hδ'_pos, H⟩ := rs_compare f M hMlo hMhi hM_pos hab
      (ε / (1 + 1) / (1 + 1) / (v - u)) (ε / (1 + 1) / (1 + 1)) hε4 δuc huc P hP
    refine ⟨δ', hδ'_pos, fun P' hP' => ?_⟩
    have hlt : ε / (1 + 1) / (1 + 1) / (v - u) * (v - u) + ε / (1 + 1) / (1 + 1) < ε := by
      rw [div_mul_cancel _ _ hvu_ne, half_add (ε / (1 + 1))]
      exact half_lt hε
    exact nearle_to_near (H P' hP') hlt
-- ANCHOR_END: continuous_integrable

-- 章末監査: sup_ub / sup_lub がフル稼働（連結性論法と sup 構成の値段）
#print axioms integrable_of_cauchy
#print axioms continuous_integrable
