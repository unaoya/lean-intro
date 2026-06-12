-- Text/Proto/Main.lean — M5(iv)+M6: 組み立て
--   連続 ⇒ 可積分（一様連続性 + 細分比較 + コーシー判定）
--   FTC の実体化（核 ftc_core + 一意性の橋 1 回で Integral 関数の定理に）
import Text.Proto.UnifCont

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 連続 ⇒ 可積分
-- ============================================================

theorem continuous_integrable (f : Real → Real) {u v : Real} (huv : u ≤ v)
    (hf : ∀ x, u ≤ x → x ≤ v → ContinuousAt f x) : IsIntegrable f u v := by
  cases Classical.em (u = v) with
  | inl he =>
    -- 退化区間 [u, u]: すべての分点が u に潰れ、どの RS も 0
    subst he
    refine ⟨0, fun ε hε => ⟨1, zero_lt_one, fun P _ => ?_⟩⟩
    have hz : ∀ i : Range P.n, f (P.ξ i) * P.Δ.length i = 0 := by
      intro i
      have hlen : P.Δ.length i = 0 := by
        show P.Δ.points (addone i) - P.Δ.points (incl i) = 0
        rw [le_antisymm _ _ (point_le_right P.Δ (addone i)) (left_le_point P.Δ (addone i)),
            le_antisymm _ _ (point_le_right P.Δ (incl i)) (left_le_point P.Δ (incl i))]
        exact sub_self u
      rw [hlen, mul_zero']
    have hsum : P.sum f = 0 := by
      show Summation P.n (fun i => f (P.ξ i) * P.Δ.length i) = 0
      rw [summation_congr P.n _ _ hz]
      exact summation_all_zero P.n
    rw [hsum]
    exact near_self hε
  | inr hne =>
    have hab : u < v := lt_of_le_of_ne huv hne
    have hvu_pos : 0 < v - u := sub_pos_of_lt hab
    have hvu_ne : v - u ≠ 0 := ne_of_gt hvu_pos
    -- 有界性（M5(i)）と判定法（M5(ii)）に細分比較（M5(iii)）を渡す
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

-- ============================================================
-- §2 FTC の実体化: 核（仮定形・一意性フリー）に橋を 1 回かけて
--    Integral 関数で述べる定理にする
-- ============================================================

theorem ftc (f : Real → Real) (a b x : Real) (hax : a ≤ x) (hxb : x ≤ b)
    (hf : ∀ t, a ≤ t → t ≤ b → ContinuousAt f t) :
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ u v, a ≤ u → u ≤ x → x ≤ v → v ≤ b →
      u < v → v - u < δ →
      Near (ε * (v - u)) (f x * (v - u)) (Integral f u v) := by
  intro ε hε
  -- 核: 連続性@x だけで跨ぎ形の評価（M4）
  obtain ⟨δ, hδ, H⟩ := ftc_core f a b x hax hxb (hf x hax hxb) ε hε
  refine ⟨δ, hδ, fun u v hau hux hxv hvb huv hδv => ?_⟩
  -- 実体化: [u,v] 上の連続性 ⇒ 可積分 ⇒ Integral が IsIntegral の証人（橋 1 回）
  have hint : IsIntegrable f u v :=
    continuous_integrable f (le_of_lt huv)
      (fun t htu htv => hf t (le_trans hau htu) (le_trans htv hvb))
  obtain ⟨J, hJ⟩ := hint
  rw [integral_eq_of_isIntegral f u v J (le_of_lt huv) hJ]
  exact H u v J hau hux hxv hvb huv hδv hJ

#print axioms continuous_integrable
#print axioms ftc
