-- Text/C16_FTC.lean — Ch16 微積分学の基本定理
-- 片側 FTC（全域の F を作らない）: 核 ftc_core（完全に局所的——区間加法性も
-- 線形性も一意性も存在定理も不要）＋実体化（橋 1 回）＋監査総決算
import Text.C15_Summit

noncomputable section

open Classical

-- ============================================================
-- §1 片側 FTC の主張: 跨ぎ形（u ≤ x ≤ v の差分商）
-- ============================================================

-- ANCHOR: straddle
def HasStraddleDeriv (f : Real → Real) (a b x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ u v J, a ≤ u → u ≤ x → x ≤ v → v ≤ b → u < v → v - u < δ →
      IsIntegral f u v J → Near (ε * (v - u)) (f x * (v - u)) J
-- ANCHOR_END: straddle

def HasRightDeriv (f : Real → Real) (b x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ v J, x < v → v ≤ b → v - x < δ →
      IsIntegral f x v J → Near (ε * (v - x)) (f x * (v - x)) J

def HasLeftDeriv (f : Real → Real) (a x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ u J, a ≤ u → u < x → x - u < δ →
      IsIntegral f u x J → Near (ε * (x - u)) (f x * (x - u)) J

-- 跨ぎ形は左右微分を直ちに含む（u = x または v = x と置くだけ）。
-- 逆向きは区間加法性が要る——跨ぎ形の方が強い
theorem right_of_straddle {f : Real → Real} {a b x : Real}
    (hax : a ≤ x) (h : HasStraddleDeriv f a b x) : HasRightDeriv f b x := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  exact ⟨δ, hδ, fun v J hxv hvb hδv hJ =>
    H x v J hax (le_refl x) (le_of_lt hxv) hvb hxv hδv hJ⟩

theorem left_of_straddle {f : Real → Real} {a b x : Real}
    (hxb : x ≤ b) (h : HasStraddleDeriv f a b x) : HasLeftDeriv f a x := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  exact ⟨δ, hδ, fun u J hau hux hδu hJ =>
    H u x J hau (le_of_lt hux) (le_refl x) hxb hux hδu hJ⟩

-- ============================================================
-- §2 核の部品: IsIntegral レベルの両側評価（脱 abs の単調性）
--    定数の積分 const_isintegral は Ch13（橋の応用）で証明済み
-- ============================================================

theorem isintegral_le_of_le {f : Real → Real} {u v J c : Real} (huv : u ≤ v)
    (hJ : IsIntegral f u v J) (hb : ∀ t, u ≤ t → t ≤ v → f t ≤ c) :
    J ≤ c * (v - u) := by
  apply le_of_forall_lt_add
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hJ ε hε
  obtain ⟨P, hP⟩ := exists_fine_partition u v δ huv hδ
  have hnear := H P hP
  have h1 : J < P.sum f + ε := lt_add_of_sub_lt hnear.1
  have h2 : P.sum f ≤ c * (v - u) := sum_le_const P hb
  exact lt_le_trans _ _ _ h1 (add_le_add_right _ _ ε h2)

theorem le_isintegral_of_le {f : Real → Real} {u v J c : Real} (huv : u ≤ v)
    (hJ : IsIntegral f u v J) (hb : ∀ t, u ≤ t → t ≤ v → c ≤ f t) :
    c * (v - u) ≤ J := by
  apply le_of_forall_lt_add
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hJ ε hε
  obtain ⟨P, hP⟩ := exists_fine_partition u v δ huv hδ
  have hnear := H P hP
  have h1 : c * (v - u) ≤ P.sum f := const_le_sum P hb
  exact le_lt_trans h1 hnear.2

-- ============================================================
-- §3 核 ftc_core: 連続なら、跨ぎ形の差分商が f(x) に収束する
--    必要なのは: 連続性@x・定数積分・両側評価。存在定理も加法性も一意性も不要
-- ============================================================

-- 注: hax / hxb は証明に不要（跨ぎの仮定 u ≤ x ≤ v が全てを運ぶ——核は完全に局所的）
-- ANCHOR: ftc_core
theorem ftc_core (f : Real → Real) (a b x : Real) (_hax : a ≤ x) (_hxb : x ≤ b)
    (hcont : ContinuousAt f x) : HasStraddleDeriv f a b x := by
  intro ε hε
  have hh : 0 < ε / (1 + 1) := pos_half ε hε
  obtain ⟨δ, hδ, hC⟩ := hcont _ hh
  refine ⟨δ, hδ, fun u v J hau hux hxv hvb huv hδv hJ => ?_⟩
  have hvu : 0 < v - u := sub_pos_of_lt huv
  -- [u,v] の点はすべて x の δ-近傍にある（v − u < δ なので）
  have hmem : ∀ t, u ≤ t → t ≤ v → Near δ x t := by
    intro t hut htv
    constructor
    · -- x − δ < t（x − t ≤ x − u ≤ v − u < δ）
      have h1 : x - t ≤ v - u :=
        le_trans (sub_le_sub_left hut x) (sub_le_sub_right hxv u)
      exact sub_lt_swap (le_lt_trans h1 hδv)
    · -- t < x + δ（t − x ≤ v − x ≤ v − u < δ）
      have h1 : t - x ≤ v - u :=
        le_trans (sub_le_sub_right htv x) (sub_le_sub_left hux v)
      have h2 := lt_add_of_sub_lt (le_lt_trans h1 hδv)
      rwa [add_comm] at h2
  -- 両側評価を積分に通す
  have hJup : J ≤ (f x + ε / (1 + 1)) * (v - u) :=
    isintegral_le_of_le (le_of_lt huv) hJ
      (fun t hut htv => le_of_lt (hC t (hmem t hut htv)).2)
  have hJlo : (f x - ε / (1 + 1)) * (v - u) ≤ J :=
    le_isintegral_of_le (le_of_lt huv) hJ
      (fun t hut htv => le_of_lt (hC t (hmem t hut htv)).1)
  -- ε/2 から ε への strict 化
  have hmul : ε / (1 + 1) * (v - u) < ε * (v - u) :=
    mul_right_lt _ _ (v - u) hvu (half_lt hε)
  constructor
  · -- f x·(v−u) − ε·(v−u) < (f x − ε/2)·(v−u) ≤ J
    have step1 : f x * (v - u) - ε * (v - u)
        < f x * (v - u) - ε / (1 + 1) * (v - u) :=
      sub_lt_sub_left hmul (f x * (v - u))
    have step2 : f x * (v - u) - ε / (1 + 1) * (v - u)
        = (f x - ε / (1 + 1)) * (v - u) :=
      mul_sub_mul (f x) (v - u) (ε / (1 + 1))
    exact lt_le_trans _ _ _ (step2 ▸ step1) hJlo
  · -- J ≤ f x·(v−u) + ε/2·(v−u) < f x·(v−u) + ε·(v−u)
    have step2 : (f x + ε / (1 + 1)) * (v - u)
        = f x * (v - u) + ε / (1 + 1) * (v - u) :=
      CommRing.right_distrib (f x) (ε / (1 + 1)) (v - u)
    have step3 : f x * (v - u) + ε / (1 + 1) * (v - u)
        < f x * (v - u) + ε * (v - u) :=
      add_left_lt _ _ _ hmul
    exact le_lt_trans (step2 ▸ hJup) step3
-- ANCHOR_END: ftc_core

-- ============================================================
-- §4 実体化: 核に橋を 1 回かけて Integral 関数の定理にする
-- ============================================================

-- ANCHOR: ftc
theorem ftc (f : Real → Real) (a b x : Real) (hax : a ≤ x) (hxb : x ≤ b)
    (hf : ∀ t, a ≤ t → t ≤ b → ContinuousAt f t) :
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ u v, a ≤ u → u ≤ x → x ≤ v → v ≤ b →
      u < v → v - u < δ →
      Near (ε * (v - u)) (f x * (v - u)) (Integral f u v) := by
  intro ε hε
  -- 核: 連続性@x だけで跨ぎ形の評価
  obtain ⟨δ, hδ, H⟩ := ftc_core f a b x hax hxb (hf x hax hxb) ε hε
  refine ⟨δ, hδ, fun u v hau hux hxv hvb huv hδv => ?_⟩
  -- 実体化: [u,v] 上の連続性 ⇒ 可積分 ⇒ Integral が IsIntegral の証人（橋 1 回）
  have hint : IsIntegrable f u v :=
    continuous_integrable f (le_of_lt huv)
      (fun t htu htv => hf t (le_trans hau htu) (le_trans htv hvb))
  obtain ⟨J, hJ⟩ := hint
  rw [integral_eq_of_isIntegral f u v J (le_of_lt huv) hJ]
  exact H u v J hau hux hxv hvb huv hδv hJ
-- ANCHOR_END: ftc

-- ============================================================
-- §5 監査総決算: 公理の勾配（どの数学がどの公理を要求したか一望する）
-- ============================================================

#print axioms sum_id                 -- [Real, instLOF] 古典論理ゼロ
#print axioms rs_insert_bound        -- +propext, Quot.sound（choice フリー）
#print axioms rs_multi_insert_bound  -- +choice（探索 find_interval の値段）
#print axioms rs_refine_eq           -- +choice（rmin = 素朴 if 定義の min が源）
#print axioms isintegral_id          -- choice あり・sup なし（完備性不要）
#print axioms continuous_unif_cont   -- +sup, sup_ub, sup_lub（連結性論法の値段）
#print axioms ftc_core               -- 核（一意性フリー）
#print axioms ftc                    -- 実体化で全公理が揃う
