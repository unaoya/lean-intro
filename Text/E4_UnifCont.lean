-- Text/E4_UnifCont.lean — 発展部 §4: 閉区間上の連続関数の一様連続性と有界性
-- Near / NearLe の両側述語で書く（脱 abs）。min も使わない（exists_min2 で合流）。
-- 一様連続性は sup 公理による連結性論法（S(t) = 「[u,t] 上 ε-一様連続」の sup が v に達する）
import Text.E3_Refine

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 Near / NearLe ツールキットの拡張（対称性・推移・単調性）
-- ============================================================

theorem near_symm {h c x : Real} (hn : Near h c x) : Near h x c := by
  constructor
  · exact sub_lt_swap (sub_lt_of_lt_add hn.2)
  · exact lt_add_of_sub_lt hn.1

theorem near_trans {h h' c t s : Real} (h1 : Near h c t) (h2 : Near h' t s) :
    Near (h + h') c s := by
  constructor
  · rw [sub_sub']
    exact lt_trans _ _ _ (add_lt_add_right (c - h) t (-h') h1.1) h2.1
  · rw [(add_assoc c h h').symm]
    exact lt_trans _ _ _ h2.2 (add_lt_add_right t (c + h) h' h1.2)

theorem nearle_near_trans {h h' c t s : Real} (h1 : NearLe h c t) (h2 : Near h' t s) :
    Near (h + h') c s := by
  constructor
  · rw [sub_sub']
    exact le_lt_trans (sub_le_sub_right h1.1 h') h2.1
  · rw [(add_assoc c h h').symm]
    exact lt_le_trans _ _ _ h2.2 (add_le_add_right t (c + h) h' h1.2)

theorem near_mono {δ δ' c x : Real} (h : Near δ c x) (hle : δ ≤ δ') : Near δ' c x :=
  ⟨le_lt_trans (sub_le_sub_left hle c) h.1,
   lt_le_trans _ _ _ h.2 (add_left_le c δ δ' hle)⟩

theorem nearle_of_near {c x y : Real} (h : Near c x y) : NearLe c x y :=
  ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem nearle_to_near {h H c s : Real} (hle : NearLe h c s) (hlt : h < H) :
    Near H c s :=
  ⟨lt_le_trans _ _ _ (sub_lt_sub_left hlt c) hle.1,
   le_lt_trans hle.2 (add_left_lt c h H hlt)⟩

-- ============================================================
-- §2 min を使わない合流の小物
-- ============================================================

-- 2 つの正数の両方以下の正数（min の代わり: le_total の場合分け）
theorem exists_min2 (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    ∃ c, 0 < c ∧ c ≤ a ∧ c ≤ b := by
  cases le_total a b with
  | inl h => exact ⟨a, ha, le_refl a, h⟩
  | inr h => exact ⟨b, hb, h, le_refl b⟩

-- x と -x の両方を上から抑える非負数（abs の代わり）
theorem exists_abs_bound (x : Real) : ∃ A, 0 ≤ A ∧ x ≤ A ∧ -x ≤ A := by
  cases le_total 0 x with
  | inl h =>
    refine ⟨x, h, le_refl x, ?_⟩
    have h1 := neg_le_neg' h
    rw [neg_zero] at h1
    exact le_trans h1 h
  | inr h =>
    refine ⟨-x, neg_neg_nonneg x h, ?_, le_refl (-x)⟩
    have h1 := neg_le_neg' h
    rw [neg_zero] at h1
    exact le_trans h h1

-- ============================================================
-- §3 一様連続性: 連結性論法（sup 公理の本領）
--    S(t) := 「f は [u,t] 上 ε-一様連続」。S の sup が v に達することを示す。
-- ============================================================

theorem continuous_unif_cont (f : Real → Real) {u v : Real} (huv : u ≤ v)
    (hf : ∀ x, u ≤ x → x ≤ v → ContinuousAt f x) (ε : Real) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ s t, u ≤ s → s ≤ v → u ≤ t → t ≤ v →
      Near δ s t → Near ε (f s) (f t) := by
  let S : Real → Prop := fun t =>
    u ≤ t ∧ t ≤ v ∧ ∃ δ, 0 < δ ∧ ∀ s₁ s₂, u ≤ s₁ → s₁ ≤ t → u ≤ s₂ → s₂ ≤ t →
      Near δ s₁ s₂ → Near ε (f s₁) (f s₂)
  have Sa : S u := by
    refine ⟨le_refl u, huv, 1, zero_lt_one, fun s₁ s₂ h1u h1t h2u h2t _ => ?_⟩
    rw [show s₁ = u from le_antisymm s₁ u h1t h1u,
        show s₂ = u from le_antisymm s₂ u h2t h2u]
    exact near_self hε
  have hne : ∃ x, S x := ⟨u, Sa⟩
  have hbdd : ∃ M, ∀ x, S x → x ≤ M := ⟨v, fun x hx => hx.2.1⟩
  let c := Real.sup S hne hbdd
  have hcu : u ≤ c := Real.sup_ub S hne hbdd u Sa
  have hcv : c ≤ v := Real.sup_lub S hne hbdd v (fun x hx => hx.2.1)
  -- c での連続性から δc を取る（誤差は ε/2 で）
  obtain ⟨δc, hδc_pos, hδc⟩ := hf c hcu hcv (ε / (1 + 1)) (pos_half ε hε)
  have hδc2_pos : 0 < δc / (1 + 1) := pos_half δc hδc_pos
  -- c − δc/2 は S の上界でない → δc/2-近くに S の元 t₀ がある
  have ht₀ : ∃ t₀, S t₀ ∧ ¬(t₀ ≤ c - δc / (1 + 1)) := by
    cases Classical.em (∃ t₀, S t₀ ∧ ¬(t₀ ≤ c - δc / (1 + 1))) with
    | inl h => exact h
    | inr h =>
      exfalso
      have hall : ∀ t₀, S t₀ → t₀ ≤ c - δc / (1 + 1) := fun t₀ ht₀ =>
        (Classical.em (t₀ ≤ c - δc / (1 + 1))).elim id
          (fun hn => absurd ⟨t₀, ht₀, hn⟩ h)
      have hle := Real.sup_lub S hne hbdd (c - δc / (1 + 1)) hall
      exact (le_lt_trans hle (sub_lt_self c hδc2_pos)).2 rfl
  obtain ⟨t₀, ht₀S, ht₀_close⟩ := ht₀
  have ht₀_gt : c - δc / (1 + 1) < t₀ := not_le_imp_lt ht₀_close
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := ht₀S.2.2
  -- δ' := 「δ₀ と δc/2 の両方以下の正数」（min の代わり）
  obtain ⟨δ', hδ'_pos, hδ'_le0, hδ'_lec⟩ := exists_min2 δ₀ (δc / (1 + 1)) hδ₀_pos hδc2_pos
  -- t₀ より右の点は c の δc/2-近傍（t₀ を経由する）
  have hnear_c : ∀ s, ¬(s ≤ t₀) → s ≤ c → Near (δc / (1 + 1)) c s := fun s hgt hsc =>
    ⟨lt_trans _ _ _ ht₀_gt (not_le_imp_lt hgt),
     le_lt_trans hsc (lt_add_pos c _ hδc2_pos)⟩
  -- 鍵: [u, c] 上で δ'-一様連続
  have unif_on_c : ∀ s₁ s₂, u ≤ s₁ → s₁ ≤ c → u ≤ s₂ → s₂ ≤ c →
      Near δ' s₁ s₂ → Near ε (f s₁) (f s₂) := by
    intro s₁ s₂ h1u h1c h2u h2c hdist
    cases Classical.em (s₁ ≤ t₀ ∧ s₂ ≤ t₀) with
    | inl hboth =>
      -- 両方 [u, t₀]: t₀ の証拠 δ₀ で済む
      exact hδ₀ s₁ s₂ h1u hboth.1 h2u hboth.2 (near_mono hdist hδ'_le0)
    | inr hnotboth =>
      -- 少なくとも一方が t₀ より右: 両方 c の δc-近傍に入り、f(c) を経由する
      have hdist' : Near (δc / (1 + 1)) s₁ s₂ := near_mono hdist hδ'_lec
      have h_s1 : Near δc c s₁ := by
        cases Classical.em (s₁ ≤ t₀) with
        | inr hgt => exact near_mono (hnear_c s₁ hgt h1c) (le_of_lt (half_lt hδc_pos))
        | inl hle =>
          have hs₂_gt : ¬(s₂ ≤ t₀) := fun h => hnotboth ⟨hle, h⟩
          have h1 := near_trans (hnear_c s₂ hs₂_gt h2c) (near_symm hdist')
          rwa [half_add δc] at h1
      have h_s2 : Near δc c s₂ := by
        cases Classical.em (s₂ ≤ t₀) with
        | inr hgt => exact near_mono (hnear_c s₂ hgt h2c) (le_of_lt (half_lt hδc_pos))
        | inl hle =>
          have hs₁_gt : ¬(s₁ ≤ t₀) := fun h => hnotboth ⟨h, hle⟩
          have h1 := near_trans (hnear_c s₁ hs₁_gt h1c) hdist'
          rwa [half_add δc] at h1
      -- f(c) を経由: Near (ε/2) (f c) (f s₁), Near (ε/2) (f c) (f s₂)
      have h1 := near_trans (near_symm (hδc s₁ h_s1)) (hδc s₂ h_s2)
      rwa [half_add ε] at h1
  -- c = v を背理法で示す（c < v なら S を c より右へ伸ばせて sup と矛盾）
  have hc_eq : c = v := by
    cases Classical.em (c = v) with
    | inl h => exact h
    | inr hne_cv =>
      exfalso
      have hclt : c < v := lt_of_le_of_ne hcv hne_cv
      have hvc_pos : 0 < v - c := sub_pos_of_lt hclt
      -- η := 「δc/2 と (v−c)/2 の両方以下の正数」
      obtain ⟨η, hη_pos, hη_lec, hη_lev⟩ :=
        exists_min2 (δc / (1 + 1)) ((v - c) / (1 + 1)) hδc2_pos (pos_half _ hvc_pos)
      have hcη_le_v : c + η ≤ v := by
        have h1 : η ≤ v - c := le_trans hη_lev (le_of_lt (half_lt hvc_pos))
        have h2 := add_left_le c η (v - c) h1
        rwa [add_sub_cancel' c v] at h2
      have hu_le_cη : u ≤ c + η := le_trans hcu (le_of_lt (lt_add_pos c η hη_pos))
      -- [c, c+η] の点は c の閉 δc/2-近傍
      have close_ext : ∀ s, c ≤ s → s ≤ c + η → NearLe (δc / (1 + 1)) c s :=
        fun s hcs hscη =>
          ⟨le_trans (le_of_lt (sub_lt_self c hδc2_pos)) hcs,
           le_trans hscη (add_left_le c η _ hη_lec)⟩
      -- S(c+η) が成り立つ（モジュラスは同じ δ'）
      have hSext : S (c + η) := by
        refine ⟨hu_le_cη, hcη_le_v, δ', hδ'_pos, ?_⟩
        intro s₁ s₂ h1u h1cη h2u h2cη hdist
        cases Classical.em (s₁ ≤ c ∧ s₂ ≤ c) with
        | inl hboth => exact unif_on_c s₁ s₂ h1u hboth.1 h2u hboth.2 hdist
        | inr hnotboth =>
          have hdist' : Near (δc / (1 + 1)) s₁ s₂ := near_mono hdist hδ'_lec
          have h_s1 : Near δc c s₁ := by
            cases Classical.em (s₁ ≤ c) with
            | inr hgt =>
              exact nearle_to_near
                (close_ext s₁ (le_of_lt (not_le_imp_lt hgt)) h1cη) (half_lt hδc_pos)
            | inl hle =>
              have hs₂_gt : ¬(s₂ ≤ c) := fun h => hnotboth ⟨hle, h⟩
              have h1 := nearle_near_trans
                (close_ext s₂ (le_of_lt (not_le_imp_lt hs₂_gt)) h2cη)
                (near_symm hdist')
              rwa [half_add δc] at h1
          have h_s2 : Near δc c s₂ := by
            cases Classical.em (s₂ ≤ c) with
            | inr hgt =>
              exact nearle_to_near
                (close_ext s₂ (le_of_lt (not_le_imp_lt hgt)) h2cη) (half_lt hδc_pos)
            | inl hle =>
              have hs₁_gt : ¬(s₁ ≤ c) := fun h => hnotboth ⟨h, hle⟩
              have h1 := nearle_near_trans
                (close_ext s₁ (le_of_lt (not_le_imp_lt hs₁_gt)) h1cη)
                hdist'
              rwa [half_add δc] at h1
          have h1 := near_trans (near_symm (hδc s₁ h_s1)) (hδc s₂ h_s2)
          rwa [half_add ε] at h1
      -- c + η ∈ S なのに sup = c より大きい: 矛盾
      have hle_sup := Real.sup_ub S hne hbdd (c + η) hSext
      exact (lt_le_trans c (c + η) c (lt_add_pos c η hη_pos) hle_sup).2 rfl
  -- 仕上げ: c = v を代入
  refine ⟨δ', hδ'_pos, ?_⟩
  intro s t hsu hsv htu htv hdist
  rw [← hc_eq] at hsv htv
  exact unif_on_c s t hsu hsv htu htv hdist

-- ============================================================
-- §4 有界性: 一様連続性（ε = 1）＋鎖の帰納法
--    u から δ/2 刻みで N 歩進めば v を越える（アルキメデス = ceil）。
--    k 歩目までで NearLe k (f u) (f t)。
-- ============================================================

theorem continuous_bounded (f : Real → Real) {u v : Real} (huv : u ≤ v)
    (hf : ∀ x, u ≤ x → x ≤ v → ContinuousAt f x) :
    ∃ M, 0 < M ∧ (∀ t, u ≤ t → t ≤ v → -M ≤ f t) ∧
      (∀ t, u ≤ t → t ≤ v → f t ≤ M) := by
  obtain ⟨δ, hδ_pos, huc⟩ := continuous_unif_cont f huv hf 1 zero_lt_one
  have hδ2_pos : 0 < δ / (1 + 1) := pos_half δ hδ_pos
  have hδ2_ne : δ / (1 + 1) ≠ 0 := fun h => hδ2_pos.2 h.symm
  -- N 歩で [u, v] を覆う
  let N := ceil ((v - u) / (δ / (1 + 1)))
  have hN_lt : (v - u) / (δ / (1 + 1)) < (N : Real) := ceil_lt _
  have hvu_lt : v - u < (N : Real) * (δ / (1 + 1)) := by
    have h := mul_right_lt _ (N : Real) (δ / (1 + 1)) hδ2_pos hN_lt
    rwa [div_mul_cancel (v - u) _ hδ2_ne] at h
  have hN_bound : v ≤ u + (N : Real) * (δ / (1 + 1)) := by
    have h := add_left_lt u (v - u) ((N : Real) * (δ / (1 + 1))) hvu_lt
    rw [add_sub_cancel' u v] at h
    exact h.1
  -- 鎖の帰納法: t ≤ u + k·(δ/2) なら NearLe k (f u) (f t)
  have chain : ∀ (k : Nat), ∀ t, u ≤ t → t ≤ v →
      t ≤ u + (k : Real) * (δ / (1 + 1)) → NearLe (k : Real) (f u) (f t) := by
    intro k
    induction k with
    | zero =>
      intro t hut _htv htk
      have h0 : ((0 : Nat) : Real) * (δ / (1 + 1)) = 0 := zero_mul' _
      rw [h0, add_zero'] at htk
      rw [show t = u from le_antisymm t u htk hut]
      exact nearle_zero (f u)
    | succ k ih =>
      intro t hut htv htk1
      have hsucc : ((k + 1 : Nat) : Real) = (k : Real) + 1 := succ_ofNat k
      cases Classical.em (t ≤ u + (k : Real) * (δ / (1 + 1))) with
      | inl hle =>
        exact nearle_mono (ih t hut htv hle) (cast_le_succ k)
      | inr hgt =>
        -- s := 1 歩手前の点。s < t ≤ s + δ/2 で一様連続性が効く
        have hs_lt_t : u + (k : Real) * (δ / (1 + 1)) < t := not_le_imp_lt hgt
        have hus : u ≤ u + (k : Real) * (δ / (1 + 1)) :=
          le_add_nonneg u _ (mul_nonneg _ _ (cast_nonneg k) (le_of_lt hδ2_pos))
        have hsv : u + (k : Real) * (δ / (1 + 1)) ≤ v :=
          le_trans (le_of_lt hs_lt_t) htv
        have hts_le : t ≤ (u + (k : Real) * (δ / (1 + 1))) + δ / (1 + 1) := by
          rw [hsucc, CommRing.right_distrib (k : Real) 1 (δ / (1 + 1)), one_mul,
              (add_assoc u ((k : Real) * (δ / (1 + 1))) (δ / (1 + 1))).symm] at htk1
          exact htk1
        have hnear : Near δ (u + (k : Real) * (δ / (1 + 1))) t := by
          constructor
          · exact lt_trans _ _ _ (sub_lt_self _ hδ_pos) hs_lt_t
          · exact le_lt_trans hts_le
              (add_left_lt (u + (k : Real) * (δ / (1 + 1))) _ _ (half_lt hδ_pos))
        have h_uc := huc (u + (k : Real) * (δ / (1 + 1))) t hus hsv hut htv hnear
        have h_ih := ih (u + (k : Real) * (δ / (1 + 1))) hus hsv (le_refl _)
        have h_comb := nearle_trans h_ih (nearle_of_near h_uc)
        rw [hsucc]
        exact h_comb
  -- 仕上げ: |f u| の代替境界 A を取り、M := A + N + 1
  obtain ⟨A, hA0, hA1, hA2⟩ := exists_abs_bound (f u)
  refine ⟨A + (N : Real) + 1, ?_, ?_, ?_⟩
  · -- 0 < M
    have h1 : (0 : Real) ≤ A + (N : Real) :=
      le_trans hA0 (le_add_nonneg A _ (cast_nonneg N))
    exact le_lt_trans h1 (lt_add_pos (A + (N : Real)) 1 zero_lt_one)
  · -- -M ≤ f t
    intro t hut htv
    have hchain := chain N t hut htv (le_trans htv hN_bound)
    -- -(A+N+1) ≤ -(A+N) = -A - N ≤ f u - N ≤ f t
    have h1 : -(A + (N : Real) + 1) ≤ -(A + (N : Real)) :=
      neg_le_neg' (le_add_nonneg (A + (N : Real)) 1 (le_of_lt zero_lt_one))
    have h2 : -(A + (N : Real)) = -A + -(N : Real) := neg_add_distrib A (N : Real)
    have h3 : -A + -(N : Real) ≤ f u + -(N : Real) := add_le_add_right (-A) (f u) _ (by
      have h4 := neg_le_neg' hA2
      rwa [neg_neg] at h4)
    rw [h2] at h1
    exact le_trans (le_trans h1 h3) hchain.1
  · -- f t ≤ M
    intro t hut htv
    have hchain := chain N t hut htv (le_trans htv hN_bound)
    have h1 : f u + (N : Real) ≤ A + (N : Real) := add_le_add_right (f u) A _ hA1
    have h2 : A + (N : Real) ≤ A + (N : Real) + 1 :=
      le_add_nonneg (A + (N : Real)) 1 (le_of_lt zero_lt_one)
    exact le_trans hchain.2 (le_trans h1 h2)

#print axioms continuous_unif_cont
#print axioms continuous_bounded
