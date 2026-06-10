import MyProject.Integral.Bounded

noncomputable section

-- ============================================================
-- 区間加法性のための補助補題
-- ============================================================

private theorem add_lt_add_right' {x y : Real} (h : x < y) (c : Real) : x + c < y + c := by
  rw [add_comm x c, add_comm y c]
  exact add_left_lt c x y h

-- [a,a] 上の積分値は 0
private theorem isintegral_self_zero (f : Real → Real) (a i : Real)
    (h : IsIntegral f a a i) : i = 0 :=
  integral_unique f a a i 0 (le_refl a) h (isintegral_self f a)

-- 区間加法性の核心：a ≤ b ≤ c のとき積分値も加法的
private theorem interval_add_isintegral (f : Real → Real) (a b c I₁ I₂ : Real)
    (hab_le : a ≤ b) (hbc_le : b ≤ c)
    (h₁ : IsIntegral f a b I₁) (h₂ : IsIntegral f b c I₂) :
    IsIntegral f a c (I₁ + I₂) := by
  cases Classical.em (a = b) with
  | inl heq =>
    subst heq
    rw [show I₁ + I₂ = I₂ from by
          rw [isintegral_self_zero f a I₁ h₁]
          exact AddCommGroup.zero_add I₂]
    exact h₂
  | inr hne_ab =>
    cases Classical.em (b = c) with
    | inl heq =>
      subst heq
      rw [show I₁ + I₂ = I₁ from by
            rw [isintegral_self_zero f b I₂ h₂]
            exact AddCommGroup.add_zero I₁]
      exact h₁
    | inr hne_bc =>
      have hab_lt : a < b := lt_of_le_of_ne hab_le hne_ab
      have hac_le : a ≤ c := le_trans hab_le hbc_le
      have hac_lt : a < c := lt_le_trans a b c hab_lt hbc_le
      -- f の有界性
      obtain ⟨M₁, hM₁⟩ := integrable_bounded f a b hab_le ⟨I₁, h₁⟩
      obtain ⟨M₂, hM₂⟩ := integrable_bounded f b c hbc_le ⟨I₂, h₂⟩
      have hM₁_nn : (0 : Real) ≤ M₁ := le_trans abs_nonneg
        (hM₁ a ((in_interval_iff hab_le).mpr ⟨le_refl a, hab_le⟩))
      have hM₂_nn : (0 : Real) ≤ M₂ := le_trans abs_nonneg
        (hM₂ b ((in_interval_iff hbc_le).mpr ⟨le_refl b, hbc_le⟩))
      have hM : ∀ t, InInterval a c t → (f t).abs ≤ M₁ + M₂ := by
        intro t ht
        have ht' := in_interval_pair hac_le ht
        cases le_total t b with
        | inl htb =>
          apply le_trans (hM₁ t ((in_interval_iff hab_le).mpr ⟨ht'.1, htb⟩))
          exact le_of_add_nonneg_eq rfl hM₂_nn
        | inr hbt =>
          apply le_trans (hM₂ t ((in_interval_iff hbc_le).mpr ⟨hbt, ht'.2⟩))
          exact le_of_nonneg_add_eq rfl hM₁_nn
      have hM_nn : (0 : Real) ≤ M₁ + M₂ :=
        le_trans hM₁_nn (le_of_add_nonneg_eq rfl hM₂_nn)
      have h2M_nn : (0 : Real) ≤ 2 * (M₁ + M₂) := mul_nonneg 2 (M₁ + M₂) zero_lt_two.1 hM_nn
      have hx1 : 2 * (M₁ + M₂) < 2 * (M₁ + M₂) + 1 := by
        have h := add_left_lt (2 * (M₁ + M₂)) 0 1 zero_lt_one
        rwa [add_zero] at h
      have hK_pos : (0 : Real) < 2 * (M₁ + M₂) + 1 := le_lt_trans h2M_nn hx1
      have hK_ne : 2 * (M₁ + M₂) + 1 ≠ 0 := ne_of_gt hK_pos
      intro ε hε
      rcases h₁ (ε / 2 / 2) (pos_half _ (pos_half ε hε)) with ⟨δ₁, hδ₁_pos, hδ₁⟩
      rcases h₂ (ε / 2 / 2) (pos_half _ (pos_half ε hε)) with ⟨δ₂, hδ₂_pos, hδ₂⟩
      refine ⟨min (min δ₁ δ₂) (ε / 2 / (2 * (M₁ + M₂) + 1)),
        min_pos _ _ (min_pos _ _ hδ₁_pos hδ₂_pos)
          (pos_div_pos _ _ (pos_half ε hε) hK_pos), ?_⟩
      intro ⟨n, Δ, ξ, hr⟩ hd
      have hn : 0 < n := Δ.pos_of_lt hac_lt
      have hb_in : InInterval a c b := (in_interval_iff hac_le).mpr ⟨hab_le, hbc_le⟩
      obtain ⟨k, hkL, hkR⟩ := Partition.find_interval Δ b hn hb_in
      obtain ⟨ξ', hr', hbd'⟩ :=
        rs_insert_bound f b (M₁ + M₂) hM hM_nn Δ ξ hr k hkL hkR
      obtain ⟨kv, hkv⟩ := k
      obtain ⟨d, hd_eq⟩ : ∃ d, n = kv + d + 1 := ⟨n - kv - 1, by omega⟩
      subst hd_eq
      let Δ' := Δ.insertPoint b ⟨kv, hkv⟩ hkL hkR
      have hb_pt : Δ'.points ⟨kv + 1, by omega⟩ = b :=
        Partition.insertPoint_pt_mid b Δ ⟨kv, hkv⟩ hkL hkR
      -- 左右の部分分割
      let ΔL : Partition (kv + 1) a b := {
        points := fun p => Δ'.points ⟨p.val, by have := p.property; omega⟩
        increase := fun i => Δ'.increase ⟨i.val, by have := i.property; omega⟩
        left := Δ'.left
        right := hb_pt }
      let ξL : Range (kv + 1) → Real := fun i => ξ' ⟨i.val, by have := i.property; omega⟩
      have hrL : ΔL.IsRepr ξL :=
        fun i => hr' ⟨i.val, by have := i.property; omega⟩
      let ΔR : Partition (d + 1) b c := {
        points := fun p => Δ'.points ⟨kv + p.val + 1, by have := p.property; omega⟩
        increase := fun j => Δ'.increase ⟨kv + j.val + 1, by have := j.property; omega⟩
        left := hb_pt
        right := Δ'.right }
      let ξR : Range (d + 1) → Real := fun j => ξ' ⟨kv + j.val + 1, by have := j.property; omega⟩
      have hrR : ΔR.IsRepr ξR :=
        fun j => hr' ⟨kv + j.val + 1, by have := j.property; omega⟩
      -- 各小区間の長さは元の diam 以下
      have hlen' : ∀ q : Range (kv + d + 1 + 1),
          Partition.length Δ' q ≤ Partition.diam Δ :=
        Partition.insertPoint_length_le_diam b Δ ⟨kv, hkv⟩ hkL hkR
      have hdiam_nn : 0 ≤ Partition.diam Δ := Δ.diam_nonneg hn
      have hdiamL : Partition.diam ΔL < δ₁ :=
        le_lt_trans
          (fmax'_le (kv + 1) _ _ hdiam_nn
            (fun i => hlen' ⟨i.val, by have := i.property; omega⟩))
          (lt_le_trans _ _ _ hd (le_trans (min_left_le _ _) (min_left_le δ₁ δ₂)))
      have hdiamR : Partition.diam ΔR < δ₂ :=
        le_lt_trans
          (fmax'_le (d + 1) _ _ hdiam_nn
            (fun j => hlen' ⟨kv + j.val + 1, by have := j.property; omega⟩))
          (lt_le_trans _ _ _ hd (le_trans (min_left_le _ _) (min_right_le δ₁ δ₂)))
      have hL_close := hδ₁ ⟨kv + 1, ΔL, ξL, hrL⟩ hdiamL
      have hR_close := hδ₂ ⟨d + 1, ΔR, ξR, hrR⟩ hdiamR
      -- RS の分割恒等式
      have e1 : RiemannSum f Δ' ξ' =
          Summation kv (fun i => f (ξ' ⟨i.val, by have := i.property; omega⟩) *
            Partition.length Δ'
              ⟨i.val, by have := i.property; omega⟩) +
          Summation (d + 2) (fun j => f (ξ' ⟨kv + j.val, by have := j.property; omega⟩) *
            Partition.length Δ'
              ⟨kv + j.val, by have := j.property; omega⟩) :=
        summation_split_at kv (d + 2)
          (fun q => f (ξ' q) * Partition.length Δ' q)
      have e2 : Summation (d + 2) (fun j => f (ξ' ⟨kv + j.val, by have := j.property; omega⟩) *
            Partition.length Δ'
              ⟨kv + j.val, by have := j.property; omega⟩) =
          f (ξ' ⟨kv, by omega⟩) *
            Partition.length Δ' ⟨kv, by omega⟩ +
          Summation (d + 1) (fun j => f (ξ' ⟨kv + j.val + 1, by have := j.property; omega⟩) *
            Partition.length Δ'
              ⟨kv + j.val + 1, by have := j.property; omega⟩) :=
        summation_first (d + 1)
          (fun j => f (ξ' ⟨kv + j.val, by have := j.property; omega⟩) *
            Partition.length Δ'
              ⟨kv + j.val, by have := j.property; omega⟩)
      have e3 : RiemannSum f ΔL ξL =
          Summation kv (fun i => f (ξ' ⟨i.val, by have := i.property; omega⟩) *
            Partition.length Δ'
              ⟨i.val, by have := i.property; omega⟩) +
          f (ξ' ⟨kv, by omega⟩) *
            Partition.length Δ' ⟨kv, by omega⟩ :=
        summation_succ kv
          (fun i => f (ξL i) * Partition.length ΔL i)
      have e4 : RiemannSum f ΔR ξR =
          Summation (d + 1) (fun j => f (ξ' ⟨kv + j.val + 1, by have := j.property; omega⟩) *
            Partition.length Δ'
              ⟨kv + j.val + 1, by have := j.property; omega⟩) := rfl
      have hsplit_sum : RiemannSum f Δ' ξ' =
          RiemannSum f ΔL ξL + RiemannSum f ΔR ξR := by
        rw [e1, e2, e3, e4, add_assoc]
      -- 挿入誤差の評価
      have hδ₃_nn : (0 : Real) ≤ ε / 2 / (2 * (M₁ + M₂) + 1) :=
        le_of_lt (pos_div_pos _ _ (pos_half ε hε) hK_pos)
      have hsplit_term : (RiemannSum f Δ' ξ' -
          RiemannSum f Δ ξ).abs ≤ ε / 2 := by
        apply le_trans hbd'
        have h1 : Partition.length Δ ⟨kv, hkv⟩ ≤
            Partition.diam Δ := le_fmax' _ _ _
        have h2 : Partition.diam Δ ≤ ε / 2 / (2 * (M₁ + M₂) + 1) :=
          le_of_lt (lt_le_trans _ _ _ hd (min_right_le _ _))
        calc 2 * (M₁ + M₂) * Partition.length Δ ⟨kv, hkv⟩
            ≤ 2 * (M₁ + M₂) * (ε / 2 / (2 * (M₁ + M₂) + 1)) :=
              mul_le_mul_left _ _ _ h2M_nn (le_trans h1 h2)
          _ ≤ (2 * (M₁ + M₂) + 1) * (ε / 2 / (2 * (M₁ + M₂) + 1)) :=
              nonneg_mul_nonneg _ _ _ hδ₃_nn (le_of_lt hx1)
          _ = ε / 2 := by
              rw [mul_comm]
              exact div_mul_cancel' (ε / 2) _ hK_ne
      -- 仕上げ
      have hA : (RiemannSum f Δ' ξ' - (I₁ + I₂)).abs < ε / 2 := by
        rw [hsplit_sum, add_sub_add]
        apply le_lt_trans (abs_triangle _ _)
        rw [show ε / 2 = ε / 2 / 2 + ε / 2 / 2 from (half_add (ε / 2)).symm]
        exact lt_add_lt _ _ _ _ hL_close hR_close
      calc (RiemannSum f Δ ξ - (I₁ + I₂)).abs
          ≤ (RiemannSum f Δ ξ - RiemannSum f Δ' ξ').abs +
            (RiemannSum f Δ' ξ' - (I₁ + I₂)).abs :=
            abs_sub_le_add _ (RiemannSum f Δ' ξ') _
        _ = (RiemannSum f Δ' ξ' - RiemannSum f Δ ξ).abs +
            (RiemannSum f Δ' ξ' - (I₁ + I₂)).abs := by
            rw [abs_sub_comm (RiemannSum f Δ ξ)]
        _ ≤ ε / 2 + (RiemannSum f Δ' ξ' - (I₁ + I₂)).abs :=
            add_le_add_right _ _ _ hsplit_term
        _ < ε / 2 + ε / 2 := add_left_lt _ _ _ hA
        _ = ε := half_add ε

/-- 区間の連結に関する可積分性（公開 API）。 -/
theorem interval_add_integrable (f : Real → Real) (a b c : Real)
    (hab' : a ≤ b) (hbc' : b ≤ c)
    (hab : IsIntegrable f a b) (hbc : IsIntegrable f b c) :
    IsIntegrable f a c := by
  obtain ⟨I₁, h₁⟩ := hab
  obtain ⟨I₂, h₂⟩ := hbc
  exact ⟨I₁ + I₂, interval_add_isintegral f a b c I₁ I₂ hab' hbc' h₁ h₂⟩

theorem interval_add_integral (f : Real → Real) (a b c : Real)
    (hab' : a ≤ b) (hbc' : b ≤ c)
    (hab : IsIntegrable f a b) (hbc : IsIntegrable f b c) :
    Integral f a b + Integral f b c = Integral f a c := by
  obtain ⟨I₁, h₁⟩ := hab
  obtain ⟨I₂, h₂⟩ := hbc
  rw [IsIntegral_iff f a b I₁ hab' h₁, IsIntegral_iff f b c I₂ hbc' h₂,
      IsIntegral_iff f a c (I₁ + I₂) (le_trans hab' hbc')
        (interval_add_isintegral f a b c I₁ I₂ hab' hbc' h₁ h₂)]

-- integral_sub_interval' は向きなし積分では一般に成立しないため削除した
-- （区間の加法性は interval_add_integral を使う）
