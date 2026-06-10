import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 積分の区間についての加法性

-- リーマン可積分なら有界であることを示し、それを用いる。
theorem integrable_bounded (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (h : IsIntegrable f a b) : ∃ M, ∀ x, InInterval a b x → abs (f x) ≤ M := by
  cases Classical.em (b ≤ a) with
  | inl hba =>
    -- a = b : 区間は一点のみ
    have heq : a = b := LinearOrderedField.le_asymm a b hab hba
    subst heq
    refine ⟨(f a).abs, fun x hx => ?_⟩
    dsimp [InInterval] at hx
    rw [if_pos (le_refl a)] at hx
    rw [LinearOrderedField.le_asymm x a hx.2 hx.1]
    exact le_refl _
  | inr hba =>
    have hba_pos : 0 < b - a := (pos_iff_lt a b).mp (ne_le_lt b a hba)
    obtain ⟨I, hI⟩ := h
    obtain ⟨δ, hδ, hbound⟩ := hI 1 zero_lt_one
    have hba_div_nn : 0 ≤ (b - a) / δ :=
      nonneg_div_nonneg (b - a) δ ((nonneg_iff_le a b).mp hab) hδ
    -- 等分割を構成
    obtain ⟨m, hm_lt, hm_ne, hm_pos_r⟩ :
        ∃ m : Nat, (b - a) / δ < (m : Real) ∧ m ≠ 0 ∧ (0 : Real) < (m : Real) := by
      refine ⟨ceil ((b - a) / δ), ceil_lt _, ?_, le_lt_trans hba_div_nn (ceil_lt _)⟩
      intro hm0
      have hc := ceil_lt ((b - a) / δ)
      rw [hm0] at hc
      exact (le_lt_trans hba_div_nn hc).2 rfl
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
    let Δ := equalPartition m a b hm_ne hab
    let ξ := equalPartitionRepr m a b hm_ne hab
    have h_repr : Δ.IsRepr a b m ξ := equalPartitionRepr_isrepr m a b hm_ne hab
    have h_diam : Partition.diam m a b Δ < δ :=
      equalPartition_diam_lt m a b δ hm_ne hab hδ hm_lt
    have hL_pos : 0 < (b - a) / (m : Real) := pos_div_pos _ _ hba_pos hm_pos_r
    have hL_ne : (b - a) / (m : Real) ≠ 0 := fun h0 => hL_pos.2 h0.symm
    -- 各点 x で、x を含む小区間の代表点だけ x に取り替えた代表点列と比較する
    refine ⟨2 / ((b - a) / (m : Real)) + fmax' m (fun j => (f (ξ j)).abs), ?_⟩
    intro x hx
    obtain ⟨k, hkL, hkR⟩ := Partition.find_interval m a b x Δ hm_pos hx
    let ξ' : Range m → Real := fun i => if i.val = k.val then x else ξ i
    have hr_bounds : ∀ j : Range m,
        Δ.points j.incl ≤ ξ j ∧ ξ j ≤ Δ.points j.addone := by
      intro j
      have hj := h_repr j
      dsimp [InInterval] at hj
      rwa [if_pos (Δ.increase j)] at hj
    have h_repr' : Δ.IsRepr a b m ξ' := by
      apply Partition.le_isrepr
      intro i
      by_cases hi : i.val = k.val
      · have hik : i = k := Subtype.ext hi
        rw [show ξ' i = x from if_pos hi, hik]
        exact ⟨hkL, hkR⟩
      · rw [show ξ' i = ξ i from if_neg hi]
        exact hr_bounds i
    -- 一点だけ代表点を変えた RS の差 = (f x - f (ξ k)) * length k
    have hdiff : RiemannSum f a b m Δ ξ' - RiemannSum f a b m Δ ξ =
        (f x - f (ξ k)) * Partition.length m a b Δ k := by
      show Summation m (fun i => f (ξ' i) * Partition.length m a b Δ i) -
          Summation m (fun i => f (ξ i) * Partition.length m a b Δ i) = _
      have hterm : ∀ i : Range m, f (ξ' i) * Partition.length m a b Δ i =
          f (ξ i) * Partition.length m a b Δ i +
          (if i.val = k.val then (f x - f (ξ k)) * Partition.length m a b Δ k
           else 0) := by
        intro i
        by_cases hi : i.val = k.val
        · have hik : i = k := Subtype.ext hi
          rw [show ξ' i = x from if_pos hi, if_pos hi, hik, ← add_mul, add_sub_cancel']
        · rw [show ξ' i = ξ i from if_neg hi, if_neg hi, add_zero]
      rw [summation_congr m _ _ hterm, additive_summation,
          summation_one_term m k _ (fun i hne => if_neg hne),
          if_pos (show k.val = k.val from rfl), add_sub_cancel]
    have hRS : (RiemannSum f a b m Δ ξ - I).abs < 1 := hbound m Δ ξ h_repr h_diam
    have hRS' : (RiemannSum f a b m Δ ξ' - I).abs < 1 := hbound m Δ ξ' h_repr' h_diam
    have h2 : ((f x - f (ξ k)) * Partition.length m a b Δ k).abs < 2 := by
      rw [← hdiff]
      have hns : I - RiemannSum f a b m Δ ξ = -(RiemannSum f a b m Δ ξ - I) := by
        show I + -RiemannSum f a b m Δ ξ = -(RiemannSum f a b m Δ ξ + -I)
        rw [neg_add_distrib, neg_neg, AddCommGroup.add_comm]
      calc (RiemannSum f a b m Δ ξ' - RiemannSum f a b m Δ ξ).abs
          = ((I - RiemannSum f a b m Δ ξ) + (RiemannSum f a b m Δ ξ' - I)).abs := by
            rw [telescope_2 (RiemannSum f a b m Δ ξ) (RiemannSum f a b m Δ ξ') I]
        _ ≤ (I - RiemannSum f a b m Δ ξ).abs + (RiemannSum f a b m Δ ξ' - I).abs :=
            abs_triangle _ _
        _ = (RiemannSum f a b m Δ ξ - I).abs + (RiemannSum f a b m Δ ξ' - I).abs := by
            rw [hns, abs_neg]
        _ < 1 + 1 := lt_add_lt _ _ _ _ hRS hRS'
        _ = 2 := rfl
    have hlen : Partition.length m a b Δ k = (b - a) / (m : Real) :=
      equalPartition_length m a b hm_ne hab k
    rw [hlen, abs_mul_nonneg hL_pos.1] at h2
    -- |f x - f (ξ k)| < 2 / L
    have hfk : (f x - f (ξ k)).abs < 2 / ((b - a) / (m : Real)) := by
      rw [← mul_div_cancel ((f x - f (ξ k)).abs) ((b - a) / (m : Real)) hL_ne]
      exact div_right_lt _ _ _ hL_pos h2
    calc (f x).abs
        = ((f x - f (ξ k)) + f (ξ k)).abs := by
          rw [show f x - f (ξ k) + f (ξ k) = f (ξ k) + (f x - f (ξ k)) from
                AddCommGroup.add_comm _ _,
              add_sub_cancel' (f (ξ k)) (f x)]
      _ ≤ (f x - f (ξ k)).abs + (f (ξ k)).abs := abs_triangle _ _
      _ ≤ 2 / ((b - a) / (m : Real)) + (f (ξ k)).abs :=
          LinearOrderedField.add_le_add _ _ _ (Real.le_of_lt hfk)
      _ ≤ 2 / ((b - a) / (m : Real)) + fmax' m (fun j => (f (ξ j)).abs) :=
          add_left_le _ _ _ (le_fmax' m (fun j => (f (ξ j)).abs) k)


-- ============================================================
-- 区間加法性のための補助補題
-- ============================================================

private theorem add_lt_add_right' {x y : Real} (h : x < y) (c : Real) : x + c < y + c := by
  rw [AddCommGroup.add_comm x c, AddCommGroup.add_comm y c]
  exact add_left_lt c x y h

-- [a,a] 上の積分値は 0
private theorem isintegral_self_zero (f : Real → Real) (a i : Real)
    (h : IsIntegral f a a i) : i = 0 := by
  apply lt_epsilon_zero
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
  let Δ0 : Partition 0 a a := {
    points := fun _ => a
    increase := fun i => absurd i.property (Nat.not_lt_zero _)
    left := rfl
    right := rfl }
  have hr0 : Δ0.IsRepr a a 0 (fun _ => a) :=
    fun i => absurd i.property (Nat.not_lt_zero _)
  have hd0 : Partition.diam 0 a a Δ0 < δ := hδ_pos
  have hclose := hδ 0 Δ0 (fun _ => a) hr0 hd0
  rw [show RiemannSum f a a 0 Δ0 (fun _ => a) - i = -i from by
        show Summation 0 (fun q => f a * Partition.length 0 a a Δ0 q) - i = -i
        rw [summation_zero]
        exact AddCommGroup.zero_add (-i)] at hclose
  rwa [abs_neg] at hclose

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
      have hab_lt : a < b := ⟨hab_le, hne_ab⟩
      have hbc_lt : b < c := ⟨hbc_le, hne_bc⟩
      have hac_le : a ≤ c := le_trans hab_le hbc_le
      have hac_lt : a < c := lt_le_trans a b c hab_lt hbc_le
      -- f の有界性
      obtain ⟨M₁, hM₁⟩ := integrable_bounded f a b hab_le ⟨I₁, h₁⟩
      obtain ⟨M₂, hM₂⟩ := integrable_bounded f b c hbc_le ⟨I₂, h₂⟩
      have hM₁_nn : (0 : Real) ≤ M₁ := le_trans abs_nonneg (hM₁ a (by
        dsimp [InInterval]; rw [if_pos hab_le]; exact ⟨le_refl a, hab_le⟩))
      have hM₂_nn : (0 : Real) ≤ M₂ := le_trans abs_nonneg (hM₂ b (by
        dsimp [InInterval]; rw [if_pos hbc_le]; exact ⟨le_refl b, hbc_le⟩))
      have hM : ∀ t, InInterval a c t → (f t).abs ≤ M₁ + M₂ := by
        intro t ht
        dsimp [InInterval] at ht
        rw [if_pos hac_le] at ht
        cases LinearOrderedField.le_total t b with
        | inl htb =>
          apply le_trans (hM₁ t (by
            dsimp [InInterval]; rw [if_pos hab_le]; exact ⟨ht.1, htb⟩))
          exact le_of_add_nonneg_eq rfl hM₂_nn
        | inr hbt =>
          apply le_trans (hM₂ t (by
            dsimp [InInterval]; rw [if_pos hbc_le]; exact ⟨hbt, ht.2⟩))
          exact le_of_nonneg_add_eq rfl hM₁_nn
      have hM_nn : (0 : Real) ≤ M₁ + M₂ :=
        le_trans hM₁_nn (le_of_add_nonneg_eq rfl hM₂_nn)
      have h2M_nn : (0 : Real) ≤ 2 * (M₁ + M₂) := mul_nonneg 2 (M₁ + M₂) zero_lt_two.1 hM_nn
      have hx1 : 2 * (M₁ + M₂) < 2 * (M₁ + M₂) + 1 := by
        have h := add_left_lt (2 * (M₁ + M₂)) 0 1 zero_lt_one
        rwa [add_zero] at h
      have hK_pos : (0 : Real) < 2 * (M₁ + M₂) + 1 := le_lt_trans h2M_nn hx1
      have hK_ne : 2 * (M₁ + M₂) + 1 ≠ 0 := fun h0 => hK_pos.2 h0.symm
      intro ε hε
      rcases h₁ (ε / 2 / 2) (pos_half _ (pos_half ε hε)) with ⟨δ₁, hδ₁_pos, hδ₁⟩
      rcases h₂ (ε / 2 / 2) (pos_half _ (pos_half ε hε)) with ⟨δ₂, hδ₂_pos, hδ₂⟩
      refine ⟨min (min δ₁ δ₂) (ε / 2 / (2 * (M₁ + M₂) + 1)),
        min_pos _ _ (min_pos _ _ hδ₁_pos hδ₂_pos)
          (pos_div_pos _ _ (pos_half ε hε) hK_pos), ?_⟩
      intro n Δ ξ hr hd
      have hn : 0 < n := by
        cases n with
        | zero => exact absurd (Partition.zero a c Δ) hac_lt.2
        | succ m => exact Nat.zero_lt_succ m
      have hb_in : InInterval a c b := by
        dsimp [InInterval]; rw [if_pos hac_le]; exact ⟨hab_le, hbc_le⟩
      obtain ⟨k, hkL, hkR⟩ := Partition.find_interval n a c b Δ hn hb_in
      obtain ⟨ξ', hr', hbd'⟩ :=
        rs_insert_bound f a c b (M₁ + M₂) hM hM_nn n Δ ξ hr k hkL hkR
      obtain ⟨kv, hkv⟩ := k
      obtain ⟨d, hd_eq⟩ : ∃ d, n = kv + d + 1 := ⟨n - kv - 1, by omega⟩
      subst hd_eq
      let Δ' := Δ.insertPoint (kv + d + 1) a c b ⟨kv, hkv⟩ hkL hkR
      have hb_pt : Δ'.points ⟨kv + 1, by omega⟩ = b :=
        Partition.insertPoint_pt_mid (kv + d + 1) a c b Δ ⟨kv, hkv⟩ hkL hkR
      -- 左右の部分分割
      let ΔL : Partition (kv + 1) a b := {
        points := fun p => Δ'.points ⟨p.val, by have := p.property; omega⟩
        increase := fun i => Δ'.increase ⟨i.val, by have := i.property; omega⟩
        left := Δ'.left
        right := hb_pt }
      let ξL : Range (kv + 1) → Real := fun i => ξ' ⟨i.val, by have := i.property; omega⟩
      have hrL : ΔL.IsRepr a b (kv + 1) ξL :=
        fun i => hr' ⟨i.val, by have := i.property; omega⟩
      let ΔR : Partition (d + 1) b c := {
        points := fun p => Δ'.points ⟨kv + p.val + 1, by have := p.property; omega⟩
        increase := fun j => Δ'.increase ⟨kv + j.val + 1, by have := j.property; omega⟩
        left := hb_pt
        right := Δ'.right }
      let ξR : Range (d + 1) → Real := fun j => ξ' ⟨kv + j.val + 1, by have := j.property; omega⟩
      have hrR : ΔR.IsRepr b c (d + 1) ξR :=
        fun j => hr' ⟨kv + j.val + 1, by have := j.property; omega⟩
      -- 各小区間の長さは元の diam 以下
      have hlen' : ∀ q : Range (kv + d + 1 + 1),
          Partition.length (kv + d + 1 + 1) a c Δ' q ≤
          Partition.diam (kv + d + 1) a c Δ := by
        intro q
        show Partition.length (kv + d + 1 + 1) a c
          (Δ.insertPoint (kv + d + 1) a c b ⟨kv, hkv⟩ hkL hkR) q ≤ _
        by_cases h1 : q.val < kv
        · rw [Partition.insertPoint_length_low (kv + d + 1) a c b Δ ⟨kv, hkv⟩ hkL hkR q h1]
          exact le_fmax' _ _ _
        · by_cases h2 : kv + 1 < q.val
          · rw [Partition.insertPoint_length_high (kv + d + 1) a c b Δ ⟨kv, hkv⟩ hkL hkR q h2]
            exact le_fmax' _ _ _
          · have hsplit := Partition.insertPoint_length_split (kv + d + 1) a c b Δ
              ⟨kv, hkv⟩ hkL hkR
            by_cases h3 : q.val = kv
            · rw [show q = ⟨kv, by omega⟩ from Subtype.ext h3]
              exact le_trans (le_of_add_nonneg_eq hsplit
                (Partition.length_nonneg _ a c _ ⟨kv + 1, by omega⟩))
                (le_fmax' _ _ ⟨kv, hkv⟩)
            · have h4 : q.val = kv + 1 := by have := q.property; omega
              rw [show q = ⟨kv + 1, by omega⟩ from Subtype.ext h4]
              exact le_trans (le_of_nonneg_add_eq hsplit
                (Partition.length_nonneg _ a c _ ⟨kv, by omega⟩))
                (le_fmax' _ _ ⟨kv, hkv⟩)
      have hdiam_nn : 0 ≤ Partition.diam (kv + d + 1) a c Δ :=
        le_trans (Partition.length_nonneg _ a c Δ ⟨0, by omega⟩)
          (le_fmax' _ _ ⟨0, by omega⟩)
      have hdiamL : Partition.diam (kv + 1) a b ΔL < δ₁ :=
        le_lt_trans
          (fmax'_le (kv + 1) _ _ hdiam_nn
            (fun i => hlen' ⟨i.val, by have := i.property; omega⟩))
          (lt_le_trans _ _ _ hd (le_trans (min_left_le _ _) (min_left_le δ₁ δ₂)))
      have hdiamR : Partition.diam (d + 1) b c ΔR < δ₂ :=
        le_lt_trans
          (fmax'_le (d + 1) _ _ hdiam_nn
            (fun j => hlen' ⟨kv + j.val + 1, by have := j.property; omega⟩))
          (lt_le_trans _ _ _ hd (le_trans (min_left_le _ _) (min_right_le δ₁ δ₂)))
      have hL_close := hδ₁ (kv + 1) ΔL ξL hrL hdiamL
      have hR_close := hδ₂ (d + 1) ΔR ξR hrR hdiamR
      -- RS の分割恒等式
      have e1 : RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' =
          Summation kv (fun i => f (ξ' ⟨i.val, by have := i.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨i.val, by have := i.property; omega⟩) +
          Summation (d + 2) (fun j => f (ξ' ⟨kv + j.val, by have := j.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨kv + j.val, by have := j.property; omega⟩) :=
        summation_split_at kv (d + 2)
          (fun q => f (ξ' q) * Partition.length (kv + d + 1 + 1) a c Δ' q)
      have e2 : Summation (d + 2) (fun j => f (ξ' ⟨kv + j.val, by have := j.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨kv + j.val, by have := j.property; omega⟩) =
          f (ξ' ⟨kv, by omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ' ⟨kv, by omega⟩ +
          Summation (d + 1) (fun j => f (ξ' ⟨kv + j.val + 1, by have := j.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨kv + j.val + 1, by have := j.property; omega⟩) :=
        summation_first (d + 1)
          (fun j => f (ξ' ⟨kv + j.val, by have := j.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨kv + j.val, by have := j.property; omega⟩)
      have e3 : RiemannSum f a b (kv + 1) ΔL ξL =
          Summation kv (fun i => f (ξ' ⟨i.val, by have := i.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨i.val, by have := i.property; omega⟩) +
          f (ξ' ⟨kv, by omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ' ⟨kv, by omega⟩ :=
        summation_succ kv
          (fun i => f (ξL i) * Partition.length (kv + 1) a b ΔL i)
      have e4 : RiemannSum f b c (d + 1) ΔR ξR =
          Summation (d + 1) (fun j => f (ξ' ⟨kv + j.val + 1, by have := j.property; omega⟩) *
            Partition.length (kv + d + 1 + 1) a c Δ'
              ⟨kv + j.val + 1, by have := j.property; omega⟩) := rfl
      have hsplit_sum : RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' =
          RiemannSum f a b (kv + 1) ΔL ξL + RiemannSum f b c (d + 1) ΔR ξR := by
        rw [e1, e2, e3, e4, AddCommGroup.add_assoc]
      -- 挿入誤差の評価
      have hδ₃_nn : (0 : Real) ≤ ε / 2 / (2 * (M₁ + M₂) + 1) :=
        Real.le_of_lt (pos_div_pos _ _ (pos_half ε hε) hK_pos)
      have hsplit_term : (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' -
          RiemannSum f a c (kv + d + 1) Δ ξ).abs ≤ ε / 2 := by
        apply le_trans hbd'
        have h1 : Partition.length (kv + d + 1) a c Δ ⟨kv, hkv⟩ ≤
            Partition.diam (kv + d + 1) a c Δ := le_fmax' _ _ _
        have h2 : Partition.diam (kv + d + 1) a c Δ ≤ ε / 2 / (2 * (M₁ + M₂) + 1) :=
          Real.le_of_lt (lt_le_trans _ _ _ hd (min_right_le _ _))
        calc 2 * (M₁ + M₂) * Partition.length (kv + d + 1) a c Δ ⟨kv, hkv⟩
            ≤ 2 * (M₁ + M₂) * (ε / 2 / (2 * (M₁ + M₂) + 1)) :=
              mul_le_mul_left _ _ _ h2M_nn (le_trans h1 h2)
          _ ≤ (2 * (M₁ + M₂) + 1) * (ε / 2 / (2 * (M₁ + M₂) + 1)) :=
              nonneg_mul_nonneg _ _ _ hδ₃_nn (Real.le_of_lt hx1)
          _ = ε / 2 := by
              rw [MulCommMonoid.mul_comm]
              exact div_mul_cancel' (ε / 2) _ hK_ne
      -- 仕上げ
      have hA : (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' - (I₁ + I₂)).abs < ε / 2 := by
        rw [hsplit_sum, add_sub_add]
        apply le_lt_trans (abs_triangle _ _)
        rw [show ε / 2 = ε / 2 / 2 + ε / 2 / 2 from (half_add (ε / 2)).symm]
        exact lt_add_lt _ _ _ _ hL_close hR_close
      calc (RiemannSum f a c (kv + d + 1) Δ ξ - (I₁ + I₂)).abs
          = ((RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' - (I₁ + I₂)) +
             (RiemannSum f a c (kv + d + 1) Δ ξ -
              RiemannSum f a c (kv + d + 1 + 1) Δ' ξ')).abs := by
            rw [telescope_2 (I₁ + I₂) (RiemannSum f a c (kv + d + 1) Δ ξ)
                (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ')]
        _ ≤ (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' - (I₁ + I₂)).abs +
            (RiemannSum f a c (kv + d + 1) Δ ξ -
             RiemannSum f a c (kv + d + 1 + 1) Δ' ξ').abs := abs_triangle _ _
        _ = (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' - (I₁ + I₂)).abs +
            (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' -
             RiemannSum f a c (kv + d + 1) Δ ξ).abs := by
            rw [show RiemannSum f a c (kv + d + 1) Δ ξ -
                  RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' =
                  -(RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' -
                    RiemannSum f a c (kv + d + 1) Δ ξ) from
                  (neg_sub _ _).symm, abs_neg]
        _ ≤ (RiemannSum f a c (kv + d + 1 + 1) Δ' ξ' - (I₁ + I₂)).abs + ε / 2 :=
            add_left_le _ _ _ hsplit_term
        _ < ε / 2 + ε / 2 := add_lt_add_right' hA (ε / 2)
        _ = ε := half_add ε

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
