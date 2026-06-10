import MyProject.Integral.Partition
import MyProject.Limit

noncomputable section

open Real Classical Range

-- リーマン和の定義
def RiemannSum (f : Real → Real) {n : Nat} {a b : Real}
  (Δ : Partition n a b) (ξ : Range n → Real) : Real :=
    Summation n (fun i ↦ f (ξ i) * Δ.length i)

theorem const_riemann_sum (c : Real) {n : Nat} {a b : Real} (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun _ ↦ c) Δ ξ = c * (b - a) := by
  rw [RiemannSum, summation_smul, Partition.length_sum]

theorem additive_riemann_sum (f g : Real → Real) {n : Nat} {a b : Real}
  (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun t ↦ f t + g t) Δ ξ = RiemannSum f Δ ξ + RiemannSum g Δ ξ := by
  rw [RiemannSum, RiemannSum, RiemannSum, ← additive_summation, summation_congr]
  intro i
  rw [add_mul]

theorem neg_riemann_sum (f : Real → Real) {n : Nat} {a b : Real}
  (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun t ↦ -f t) Δ ξ = -RiemannSum f Δ ξ := by
  rw [RiemannSum, RiemannSum, neg_summation]
  apply summation_congr
  intro i
  rw [neg_mul]

theorem RiemannSum_nonneg (f : Real → Real) {n : Nat} {a b : Real}
    (Δ : Partition n a b) (ξ : Range n → Real)
    (h' : ∀ x, InInterval a b x → 0 ≤ f x) (h : Δ.IsRepr ξ) :
    0 ≤ RiemannSum f Δ ξ := by
  apply summation_nonneg
  intro i
  apply mul_nonneg
  · apply h' (ξ i) (Δ.repr_in_interval ξ h i)
  · apply Δ.length_nonneg i

-- Helper: |RS(f)| ≤ M*(b-a) when |f| ≤ M on [a,b]
theorem rs_abs_bound (f : Real → Real) (M : Real) {n : Nat} {a b : Real}
    (hbound : ∀ t, InInterval a b t → (f t).abs ≤ M)
    (Δ : Partition n a b) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) :
    (RiemannSum f Δ ξ).abs ≤ M * (b - a) := by
  apply abs_le
  · -- -(RS f) ≤ M*(b-a)
    have h0 : -(RiemannSum f Δ ξ) = RiemannSum (fun t => -f t) Δ ξ :=
      (neg_riemann_sum f Δ ξ).symm
    rw [h0]
    have h1 : RiemannSum (fun t => -f t) Δ ξ ≤ RiemannSum (fun _ => M) Δ ξ := by
      apply summation_le; intro i
      apply nonneg_mul_nonneg _ _ _ (Δ.length_nonneg i)
      exact le_trans (neg_le_abs _) (hbound (ξ i) (Δ.repr_in_interval ξ hr i))
    rw [const_riemann_sum] at h1; exact h1
  · -- RS f ≤ M*(b-a)
    have h1 : RiemannSum f Δ ξ ≤ RiemannSum (fun _ => M) Δ ξ := by
      apply summation_le; intro i
      apply nonneg_mul_nonneg _ _ _ (Δ.length_nonneg i)
      exact le_trans (le_abs _) (hbound (ξ i) (Δ.repr_in_interval ξ hr i))
    rw [const_riemann_sum] at h1; exact h1

-- 分割に点を挿入した時の RS の差のバウンド
theorem rs_insert_bound (f : Real → Real) {a b : Real} (c M : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (_hM_nn : 0 ≤ M)
    {n : Nat} (Δ : Partition n a b) (ξ : Range n → Real) (hr : Δ.IsRepr ξ)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    ∃ (ξ' : Range (n + 1) → Real),
      (Δ.insertPoint c k hL hR).IsRepr ξ' ∧
      (RiemannSum f (Δ.insertPoint c k hL hR) ξ' -
       RiemannSum f Δ ξ).abs ≤ 2 * M * Partition.length Δ k := by
  let Δ' := Δ.insertPoint c k hL hR
  -- repr: c for split intervals, original elsewhere
  let ξ' : Range (n + 1) → Real := fun i =>
    if h : i.val < k.val then ξ ⟨i.val, by have := k.property; omega⟩
    else if h₂ : i.val ≤ k.val + 1 then c
    else ξ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩
  have hr_bounds : ∀ j : Range n,
      Δ.points (incl j) ≤ ξ j ∧ ξ j ≤ Δ.points (addone j) := by
    intro j; have hj := hr j; dsimp [InInterval] at hj
    rwa [if_pos (Δ.increase j)] at hj
  refine ⟨ξ', ?repr, ?bound⟩
  case repr =>
    apply Partition.le_isrepr
    intro i
    by_cases h1 : i.val < k.val
    · -- i < k: same repr, same partition points
      rw [show ξ' i = ξ ⟨i.val, by have := k.property; omega⟩ from dif_pos h1,
          Partition.insertPoint_pt_le c Δ k hL hR (incl i)
            (by simp [incl_val]; omega),
          Partition.insertPoint_pt_le c Δ k hL hR (addone i)
            (by simp [addone_val]; omega)]
      exact hr_bounds ⟨i.val, by have := k.property; omega⟩
    · by_cases h2 : i.val ≤ k.val + 1
      · -- i ∈ {k, k+1}: ξ'(i) = c
        rw [show ξ' i = c from (dif_neg h1).trans (dif_pos h2)]
        by_cases h3 : i.val = k.val
        · -- i = k: interval [Δ.pts(incl k), c]
          constructor
          · have hpt : Δ'.points (incl i) = Δ.points (incl k) := by
              rw [Partition.insertPoint_pt_le c Δ k hL hR (incl i)
                    (by simp [incl_val]; omega)]
              congr 1; exact Subtype.ext (by simp [incl_val]; omega)
            rw [hpt]; exact hL
          · have : addone i = (⟨k.val + 1, by have := k.property; omega⟩ : Range (n + 2)) :=
              Subtype.ext (by simp [addone_val]; omega)
            rw [this, Partition.insertPoint_pt_mid]; exact le_refl c
        · -- i = k+1: interval [c, Δ.pts(addone k)]
          constructor
          · have : incl i = (⟨k.val + 1, by have := k.property; omega⟩ : Range (n + 2)) :=
              Subtype.ext (by simp [incl_val]; omega)
            rw [this, Partition.insertPoint_pt_mid]; exact le_refl c
          · have hpt : Δ'.points (addone i) = Δ.points (addone k) := by
              rw [Partition.insertPoint_pt_gt c Δ k hL hR (addone i)
                    (by simp [addone_val]; omega)]
              congr 1; exact Subtype.ext (by simp [addone_val]; omega)
            rw [hpt]; exact hR
      · -- i > k+1: shifted repr
        have hξ : ξ' i = ξ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ :=
          (dif_neg h1).trans (dif_neg (by omega))
        have hb := hr_bounds ⟨i.val - 1, by have := i.property; have := k.property; omega⟩
        constructor
        · rw [hξ, Partition.insertPoint_pt_gt c Δ k hL hR (incl i)
              (by simp [incl_val]; omega)]
          exact hb.1
        · rw [hξ]
          have h_pt : Δ'.points (addone i) =
              Δ.points (addone ⟨i.val - 1,
              by have := i.property; have := k.property; omega⟩) := by
            rw [Partition.insertPoint_pt_gt c Δ k hL hR (addone i)
                (by simp [addone_val]; omega)]
            congr 1; exact Subtype.ext (by simp [addone_val]; omega)
          rw [h_pt]; exact hb.2
  case bound =>
    -- Key identity: RS' - RS = (f(c) - f(ξ(k))) * Δ.length(k)
    have hDiff : RiemannSum f Δ' ξ' - RiemannSum f Δ ξ =
        (f c - f (ξ k)) * Δ.length k := by
      rw [RiemannSum, RiemannSum]
      -- Collapsed n-term function matching the (n+1)-term RS'
      let fk : Range n → Real := fun i =>
        if i.val = k.val then f c * Partition.length Δ k
        else f (ξ i) * Partition.length Δ i
      -- Step 1: RS' sum collapses to Summation n fk
      have hRS' : Summation (n + 1) (fun i ↦ f (ξ' i) * Partition.length Δ' i) =
          Summation n fk := by
        apply summation_split_term n k
        · -- h_low: i < k
          intro i hi
          rw [show ξ' i = ξ ⟨i.val, by have := k.property; omega⟩ from dif_pos hi,
              Partition.insertPoint_length_low c Δ k hL hR i hi]
          show f (ξ ⟨i.val, _⟩) * Partition.length Δ ⟨i.val, _⟩ = fk ⟨i.val, _⟩
          show _ = if (⟨i.val, _⟩ : Range n).val = k.val then _ else _
          rw [if_neg (show i.val ≠ k.val from by omega)]
        · -- h_split: k and k+1
          have hξk : ξ' ⟨k.val, Nat.lt_succ_of_lt k.property⟩ = c := by
            show (if h : k.val < k.val then _ else if h₂ : k.val ≤ k.val + 1 then c else _) = c
            rw [dif_neg (by omega), dif_pos (by omega)]
          have hξk1 : ξ' ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ = c := by
            show (if h : k.val + 1 < k.val then _ else
              if h₂ : k.val + 1 ≤ k.val + 1 then c else _) = c
            rw [dif_neg (by omega), dif_pos (by omega)]
          rw [hξk, hξk1, ← CommRing.left_distrib,
              Partition.insertPoint_length_split c Δ k hL hR]
          show f c * Partition.length Δ k = fk k
          show _ = if k.val = k.val then _ else _
          rw [if_pos rfl]
        · -- h_high: i > k+1
          intro i hi
          rw [show ξ' i = ξ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ from
                (dif_neg (by omega)).trans (dif_neg (by omega)),
              Partition.insertPoint_length_high c Δ k hL hR i hi]
          show f (ξ ⟨i.val - 1, _⟩) * Partition.length Δ ⟨i.val - 1, _⟩ =
               fk ⟨i.val - 1, _⟩
          show _ = if (⟨i.val - 1, _⟩ : Range n).val = k.val then _ else _
          rw [if_neg (show i.val - 1 ≠ k.val from by omega)]
      -- Step 2: Summation n fk = RS + correction
      have heq : Summation n fk = Summation n (fun i ↦ f (ξ i) * Partition.length Δ i) +
          (f c - f (ξ k)) * Partition.length Δ k := by
        have hterm : ∀ i : Range n, fk i = f (ξ i) * Partition.length Δ i +
            (if i.val = k.val then (f c - f (ξ k)) * Partition.length Δ k
             else 0) := by
          intro i
          show (if i.val = k.val then f c * Partition.length Δ k
                else f (ξ i) * Partition.length Δ i) = _
          by_cases hi : i.val = k.val
          · rw [if_pos hi, if_pos hi]
            have hik : i = k := Subtype.ext hi; subst hik
            rw [← add_mul, add_sub_cancel']
          · rw [if_neg hi, if_neg hi, add_zero]
        rw [summation_congr n _ _ hterm, additive_summation,
            summation_one_term n k _ (fun i hne => if_neg hne)]
        rw [if_pos (show k.val = k.val from rfl)]
      -- Step 3: Conclude
      rw [hRS', heq, add_sub_cancel]
    rw [hDiff, abs_mul_nonneg (Δ.length_nonneg k)]
    apply nonneg_mul_nonneg _ _ _ (Δ.length_nonneg k)
    -- Goal: |f c - f (ξ k)| ≤ 2 * M
    have hc_in : InInterval a b c := by
      dsimp [InInterval]; rw [if_pos (Δ.left_le_right)]
      exact ⟨le_trans (Δ.left_le_point (incl k)) hL,
             le_trans hR (Δ.point_le_right (addone k))⟩
    have hfc : (f c).abs ≤ M := hM c hc_in
    have hfξ : (f (ξ k)).abs ≤ M := hM _ (Δ.repr_in_interval ξ hr k)
    apply le_trans (abs_triangle (f c) (-(f (ξ k))))
    rw [abs_neg]
    rw [show (2 : Real) * M = M + M from by
      rw [show (2 : Real) = 1 + 1 from rfl, add_mul, one_mul]]
    exact le_trans (LinearOrderedField.add_le_add _ _ _ hfc) (add_left_le _ _ _ hfξ)

-- m 点挿入で RS の差を制御
theorem rs_multi_insert_bound (f : Real → Real) {a b : Real} (M : Real)
    (hM : ∀ t, InInterval a b t → (f t).abs ≤ M) (hM_nn : 0 ≤ M)
    {n : Nat} (hn : 0 < n) (Δ : Partition n a b)
    (ξ : Range n → Real) (hr : Δ.IsRepr ξ) :
    ∀ (m : Nat) (cs : Range m → Real) (_hcs : ∀ j, InInterval a b (cs j)),
    ∃ (Δ' : Partition (n + m) a b) (ξ' : Range (n + m) → Real),
      Δ'.IsRepr ξ' ∧
      (∀ i : Range (n + m), Δ'.length i ≤ Δ.diam) ∧
      (∀ j : Range m, ∃ p : Range (n + m + 1), Δ'.points p = cs j) ∧
      (RiemannSum f Δ' ξ' - RiemannSum f Δ ξ).abs ≤
        Real.ofNat m * (2 * M * Δ.diam) := by
  intro m; induction m with
  | zero =>
    intro cs _hcs
    exact ⟨Δ, ξ, hr, fun i => le_fmax' n Δ.length i,
      fun j => absurd j.property (Nat.not_lt_zero _), by
      show (RiemannSum f Δ ξ - RiemannSum f Δ ξ).abs ≤
        0 * (2 * M * Partition.diam Δ)
      rw [sub_self, abs_zero, zero_mul']; exact le_refl 0⟩
  | succ m ih =>
    intro cs hcs
    -- First m points
    obtain ⟨Δ₁, ξ₁, hr₁, hlen₁, hpts₁, hbd₁⟩ :=
      ih (fun j => cs ⟨j.val, Nat.lt_succ_of_lt j.property⟩)
         (fun j => hcs ⟨j.val, Nat.lt_succ_of_lt j.property⟩)
    -- Insert (m+1)-th point
    let c := cs ⟨m, Nat.lt_succ_self m⟩
    have hc_in := hcs ⟨m, Nat.lt_succ_self m⟩
    obtain ⟨k, hkL, hkR⟩ := Partition.find_interval Δ₁ c (by omega) hc_in
    obtain ⟨ξ₂, hr₂, hbd₂⟩ := rs_insert_bound f c M hM hM_nn Δ₁ ξ₁ hr₁ k hkL hkR
    let Δ₂ := Δ₁.insertPoint c k hkL hkR
    refine ⟨Δ₂, ξ₂, hr₂, ?_, ?_, ?_⟩
    · -- ∀ i, Δ₂.length i ≤ Δ.diam
      intro i
      show Partition.length Δ₂ i ≤ Partition.diam Δ
      by_cases h1 : i.val < k.val
      · calc Partition.length Δ₂ i
              = Δ₁.length ⟨i.val, by have := k.property; omega⟩ :=
                Partition.insertPoint_length_low c Δ₁ k hkL hkR i h1
            _ ≤ Δ.diam := hlen₁ ⟨i.val, by have := k.property; omega⟩
      · by_cases h2 : k.val + 1 < i.val
        · calc Partition.length Δ₂ i
                = Δ₁.length ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ :=
                  Partition.insertPoint_length_high c Δ₁ k hkL hkR i h2
              _ ≤ Δ.diam := hlen₁ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩
        · -- Split intervals: i ∈ {k.val, k.val + 1}
          have hsplit := Partition.insertPoint_length_split c Δ₁ k hkL hkR
          by_cases h3 : i.val = k.val
          · have hi : i = ⟨k.val, Nat.lt_succ_of_lt k.property⟩ := Subtype.ext h3
            rw [hi]
            exact le_trans (le_of_add_nonneg_eq hsplit
              (Δ₂.length_nonneg ⟨k.val + 1, Nat.succ_lt_succ k.property⟩)) (hlen₁ k)
          · have h4 : i.val = k.val + 1 := by have := i.property; omega
            have hi : i = ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ := Subtype.ext h4
            rw [hi]
            exact le_trans (le_of_nonneg_add_eq hsplit
              (Δ₂.length_nonneg ⟨k.val, Nat.lt_succ_of_lt k.property⟩)) (hlen₁ k)
    · -- 挿入した点はすべて Δ₂ の分点
      intro j
      by_cases hjm : j.val = m
      · refine ⟨⟨k.val + 1, by have := k.property; omega⟩, ?_⟩
        rw [show j = ⟨m, Nat.lt_succ_self m⟩ from Subtype.ext hjm]
        exact Partition.insertPoint_pt_mid c Δ₁ k hkL hkR
      · have hjm' : j.val < m := by have := j.property; omega
        obtain ⟨p, hp⟩ := hpts₁ ⟨j.val, hjm'⟩
        have hcsj : cs ⟨j.val, Nat.lt_succ_of_lt hjm'⟩ = cs j := by
          congr 1
        rw [hcsj] at hp
        by_cases hpk : p.val ≤ k.val
        · refine ⟨⟨p.val, by have := p.property; omega⟩, ?_⟩
          exact (Partition.insertPoint_pt_le c Δ₁ k hkL hkR
            ⟨p.val, by have := p.property; omega⟩ hpk).trans hp
        · refine ⟨⟨p.val + 1, by have := p.property; omega⟩, ?_⟩
          exact (Partition.insertPoint_pt_gt c Δ₁ k hkL hkR
            ⟨p.val + 1, by have := p.property; omega⟩
            (show k.val + 1 < p.val + 1 by omega)).trans hp
    · -- |RS₂ - RS₀| ≤ ofNat (m+1) * (2M * diam)
      have h2M_nn : 0 ≤ 2 * M := mul_nonneg 2 M
        (le_trans zero_lt_one.1 (by calc (1 : Real) = 1 + 0 := (add_zero 1).symm
          _ ≤ 1 + 1 := add_left_le 1 0 1 zero_lt_one.1)) hM_nn
      have h_single : (RiemannSum f Δ₂ ξ₂ -
          RiemannSum f Δ₁ ξ₁).abs ≤ 2 * M * Δ.diam := by
        apply le_trans hbd₂
        rw [show 2 * M * Δ₁.length k = Δ₁.length k * (2 * M) from mul_comm _ _,
            show 2 * M * Δ.diam = Δ.diam * (2 * M) from mul_comm _ _]
        exact nonneg_mul_nonneg _ _ _ h2M_nn (hlen₁ k)
      -- Triangle: |RS₂ - RS₀| ≤ |RS₁ - RS₀| + |RS₂ - RS₁|
      let K := 2 * M * Δ.diam
      have hdecomp : RiemannSum f Δ₂ ξ₂ - RiemannSum f Δ ξ =
          (RiemannSum f Δ₁ ξ₁ - RiemannSum f Δ ξ) +
          (RiemannSum f Δ₂ ξ₂ - RiemannSum f Δ₁ ξ₁) :=
        telescope_2 (RiemannSum f Δ ξ) (RiemannSum f Δ₂ ξ₂)
          (RiemannSum f Δ₁ ξ₁)
      -- |RS₂ - RS₀| ≤ |RS₁ - RS₀| + |RS₂ - RS₁| ≤ m*K + K = (m+1)*K
      have hsum_le : (RiemannSum f Δ₁ ξ₁ - RiemannSum f Δ ξ).abs +
          (RiemannSum f Δ₂ ξ₂ - RiemannSum f Δ₁ ξ₁).abs ≤
          Real.ofNat (m + 1) * K := by
        have hstep : Real.ofNat m * K + K = Real.ofNat (m + 1) * K := by
          rw [succ_ofNat, add_mul, one_mul]
        rw [← hstep]
        exact le_trans (LinearOrderedField.add_le_add _ _ _ hbd₁) (add_left_le _ _ _ h_single)
      show (RiemannSum f Δ₂ ξ₂ - RiemannSum f Δ ξ).abs ≤
          Real.ofNat (m + 1) * (2 * M * Partition.diam Δ)
      rw [hdecomp]
      exact le_trans (abs_triangle _ _) hsum_le
