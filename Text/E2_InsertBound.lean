-- Text/E2_InsertBound.lean — 発展部 §2: 点挿入によるリーマン和の変化の評価
-- NearLe（両側評価の述語——Ch11 の生の不等式がここで昇格）と
-- Σ の分割補題（one_term / split_term）、挿入の評価（2M は M+M で書く）
import Text.E1_Insert

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 有限和の分割補題（添字の組み替えのボス級）
-- ============================================================

-- 1 点でだけ非零の関数の和はその値
theorem summation_one_term (m : Nat) (k : Range m) (h : Range m → Real)
    (hzero : ∀ i : Range m, i.val ≠ k.val → h i = 0) :
    Summation m h = h k := by
  induction m with
  | zero => exact absurd k.property (Nat.not_lt_zero _)
  | succ n ih =>
    rw [summation_succ]
    by_cases hkn : k.val = n
    · -- k は最後の項: incl 側は全部 0
      have hall : ∀ i : Range n, h (incl i) = 0 := by
        intro i
        apply hzero
        show i.val ≠ k.val
        have := i.property
        omega
      rw [summation_congr n _ _ hall, summation_all_zero, zero_add']
      have hk : (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) = k := Subtype.ext hkn.symm
      rw [hk]
    · -- k.val < n: 最後の項が 0
      have hklt : k.val < n := by have := k.property; omega
      have hlast : h ⟨n, Nat.lt_succ_self n⟩ = 0 := by
        apply hzero
        show n ≠ k.val
        omega
      rw [hlast, add_zero]
      have h_ih := ih ⟨k.val, hklt⟩ (fun i => h (incl i)) (by
        intro i hne
        apply hzero (incl i)
        show i.val ≠ k.val
        exact hne)
      exact h_ih

-- k 番目の項を 2 つに分割しても和は変わらない（挿入の核になる組み替え）
theorem summation_split_term (n : Nat) (k : Range n) (f : Range n → Real)
    (g : Range (n + 1) → Real)
    (h_low : ∀ (i : Range (n + 1)) (hi : i.val < k.val),
      g i = f ⟨i.val, Nat.lt_trans hi k.property⟩)
    (h_split : g ⟨k.val, Nat.lt_succ_of_lt k.property⟩ +
      g ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ = f k)
    (h_high : ∀ (i : Range (n + 1)) (hi : k.val + 1 < i.val),
      g i = f ⟨i.val - 1, by have := i.property; omega⟩) :
    Summation (n + 1) g = Summation n f := by
  induction n with
  | zero => exact absurd k.property (Nat.not_lt_zero _)
  | succ n ih =>
    rw [summation_succ, summation_succ]
    by_cases hkn : k.val = n
    · -- k が最後の小区間: 末尾 2 項が分割対 (h_split)
      rw [summation_succ]
      have hcongr : ∀ i : Range n, g (incl (incl i)) = f (incl i) := by
        intro i
        have := i.property
        exact h_low (incl (incl i)) (by show i.val < k.val; omega)
      rw [summation_congr n _ _ hcongr, add_assoc]
      congr 1
      have e1 : (⟨k.val, Nat.lt_succ_of_lt k.property⟩ : Range (n + 2)) =
          incl (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) :=
        Subtype.ext hkn
      have e2 : (⟨k.val + 1, Nat.succ_lt_succ k.property⟩ : Range (n + 2)) =
          (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Range (n + 2)) :=
        Subtype.ext (by show k.val + 1 = n + 1; omega)
      have e3 : k = (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) := Subtype.ext hkn
      rw [e1, e2, e3] at h_split
      exact h_split
    · -- k.val < n: 末尾の項は両辺で一致、残りは帰納法
      have hklt : k.val < n := by have := k.property; omega
      have hlast : g ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ = f ⟨n, Nat.lt_succ_self n⟩ :=
        h_high ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ (by show k.val + 1 < n + 1; omega)
      rw [hlast]
      congr 1
      exact ih ⟨k.val, hklt⟩ (fun i => f (incl i)) (fun i => g (incl i))
        (fun i hi => h_low (incl i) hi)
        h_split
        (fun i hi => h_high (incl i) hi)

-- ============================================================
-- §2 NearLe: 両側評価の述語（abs の不等式バージョンの代替。
--    |y − x| ≤ c の代わりに x − c ≤ y ∧ y ≤ x + c）
-- ============================================================

-- ANCHOR: nearle
def NearLe (c x y : Real) : Prop := x - c ≤ y ∧ y ≤ x + c
-- ANCHOR_END: nearle

theorem nearle_zero (x : Real) : NearLe 0 x x := by
  constructor
  · show x + -(0 : Real) ≤ x
    rw [neg_zero, add_zero']
    exact le_refl x
  · show x ≤ x + (0 : Real)
    rw [add_zero']
    exact le_refl x

-- 三角不等式に相当する連結（abs_triangle の代替）
theorem nearle_trans {c₁ c₂ x y z : Real}
    (h₁ : NearLe c₁ x y) (h₂ : NearLe c₂ y z) : NearLe (c₁ + c₂) x z := by
  constructor
  · rw [sub_sub']
    exact le_trans (sub_le_sub_right h₁.1 c₂) h₂.1
  · rw [(add_assoc x c₁ c₂).symm]
    exact le_trans h₂.2 (add_le_add_right y (x + c₁) c₂ h₁.2)

-- 許容誤差は大きくしてよい
theorem nearle_mono {c c' x y : Real} (h : NearLe c x y) (hcc : c ≤ c') :
    NearLe c' x y := by
  constructor
  · exact le_trans (sub_le_sub_left hcc x) h.1
  · exact le_trans h.2 (add_left_le x c c' hcc)

-- 補正項 d の両側評価から x + d の NearLe へ
theorem nearle_of_add {x d c : Real} (hlo : -c ≤ d) (hhi : d ≤ c) :
    NearLe c x (x + d) := by
  constructor
  · exact add_left_le x (-c) d hlo
  · exact add_left_le x d c hhi

-- ============================================================
-- §3 1 点挿入によるリーマン和の変化: NearLe ((M+M)·len k) で評価
--    （|RS' − RS| ≤ 2M·len k の脱 abs 版。有界性も両側 hMlo / hMhi で持つ）
-- ============================================================

theorem rs_insert_bound (f : Real → Real) {u v : Real} (c M : Real)
    (hMlo : ∀ t, u ≤ t → t ≤ v → -M ≤ f t)
    (hMhi : ∀ t, u ≤ t → t ≤ v → f t ≤ M)
    {n : Nat} (Δ : Partition n u v) (ξ : Range n → Real) (hr : Δ.IsRepr ξ)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    ∃ ξ' : Range (n + 1) → Real,
      (Δ.insertPoint c k hL hR).IsRepr ξ' ∧
      NearLe ((M + M) * Δ.length k)
        (RiemannSum f Δ ξ) (RiemannSum f (Δ.insertPoint c k hL hR) ξ') := by
  -- タグ: 分割された 2 区間は c、他は元のタグをずらして使う
  let ξ' : Range (n + 1) → Real := fun i =>
    if h : i.val < k.val then ξ ⟨i.val, by have := k.property; omega⟩
    else if h₂ : i.val ≤ k.val + 1 then c
    else ξ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩
  -- (1) ξ' は挿入後の分割の代表点系
  have hrepr : (Δ.insertPoint c k hL hR).IsRepr ξ' := by
    intro i
    by_cases h1 : i.val < k.val
    · -- i < k: 分点もタグも元のまま
      have hξ : ξ' i = ξ ⟨i.val, by have := k.property; omega⟩ := dif_pos h1
      rw [hξ,
          Partition.insertPoint_pt_le c Δ k hL hR (incl i) (by show i.val ≤ k.val; omega),
          Partition.insertPoint_pt_le c Δ k hL hR (addone i) (by show i.val + 1 ≤ k.val; omega)]
      exact hr ⟨i.val, by have := k.property; omega⟩
    · by_cases h2 : i.val ≤ k.val + 1
      · -- i ∈ {k, k+1}: タグは c
        have hξ : ξ' i = c := (dif_neg h1).trans (dif_pos h2)
        rw [hξ]
        by_cases h3 : i.val = k.val
        · -- 区間 [pts (incl k), c]
          constructor
          · have hpt : (Δ.insertPoint c k hL hR).points (incl i) = Δ.points (incl k) := by
              rw [Partition.insertPoint_pt_le c Δ k hL hR (incl i) (by show i.val ≤ k.val; omega)]
              congr 1
              exact Subtype.ext (show i.val = k.val from h3)
            rw [hpt]
            exact hL
          · have he : addone i = (⟨k.val + 1, by have := k.property; omega⟩ : Range (n + 2)) :=
              Subtype.ext (show i.val + 1 = k.val + 1 from by omega)
            rw [he, Partition.insertPoint_pt_mid]
            exact le_refl c
        · -- 区間 [c, pts (addone k)]
          have h4 : i.val = k.val + 1 := by omega
          constructor
          · have he : incl i = (⟨k.val + 1, by have := k.property; omega⟩ : Range (n + 2)) :=
              Subtype.ext (show i.val = k.val + 1 from h4)
            rw [he, Partition.insertPoint_pt_mid]
            exact le_refl c
          · have hpt : (Δ.insertPoint c k hL hR).points (addone i) = Δ.points (addone k) := by
              rw [Partition.insertPoint_pt_gt c Δ k hL hR (addone i)
                    (by show k.val + 1 < i.val + 1; omega)]
              congr 1
              exact Subtype.ext (by show i.val + 1 - 1 = k.val + 1; omega)
            rw [hpt]
            exact hR
      · -- i > k+1: 1 つずれた元のタグ
        have hξ : ξ' i = ξ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ :=
          (dif_neg h1).trans (dif_neg (by omega))
        have hb := hr ⟨i.val - 1, by have := i.property; have := k.property; omega⟩
        constructor
        · rw [hξ, Partition.insertPoint_pt_gt c Δ k hL hR (incl i)
                (by show k.val + 1 < i.val; omega)]
          exact hb.1
        · rw [hξ]
          have hpt : (Δ.insertPoint c k hL hR).points (addone i) =
              Δ.points (addone ⟨i.val - 1, by have := i.property; have := k.property; omega⟩) := by
            rw [Partition.insertPoint_pt_gt c Δ k hL hR (addone i)
                  (by show k.val + 1 < i.val + 1; omega)]
            congr 1
            exact Subtype.ext (by show i.val + 1 - 1 = i.val - 1 + 1; omega)
          rw [hpt]
          exact hb.2
  -- (2) 核となる等式: RS' − RS = (f c − f (ξ k)) · len k
  have hDiff : RiemannSum f (Δ.insertPoint c k hL hR) ξ' - RiemannSum f Δ ξ =
      (f c - f (ξ k)) * Δ.length k := by
    show Summation (n + 1) (fun i => f (ξ' i) * (Δ.insertPoint c k hL hR).length i)
        - Summation n (fun i => f (ξ i) * Δ.length i)
        = (f c - f (ξ k)) * Δ.length k
    -- k 番目だけ f c に置き換えた n 項関数
    let fk : Range n → Real := fun i =>
      if i.val = k.val then f c * Δ.length k
      else f (ξ i) * Δ.length i
    -- Step 1: (n+1) 項の RS' は fk の n 項和に潰れる（summation_split_term）
    have hRS' : Summation (n + 1) (fun i => f (ξ' i) * (Δ.insertPoint c k hL hR).length i)
        = Summation n fk := by
      apply summation_split_term n k
      · -- i < k
        intro i hi
        show f (ξ' i) * (Δ.insertPoint c k hL hR).length i
            = fk ⟨i.val, Nat.lt_trans hi k.property⟩
        rw [show ξ' i = ξ ⟨i.val, by have := k.property; omega⟩ from dif_pos hi,
            Partition.insertPoint_length_low c Δ k hL hR i hi]
        show _ = if (⟨i.val, Nat.lt_trans hi k.property⟩ : Range n).val = k.val
            then _ else _
        rw [if_neg (show i.val ≠ k.val from by omega)]
      · -- k と k+1: タグは c、長さは split で合算
        have hξk : ξ' ⟨k.val, Nat.lt_succ_of_lt k.property⟩ = c := by
          show (if h : k.val < k.val then _ else if h₂ : k.val ≤ k.val + 1 then c else _) = c
          rw [dif_neg (by omega), dif_pos (by omega)]
        have hξk1 : ξ' ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ = c := by
          show (if h : k.val + 1 < k.val then _ else
            if h₂ : k.val + 1 ≤ k.val + 1 then c else _) = c
          rw [dif_neg (by omega), dif_pos (by omega)]
        show f (ξ' ⟨k.val, Nat.lt_succ_of_lt k.property⟩)
              * (Δ.insertPoint c k hL hR).length ⟨k.val, Nat.lt_succ_of_lt k.property⟩
            + f (ξ' ⟨k.val + 1, Nat.succ_lt_succ k.property⟩)
              * (Δ.insertPoint c k hL hR).length ⟨k.val + 1, Nat.succ_lt_succ k.property⟩
            = fk k
        rw [hξk, hξk1, ← CommRing.left_distrib,
            Partition.insertPoint_length_split c Δ k hL hR]
        show _ = if k.val = k.val then _ else _
        rw [if_pos rfl]
      · -- i > k+1
        intro i hi
        show f (ξ' i) * (Δ.insertPoint c k hL hR).length i = fk ⟨i.val - 1, _⟩
        rw [show ξ' i = ξ ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ from
              (dif_neg (by omega)).trans (dif_neg (by omega)),
            Partition.insertPoint_length_high c Δ k hL hR i hi]
        show _ = if (⟨i.val - 1, _⟩ : Range n).val = k.val then _ else _
        rw [if_neg (show i.val - 1 ≠ k.val from by omega)]
    -- Step 2: fk の和 = 元の和 + 補正項
    have heq : Summation n fk
        = Summation n (fun i => f (ξ i) * Δ.length i) + (f c - f (ξ k)) * Δ.length k := by
      have hterm : ∀ i : Range n, fk i = f (ξ i) * Δ.length i +
          (if i.val = k.val then (f c - f (ξ k)) * Δ.length k else 0) := by
        intro i
        show (if i.val = k.val then f c * Δ.length k else f (ξ i) * Δ.length i) = _
        by_cases hi : i.val = k.val
        · rw [if_pos hi, if_pos hi]
          have hik : i = k := Subtype.ext hi
          subst hik
          rw [← CommRing.right_distrib, add_sub_cancel']
        · rw [if_neg hi, if_neg hi, add_zero]
      rw [summation_congr n _ _ hterm, additive_summation,
          summation_one_term n k _ (fun i hne => if_neg hne)]
      rw [if_pos (show k.val = k.val from rfl)]
    -- Step 3: 結論
    rw [hRS', heq, add_sub_cancel]
  -- (3) 補正項 d = (f c − f (ξ k)) · len k の両側評価
  have hc_u : u ≤ c :=
    calc u = Δ.points ⟨0, Nat.succ_pos n⟩ := Δ.left.symm
      _ ≤ Δ.points (incl k) :=
          points_mono Δ ⟨0, Nat.succ_pos n⟩ k.val
            (Nat.lt_succ_of_lt k.property) (Nat.zero_le _)
      _ ≤ c := hL
  have hc_v : c ≤ v :=
    calc c ≤ Δ.points (addone k) := hR
      _ ≤ Δ.points ⟨n, Nat.lt_succ_self n⟩ :=
          points_mono Δ (addone k) n (Nat.lt_succ_self n) k.property
      _ = v := Δ.right
  have hξmem := tag_mem' Δ ξ hr k
  have hd_hi : f c - f (ξ k) ≤ M + M := by
    have h1 : -(f (ξ k)) ≤ M := by
      have h2 := neg_le_neg' (hMlo _ hξmem.1 hξmem.2)
      rwa [neg_neg] at h2
    exact add_le_add' (hMhi c hc_u hc_v) h1
  have hd_lo : -(M + M) ≤ f c - f (ξ k) := by
    have h1 : -M ≤ -(f (ξ k)) := neg_le_neg' (hMhi _ hξmem.1 hξmem.2)
    have h2 := add_le_add' (hMlo c hc_u hc_v) h1
    rwa [← neg_add_distrib] at h2
  have hlen := length_nonneg Δ k
  have hd_hi' : (f c - f (ξ k)) * Δ.length k ≤ (M + M) * Δ.length k :=
    nonneg_mul_nonneg _ _ _ hlen hd_hi
  have hd_lo' : -((M + M) * Δ.length k) ≤ (f c - f (ξ k)) * Δ.length k := by
    have h1 : (-(M + M)) * Δ.length k ≤ (f c - f (ξ k)) * Δ.length k :=
      nonneg_mul_nonneg _ _ _ hlen hd_lo
    rwa [neg_mul] at h1
  -- (4) 仕上げ: RS' = RS + d に書き直して両側評価を適用
  have hsum : RiemannSum f (Δ.insertPoint c k hL hR) ξ'
      = RiemannSum f Δ ξ + (f c - f (ξ k)) * Δ.length k := by
    rw [← hDiff]
    exact (add_sub_cancel' _ _).symm
  refine ⟨ξ', hrepr, ?_⟩
  rw [hsum]
  exact nearle_of_add hd_lo' hd_hi'

-- ============================================================
-- §4 m 点挿入: 細かさは ∀-Fine 形のまま保たれ、RS の変化は
--    m · ((M+M)·δ) で制御される
-- ============================================================

theorem rs_multi_insert_bound (f : Real → Real) {u v : Real} (M : Real)
    (hMlo : ∀ t, u ≤ t → t ≤ v → -M ≤ f t)
    (hMhi : ∀ t, u ≤ t → t ≤ v → f t ≤ M)
    (hM_nn : 0 ≤ M)
    {n : Nat} (hn : 0 < n) (Δ : Partition n u v) (ξ : Range n → Real) (hr : Δ.IsRepr ξ)
    {δ : Real} (hfine : ∀ i, Δ.length i < δ) :
    ∀ (m : Nat) (cs : Range m → Real), (∀ j, u ≤ cs j ∧ cs j ≤ v) →
    ∃ (Δ' : Partition (n + m) u v) (ξ' : Range (n + m) → Real),
      Δ'.IsRepr ξ' ∧
      (∀ i, Δ'.length i < δ) ∧
      (∀ j : Range m, ∃ p : Range (n + m + 1), Δ'.points p = cs j) ∧
      NearLe (Real.ofNat m * ((M + M) * δ))
        (RiemannSum f Δ ξ) (RiemannSum f Δ' ξ') := by
  intro m
  induction m with
  | zero =>
    intro cs _hcs
    refine ⟨Δ, ξ, hr, hfine, fun j => absurd j.property (Nat.not_lt_zero _), ?_⟩
    have h0 : Real.ofNat 0 * ((M + M) * δ) = 0 := zero_mul' _
    rw [h0]
    exact nearle_zero _
  | succ m ih =>
    intro cs hcs
    -- 最初の m 点を挿入
    obtain ⟨Δ₁, ξ₁, hr₁, hfine₁, hpts₁, hbd₁⟩ :=
      ih (fun j => cs ⟨j.val, Nat.lt_succ_of_lt j.property⟩)
         (fun j => hcs ⟨j.val, Nat.lt_succ_of_lt j.property⟩)
    -- m+1 番目の点 c を挿入
    have hc := hcs ⟨m, Nat.lt_succ_self m⟩
    obtain ⟨k, hkL, hkR⟩ := Partition.find_interval Δ₁ (cs ⟨m, Nat.lt_succ_self m⟩)
      (by omega) hc.1 hc.2
    obtain ⟨ξ₂, hr₂, hbd₂⟩ := rs_insert_bound f (cs ⟨m, Nat.lt_succ_self m⟩) M hMlo hMhi
      Δ₁ ξ₁ hr₁ k hkL hkR
    refine ⟨Δ₁.insertPoint (cs ⟨m, Nat.lt_succ_self m⟩) k hkL hkR, ξ₂, hr₂, ?_, ?_, ?_⟩
    · -- 細かさは ∀ 形のまま保たれる（B1 の insertPoint_fine）
      exact Partition.insertPoint_fine _ Δ₁ k hkL hkR hfine₁
    · -- 挿入した点はすべて分点
      intro j
      by_cases hjm : j.val = m
      · refine ⟨⟨k.val + 1, by have := k.property; omega⟩, ?_⟩
        have he : cs j = cs ⟨m, Nat.lt_succ_self m⟩ := congrArg cs (Subtype.ext hjm)
        rw [he]
        exact Partition.insertPoint_pt_mid _ Δ₁ k hkL hkR
      · have hjm' : j.val < m := by have := j.property; omega
        obtain ⟨p, hp⟩ := hpts₁ ⟨j.val, hjm'⟩
        have hcsj : cs ⟨j.val, Nat.lt_succ_of_lt hjm'⟩ = cs j :=
          congrArg cs (Subtype.ext rfl)
        rw [hcsj] at hp
        by_cases hpk : p.val ≤ k.val
        · exact ⟨⟨p.val, by have := p.property; omega⟩,
            (Partition.insertPoint_pt_le _ Δ₁ k hkL hkR
              ⟨p.val, by have := p.property; omega⟩ hpk).trans hp⟩
        · exact ⟨⟨p.val + 1, by have := p.property; omega⟩,
            (Partition.insertPoint_pt_gt _ Δ₁ k hkL hkR
              ⟨p.val + 1, by have := p.property; omega⟩
              (by show k.val + 1 < p.val + 1; omega)).trans hp⟩
    · -- 評価の合算: m·C + C = (m+1)·C（C = (M+M)·δ）
      have h2M_nn : 0 ≤ M + M := by
        have h1 := add_le_add' hM_nn hM_nn
        rwa [zero_add'] at h1
      have hstep : NearLe ((M + M) * δ) (RiemannSum f Δ₁ ξ₁)
          (RiemannSum f (Δ₁.insertPoint (cs ⟨m, Nat.lt_succ_self m⟩) k hkL hkR) ξ₂) := by
        apply nearle_mono hbd₂
        rw [mul_comm (M + M) (Partition.length Δ₁ k), mul_comm (M + M) δ]
        exact nonneg_mul_nonneg _ _ _ h2M_nn (le_of_lt (hfine₁ k))
      have hcomb := nearle_trans hbd₁ hstep
      have hC : Real.ofNat m * ((M + M) * δ) + (M + M) * δ
          = Real.ofNat (m + 1) * ((M + M) * δ) := by
        rw [succ_ofNat, CommRing.right_distrib (Real.ofNat m) 1 ((M + M) * δ), one_mul]
      rw [← hC]
      exact hcomb
