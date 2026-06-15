-- Text/E1_Insert.lean — 発展部「存在定理への登山」§1: 分割への点の挿入と小区間の探索
-- （∀-Fine 形。find_interval は Ch11 の探索 has_min の実戦）
-- 発展部は本編（C15_FTC）の後に置かれ、主線の import 連鎖からは独立
import Text.C17_FTC

noncomputable section

open Classical
open Range

namespace Partition

-- u ≤ x ≤ v なら x を含む小区間が存在する（最小添字の探索 = has_min の応用）
theorem find_interval {n : Nat} {u v : Real} (Δ : Partition n u v) (x : Real)
    (hn : 0 < n) (hxa : u ≤ x) (hxb : x ≤ v) :
    ∃ k : Range n, Δ.points (incl k) ≤ x ∧ x ≤ Δ.points (addone k) := by
  let p : Nat → Prop := fun i =>
    ∃ h : i < n, x ≤ Δ.points ⟨i + 1, Nat.succ_lt_succ h⟩
  have hp : ∃ i, p i := by
    have hn' : n - 1 < n := by omega
    have heq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    refine ⟨n - 1, hn', ?_⟩
    have hpt : Δ.points ⟨n - 1 + 1, Nat.succ_lt_succ hn'⟩
        = Δ.points ⟨n, Nat.lt_succ_self n⟩ := by
      congr 1; exact Subtype.ext heq
    rw [hpt, Δ.right]; exact hxb
  rcases has_min p hp with ⟨k, ⟨hkn, hkle⟩, hmin⟩
  refine ⟨⟨k, hkn⟩, ?_, hkle⟩
  show Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ ≤ x
  cases Classical.em (k = 0) with
  | inl hk0 =>
    subst hk0; rw [Δ.left]; exact hxa
  | inr hk_ne =>
    have hk_pos : 0 < k := Nat.zero_lt_of_ne_zero hk_ne
    have not_pk : ¬ p (k - 1) := by
      intro hpk; exact hmin (k - 1) hpk (Nat.pred_lt hk_ne)
    have hk_lt_ns : k < n + 1 := Nat.lt_succ_of_lt hkn
    have hkm1_lt : k - 1 < n := by omega
    have heq : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
    have h1 : ¬ (x ≤ Δ.points ⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩) := by
      intro hle; exact not_pk ⟨hkm1_lt, hle⟩
    have h2 : ¬ (x ≤ Δ.points ⟨k, hk_lt_ns⟩) := by
      rwa [show (⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩ : Range (n + 1)) =
           ⟨k, hk_lt_ns⟩ from Subtype.ext heq] at h1
    cases le_total x (Δ.points ⟨k, hk_lt_ns⟩) with
    | inl hle => exact absurd hle h2
    | inr hge => exact hge

-- 分割に点 c を挿入する
def insertPoint {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    Partition (n + 1) u v where
  points := fun ⟨i, hi⟩ =>
    have hk : k.val < n := k.property
    if h₁ : i ≤ k.val then Δ.points ⟨i, by omega⟩
    else if h₂ : i = k.val + 1 then c
    else Δ.points ⟨i - 1, by omega⟩
  increase := by
    intro ⟨i, hi⟩
    have hk : k.val < n := k.property
    dsimp [Range.incl, Range.addone]
    by_cases h1 : i + 1 ≤ k.val
    · rw [dif_pos (show i ≤ k.val from by omega), dif_pos h1]
      exact Δ.increase ⟨i, by omega⟩
    · by_cases h2 : i ≤ k.val
      · have hik : i = k.val := by omega
        subst hik
        rw [dif_pos h2, dif_neg h1, if_pos rfl]
        exact hL
      · by_cases h3 : i = k.val + 1
        · subst h3
          rw [dif_neg h2, if_pos rfl,
              dif_neg h1, if_neg (show ¬(k.val + 1 + 1 = k.val + 1) from by omega)]
          exact hR
        · rw [dif_neg h2, if_neg h3,
              dif_neg h1, if_neg (show ¬(i + 1 = k.val + 1) from by omega)]
          have h_incr := Δ.increase ⟨i - 1, by omega⟩
          have h_eq : (addone (⟨i - 1, by omega⟩ : Range n) : Range (n + 1)) =
                      ⟨i, by omega⟩ := Subtype.ext (show (i - 1) + 1 = i from by omega)
          rw [h_eq] at h_incr
          exact h_incr
  left := by
    dsimp only []
    rw [dif_pos (Nat.zero_le k.val)]
    exact Δ.left
  right := by
    have hk : k.val < n := k.property
    dsimp only []
    rw [dif_neg (show ¬(n + 1 ≤ k.val) from by omega),
        dif_neg (show ¬(n + 1 = k.val + 1) from by omega)]
    exact Δ.right

-- 点アクセス補題
theorem insertPoint_pt_le {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 2)) (hi : i.val ≤ k.val) :
    (Δ.insertPoint c k hL hR).points i =
    Δ.points ⟨i.val, by have := k.property; omega⟩ := by
  obtain ⟨i_val, i_prop⟩ := i
  simp only [insertPoint]
  exact dif_pos hi

theorem insertPoint_pt_mid {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    (Δ.insertPoint c k hL hR).points ⟨k.val + 1, by have := k.property; omega⟩ = c := by
  simp only [insertPoint]
  exact (dif_neg (show ¬(k.val + 1 ≤ k.val) from by omega)).trans (dif_pos trivial)

theorem insertPoint_pt_gt {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 2)) (hi : k.val + 1 < i.val) :
    (Δ.insertPoint c k hL hR).points i =
    Δ.points ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ := by
  obtain ⟨i_val, i_prop⟩ := i
  have hi' : k.val + 1 < i_val := hi
  simp only [insertPoint]
  exact (dif_neg (by omega)).trans (dif_neg (by omega))

-- length 補題
theorem insertPoint_length_low {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 1)) (hi : i.val < k.val) :
    (Δ.insertPoint c k hL hR).length i =
    Δ.length ⟨i.val, by have := k.property; omega⟩ := by
  simp only [length]
  rw [insertPoint_pt_le c Δ k hL hR (addone i) (show i.val + 1 ≤ k.val from by omega),
      insertPoint_pt_le c Δ k hL hR (incl i) (show i.val ≤ k.val from by omega)]
  congr 1

theorem insertPoint_length_split {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    (Δ.insertPoint c k hL hR).length ⟨k.val, Nat.lt_succ_of_lt k.property⟩ +
    (Δ.insertPoint c k hL hR).length ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ =
    Δ.length k := by
  have h1 : (Δ.insertPoint c k hL hR).points
      (addone ⟨k.val, Nat.lt_succ_of_lt k.property⟩) = c := by
    rw [show (addone ⟨k.val, Nat.lt_succ_of_lt k.property⟩ : Range (n + 2)) =
          ⟨k.val + 1, by have := k.property; omega⟩ from rfl]
    exact insertPoint_pt_mid c Δ k hL hR
  have h2 : (Δ.insertPoint c k hL hR).points
      (incl ⟨k.val, Nat.lt_succ_of_lt k.property⟩) = Δ.points (incl k) :=
    insertPoint_pt_le c Δ k hL hR _ (show k.val ≤ k.val from Nat.le_refl _)
  have h3 : (Δ.insertPoint c k hL hR).points
      (addone ⟨k.val + 1, Nat.succ_lt_succ k.property⟩) = Δ.points (addone k) :=
    insertPoint_pt_gt c Δ k hL hR _ (show k.val + 1 < k.val + 1 + 1 from by omega)
  have h4 : (Δ.insertPoint c k hL hR).points
      (incl ⟨k.val + 1, Nat.succ_lt_succ k.property⟩) = c := by
    rw [show (incl ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ : Range (n + 2)) =
          ⟨k.val + 1, by have := k.property; omega⟩ from rfl]
    exact insertPoint_pt_mid c Δ k hL hR
  simp only [length]; rw [h1, h2, h3, h4]
  rw [← add_sub_add c (Δ.points (addone k)) (Δ.points (incl k)) c,
      show Δ.points (incl k) + c = c + Δ.points (incl k) from add_comm _ _]
  exact add_sub_add' c (Δ.points (addone k)) (Δ.points (incl k))

theorem insertPoint_length_high {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 1)) (hi : k.val + 1 < i.val) :
    (Δ.insertPoint c k hL hR).length i =
    Δ.length ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ := by
  simp only [length]
  rw [insertPoint_pt_gt c Δ k hL hR (addone i) (show k.val + 1 < i.val + 1 from by omega),
      insertPoint_pt_gt c Δ k hL hR (incl i) (show k.val + 1 < i.val from hi)]
  congr 1
  · congr 1; exact Subtype.ext (show i.val + 1 - 1 = i.val - 1 + 1 from by omega)

-- ∀-Fine 形: 細かい分割に点を挿しても細かいまま（diam を使わない）
theorem insertPoint_fine {n : Nat} {u v : Real} (c : Real) (Δ : Partition n u v)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    {δ : Real} (hf : ∀ i, Δ.length i < δ) :
    ∀ q, (Δ.insertPoint c k hL hR).length q < δ := by
  intro q
  by_cases h1 : q.val < k.val
  · rw [insertPoint_length_low c Δ k hL hR q h1]
    exact hf _
  · by_cases h2 : k.val + 1 < q.val
    · rw [insertPoint_length_high c Δ k hL hR q h2]
      exact hf _
    · have hsplit := insertPoint_length_split c Δ k hL hR
      by_cases h3 : q.val = k.val
      · rw [show q = ⟨k.val, Nat.lt_succ_of_lt k.property⟩ from Subtype.ext h3]
        exact le_lt_trans (le_of_add_nonneg_eq hsplit
          (length_nonneg _ ⟨k.val + 1, Nat.succ_lt_succ k.property⟩)) (hf k)
      · have h4 : q.val = k.val + 1 := by have := q.property; have := k.property; omega
        rw [show q = ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ from Subtype.ext h4]
        exact le_lt_trans (le_of_nonneg_add_eq hsplit
          (length_nonneg _ ⟨k.val, Nat.lt_succ_of_lt k.property⟩)) (hf k)

end Partition
