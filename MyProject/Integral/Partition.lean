import MyProject.Lemmas
import Init.Data.Nat.Basic

noncomputable section

open Real Classical Range

-- 分割を定義
structure Partition (n : Nat) (a b : Real) where
  points : Range n.succ → Real
  increase : ∀ i : Range n, points (incl i) ≤ points (addone i)
  left : points ⟨0, by simp⟩ = a
  right : points ⟨n, by simp⟩ = b

namespace Partition

theorem zero {a b : Real} (Δ : Partition 0 a b) : a = b := by
  have ha : Δ.points ⟨0, by simp⟩ = a := by rw [Δ.left]
  have hb : Δ.points ⟨0, by simp⟩ = b := by rw [Δ.right]
  rw [← ha, hb]

theorem zero_point {a b : Real} (Δ : Partition 0 a b) :
    Δ.points ⟨0, Nat.one_pos⟩ = a := Δ.left

theorem range_one (n : Nat) (hn : n = 0) (i : Range n.succ) : i = ⟨0, Nat.zero_lt_succ n⟩ := by
  rw [ext]
  simp
  have := i.property
  rw [Nat.lt_succ_iff] at this
  rw [← Nat.le_zero_eq]
  exact le_of_le_of_eq this hn

theorem left_le_point {n : Nat} {a b : Real} (Δ : Partition n a b) (i : Range n.succ) :
  a ≤ Δ.points i := by
  apply induction n.succ (fun i => a ≤ Δ.points i)
  intro x IH
  by_cases h : x = ⟨0, by simp⟩
  · rw [h, Δ.left]
    apply le_refl a
  · have h₀ : ¬x.val = 0 := fun h' => h (Subtype.ext_iff.2 h')
    let y : Range n := ⟨x.val.pred, Nat.pred_lt_pred h₀ x.property⟩
    calc
      a ≤ Δ.points y.incl := (IH y.incl (Nat.pred_lt h₀))
      _ ≤ Δ.points y.addone := Δ.increase y
      _ = Δ.points x := congrArg Δ.points (Subtype.ext_iff.2 (Nat.succ_pred_eq_of_ne_zero h₀))

theorem sub_lt_self (m n : Nat) (hm : 0 < m) (hn : 0 < n) : n - m < n := Nat.sub_lt hn hm

theorem left_le_right {n : Nat} {a b : Real} (Δ : Partition n a b) :
    a ≤ b := by
  rw [← Δ.right]
  exact Δ.left_le_point ⟨n, by simp⟩

theorem sub_add_eq_sub_sub (n m : Nat) (h : m ≤ n) (h' : 0 < m) : n - m + 1 = n - (m - 1) := by
  have h₀ : m - 1 < n := by exact Nat.sub_one_lt_of_le h' h
  have h₁ : 0 < n - (m - 1) := by exact Nat.zero_lt_sub_of_lt h₀
  rw [← Nat.succ_eq_add_one, ← Nat.succ_pred_eq_of_pos h₁, Nat.succ_inj']
  simp
  rw [Nat.sub_sub, ← Nat.pred_eq_sub_one, ← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos h']

theorem point_le_right {n : Nat} {a b : Real} (Δ : Partition n a b) (i : Range n.succ) :
  Δ.points i ≤ b := by
  by_cases hn : n = 0
  · rw [range_one n hn i, Δ.left]
    exact Δ.left_le_right
  · let P : Range n.succ → Prop := fun i => Δ.points ⟨n - i.val, Nat.sub_lt_succ n i.val⟩ ≤ b
    have hP : ∀ i, P i := by
      apply induction n.succ P
      intro x IH
      by_cases h : x = ⟨0, by simp⟩
      · rw [h]
        dsimp [P]
        rw [Δ.right]
        apply le_refl b
      · have h₀ : ¬x.val = 0 := fun h' => h (Subtype.ext_iff.2 h')
        let y : Range n := ⟨x.val.pred, Nat.pred_lt_pred h₀ x.property⟩
        have h₁ : n - x.val < n :=
          Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) (Nat.zero_lt_of_ne_zero h₀)
        have h₂ : n - x.val < n.succ :=
          Nat.sub_lt_succ n x.val
        have h₃ : n - y.val < n.succ :=
          Nat.sub_lt_succ n y.val
        calc
          Δ.points ⟨n - x.val, h₂⟩ ≤ Δ.points ⟨n - y.val, h₃⟩ := by
            have : incl ⟨n - x.val, h₁⟩ = ⟨n - x.val, h₂⟩ := rfl
            rw [← this]
            have : addone ⟨n - x.val, h₁⟩ = ⟨n - y.val, h₃⟩ := by
              simp [ext]
              exact sub_add_eq_sub_sub n x.val (Nat.lt_succ.1 x.property) (Nat.zero_lt_of_ne_zero h₀)
            rw [← this]
            apply Δ.increase
          _ ≤ b := IH y.incl (Nat.pred_lt h₀)
    let j : Range n.succ := ⟨n - i.val, Nat.sub_lt_succ n i.val⟩
    have : ⟨n - j.val, Nat.sub_lt_succ n j.val⟩ = i := by
      rw [ext]
      exact Nat.sub_sub_self (Nat.le_of_lt_succ i.property)
    rw [← this]
    exact hP j

-- 分点の単調性
theorem points_mono {n : Nat} {a b : Real} (Δ : Partition n a b)
    (i j : Range n.succ) (hij : i.val ≤ j.val) : Δ.points i ≤ Δ.points j := by
  obtain ⟨d, hd⟩ : ∃ d, j.val = i.val + d := ⟨j.val - i.val, by omega⟩
  clear hij
  revert j
  induction d with
  | zero =>
    intro j hd
    rw [show i = j from Subtype.ext (by omega)]
    exact le_refl _
  | succ d ih =>
    intro j hd
    have hd' : i.val + d < n := by have := j.property; omega
    have hstep := Δ.increase ⟨i.val + d, hd'⟩
    rw [show (addone (⟨i.val + d, hd'⟩ : Range n) : Range n.succ) = j from
          Subtype.ext (by simp only [addone_val]; omega)] at hstep
    refine le_trans ?_ hstep
    rw [show (incl (⟨i.val + d, hd'⟩ : Range n) : Range n.succ) =
          ⟨i.val + d, Nat.lt_succ_of_lt hd'⟩ from Subtype.ext (by simp only [incl_val])]
    exact ih ⟨i.val + d, Nat.lt_succ_of_lt hd'⟩ rfl

theorem points_in_interval {n : Nat} {a b : Real} (Δ : Partition n a b) (i : Range n.succ) :
    InInterval a b (Δ.points i) :=
  (in_interval_iff Δ.left_le_right).mpr ⟨Δ.left_le_point i, Δ.point_le_right i⟩

-- 代表点を定義
def IsRepr {n : Nat} {a b : Real} (Δ : Partition n a b)
  (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, InInterval (Δ.points i.incl) (Δ.points i.addone) (ξ i)

theorem le_isrepr {n : Nat} {a b : Real} (Δ : Partition n a b)
    (ξ : Range n → Real) (h : ∀ i, (Δ.points i.incl) ≤ ξ i ∧ ξ i ≤ (Δ.points i.addone)) :
    IsRepr Δ ξ :=
  fun i => (in_interval_iff (Δ.increase i)).mpr (h i)

-- 代表点の小区間内境界（IsRepr の展開）
theorem repr_bounds {n : Nat} {a b : Real} {Δ : Partition n a b} {ξ : Range n → Real}
    (h : IsRepr Δ ξ) (i : Range n) :
    Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i) :=
  in_interval_pair (Δ.increase i) (h i)

theorem repr_in_interval {n : Nat} {a b : Real} (Δ : Partition n a b)
  (ξ : Range n → Real) (h : IsRepr Δ ξ) :
    ∀ i : Range n, InInterval a b (ξ i) := by
  intro i
  have hb := repr_bounds h i
  exact (in_interval_iff Δ.left_le_right).mpr
    ⟨le_trans (Δ.left_le_point i.incl) hb.1,
     le_trans hb.2 (Δ.point_le_right i.addone)⟩

def length {n : Nat} {a b : Real} (Δ : Partition n a b) (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

theorem length_nonneg {n : Nat} {a b : Real} (Δ : Partition n a b) (i : Range n) :
  0 ≤ Δ.length i := by
  simp [length]
  rw [← nonneg_iff_le]
  exact Δ.increase i

theorem length_sum {n : Nat} {a b : Real} (Δ : Partition n a b) :
  Summation n Δ.length = b - a := by
  have : Summation n Δ.length = Summation n (fun i ↦ Δ.points (addone i) - Δ.points (incl i)) := by rfl
  rw [this, telescope_sum n (Δ.points)]
  simp [Δ.left, Δ.right]

def diam {n : Nat} {a b : Real} (Δ : Partition n a b) : Real :=
  fmax' n Δ.length

-- x ∈ [a,b] なら x を含む小区間が存在する
theorem find_interval {n : Nat} {a b : Real} (Δ : Partition n a b) (x : Real)
    (hn : 0 < n) (hx : InInterval a b x) :
    ∃ k : Range n, Δ.points (incl k) ≤ x ∧ x ≤ Δ.points (addone k) := by
  have hab := Δ.left_le_right
  have hxa : a ≤ x := (in_interval_pair hab hx).1
  have hxb : x ≤ b := (in_interval_pair hab hx).2
  -- p(i) := i < n ∧ x ≤ Δ.points ⟨i+1, ⟩
  let p : Nat → Prop := fun i =>
    ∃ h : i < n, x ≤ Δ.points ⟨i + 1, Nat.succ_lt_succ h⟩
  -- p(n-1) holds since x ≤ b = Δ.points ⟨n⟩
  have hp : ∃ i, p i := by
    have hn' : n - 1 < n := Nat.pred_lt (Nat.not_eq_zero_of_lt hn)
    have heq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    refine ⟨n - 1, hn', ?_⟩
    have : Δ.points ⟨n - 1 + 1, Nat.succ_lt_succ hn'⟩ = Δ.points ⟨n, by simp⟩ := by
      congr 1; exact Subtype.ext heq
    rw [this, Δ.right]; exact hxb
  -- 最小の k を取得
  rcases has_min p hp with ⟨k, ⟨hkn, hkle⟩, hmin⟩
  refine ⟨⟨k, hkn⟩, ?_, hkle⟩
  -- Δ.points (incl ⟨k, hkn⟩) ≤ x を示す
  -- incl ⟨k, hkn⟩ = ⟨k, Nat.lt_succ_of_lt hkn⟩
  show Δ.points ⟨k, Nat.lt_succ_of_lt hkn⟩ ≤ x
  cases Classical.em (k = 0) with
  | inl hk0 =>
    -- k = 0: Δ.points ⟨0, ⟩ = a ≤ x
    subst hk0; rw [Δ.left]; exact hxa
  | inr hk_ne =>
    -- k > 0: ¬p(k-1) なので x ≤ Δ.points ⟨k, ⟩ は偽
    have hk_pos : 0 < k := Nat.zero_lt_of_ne_zero hk_ne
    have not_pk : ¬ p (k - 1) := by
      intro hpk; exact hmin (k - 1) hpk (Nat.pred_lt hk_ne)
    -- ¬p(k-1): k-1 < n だが x ≤ Δ.points ⟨k, ⟩ が偽
    have hk_lt_ns : k < n.succ := Nat.lt_succ_of_lt hkn
    have hkm1_lt : k - 1 < n := Nat.lt_of_lt_of_le (Nat.pred_lt hk_ne) (Nat.le_of_lt hkn)
    have heq : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
    have : ¬ (x ≤ Δ.points ⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩) := by
      intro hle; exact not_pk ⟨hkm1_lt, hle⟩
    have : ¬ (x ≤ Δ.points ⟨k, hk_lt_ns⟩) := by
      rwa [show (⟨k - 1 + 1, Nat.succ_lt_succ hkm1_lt⟩ : Range n.succ) =
           ⟨k, hk_lt_ns⟩ from Subtype.ext heq] at this
    cases LinearOrderedField.le_total x (Δ.points ⟨k, hk_lt_ns⟩) with
    | inl hle => exact absurd hle this
    | inr hge => exact hge

-- 分割に点を挿入
def insertPoint {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    Partition (n + 1) a b where
  points := fun ⟨i, hi⟩ =>
    have hk : k.val < n := k.property
    if h₁ : i ≤ k.val then Δ.points ⟨i, by omega⟩
    else if h₂ : i = k.val + 1 then c
    else Δ.points ⟨i - 1, by omega⟩
  increase := by
    intro ⟨i, hi⟩
    have hk : k.val < n := k.property
    dsimp [incl, addone]
    by_cases h1 : i + 1 ≤ k.val
    · -- Case 1: both i and i+1 ≤ k.val
      rw [dif_pos (show i ≤ k.val from by omega), dif_pos h1]
      exact Δ.increase ⟨i, by omega⟩
    · by_cases h2 : i ≤ k.val
      · -- Case 2: i = k.val
        have hik : i = k.val := by omega
        subst hik
        rw [dif_pos h2, dif_neg h1, if_pos rfl]
        exact hL
      · by_cases h3 : i = k.val + 1
        · -- Case 3: i = k.val + 1
          subst h3
          rw [dif_neg h2, if_pos rfl,
              dif_neg h1, if_neg (show ¬(k.val + 1 + 1 = k.val + 1) from by omega)]
          exact hR
        · -- Case 4: i > k.val + 1
          rw [dif_neg h2, if_neg h3,
              dif_neg h1, if_neg (show ¬(i + 1 = k.val + 1) from by omega)]
          have h_incr := Δ.increase ⟨i - 1, by omega⟩
          have h_eq : (addone (⟨i - 1, by omega⟩ : Range n) : Range n.succ) =
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

-- insertPoint の点アクセス補題
theorem insertPoint_pt_le {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 2)) (hi : i.val ≤ k.val) :
    (Δ.insertPoint c k hL hR).points i =
    Δ.points ⟨i.val, by have := k.property; omega⟩ := by
  obtain ⟨i_val, i_prop⟩ := i
  simp only [insertPoint]
  exact dif_pos hi

theorem insertPoint_pt_mid {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    (Δ.insertPoint c k hL hR).points ⟨k.val + 1, by have := k.property; omega⟩ = c := by
  simp only [insertPoint]
  exact (dif_neg (show ¬(k.val + 1 ≤ k.val) from by omega)).trans (dif_pos trivial)

theorem insertPoint_pt_gt {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 2)) (hi : k.val + 1 < i.val) :
    (Δ.insertPoint c k hL hR).points i =
    Δ.points ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ := by
  obtain ⟨i_val, i_prop⟩ := i
  have hi' : k.val + 1 < i_val := hi
  simp only [insertPoint]
  exact (dif_neg (by omega)).trans (dif_neg (by omega))

-- insertPoint の length 補題
theorem insertPoint_length_low {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 1)) (hi : i.val < k.val) :
    (Δ.insertPoint c k hL hR).length i =
    Δ.length ⟨i.val, by have := k.property; omega⟩ := by
  simp only [length]
  rw [insertPoint_pt_le c Δ k hL hR (addone i) (by simp [addone_val]; omega),
      insertPoint_pt_le c Δ k hL hR (incl i) (by simp [incl_val]; omega)]
  congr 1

theorem insertPoint_length_split {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k)) :
    (Δ.insertPoint c k hL hR).length ⟨k.val, Nat.lt_succ_of_lt k.property⟩ +
    (Δ.insertPoint c k hL hR).length ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ =
    Δ.length k := by
  let Δ' := Δ.insertPoint c k hL hR
  have h1 : Δ'.points (addone ⟨k.val, Nat.lt_succ_of_lt k.property⟩) = c := by
    rw [show (addone ⟨k.val, Nat.lt_succ_of_lt k.property⟩ : Range (n + 2)) =
          ⟨k.val + 1, by have := k.property; omega⟩ from Subtype.ext (by simp [addone_val])]
    exact insertPoint_pt_mid c Δ k hL hR
  have h2 : Δ'.points (incl ⟨k.val, Nat.lt_succ_of_lt k.property⟩) = Δ.points (incl k) :=
    insertPoint_pt_le c Δ k hL hR _ (by simp [incl_val])
  have h3 : Δ'.points (addone ⟨k.val + 1, Nat.succ_lt_succ k.property⟩) = Δ.points (addone k) :=
    insertPoint_pt_gt c Δ k hL hR _ (by simp [addone_val])
  have h4 : Δ'.points (incl ⟨k.val + 1, Nat.succ_lt_succ k.property⟩) = c := by
    rw [show (incl ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ : Range (n + 2)) =
          ⟨k.val + 1, by have := k.property; omega⟩ from Subtype.ext (by simp [incl_val])]
    exact insertPoint_pt_mid c Δ k hL hR
  simp only [length]; rw [h1, h2, h3, h4]
  rw [← add_sub_add c (Δ.points (addone k)) (Δ.points (incl k)) c,
      show Δ.points (incl k) + c = c + Δ.points (incl k) from add_comm _ _]
  exact add_sub_add' c (Δ.points (addone k)) (Δ.points (incl k))

theorem insertPoint_length_high {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (i : Range (n + 1)) (hi : k.val + 1 < i.val) :
    (Δ.insertPoint c k hL hR).length i =
    Δ.length ⟨i.val - 1, by have := i.property; have := k.property; omega⟩ := by
  simp only [length]
  rw [insertPoint_pt_gt c Δ k hL hR (addone i) (by simp [addone_val]; omega),
      insertPoint_pt_gt c Δ k hL hR (incl i) (by simp [incl_val]; omega)]
  congr 1
  · congr 1; exact Subtype.ext (by simp [addone_val]; omega)

-- a < b なら分割は少なくとも 1 区間を持つ
theorem pos_of_lt {n : Nat} {a b : Real} (Δ : Partition n a b) (hab : a < b) : 0 < n := by
  cases n with
  | zero => exact absurd (Partition.zero Δ) hab.2
  | succ m => exact Nat.zero_lt_succ m

-- diam は非負（n ≥ 1）
theorem diam_nonneg {n : Nat} {a b : Real} (Δ : Partition n a b) (hn : 0 < n) :
    0 ≤ Δ.diam := le_trans (Δ.length_nonneg ⟨0, hn⟩) (le_fmax' n _ ⟨0, hn⟩)

-- 点挿入後の各小区間の長さは元の diam 以下
theorem insertPoint_length_le_diam {n : Nat} {a b : Real} (c : Real) (Δ : Partition n a b)
    (k : Range n) (hL : Δ.points (incl k) ≤ c) (hR : c ≤ Δ.points (addone k))
    (q : Range (n + 1)) : (Δ.insertPoint c k hL hR).length q ≤ Δ.diam := by
  by_cases h1 : q.val < k.val
  · rw [insertPoint_length_low c Δ k hL hR q h1]
    exact le_fmax' _ _ _
  · by_cases h2 : k.val + 1 < q.val
    · rw [insertPoint_length_high c Δ k hL hR q h2]
      exact le_fmax' _ _ _
    · have hsplit := insertPoint_length_split c Δ k hL hR
      by_cases h3 : q.val = k.val
      · rw [show q = ⟨k.val, Nat.lt_succ_of_lt k.property⟩ from Subtype.ext h3]
        exact le_trans (le_of_add_nonneg_eq hsplit
          ((Δ.insertPoint c k hL hR).length_nonneg ⟨k.val + 1, Nat.succ_lt_succ k.property⟩))
          (le_fmax' _ _ k)
      · have h4 : q.val = k.val + 1 := by have := q.property; have := k.property; omega
        rw [show q = ⟨k.val + 1, Nat.succ_lt_succ k.property⟩ from Subtype.ext h4]
        exact le_trans (le_of_nonneg_add_eq hsplit
          ((Δ.insertPoint c k hL hR).length_nonneg ⟨k.val, Nat.lt_succ_of_lt k.property⟩))
          (le_fmax' _ _ k)

end Partition

-- タグ付き分割：分割と代表点列（IsRepr）の組。
-- 積分の定義などで「∀ n Δ ξ, IsRepr → …」の 4 つ組を 1 変数に束ねる。
structure TaggedPartition (a b : Real) where
  n : Nat
  Δ : Partition n a b
  ξ : Range n → Real
  repr : Δ.IsRepr ξ
