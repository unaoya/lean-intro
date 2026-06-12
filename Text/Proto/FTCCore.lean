-- Text/Proto/FTCCore.lean — M4: ftc_core の証明
-- 部品: Σ の比較・望遠鏡和・定数積分・IsIntegral レベルの両側評価・分点の単調性
import Text.Proto.Unique
import Text.Proto.FTC

noncomputable section

open Range

-- ============================================================
-- Summation の比較と望遠鏡和（Ch7 コーパスの先行試作）
-- ============================================================

theorem summation_le : ∀ (n : Nat) (f g : Range n → Real),
    (∀ i, f i ≤ g i) → Summation n f ≤ Summation n g := by
  intro n
  induction n with
  | zero => intro f g _; exact le_refl 0
  | succ m ih =>
    intro f g h
    exact add_le_add' (ih _ _ (fun k => h (Range.incl k))) (h ⟨m, Nat.lt_succ_self m⟩)

theorem summation_mul_left : ∀ (n : Nat) (f : Range n → Real) (c : Real),
    Summation n (fun i => c * f i) = c * Summation n f := by
  intro n
  induction n with
  | zero => intro f c; exact (mul_zero' c).symm
  | succ m ih =>
    intro f c
    show Summation m (fun k => c * f (Range.incl k)) + c * f ⟨m, Nat.lt_succ_self m⟩
        = c * (Summation m (fun k => f (Range.incl k)) + f ⟨m, Nat.lt_succ_self m⟩)
    rw [ih (fun k => f (Range.incl k)) c, CommRing.left_distrib]

theorem summation_telescope : ∀ (n : Nat) (g : Range (n + 1) → Real),
    Summation n (fun i => g (Range.addone i) - g (Range.incl i))
      = g ⟨n, Nat.lt_succ_self n⟩ - g ⟨0, Nat.succ_pos n⟩ := by
  intro n
  induction n with
  | zero => intro g; exact (sub_self _).symm
  | succ m ih =>
    intro g
    show Summation m (fun k =>
          g (Range.addone (Range.incl k)) - g (Range.incl (Range.incl k)))
        + (g (Range.addone ⟨m, Nat.lt_succ_self m⟩)
            - g (Range.incl ⟨m, Nat.lt_succ_self m⟩)) = _
    have h := ih (fun j => g (Range.incl j))
    rw [show (fun k : Range m =>
          g (Range.addone (Range.incl k)) - g (Range.incl (Range.incl k)))
        = (fun k : Range m =>
          g (Range.incl (Range.addone k)) - g (Range.incl (Range.incl k))) from rfl]
    rw [h]
    exact (telescope_2 (g ⟨0, Nat.succ_pos (m + 1)⟩)
      (g ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) (g ⟨m, Nat.lt_succ_of_lt (Nat.lt_succ_self m)⟩)).symm

-- ============================================================
-- 分割の補題（長さの非負性・分点の単調性・タグの所属・長さの総和）
-- ============================================================

theorem length_nonneg {n : Nat} {u v : Real} (Δ : Partition n u v) (i : Range n) :
    0 ≤ Δ.length i :=
  (nonneg_iff_le _ _).mp (Δ.increase i)

theorem points_mono {n : Nat} {u v : Real} (Δ : Partition n u v) (k : Range (n + 1)) :
    ∀ (lv : Nat) (hl : lv < n + 1), k.val ≤ lv → Δ.points k ≤ Δ.points ⟨lv, hl⟩ := by
  intro lv
  induction lv with
  | zero =>
    intro hl hk
    have hke : k = ⟨0, hl⟩ := Subtype.ext (Nat.le_zero.mp hk)
    rw [hke]; exact le_refl _
  | succ m ih =>
    intro hl hk
    rcases Nat.lt_or_ge k.val (m + 1) with hlt | hge
    · have hm : m < n + 1 := Nat.lt_of_succ_lt hl
      have hmn : m < n := Nat.lt_of_succ_lt_succ hl
      exact le_trans (ih hm (Nat.le_of_lt_succ hlt)) (Δ.increase ⟨m, hmn⟩)
    · have hke : k = ⟨m + 1, hl⟩ := Subtype.ext (Nat.le_antisymm hk hge)
      rw [hke]; exact le_refl _

theorem tag_mem {u v : Real} (P : TaggedPartition u v) (i : Range P.n) :
    u ≤ P.ξ i ∧ P.ξ i ≤ v := by
  have h1 : P.Δ.points ⟨0, Nat.succ_pos P.n⟩ ≤ P.Δ.points (Range.incl i) :=
    points_mono P.Δ ⟨0, Nat.succ_pos P.n⟩ i.val
      (Nat.lt_succ_of_lt i.property) (Nat.zero_le _)
  have h2 : P.Δ.points (Range.addone i) ≤ P.Δ.points ⟨P.n, Nat.lt_succ_self P.n⟩ :=
    points_mono P.Δ (Range.addone i) P.n (Nat.lt_succ_self P.n) i.property
  constructor
  · calc u = P.Δ.points ⟨0, Nat.succ_pos P.n⟩ := P.Δ.left.symm
      _ ≤ P.Δ.points (Range.incl i) := h1
      _ ≤ P.ξ i := (P.repr i).1
  · calc P.ξ i ≤ P.Δ.points (Range.addone i) := (P.repr i).2
      _ ≤ P.Δ.points ⟨P.n, Nat.lt_succ_self P.n⟩ := h2
      _ = v := P.Δ.right

theorem length_sum {n : Nat} {u v : Real} (Δ : Partition n u v) :
    Summation n (fun i => Δ.length i) = v - u := by
  show Summation n (fun i => Δ.points (Range.addone i) - Δ.points (Range.incl i)) = v - u
  rw [summation_telescope n Δ.points, Δ.right, Δ.left]

-- ============================================================
-- 定数関数のリーマン和と積分
-- ============================================================

theorem const_sum {u v : Real} (P : TaggedPartition u v) (c : Real) :
    P.sum (fun _ => c) = c * (v - u) := by
  show Summation P.n (fun i => c * P.Δ.length i) = c * (v - u)
  rw [summation_mul_left P.n (fun i => P.Δ.length i) c, length_sum P.Δ]

theorem sub_lt_swap {a b c : Real} (h : a - b < c) : a - c < b := by
  have h1 := lt_add_of_sub_lt h
  have h2 := add_lt_add_right a (c + b) (-c) h1
  rwa [show c + b + -c = b from by
    rw [add_comm c b, add_assoc, add_neg', add_zero']] at h2

theorem near_self {z ε : Real} (hε : 0 < ε) : Near ε z z := by
  constructor
  · have hneg : -ε < (0 : Real) := by
      have h := neg_lt_neg hε; rwa [neg_zero] at h
    have h := add_left_lt z (-ε) 0 hneg
    rwa [add_zero'] at h
  · have h := add_left_lt z 0 ε hε
    rwa [add_zero'] at h

theorem const_isintegral (c u v : Real) :
    IsIntegral (fun _ => c) u v (c * (v - u)) := by
  intro ε hε
  refine ⟨1, zero_lt_one, fun P _ => ?_⟩
  rw [const_sum P c]
  exact near_self hε

-- ============================================================
-- IsIntegral レベルの両側評価（脱 abs の単調性）
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
  have h2 : P.sum f ≤ c * (v - u) := by
    rw [← const_sum P c]
    show Summation P.n (fun i => f (P.ξ i) * P.Δ.length i)
        ≤ Summation P.n (fun i => c * P.Δ.length i)
    apply summation_le
    intro i
    obtain ⟨hu, hv⟩ := tag_mem P i
    exact nonneg_mul_nonneg _ _ _ (length_nonneg P.Δ i) (hb _ hu hv)
  exact lt_le_trans _ _ _ h1 (add_le_add_right _ _ ε h2)

theorem le_isintegral_of_le {f : Real → Real} {u v J c : Real} (huv : u ≤ v)
    (hJ : IsIntegral f u v J) (hb : ∀ t, u ≤ t → t ≤ v → c ≤ f t) :
    c * (v - u) ≤ J := by
  apply le_of_forall_lt_add
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hJ ε hε
  obtain ⟨P, hP⟩ := exists_fine_partition u v δ huv hδ
  have hnear := H P hP
  have h1 : c * (v - u) ≤ P.sum f := by
    rw [← const_sum P c]
    show Summation P.n (fun i => c * P.Δ.length i)
        ≤ Summation P.n (fun i => f (P.ξ i) * P.Δ.length i)
    apply summation_le
    intro i
    obtain ⟨hu, hv⟩ := tag_mem P i
    exact nonneg_mul_nonneg _ _ _ (length_nonneg P.Δ i) (hb _ hu hv)
  exact le_lt_trans h1 hnear.2

-- ============================================================
-- ftc_core: 連続なら、跨ぎ形の差分商が f(x) に収束する
-- 必要なのは: 連続性@x・定数積分・両側評価。存在定理も加法性も一意性も不要
-- ============================================================

theorem ftc_core (f : Real → Real) (a b x : Real) (hax : a ≤ x) (hxb : x ≤ b)
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

#print axioms ftc_core
