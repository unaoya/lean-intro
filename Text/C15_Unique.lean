-- Text/C15_Unique.lean — Ch15 一意性（ε/2 ＋ ネットの非空性 = アルキメデスの値段）
-- min-free 合流（le_total の場合分け＋fine_mono）・橋 = choose の仕様書・橋の応用
import Text.C14_Integral

noncomputable section

open Classical

-- 細かさの単調性（min を使わない合流の部品）
theorem fine_mono {a b : Real} {P : TaggedPartition a b} {δ δ' : Real}
    (h : P.Fine δ) (hle : δ ≤ δ') : P.Fine δ' :=
  fun i => lt_le_trans _ _ _ (h i) hle

-- (∀ ε > 0, x < c + ε) → x ≤ c（古典的: x = c か否かの場合分け）
theorem le_of_forall_lt_add {x c : Real} (h : ∀ ε, 0 < ε → x < c + ε) : x ≤ c := by
  cases le_total x c with
  | inl h' => exact h'
  | inr h' =>
    cases Classical.em (x = c) with
    | inl he => exact he ▸ le_refl x
    | inr hne =>
      exfalso
      have hcx : c < x := lt_of_le_of_ne h' (fun e => hne e.symm)
      have hp : 0 < x - c := sub_pos_of_lt hcx
      have hx := h (x - c) hp
      rw [add_sub_cancel' c x] at hx
      exact hx.2 rfl

-- ============================================================
-- 一意性。中身は「ε/2 論法」＋「細かい分割の存在」（後者がアルキメデスの値段）
-- ============================================================

-- ANCHOR: integral_unique
theorem integral_unique (f : Real → Real) (a b i j : Real) (hab : a ≤ b)
    (hi : IsIntegral f a b i) (hj : IsIntegral f a b j) : i = j := by
  -- 任意の ε で i < j + ε かつ j < i + ε を示す
  have key : ∀ ε, 0 < ε → i < j + ε ∧ j < i + ε := by
    intro ε hε
    have hh : 0 < ε / (1 + 1) := pos_half ε hε
    rcases hi _ hh with ⟨δi, hδi, Hi⟩
    rcases hj _ hh with ⟨δj, hδj, Hj⟩
    -- min を使わない合流: 小さい方の δ で細かい分割を取り、fine_mono で両方に効かせる
    have hP : ∃ P : TaggedPartition a b, P.Fine δi ∧ P.Fine δj := by
      cases le_total δi δj with
      | inl hle =>
        obtain ⟨P, hP⟩ := exists_fine_partition a b δi hab hδi
        exact ⟨P, hP, fine_mono hP hle⟩
      | inr hle =>
        obtain ⟨P, hP⟩ := exists_fine_partition a b δj hab hδj
        exact ⟨P, fine_mono hP hle, hP⟩
    obtain ⟨P, hPi, hPj⟩ := hP
    have hni : Near (ε / (1 + 1)) i (P.sum f) := Hi P hPi
    have hnj : Near (ε / (1 + 1)) j (P.sum f) := Hj P hPj
    constructor
    · -- i < j + ε : i − h < RS < j + h なので i < j + (h + h) = j + ε
      have h1 : i < P.sum f + ε / (1 + 1) := lt_add_of_sub_lt hni.1
      have h2 : P.sum f + ε / (1 + 1) < (j + ε / (1 + 1)) + ε / (1 + 1) :=
        add_lt_add_right _ _ _ hnj.2
      have h3 := lt_trans _ _ _ h1 h2
      rwa [add_assoc, half_add] at h3
    · have h1 : j < P.sum f + ε / (1 + 1) := lt_add_of_sub_lt hnj.1
      have h2 : P.sum f + ε / (1 + 1) < (i + ε / (1 + 1)) + ε / (1 + 1) :=
        add_lt_add_right _ _ _ hni.2
      have h3 := lt_trans _ _ _ h1 h2
      rwa [add_assoc, half_add] at h3
  exact le_antisymm i j
    (le_of_forall_lt_add (fun ε hε => (key ε hε).1))
    (le_of_forall_lt_add (fun ε hε => (key ε hε).2))
-- ANCHOR_END: integral_unique

-- ============================================================
-- 橋: choose が拾った値はあなたの導出した値に等しい（choose の仕様書）
-- ============================================================

-- ANCHOR: bridge
theorem integral_eq_of_isIntegral (f : Real → Real) (a b i : Real)
    (hab : a ≤ b) (hi : IsIntegral f a b i) : Integral f a b = i := by
  have hint : a ≤ b ∧ IsIntegrable f a b := ⟨hab, ⟨i, hi⟩⟩
  show (if h : a ≤ b ∧ IsIntegrable f a b then Classical.choose h.2 else 0) = i
  rw [dif_pos hint]
  exact integral_unique f a b _ i hab (Classical.choose_spec hint.2) hi
-- ANCHOR_END: bridge

-- ============================================================
-- 橋の応用: 値の等式たち（const を 1 本導出して見せる。
-- 線形性・単調性等の持ち上げは発展演習——主線（FTC）はこれらを使わない）
-- ============================================================

theorem const_isintegral (c u v : Real) :
    IsIntegral (fun _ => c) u v (c * (v - u)) := by
  intro ε hε
  refine ⟨1, zero_lt_one, fun P _ => ?_⟩
  rw [const_sum P c]
  exact near_self hε

theorem integral_const (c u v : Real) (huv : u ≤ v) :
    Integral (fun _ => c) u v = c * (v - u) :=
  integral_eq_of_isIntegral _ u v _ huv (const_isintegral c u v)

#print axioms integral_unique
#print axioms integral_eq_of_isIntegral
#print axioms integral_const
