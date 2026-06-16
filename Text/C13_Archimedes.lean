-- Text/C13_Archimedes.lean — Ch13 アルキメデスと探索
-- 第 II 部の開幕: (1) sup（Skolem 化済み——choice 不要）(2) 探索 has_min（choice 不要・
-- ただし noncomputable）(3) 分岐 Classical.em（古典論理の入口）。
-- sup 公理はここで初稼働し、archimedean（白眉①）が出る。素朴定義実験もここ。
import Text.C12_Example

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 古典論理の入口（第 I 部に置けなかった補題——監査で確認できる）
-- ============================================================

-- < が ≤ ∧ ≠ で定義されているため、二重否定除去相当が必要
theorem not_lt_imp_le {a b : Real} (h : ¬(a < b)) : b ≤ a := by
  cases le_total a b with
  | inr h' => exact h'
  | inl hab =>
    have heq : a = b := Classical.byContradiction (fun hne => h ⟨hab, hne⟩)
    exact heq ▸ le_refl a

theorem not_le_imp_lt {a b : Real} (h : ¬ a ≤ b) : b < a := by
  have hba : b ≤ a := not_lt_imp_le (fun hlt => h (le_of_lt hlt))
  refine ⟨hba, fun he => ?_⟩
  apply h
  rw [he]
  exact le_refl a

-- ============================================================
-- §2 上限の近似（sup 公理の初稼働）
-- ============================================================

theorem sup_near (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ B, ∀ x, S x → x ≤ B)
    (γ : Real) (hγ : 0 < γ) : ∃ x, S x ∧ Real.sup S hne hbdd - γ < x := by
  cases Classical.em (∃ x, S x ∧ Real.sup S hne hbdd - γ < x) with
  | inl hex => exact hex
  | inr hnex =>
    exfalso
    have hub : ∀ x, S x → x ≤ Real.sup S hne hbdd - γ := fun x hx =>
      (Classical.em (Real.sup S hne hbdd - γ < x)).elim
        (fun hlt => absurd ⟨x, hx, hlt⟩ hnex) not_lt_imp_le
    have hle := Real.sup_lub S hne hbdd _ hub
    have h1 := add_le_add_right (Real.sup S hne hbdd)
      (Real.sup S hne hbdd - γ) (-(Real.sup S hne hbdd)) hle
    rw [AddCommGroup.add_neg] at h1
    rw [show Real.sup S hne hbdd - γ + -(Real.sup S hne hbdd) = -γ from by
          show Real.sup S hne hbdd + -γ + -(Real.sup S hne hbdd) = -γ
          rw [add_comm (Real.sup S hne hbdd) (-γ),
              add_assoc, AddCommGroup.add_neg, AddCommMonoid.add_zero]] at h1
    have h2 : γ ≤ 0 :=
      calc γ = 0 + γ := (AddCommMonoid.zero_add γ).symm
        _ ≤ -γ + γ := add_le_add_right 0 (-γ) γ h1
        _ = 0 := AddCommGroup.neg_add γ
    exact hγ.2 (le_antisymm 0 γ hγ.1 h2)

-- ============================================================
-- §3 白眉①: アルキメデス（上限公理から導かれるため公理ではなく定理）
-- ============================================================

-- ANCHOR: archimedean
theorem archimedean (a : Real) : ∃ n : Nat, a < (n : Real) := by
  cases Classical.em (∃ n : Nat, a < (n : Real)) with
  | inl h => exact h
  | inr h =>
    exfalso
    have hub : ∀ n : Nat, (n : Real) ≤ a := fun n =>
      not_lt_imp_le (fun hlt => h ⟨n, hlt⟩)
    have hS_ne : ∃ x : Real, ∃ n : Nat, x = (n : Real) := ⟨(0 : Real), 0, rfl⟩
    have hS_bdd : ∃ M, ∀ x : Real, (∃ n : Nat, x = (n : Real)) → x ≤ M :=
      ⟨a, fun x hx => by obtain ⟨n, rfl⟩ := hx; exact hub n⟩
    obtain ⟨x, hxS, hgt⟩ := sup_near _ hS_ne hS_bdd 1 zero_lt_one
    obtain ⟨n, rfl⟩ := hxS
    have h1 : Real.sup _ hS_ne hS_bdd < (1 : Real) + (n : Real) := by
      have h2 := add_left_lt 1 (Real.sup _ hS_ne hS_bdd - 1) (n : Real) hgt
      rwa [add_sub_cancel' 1 (Real.sup _ hS_ne hS_bdd)] at h2
    have h3 : (1 : Real) + (n : Real) = ((n + 1 : Nat) : Real) := by
      rw [add_comm]; exact (succ_ofNat n).symm
    have h4 : ((n + 1 : Nat) : Real) ≤ Real.sup _ hS_ne hS_bdd :=
      Real.sup_ub _ hS_ne hS_bdd _ ⟨n + 1, rfl⟩
    rw [h3] at h1
    exact (lt_le_trans _ _ _ h1 h4).2 rfl
-- ANCHOR_END: archimedean

-- ============================================================
-- §4 探索: Nat 述語の最小値・natMin・ceil
-- ============================================================

theorem has_min (p : Nat → Prop) (hp : ∃ n, p n) :
    ∃ a, p a ∧ ∀ x, p x → ¬(x < a) := by
  rcases hp with ⟨a, ha⟩
  revert ha
  induction a using Nat.strongRecOn with
  | ind n IH =>
    intro hn
    by_cases h' : ∃ m, m < n ∧ p m
    · rcases h' with ⟨m, hm, hpm⟩
      exact IH m hm hpm
    · exact ⟨n, hn, fun x hpx hxn => h' ⟨x, hxn, hpx⟩⟩

noncomputable def natMin (p : Nat → Prop) (hp : ∃ n, p n) : Nat :=
  Classical.choose (has_min p hp)

noncomputable def ceil (a : Real) : Nat := natMin (fun n => a < (n : Real)) (archimedean a)

theorem ceil_lt (a : Real) : a < ((ceil a : Nat) : Real) :=
  (Classical.choose_spec (has_min (fun n => a < (n : Real)) (archimedean a))).1

theorem nat_ne_zero_of_nonneg_lt (x : Real) (m : Nat) (hx : 0 ≤ x)
    (hlt : x < (m : Real)) : m ≠ 0 := by
  intro hm; subst hm; exact (le_lt_trans hx hlt).2 rfl

-- ============================================================
-- §5 アルキメデスが細かい分割を製造する（第 II 部全体の燃料）
-- ============================================================

-- 等分割の細かさ（∀ 形——diam を使わない）
theorem equalPartition_fine (m : Nat) (a b δ : Real) (hm : m ≠ 0) (hab : a ≤ b)
    (hδ : 0 < δ) (hlt : (b - a) / δ < (m : Real)) :
    ∀ i : Range m, (equalPartition m a b hm hab).length i < δ := by
  intro i
  rw [equalPartition_length m a b hm hab i]
  have hm_pos : 0 < ((m : Nat) : Real) := cast_pos_of_ne m hm
  have h1 : (b - a) / δ * δ < (m : Real) * δ := mul_right_lt _ _ δ hδ hlt
  rw [div_mul_cancel _ _ (ne_of_gt hδ)] at h1
  have h2 : (b - a) / (m : Real) < ((m : Real) * δ) / (m : Real) :=
    div_right_lt _ _ _ hm_pos h1
  rwa [mul_div_cancel' _ _ (ne_of_gt hm_pos)] at h2

-- 任意の細かさの等分割の存在（raw 版。TaggedPartition に束ねた版は Ch15）
theorem exists_fine_equalPartition (a b δ : Real) (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ m, ∃ hm : m ≠ 0,
      ∀ i : Range m, (equalPartition m a b hm hab).length i < δ := by
  have hba_nn : 0 ≤ b - a := (nonneg_iff_le a b).mp hab
  have hba_div_nn : 0 ≤ (b - a) / δ := nonneg_div_nonneg (b - a) δ hba_nn hδ
  have hm_lt : (b - a) / δ < ((ceil ((b - a) / δ) : Nat) : Real) := ceil_lt _
  have hm_ne : ceil ((b - a) / δ) ≠ 0 :=
    nat_ne_zero_of_nonneg_lt _ _ hba_div_nn hm_lt
  exact ⟨ceil ((b - a) / δ), hm_ne,
    equalPartition_fine _ a b δ hm_ne hab hδ hm_lt⟩

-- ============================================================
-- §6 素朴定義実験: max / min を if で書くと choice が監査に現れる
--    （Ch13 の両側評価が abs の言い換えだった種明かし。
--      rmin は発展部の細分機械が証明装置として実際に使う）
-- ============================================================

-- ANCHOR: naive_max
noncomputable def rmax (a b : Real) : Real := if a ≤ b then b else a
noncomputable def rmin (a b : Real) : Real := if a ≤ b then a else b
-- ANCHOR_END: naive_max

theorem rmin_eq_left {a b : Real} (h : a ≤ b) : rmin a b = a := if_pos h

theorem rmin_eq_right {a b : Real} (h : b ≤ a) : rmin a b = b := by
  show (if a ≤ b then a else b) = b
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    exact le_antisymm a b hab h
  · rw [if_neg hab]

-- 監査: rmax の定義だけで Classical.choice（propDecidable）が入る
#print axioms rmax
-- 監査: sup 公理 3 本がここで初登場する
#print axioms archimedean
#print axioms exists_fine_equalPartition
