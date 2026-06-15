-- Text/C09_Order.lean — Ch9 順序と calc（≤/< のスカラー代数）
-- 順序の補題コーパス（公理の取り出し→加法と順序→移項→乗法順序）を獲得し、
-- ≤/< 混在の calc（Trans インスタンス）まで設計する。
-- 等式コーパスは Ch6/7・自動化は Ch8（順序の等式変形に使える）・帰納法は Ch10。
-- 注意: この章まで古典論理ゼロ（not_lt_imp_le 等の古典補題は第 II 部）。
import Text.C08_Automation

-- ============================================================
-- 順序の基本（クラスの公理の取り出しと推移律の変種）
-- ============================================================

theorem le_refl (a : Real) : a ≤ a := LinearOrderedField.le_refl a
theorem le_trans {a b c : Real} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  LinearOrderedField.le_trans a b c h₁ h₂
theorem le_antisymm (a b : Real) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  LinearOrderedField.le_antisymm a b h₁ h₂
theorem le_total (a b : Real) : a ≤ b ∨ b ≤ a := LinearOrderedField.le_total a b
theorem add_le_add_right (a b c : Real) (h : a ≤ b) : a + c ≤ b + c :=
  LinearOrderedField.add_le_add a b c h

theorem lt_trans (a b c : Real) : a < b → b < c → a < c := by
  intro ⟨hab, _⟩ ⟨hbc, hne_bc⟩
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne_bc (le_antisymm b c hbc (heq ▸ hab))⟩

theorem lt_le_trans (a b c : Real) : a < b → b ≤ c → a < c := by
  intro ⟨hab, hne⟩ hbc
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne (le_antisymm a b hab (heq ▸ hbc))⟩

theorem le_lt_trans {a b c : Real} : a ≤ b → b < c → a < c := by
  intro hab ⟨hbc, hne⟩
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne (le_antisymm b c hbc (heq ▸ hab))⟩

-- calc 用の Trans インスタンス（≤/< 混在の calc はこの機構で動く——種明かしの素材）
instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le :=
  ⟨fun h₁ h₂ => le_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt :=
  ⟨fun h₁ h₂ => lt_le_trans _ _ _ h₁ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => le_lt_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => lt_trans _ _ _ h₁ h₂⟩
instance : Trans (Eq : Real → Real → Prop) LE.le LE.le := ⟨fun h₁ h₂ => h₁ ▸ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) Eq LE.le := ⟨fun h₁ h₂ => h₂ ▸ h₁⟩

-- ============================================================
-- 加法と順序
-- ============================================================

theorem add_left_le (a b c : Real) : b ≤ c → a + b ≤ a + c := by
  intro h
  have h1 := add_le_add_right b c a h
  rw [add_comm b a, add_comm c a] at h1; exact h1

theorem add_left_lt (a b c : Real) : b < c → a + b < a + c := by
  intro ⟨hle, hne⟩
  exact ⟨add_left_le a b c hle, fun h => hne (add_left_cancel' a b c h)⟩

theorem add_lt_add_right (a b c : Real) : a < b → a + c < b + c := by
  intro h
  rw [add_comm a c, add_comm b c]
  exact add_left_lt c a b h

theorem add_le_add' {a b c d : Real} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right a b c h₁) (add_left_le b c d h₂)

theorem nonneg_iff_le (a b : Real) : a ≤ b ↔ 0 ≤ b - a := by
  constructor
  · intro h
    have h1 := add_le_add_right a b (-a) h
    rw [add_neg'] at h1; exact h1
  · intro h
    have h1 := add_le_add_right (0 : Real) (b + -a) a h
    rw [zero_add'] at h1
    rw [show b + -a + a = b from by
      calc b + -a + a = b + (-a + a) := add_assoc _ _ _
        _ = b + 0 := by rw [neg_add']
        _ = b := add_zero' _] at h1
    exact h1

theorem neg_neg_nonneg (a : Real) : a ≤ 0 → 0 ≤ -a := by
  intro h
  have h1 := add_le_add_right a (0 : Real) (-a) h
  rw [add_neg', zero_add'] at h1; exact h1

theorem sub_pos_of_lt {a b : Real} (h : a < b) : 0 < b - a := by
  refine ⟨(nonneg_iff_le a b).mp h.1, fun heq => h.2 ?_⟩
  have h' : a + (b - a) = a + 0 := by rw [← heq]
  rw [add_sub_cancel', add_zero'] at h'
  exact h'.symm

theorem neg_le_neg' {a b : Real} (h : a ≤ b) : -b ≤ -a := by
  have h1 := add_le_add_right a b (-a + -b) h
  rw [show a + (-a + -b) = -b from by
      rw [← add_assoc, add_neg', zero_add'],
    show b + (-a + -b) = -a from by
      rw [add_comm (-a) (-b), ← add_assoc, add_neg', zero_add']] at h1
  exact h1

theorem neg_lt_neg {a b : Real} (h : a < b) : -b < -a :=
  ⟨neg_le_neg' h.1, fun e => h.2 (by
    have e2 := congrArg (fun z => -z) e
    simp only [] at e2
    rw [show -(-b) = b from neg_neg b, show -(-a) = a from neg_neg a] at e2
    exact e2.symm)⟩

theorem sub_le_sub_right {a b : Real} (h : a ≤ b) (c : Real) : a - c ≤ b - c :=
  add_le_add_right a b (-c) h

theorem sub_le_sub_left {a b : Real} (h : a ≤ b) (c : Real) : c - b ≤ c - a :=
  add_left_le c (-b) (-a) (neg_le_neg' h)

theorem sub_lt_sub_left {a b : Real} (h : a < b) (c : Real) : c - b < c - a :=
  add_left_lt c (-b) (-a) (neg_lt_neg h)

-- ============================================================
-- 移項の小物（両側評価の組み立てに繰り返し使う）
-- ============================================================

theorem lt_add_of_sub_lt {a b c : Real} (h : a - b < c) : a < c + b := by
  have h1 := add_lt_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

theorem sub_lt_swap {a b c : Real} (h : a - b < c) : a - c < b := by
  have h1 := lt_add_of_sub_lt h
  have h2 := add_lt_add_right a (c + b) (-c) h1
  rwa [show c + b + -c = b from by
    rw [add_comm c b, add_assoc, add_neg', add_zero']] at h2

theorem sub_lt_of_lt_add {a b c : Real} (h : a < b + c) : a - b < c := by
  have h1 := add_lt_add_right a (b + c) (-b) h
  have h2 : (b + c) + -b = c := by
    rw [add_comm b c, add_assoc, add_neg', add_zero']
  rwa [h2] at h1

theorem sub_lt_self (z : Real) {h : Real} (hh : 0 < h) : z - h < z := by
  have hneg : -h < (0 : Real) := by
    have := neg_lt_neg hh; rwa [neg_zero] at this
  have := add_left_lt z (-h) 0 hneg
  rwa [add_zero'] at this

theorem le_add_of_sub_le {a b c : Real} (h : a - b ≤ c) : a ≤ c + b := by
  have h1 := add_le_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

theorem le_of_add_nonneg_eq {a b c : Real} (h : a + b = c) (hb : 0 ≤ b) : a ≤ c := by
  have h1 := add_left_le a 0 b hb
  rw [add_zero'] at h1
  exact h ▸ h1

theorem le_of_nonneg_add_eq {a b c : Real} (h : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  have h1 := add_le_add_right 0 a b ha
  rw [zero_add'] at h1
  exact h ▸ h1

theorem lt_add_pos (a b : Real) (hb : 0 < b) : a < a + b := by
  have h := add_left_lt a 0 b hb
  rwa [add_zero'] at h

theorem le_add_nonneg (a b : Real) (hb : 0 ≤ b) : a ≤ a + b := by
  have h := add_left_le a 0 b hb
  rwa [add_zero'] at h

-- ============================================================
-- 乗法の順序（0 < 1 は公理からの定理——nontrivial の出番）
-- ============================================================

theorem mul_nonneg (a b : Real) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b :=
  LinearOrderedField.mul_nonneg a b h h'

theorem nonmul_neg_le (a b c : Real) (hc : 0 ≤ c) (hab : 0 ≤ b - a) :
    0 ≤ b * c - a * c := by
  rw [show b * c - a * c = b * c + -(a * c) from rfl,
      show -(a * c) = (-a) * c from (neg_mul a c).symm,
      show b * c + (-a) * c = (b + -a) * c from (CommRing.right_distrib b (-a) c).symm]
  exact mul_nonneg (b + -a) c hab hc

theorem nonneg_mul_nonneg (a b c : Real) (h : 0 ≤ c) : a ≤ b → a * c ≤ b * c := by
  intro hab; rw [nonneg_iff_le] at hab ⊢
  exact nonmul_neg_le a b c h hab

theorem mul_right_lt (a b c : Real) : 0 < c → a < b → a * c < b * c := by
  intro ⟨hc, hnc⟩ ⟨hab, hne⟩
  constructor
  · exact nonneg_mul_nonneg a b c hc hab
  · intro heq; apply hne
    have hcne : c ≠ (0 : Real) := hnc.symm
    calc a = a * c * Field.inv c := by
          rw [mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]
      _ = b * c * Field.inv c := by rw [heq]
      _ = b := by rw [mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]

theorem zero_lt_one : (0 : Real) < 1 := by
  cases le_total (0 : Real) 1 with
  | inl h => exact ⟨h, fun heq => Field.nontrivial heq⟩
  | inr h =>
    have h0 : (0 : Real) ≤ -1 := neg_neg_nonneg 1 h
    have h1 : (0 : Real) ≤ (-1) * (-1) := mul_nonneg (-1) (-1) h0 h0
    have h2 : (-1 : Real) * (-1) = 1 := by
      calc (-1 : Real) * (-1) = -(1 * (-1)) := neg_mul 1 (-1)
        _ = -(-(1 * 1)) := by rw [mul_neg]
        _ = 1 * 1 := neg_neg _
        _ = 1 := one_mul_b 1
    rw [h2] at h1
    exact absurd (le_antisymm (0 : Real) (1 : Real) h1 h) Field.nontrivial

-- リテラル 2 はまだ無い: 1 + 1 で書く（リテラル機構は Ch8）
theorem zero_lt_one_one : (0 : Real) < 1 + 1 := by
  have h1 := add_left_lt 1 0 1 zero_lt_one
  rw [add_zero'] at h1
  exact lt_trans 0 1 (1 + 1) zero_lt_one h1

theorem one_one_ne_zero : ((1 : Real) + 1) ≠ 0 := ne_of_gt zero_lt_one_one

theorem pos_inv (b : Real) (hb : 0 < b) : 0 < Field.inv b := by
  have hbne : b ≠ (0 : Real) := hb.2.symm
  constructor
  · cases le_total (0 : Real) (Field.inv b) with
    | inl h => exact h
    | inr h =>
      exfalso
      have h0 : (0 : Real) ≤ -(Field.inv b) := neg_neg_nonneg _ h
      have h1 : (0 : Real) ≤ b * -(Field.inv b) :=
        mul_nonneg b (-(Field.inv b)) hb.1 h0
      rw [mul_neg, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne] at h1
      have h2 : (1 : Real) ≤ 0 := by
        have := add_le_add_right (0 : Real) (-(1 : Real)) (1 : Real) h1
        rw [zero_add', neg_add'] at this; exact this
      exact zero_lt_one.2 (le_antisymm (0 : Real) (1 : Real) zero_lt_one.1 h2)
  · intro h
    exact Field.nontrivial (show (0 : Real) = 1 from by
      calc (0 : Real) = b * 0 := (mul_zero' b).symm
        _ = b * Field.inv b := by rw [h]
        _ = 1 := Field.mul_inv b hbne)

theorem pos_mul_pos (a b : Real) : 0 < a → 0 < b → 0 < a * b := by
  intro ha hb
  exact ⟨mul_nonneg a b ha.1 hb.1, fun h =>
    ha.2 (by
      calc (0 : Real) = 0 * Field.inv b := (zero_mul' _).symm
        _ = (a * b) * Field.inv b := by rw [h]
        _ = a * (b * Field.inv b) := mul_assoc _ _ _
        _ = a * 1 := by rw [show b * Field.inv b = (1 : Real) from Field.mul_inv b hb.2.symm]
        _ = a := mul_one_b a)⟩
