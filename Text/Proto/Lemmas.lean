-- Text/Proto/Lemmas.lean — M2: 一意性に必要な補題コーパス（参照実装から移植・命名改善版）
import Text.Proto.Numerals

noncomputable section

open Classical

-- ============================================================
-- 代数（橋渡しと基本計算）
-- ============================================================

theorem add_neg' (a : Real) : a + -a = (0 : Real) := AddCommGroup.add_neg a
theorem neg_add' (a : Real) : -a + a = (0 : Real) := AddCommGroup.neg_add a
theorem zero_add' (a : Real) : (0 : Real) + a = a := AddCommGroup.zero_add a
theorem add_zero' (a : Real) : a + (0 : Real) = a := AddCommGroup.add_zero a
theorem one_mul_b (a : Real) : (1 : Real) * a = a := MulCommMonoid.one_mul a
theorem mul_one_b (a : Real) : a * (1 : Real) = a := MulCommMonoid.mul_one a

theorem add_comm (a b : Real) : a + b = b + a := AddCommGroup.add_comm a b
theorem add_assoc (a b c : Real) : a + b + c = a + (b + c) := AddCommGroup.add_assoc a b c
theorem mul_comm (a b : Real) : a * b = b * a := MulCommMonoid.mul_comm a b
theorem mul_assoc (a b c : Real) : a * b * c = a * (b * c) := MulCommMonoid.mul_assoc a b c

theorem add_left_cancel' (a b c : Real) (h : a + b = a + c) : b = c := by
  calc b = 0 + b := (zero_add' _).symm
    _ = (-a + a) + b := by rw [neg_add']
    _ = -a + (a + b) := AddCommGroup.add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + c := by rw [neg_add']
    _ = c := zero_add' _

theorem mul_zero' (a : Real) : a * (0 : Real) = 0 := by
  apply add_left_cancel' (a * (0 : Real))
  calc a * 0 + (a * 0) = a * (0 + 0) := (CommRing.left_distrib a 0 0).symm
    _ = a * 0 := by rw [zero_add' (0 : Real)]
    _ = a * 0 + 0 := (add_zero' _).symm

theorem zero_mul' (a : Real) : (0 : Real) * a = 0 := by
  rw [MulCommMonoid.mul_comm]; exact mul_zero' a

theorem neg_zero : -(0 : Real) = 0 := by
  calc -(0 : Real) = -(0 : Real) + 0 := (add_zero' _).symm
    _ = 0 := neg_add' 0

theorem neg_add_distrib (a b : Real) : -(a + b) = -a + -b := by
  apply add_left_cancel' (a + b)
  have lhs : (a + b) + -(a + b) = (0 : Real) := add_neg' _
  have rhs : (a + b) + (-a + -b) = (0 : Real) := by
    calc (a + b) + (-a + -b)
      = a + (b + (-a + -b)) := AddCommGroup.add_assoc _ _ _
      _ = a + ((b + -a) + -b) := by rw [AddCommGroup.add_assoc b (-a) (-b)]
      _ = a + ((-a + b) + -b) := by rw [AddCommGroup.add_comm b (-a)]
      _ = a + (-a + (b + -b)) := by rw [AddCommGroup.add_assoc (-a) b (-b)]
      _ = a + (-a + 0) := by rw [add_neg']
      _ = a + -a := by rw [add_zero']
      _ = 0 := add_neg' _
  rw [lhs, rhs]

theorem neg_neg (a : Real) : -(-a) = a := by
  apply add_left_cancel' (-a); rw [add_neg', neg_add']

theorem neg_mul (a b : Real) : -a * b = -(a * b) := by
  apply add_left_cancel' (a * b)
  calc a * b + -a * b = (a + -a) * b := (CommRing.right_distrib a (-a) b).symm
    _ = 0 * b := by rw [add_neg']
    _ = 0 := zero_mul' b
    _ = a * b + -(a * b) := (add_neg' _).symm

theorem mul_neg (a b : Real) : a * (-b) = -(a * b) := by
  rw [MulCommMonoid.mul_comm a (-b), neg_mul, MulCommMonoid.mul_comm b a]

theorem sub_self (a : Real) : a - a = 0 := add_neg' a

theorem add_sub_cancel (a b : Real) : a + b - a = b := by
  calc a + b + -a = a + (b + -a) := AddCommGroup.add_assoc _ _ _
    _ = a + (-a + b) := by rw [AddCommGroup.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_cancel' (a b : Real) : a + (b - a) = b := by
  calc a + (b + -a) = a + (-a + b) := by rw [AddCommGroup.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_add' (a b c : Real) : a + b - (a + c) = (b - c) := by
  show a + b + -(a + c) = b + -c
  rw [show -(a + c) = -a + -c from neg_add_distrib a c]
  calc a + b + (-a + -c) = a + (b + (-a + -c)) := AddCommGroup.add_assoc _ _ _
    _ = a + (b + -a + -c) := by rw [AddCommGroup.add_assoc b (-a) (-c)]
    _ = a + (-a + b + -c) := by rw [AddCommGroup.add_comm b (-a)]
    _ = a + (-a + (b + -c)) := by rw [AddCommGroup.add_assoc (-a) b (-c)]
    _ = (a + -a) + (b + -c) := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + (b + -c) := by rw [add_neg']
    _ = b + -c := zero_add' _

theorem mul_sub_mul (a b c : Real) : a * b - c * b = (a - c) * b := by
  show a * b + -(c * b) = (a + -c) * b
  rw [show -(c * b) = (-c) * b from (neg_mul c b).symm]
  exact (CommRing.right_distrib a (-c) b).symm

theorem zero_div (a : Real) : 0 / a = 0 := by
  show (0 : Real) * Field.inv a = 0; exact zero_mul' _

theorem add_zero (a : Real) : a + 0 = a := add_zero' a
theorem one_mul (a : Real) : 1 * a = a := one_mul_b a

theorem sub_add_cancel (a b : Real) : a - b + b = a := by
  show a + -b + b = a
  rw [AddCommGroup.add_assoc, neg_add', add_zero']

-- ============================================================
-- 順序
-- ============================================================

theorem le_of_lt {a b : Real} : a < b → a ≤ b := fun h => h.1
theorem le_refl (a : Real) : a ≤ a := LinearOrderedField.le_refl a
theorem le_trans {a b c : Real} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  LinearOrderedField.le_trans a b c h₁ h₂
theorem le_antisymm (a b : Real) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  LinearOrderedField.le_antisymm a b h₁ h₂
theorem le_total (a b : Real) : a ≤ b ∨ b ≤ a := LinearOrderedField.le_total a b
theorem add_le_add_right (a b c : Real) (h : a ≤ b) : a + c ≤ b + c :=
  LinearOrderedField.add_le_add a b c h
theorem lt_of_le_of_ne {a b : Real} (h : a ≤ b) (hne : a ≠ b) : a < b := ⟨h, hne⟩
theorem ne_of_gt {a b : Real} (h : a < b) : b ≠ a := fun h0 => h.2 h0.symm

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

-- calc 用の Trans インスタンス
instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le :=
  ⟨fun h₁ h₂ => le_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt :=
  ⟨fun h₁ h₂ => lt_le_trans _ _ _ h₁ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => le_lt_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => lt_trans _ _ _ h₁ h₂⟩

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

-- 古典論理が要る移項（< が ≤ ∧ ≠ で定義されているため二重否定除去相当が必要）
theorem not_lt_imp_le {a b : Real} (h : ¬(a < b)) : b ≤ a := by
  cases le_total a b with
  | inr h' => exact h'
  | inl hab =>
    have heq : a = b := Classical.byContradiction (fun hne => h ⟨hab, hne⟩)
    exact heq ▸ le_refl a

-- ============================================================
-- 乗法の順序・除法
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

-- リテラル 2 は導入しない: 1 + 1 で書く（半分の構成のため）
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

theorem mul_div_cancel' (a b : Real) (ha : a ≠ (0 : Real)) : a * b / a = b := by
  show a * b * Field.inv a = b
  calc a * b * Field.inv a = b * a * Field.inv a := by rw [mul_comm a b]
    _ = b * (a * Field.inv a) := mul_assoc b a (Field.inv a)
    _ = b * 1 := by rw [show a * Field.inv a = (1 : Real) from Field.mul_inv a ha]
    _ = b := mul_one_b b

theorem div_mul_cancel (a c : Real) (hc : c ≠ (0 : Real)) : a / c * c = a := by
  show a * Field.inv c * c = a
  rw [mul_assoc, show Field.inv c * c = (1 : Real) from Field.inv_mul c hc, mul_one_b]

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by
  show a * Field.inv c + -(b * Field.inv c) = (a + -b) * Field.inv c
  rw [show -(b * Field.inv c) = (-b) * Field.inv c from by rw [neg_mul]]
  exact (CommRing.right_distrib a (-b) (Field.inv c)).symm

theorem half_add (a : Real) : a / (1 + 1) + a / (1 + 1) = a := by
  show a * Field.inv (1 + 1) + a * Field.inv (1 + 1) = a
  rw [← CommRing.left_distrib]
  suffices h : Field.inv ((1 : Real) + 1) + Field.inv ((1 : Real) + 1) = (1 : Real) by
    rw [h, mul_one_b]
  have h1 : ((1 : Real) + 1) * Field.inv ((1 : Real) + 1) = (1 : Real) :=
    Field.mul_inv (1 + 1) one_one_ne_zero
  rw [CommRing.right_distrib, one_mul_b] at h1; exact h1

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / (1 + 1) :=
  pos_mul_pos a (Field.inv (1 + 1)) h (pos_inv (1 + 1) zero_lt_one_one)

theorem pos_div_pos (a b : Real) : 0 < a → 0 < b → 0 < a / b :=
  fun ha hb => pos_mul_pos a (Field.inv b) ha (pos_inv b hb)

theorem nonneg_div_nonneg (a b : Real) : 0 ≤ a → 0 < b → 0 ≤ a / b :=
  fun ha hb => mul_nonneg a (Field.inv b) ha (pos_inv b hb).1

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c :=
  fun hc hab => mul_right_lt a b (Field.inv c) (pos_inv c hc) hab

theorem div_right_le (a b c : Real) : 0 < c → a ≤ b → a / c ≤ b / c :=
  fun hc hab => nonneg_mul_nonneg a b (Field.inv c) (pos_inv c hc).1 hab
