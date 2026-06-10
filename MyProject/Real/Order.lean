import MyProject.Real.Algebra

noncomputable section

open Real Classical

-- 順序の基本（推移律・移項・Trans インスタンス）

theorem Real.le_of_lt {a b : Real} : a < b → a ≤ b := fun h => h.1

theorem le_refl (a : Real) : a ≤ a := LinearOrderedField.le_refl a

theorem le_trans {a b c : Real} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  LinearOrderedField.le_trans a b c h₁ h₂

theorem lt_neq (a b : Real) : a < b → a ≠ b := fun h => h.2

theorem lt_trans (a b c : Real) : a < b → b < c → a < c := by
  intro ⟨hab, _⟩ ⟨hbc, hne_bc⟩
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne_bc (LinearOrderedField.le_asymm b c hbc (heq ▸ hab))⟩

theorem lt_le_trans (a b c : Real) : a < b → b ≤ c → a < c := by
  intro ⟨hab, hne⟩ hbc
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne (LinearOrderedField.le_asymm a b hab (heq ▸ hbc))⟩

theorem le_lt_trans {a b c : Real} : a ≤ b → b < c → a < c := by
  intro hab ⟨hbc, hne⟩
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne (LinearOrderedField.le_asymm b c hbc (heq ▸ hab))⟩

theorem ne_le_lt (a b : Real) : ¬a ≤ b → b < a := by
  intro h
  cases LinearOrderedField.le_total a b with
  | inl h' => exact absurd h' h
  | inr h' => exact ⟨h', fun heq => h (heq ▸ LinearOrderedField.le_refl a)⟩

-- ============================================================
-- §3. Additive order
-- ============================================================

theorem add_left_le (a b c : Real) : b ≤ c → a + b ≤ a + c := by
  intro h
  have h1 := LinearOrderedField.add_le_add b c a h
  rw [add_comm b a, add_comm c a] at h1; exact h1

theorem add_left_lt (a b c : Real) : b < c → a + b < a + c := by
  intro ⟨hle, hne⟩
  exact ⟨add_left_le a b c hle, fun h => hne (add_left_cancel' a b c h)⟩

theorem nonneg_iff_le (a b : Real) : a ≤ b ↔ 0 ≤ b - a := by
  constructor
  · intro h
    have h1 := LinearOrderedField.add_le_add a b (-a) h
    rw [add_neg'] at h1; exact h1
  · intro h
    have h1 := LinearOrderedField.add_le_add (0 : Real) (b + -a) a h
    rw [zero_add'] at h1
    rw [show b + -a + a = b from by
      calc b + -a + a = b + (-a + a) := add_assoc _ _ _
        _ = b + 0 := by rw [neg_add']
        _ = b := add_zero' _] at h1
    exact h1

theorem neg_neg_nonneg (a : Real) : a ≤ 0 → 0 ≤ -a := by
  intro h
  have h1 := LinearOrderedField.add_le_add a (0 : Real) (-a) h
  rw [add_neg', zero_add'] at h1; exact h1

theorem neg_neg_pos (a : Real) : a < 0 → 0 < -a := by
  intro ⟨hle, hne⟩
  exact ⟨neg_neg_nonneg a hle, fun h => hne (by
    calc a = -(-a) := (neg_neg a).symm
      _ = -(0 : Real) := by rw [h.symm]
      _ = 0 := neg_zero)⟩

theorem neg_le_neg (a b : Real) (h : a ≤ b) : -b ≤ -a := by
  have h1 := LinearOrderedField.add_le_add a b (-a + -b) h
  rw [show a + (-a + -b) = -b from by
      calc a + (-a + -b) = (a + -a) + -b := (add_assoc _ _ _).symm
        _ = 0 + -b := by rw [add_neg']
        _ = -b := zero_add' _,
    show b + (-a + -b) = -a from by
      calc b + (-a + -b) = b + (-b + -a) := by rw [add_comm (-a) (-b)]
        _ = (b + -b) + -a := (add_assoc _ _ _).symm
        _ = 0 + -a := by rw [add_neg']
        _ = -a := zero_add' _] at h1
  exact h1

-- ============================================================
-- §4. Multiplicative order
-- ============================================================

theorem le_sub (a b : Real) : 0 ≤ a - b ↔ b ≤ a := (nonneg_iff_le b a).symm

theorem pos_iff_lt (a b : Real) : a < b ↔ 0 < b - a := by
  constructor
  · intro ⟨hle, hne⟩
    exact ⟨(nonneg_iff_le a b).mp hle, fun h =>
      hne (by
        have heq : b + -a = (0 : Real) := h.symm
        calc a = a + 0 := (add_zero' a).symm
          _ = a + (b + -a) := by rw [heq]
          _ = a + (-a + b) := by rw [add_comm b (-a)]
          _ = (a + -a) + b := (add_assoc _ _ _).symm
          _ = 0 + b := by rw [add_neg']
          _ = b := zero_add' _)⟩
  · intro ⟨hle, hne⟩
    exact ⟨(nonneg_iff_le a b).mpr hle, fun h => hne (by rw [h]; exact (add_neg' b).symm)⟩

theorem lt_add_lt (a b c d : Real) : a < b → c < d → a + c < b + d := by
  intro hab hcd
  exact lt_trans (a + c) (a + d) (b + d) (add_left_lt a c d hcd)
    (by rw [add_comm a d, add_comm b d]; exact add_left_lt d a b hab)

-- ============================================================
-- §8. Abs
-- ============================================================

instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le :=
  ⟨fun h₁ h₂ => LinearOrderedField.le_trans _ _ _ h₁ h₂⟩

instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt :=
  ⟨fun h₁ h₂ => lt_le_trans _ _ _ h₁ h₂⟩

instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => le_lt_trans h₁ h₂⟩

instance : Trans (Eq : Real → Real → Prop) LE.le LE.le :=
  ⟨fun h₁ h₂ => h₁ ▸ h₂⟩

instance : Trans (LE.le : Real → Real → Prop) Eq LE.le :=
  ⟨fun h₁ h₂ => h₂ ▸ h₁⟩

-- ============================================================
-- §12. More theorems
-- ============================================================

theorem pos_sub_iff (a b : Real) : a < b ↔ 0 < b - a := pos_iff_lt a b

theorem nonneg_sub_iff (a b : Real) : a ≤ b ↔ 0 ≤ b - a := nonneg_iff_le a b

theorem le_lt_trans' (a b c : Real) : a ≤ b → b < c → a < c := le_lt_trans

-- 順序
theorem not_lt_imp_le {a b : Real} (h : ¬(a < b)) : b ≤ a := by
  cases LinearOrderedField.le_total a b with
  | inl hle =>
    cases Classical.em (a = b) with
    | inl heq => exact heq ▸ le_refl a
    | inr hne => exact absurd ⟨hle, hne⟩ h
  | inr hle => exact hle

-- 順序（移項）
theorem neg_le_swap {a b : Real} (h : -a ≤ b) : -b ≤ a := by
  have h1 := add_left_le a (-a) b h
  rw [AddCommGroup.add_neg] at h1
  have h2 := add_left_le (-b) AddCommGroup.zero (a + b) h1
  rw [AddCommGroup.add_zero] at h2
  have h3 : -b + (a + b) = a := by
    calc -b + (a + b) = (-b + a) + b := (add_assoc _ _ _).symm
      _ = (a + -b) + b := by rw [add_comm (-b) a]
      _ = a + (-b + b) := add_assoc _ _ _
      _ = a + AddCommGroup.zero := by rw [AddCommGroup.neg_add]
      _ = a := AddCommGroup.add_zero _
  rw [h3] at h2; exact h2

theorem sub_lt_swap {a b c : Real} (h : a - b < c) : a - c < b := by
  have h1 := add_left_lt (b - c) (a - b) c h
  rw [show (b - c) + (a - b) = a - c from (telescope_2 c a b).symm,
      show (b - c) + c = b from by rw [add_comm]; exact add_sub_cancel' c b] at h1
  exact h1

theorem sub_le_swap {a b c : Real} (h : a - b ≤ c) : a - c ≤ b := by
  have h1 := LinearOrderedField.add_le_add (a - b) c (b - c) h
  rw [show a - b + (b - c) = a - c from by
        rw [add_comm]; exact (telescope_2 c a b).symm,
      show c + (b - c) = b from add_sub_cancel' c b] at h1
  exact h1

theorem le_add_of_sub_le {A B C : Real} (h : A - B ≤ C) : A ≤ B + C := by
  have h1 := LinearOrderedField.add_le_add (A - B) C B h
  rw [add_comm (A - B) B, add_sub_cancel' B A,
      add_comm C B] at h1
  exact h1

theorem sub_le_of_le_add {A B C : Real} (h : A ≤ B + C) : A - B ≤ C := by
  have h1 := LinearOrderedField.add_le_add A (B + C) (-B) h
  rw [show B + C + -B = C from by
        rw [add_comm B C, add_assoc, AddCommGroup.add_neg,
            AddCommGroup.add_zero]] at h1
  exact h1

theorem le_of_add_nonneg_eq {a b c : Real} (h : a + b = c) (hb : 0 ≤ b) : a ≤ c := by
  calc a = a + 0 := (add_zero a).symm
    _ ≤ a + b := add_left_le a 0 b hb
    _ = c := h

theorem le_of_nonneg_add_eq {a b c : Real} (h : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  rw [add_comm] at h
  exact le_of_add_nonneg_eq h ha
