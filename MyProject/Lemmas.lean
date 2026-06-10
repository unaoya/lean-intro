import MyProject.Numbers.Real
import MyProject.Numbers.NatNum

noncomputable section

open Real Classical

-- Summation は Numbers/NatNum.lean の Summation（タイポ）の正書きエイリアス
abbrev Summation {α : Type} [Add α] [OfNat α 0] : (n : Nat) → (Range n → α) → α := Sumation

-- ============================================================
-- §0. Bridge lemmas
-- ============================================================
private theorem add_neg' (a : Real) : a + -a = (0 : Real) := AddCommGroup.add_neg a
private theorem neg_add' (a : Real) : -a + a = (0 : Real) := AddCommGroup.neg_add a
private theorem zero_add' (a : Real) : (0 : Real) + a = a := AddCommGroup.zero_add a
private theorem add_zero' (a : Real) : a + (0 : Real) = a := AddCommGroup.add_zero a
private theorem one_mul_b (a : Real) : (1 : Real) * a = a := MulCommMonoid.one_mul a
private theorem mul_one_b (a : Real) : a * (1 : Real) = a := MulCommMonoid.mul_one a

-- ============================================================
-- §1. Basic algebra
-- ============================================================
private theorem add_left_cancel' (a b c : Real) (h : a + b = a + c) : b = c := by
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

private theorem zero_mul_r (a : Real) : (0 : Real) * a = 0 := by
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
    _ = 0 := zero_mul_r b
    _ = a * b + -(a * b) := (add_neg' _).symm

theorem mul_neg (a b : Real) : a * (-b) = -(a * b) := by
  rw [MulCommMonoid.mul_comm a (-b), neg_mul, MulCommMonoid.mul_comm b a]

theorem sub_self (a : Real) : a - a = 0 := add_neg' a
theorem add_neg_sub (a b : Real) : a + -b = a - b := rfl
theorem sub_add_neg (a b : Real) : a - b = a + -b := rfl

theorem add_sub_cancel (a b : Real) : a + b - a = b := by
  calc a + b + -a = a + (b + -a) := AddCommGroup.add_assoc _ _ _
    _ = a + (-a + b) := by rw [AddCommGroup.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_add (a b c d : Real) : a + b - (c + d) = (a - c) + (b - d) := by
  show a + b + -(c + d) = (a + -c) + (b + -d)
  rw [show -(c + d) = -c + -d from neg_add_distrib c d]
  calc a + b + (-c + -d) = a + (b + (-c + -d)) := AddCommGroup.add_assoc _ _ _
    _ = a + (b + -c + -d) := by rw [AddCommGroup.add_assoc b (-c) (-d)]
    _ = a + (-c + b + -d) := by rw [AddCommGroup.add_comm b (-c)]
    _ = a + (-c + (b + -d)) := by rw [AddCommGroup.add_assoc (-c) b (-d)]
    _ = (a + -c) + (b + -d) := (AddCommGroup.add_assoc _ _ _).symm

theorem add_mul (a b c : Real) : (a + b) * c = a * c + b * c := CommRing.right_distrib a b c

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

-- ============================================================
-- §2. Order basics
-- ============================================================
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
  rw [AddCommGroup.add_comm b a, AddCommGroup.add_comm c a] at h1; exact h1

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
      calc b + -a + a = b + (-a + a) := AddCommGroup.add_assoc _ _ _
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

private theorem neg_le_neg (a b : Real) (h : a ≤ b) : -b ≤ -a := by
  have h1 := LinearOrderedField.add_le_add a b (-a + -b) h
  rw [show a + (-a + -b) = -b from by
      calc a + (-a + -b) = (a + -a) + -b := (AddCommGroup.add_assoc _ _ _).symm
        _ = 0 + -b := by rw [add_neg']
        _ = -b := zero_add' _,
    show b + (-a + -b) = -a from by
      calc b + (-a + -b) = b + (-b + -a) := by rw [AddCommGroup.add_comm (-a) (-b)]
        _ = (b + -b) + -a := (AddCommGroup.add_assoc _ _ _).symm
        _ = 0 + -a := by rw [add_neg']
        _ = -a := zero_add' _] at h1
  exact h1

-- ============================================================
-- §4. Multiplicative order
-- ============================================================
theorem mul_nonneg (a b : Real) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b :=
  LinearOrderedField.mul_pos a b h h'

private theorem nonmul_neg_le (a b c : Real) (hc : 0 ≤ c) (hab : 0 ≤ b - a) :
    0 ≤ b * c - a * c := by
  rw [show b * c - a * c = b * c + -(a * c) from rfl,
      show -(a * c) = (-a) * c from (neg_mul a c).symm,
      show b * c + (-a) * c = (b + -a) * c from (CommRing.right_distrib b (-a) c).symm]
  exact LinearOrderedField.mul_pos (b + -a) c hab hc

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
          rw [MulCommMonoid.mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]
      _ = b * c * Field.inv c := by rw [heq]
      _ = b := by rw [MulCommMonoid.mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]

theorem zero_lt_one : (0 : Real) < 1 := by
  cases LinearOrderedField.le_total (0 : Real) 1 with
  | inl h => exact ⟨h, fun heq => Field.nontrivial heq⟩
  | inr h =>
    have h0 : (0 : Real) ≤ -1 := neg_neg_nonneg 1 h
    have h1 : (0 : Real) ≤ (-1) * (-1) := LinearOrderedField.mul_pos (-1) (-1) h0 h0
    have h2 : (-1 : Real) * (-1) = 1 := by
      calc (-1 : Real) * (-1) = -(1 * (-1)) := neg_mul 1 (-1)
        _ = -(-(1 * 1)) := by rw [mul_neg]
        _ = 1 * 1 := neg_neg _
        _ = 1 := one_mul_b 1
    rw [h2] at h1
    exact absurd (LinearOrderedField.le_asymm (0 : Real) (1 : Real) h1 h) Field.nontrivial

theorem zero_lt_two : (0 : Real) < 2 := by
  have h1 := add_left_lt 1 0 1 zero_lt_one
  rw [add_zero'] at h1
  exact lt_trans 0 1 (1 + 1) zero_lt_one h1

private theorem two_ne_zero : (2 : Real) ≠ 0 := zero_lt_two.2.symm

-- ============================================================
-- §5. Inverse positivity
-- ============================================================
private theorem pos_inv (b : Real) (hb : 0 < b) : 0 < Field.inv b := by
  have hbne : b ≠ (0 : Real) := hb.2.symm
  constructor
  · cases LinearOrderedField.le_total (0 : Real) (Field.inv b) with
    | inl h => exact h
    | inr h =>
      exfalso
      have h0 : (0 : Real) ≤ -(Field.inv b) := neg_neg_nonneg _ h
      have h1 : (0 : Real) ≤ b * -(Field.inv b) :=
        LinearOrderedField.mul_pos b (-(Field.inv b)) hb.1 h0
      rw [mul_neg, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne] at h1
      have h2 : (1 : Real) ≤ 0 := by
        have := LinearOrderedField.add_le_add (0 : Real) (-(1 : Real)) (1 : Real) h1
        rw [zero_add', neg_add'] at this; exact this
      exact zero_lt_one.2 (LinearOrderedField.le_asymm (0 : Real) (1 : Real) zero_lt_one.1 h2)
  · intro h
    exact Field.nontrivial (show (0 : Real) = 1 from by
      calc (0 : Real) = b * 0 := (mul_zero' b).symm
        _ = b * Field.inv b := by rw [h]
        _ = 1 := Field.mul_inv b hbne)

private theorem nonneg_inv (b : Real) (hb : 0 ≤ b) (hbne : b ≠ 0) : 0 ≤ Field.inv b :=
  (pos_inv b ⟨hb, hbne.symm⟩).1

-- ============================================================
-- §6. Division theorems
-- ============================================================
theorem pos_mul_pos (a b : Real) : 0 < a → 0 < b → 0 < a * b := by
  intro ha hb
  exact ⟨LinearOrderedField.mul_pos a b ha.1 hb.1, fun h =>
    ha.2 (by
      calc (0 : Real) = 0 * Field.inv b := (zero_mul_r _).symm
        _ = (a * b) * Field.inv b := by rw [h]
        _ = a * (b * Field.inv b) := MulCommMonoid.mul_assoc _ _ _
        _ = a * 1 := by rw [show b * Field.inv b = (1 : Real) from Field.mul_inv b hb.2.symm]
        _ = a := mul_one_b a)⟩

theorem mul_div_cancel (a b : Real) (hb : b ≠ (0 : Real)) : a * b / b = a := by
  show a * b * Field.inv b = a
  rw [MulCommMonoid.mul_assoc, show b * Field.inv b = (1 : Real) from Field.mul_inv b hb, mul_one_b]

theorem mul_div_cancel' (a b : Real) (ha : a ≠ (0 : Real)) : a * b / a = b := by
  show a * b * Field.inv a = b
  calc a * b * Field.inv a = b * a * Field.inv a := by rw [MulCommMonoid.mul_comm a b]
    _ = b * (a * Field.inv a) := MulCommMonoid.mul_assoc b a (Field.inv a)
    _ = b * 1 := by rw [show a * Field.inv a = (1 : Real) from Field.mul_inv a ha]
    _ = b := mul_one_b b

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by
  show a * Field.inv c + -(b * Field.inv c) = (a + -b) * Field.inv c
  rw [show -(b * Field.inv c) = (-b) * Field.inv c from by rw [neg_mul]]
  exact (CommRing.right_distrib a (-b) (Field.inv c)).symm

theorem half_add (a : Real) : a / 2 + a / 2 = a := by
  show a * Field.inv (2 : Real) + a * Field.inv (2 : Real) = a
  rw [← CommRing.left_distrib]
  suffices h : Field.inv (2 : Real) + Field.inv (2 : Real) = (1 : Real) by rw [h, mul_one_b]
  have h1 : ((1 : Real) + 1) * Field.inv (2 : Real) = (1 : Real) := Field.mul_inv 2 two_ne_zero
  rw [CommRing.right_distrib, one_mul_b] at h1; exact h1

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / 2 :=
  pos_mul_pos a (Field.inv 2) h (pos_inv 2 zero_lt_two)

theorem pos_div_pos (a b : Real) : 0 < a → 0 < b → 0 < a / b :=
  fun ha hb => pos_mul_pos a (Field.inv b) ha (pos_inv b hb)

theorem nonneg_div_nonneg (a b : Real) : 0 ≤ a → 0 < b → 0 ≤ a / b :=
  fun ha hb => LinearOrderedField.mul_pos a (Field.inv b) ha (pos_inv b hb).1

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c :=
  fun hc hab => mul_right_lt a b (Field.inv c) (pos_inv c hc) hab

theorem div_right_le (a b c : Real) : 0 ≤ c → a ≤ b → a / c ≤ b / c := by
  intro hc hab
  cases Classical.em (c = 0) with
  | inl heq =>
    show a * Field.inv c ≤ b * Field.inv c
    have hinv : Field.inv c = (0 : Real) := by rw [heq]; exact Real.inv_zero
    rw [hinv, mul_zero', mul_zero']; exact le_refl 0
  | inr hne => exact nonneg_mul_nonneg a b (Field.inv c) (nonneg_inv c hc hne) hab

-- ============================================================
-- §7. More order
-- ============================================================
theorem min_pos (a b : Real) (h : 0 < a) (h' : 0 < b) : 0 < min a b := by
  show (0 : Real) < (if a ≤ b then a else b); split <;> assumption

theorem le_sub (a b : Real) : 0 ≤ a - b ↔ b ≤ a := (nonneg_iff_le b a).symm

theorem pos_iff_lt (a b : Real) : a < b ↔ 0 < b - a := by
  constructor
  · intro ⟨hle, hne⟩
    exact ⟨(nonneg_iff_le a b).mp hle, fun h =>
      hne (by
        have heq : b + -a = (0 : Real) := h.symm
        calc a = a + 0 := (add_zero' a).symm
          _ = a + (b + -a) := by rw [heq]
          _ = a + (-a + b) := by rw [AddCommGroup.add_comm b (-a)]
          _ = (a + -a) + b := (AddCommGroup.add_assoc _ _ _).symm
          _ = 0 + b := by rw [add_neg']
          _ = b := zero_add' _)⟩
  · intro ⟨hle, hne⟩
    exact ⟨(nonneg_iff_le a b).mpr hle, fun h => hne (by rw [h]; exact (add_neg' b).symm)⟩

theorem min_left_le (a b : Real) : min a b ≤ a := by
  show (if a ≤ b then a else b) ≤ a; split
  · exact le_refl a
  · rename_i h; exact (ne_le_lt a b h).1

theorem min_right_le (a b : Real) : min a b ≤ b := by
  show (if a ≤ b then a else b) ≤ b; split
  · rename_i h; exact h
  · exact le_refl b

theorem lt_add_lt (a b c d : Real) : a < b → c < d → a + c < b + d := by
  intro hab hcd
  exact lt_trans (a + c) (a + d) (b + d) (add_left_lt a c d hcd)
    (by rw [AddCommGroup.add_comm a d, AddCommGroup.add_comm b d]; exact add_left_lt d a b hab)

-- ============================================================
-- §8. Abs
-- ============================================================
theorem le_abs (a : Real) : a ≤ abs a := by
  show a ≤ (if a ≤ -a then -a else a); split
  · rename_i h; exact h
  · exact le_refl a

theorem neg_le_abs (a : Real) : -a ≤ abs a := by
  show -a ≤ (if a ≤ -a then -a else a); split
  · exact le_refl (-a)
  · rename_i h; exact (ne_le_lt a (-a) h).1

theorem abs_le (a b : Real) (h₀ : -a ≤ b) (h₁ : a ≤ b) : abs a ≤ b := by
  show (if a ≤ -a then -a else a) ≤ b; split <;> assumption

theorem abs_zero : (0 : Real).abs = 0 := by
  show (if (0 : Real) ≤ -(0 : Real) then -(0 : Real) else (0 : Real)) = 0
  rw [neg_zero, if_pos (le_refl (0 : Real))]

theorem pos_abs {x : Real} (h : 0 < x) : x.abs = x := by
  show (if x ≤ -x then -x else x) = x
  have hneg_le : -x ≤ 0 := by
    have := LinearOrderedField.add_le_add (0 : Real) x (-x) h.1
    rw [zero_add', add_neg'] at this; exact this
  rw [if_neg (fun hle => h.2 (LinearOrderedField.le_asymm (0 : Real) x h.1
    (LinearOrderedField.le_trans x (-x) 0 hle hneg_le)))]

theorem nonneg_abs {x : Real} (hx : 0 ≤ x) : x.abs = x := by
  cases Classical.em (x = 0) with
  | inl heq => rw [heq]; exact abs_zero
  | inr hne => exact pos_abs ⟨hx, fun h => hne h.symm⟩

private theorem nonpos_abs {x : Real} (hx : x ≤ 0) : x.abs = -x := by
  show (if x ≤ -x then -x else x) = -x
  rw [if_pos (LinearOrderedField.le_trans x 0 (-x) hx (neg_neg_nonneg x hx))]

theorem abs_nonneg {x : Real} : 0 ≤ x.abs := by
  cases LinearOrderedField.le_total (0 : Real) x with
  | inl h => exact LinearOrderedField.le_trans 0 x x.abs h (le_abs x)
  | inr h => exact LinearOrderedField.le_trans 0 (-x) x.abs (neg_neg_nonneg x h) (neg_le_abs x)

theorem abs_neg (z : Real) : Real.abs (-z) = Real.abs z := by
  show (if -z ≤ -(-z) then -(-z) else -z) = (if z ≤ -z then -z else z)
  rw [neg_neg]
  cases Classical.em (z ≤ -z) with
  | inl h =>
    rw [if_pos h]
    cases Classical.em (-z ≤ z) with
    | inl h' => rw [if_pos h']; exact LinearOrderedField.le_asymm z (-z) h h'
    | inr h' => rw [if_neg h']
  | inr h =>
    rw [if_neg h]
    rw [if_pos (by cases LinearOrderedField.le_total z (-z) with
      | inl h' => exact absurd h' h
      | inr h' => exact h')]

theorem abs_triangle (a b : Real) : abs (a + b) ≤ abs a + abs b := by
  apply abs_le
  · -- -(a+b) ≤ abs a + abs b
    rw [show -(a + b) = -a + -b from neg_add_distrib a b]
    exact LinearOrderedField.le_trans _ _ _
      (LinearOrderedField.add_le_add (-a) (Real.abs a) (-b) (neg_le_abs a))
      (add_left_le (Real.abs a) (-b) (Real.abs b) (neg_le_abs b))
  · exact LinearOrderedField.le_trans _ _ _
      (LinearOrderedField.add_le_add a (Real.abs a) b (le_abs a))
      (add_left_le (Real.abs a) b (Real.abs b) (le_abs b))

theorem neg_sub_neg_abs (a b : Real) : abs (-a - -b) = abs (a - b) := by
  show Real.abs (-a + -(-b)) = Real.abs (a + -b)
  rw [neg_neg]
  have h : -a + b = -(a + -b) := by
    rw [show -(a + -b) = -a + -(-b) from neg_add_distrib a (-b), neg_neg]
  rw [h, abs_neg]

@[simp]
theorem sub_zero_abs (x : Real) : (x - 0).abs = x.abs := by
  show Real.abs (x + -(0 : Real)) = Real.abs x
  rw [neg_zero, add_zero']

-- abs multiplicativity for nonneg right factor
theorem abs_mul_nonneg {x y : Real} (hy : 0 ≤ y) : Real.abs (x * y) = Real.abs x * y := by
  cases Classical.em (y = 0) with
  | inl heq => rw [heq, mul_zero', abs_zero, mul_zero']
  | inr hyne =>
    cases LinearOrderedField.le_total (0 : Real) x with
    | inl hx => rw [nonneg_abs (LinearOrderedField.mul_pos x y hx hy), nonneg_abs hx]
    | inr hx =>
      have hnx : (0 : Real) ≤ -x := neg_neg_nonneg x hx
      have hxy_neg : x * y ≤ 0 := by
        have h1 : (0 : Real) ≤ (-x) * y := LinearOrderedField.mul_pos (-x) y hnx hy
        rw [neg_mul] at h1
        have := LinearOrderedField.add_le_add (0 : Real) (-(x * y)) (x * y) h1
        rw [zero_add', neg_add'] at this; exact this
      rw [nonpos_abs hxy_neg, nonpos_abs hx, neg_mul]

-- Full abs_mul
private theorem abs_mul' (x y : Real) : Real.abs (x * y) = Real.abs x * Real.abs y := by
  cases LinearOrderedField.le_total (0 : Real) y with
  | inl hy => rw [abs_mul_nonneg hy, nonneg_abs hy]
  | inr hy =>
    have hny : (0 : Real) ≤ -y := neg_neg_nonneg y hy
    rw [show x * y = -(x * (-y)) from by rw [mul_neg, neg_neg],
        abs_neg, abs_mul_nonneg hny, nonpos_abs hy]

theorem div_abs_le {a b c : Real} (h : a.abs ≤ b.abs) : (a / c).abs ≤ (b / c).abs := by
  show Real.abs (a * Field.inv c) ≤ Real.abs (b * Field.inv c)
  rw [abs_mul' a (Field.inv c), abs_mul' b (Field.inv c)]
  exact nonneg_mul_nonneg (Real.abs a) (Real.abs b) (Real.abs (Field.inv c)) abs_nonneg h

-- Reverse triangle inequality: ||a| - |b|| ≤ |a - b|
theorem abs_sub_abs_le (a b : Real) : (a.abs - b.abs).abs ≤ (a - b).abs := by
  apply abs_le
  · -- -(|a| - |b|) = |b| - |a| ≤ |a - b|
    have h1 : b.abs ≤ (b - a).abs + a.abs := by
      calc b.abs = ((b - a) + a).abs := by
            congr 1; show b = (b + -a) + a
            rw [AddCommGroup.add_assoc, AddCommGroup.neg_add, AddCommGroup.add_zero]
        _ ≤ (b - a).abs + a.abs := abs_triangle (b - a) a
    have h2 : b.abs - a.abs ≤ (b - a).abs := by
      have h1' := LinearOrderedField.add_le_add _ _ (-a.abs) h1
      rw [show (b - a).abs + a.abs + -a.abs = (b - a).abs from by
        rw [AddCommGroup.add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1'
      exact h1'
    have h3 : -(a.abs - b.abs) = b.abs - a.abs := by
      show -(a.abs + -b.abs) = b.abs + -a.abs
      rw [neg_add_distrib, neg_neg, AddCommGroup.add_comm]
    rw [h3]
    calc b.abs - a.abs ≤ (b - a).abs := h2
      _ = (a - b).abs := by
        have : b - a = -(a - b) := by
          show b + -a = -(a + -b)
          rw [neg_add_distrib, neg_neg, AddCommGroup.add_comm]
        rw [this, abs_neg]
  · -- |a| - |b| ≤ |a - b|
    have h1 : a.abs ≤ (a - b).abs + b.abs := by
      calc a.abs = ((a - b) + b).abs := by
            congr 1; show a = (a + -b) + b
            rw [AddCommGroup.add_assoc, AddCommGroup.neg_add, AddCommGroup.add_zero]
        _ ≤ (a - b).abs + b.abs := abs_triangle (a - b) b
    have h1' := LinearOrderedField.add_le_add _ _ (-b.abs) h1
    rw [show (a - b).abs + b.abs + -b.abs = (a - b).abs from by
      rw [AddCommGroup.add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1'
    exact h1'

-- ============================================================
-- §9. Summation
-- ============================================================
theorem summation_smul (n : Nat) (f : Range n → Real) (c : Real) :
  Summation n (fun i ↦ c * f i) = c * Summation n f := by
  induction n with
  | zero => simp [Summation, Sumation]; exact (mul_zero' c).symm
  | succ n ih =>
    simp only [Summation, Sumation] at ih ⊢
    rw [ih]; exact (CommRing.left_distrib c _ _).symm

private theorem add_four_comm (a b c d : Real) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d) = a + (b + (c + d)) := AddCommGroup.add_assoc _ _ _
    _ = a + ((b + c) + d) := by rw [(AddCommGroup.add_assoc b c d).symm]
    _ = a + ((c + b) + d) := by rw [AddCommGroup.add_comm b c]
    _ = a + (c + (b + d)) := by rw [AddCommGroup.add_assoc c b d]
    _ = (a + c) + (b + d) := (AddCommGroup.add_assoc _ _ _).symm

theorem additive_summation (n : Nat) (f g : Range n → Real) :
  Summation n (fun i ↦ f i + g i) = Summation n f + Summation n g := by
  induction n with
  | zero => simp [Summation, Sumation]; exact (zero_add' 0).symm
  | succ n ih =>
    simp only [Summation, Sumation] at ih ⊢
    rw [ih]
    exact add_four_comm _ _ _ _

theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
  Summation n f = Summation n g := congrArg _ (funext h)

theorem neg_summation (n : Nat) (f : Range n → Real) :
  -Summation n f = Summation n (fun i ↦ -f i) := by
  induction n with
  | zero => simp [Summation, Sumation]; exact neg_zero
  | succ n ih => simp only [Summation, Sumation]; rw [neg_add_distrib, ih]

theorem summation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
  0 ≤ Summation n f := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    simp only [Summation, Sumation]
    let f' : Range n → Real := fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩
    have h1 : (0 : Real) ≤ Summation n f' :=
      ih f' (fun i => h ⟨i.val, Nat.lt_of_lt_of_le i.property (Nat.le_succ n)⟩)
    have h2 := h ⟨n, Nat.lt_add_one n⟩
    have h3 := LinearOrderedField.add_le_add (0 : Real) (Summation n f') (0 : Real) h1
    rw [add_zero'] at h3
    exact LinearOrderedField.le_trans _ _ _ h3 (add_left_le _ 0 _ h2)

theorem summation_le (n : Nat) (f g : Range n → Real) (h : ∀ i, f i ≤ g i) :
    Summation n f ≤ Summation n g := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    simp only [Summation, Sumation]
    let f' : Range n → Real := fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩
    let g' : Range n → Real := fun k => g ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩
    have ih' : Summation n f' ≤ Summation n g' :=
      ih f' g' (fun i => h ⟨i.val, Nat.lt_of_lt_of_le i.property (Nat.le_succ n)⟩)
    have hn := h ⟨n, Nat.lt_add_one n⟩
    exact le_trans
      (LinearOrderedField.add_le_add _ _ (f ⟨n, Nat.lt_add_one n⟩) ih')
      (add_left_le (Summation n g') _ _ hn)

-- ============================================================
-- §10. fmax'
-- ============================================================
def fpred' (n : Nat) (f : Range n.succ → Real) : Range n → Real :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ n => fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n.succ)⟩

def fmax' (n : Nat) (f : Range n → Real) : Real :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => max (f ⟨n, Nat.lt_succ_self n⟩) (fmax' n (fpred' n f))

theorem fmax'_lt (n : Nat) (f : Range n → Real) (a : Real) (ha : 0 < a) :
    (∀ i, f i < a) → fmax' n f < a := by
  intro hf
  induction n with
  | zero => exact ha
  | succ n ih =>
    show (if f ⟨n, _⟩ ≤ fmax' n (fpred' n f) then fmax' n (fpred' n f) else f ⟨n, _⟩) < a
    split
    · exact ih (fpred' n f) (by
        intro ⟨i, hi⟩
        cases n with
        | zero => exact absurd hi (Nat.not_lt_zero _)
        | succ m =>
          have : i < (m + 1 + 1) := Nat.lt_of_lt_of_le hi (Nat.le_step (Nat.le_refl _))
          exact hf ⟨i, Nat.lt_of_lt_of_le this (Nat.le_refl _)⟩)
    · exact hf ⟨n, Nat.lt_succ_self n⟩

private theorem fpred'_eq_f {n : Nat} (f : Range (n + 1) → Real) (k : Range (n + 1))
    (hlt : k.val < n) : fpred' n f ⟨k.val, hlt⟩ = f k := by
  cases n with
  | zero => exact absurd hlt (Nat.not_lt_zero _)
  | succ m => rfl

theorem le_fmax' (n : Nat) (f : Range n → Real) (k : Range n) : f k ≤ fmax' n f := by
  induction n with
  | zero => exact absurd k.property (Nat.not_lt_zero _)
  | succ n ih =>
    show f k ≤ (if f ⟨n, _⟩ ≤ fmax' n (fpred' n f) then fmax' n (fpred' n f) else f ⟨n, _⟩)
    by_cases hk : k.val = n
    · have hke : k = ⟨n, Nat.lt_succ_self n⟩ := Subtype.ext hk
      subst hke; split
      · assumption
      · exact le_refl _
    · have hlt : k.val < n := by have := k.property; omega
      rw [← fpred'_eq_f f k hlt]; split
      · exact ih (fpred' n f) ⟨k.val, hlt⟩
      · rename_i hcond
        exact le_trans (ih (fpred' n f) ⟨k.val, hlt⟩)
          ((LinearOrderedField.le_total _ _).elim (absurd · hcond) id)

theorem fmax'_le (n : Nat) (f : Range n → Real) (a : Real) (ha : 0 ≤ a)
    (hf : ∀ i, f i ≤ a) : fmax' n f ≤ a := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    show (if f ⟨n, _⟩ ≤ fmax' n (fpred' n f) then fmax' n (fpred' n f) else f ⟨n, _⟩) ≤ a
    split
    · exact ih (fpred' n f) (fun ⟨i, hi⟩ => by
        cases n with
        | zero => exact absurd hi (Nat.not_lt_zero _)
        | succ m => exact hf ⟨i, by omega⟩)
    · exact hf ⟨n, Nat.lt_succ_self n⟩

-- ============================================================
-- §11. Instances
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
theorem nez_of_abs_pos {x : Real} (h : 0 < x.abs) : x ≠ 0 := by
  intro heq; rw [heq, abs_zero] at h; exact h.2 rfl

theorem right_le_pos_add_pos (a b : Real) : 0 ≤ a → 0 ≤ b → b ≤ (a + b).abs := by
  intro ha _
  exact LinearOrderedField.le_trans b (a + b) (a + b).abs
    (by have := LinearOrderedField.add_le_add (0 : Real) a b ha; rw [zero_add'] at this; exact this)
    (le_abs (a + b))

-- ============================================================
-- §13. NatCast
-- ============================================================
theorem succ_ofNat (n : Nat) : Real.ofNat (n + 1) = Real.ofNat n + (1 : Real) := by
  cases n with
  | zero => show (1 : Real) = (0 : Real) + 1; exact (zero_add' 1).symm
  | succ m => rfl

theorem cast_nonneg (n : Nat) : (0 : Real) ≤ Real.ofNat n := by
  induction n with
  | zero => exact le_refl 0
  | succ m ih =>
    rw [succ_ofNat]
    calc (0 : Real) = 0 + 0 := (add_zero' 0).symm
      _ ≤ Real.ofNat m + 0 := LinearOrderedField.add_le_add 0 (Real.ofNat m) 0 ih
      _ ≤ Real.ofNat m + 1 := add_left_le _ 0 1 zero_lt_one.1

private theorem cast_pos_succ (n : Nat) : (0 : Real) < Real.ofNat (n + 1) := by
  rw [succ_ofNat]
  exact lt_le_trans 0 1 (Real.ofNat n + 1) zero_lt_one
    (by calc (1 : Real) = 0 + 1 := (zero_add' 1).symm
        _ ≤ Real.ofNat n + 1 := LinearOrderedField.add_le_add 0 (Real.ofNat n) 1 (cast_nonneg n))

theorem cast_add (n m : Nat) : (Nat.cast : Nat → Real) n + (Nat.cast m) = (Nat.cast (n + m)) := by
  show Real.ofNat n + Real.ofNat m = Real.ofNat (n + m)
  induction m with
  | zero => rw [Nat.add_zero]; exact add_zero' _
  | succ m ih =>
    have eq1 : Real.ofNat m.succ = Real.ofNat m + 1 := succ_ofNat m
    have eq2 : n + m.succ = (n + m).succ := Nat.add_succ n m
    have eq3 : Real.ofNat (n + m).succ = Real.ofNat (n + m) + 1 := succ_ofNat (n + m)
    rw [eq1, eq2, eq3]
    calc Real.ofNat n + (Real.ofNat m + 1)
      = (Real.ofNat n + Real.ofNat m) + 1 := (AddCommGroup.add_assoc _ _ _).symm
      _ = Real.ofNat (n + m) + 1 := by rw [ih]

theorem cast_lt (a b : Nat) : a < b → (a : Real) < b := by
  show a < b → (Real.ofNat a : Real) < Real.ofNat b
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt h
  -- hd : b = a + d + 1, i.e. b = (a + d) + 1
  have hassoc : a + d + 1 = a + (d + 1) := Nat.add_assoc a d 1
  rw [hd, hassoc]
  have h_eq : Real.ofNat (a + (d + 1)) = Real.ofNat a + Real.ofNat (d + 1) :=
    (cast_add a (d + 1)).symm
  rw [h_eq]
  have hpos : (0 : Real) < Real.ofNat (d + 1) := cast_pos_succ d
  have h1 := add_left_lt (Real.ofNat a) 0 (Real.ofNat (d + 1)) hpos
  rw [add_zero'] at h1; exact h1

theorem lt_cast (n m : Nat) : n < m → (n : Real) < m := cast_lt n m

-- ============================================================
-- §14. Ceil
-- ============================================================
axiom archimedean (a : Real) : ∃ n : Nat, a < n

def ceil (a : Real) : Nat := min (fun n => a < n) (archimedean a)

private theorem ceil_spec (a : Real) :
    a < ↑(ceil a) ∧ ∀ x : Nat, a < ↑x → ¬(x < ceil a) :=
  Classical.choose_spec (has_min (fun n => a < ↑n) (archimedean a))

theorem ceil_lt (a : Real) : a < ↑(ceil a) := (ceil_spec a).1

theorem ceil_nonneg (a : Real) : (0 : Real) ≤ ↑(ceil a) := cast_nonneg (ceil a)

theorem pos_ceil_pos (a : Real) : 0 < a → (0 : Real) < ↑(ceil a) :=
  fun h => lt_trans 0 a ↑(ceil a) h (ceil_lt a)

-- ============================================================
-- §15. Range value theorems
-- ============================================================
theorem zero_val (n : Nat) (hn : 0 < n) : (⟨0, hn⟩ : Range n).val = (0 : Real) := rfl

theorem range_val (n k : Nat) (hk : k < n) : (⟨k, hk⟩ : Range n).val = (k : Real) := rfl

theorem zero_mul' (a : Real) : 0 * a = 0 := zero_mul_r a
theorem zero_div (a : Real) : 0 / a = 0 := by show (0 : Real) * Field.inv a = 0; exact zero_mul_r _
theorem add_zero (a : Real) : a + 0 = a := add_zero' a
theorem one_mul (a : Real) : 1 * a = a := one_mul_b a

theorem cast_one_mul (x : Real) : (Nat.cast 1) * x = x := by
  show Real.ofNat 1 * x = x; exact one_mul_b x

open Range

theorem cast_incl_val (n : Nat) (k : Range n) : ((incl k).val : Real) = (k.val : Real) := rfl

theorem cast_addone_val (n : Nat) (k : Range n) : ((addone k).val : Real) = (k.val : Real) + 1 := by
  show (Nat.cast (k.val + 1) : Real) = (Nat.cast k.val : Real) + 1
  show Real.ofNat (k.val + 1) = Real.ofNat k.val + 1
  exact succ_ofNat k.val

theorem incl_lt_addone (n : Nat) (i : Range n) : (incl i).val < (addone i).val :=
  Nat.lt_succ_self i.val

-- ============================================================
-- §16. InInterval
-- ============================================================
def InInterval (a b : Real) (x : Real) : Prop :=
  if a ≤ b then a ≤ x ∧ x ≤ b else b ≤ x ∧ x ≤ a

def InInterval_abs {x h t : Real} : InInterval x (x + h) t → (t - x).abs ≤ h.abs := by
  intro hint
  dsimp [InInterval] at hint
  split at hint
  · -- x ≤ x + h
    rename_i hle
    have hh : (0 : Real) ≤ h := by
      have := LinearOrderedField.add_le_add x (x + h) (-x) hle
      rw [add_neg', show (x + h) + -x = h from add_sub_cancel x h] at this; exact this
    have htx : (0 : Real) ≤ t + -x := by
      have := LinearOrderedField.add_le_add x t (-x) hint.1
      rw [add_neg'] at this; exact this
    have htxh : t + -x ≤ h := by
      have := LinearOrderedField.add_le_add t (x + h) (-x) hint.2
      rw [show (x + h) + -x = h from add_sub_cancel x h] at this; exact this
    show Real.abs (t + -x) ≤ Real.abs h
    rw [nonneg_abs htx, nonneg_abs hh]; exact htxh
  · -- ¬(x ≤ x + h)
    rename_i hnle
    have hh : h ≤ 0 := by
      have hlt := ne_le_lt x (x + h) hnle
      have := LinearOrderedField.add_le_add (x + h) x (-x) hlt.1
      rw [show (x + h) + -x = h from add_sub_cancel x h, add_neg'] at this; exact this
    have htx : t + -x ≤ 0 := by
      have := LinearOrderedField.add_le_add t x (-x) hint.2
      rw [add_neg'] at this; exact this
    have hhtx : h ≤ t + -x := by
      have := LinearOrderedField.add_le_add (x + h) t (-x) hint.1
      rw [show (x + h) + -x = h from add_sub_cancel x h] at this; exact this
    show Real.abs (t + -x) ≤ Real.abs h
    rw [nonpos_abs htx, nonpos_abs hh]
    exact neg_le_neg h (t + -x) hhtx

-- ============================================================
-- §17. Remaining
-- ============================================================
theorem aux (a b c : Real) (hc : c ≠ (0 : Real)) : a * (b + c - b) / c = a := by
  rw [add_sub_cancel b c]; exact mul_div_cancel a c hc

theorem pos_sub_iff (a b : Real) : a < b ↔ 0 < b - a := pos_iff_lt a b
theorem nonneg_sub_iff (a b : Real) : a ≤ b ↔ 0 ≤ b - a := nonneg_iff_le a b
theorem le_lt_trans' (a b c : Real) : a ≤ b → b < c → a < c := le_lt_trans

theorem summation_zero (f : Range 0 → Real) : Summation 0 f = 0 := rfl

theorem summation_succ (n : Nat) (f : Range n.succ → Real) :
  Summation n.succ f = Summation n (fun i ↦ f (incl i)) + f ⟨n, by exact Nat.lt_add_one n⟩ := rfl

theorem telescope_2 (a b c : Real) : b - a = (c - a) + (b - c) := by
  show b + -a = (c + -a) + (b + -c)
  symm
  calc (c + -a) + (b + -c) = c + (-a + (b + -c)) := AddCommGroup.add_assoc _ _ _
    _ = c + (-a + b + -c) := by rw [AddCommGroup.add_assoc (-a) b (-c)]
    _ = c + (b + -a + -c) := by rw [AddCommGroup.add_comm (-a) b]
    _ = c + (b + (-a + -c)) := by rw [AddCommGroup.add_assoc b (-a) (-c)]
    _ = (c + b) + (-a + -c) := (AddCommGroup.add_assoc _ _ _).symm
    _ = (c + b) + -(a + c) := by rw [neg_add_distrib]
    _ = (b + c) + -(c + a) := by rw [AddCommGroup.add_comm c b, AddCommGroup.add_comm a c]
    _ = (b + c) + (-c + -a) := by rw [neg_add_distrib]
    _ = b + (c + (-c + -a)) := AddCommGroup.add_assoc _ _ _
    _ = b + ((c + -c) + -a) := by rw [(AddCommGroup.add_assoc c (-c) (-a)).symm]
    _ = b + (0 + -a) := by rw [add_neg']
    _ = b + -a := by rw [zero_add']

theorem telescope_sum (n : Nat) (f : Range n.succ → Real) :
  Summation n (fun i ↦ f (addone i) - f (incl i)) = f ⟨n, by exact Nat.lt_add_one n⟩ - f ⟨0, by simp⟩ :=
  match n with
  | Nat.zero => by rw [summation_zero, sub_self]
  | Nat.succ n => by
    rw [summation_succ]
    let f' : Range n.succ → Real := fun i => f (incl i)
    have (i : Range n) : addone (incl i) = incl (addone i) := by rw [addone_incl_comm n i]
    have : (fun i ↦ f (addone (incl i)) - f (incl (incl i))) = fun i ↦ f (incl (addone i)) - f (incl (incl i)) := by
      apply funext; intro i; rw [this]
    rw [this, telescope_sum n f']
    dsimp [f']
    rw [← telescope_2]; rfl

theorem div_lt_iff (a b c : Real) (bpos : 0 < b) (cpos : 0 < c) : a / b < c ↔ a / c < b := by
  have hbne := bpos.2.symm
  have hcne := cpos.2.symm
  constructor
  · intro h
    -- a * inv b < c → (a * inv b) * b < c * b → a < c * b
    have h1 := mul_right_lt (a * Field.inv b) c b bpos h
    rw [MulCommMonoid.mul_assoc, show Field.inv b * b = (1 : Real) from Field.inv_mul b hbne,
        mul_one_b] at h1
    -- a < c * b → a * inv c < c * b * inv c = b
    have h2 := mul_right_lt a (c * b) (Field.inv c) (pos_inv c cpos) h1
    rw [show c * b = b * c from MulCommMonoid.mul_comm c b,
        MulCommMonoid.mul_assoc, show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne,
        mul_one_b] at h2
    exact h2
  · intro h
    have h1 := mul_right_lt (a * Field.inv c) b c cpos h
    rw [MulCommMonoid.mul_assoc, show Field.inv c * c = (1 : Real) from Field.inv_mul c hcne,
        mul_one_b] at h1
    have h2 := mul_right_lt a (b * c) (Field.inv b) (pos_inv b bpos) h1
    rw [show b * c = c * b from MulCommMonoid.mul_comm b c,
        MulCommMonoid.mul_assoc, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne,
        mul_one_b] at h2
    exact h2

-- Σ of zero function = 0
theorem summation_all_zero (n : Nat) : Summation n (fun _ : Range n => (0 : Real)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Summation m (fun _ : Range m => (0 : Real)) + (0 : Real) = 0
    rw [ih, zero_add']

-- Σ of function nonzero at one point = that value
theorem summation_one_term (m : Nat) (k : Range m) (h : Range m → Real)
    (hzero : ∀ i : Range m, i.val ≠ k.val → h i = 0) :
    Summation m h = h k := by
  induction m with
  | zero => exact absurd k.property (Nat.not_lt_zero _)
  | succ n ih =>
    rw [summation_succ]
    by_cases hkn : k.val = n
    · -- k is the last element: all incl terms are 0
      have hall : ∀ i : Range n, h (incl i) = 0 := by
        intro i; apply hzero; show (incl i).val ≠ k.val
        have := i.property; simp only [incl_val]; omega
      rw [summation_congr n _ _ hall, summation_all_zero, zero_add']
      have : (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) = k := Subtype.ext hkn.symm
      rw [this]
    · -- k.val < n: last term is 0
      have hklt : k.val < n := by have := k.property; omega
      have hlast : h ⟨n, Nat.lt_succ_self n⟩ = 0 := by
        apply hzero; show n ≠ k.val; omega
      rw [hlast, add_zero]
      have h_ih := ih ⟨k.val, hklt⟩ (fun i => h (incl i)) (by
        intro i hne; apply hzero (incl i)
        show (incl i).val ≠ k.val; simp only [incl_val]; exact hne)
      rw [h_ih]; rfl

-- k番目の項を2つに分割しても和は変わらない
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
    have hk := k.property  -- k.val < n + 1
    rw [summation_succ, summation_succ]
    by_cases hkn : k.val = n
    · -- k is last: rewrite h_split to match the goal
      rw [summation_succ]
      have hcongr : ∀ i : Range n, g (incl (incl i)) = f (incl i) := by
        intro i; have := i.property
        exact h_low (incl (incl i)) (by simp only [incl_val]; omega)
      rw [summation_congr n _ _ hcongr, AddCommGroup.add_assoc]; congr 1
      -- Goal: g (incl ⟨n, _⟩) + g ⟨n+1, _⟩ = f ⟨n, _⟩
      -- h_split: g ⟨k.val, _⟩ + g ⟨k.val+1, _⟩ = f k
      have e1 : (⟨k.val, Nat.lt_succ_of_lt k.property⟩ : Range (n + 2)) =
                 incl (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) :=
        Subtype.ext (by simp [incl_val]; omega)
      have e2 : (⟨k.val + 1, Nat.succ_lt_succ k.property⟩ : Range (n + 2)) =
                 (⟨n + 1, by omega⟩ : Range (n + 2)) :=
        Subtype.ext (by show k.val + 1 = n + 1; omega)
      have e3 : k = (⟨n, Nat.lt_succ_self n⟩ : Range (n + 1)) :=
        Subtype.ext hkn
      rw [e1, e2, e3] at h_split; exact h_split
    · -- k < n: last terms match
      have hklt : k.val < n := by omega
      have hlast : g ⟨n + 1, by omega⟩ = f ⟨n, Nat.lt_succ_self n⟩ :=
        h_high ⟨n + 1, by omega⟩ (by show k.val + 1 < n + 1; omega)
      rw [hlast]; congr 1
      exact ih ⟨k.val, hklt⟩ (fun i => f (incl i)) (fun i => g (incl i))
        (fun i hi => h_low (incl i) (by simp only [incl_val]; exact hi))
        h_split
        (fun i hi => h_high (incl i) (by simp only [incl_val]; exact hi))

-- ============================================================
-- §17. 集約補題（Integral 以下の重複 private を統合）
-- ============================================================

-- 順序
theorem not_lt_imp_le {a b : Real} (h : ¬(a < b)) : b ≤ a := by
  cases LinearOrderedField.le_total a b with
  | inl hle =>
    cases Classical.em (a = b) with
    | inl heq => exact heq ▸ le_refl a
    | inr hne => exact absurd ⟨hle, hne⟩ h
  | inr hle => exact hle

-- 代数（符号の整理）
theorem neg_sub (a b : Real) : -(a - b) = b - a := by
  show -(a + -b) = b + -a; rw [neg_add_distrib, neg_neg, AddCommGroup.add_comm]

theorem sub_zero (x : Real) : x - 0 = x := by
  show x + -(0 : Real) = x
  rw [neg_zero, add_zero]

theorem add_neg_cancel_right (x y : Real) : (x + y) + -y = x := by
  rw [AddCommGroup.add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]

theorem neg_add_cancel_left (x y : Real) : -x + (x + y) = y := by
  rw [← AddCommGroup.add_assoc, AddCommGroup.neg_add, AddCommGroup.zero_add]

theorem neg_neg_cancel_left (x y : Real) : (-x + -y) + x = -y := by
  rw [AddCommGroup.add_comm (-x) (-y), AddCommGroup.add_assoc, AddCommGroup.neg_add,
      AddCommGroup.add_zero]

theorem add_neg_neg_cancel (x y : Real) : x + (-y + -x) = -y := by
  rw [AddCommGroup.add_comm (-y) (-x), ← AddCommGroup.add_assoc, AddCommGroup.add_neg,
      AddCommGroup.zero_add]

-- 順序（移項）
theorem neg_le_swap {a b : Real} (h : -a ≤ b) : -b ≤ a := by
  have h1 := add_left_le a (-a) b h
  rw [AddCommGroup.add_neg] at h1
  have h2 := add_left_le (-b) AddCommGroup.zero (a + b) h1
  rw [AddCommGroup.add_zero] at h2
  have h3 : -b + (a + b) = a := by
    calc -b + (a + b) = (-b + a) + b := (AddCommGroup.add_assoc _ _ _).symm
      _ = (a + -b) + b := by rw [AddCommGroup.add_comm (-b) a]
      _ = a + (-b + b) := AddCommGroup.add_assoc _ _ _
      _ = a + AddCommGroup.zero := by rw [AddCommGroup.neg_add]
      _ = a := AddCommGroup.add_zero _
  rw [h3] at h2; exact h2

theorem sub_lt_swap {a b c : Real} (h : a - b < c) : a - c < b := by
  have h1 := add_left_lt (b - c) (a - b) c h
  rw [show (b - c) + (a - b) = a - c from (telescope_2 c a b).symm,
      show (b - c) + c = b from by rw [AddCommGroup.add_comm]; exact add_sub_cancel' c b] at h1
  exact h1

theorem sub_le_swap {a b c : Real} (h : a - b ≤ c) : a - c ≤ b := by
  have h1 := LinearOrderedField.add_le_add (a - b) c (b - c) h
  rw [show a - b + (b - c) = a - c from by
        rw [AddCommGroup.add_comm]; exact (telescope_2 c a b).symm,
      show c + (b - c) = b from add_sub_cancel' c b] at h1
  exact h1

theorem le_add_of_sub_le {A B C : Real} (h : A - B ≤ C) : A ≤ B + C := by
  have h1 := LinearOrderedField.add_le_add (A - B) C B h
  rw [AddCommGroup.add_comm (A - B) B, add_sub_cancel' B A,
      AddCommGroup.add_comm C B] at h1
  exact h1

theorem sub_le_of_le_add {A B C : Real} (h : A ≤ B + C) : A - B ≤ C := by
  have h1 := LinearOrderedField.add_le_add A (B + C) (-B) h
  rw [show B + C + -B = C from by
        rw [AddCommGroup.add_comm B C, AddCommGroup.add_assoc, AddCommGroup.add_neg,
            AddCommGroup.add_zero]] at h1
  exact h1

theorem le_of_add_nonneg_eq {a b c : Real} (h : a + b = c) (hb : 0 ≤ b) : a ≤ c := by
  calc a = a + 0 := (add_zero a).symm
    _ ≤ a + b := add_left_le a 0 b hb
    _ = c := h

theorem le_of_nonneg_add_eq {a b c : Real} (h : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  rw [AddCommGroup.add_comm] at h
  exact le_of_add_nonneg_eq h ha

-- 乗法・除法
theorem mul_le_mul_left (c x y : Real) (hc : 0 ≤ c) (h : x ≤ y) : c * x ≤ c * y := by
  rw [MulCommMonoid.mul_comm c x, MulCommMonoid.mul_comm c y]
  exact nonneg_mul_nonneg x y c hc h

theorem div_mul_cancel' (a b : Real) (hb : b ≠ 0) : a / b * b = a := by
  show a * Field.inv b * b = a
  rw [MulCommMonoid.mul_assoc, Field.inv_mul b hb, MulCommMonoid.mul_one]

theorem div_add_div (a b c : Real) : a / c + b / c = (a + b) / c := by
  show a * Field.inv c + b * Field.inv c = (a + b) * Field.inv c
  exact (add_mul a b (Field.inv c)).symm

theorem neg_div (a b : Real) : -a / b = -(a / b) := by
  show -a * Field.inv b = -(a * Field.inv b)
  exact neg_mul a (Field.inv b)

theorem half_lt {ε : Real} (hε : 0 < ε) : ε / 2 < ε := by
  have h1 := add_left_lt (ε / 2) 0 (ε / 2) (pos_half ε hε)
  rw [add_zero] at h1; rw [half_add] at h1; exact h1

-- min
theorem min_eq_left {a b : Real} (h : a ≤ b) : min a b = a := by
  show (if a ≤ b then a else b) = a
  rw [if_pos h]

theorem min_eq_right {a b : Real} (h : b ≤ a) : min a b = b := by
  show (if a ≤ b then a else b) = b
  cases Classical.em (a ≤ b) with
  | inl h' => rw [if_pos h']; exact LinearOrderedField.le_asymm a b h' h
  | inr h' => rw [if_neg h']

-- ε-論法
theorem le_of_forall_le_add {A B : Real} (h : ∀ γ, 0 < γ → A ≤ B + γ) : A ≤ B := by
  cases LinearOrderedField.le_total A B with
  | inl hle => exact hle
  | inr hge =>
    cases Classical.em (A = B) with
    | inl heq => rw [heq]; exact le_refl B
    | inr hne =>
      exfalso
      have hBA : B < A := ⟨hge, fun h0 => hne h0.symm⟩
      have hpos : 0 < A - B := (pos_iff_lt B A).mp hBA
      have h1 := h ((A - B) / 2) (pos_half _ hpos)
      have h2 : B + (A - B) / 2 < B + (A - B) := add_left_lt B _ _ (half_lt hpos)
      rw [add_sub_cancel' B A] at h2
      exact (le_lt_trans h1 h2).2 rfl

-- 絶対値
theorem abs_sub_comm (a b : Real) : (a - b).abs = (b - a).abs := by
  rw [← neg_sub a b, abs_neg]

theorem abs_sub_le_add (x y z : Real) : (x - z).abs ≤ (x - y).abs + (y - z).abs := by
  calc (x - z).abs
      = ((y - z) + (x - y)).abs := by rw [telescope_2 z x y]
    _ ≤ (y - z).abs + (x - y).abs := abs_triangle _ _
    _ = (x - y).abs + (y - z).abs := AddCommGroup.add_comm _ _

theorem abs_sub_le_of_mem {P Q s t : Real}
    (hsP : P ≤ s) (hsQ : s ≤ Q) (htP : P ≤ t) (htQ : t ≤ Q) :
    (s - t).abs ≤ Q - P := by
  have hnegt : -t ≤ -P := neg_le_swap (show -(-P) ≤ t from by rw [neg_neg]; exact htP)
  have hnegs : -s ≤ -P := neg_le_swap (show -(-P) ≤ s from by rw [neg_neg]; exact hsP)
  apply abs_le
  · rw [neg_sub]
    exact le_trans (LinearOrderedField.add_le_add t Q (-s) htQ) (add_left_le Q _ _ hnegs)
  · exact le_trans (LinearOrderedField.add_le_add s Q (-t) hsQ) (add_left_le Q _ _ hnegt)

-- InInterval の展開
theorem in_interval_iff {a b t : Real} (hab : a ≤ b) :
    InInterval a b t ↔ a ≤ t ∧ t ≤ b := by
  dsimp [InInterval]
  rw [if_pos hab]

theorem in_interval_pair {a b t : Real} (hab : a ≤ b) (h : InInterval a b t) :
    a ≤ t ∧ t ≤ b := (in_interval_iff hab).mp h

theorem abs_summation_le (n : Nat) (h : Range n → Real) :
    (Summation n h).abs ≤ Summation n (fun i => (h i).abs) := by
  induction n with
  | zero =>
    rw [show Summation 0 h = 0 from rfl, abs_zero]
    exact le_refl 0
  | succ m ih =>
    rw [summation_succ m h, summation_succ m (fun i => (h i).abs)]
    apply le_trans (abs_triangle _ _)
    exact LinearOrderedField.add_le_add _ _ _ (ih (fun i => h (Range.incl i)))

theorem sub_summation (n : Nat) (F G : Range n → Real) :
    Summation n F - Summation n G = Summation n (fun i => F i - G i) := by
  calc Summation n F - Summation n G
      = Summation n F + Summation n (fun i => -G i) := by
        show Summation n F + -Summation n G = _
        rw [neg_summation]
    _ = Summation n (fun i => F i + -G i) := (additive_summation n F (fun i => -G i)).symm
    _ = Summation n (fun i => F i - G i) := rfl

-- 総和を前後 2 ブロックに分割
theorem summation_split_at (c d : Nat) (g : Range (c + d) → Real) :
    Summation (c + d) g =
    Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
    Summation d (fun j => g ⟨c + j.val, by have := j.property; omega⟩) := by
  induction d with
  | zero =>
    rw [summation_zero, add_zero]
    apply summation_congr
    intro i
    rfl
  | succ d ih =>
    calc Summation (c + (d + 1)) g
        = Summation (c + d) (fun i => g (Range.incl i)) +
          g ⟨c + d, Nat.lt_succ_self (c + d)⟩ := summation_succ (c + d) g
      _ = (Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
           Summation d (fun j => g ⟨c + j.val, by have := j.property; omega⟩)) +
          g ⟨c + d, Nat.lt_succ_self (c + d)⟩ :=
          congrArg (fun s => s + g ⟨c + d, Nat.lt_succ_self (c + d)⟩)
            (ih (fun i => g (Range.incl i)))
      _ = Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
          (Summation d (fun j => g ⟨c + j.val, by have := j.property; omega⟩) +
           g ⟨c + d, Nat.lt_succ_self (c + d)⟩) := AddCommGroup.add_assoc _ _ _
      _ = Summation c (fun i => g ⟨i.val, by have := i.property; omega⟩) +
          Summation (d + 1) (fun j => g ⟨c + j.val, by have := j.property; omega⟩) :=
          congrArg (fun s => Summation c (fun i =>
              g ⟨i.val, by have := i.property; omega⟩) + s)
            (summation_succ d (fun j : Range (d + 1) =>
              g ⟨c + j.val, by have := j.property; omega⟩)).symm

-- 総和の先頭 1 項を取り出す
theorem summation_first (m : Nat) (h : Range (m + 1) → Real) :
    Summation (m + 1) h = h ⟨0, Nat.zero_lt_succ m⟩ +
      Summation m (fun j => h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩) := by
  induction m with
  | zero =>
    calc Summation (0 + 1) h
        = Summation 0 (fun i => h (Range.incl i)) + h ⟨0, Nat.zero_lt_succ 0⟩ :=
          summation_succ 0 h
      _ = 0 + h ⟨0, Nat.zero_lt_succ 0⟩ := rfl
      _ = h ⟨0, Nat.zero_lt_succ 0⟩ := AddCommGroup.zero_add _
      _ = h ⟨0, Nat.zero_lt_succ 0⟩ +
          Summation 0 (fun j => h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩) :=
          (add_zero _).symm
  | succ m ih =>
    calc Summation (m + 1 + 1) h
        = Summation (m + 1) (fun i => h (Range.incl i)) +
          h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ := summation_succ (m + 1) h
      _ = (h ⟨0, Nat.zero_lt_succ (m + 1)⟩ +
           Summation m (fun j => h ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt j.property)⟩)) +
          h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ :=
          congrArg (fun s => s + h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
            (ih (fun i => h (Range.incl i)))
      _ = h ⟨0, Nat.zero_lt_succ (m + 1)⟩ +
          (Summation m (fun j => h ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt j.property)⟩) +
           h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) := AddCommGroup.add_assoc _ _ _
      _ = h ⟨0, Nat.zero_lt_succ (m + 1)⟩ +
          Summation (m + 1) (fun j => h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩) :=
          congrArg (fun s => h ⟨0, Nat.zero_lt_succ (m + 1)⟩ + s)
            (summation_succ m (fun j : Range (m + 1) =>
              h ⟨j.val + 1, Nat.succ_lt_succ j.property⟩)).symm

-- ============================================================
-- §18. 上限の近似
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
    have h1 := LinearOrderedField.add_le_add (Real.sup S hne hbdd)
      (Real.sup S hne hbdd - γ) (-(Real.sup S hne hbdd)) hle
    rw [AddCommGroup.add_neg] at h1
    rw [show Real.sup S hne hbdd - γ + -(Real.sup S hne hbdd) = -γ from by
          show Real.sup S hne hbdd + -γ + -(Real.sup S hne hbdd) = -γ
          rw [AddCommGroup.add_comm (Real.sup S hne hbdd) (-γ),
              AddCommGroup.add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1
    have h2 : γ ≤ 0 :=
      calc γ = 0 + γ := (AddCommGroup.zero_add γ).symm
        _ ≤ -γ + γ := LinearOrderedField.add_le_add 0 (-γ) γ h1
        _ = 0 := AddCommGroup.neg_add γ
    exact hγ.2 (LinearOrderedField.le_asymm 0 γ hγ.1 h2)

#check (inferInstance : Max Real)

#check "all done"
