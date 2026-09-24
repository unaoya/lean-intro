-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。
-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。

import LeanIntro.Original.«06_Topology»

-- # 発展演習: 実数

-- ## Part A: 実数の公理

class CompleteOrderedField (R : Type) extends Add R, Mul R, Neg R, Inv R, Zero R, One R,
    LE R, LT R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  zero_ne_one : (0 : R) ≠ 1
  mul_inv_cancel : ∀ a : R, a ≠ 0 → a * a⁻¹ = 1
  le_refl : ∀ a : R, a ≤ a
  le_trans : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : R, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : R, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : R, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c, c + a ≤ c + b
  mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  exists_lub : ∀ S : Set R, (∃ x, x ∈ S) → (∃ M, ∀ x ∈ S, x ≤ M) →
    ∃ s, (∀ x ∈ S, x ≤ s) ∧ ∀ M, (∀ x ∈ S, x ≤ M) → s ≤ M

namespace CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

instance : Sub R := ⟨fun a b => a + -b⟩
instance : Div R := ⟨fun a b => a * b⁻¹⟩
instance : OfNat R 2 := ⟨1 + 1⟩

instance : Std.Associative (α := R) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := R) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := R) (· * ·) := ⟨mul_assoc⟩
instance : Std.Commutative (α := R) (· * ·) := ⟨mul_comm⟩

theorem sub_def (a b : R) : a - b = a + -b := rfl

theorem div_def (a b : R) : a / b = a * b⁻¹ := rfl

theorem two_def : (2 : R) = 1 + 1 := rfl

-- ## Part B: 足し算と掛け算

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
  sorry

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  rw [add_comm a, add_comm b] at h
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_neg (a : R) : -(-a) = a :=
  sorry

theorem neg_zero : -(0 : R) = 0 := neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_add (a b : R) : -(a + b) = -a + -b :=
  sorry

theorem sub_self (a : R) : a - a = 0 := add_neg_cancel a

theorem sub_zero (a : R) : a - 0 = a := by rw [sub_def, neg_zero, add_zero]

theorem zero_sub (a : R) : 0 - a = -a := by rw [sub_def, zero_add]

theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_def, add_assoc, neg_add_cancel, add_zero]

theorem add_sub_cancel (a b : R) : a + b - b = a := by
  rw [sub_def, add_assoc, add_neg_cancel, add_zero]

theorem sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg (· + b) h
    simp only at h'
    rw [sub_add_cancel, zero_add] at h'
    exact h'
  · intro h; rw [h, sub_self]

theorem neg_sub (a b : R) : -(a - b) = b - a := by
  rw [sub_def, neg_add, neg_neg, sub_def, add_comm]

theorem sub_add_sub_cancel (a b c : R) : a - b + (b - c) = a - c := by
  rw [sub_def, sub_def, sub_def, add_assoc, ← add_assoc (-b), neg_add_cancel, zero_add]

theorem add_sub_add_right (a b c : R) : a + c - (b + c) = a - b := by
  rw [sub_def, sub_def, neg_add]
  calc a + c + (-b + -c) = a + -b + (c + -c) := by ac_rfl
    _ = a + -b := by rw [add_neg_cancel, add_zero]

theorem mul_one (a : R) : a * 1 = a := by rw [mul_comm, one_mul]

theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

theorem mul_zero (a : R) : a * 0 = 0 :=
  sorry

theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]

theorem mul_neg (a b : R) : a * -b = -(a * b) :=
  sorry

theorem neg_mul (a b : R) : -a * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_def, sub_def, mul_add, mul_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [mul_comm, mul_sub, mul_comm c, mul_comm c]

theorem two_mul (a : R) : 2 * a = a + a := by rw [two_def, add_mul, one_mul]

theorem mul_eq_zero {a b : R} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  sorry

theorem inv_mul_cancel {a : R} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_cancel a h]

theorem div_mul_cancel {a b : R} (h : b ≠ 0) : a / b * b = a := by
  rw [div_def, mul_assoc, inv_mul_cancel h, mul_one]

theorem mul_div_cancel {a b : R} (h : b ≠ 0) : a * b / b = a := by
  rw [div_def, mul_assoc, mul_inv_cancel b h, mul_one]

theorem mul_div_cancel_left {c : R} (e : R) (h : c ≠ 0) : c * (e / c) = e := by
  rw [mul_comm, div_mul_cancel h]

theorem inv_ne_zero {a : R} (h : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h'
  have := mul_inv_cancel a h
  rw [h', mul_zero] at this
  exact zero_ne_one this

-- ## Part C: 順序

theorem lt_irrefl (a : R) : ¬ a < a := fun h => ((lt_iff_le_not_le a a).mp h).2 (le_refl a)

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b := ((lt_iff_le_not_le a b).mp h).1

theorem not_le {a b : R} : ¬ a ≤ b ↔ b < a :=
  sorry

theorem not_lt {a b : R} : ¬ a < b ↔ b ≤ a := by
  constructor
  · intro h
    rcases le_total b a with h' | h'
    · exact h'
    · exact Classical.byContradiction fun h'' => h (not_le.mp h'')
  · intro h h'
    exact not_le.mpr h' h

theorem lt_of_le_of_lt {a b c : R} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  not_le.mp fun h => not_le.mpr h₂ (le_trans c a b h h₁)

theorem lt_of_lt_of_le {a b c : R} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  not_le.mp fun h => not_le.mpr h₁ (le_trans b c a h₂ h)

theorem lt_trans {a b c : R} (h₁ : a < b) (h₂ : b < c) : a < c :=
  lt_of_le_of_lt (le_of_lt h₁) h₂

instance : Trans (α := R) (β := R) (γ := R) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans _ _ _⟩
instance : Trans (α := R) (β := R) (γ := R) (· ≤ ·) (· < ·) (· < ·) := ⟨lt_of_le_of_lt⟩
instance : Trans (α := R) (β := R) (γ := R) (· < ·) (· ≤ ·) (· < ·) := ⟨lt_of_lt_of_le⟩
instance : Trans (α := R) (β := R) (γ := R) (· < ·) (· < ·) (· < ·) := ⟨lt_trans⟩

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := fun e => lt_irrefl b (e ▸ h)

theorem lt_of_le_of_ne {a b : R} (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b :=
  not_le.mp fun h => h₂ (le_antisymm a b h₁ h)

theorem lt_or_le (a b : R) : a < b ∨ b ≤ a := by
  by_cases h : b ≤ a
  · exact .inr h
  · exact .inl (not_le.mp h)

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a, add_comm b]; exact add_le_add_left a b h c

theorem le_of_add_le_add_left {a b c : R} (h : c + a ≤ c + b) : a ≤ b := by
  have := add_le_add_left _ _ h (-c)
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at this
  exact this

theorem add_lt_add_left {a b : R} (h : a < b) (c : R) : c + a < c + b :=
  sorry

theorem add_lt_add_right {a b : R} (h : a < b) (c : R) : a + c < b + c := by
  rw [add_comm a, add_comm b]; exact add_lt_add_left h c

theorem add_le_add {a b c d : R} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans _ _ _ (add_le_add_right h₁ c) (add_le_add_left _ _ h₂ b)

theorem add_lt_add {a b c d : R} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  lt_trans (add_lt_add_right h₁ c) (add_lt_add_left h₂ b)

theorem add_lt_add_of_lt_of_le {a b c d : R} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left _ _ h₂ b)

theorem sub_nonneg {a b : R} : 0 ≤ b - a ↔ a ≤ b :=
  sorry

theorem sub_pos {a b : R} : 0 < b - a ↔ a < b := by
  constructor
  · intro h; exact not_le.mp fun h' => not_le.mpr h (by
      have := add_le_add_right h' (-a); rwa [add_neg_cancel] at this)
  · intro h; exact not_le.mp fun h' => not_le.mpr h (by
      have := add_le_add_right h' a; rwa [zero_add, sub_add_cancel] at this)

theorem neg_le_neg {a b : R} (h : a ≤ b) : -b ≤ -a :=
  sorry

theorem neg_lt_neg {a b : R} (h : a < b) : -b < -a :=
  not_le.mp fun h' => not_le.mpr h (by have := neg_le_neg h'; rwa [neg_neg, neg_neg] at this)

theorem neg_nonneg {a : R} : 0 ≤ -a ↔ a ≤ 0 := by
  constructor
  · intro h; have := neg_le_neg h; rwa [neg_neg, neg_zero] at this
  · intro h; have := neg_le_neg h; rwa [neg_zero] at this

theorem neg_pos {a : R} : 0 < -a ↔ a < 0 := by
  constructor
  · intro h; have := neg_lt_neg h; rwa [neg_neg, neg_zero] at this
  · intro h; have := neg_lt_neg h; rwa [neg_zero] at this

theorem add_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have := add_lt_add ha hb; rwa [add_zero] at this

theorem add_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have := add_le_add ha hb; rwa [add_zero] at this

theorem lt_add_of_pos_right (a : R) {b : R} (h : 0 < b) : a < a + b := by
  have := add_lt_add_left h a; rwa [add_zero] at this

theorem sub_lt_self (a : R) {b : R} (h : 0 < b) : a - b < a := by
  have := add_lt_add_left (neg_lt_neg h) a
  rwa [neg_zero, add_zero] at this

theorem mul_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  sorry

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  have := mul_nonneg c (b - a) hc (sub_nonneg.mpr h)
  rw [mul_sub] at this
  exact sub_nonneg.mp this

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm a, mul_comm b]; exact mul_le_mul_of_nonneg_left h hc

theorem mul_lt_mul_of_pos_left {a b c : R} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  have := mul_pos hc (sub_pos.mpr h)
  rw [mul_sub] at this
  exact sub_pos.mp this

theorem mul_self_nonneg (a : R) : 0 ≤ a * a := by
  rcases le_total 0 a with h | h
  · exact mul_nonneg a a h h
  · have := mul_nonneg (-a) (-a) (neg_nonneg.mpr h) (neg_nonneg.mpr h)
    rwa [neg_mul_neg] at this

theorem zero_lt_one : (0 : R) < 1 :=
  sorry

theorem zero_lt_two : (0 : R) < 2 := add_pos zero_lt_one zero_lt_one

theorem inv_pos {a : R} (h : 0 < a) : 0 < a⁻¹ :=
  sorry

theorem div_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := mul_pos ha (inv_pos hb)

theorem two_ne_zero : (2 : R) ≠ 0 := (ne_of_lt zero_lt_two).symm

theorem add_halves (a : R) : a / 2 + a / 2 = a := by
  rw [← two_mul, mul_comm, div_mul_cancel two_ne_zero]

theorem half_pos {a : R} (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

theorem half_lt_self {a : R} (h : 0 < a) : a / 2 < a :=
  sorry

theorem half_add_lt {c ε : R} (h : 0 < ε) : c + ε / 2 < c + ε :=
  add_lt_add_left (half_lt_self h) c

-- ## Part D: 絶対値と最小値

open Classical in

noncomputable def abs (a : R) : R := if 0 ≤ a then a else -a

theorem abs_of_nonneg {a : R} (h : 0 ≤ a) : abs a = a := by
  rw [abs, if_pos h]

theorem abs_of_neg {a : R} (h : a < 0) : abs a = -a := by
  rw [abs, if_neg (not_le.mpr h)]

theorem abs_zero : abs (0 : R) = 0 := abs_of_nonneg (le_refl 0)

theorem abs_of_nonpos {a : R} (h : a ≤ 0) : abs a = -a := by
  rcases lt_or_le a 0 with h' | h'
  · exact abs_of_neg h'
  · have : a = 0 := le_antisymm _ _ h h'
    rw [this, abs_zero, neg_zero]

theorem abs_nonneg (a : R) : 0 ≤ abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h]; exact le_of_lt (neg_pos.mpr h)
  · rw [abs_of_nonneg h]; exact h

theorem le_abs_self (a : R) : a ≤ abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h]; exact le_trans _ _ _ (le_of_lt h) (le_of_lt (neg_pos.mpr h))
  · rw [abs_of_nonneg h]; exact le_refl a

theorem abs_neg (a : R) : abs (-a) = abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h, abs_of_nonneg (le_of_lt (neg_pos.mpr h))]
  · rcases lt_or_le 0 a with h' | h'
    · rw [abs_of_nonneg h, abs_of_neg (neg_pos.mp (by rwa [neg_neg]))]
      exact neg_neg a
    · have : a = 0 := le_antisymm _ _ h' h
      rw [this, neg_zero]

theorem neg_abs_le (a : R) : -abs a ≤ a := by
  have := le_abs_self (-a)
  rw [abs_neg] at this
  have := neg_le_neg this
  rwa [neg_neg] at this

theorem abs_sub_comm (a b : R) : abs (a - b) = abs (b - a) := by
  rw [← neg_sub, abs_neg]

theorem abs_lt {a b : R} : abs a < b ↔ -b < a ∧ a < b :=
  sorry

theorem abs_add (a b : R) : abs (a + b) ≤ abs a + abs b :=
  sorry

theorem abs_sub_le (a b c : R) : abs (a - c) ≤ abs (a - b) + abs (b - c) := by
  rw [← sub_add_sub_cancel a b c]
  exact abs_add _ _

theorem abs_sub_self (a : R) : abs (a - a) = 0 := by rw [sub_self, abs_zero]

theorem abs_le_abs_add_abs_sub (a b : R) : abs a ≤ abs b + abs (a - b) := by
  have := abs_add b (a - b)
  rwa [sub_def, ← add_assoc, add_comm b a, add_assoc, add_neg_cancel, add_zero] at this

theorem abs_sub_lt_of {c y ε : R} (h₁ : c - ε < y) (h₂ : y < c + ε) : abs (y - c) < ε := by
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have := add_lt_add_right h₁ (-c)
    rw [sub_def, add_comm c, add_assoc, add_neg_cancel, add_zero] at this
    exact this
  · have := add_lt_add_right h₂ (-c)
    rw [add_comm c, add_assoc, add_neg_cancel, add_zero] at this
    exact this

theorem mul_nonpos_of_nonneg_of_nonpos {a b : R} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have := mul_nonneg a (-b) ha (neg_nonneg.mpr hb)
  rw [mul_neg] at this
  exact neg_nonneg.mp this

theorem abs_mul (a b : R) : abs (a * b) = abs a * abs b :=
  sorry

open Classical in
noncomputable def min (a b : R) : R := if a ≤ b then a else b

theorem min_le_left (a b : R) : min a b ≤ a := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact le_refl a
  · rw [if_neg h]; exact le_of_lt (not_le.mp h)

theorem min_le_right (a b : R) : min a b ≤ b := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact le_refl b

theorem lt_min {a b c : R} (hb : a < b) (hc : a < c) : a < min b c := by
  unfold min
  by_cases h : b ≤ c
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact hc

-- ## Part E: 完備性

theorem exists_mem_gt_of_lub {S : Set R} {s : R}
    (hlub : ∀ M, (∀ x ∈ S, x ≤ M) → s ≤ M) {ε : R} (hε : 0 < ε) :
    ∃ x, x ∈ S ∧ s - ε < x :=
  sorry

def natCast : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1

theorem natCast_zero : (natCast 0 : R) = 0 := rfl

theorem natCast_succ (n : Nat) : (natCast (n + 1) : R) = natCast n + 1 := rfl

theorem natCast_nonneg : ∀ n : Nat, (0 : R) ≤ natCast n
  | 0 => le_refl 0
  | n + 1 => add_nonneg (natCast_nonneg n) (le_of_lt zero_lt_one)

theorem natCast_add (m : Nat) : ∀ n : Nat, (natCast (m + n) : R) = natCast m + natCast n
  | 0 => (add_zero _).symm
  | n + 1 => by
      rw [← Nat.add_assoc, natCast_succ, natCast_succ, natCast_add m n, add_assoc]

theorem exists_nat_gt (x : R) : ∃ n : Nat, x < natCast n :=
  sorry

def intCast : Int → R
  | Int.ofNat n => natCast n
  | Int.negSucc n => -natCast (n + 1)

theorem intCast_natCast (n : Nat) : (intCast (n : Int) : R) = natCast n := rfl

theorem intCast_zero : (intCast 0 : R) = 0 := rfl

theorem intCast_sub_one : ∀ k : Int, (intCast (k - 1) : R) = intCast k - 1
  | Int.ofNat 0 => by
      rw [show Int.ofNat 0 - 1 = Int.negSucc 0 from rfl]
      show -(natCast 1 : R) = natCast 0 - 1
      rw [natCast_succ, natCast_zero, zero_add, zero_sub]
  | Int.ofNat (n + 1) => by
      rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp only [Int.ofNat_eq_natCast]; omega]
      show (natCast n : R) = natCast (n + 1) - 1
      rw [natCast_succ, add_sub_cancel]
  | Int.negSucc n => by
      rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) by simp only [Int.negSucc_eq]; omega]
      show -(natCast (n + 1 + 1) : R) = -natCast (n + 1) - 1
      rw [natCast_succ (n + 1), neg_add]; rfl

theorem intCast_add_one (k : Int) : (intCast (k + 1) : R) = intCast k + 1 := by
  have h := intCast_sub_one (R := R) (k + 1)
  rw [Int.add_sub_cancel] at h
  rw [h, sub_add_cancel]

theorem intCast_add_natCast (k : Int) : ∀ n : Nat,
    (intCast (k + n) : R) = intCast k + natCast n
  | 0 => by rw [Int.natCast_zero, Int.add_zero]; exact (add_zero _).symm
  | n + 1 => by
      rw [Int.natCast_add, Int.natCast_one, ← Int.add_assoc, intCast_add_one,
        intCast_add_natCast k n, natCast_succ, add_assoc]

theorem intCast_neg_natCast_add (N : Nat) : (intCast (-(N : Int)) : R) + natCast N = 0 := by
  rw [← intCast_add_natCast, Int.add_left_neg]; rfl

theorem intCast_sub_natCast (k : Int) : ∀ n : Nat,
    (intCast (k - n) : R) = intCast k - natCast n
  | 0 => by rw [Int.natCast_zero, Int.sub_zero, natCast_zero, sub_zero]
  | n + 1 => by
      rw [show k - ((n + 1 : Nat) : Int) = k - (n : Int) - 1 by omega, intCast_sub_one,
        intCast_sub_natCast k n, natCast_succ, sub_def, sub_def, sub_def, neg_add, add_assoc]

theorem intCast_add (m : Int) : ∀ n : Int, (intCast (m + n) : R) = intCast m + intCast n
  | Int.ofNat k => intCast_add_natCast m k
  | Int.negSucc k => by
      rw [show m + Int.negSucc k = m - ((k + 1 : Nat) : Int) by simp only [Int.negSucc_eq]; omega,
        intCast_sub_natCast]
      rfl

theorem intCast_neg (m : Int) : (intCast (-m) : R) = -intCast m := by
  apply Eq.symm
  apply neg_eq_of_add_eq_zero
  rw [← intCast_add, Int.add_right_neg]; rfl

theorem exists_int_floor (x : R) : ∃ n : Int, intCast n ≤ x ∧ x < intCast n + 1 :=
  sorry

-- ## Part F: 位相と連続性

instance : TopologicalSpace R where
  IsOpen s := ∀ x ∈ s, ∃ ε, 0 < ε ∧ ∀ y, abs (y - x) < ε → y ∈ s
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

theorem isOpen_iff {s : Set R} :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε, 0 < ε ∧ ∀ y, abs (y - x) < ε → y ∈ s := Iff.rfl

def ball (x ε : R) : Set R := {y | abs (y - x) < ε}

theorem isOpen_ball (x ε : R) : IsOpen (ball x ε) :=
  sorry

theorem mem_ball_self {x ε : R} (h : 0 < ε) : x ∈ ball x ε := by
  show abs (x - x) < ε
  rw [abs_sub_self]; exact h

section Continuity

variable {X : Type} [TopologicalSpace X]

theorem continuous_of_forall {f : X → R}
    (h : ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (f y - f x) < ε) :
    Continuous f :=
  sorry

theorem forall_of_continuous {f : X → R} (hf : Continuous f) (x : X) {ε : R} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (f y - f x) < ε :=
  ⟨f ⁻¹' ball (f x) ε, hf _ (isOpen_ball _ _), mem_ball_self hε, fun _ hy => hy⟩

theorem continuous_id' : Continuous (fun x : R => x) :=
  continuous_of_forall fun x ε hε => ⟨ball x ε, isOpen_ball x ε, mem_ball_self hε, fun _ hy => hy⟩

theorem continuous_const (c : R) : Continuous (fun _ : X => c) :=
  continuous_of_forall fun _ _ hε =>
    ⟨Set.univ, isOpen_univ, trivial, fun _ _ => by rw [abs_sub_self]; exact hε⟩

theorem continuous_add {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) :=
  sorry

theorem continuous_neg {f : X → R} (hf : Continuous f) : Continuous (fun x => -f x) := by
  apply continuous_of_forall
  intro x ε hε
  obtain ⟨U, hU, hxU, hfU⟩ := forall_of_continuous hf x hε
  refine ⟨U, hU, hxU, fun y hy => ?_⟩
  have e : -f y - -f x = -(f y - f x) := by rw [sub_def, sub_def, neg_add]
  rw [e, abs_neg]; exact hfU y hy

theorem continuous_sub {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) := continuous_add hf (continuous_neg hg)

theorem continuous_mul {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) :=
  sorry

end Continuity

-- ## Part G: 閉区間

def Icc (a b : R) : Set R := {x | a ≤ x ∧ x ≤ b}

theorem finite_insert {I : Type} {J : Set I} (hJ : J.Finite) (i : I) :
    ({j | j ∈ J ∨ j = i} : Set I).Finite :=
  sorry

theorem finite_singleton {I : Type} (i : I) : ({j | j = i} : Set I).Finite :=
  ⟨1, fun _ => i, fun _ hj => ⟨⟨0, Nat.zero_lt_one⟩, hj.symm⟩⟩

theorem isCompact_Icc (a b : R) : IsCompact (Icc a b) :=
  sorry

theorem Icc_connected {a b : R} {U V : Set R} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : ∀ x ∈ Icc a b, x ∈ U ∨ x ∈ V) (hdisj : ∀ x ∈ Icc a b, x ∈ U → x ∈ V → False)
    (hab : a ≤ b) (ha : a ∈ U) : ∀ x ∈ Icc a b, x ∈ U :=
  sorry

noncomputable def finMin : (n : Nat) → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, g => min (g 0) (finMin n fun k => g k.succ)

theorem finMin_pos : ∀ (n : Nat) (g : Fin n → R), (∀ k, 0 < g k) → 0 < finMin n g
  | 0, _, _ => zero_lt_one
  | n + 1, _, h => lt_min (h 0) (finMin_pos n _ fun k => h k.succ)

theorem finMin_le : ∀ (n : Nat) (g : Fin n → R) (k : Fin n), finMin n g ≤ g k :=
  sorry

theorem lebesgue {a b : R} {I : Type} (U : I → Set R) (hU : ∀ i, IsOpen (U i))
    (hcov : Icc a b ⊆ (⋃ i, U i)) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ Icc a b, ∃ i, ∀ y, abs (y - x) < δ → y ∈ U i :=
  sorry

end CompleteOrderedField

#print axioms CompleteOrderedField.lebesgue
