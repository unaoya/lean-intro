import MyProject.Numbers.Continuity
import MyProject.Numbers.NatNum

noncomputable section

open Real Classical

-- 実数の計算とかsummationの計算とか。抽象化して準備しておく。

theorem summation_smul (n : Nat) (f : Range n → Real) (c : Real) :
  Sumation n (fun i ↦ c * f i) = c * Sumation n f := by
  sorry

theorem sub_self (a : Real) : a - a = 0 := by
  sorry

theorem add_sub_cancel (a b : Real) : a + b - a = b := by
  sorry

theorem add_sub_add (a b c d : Real) : a + b - (c + d) = (a - c) + (b - d) := by
  sorry

theorem add_mul (a b c : Real) : (a + b) * c = a * c + b * c := by
  sorry

theorem neg_mul (a b : Real) : -a * b = -(a * b) := by
  sorry

theorem add_neg_sub (a b : Real) : a + -b = a - b := by
  sorry

theorem mul_div_cancel (a b : Real) : a * b / b = a := by
  sorry

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by
  sorry

theorem half_add (a : Real) : a / 2 + a / 2 = a := by
  sorry

theorem zero_lt_one : (0 : Real) < 1 := by
  sorry

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / 2 := by
  sorry

theorem min_pos (a b : Real) (h : 0 < a) (h' : 0 < b) : 0 < min a b := by
  sorry

theorem mul_nonneg (a b : Real) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b := by
  sorry

theorem Real.le_of_lt {a b : Real} : a < b → a ≤ b := by
  sorry

theorem le_sub (a b : Real) : 0 ≤ a - b ↔ a ≤ b := by
  sorry

theorem pos_iff_lt (a b : Real) : a < b ↔ 0 < b - a := by
  sorry

theorem lt_le_trans (a b c : Real) : a < b → b ≤ c → a < c := by
  sorry

theorem le_lt_trans {a b c : Real} : a ≤ b → b < c → a < c := by
  sorry

theorem min_left_le (a b : Real) : min a b ≤ a := by
  sorry

theorem min_right_le (a b : Real) : min a b ≤ b := by
  sorry

theorem lt_add_lt (a b c d : Real) : a < b → c < d → a + c < b + d := by
  sorry

instance : Max Real := sorry

#check (inferInstance : Max Real)

theorem le_abs (a : Real) : a ≤ abs a := by
  sorry

theorem neg_le_abs (a : Real) : -a ≤ abs a := by
  sorry

theorem abs_le (a b : Real) (h₀ : -a ≤ b) (h₁ : a ≤ b) : abs a ≤ b := by
  sorry

theorem abs_zero : (0 : Real).abs = 0 := by
  sorry

theorem abs_triangle (a b : Real) : abs (a + b) ≤ abs a + abs b := by
  sorry

theorem neg_sub_neg_abs (a b : Real) : abs (-a - -b) = abs (a - b) := by
  sorry

theorem addtive_summation (n : Nat) (f g : Range n → Real) :
  Sumation n (fun i ↦ f i + g i) = Sumation n f + Sumation n g := by
  sorry

theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
  Sumation n f = Sumation n g := by
  sorry

theorem neg_summation (n : Nat) (f : Range n → Real) :
  -Sumation n f = Sumation n (fun i ↦ -f i) := by
  sorry

theorem sumation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
  0 ≤ Sumation n f := by
  sorry

def fpred' (n : Nat) (f : Range n.succ → Real) : Range n → Real :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ n => fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n.succ)⟩

def fmax' (n : Nat) (f : Range n → Real) : Real :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => max (f ⟨n, Nat.lt_succ_self n⟩) (fmax' n (fpred' n f))

theorem fmax'_lt (n : Nat) (f : Range n → Real) (a : Real) : (∀ i, f i < a) → fmax' n f < a := by
  sorry

@[simp]
theorem sub_zero_abs (x : Real) : (x - 0).abs = x.abs := sorry

instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le := sorry

instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt := sorry

instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt := sorry

theorem nez_of_abs_pos {x : Real} (h : 0 < x.abs) : x ≠ 0 := by sorry

theorem pos_abs {x : Real} (h : 0 < x) : x.abs = x := by sorry

theorem abs_nonneg {x : Real} : 0 ≤ x.abs := by sorry

theorem le_trans {a b c : Real} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  apply Trans.trans h₁ h₂

theorem div_abs_le {a b c : Real} (h : a.abs ≤ b.abs) : (a / c).abs ≤ (b / c).abs := by sorry

example (a b : Real) : a * b / b = a := by
  rw [mul_div_cancel]

theorem aux (a b c : Real) : a * (b + c - b) / c = a := sorry

def InInterval (a b : Real) (x : Real) : Prop :=
  if a ≤ b then a ≤ x ∧ x ≤ b else b ≤ x ∧ x ≤ a

def InInterval_abs {x h t : Real} : InInterval x (x + h) t → (t - x).abs ≤ h.abs := by
  sorry

axiom archimedean (a : Real) : ∃ n : Nat, a < n

def ceil (a : Real) : Nat := min (fun n => a < n) (archimedean a)

theorem ne_le_lt (a b : Real) : ¬a ≤ b → b < a := by
  sorry

theorem neg_neg (a : Real) : -(-a) = a := by
  sorry

theorem neg_neg_pos (a : Real) : a < 0 → 0 < -a := by
  sorry

theorem neg_neg_nonneg (a : Real) : a ≤ 0 → 0 ≤ -a := by
  sorry

theorem zero_val (n : Nat) : (⟨0, sorry⟩ : Range n).val = (0 : Real) := by
  sorry

theorem range_val (n k : Nat) : (⟨k, sorry⟩ : Range n).val = (k : Real) := by
  sorry

theorem zero_mul' (a : Real) : 0 * a = 0 := by
  sorry

theorem zero_div (a : Real) : 0 / a = 0 := by
  sorry

theorem add_zero (a : Real) : a + 0 = a := by
  sorry

theorem lt_neq (a b : Real) : a < b → a ≠ b := by
  sorry

theorem sub_add_neg (a b : Real) : a - b = a + -b := by
  sorry

theorem right_le_pos_add_pos (a b : Real) : 0 ≤ a → 0 ≤ b → b ≤ (a + b).abs := by
  sorry

theorem add_left_lt (a b c : Real) : b < c → a + b < a + c := by
  sorry

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c := by
  sorry

theorem mul_right_lt (a b c : Real) : 0 < c → a < b → a * c < b * c := by
  sorry

theorem pos_ceil_pos (a : Real) : 0 < a → (0 : Real) < ceil a := by
  sorry

theorem pos_sub_iff (a b : Real) : a < b ↔ 0 < b - a := by
  sorry

theorem lt_cast (n m : Nat) : n < m → (n : Real) < m := by
  sorry

theorem incl_lt_addone (n : Nat) (i : Range n) : (incl i).val < (addone i).val := by
  sorry

theorem pos_mul_pos (a b : Real) : 0 < a → 0 < b → 0 < a * b := by
  sorry

theorem zero_lt_two : (0 : Real) < 2 := by
  sorry

theorem mul_div_cancel' (a b : Real) : a * b / a = b := by
  sorry

theorem add_sub_cancel' (a b : Real) : a + (b - a) = b := by
  sorry

theorem le_refl (a : Real) : a ≤ a := by
  sorry

theorem add_sub_add' (a b c : Real) : a + b - (a + c) = (b - c) := by
  sorry

theorem mul_sub_mul (a b c : Real) : a * b - c * b = (a - c) * b := by
  sorry

theorem cast_incl_val (n : Nat) (k : Range n) : ((incl k).val : Real) = (k.val : Real) := by
  sorry

theorem cast_addone_val (n : Nat) (k : Range n) : ((addone k).val : Real) = (k.val : Real) + 1 := by
  sorry

theorem one_mul (a : Real) : 1 * a = a := by
  sorry

theorem ceil_lt (a : Real) : a < ceil a := by
  sorry

theorem div_lt_iff (a b c : Real) (bpos : 0 < b) (cpos : 0 < c) : a / b < c ↔ a / c < b := by
  sorry

theorem lt_trans (a b c : Real) : a < b → b < c → a < c := by
  sorry

theorem pos_div_pos (a b : Real) : 0 < a → 0 < b → 0 < a / b := by
  sorry
