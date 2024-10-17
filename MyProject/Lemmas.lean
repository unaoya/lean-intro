import MyProject.Real
import MyProject.NatNum

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

theorem Real.le_of_lt (a b : Real) : a < b → a ≤ b := by
  sorry

theorem le_sub (a b : Real) : 0 ≤ a - b ↔ a ≤ b := by
  sorry

theorem pos_iff_lt (a b : Real) : a < b ↔ 0 < b - a := by
  sorry

theorem lt_le_trans (a b c : Real) : a < b → b ≤ c → a < c := by
  sorry

theorem le_lt_trans (a b c : Real) : a ≤ b → b < c → a < c := by
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
