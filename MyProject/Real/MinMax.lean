import MyProject.Real.Abs

noncomputable section

open Real Classical

-- min / max / fmax'

theorem min_pos (a b : Real) (h : 0 < a) (h' : 0 < b) : 0 < min a b := by
  show (0 : Real) < (if a ≤ b then a else b); split <;> assumption

theorem min_left_le (a b : Real) : min a b ≤ a := by
  show (if a ≤ b then a else b) ≤ a; split
  · exact le_refl a
  · rename_i h; exact (ne_le_lt a b h).1

theorem min_right_le (a b : Real) : min a b ≤ b := by
  show (if a ≤ b then a else b) ≤ b; split
  · rename_i h; exact h
  · exact le_refl b

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
          have : i < (m + 1 + 1) := Nat.lt_of_lt_of_le hi (Nat.le_succ_of_le (Nat.le_refl _))
          exact hf ⟨i, Nat.lt_of_lt_of_le this (Nat.le_refl _)⟩)
    · exact hf ⟨n, Nat.lt_succ_self n⟩

theorem fpred'_eq_f {n : Nat} (f : Range (n + 1) → Real) (k : Range (n + 1))
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
          ((le_total _ _).elim (absurd · hcond) id)

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

-- min
theorem min_eq_left {a b : Real} (h : a ≤ b) : min a b = a := by
  show (if a ≤ b then a else b) = a
  rw [if_pos h]

theorem min_eq_right {a b : Real} (h : b ≤ a) : min a b = b := by
  show (if a ≤ b then a else b) = b
  cases Classical.em (a ≤ b) with
  | inl h' => rw [if_pos h']; exact le_antisymm a b h' h
  | inr h' => rw [if_neg h']
