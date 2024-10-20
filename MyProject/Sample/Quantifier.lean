theorem zero_is_min : ∀ n : Nat, 0 ≤ n := fun n ↦ Nat.zero_le n

#check Nat.zero_le

-- protected inductive Nat.le (n : Nat) : Nat → Prop
--   /-- Less-equal is reflexive: `n ≤ n` -/
--   | refl     : Nat.le n n
--   /-- If `n ≤ m`, then `n ≤ m + 1`. -/
--   | step {m} : Nat.le n m → Nat.le n (succ m)

-- theorem Nat.zero_le : (n : Nat) → LE.le 0 n
--   | zero   => Nat.le.refl
--   | succ n => Nat.le.step (zero_le n)

-- protected inductive Nat.le (n : Nat) : Nat → Prop
--   /-- Less-equal is reflexive: `n ≤ n` -/
--   | refl     : Nat.le n n
--   /-- If `n ≤ m`, then `n ≤ m + 1`. -/
--   | step {m} : Nat.le n m → Nat.le n (succ m)

-- protected theorem one_lt_two : 1 < 2 := Nat.succ_lt_succ Nat.zero_lt_one

#check Nat.succ_lt_succ

-- theorem succ_lt_succ {n m : Nat} : n < m → succ n < succ m := succ_le_succ

-- theorem Nat.succ_le_succ : LE.le n m → LE.le (succ n) (succ m)
--   | Nat.le.refl   => Nat.le.refl
--   | Nat.le.step h => Nat.le.step (succ_le_succ h)

#check Nat.zero_lt_one

-- protected theorem zero_lt_one : 0 < (1:Nat) :=
--   zero_lt_succ 0

-- theorem Nat.zero_lt_succ (n : Nat) : LT.lt 0 (succ n) :=
--   succ_le_succ (zero_le n)

-- theorem Nat.zero_le : (n : Nat) → LE.le 0 n
--   | zero   => Nat.le.refl
--   | succ n => Nat.le.step (zero_le n)

theorem one_not_max : ∃ m, 1 < m :=
  ⟨2, Nat.one_lt_two⟩

theorem one_not_max' (n : Nat) : ∃ m, n < m :=
  Exists.intro (n + 1) (Nat.lt_succ_self n)

theorem no_max : ∀ n : Nat,  ∃ m : Nat, n < m :=
  fun n => ⟨(n + 1), (Nat.lt_succ_self n)⟩

theorem no_max' (n : Nat) : ∃ m, n < m :=
  ⟨(n + 1), (Nat.lt_succ_self n)⟩

-- example (n : Nat) : n < Nat.succ n := Nat.le_refl (Nat.succ n)

-- protected def Nat.lt (n m : Nat) : Prop :=
--   Nat.le (succ n) m
