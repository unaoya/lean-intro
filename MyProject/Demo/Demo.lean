def my_first_theorem : 1 = 1 :=
  Eq.refl 1

def n : Nat := 1

def twice : Nat → Nat :=
  fun n ↦ n + n

def twice' (n : Nat) : Nat :=
  n + n

#check n
#check twice
#check twice'
#check Eq.refl 1
#check Eq.refl

#check Nat
#check Type

def total (a b c : Nat)
  (bag : Bool) : Nat
  := a * 100 + b * 50 +
    c * 200 + if bag then 10 else 0

#eval total 1 2 3 true

theorem A (a b c : Nat)
  (h₀ : a = b) (h₁ : b = c)
  : a = c := Eq.trans h₀ h₁

#check @Eq Nat

theorem zero_is_min : ∀ n : Nat, 0 ≤ n
  :=
  fun n => Nat.zero_le n

#check Nat.zero_le
#check Nat.zero_le 1

#check False
#check False.elim

#check Prop

variable (α β : Type)

#check α → Prop

variable (f : (α → Prop) → Prop)

#check ∀ b : α → Prop, f b
