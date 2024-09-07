class AddCommGroup (α : Type) extends Add α, Neg α where
  zero : α
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a, a + zero = a
  zero_add : ∀ a, zero + a = a
  add_neg : ∀ a, a + -a = zero
  neg_add : ∀ a, -a + a = zero

class MulCommMonoid (α : Type) extends Mul α where
  one : α
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  mul_one : ∀ a, a * one = a
  one_mul : ∀ a, one * a = a

class CommRing (α : Type) extends AddCommGroup α, MulCommMonoid α where
  left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c)
  right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c)

class Field (α : Type) extends CommRing α where
  inv : α → α
  mul_inv : ∀ a, a ≠ zero → a * inv a = one
  inv_mul : ∀ a, a ≠ zero → inv a * a = one
  nontrivial : zero ≠ one

class LinearOrderedField (α : Type) extends Field α, LE α where
  le_refl : ∀ a : α, a ≤ a
  le_asymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  add_le_add : ∀ a b c : α, a ≤ b → a + c ≤ b + c
  mul_pos : ∀ a b : α, zero ≤ a → zero ≤ b → zero ≤ a * b

class NonNeg (α : Type) where
  nonneg : α → Prop

class Abs (α : Type) where
  abs : α → α

variable {α : Type} [LinearOrderedField α]

instance : NonNeg α := sorry

instance (a : α) : Decidable (NonNeg.nonneg a) := sorry

instance : Sub α := sorry

instance : Div α := sorry

instance : LT α := sorry

instance (n : Nat) : OfNat α n := sorry

instance : NatCast α := sorry

instance : Min α := sorry

instance : Abs α := ⟨fun a => min a (-a)⟩

class CompletLinearOrderedField (α : Type) extends LinearOrderedField α where
