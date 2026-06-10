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

variable {α : Type} [Field α]

instance : Sub α := ⟨fun a b => a + -b⟩

instance : Div α := ⟨fun a b => a * Field.inv b⟩

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

-- NatCast for LinearOrderedField (no OfNat dependency)
section NatCastDef
variable {α : Type} [LinearOrderedField α]

noncomputable def natCastOfField : Nat → α
  | 0 => AddCommGroup.zero
  | 1 => MulCommMonoid.one
  | Nat.succ (Nat.succ n) => natCastOfField (Nat.succ n) + MulCommMonoid.one

noncomputable instance instNatCastLOF : NatCast α := ⟨natCastOfField⟩
end NatCastDef

variable {α : Type} [LinearOrderedField α] [OfNat α 0]

instance : NonNeg α := ⟨fun a => 0 ≤ a⟩

noncomputable instance (a : α) : Decidable (NonNeg.nonneg a) := Classical.propDecidable _

instance : LT α := ⟨fun a b => a ≤ b ∧ a ≠ b⟩

noncomputable instance : DecidableRel (LE.le : α → α → Prop) := fun _ _ => Classical.propDecidable _

noncomputable instance : Min α := ⟨fun a b => if a ≤ b then a else b⟩

noncomputable instance : Max α := ⟨fun a b => if a ≤ b then b else a⟩

noncomputable instance : Abs α := ⟨fun a => max a (-a)⟩

class CompletLinearOrderedField (α : Type) extends LinearOrderedField α where
