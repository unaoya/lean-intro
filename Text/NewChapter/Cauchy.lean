def sequence (α : Type u) : Type u := Nat → α

def const_seq {α : Type u} (a : α) : sequence α :=
  fun _ => a

class Dist (α : Type u) where
  dist : α → α → Rat

def is_cauchy {α : Type u} (seq : sequence α) [Dist α] : Prop :=
  ∀ ε, ∃ N, ∀ n m, n ≥ N ∧ m ≥ N → Dist.dist (seq n) (seq m) ≤ ε

theorem const_is_cauchy {α : Type u} (a : α) [Dist α] : is_cauchy (const_seq a) :=
  sorry

def cauchy_seq (α : Type u) [Dist α] : Type u :=
  {seq : sequence α // is_cauchy seq}

instance : Dist Rat where
  dist x y := max (x - y) (y - x)

def Real : Type := cauchy_seq Rat

instance : Zero Real where
  zero := ⟨const_seq 0, const_is_cauchy 0⟩

instance : One Real where
  one := ⟨const_seq 1, const_is_cauchy 1⟩
