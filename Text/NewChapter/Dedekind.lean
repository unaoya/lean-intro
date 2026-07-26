structure is_dedekind_cut {α : Type u} [LT α] [LE α] (A : α → Prop) where
  non_empty : ∃ a : α, A a
  not_all : ∃ a : α, ¬(A a)
  left_all : ∀ a b : α, a < b → A b → A a
  non_max : ∀ a : α, A a → ∃ b : α, a < b ∧ A b

def Real : Type :=
  {A : Rat → Prop // is_dedekind_cut A}

def incl (r : Rat) : Real where
  val x := x < r
  property := sorry
  -- property where
  -- non_empty := sorry
  -- not_all := sorry
  -- left_all := sorry
  -- non_max := sorry

instance : Zero Real where
  zero := incl 0

instance : One Real where
  one := incl 1

instance : Add Real where
  add A B :=
    ⟨fun r => ∃ a b : Rat, A.val a ∧ B.val b ∧ r = a + b,
    sorry⟩
