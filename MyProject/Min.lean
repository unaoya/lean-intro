-- theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) :
--     s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
--   | ⟨a, ha⟩ => show ∃ b ∈ s, ∀ x ∈ s, ¬r x b from
--     Acc.recOn (H.apply a) (fun x _ IH =>
--         not_imp_not.1 fun hne hx => hne <| ⟨x, hx, fun y hy hyx => hne <| IH y hyx hy⟩)
--       ha

-- example {r : α → α → Prop} (H : WellFounded r) (s : Set α) (hs : s.Nonempty) :
--     ∃ a ∈ s, ∀ x ∈ s, ¬r x a := by
--   rcases hs with ⟨a, ha⟩
--   show ∃ b ∈ s, ∀ x ∈ s, ¬r x b
--   let motive (y : α) (_ : Acc r y) := y ∈ s → ∃ b ∈ s, ∀ x ∈ s, ¬r x b
--   apply @Acc.recOn α r motive a (H.apply a)
--     (fun x _ IH => not_imp_not.1 fun hne hx => hne ⟨x, hx, fun y hy hyx => hne (IH y hyx hy)⟩)
--   exact ha


-- example (s : Set Nat) (hs : s.Nonempty) :
--     ∃ a ∈ s, ∀ x ∈ s, ¬(x < a) := by
--   rcases hs with ⟨a, ha⟩
--   let motive (y : Nat) := y ∈ s → ∃ b ∈ s, ∀ x ∈ s, ¬(x < b)
--   let n := a
--   let (ind : ∀ n, (∀ m, m < n → motive m) → motive n) :=
--     fun n IH => (fun h => sorry)
--   have h := @Nat.strongInductionOn motive n ind
--   exact h ha


theorem has_min (p : Nat → Prop) (hp : ∃ n, p n) :
    ∃ a, p a ∧ ∀ x, p x → ¬(x < a) := by
  rcases hp with ⟨a, ha⟩
  let motive (y : Nat) := p y → ∃ b, p b ∧ ∀ x, p x → ¬(x < b)
  let (ind : ∀ n, (∀ m, m < n → motive m) → motive n) :=
    fun n IH => (fun h => ?h)
  have h := @Nat.strongRecOn motive a ind
  exact h ha
  by_cases h : ∀ x, p x → ¬(x < a)
  sorry
  sorry


noncomputable def min (p : Nat → Prop) (hp : ∃ n, p n) : Nat :=
  Classical.choose (has_min p hp)
