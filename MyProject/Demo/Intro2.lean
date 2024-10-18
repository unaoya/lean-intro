theorem A (a b c : Nat) (h₀ : a = b) (h₁ : b = c) : a = c := Eq.trans h₀ h₁

#check Eq.trans

theorem B (a b : Nat) : (a + 1) * b = a * b + b :=
  have h₀ : (a + 1) * b = a * b + 1 * b := Nat.right_distrib _ _ _
  have h₁ : 1 * b = b := Nat.one_mul _
  have h₂ : a * b + 1 * b = a * b + b := congrArg (fun x => (a * b) + x) h₁
  Eq.trans h₀ h₂

theorem B' (a b : Nat) : (a + 1) * b = a * b + b :=
  Eq.trans (Nat.right_distrib a 1 b) (congrArg (fun x => a * b + x) (Nat.one_mul b))

theorem B'' (a b : Nat) : (a + 1) * b = a * b + b :=
  Eq.trans (Nat.right_distrib _ _ _) (congrArg (fun x => a * b + x) (Nat.one_mul _))

theorem C (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  have h₀ : (a + 1) * (b + 1) = a * (b + 1) + (b + 1) := B _ _
  have h₁ : a * (b + 1) = a * b + a := sorry
  have h₂ : a * (b + 1) + (b + 1) = a * b + a + (b + 1) := congrArg (fun x => x + (b + 1)) h₁
  have h₃ : a * b + a + (b + 1) = a * b + a + b + 1 := Eq.symm (Nat.add_assoc _ _ _)
  Eq.trans (Eq.trans h₀ h₂) h₃

example (a b : Nat) : (a + 1) * b = a * b + b := by
  simp [Nat.right_distrib]

example (a b c : Nat) (h₀ : a = b) (h₁ : b = c) : a = c := by simp [h₀, h₁]

example (a b c d : Nat) (h₀ : a = b) (h₁ : b = c) (h₂ : c = d) : a = d := by simp [h₀, h₁, h₂]

example (a b c d : Nat) (h₀ : a = b) (h₁ : b = c) (h₂ : c = d) : a = d :=
  calc
    a = b := h₀
    _ = c := h₁
    _ = d := h₂

example (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 := by
  simp [Nat.right_distrib, Nat.left_distrib]
  sorry
