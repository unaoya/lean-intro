theorem A (a b c : Nat) (h₀ : a = b) (h₁ : b = c) : a = c :=
  calc
    a = b := h₀
    _ = c := h₁

theorem A' (a b c : Nat) (h₀ : a = b) (h₁ : b = c) : a = c := by simp [h₀, h₁]

theorem B (a b : Nat) : (a + 1) * b = a * b + b :=
  calc
    (a + 1) * b = a * b + 1 * b := Nat.right_distrib _ _ _
    _ = a * b + b := by simp [Nat.one_mul]

theorem C (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  calc
    (a + 1) * (b + 1) = a * (b + 1) + 1 * (b + 1) := by apply Nat.right_distrib
    _ = a * b + a + b + 1 := by simp [Nat.left_distrib, Nat.add_assoc]
