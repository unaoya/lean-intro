def total (a b c : Nat) (d : Bool) : Nat :=
  if d then a + b + c + 1 else a + b + c

def total' (a b c : Nat) (d : Bool) : Nat :=
  match d with
  | true => a + b + c + 1
  | false => a + b + c

#check total

#eval total 1 2 3 true

#eval total' 1 2 3 false

theorem A (a b c : Nat) (h₀ : a = b) (h₁ : b = c) : a = c := Eq.trans h₀ h₁

#check Eq.trans

theorem B (a b : Nat) : (a + 1) * b = a * b + b :=
  Eq.trans (Nat.right_distrib a 1 b) (congrArg (fun x => a * b + x) (Nat.one_mul b))

theorem B' (a b : Nat) : (a + 1) * b = a * b + b :=
  Eq.trans (Nat.right_distrib _ _ _) (congrArg _ (Nat.one_mul _))

theorem B'' (a b : Nat) : (a + 1) * b = a * b + b :=
  have h₀ : (a + 1) * b = a * b + 1 * b := Nat.right_distrib _ _ _
  have h₁ : 1 * b = b := Nat.one_mul _
  have h₂ : a * b + 1 * b = a * b + b := congrArg (fun x => (a * b) + x) h₁
  Eq.trans h₀ h₂

theorem C (a b : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  Eq.trans
    (Eq.trans
      (B a (b + 1))
      (congrArg
        (fun x => x + (b + 1))
        (Eq.trans
          (Nat.left_distrib a b 1)
          (congrArg (fun x => a * b + x) (Nat.mul_one a)))))
    (Eq.symm (Nat.add_assoc (a * b + a) b 1))

theorem C' (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  Eq.trans
    (Eq.trans
      (B _ _)
      (congrArg
        (fun x => x + _)
        (Eq.trans
          (Nat.left_distrib _ _ _)
          (congrArg _ (Nat.mul_one _)))))
    (Eq.symm (Nat.add_assoc _ _ _))

theorem C'' (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  ((B _ _).trans
    (congrArg
      (fun x => x + _)
      ((Nat.left_distrib _ _ _).trans
        (congrArg _ (Nat.mul_one _))))).trans
    (Nat.add_assoc _ _ _).symm

theorem C''' (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  have h₀ : (a + 1) * (b + 1) = a * (b + 1) + (b + 1) := B _ _
  have h₁ : a * (b + 1) = a * b + a :=
    Eq.trans (Nat.left_distrib _ _ _) (congrArg _ (Nat.mul_one _))
  have h₂ : a * (b + 1) + (b + 1) = a * b + a + (b + 1) :=
    congrArg (fun x => x + _) h₁
  have h₃ : a * b + a + (b + 1) = a * b + a + b + 1 := Eq.symm (Nat.add_assoc _ _ _)
  Eq.trans (Eq.trans h₀ h₂) h₃

theorem C'''' (a : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 :=
  have h₀ : (a + 1) * (b + 1) = a * (b + 1) + (b + 1) := B _ _
  have h₁ : a * (b + 1) = a * b + a :=
    (Nat.left_distrib _ _ _).trans (congrArg _ (Nat.mul_one _))
  have h₂ : a * (b + 1) + (b + 1) = a * b + a + (b + 1) :=
    congrArg (fun x => x + _) h₁
  have h₃ : a * b + a + (b + 1) = a * b + a + b + 1 := (Nat.add_assoc _ _ _).symm
  (h₀.trans h₂).trans h₃

example (a b : Nat) : (a + 1) * b = a * b + b := by
  simp [Nat.right_distrib]
