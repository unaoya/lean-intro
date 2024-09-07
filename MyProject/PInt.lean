import MyProject.NZInt

-- IntとNZIntのペアの型PIntを定義する

@[ext]
structure PInt where
  num : Int
  den : NZInt

namespace PInt

instance (n : Nat) : OfNat PInt n := ⟨⟨n, ⟨1, by simp⟩⟩⟩

@[simp]
theorem eq_iff : ∀ a b : PInt, a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := by
  exact fun a b ↦ PInt.ext_iff

-- PIntに同値関係を定義する
-- 分数が一致すること
def fracEq (a b : PInt) : Prop := a.1 * b.2.val = a.2.val * b.1

-- これが同値関係であることを確かめる。
theorem fracEq_refl (a : PInt) : fracEq a a := by
  rw [fracEq, Int.mul_comm]

theorem fracEq_symm {a b : PInt} (h : fracEq a b) : fracEq b a := by
  rw [fracEq, Int.mul_comm] at *
  exact h.symm

theorem aux (a b c d : Int) : a * b * c * d = a * d * b * c := by
  rw [Int.mul_assoc _ b c, Int.mul_assoc, Int.mul_comm _ d, ← Int.mul_assoc, Int.mul_assoc _ b c]

theorem aux' (a b c : Int) (h : a * c = b * c) (hc : c ≠ 0) : a = b := by
  exact Int.eq_of_mul_eq_mul_right hc h

theorem fracEq_trans {a b c : PInt} (h1 : fracEq a b) (h2 : fracEq b c) : fracEq a c := by
  rw [fracEq] at *
  by_cases h : b.num = 0
  · rw [h] at h1 h2
    simp at *
    have h₀ : a.num = 0 := by
      rw [Int.mul_eq_zero] at h1
      rcases h1 with h1 | h1
      exact h1
      have := b.den.property
      exact False.elim (this h1)
    have h₁ : c.num = 0 := by
      have h2 := h2.symm
      rw [Int.mul_eq_zero] at h2
      rcases h2 with h2 | h2
      have := b.den.property
      exact False.elim (this h2)
      exact h2
    rw [h₀, h₁]
    simp
  · have : a.1 * b.2.val * b.1 * c.2.val = a.2.val * b.1 * b.2.val * c.1 := by
      rw [h1, Int.mul_assoc, h2, ← Int.mul_assoc]
    rw [Int.mul_comm] at this
    rw [aux, Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm _ b.num, ← Int.mul_assoc, Int.mul_comm c.den.val] at this
    apply aux' _ _ _ (aux' _ _ _ this b.den.property) h

theorem fracEq_Eq : Equivalence fracEq :=
  {
    refl := fracEq_refl
    symm := fracEq_symm
    trans := fracEq_trans
  }

instance : HasEquiv PInt where
  Equiv := fracEq

theorem Equiv_iff (a b : PInt) : a ≈ b ↔ fracEq a b := by rfl

@[simp]
theorem equiv (a b : PInt) : a ≈ b ↔ a.1 * b.2.val = a.2.val * b.1 := by rfl

def nonneg (a : PInt) : Prop := 0 ≤ a.1 * a.2.val

@[simp]
theorem nonneg_def (a : PInt) : nonneg a ↔ 0 ≤ a.1 * a.2.val := by rfl

instance : DecidablePred nonneg := by
  intro a
  rw [nonneg]
  exact Int.decLe 0 (a.num * a.den.val)

theorem nonneg_wd (a b : PInt) (h : a ≈ b) : nonneg a = nonneg b := by
  ext
  simp
  simp at h
  constructor
  · intro h'
    by_cases h₀ : 0 ≤ b.1
    sorry
    sorry
  · sorry

def add (a b : PInt) : PInt := ⟨a.1 * b.2.val + b.1 * a.2.val, a.2 * b.2⟩

instance : Add PInt := ⟨add⟩

@[simp]
theorem add_num (a b : PInt) : (a + b).1 = a.1 * b.2.val + b.1 * a.2.val := rfl

@[simp]
theorem add_den (a b : PInt) : (a + b).2 = a.2 * b.2 := rfl

theorem add_comm (a b : PInt) : a + b = b + a := by
  simp
  constructor
  · rw [Int.add_comm]
  · rw [Int.mul_comm]

theorem add_wd' (a b c : PInt) (h : a ≈ b) : a + c ≈ b + c := by
  simp at *
  rw [Int.add_mul, Int.mul_add, Int.mul_assoc]
  rw [← Int.mul_assoc c.2.val, Int.mul_comm c.2.val, Int.mul_assoc, ← Int.mul_assoc, h, Int.mul_assoc, ← Int.mul_assoc b.1, Int.mul_comm b.1, Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm b.1]
  rw [Int.add_left_inj]
  rw [Int.mul_comm c.1, Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc c.2.val c.1, Int.mul_comm c.2.val c.1, Int.mul_assoc, Int.mul_comm c.2.val b.2.val]

theorem add_wd (a b c d : PInt) (h1 : a ≈ b) (h2 : c ≈ d) : a + c ≈ b + d := by
  have h₀ : a + c ≈ b + c := add_wd' a b c h1
  have h₁ : b + c ≈ b + d := by rw [add_comm, add_comm _ d]; exact add_wd' c d b h2
  rw [Equiv_iff] at *
  apply fracEq_trans h₀ h₁

def neg (a : PInt) : PInt := ⟨-a.1, a.2⟩

instance : Neg PInt := ⟨neg⟩

@[simp]
theorem neg_num (a : PInt) : (-a).1 = -a.1 := rfl

@[simp]
theorem neg_den (a : PInt) : (-a).2 = a.2 := rfl

theorem neg_wd (a b : PInt) (h : a ≈ b) : -a ≈ -b := by
  simp at *
  rw [h]

-- def sub (a b : PInt) : PInt := a + -b

-- instance : Sub PInt := ⟨sub⟩

-- theorem sub_def (a b : PInt) : a - b = a + -b := rfl

-- @[simp]
-- theorem sub_add_neg (a b : PInt) : a - b = a + -b := rfl

-- @[simp]
-- theorem sub_num (a b : PInt) : (a - b).1 = a.1 * b.2.val - b.1 * a.2.val := by
--   simp
--   rw [Int.sub_eq_add_neg.symm]

-- @[simp]
-- theorem sub_den (a b : PInt) : (a - b).2 = a.2 * b.2 := rfl

-- theorem sub_wd (a b c d : PInt) (h1 : a ≈ b) (h2 : c ≈ d) : a - c ≈ b - d := by
--   rw [PInt.sub_def, PInt.sub_def]
--   exact PInt.add_wd _ _ _ _ h1 (neg_wd _ _ h2)

def mul (a b : PInt) : PInt := ⟨a.1 * b.1, a.2 * b.2⟩

instance : Mul PInt := ⟨mul⟩

@[simp]
theorem mul_num (a b : PInt) : (a * b).1 = a.1 * b.1 := rfl

@[simp]
theorem mul_den (a b : PInt) : (a * b).2 = a.2 * b.2 := rfl

theorem mul_comm (a b : PInt) : a * b = b * a := by
  simp
  rw [Int.mul_comm, Int.mul_comm _ b.2.val]
  exact ⟨rfl, rfl⟩

theorem mul_wd' (a b c : PInt) (h : a ≈ b) : a * c ≈ b * c := by
  simp at *
  rw [Int.mul_assoc, ← Int.mul_assoc c.1, Int.mul_comm c.1, ← Int.mul_assoc, ← Int.mul_assoc, h, Int.mul_assoc, Int.mul_assoc, Int.mul_comm c.1, ← Int.mul_assoc b.1, Int.mul_comm b.1, Int.mul_assoc, ← Int.mul_assoc]

theorem mul_wd (a b c d : PInt) (h1 : a ≈ b) (h2 : c ≈ d) : a * c ≈ b * d := by
  have h₀ : a * c ≈ b * c := mul_wd' a b c h1
  have h₁ : b * c ≈ b * d := by rw [mul_comm, mul_comm _ d]; exact mul_wd' c d b h2
  rw [Equiv_iff] at *
  apply fracEq_trans h₀ h₁

def inv (a : PInt) : PInt := if h : a.1 ≠ 0 then ⟨a.2.val, ⟨a.1, h⟩⟩ else ⟨0, ⟨1, by simp⟩⟩

@[simp]
theorem inv_nonzero (a : PInt) (h : a.1 ≠ 0) : inv a = ⟨a.2.val, ⟨a.1, h⟩⟩ := by
  simp [inv, h]

@[simp]
theorem inv_zero (a : PInt) (h : a.1 = 0) : inv a = ⟨0, ⟨1, by simp⟩⟩ := by
  simp [inv, h]

@[simp]
theorem inv_num (a : PInt) : (inv a).1 = if a.1 ≠ 0 then a.2.val else 0 := by
  by_cases h : a.1 ≠ 0
  · rw [if_pos h, inv_nonzero a h]
  · rw [if_neg h]
    simp at h
    rw [inv_zero a h]

@[simp]
theorem inv_den (a : PInt) : (inv a).2 = if h : a.1 ≠ 0 then ⟨a.1, h⟩ else ⟨1, by simp⟩ := by
  by_cases h : a.1 ≠ 0
  sorry
  sorry

theorem inv_wd (a b : PInt) (h : a ≈ b) : inv a ≈ inv b := by
  sorry

end PInt
