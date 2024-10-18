-- 0でない整数の型をIntの部分型として定義する
def NZInt := { n : Int // n ≠ 0}

namespace NZInt

def mul (a b : NZInt) : NZInt := ⟨a.val * b.val, Int.mul_ne_zero a.property b.property⟩

instance : Mul NZInt := ⟨mul⟩

@[simp]
theorem eq_iff (a b : NZInt) : a = b ↔ a.val = b.val := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply Subtype.eq
    exact h

@[simp]
theorem mul_val (a b : NZInt) : (a * b).val = a.val * b.val := rfl

theorem mul_comm (a b : NZInt) : a * b = b * a := by
  simp
  exact Int.mul_comm a.val b.val

end NZInt
