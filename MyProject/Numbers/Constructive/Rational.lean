import MyProject.Numbers.Structure
import MyProject.Numbers.PInt

def setoid_rat : Setoid PInt := ⟨PInt.fracEq, PInt.fracEq_Eq⟩

def Rat : Type := Quotient setoid_rat

namespace Rat

def mk (a : Int) (b : NZInt) : Rat := Quotient.mk setoid_rat ⟨a, b⟩

instance (n : Nat) : OfNat Rat n := ⟨Quotient.mk setoid_rat ⟨n, ⟨1, by simp⟩⟩⟩

instance : NatCast Rat := ⟨fun n => Quotient.mk setoid_rat ⟨n, ⟨1, by simp⟩⟩⟩

def add : Rat → Rat → Rat := Quotient.lift₂ (fun a b => Quotient.mk _ (a + b)) (fun a b c d h h' => Quotient.sound (PInt.add_wd a c b d h h'))

instance : Add Rat := ⟨add⟩

def neg : Rat → Rat := Quotient.lift (fun a => Quotient.mk _ (-a)) (fun a b h => Quotient.sound (PInt.neg_wd a b h))

instance : Neg Rat := ⟨neg⟩

def mul : Rat → Rat → Rat := Quotient.lift₂ (fun a b => Quotient.mk _ (a * b)) (fun a b c d h h' => Quotient.sound (PInt.mul_wd a c b d h h'))

instance : Mul Rat := ⟨mul⟩

def inv : Rat → Rat := Quotient.lift (fun a => Quotient.mk _ (PInt.inv a)) (fun a b h => Quotient.sound (PInt.inv_wd a b h))

instance : AddCommGroup Rat :=
{
  zero := 0,
  add_assoc := sorry,
  add_comm := sorry,
  add_zero := sorry,
  zero_add := sorry,
  add_neg := sorry,
  neg_add := sorry
}

instance : MulCommMonoid Rat :=
{
  one := 1,
  mul_assoc := sorry,
  mul_comm := sorry,
  mul_one := sorry,
  one_mul := sorry
}

instance : CommRing Rat :=
{
  left_distrib := sorry,
  right_distrib := sorry
}

instance : Field Rat :=
{
  inv := inv,
  mul_inv := sorry,
  inv_mul := sorry,
  nontrivial := by
    have h₀ : (AddCommGroup.zero : Rat) = 0 := rfl
    have h₁ : (MulCommMonoid.one : Rat) = 1 := rfl
    rw [h₀, h₁]
    sorry
}

def nonneg : Rat → Prop := Quotient.lift PInt.nonneg PInt.nonneg_wd

instance [hf : DecidablePred PInt.nonneg] : DecidablePred nonneg := by
  exact (fun q ↦ Quot.recOnSubsingleton (motive := fun _ ↦ Decidable _) q hf)

-- example : nonneg (Quotient.mk setoid_rat ⟨1, ⟨2, by simp⟩⟩) := by
--   rw [nonneg]
--   have : PInt.nonneg (1, ⟨2, by simp⟩) := by
--     rw [PInt.nonneg]
--     simp
--   exact this

def le : Rat → Rat → Prop := fun x y => nonneg (y - x)

instance : LE Rat := ⟨le⟩

instance : DecidableRel le := by
  intro a b
  rw [le]
  have : DecidablePred (fun a => nonneg (b - a)) := inferInstance
  exact inferInstance

instance (n : Nat) : OfNat Rat n := ⟨Quotient.mk setoid_rat ⟨n, ⟨1, by simp⟩⟩⟩

-- def lt : Rat → Rat → Prop := fun x y => nonneg (y - x) ∧ x ≠ y

-- instance : LT Rat := ⟨lt⟩

-- instance : Min Rat := @minOfLe _ _ (inferInstance : DecidableRel Rat.le)

-- @[simp]
-- theorem min_def (x y : Rat) : min x y = if Rat.le x y then x else y := rfl

-- @[simp]
-- theorem min_def' (x y : Rat) (h : x ≤ y) : min x y = x := by
--   simp
--   intro h'
--   contradiction

-- -- 絶対値の定義
-- -- absもクラスある？
-- def abs (x : Rat) : Rat := min x (-x)

instance : LinearOrderedField Rat :=
{
  le := le,
  le_refl := sorry,
  le_asymm := sorry,
  le_trans := sorry,
  le_total := sorry,
  add_le_add := sorry,
  mul_pos := sorry
}

#check (inferInstance : Abs Rat)

#check Abs.abs (1 : Rat)

def abs (x : Rat) : Rat := Abs.abs x

end Rat
