import MyProject.Numbers.Rational

-- 実数の型を定義し、完備アルキメデス順序体であることを示す。
-- まず有理数体を作る。有理数の型を定義し、順序体であることを示す。
-- 次にコーシー列を定義し、実数を定義する

-- 体のクラス

-- 順序体のクラス

-- section Ratとかnamespace Ratとか

def IsCauchy (f : Nat → Rat) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, m ≥ N ∧ n ≥ N → Rat.abs (f m - f n) < ε

def CauchySeq : Type := { f : Nat → Rat // IsCauchy f }

namespace CauchySeq

def add (f g : CauchySeq) : CauchySeq := ⟨λ n => f.val n + g.val n, sorry⟩

instance : Add CauchySeq := ⟨add⟩

def mul (f g : CauchySeq) : CauchySeq := ⟨λ n => f.val n * g.val n, sorry⟩

instance : Mul CauchySeq := ⟨mul⟩

def neg (f : CauchySeq) : CauchySeq := ⟨λ n => -f.val n, sorry⟩

instance : Neg CauchySeq := ⟨neg⟩

def inv (f : CauchySeq) : CauchySeq := ⟨λ n => Rat.inv (f.val n), sorry⟩

def div (f g : CauchySeq) : CauchySeq := ⟨λ n => f.val n / g.val n, sorry⟩

instance : Div CauchySeq := ⟨div⟩

instance (n : Nat) : OfNat CauchySeq n := ⟨⟨λ m => n, sorry⟩⟩

instance : NatCast CauchySeq := ⟨fun n => ⟨λ m => n, sorry⟩⟩

def sub (f g : CauchySeq) : CauchySeq := ⟨λ n => f.val n - g.val n, sorry⟩

instance : Sub CauchySeq := ⟨sub⟩

def nonneg (f : CauchySeq) : Prop := ∀ n, Rat.nonneg (f.val n)

instance : DecidablePred nonneg := by sorry

def le (f g : CauchySeq) : Prop := ∀ n, Rat.le (f.val n) (g.val n)

instance : LE CauchySeq := ⟨le⟩

instance : DecidableRel le := by sorry

-- instance (n : Nat) : OfNat CauchySeq n := ⟨⟨λ m => n, sorry⟩⟩

instance : LT CauchySeq := sorry

end CauchySeq

-- 実数の定義

def CSEq (f g : CauchySeq) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, n ≥ N → Rat.abs (f.val n - g.val n) < ε

theorem CSEq_eq : Equivalence CSEq := sorry

def CSsetoid : Setoid CauchySeq := ⟨CSEq, CSEq_eq⟩

def Real : Type := Quotient CSsetoid

namespace Real

def mk (f : CauchySeq) : Real := Quotient.mk CSsetoid f

instance : NatCast Real := ⟨fun n => mk n⟩

def add : Real → Real → Real := sorry

instance : Add Real := ⟨add⟩

def mul : Real → Real → Real := sorry

instance : Mul Real := ⟨mul⟩

def neg : Real → Real := sorry

instance : Neg Real := ⟨neg⟩

def div : Real → Real → Real := sorry

instance : Div Real := ⟨div⟩

instance : NatCast Real := ⟨fun n => Quotient.mk CSsetoid n⟩

instance (n : Nat) : OfNat Real n := sorry

def sub : Real → Real → Real := fun x y => add x (neg y)

instance : Sub Real := ⟨sub⟩

def nonneg : Real → Prop := Quotient.lift CauchySeq.nonneg sorry

instance : DecidablePred nonneg := by sorry

def le : Real → Real → Prop := fun x y => nonneg (y - x)

instance : LE Real := ⟨le⟩

instance : DecidableRel le := by sorry

instance : LT Real := sorry

instance : AddCommGroup Real :=
{
  zero := 0,
  add_assoc := sorry,
  add_comm := sorry,
  add_zero := sorry,
  zero_add := sorry,
  add_neg := sorry,
  neg_add := sorry
}

instance : MulCommMonoid Real :=
{
  one := sorry,
  mul_assoc := sorry,
  mul_comm := sorry,
  mul_one := sorry,
  one_mul := sorry
}

instance : CommRing Real :=
{
  left_distrib := sorry,
  right_distrib := sorry
}

instance : Field Real :=
{
  inv := sorry,
  mul_inv := sorry,
  inv_mul := sorry,
  nontrivial := sorry
}

instance : LinearOrderedField Real :=
{
  le := sorry,
  le_refl := sorry,
  le_asymm := sorry,
  le_trans := sorry,
  le_total := sorry,
  add_le_add := sorry,
  mul_pos := sorry
}

def abs (x : Real) : Real := Abs.abs x

-- 完備性
