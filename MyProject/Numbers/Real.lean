import MyProject.Numbers.Structure

-- 実数の公理的定義
-- Real を完備線形順序体として公理的に導入する

axiom Real : Type

-- Real は線形順序体
axiom Real.instLOF : LinearOrderedField Real

noncomputable instance : LinearOrderedField Real := Real.instLOF

-- OfNat: 0 と 1 を直接定義し、AddCommGroup.zero / MulCommMonoid.one と定義的に一致させる
noncomputable instance : OfNat Real 0 := ⟨AddCommGroup.zero⟩
noncomputable instance : OfNat Real 1 := ⟨MulCommMonoid.one⟩

-- 一般の自然数リテラル用（2以上）
noncomputable def Real.ofNat : Nat → Real
  | 0 => (0 : Real)
  | 1 => (1 : Real)
  | Nat.succ (Nat.succ n) => Real.ofNat (Nat.succ n) + (1 : Real)

noncomputable instance (n : Nat) : OfNat Real (n + 2) := ⟨Real.ofNat (n + 2)⟩

noncomputable instance : NatCast Real := ⟨Real.ofNat⟩

-- 逆元のゼロでの値（inv 0 = 0 の規約）
axiom Real.inv_zero : Field.inv (0 : Real) = (0 : Real)

-- 完備性（上限公理）
axiom Real.sup (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) : Real
axiom Real.sup_ub (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ x, S x → x ≤ Real.sup S hne hbdd
axiom Real.sup_lub (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ M, (∀ x, S x → x ≤ M) → Real.sup S hne hbdd ≤ M

namespace Real

noncomputable def abs (x : Real) : Real := Abs.abs x

end Real
