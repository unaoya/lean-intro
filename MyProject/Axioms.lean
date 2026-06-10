-- 杉浦の実数の公理の形式化
-- 本プロジェクトは実数を公理的に導入する方針（構成的定義は採らない）。
-- このファイルに「代数構造のクラス階層（インターフェース）」と「実数の公理」を集約する。

-- ============================================================
-- 代数構造のクラス階層（実数が満たすべきインターフェース）
-- ============================================================

class AddCommGroup (α : Type) extends Add α, Neg α where
  zero : α
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a, a + zero = a
  zero_add : ∀ a, zero + a = a
  add_neg : ∀ a, a + -a = zero
  neg_add : ∀ a, -a + a = zero

class MulCommMonoid (α : Type) extends Mul α where
  one : α
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  mul_one : ∀ a, a * one = a
  one_mul : ∀ a, one * a = a

class CommRing (α : Type) extends AddCommGroup α, MulCommMonoid α where
  left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c)
  right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c)

class Field (α : Type) extends CommRing α where
  inv : α → α
  mul_inv : ∀ a, a ≠ zero → a * inv a = one
  inv_mul : ∀ a, a ≠ zero → inv a * a = one
  nontrivial : zero ≠ one

variable {α : Type} [Field α]

instance : Sub α := ⟨fun a b => a + -b⟩

instance : Div α := ⟨fun a b => a * Field.inv b⟩

class LinearOrderedField (α : Type) extends Field α, LE α where
  le_refl : ∀ a : α, a ≤ a
  le_asymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  add_le_add : ∀ a b c : α, a ≤ b → a + c ≤ b + c
  mul_pos : ∀ a b : α, zero ≤ a → zero ≤ b → zero ≤ a * b

class NonNeg (α : Type) where
  nonneg : α → Prop

class Abs (α : Type) where
  abs : α → α

variable {α : Type} [LinearOrderedField α] [OfNat α 0]

instance : NonNeg α := ⟨fun a => 0 ≤ a⟩

noncomputable instance (a : α) : Decidable (NonNeg.nonneg a) := Classical.propDecidable _

instance : LT α := ⟨fun a b => a ≤ b ∧ a ≠ b⟩

noncomputable instance : DecidableRel (LE.le : α → α → Prop) := fun _ _ => Classical.propDecidable _

noncomputable instance : Min α := ⟨fun a b => if a ≤ b then a else b⟩

noncomputable instance : Max α := ⟨fun a b => if a ≤ b then b else a⟩

noncomputable instance : Abs α := ⟨fun a => max a (-a)⟩

class CompletLinearOrderedField (α : Type) extends LinearOrderedField α where

-- ============================================================
-- 実数の公理的定義
-- Real を完備線形順序体として公理的に導入する。
-- 本プロジェクトの実数公理はこのファイルに集約されている：
--   (R1) Real は線形順序体（体の公理＋順序の公理） … Real.instLOF
--   (R2) 連続性（上限公理）                        … Real.sup / sup_ub / sup_lub
-- アルキメデスの性質は上限公理から定理として導出する（Real/Cast.lean の archimedean）。
-- inv 0 = 0 の規約は不要になったため公理から外した（除法の補題は正値仮定で運用）。
-- ============================================================

axiom Real : Type

-- (R1) Real は線形順序体
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

-- (R2) 連続性（上限公理）
axiom Real.sup (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) : Real
axiom Real.sup_ub (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ x, S x → x ≤ Real.sup S hne hbdd
axiom Real.sup_lub (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ M, (∀ x, S x → x ≤ M) → Real.sup S hne hbdd ≤ M

namespace Real

noncomputable def abs (x : Real) : Real := Abs.abs x

end Real
