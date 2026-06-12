-- Text/Proto/Axioms.lean — 試作: 代数階層クラス＋実数の公理（フル契約）＋最小インスタンス
-- 教材版の命名改善: le_asymm → le_antisymm, mul_pos → mul_nonneg

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
  mul_inv : ∀ a : α, a ≠ zero → a * inv a = one
  inv_mul : ∀ a : α, a ≠ zero → inv a * a = one
  nontrivial : zero ≠ one

class LinearOrderedField (α : Type) extends Field α, LE α where
  le_refl : ∀ a : α, a ≤ a
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  add_le_add : ∀ a b c : α, a ≤ b → a + c ≤ b + c
  mul_nonneg : ∀ a b : α, zero ≤ a → zero ≤ b → zero ≤ a * b

-- ============================================================
-- 実数の公理（5 本）
-- ============================================================

axiom Real : Type

-- (R1) Real は線形順序体
axiom Real.instLOF : LinearOrderedField Real

noncomputable instance : LinearOrderedField Real := Real.instLOF

-- (R2) 連続性（上限公理）。証人はデータ・性質は Prop（Skolem 形）
axiom Real.sup (S : Real → Prop) (hne : ∃ x, S x)
    (hbdd : ∃ M, ∀ x, S x → x ≤ M) : Real
axiom Real.sup_ub (S : Real → Prop) (hne : ∃ x, S x)
    (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ x, S x → x ≤ Real.sup S hne hbdd
axiom Real.sup_lub (S : Real → Prop) (hne : ∃ x, S x)
    (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ M, (∀ x, S x → x ≤ M) → Real.sup S hne hbdd ≤ M

-- ============================================================
-- 最小インスタンス 3 つ（リーマン和の記述に必要な分だけ）
-- ============================================================

-- Σ の基底に必要な 0（リテラル 1 以上と NatCast は Ch8 まで導入しない）
noncomputable instance : OfNat Real 0 := ⟨AddCommGroup.zero⟩

-- length の引き算（階層にあるのは Neg。中置 a - b の記法は別途）
noncomputable instance : Sub Real := ⟨fun a b => a + -b⟩

-- < は ≤ ∧ ≠ で定義（命題なので Decidable 不要）
instance : LT Real := ⟨fun a b => a ≤ b ∧ a ≠ b⟩
