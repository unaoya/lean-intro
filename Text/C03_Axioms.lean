-- Text/C03_Axioms.lean — Ch3 実数を公理で読む
-- Ch2 で得た「構造＝データ・class＝自動で見つかる構造」の見方で、実数の公理を読む。
-- 代数階層クラス＋公理 5 本＋最小インスタンス＋根幹 2 行の観察＋最初の実数証明（< の 3 兄弟）
-- sup 最小性実験（演習）: sup 公理 3 本をコメントアウトしても C05 まではビルドが通る

-- ============================================================
-- 代数構造のクラス階層（実数が満たすべきインターフェース）
-- ============================================================

-- ANCHOR: hierarchy
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
-- ANCHOR_END: hierarchy

-- ============================================================
-- 実数の公理（5 本）
-- ============================================================

-- ANCHOR: axioms
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
-- ANCHOR_END: axioms

-- ============================================================
-- 最小インスタンス（リーマン和の記述に必要な分だけ）
-- ============================================================

-- ゼロの窓口クラス: core の `Zero`（mathlib から昇格）に公理の zero を登録する。
-- リテラル 0 へは core の一方向 bridge `Zero.toOfNat0 : [Zero α] → OfNat α 0` が配線する。
-- 良い菱形の規律: 経路は一方向・値は defeq（悪い菱形は C03 のトイデモ参照）。
-- リテラル 1 以上と NatCast は Ch8 まで導入しない
-- ANCHOR: zero_bridge
noncomputable instance : Zero Real := ⟨AddCommGroup.zero⟩
-- ANCHOR_END: zero_bridge

-- length の引き算（階層にあるのは Neg。中置 a - b はここで定義）
noncomputable instance : Sub Real := ⟨fun a b => a + -b⟩

-- < は ≤ ∧ ≠ で定義（命題なので Decidable 不要）
instance : LT Real := ⟨fun a b => a ≤ b ∧ a ≠ b⟩

-- ============================================================
-- 最初の実数証明: < の 3 兄弟（Ch1 の論理が Real に着地する瞬間）
-- ============================================================

-- ANCHOR: three_brothers
theorem le_of_lt {a b : Real} : a < b → a ≤ b := fun h => h.1

theorem lt_of_le_of_ne {a b : Real} (h : a ≤ b) (hne : a ≠ b) : a < b := ⟨h, hne⟩

theorem ne_of_gt {a b : Real} (h : a < b) : b ≠ a := fun h0 => h.2 h0.symm
-- ANCHOR_END: three_brothers

-- ============================================================
-- 根幹の 2 行と、自動で見つかる構造（class = 自動解決される structure）
--   axiom Real.instLOF（構造一式を公理で名指し）＋ instance（正準登録）の観察。
--   これが Ch2 の「class＝自動で見つかる構造」の実物——だから a + b が動く。
-- ============================================================

#check Real.instLOF
#check (inferInstance : LinearOrderedField Real)

-- `a + b` が型検査を通る——書いた覚えのない「+」をインスタンス解決が運んでくる
#check fun (a b : Real) => a + b
#check fun (a b : Real) => a ≤ b

-- 今 Real に登録された数のインスタンスは 0 だけ（リテラル 1 は Ch6・2 以上は Ch8）。
-- #check_failure は「失敗すること」自体を検査する——伏線がビルドで保証される
-- ANCHOR: check_failure
#check (0 : Real)         -- 通る（Σ の基底として上で導入済み）
#check_failure (1 : Real) -- failed to synthesize OfNat Real 1（1 は Ch6 で）
#check_failure (2 : Real) -- failed to synthesize OfNat Real 2（2 以上は Ch8 で）
-- ANCHOR_END: check_failure
