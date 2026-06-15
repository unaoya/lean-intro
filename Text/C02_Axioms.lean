-- Text/C02_Axioms.lean — Ch2–3 実数の公理（フル契約）
-- 代数階層クラス＋公理 5 本＋最小インスタンス 3 つ＋最初の実数証明（< の 3 兄弟）
-- sup 最小性実験（Ch2 演習）: sup 公理 3 本をコメントアウトしても C05 まではビルドが通る

-- ============================================================
-- 数学的構造はデータ: 「α 上の構造」は型であり、住人が「構造ひとつ」
--   （階層クラスを読む前の見方。Ch1 の ⟨⟩ ペアの大きい版・instance は使わない）
-- ============================================================

-- ANCHOR: structure_as_data
#check (Add Nat)                              -- Add Nat : Type（「α 上の加法構造」は型）

-- Add α の住人とは「α 上の二項演算ひとつ」にすぎない（⟨⟩ で作れる）
example : Add Nat := ⟨Nat.add⟩               -- 普通の加法
example : Add Nat := ⟨fun a b => a * b⟩      -- 乗法も Nat 上の二項演算 → Add Nat の住人

-- 同じ集合 Nat に「構造」はいくつも載る。Add は法則を持たない——だから乗法すら
-- 住人になれてしまう。法則（結合律・単位律…）は AddCommGroup 以降が束ねる。
-- これが「階層がある」理由であり、次に読む公理の束の正体。
-- ANCHOR_END: structure_as_data

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
