-- Text/C04_Axioms.lean — Ch4 実数を公理で読む
-- Ch3 で得た「構造＝データ・class＝自動で見つかる構造」の見方で、実数の公理を読む。
-- 代数階層クラス＋公理 5 本＋最小インスタンス＋根幹 2 行の観察＋最初の実数証明（< の 3 兄弟）
-- sup 最小性実験（演習）: sup 公理 3 本をコメントアウトしても C05 まではビルドが通る

-- ============================================================
-- 代数構造のクラス階層（実数が満たすべきインターフェース）
-- ============================================================

-- 加法は「可換モノイド（逆元なし）→ 可換群（逆元あり）」の 2 段で積む。
-- 補題が成り立つ最小構造を Ch10 で示すための土台（モノイドで足りる加法補題と
-- 群が要る符号補題を分ける）。
-- ANCHOR: hierarchy
class AddCommMonoid (α : Type) extends Add α where
  zero : α
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a, a + zero = a
  zero_add : ∀ a, zero + a = a

class AddCommGroup (α : Type) extends AddCommMonoid α, Neg α where
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
-- ANCHOR_END: hierarchy

-- 注: zero/add_assoc/add_comm/zero_add/add_zero は AddCommMonoid へ移ったが、
-- extends が親フィールドのアクセサ `AddCommMonoid.zero` 等を自動生成するので、
-- Ch7・Ch8 の既存参照（`AddCommMonoid.zero_add` 等）はそのまま温存される。

-- 順序の階層（補題が成り立つ最小構造を Ch10 で活用するための中間クラス）。
-- 順序モノイド（加法と順序）→ 順序群（符号も）→ 順序体（乗法も）→ 全順序体（線形性）。
-- ANCHOR: order_hierarchy
class OrderedAddCommMonoid (α : Type) extends AddCommMonoid α, LE α where
  le_refl : ∀ a : α, a ≤ a
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  add_le_add_right : ∀ a b c : α, a ≤ b → a + c ≤ b + c

class OrderedAddCommGroup (α : Type) extends AddCommGroup α, OrderedAddCommMonoid α

class OrderedField (α : Type) extends OrderedAddCommGroup α, Field α where
  mul_nonneg : ∀ a b : α, zero ≤ a → zero ≤ b → zero ≤ a * b

class LinearOrderedField (α : Type) extends OrderedField α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
-- ANCHOR_END: order_hierarchy

-- le_refl/le_antisymm/le_trans/le_total/mul_nonneg は中間クラスへ移ったが、extends の
-- 自動アクセサで `OrderedAddCommMonoid.le_trans` 等はそのまま引ける。唯一 add_le_add は
-- フィールド名が add_le_add_right に変わったので、従来名のエイリアスを 1 本だけ置く。
theorem LinearOrderedField.add_le_add {α : Type} [LinearOrderedField α] (a b c : α)
    (h : a ≤ b) : a + c ≤ b + c := OrderedAddCommMonoid.add_le_add_right a b c h

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

-- CH 対応の続き（Ch1 の表を ∀∃ で埋める）: 上の署名の `∀` と `∃` の正体——
--   `∀ x, P x` は **依存関数 `(x) → P x`**（→ と同じ関数・codomain が x に依存するだけ）。
--     導入規則 = `fun x => …`・除去規則 = 適用。だから ∀ の証明は関数を書くこと。
--   `∃ x, P x` は **帰納型 `Exists`**（Σ＝依存和）。導入 = `⟨a, h⟩`（証人＋証明）・
--     除去 = `.elim`（場合分け＝cases）。「∃ をデータに格上げ」したのが sup の証人。
-- → ∀ ¬ は依存関数（Π）・∧ ∨ ∃ ⊥ ⊤ = は帰納型——2 つの原始の導入/除去で論理は尽きる（Ch5 で #print 確認）

-- ============================================================
-- 最小インスタンス（リーマン和の記述に必要な分だけ）
-- ============================================================

-- ゼロの窓口クラス: core の `Zero`（mathlib から昇格）に公理の zero を登録する。
-- リテラル 0 へは core の一方向 bridge `Zero.toOfNat0 : [Zero α] → OfNat α 0` が配線する。
-- 良い菱形の規律: 経路は一方向・値は defeq（悪い菱形のデモは C12 の DiamondIncident）。
-- ANCHOR: zero_bridge
noncomputable instance : Zero Real := ⟨AddCommMonoid.zero⟩
-- ANCHOR_END: zero_bridge

-- 1 の窓口: core の `One` に公理の one を登録（リテラル 1 は bridge One.toOfNat1 経由）。
-- 0 と同じく Ch4 で導入する——加群（Ch5）のスカラー単位 1 で使うため前倒し。
-- 2 以上のリテラルと NatCast は Ch6（C06_Structures）で導入する。
noncomputable instance : One Real := ⟨MulCommMonoid.one⟩

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

-- 名前空間（namespace）との最初の接触＝「アクセス」: `Real.sup`・`Real.instLOF`・
--   `AddCommGroup.add_neg`・`OrderedAddCommMonoid.le_trans` のドット付きの名前は、
--   `名前空間.名前` という階層化された名前への参照。`le_trans` は順序クラス
--   `OrderedAddCommMonoid` に整理されている——フルパスで名指せばどこからでも引ける。
--   （この段階はまだ「既にある名前空間を読む」だけ。自分で名前空間を**作る**のは
--    Ch5 `namespace Range`、`open` で接頭辞を省く旨味は Ch6 で。）
-- 公理は「すでに証明された定理」: 階層のフィールドはそのまま項として使える。
-- この `a ≤ c` の `≤` が動くのも、class が `LE Real` を解決しているから（Ch3 の回収）。
-- 本格的な順序コーパスは Ch10。ここは「公理を引くだけで証明になる」一度きりの実演。
example (a b c : Real) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  OrderedAddCommMonoid.le_trans a b c hab hbc

-- 定義の意図を term で読む: `<` を `a ≤ b ∧ a ≠ b` と置いたので、`a < a` は不可能。
-- `h.2` は `a ≠ a`（＝ `a = a → False`）、それに `rfl : a = a` を渡すだけ。
theorem lt_irrefl (a : Real) : ¬ (a < a) := fun h => h.2 rfl

-- ============================================================
-- 根幹の 2 行と、自動で見つかる構造（class = 自動解決される structure）
--   axiom Real.instLOF（構造一式を公理で名指し）＋ instance（正準登録）の観察。
--   これが Ch3 の「class＝自動で見つかる構造」の実物——だから a + b が動く。
-- ============================================================

#check Real.instLOF
#check (inferInstance : LinearOrderedField Real)

-- `a + b` が型検査を通る——書いた覚えのない「+」をインスタンス解決が運んでくる
#check fun (a b : Real) => a + b
#check fun (a b : Real) => a ≤ b

-- 今 Real に登録された数のインスタンスは 0 と 1 だけ（2 以上は Ch6 C06_Structures で）。
-- #check_failure は「失敗すること」自体を検査する——伏線がビルドで保証される
-- ANCHOR: check_failure
#check (0 : Real)         -- 通る（Σ の基底・上で Zero bridge を導入済み）
#check (1 : Real)         -- 通る（加群のスカラー単位・上で One bridge を導入済み）
#check_failure (2 : Real) -- failed to synthesize OfNat Real 2（2 以上は Ch6 で）
-- ANCHOR_END: check_failure
