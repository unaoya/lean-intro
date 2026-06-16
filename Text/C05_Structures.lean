-- Text/C05_Structures.lean — Ch5 数学的構造とその射（加群・順序半環の射 cast・分割の例）
-- Ch2 で「構造＝データ・class＝自動で見つかる構造」を学んだ。ここでは具体的な数学的構造を
-- **定義として**並べる: 加群（Real 上の Module）とその射（線形写像 IsLinearMap）・順序半環の射
-- （cast）・分割の具体例（等分割の points formula）。
-- 証明本体は道具が要るので後回し: Σ/リーマン和の線形性は Ch10（帰納法のあと）、
-- cast の順序系（≤ を保つ・正値・単射）と等分割 increase の完成は Ch11。
-- ここは「構造と射の輪郭」を term で描く章——tactic も順序補題もまだ使わない。
import Text.C04_Summation

-- ============================================================
-- 加群（Real 上の Module）: リーマン和の線形性（Ch10 で証明）の土台を**定義として**用意する。
--   行き先 V が加群なら α → V も各点で加群——Range n → Real も Real → Real も自動で加群。
--   公理の証明（線形写像 IsLinearMap・Σ の線形性）は道具が揃う Ch10 で行う。
-- ============================================================

-- ANCHOR: module
class Module (V : Type) extends Add V, Neg V, Zero V, SMul Real V where
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  add_comm : ∀ u v : V, u + v = v + u
  add_zero : ∀ v : V, v + 0 = v
  add_neg : ∀ v : V, v + -v = 0
  one_smul : ∀ v : V, (1 : Real) • v = v
  mul_smul : ∀ (a b : Real) (v : V), (a * b) • v = a • (b • v)
  smul_add : ∀ (a : Real) (u v : V), a • (u + v) = a • u + a • v
  add_smul : ∀ (a b : Real) (v : V), (a + b) • v = a • v + b • v

-- 線形写像（線形形式は W = Real の場合）
def IsLinearMap {V W : Type} [Module V] [Module W] (T : V → W) : Prop :=
  (∀ u v : V, T (u + v) = T u + T v) ∧
  (∀ (c : Real) (v : V), T (c • v) = c • T v)
-- ANCHOR_END: module

-- Real 自身は Real 上の加群（• は積）。公理は階層クラス（Ch3）のフィールドから直接。
noncomputable instance : Module Real where
  smul := fun c x => c * x
  add_assoc := AddCommMonoid.add_assoc
  add_comm := AddCommMonoid.add_comm
  add_zero := AddCommMonoid.add_zero
  add_neg := AddCommGroup.add_neg
  one_smul := MulCommMonoid.one_mul
  mul_smul := MulCommMonoid.mul_assoc
  smul_add := CommRing.left_distrib
  add_smul := CommRing.right_distrib

-- ★ 行き先 V が加群なら任意の射 α → V も加群（各点演算で誘導）。証明は V の加群公理を
-- funext で点ごとに持ち上げるだけ。Range n → Real も Real → Real も個別インスタンス不要。
noncomputable instance funModule {α V : Type} [Module V] : Module (α → V) where
  add := fun f g => fun x => f x + g x
  neg := fun f => fun x => -(f x)
  zero := fun _ => 0
  smul := fun c f => fun x => c • f x
  add_assoc := fun f g h => funext fun x => Module.add_assoc (f x) (g x) (h x)
  add_comm := fun f g => funext fun x => Module.add_comm (f x) (g x)
  add_zero := fun f => funext fun x => Module.add_zero (f x)
  add_neg := fun f => funext fun x => Module.add_neg (f x)
  one_smul := fun f => funext fun x => Module.one_smul (f x)
  mul_smul := fun a b f => funext fun x => Module.mul_smul a b (f x)
  smul_add := fun a f g => funext fun x => Module.smul_add a (f x) (g x)
  add_smul := fun a b f => funext fun x => Module.add_smul a b (f x)

-- ============================================================
-- 順序半環の射 cast: Nat を Real に埋め込む写像の「定義」と「射の概念」。
--   cast が 0・1・+・×・≤ を保つ（射である）ことの証明は、道具（順序・帰納法）が
--   揃う Ch11 で。ここでは埋め込みの定義と「順序半環の射」という概念だけを置く。
-- ============================================================

-- 自然数の埋め込み（構造的再帰）: 0 ↦ 0, n+1 ↦ (n の像)+1
-- ANCHOR: of_nat
noncomputable def Real.ofNat : Nat → Real
  | 0 => 0
  | n + 1 => Real.ofNat n + 1
-- ANCHOR_END: of_nat

-- リテラル 2 以上（Ch3 の failed to synthesize OfNat Real 2 がここで解決）
noncomputable instance (n : Nat) : OfNat Real (n + 2) := ⟨Real.ofNat (n + 2)⟩
-- 変数の埋め込み ↑n（リテラル用 OfNat との対比）
noncomputable instance : NatCast Real := ⟨Real.ofNat⟩
-- 除法の記法（等分割の分点式のため）
noncomputable instance : Div Real := ⟨fun a b => a * Field.inv b⟩

-- 順序写像（順序を保つ写像＝弱単調）。順序集合間の「順序の射」を抽象的に述べる述語。
-- ANCHOR: monotone
def Monotone {α β : Type} [LE α] [LE β] (φ : α → β) : Prop := ∀ a b, a ≤ b → φ a ≤ φ b
-- ANCHOR_END: monotone

-- **順序半環の射**: Nat → Real が 0・1・+・×・≤ を保つこと（≤ の保存＝順序写像 Monotone）。
-- Nat と Real を順序半環とみなしたときの準同型。cast がこの実例であることの証明は Ch11。
-- ANCHOR: cast_hom
structure IsOrderedSemiringHom (φ : Nat → Real) : Prop where
  map_zero : φ 0 = 0
  map_one : φ 1 = 1
  map_add : ∀ a b, φ (a + b) = φ a + φ b
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  monotone : Monotone φ
-- ANCHOR_END: cast_hom

-- ============================================================
-- 分割の具体例（分点式）: n 等分割の分点を与える関数。Ch4 の Partition を cast と除法で
--   具体的に作るための「材料」。points i = a + i·(b−a)/m——cast（↑i.val）と除法（/m）が
--   登場する最初の実例。これが広義単調（increase）で両端が a,b になることの証明には順序・
--   除法の補題が要るので、完全な Partition への組み上げ（equalPartition）は Ch11 で行う。
-- ============================================================

-- ANCHOR: equal_points
noncomputable def equalPoints (m : Nat) (a b : Real) : Range m → Real :=
  fun i => a + ((i.val : Nat) : Real) * (b - a) / (m : Real)
-- ANCHOR_END: equal_points
