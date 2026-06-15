-- Text/C04_Summation.lean — Ch4 有限和（Range = 証明を抱えた添字、Summation = 構造的再帰）
import Text.C03_Axioms

-- 「n 未満の自然数」: 値と範囲内である証明の同梱（Subtype = 依存和の実物）
-- ANCHOR: range
def Range (n : Nat) := { i : Nat // i < n }

-- 名前空間を**作る**（Ch3 の「アクセス」の対）: `namespace Range … end Range` で囲むと、
--   中で定義した `incl` は外から `Range.incl` という名前になる。Range に関わる操作を
--   1 つの接頭辞の下に束ね、名前の衝突を避け、所属を名前で示す。
--   （次章 Ch5 で `open Range` すれば接頭辞 `Range.` を省ける——それが旨味。）
namespace Range

-- 隣接分点を安全に参照するための 2 つの埋め込み
def incl {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val, Nat.lt_succ_of_lt k.property⟩

def addone {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val + 1, Nat.succ_lt_succ k.property⟩

end Range
-- ANCHOR_END: range

-- 有限和。契約は最小（二項演算とゼロの値 = [Add α] [Zero α]）。
-- 基底の `0` は C02 の bridge（Zero → OfNat）経由で Zero.zero に defeq。
-- 添字つき族に対して定義する（List でない理由は本文の設計議論）
-- ANCHOR: summation
def Summation {α : Type} [Add α] [Zero α] : (n : Nat) → (Range n → α) → α
  | 0 => fun _ => 0
  | n + 1 => fun f => Summation n (fun k => f (Range.incl k)) + f ⟨n, Nat.lt_succ_self n⟩
-- ANCHOR_END: summation

-- 定義の再帰方程式は rfl で定理になる（計算で証明される——defeq の予告編）
-- ANCHOR: summation_rfl
theorem summation_zero {α : Type} [Add α] [Zero α] (f : Range 0 → α) :
    Summation 0 f = 0 := rfl

theorem summation_succ {α : Type} [Add α] [Zero α] (n : Nat) (f : Range (n + 1) → α) :
    Summation (n + 1) f
      = Summation n (fun k => f (Range.incl k)) + f ⟨n, Nat.lt_succ_self n⟩ := rfl
-- ANCHOR_END: summation_rfl

-- ============================================================
-- 帰納型を「証明で使う」: 除去規則（eliminator = recursor）
--   どの帰納型にも 導入規則（構成子＝値を作る）と 除去規則（recursor＝値を使う）がある。
--   除去規則は同じ形だが、**構成子が再帰的な引数を持つと、その分だけ「結果の予測」
--   ＝帰納法の仮定 (IH) を受け取る**。再帰の有無が cases と induction を分ける:
--     ・非再帰（Or・And・Subtype）の除去 = 場合分け `cases`（IH 無し）。Ch1 の `.elim`
--       （or_swap・and_or_distrib）が既にこれ——∨ の除去規則の適用だった。
--     ・再帰（Nat）の除去 = `induction`（succ の段で motive n = IH を受け取る）。
--   下の 2 つの型を並べると、IH が「再帰している箇所」にちょうど現れるのが見える。
-- ============================================================

-- ANCHOR: eliminators
#check @Or.rec    -- (a → C) → (b → C) → (a ∨ b) → C        ← 各構成子の引数だけ・IH 無し（=cases）
#check @Nat.rec   -- motive 0 → ((n) → motive n → motive (n+1)) → (n) → motive n
                  --                        ↑ motive n = 帰納法の仮定 IH（Nat が再帰だから）
-- ANCHOR_END: eliminators

-- ============================================================
-- CH 対応のパンチライン: 論理 = 依存関数（Π）＋ 帰納型、それぞれの導入/除去だけ
--   Ch1・Ch3 で見た結合子は、Lean では 2 つの原始に還元される:
--     ・→ と ∀ は **依存関数（Π 型）**。導入 = `fun`（λ）・除去 = 適用。
--       違いは codomain が引数に依存するかだけ（→ は非依存・∀ は依存）。¬A = A → False も関数。
--     ・∧ ∨ ∃ ⊥ ⊤ = は **帰納型**。導入 = 構成子・除去 = recursor（cases/induction）。
--   だから「依存関数の導入/除去（λ/適用）」と「帰納型の導入/除去（構成子/recursor）」だけで
--   論理はすべて書ける。#print で「これらは帰納型」が、#check で「→/∀ は Π」が見える:
-- ============================================================

-- ANCHOR: ch_punchline
#print And      -- structure（構成子 intro 1 つ・除去 .1 .2 = And.rec）
#print Or       -- inductive（構成子 inl/inr・除去 .elim = Or.rec）
#print Exists   -- inductive（構成子 intro 1 つ・依存・除去 .elim = Exists.rec）
#print False    -- inductive（構成子 0・除去 False.elim = 爆発律）
-- → と ∀ は帰納型ではなく Π（依存関数）。これだけが帰納型と別格の原始:
#check fun (A B : Prop) => A → B          -- 非依存の関数型（→）
#check fun (P : Nat → Prop) => ∀ n, P n   -- 依存関数型（∀）
-- ANCHOR_END: ch_punchline

-- ============================================================
-- Summation について証明する（予告）: 定義した recursor をそのまま証明に使う
--   Summation は `Nat.rec`（構造的再帰）で定義した。それを **除去規則として証明に
--   走らせる**のが induction——「定義する再帰」と「証明する帰納」は同じ recursor。
--   ここでは term mode のまま 2 つだけ（ergonomic な induction タクティクと Σ 補題
--   コーパス本体は Ch10。本章は「定義＋最初の証明」で閉じる）。
-- ============================================================

-- ANCHOR: summation_first_proofs
-- (1) 合同: f と g が各点で等しければ和も等しい（`congrArg` だけ・除去規則も不要）
theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
    Summation n f = Summation n g := congrArg (Summation n) (funext h)

-- (2) 帰納法の予告: 全部 0 の和は 0。n についての構造的再帰（＝`Nat.rec` の除去）で証明。
--     succ の段に現れる `summation_all_zero n` が**帰納法の仮定 (IH) そのもの**。
theorem summation_all_zero : (n : Nat) → Summation n (fun _ : Range n => (0 : Real)) = 0
  | 0 => rfl
  | n + 1 => (congrArg (· + (0 : Real)) (summation_all_zero n)).trans (AddCommMonoid.zero_add 0)
-- ANCHOR_END: summation_first_proofs

-- ============================================================
-- 加群（Real 上の Module）: リーマン和の線形性（Ch9 で証明）の土台を**定義として**用意する。
--   行き先 V が加群なら α → V も各点で加群——Range n → Real も Real → Real も自動で加群。
--   公理の証明（線形写像 IsLinearMap・Σ の線形性）は道具が揃う Ch9 で行う。
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
