-- Text/C04_Summation.lean — Ch4 帰納型と構造的再帰・分割とリーマン和の定義（到達点①）
import Text.C03_Axioms

-- 「n 未満の自然数」: 値と範囲内である証明の同梱（Subtype = 依存和の実物）
-- ANCHOR: range
def Range (n : Nat) := { i : Nat // i < n }
-- ANCHOR_END: range

-- ANCHOR: range_intro
-- Range の「項」と「関数」の基本動作（Subtype の導入と除去）:
--   項を作る = 値と「範囲内」の証明を ⟨_, _⟩ で組む（導入）／取り出す = .val（除去）
example : Range 3 := ⟨2, Nat.lt_succ_self 2⟩      -- 値 2 ＋ 証明 2 < 3（= 2 < 2+1）
example (i : Range 3) : Nat := i.val              -- Range「から」の関数（domain が Range・射影）
-- Range 3「から」の関数を i.val の 0/1/2 で場合分け。i.val < 3 ゆえ 0/1/2 で尽きるが、
-- 型 `Range 3` だけからは Lean にそれが分からない——Nat 全体の網羅に最後の枝が要る（依存型の限界）
example (i : Range 3) : Nat := match i.val with
  | 0 => 10
  | 1 => 20
  | 2 => 30
  | _ => 0                                        -- i.val < 3 ゆえ到達しない（網羅性のためのダミー）
-- Range「へ」の関数（codomain が Range）は値を作り範囲内の証明を添える——下の incl/addone が実戦
-- ANCHOR_END: range_intro

-- ANCHOR: range_funcs
-- 名前空間を**作る**（Ch3 の「アクセス」の対）: `namespace Range … end Range` で囲むと、
--   中で定義した `incl` は外から `Range.incl` という名前になる。Range に関わる操作を
--   1 つの接頭辞の下に束ね、名前の衝突を避け、所属を名前で示す。
--   （この後 `open Range` すれば接頭辞 `Range.` を省ける——それが旨味。下の分割定義で実演。）
namespace Range

-- incl/addone は「Range への関数」の実戦（Range n の項から Range (n+1) の項を作る——
-- 値は同じ / +1、添える「範囲内」の証明だけを既存補題で作り替える）。隣接分点の安全な参照
def incl {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val, Nat.lt_succ_of_lt k.property⟩

def addone {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val + 1, Nat.succ_lt_succ k.property⟩

end Range
-- ANCHOR_END: range_funcs

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
-- 分割とリーマン和の**定義**（到達点①）。証明技術は不要——structure とΣで値を作るだけ。
--   代表点が妥当（leftRepr_isRepr）であることの証明は順序 le_refl を要するので Ch10 で。
-- ============================================================

open Range

-- 区間 [a, b] の n 分割: 広義単調な分点列で両端が a, b（データと証明が同居する依存レコード）。
-- ANCHOR: partition
structure Partition (n : Nat) (a b : Real) where
  points : Range (n + 1) → Real
  increase : ∀ i : Range n, points (incl i) ≤ points (addone i)
  left : points ⟨0, Nat.succ_pos n⟩ = a
  right : points ⟨n, Nat.lt_succ_self n⟩ = b
-- ANCHOR_END: partition

namespace Partition

-- i 番目の小区間の長さ（dot 記法 Δ.length が効く）
noncomputable def length {n : Nat} {a b : Real} (Δ : Partition n a b)
    (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

end Partition

-- リーマン和の定義は 1 行（値ベクトル f∘ξ と幅ベクトル length の和）
-- ANCHOR: riemann_sum
noncomputable def RiemannSum (f : Real → Real) {n : Nat} {a b : Real}
    (Δ : Partition n a b) (ξ : Range n → Real) : Real :=
  Summation n (fun i => f (ξ i) * Δ.length i)
-- ANCHOR_END: riemann_sum

namespace Partition

-- ANCHOR: is_repr
/-- 代表点系 `IsRepr`: タグ `ξ i` が各小区間 `[points (incl i), points (addone i)]` に
属すること。リーマン和の概念の一部（妥当なタグの条件）。 -/
def IsRepr {n : Nat} {a b : Real} (Δ : Partition n a b) (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)
-- ANCHOR_END: is_repr

-- ANCHOR: endpoint_repr
/-- 左端代表点: 各小区間の左端 `points (incl i)` をタグにする。 -/
def leftRepr {n : Nat} {a b : Real} (Δ : Partition n a b) : Range n → Real :=
  fun i => Δ.points (incl i)

/-- 右端代表点: 各小区間の右端 `points (addone i)` をタグにする。 -/
def rightRepr {n : Nat} {a b : Real} (Δ : Partition n a b) : Range n → Real :=
  fun i => Δ.points (addone i)
-- ANCHOR_END: endpoint_repr

end Partition

-- クリフハンガー: 1 分割（リテラルも除法も不要、自明の極み——なのに increase が
-- 添字の場合分けなしには書けない。読者版では increase が sorry のまま幕、Ch6 で完成）。
-- ANCHOR: trivial_partition
def trivialPartition (a b : Real) (hab : a ≤ b) : Partition 1 a b where
  points := fun i => match i.val with
    | 0 => a
    | _ + 1 => b
  increase := by
    intro ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact hab
    | v + 1, hv => exact absurd hv (by omega)
  left := rfl
  right := rfl
-- ANCHOR_END: trivial_partition
