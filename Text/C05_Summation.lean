-- Text/C05_Summation.lean — Ch5 リーマン和の定義 — 構造的再帰（Summation）と structure（到達点①）
-- Ch2 で型の構成（Range＝Subtype・帰納型・recursor）を見た。ここではその構造的再帰で有限和
-- Summation を定義し、分割（structure Partition）とリーマン和へ組み上げる（到達点①）。
import Text.C04_Axioms      -- 実数・階層クラス
import Text.C02_Types       -- Range（Ch2 の Subtype 実例）を Σ の添字に使う

-- 帰納的定義の入門: 自然数からの写像を「zero でどうなるか／succ でどうなるか」の 2 段で定める
-- （Ch2 で見た Nat.rec の実演）。まず簡単な例 sumTo n = 0 + 1 + … + n から始める。
-- ANCHOR: sum_to
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)   -- succ の段で「前の結果 sumTo n」に n+1 を足す
example : sumTo 3 = 6 := rfl     -- 0+1+2+3 = 6（再帰方程式は定義どおり rfl で計算される）
-- ANCHOR_END: sum_to

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
-- Summation について証明する（予告）: 定義した recursor をそのまま証明に使う
--   Summation は `Nat.rec`（構造的再帰）で定義した。それを **除去規則として証明に
--   走らせる**のが induction——「定義する再帰」と「証明する帰納」は同じ recursor。
--   ここでは term mode のまま 2 つだけ（ergonomic な induction タクティクと Σ 補題
--   コーパス本体は Ch11。本章は「定義＋最初の証明」で閉じる）。
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
--   代表点が妥当（leftRepr_isRepr）であることの証明は順序 le_refl を要するので Ch11 で。
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
-- 添字の場合分けなしには書けない。読者版では increase が sorry のまま幕、Ch7 で完成）。
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
