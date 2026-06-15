-- Text/C04_Summation.lean — Ch4 有限和（Range = 証明を抱えた添字、Summation = 構造的再帰）
import Text.C03_Axioms

-- 「n 未満の自然数」: 値と範囲内である証明の同梱（Subtype = 依存和の実物）
-- ANCHOR: range
def Range (n : Nat) := { i : Nat // i < n }

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
-- Summation について証明する（予告）: 再帰と帰納は同じ recursor
--   Summation は構造的再帰（`Nat.rec`）で定義した。それについて証明するときも
--   同じ `Nat.rec` を **帰納法** として走らせる——「定義する再帰」と「証明する帰納」は
--   表裏一体。ここでは term mode のまま 2 つだけ見る（ergonomic な `induction`
--   タクティクと Σ 補題コーパス本体は Ch10。本章は「定義＋最初の証明」で閉じる）。
-- ============================================================

-- ANCHOR: summation_first_proofs
-- (1) 合同: f と g が各点で等しければ和も等しい（`congrArg` だけ・帰納法は不要）
theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
    Summation n f = Summation n g := congrArg (Summation n) (funext h)

-- (2) 帰納法の予告: 全部 0 の和は 0。n についての構造的再帰（＝`Nat.rec`）で証明する。
--     succ の段に現れる `summation_all_zero n` が**帰納法の仮定そのもの**。
theorem summation_all_zero : (n : Nat) → Summation n (fun _ : Range n => (0 : Real)) = 0
  | 0 => rfl
  | n + 1 => (congrArg (· + (0 : Real)) (summation_all_zero n)).trans (AddCommGroup.zero_add 0)
-- ANCHOR_END: summation_first_proofs
