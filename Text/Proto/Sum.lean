-- Text/Proto/Sum.lean — 試作: Range（証明を抱えた添字）と有限和 Summation
import Text.Proto.Axioms

-- 「n 未満の自然数」: 値と範囲内である証明の同梱（Subtype）
def Range (n : Nat) := { i : Nat // i < n }

namespace Range

-- 隣接分点を安全に参照するための 2 つの埋め込み
def incl {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val, Nat.lt_succ_of_lt k.property⟩

def addone {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val + 1, Nat.succ_lt_succ k.property⟩

end Range

-- 有限和。添字つき族に対して定義する（List でない理由は設計書「表現の選択の論点」）
def Summation {α : Type} [Add α] [OfNat α 0] : (n : Nat) → (Range n → α) → α
  | 0 => fun _ => 0
  | n + 1 => fun f => Summation n (fun k => f (Range.incl k)) + f ⟨n, Nat.lt_succ_self n⟩

-- 定義の再帰方程式は rfl で定理になる（計算で証明される——defeq の予告編）
theorem summation_zero {α : Type} [Add α] [OfNat α 0] (f : Range 0 → α) :
    Summation 0 f = 0 := rfl

theorem summation_succ {α : Type} [Add α] [OfNat α 0] (n : Nat) (f : Range (n + 1) → α) :
    Summation (n + 1) f
      = Summation n (fun k => f (Range.incl k)) + f ⟨n, Nat.lt_succ_self n⟩ := rfl
