-- Text/Proto/Partition.lean — 試作: 分割・リーマン和・タグ付き分割
import Text.Proto.Sum

open Range

-- 区間 [a, b] の n 分割: 広義単調な分点列で両端が a, b。
-- データ（points）と証明（increase / left / right）が同居する依存レコード
structure Partition (n : Nat) (a b : Real) where
  points : Range (n + 1) → Real
  increase : ∀ i : Range n, points (incl i) ≤ points (addone i)
  left : points ⟨0, Nat.succ_pos n⟩ = a
  right : points ⟨n, Nat.lt_succ_self n⟩ = b

namespace Partition

-- i 番目の小区間の長さ
noncomputable def length {n : Nat} {a b : Real} (Δ : Partition n a b)
    (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

-- タグが各小区間内にあること。if 無しの直接形（設計決定 D2: InInterval を経由しない）
def IsRepr {n : Nat} {a b : Real} (Δ : Partition n a b) (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)

end Partition

-- リーマン和
noncomputable def RiemannSum (f : Real → Real) {n : Nat} {a b : Real}
    (Δ : Partition n a b) (ξ : Range n → Real) : Real :=
  Summation n (fun i => f (ξ i) * Δ.length i)

-- タグ付き分割: 「∀ n Δ ξ, IsRepr → …」の 4 つ組を 1 変数に束ねる
structure TaggedPartition (a b : Real) where
  n : Nat
  Δ : Partition n a b
  ξ : Range n → Real
  repr : Δ.IsRepr ξ

namespace TaggedPartition

noncomputable def sum {a b : Real} (P : TaggedPartition a b) (f : Real → Real) : Real :=
  RiemannSum f P.Δ P.ξ

-- 細かさ: ∀ 形（diam / max を使わない、設計決定）
def Fine {a b : Real} (P : TaggedPartition a b) (δ : Real) : Prop :=
  ∀ i, P.Δ.length i < δ

end TaggedPartition

-- 1 分割（自明な分割）。クリフハンガー候補の難易度検証を兼ねて、ここでは完成形を書く
def trivialPartition (a b : Real) (hab : a ≤ b) : Partition 1 a b where
  points := fun i => if i.val = 0 then a else b
  increase := by
    intro ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact hab
    | v + 1, hv => exact absurd hv (by omega)
  left := rfl
  right := rfl
