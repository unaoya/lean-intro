-- Text/C05_RiemannSum.lean — Ch5 分割とリーマン和の定義（到達点①）
-- 代表点の妥当性 IsRepr もここで定義（タグは小区間内から選ぶ＝リーマン和の概念の一部）。
-- TaggedPartition（束ねた版）は Ch12 まで持たない。
-- TODO(P4): Σ 記法・リーマン和の記法をここで自作する（notation 初登場）
import Text.C04_Summation

open Range

-- 区間 [a, b] の n 分割: 広義単調な分点列で両端が a, b。
-- データ（points）と証明（increase / left / right）が同居する依存レコード
-- ANCHOR: partition
structure Partition (n : Nat) (a b : Real) where
  points : Range (n + 1) → Real
  increase : ∀ i : Range n, points (incl i) ≤ points (addone i)
  left : points ⟨0, Nat.succ_pos n⟩ = a
  right : points ⟨n, Nat.lt_succ_self n⟩ = b
-- ANCHOR_END: partition

namespace Partition

-- i 番目の小区間の長さ
noncomputable def length {n : Nat} {a b : Real} (Δ : Partition n a b)
    (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

end Partition

-- リーマン和の定義は 1 行
-- ANCHOR: riemann_sum
noncomputable def RiemannSum (f : Real → Real) {n : Nat} {a b : Real}
    (Δ : Partition n a b) (ξ : Range n → Real) : Real :=
  Summation n (fun i => f (ξ i) * Δ.length i)
-- ANCHOR_END: riemann_sum

-- 代表点の妥当性: タグ ξ は各小区間の中から選ぶ。RiemannSum 自体は任意の ξ で計算できるが、
-- 「リーマン和」と呼ぶにはタグが代表点系（IsRepr）であることを課す。
-- この条件が効く場面（性質 4・非負性）は Ch9 で見る——落とすと何が壊れるかも。
namespace Partition

-- ANCHOR: is_repr
/-- 代表点系 `IsRepr`: タグ `ξ i` が各小区間 `[points (incl i), points (addone i)]` に
属すること。リーマン和の概念の一部（妥当なタグの条件）。 -/
def IsRepr {n : Nat} {a b : Real} (Δ : Partition n a b) (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)
-- ANCHOR_END: is_repr

end Partition

-- クリフハンガー: 1 分割（リテラルも除法も不要、自明の極み——なのに increase が
-- 添字の場合分けなしには書けない。読者版では increase が sorry のまま幕、Ch8 で完成）
-- ANCHOR: trivial_partition
def trivialPartition (a b : Real) (hab : a ≤ b) : Partition 1 a b where
  points := fun i => if i.val = 0 then a else b
  increase := by
    intro ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact hab
    | v + 1, hv => exact absurd hv (by omega)
  left := rfl
  right := rfl
-- ANCHOR_END: trivial_partition
