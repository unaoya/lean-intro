-- 杉浦の実数の公理の形式化
-- 構造をクラスにする
-- 自然数の継承的部分集合による定義とNatが同値になること

import MyProject.Numbers.Structure

-- ============================================================
-- 実数の公理的定義
-- Real を完備線形順序体として公理的に導入する。
-- 本プロジェクトの実数公理はこのファイルに集約されている：
--   (R1) Real は線形順序体（体の公理＋順序の公理） … Real.instLOF
--   (R2) 連続性（上限公理）                        … Real.sup / sup_ub / sup_lub
-- アルキメデスの性質は上限公理から定理として導出する（Real/Cast.lean の archimedean）。
-- inv 0 = 0 の規約は不要になったため公理から外した（除法の補題は正値仮定で運用）。
-- ============================================================

axiom Real : Type

-- (R1) Real は線形順序体
axiom Real.instLOF : LinearOrderedField Real

noncomputable instance : LinearOrderedField Real := Real.instLOF

-- OfNat: 0 と 1 を直接定義し、AddCommGroup.zero / MulCommMonoid.one と定義的に一致させる
noncomputable instance : OfNat Real 0 := ⟨AddCommGroup.zero⟩
noncomputable instance : OfNat Real 1 := ⟨MulCommMonoid.one⟩

-- 一般の自然数リテラル用（2以上）
noncomputable def Real.ofNat : Nat → Real
  | 0 => (0 : Real)
  | 1 => (1 : Real)
  | Nat.succ (Nat.succ n) => Real.ofNat (Nat.succ n) + (1 : Real)

noncomputable instance (n : Nat) : OfNat Real (n + 2) := ⟨Real.ofNat (n + 2)⟩

noncomputable instance : NatCast Real := ⟨Real.ofNat⟩

-- (R2) 連続性（上限公理）
axiom Real.sup (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) : Real
axiom Real.sup_ub (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ x, S x → x ≤ Real.sup S hne hbdd
axiom Real.sup_lub (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
  ∀ M, (∀ x, S x → x ≤ M) → Real.sup S hne hbdd ≤ M

namespace Real

noncomputable def abs (x : Real) : Real := Abs.abs x

end Real
