-- Text/Proto/Numerals.lean — M2: リテラル 1・自然数の埋め込み・除法の記法
import Text.Proto.Axioms

-- リテラル 1（M2 で初めて必要になる: zero_lt_one・半分の構成）
noncomputable instance : OfNat Real 1 := ⟨MulCommMonoid.one⟩

-- 自然数の埋め込み（n 等分の分点式とアルキメデスのため）
noncomputable def Real.ofNat : Nat → Real
  | 0 => 0
  | n + 1 => Real.ofNat n + 1

noncomputable instance : NatCast Real := ⟨Real.ofNat⟩

-- 除法の記法（等分割の分点式のため）
noncomputable instance : Div Real := ⟨fun a b => a * Field.inv b⟩
