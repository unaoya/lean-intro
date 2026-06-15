-- Text/C06_Tactics.lean — Ch6 タクティク入門（tactic mode の機構と信頼）
-- by・ゴール状態・intro/exact/apply/rw/have/show を学び、「タクティクは証明項を書く
-- 機械」であることを #print で確かめる。等式補題を数本だけ手で証明して道具に慣れる。
-- 等式コーパス本体は Ch7（C07_Rewrite）、自動化は Ch8、順序と calc は Ch9。
import Text.C05_RiemannSum

-- 1 の窓口: core の `One` に公理の one を登録（リテラル 1 は bridge One.toOfNat1 経由——
-- C02 の Zero と対。数の段階導入: 0=Ch2・1=Ch6・2 以上と NatCast=Ch8）
noncomputable instance : One Real := ⟨MulCommMonoid.one⟩

-- ============================================================
-- 橋渡し（クラスのフィールドを使いやすい形で取り出す）
-- ============================================================

theorem add_neg' (a : Real) : a + -a = (0 : Real) := AddCommGroup.add_neg a
theorem neg_add' (a : Real) : -a + a = (0 : Real) := AddCommGroup.neg_add a
theorem zero_add' (a : Real) : (0 : Real) + a = a := AddCommGroup.zero_add a
theorem add_zero' (a : Real) : a + (0 : Real) = a := AddCommGroup.add_zero a
theorem one_mul_b (a : Real) : (1 : Real) * a = a := MulCommMonoid.one_mul a
theorem mul_one_b (a : Real) : a * (1 : Real) = a := MulCommMonoid.mul_one a

theorem add_comm (a b : Real) : a + b = b + a := AddCommGroup.add_comm a b
theorem add_assoc (a b c : Real) : a + b + c = a + (b + c) := AddCommGroup.add_assoc a b c
theorem mul_comm (a b : Real) : a * b = b * a := MulCommMonoid.mul_comm a b
theorem mul_assoc (a b c : Real) : a * b * c = a * (b * c) := MulCommMonoid.mul_assoc a b c

theorem add_zero (a : Real) : a + 0 = a := add_zero' a
theorem one_mul (a : Real) : 1 * a = a := one_mul_b a

-- ============================================================
-- 基本計算（消去・ゼロ・符号）
-- ============================================================

theorem add_left_cancel' (a b c : Real) (h : a + b = a + c) : b = c := by
  calc b = 0 + b := (zero_add' _).symm
    _ = (-a + a) + b := by rw [neg_add']
    _ = -a + (a + b) := AddCommGroup.add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + c := by rw [neg_add']
    _ = c := zero_add' _
