-- Text/C06_Tactics.lean — Ch6 sorry を埋める道具 I（タクティク演習集: 等式の corpus）
-- 群・環の等式補題を intro / exact / apply / rw / calc のドリルとして獲得する。
-- 順序・不等式の補題は Ch7（C07）、古典論理を使う補題は第 II 部（C11）へ。
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

theorem mul_zero' (a : Real) : a * (0 : Real) = 0 := by
  apply add_left_cancel' (a * (0 : Real))
  calc a * 0 + (a * 0) = a * (0 + 0) := (CommRing.left_distrib a 0 0).symm
    _ = a * 0 := by rw [zero_add' (0 : Real)]
    _ = a * 0 + 0 := (add_zero' _).symm

theorem zero_mul' (a : Real) : (0 : Real) * a = 0 := by
  rw [MulCommMonoid.mul_comm]; exact mul_zero' a

theorem neg_zero : -(0 : Real) = 0 := by
  calc -(0 : Real) = -(0 : Real) + 0 := (add_zero' _).symm
    _ = 0 := neg_add' 0

theorem neg_add_distrib (a b : Real) : -(a + b) = -a + -b := by
  apply add_left_cancel' (a + b)
  have lhs : (a + b) + -(a + b) = (0 : Real) := add_neg' _
  have rhs : (a + b) + (-a + -b) = (0 : Real) := by
    calc (a + b) + (-a + -b)
      = a + (b + (-a + -b)) := AddCommGroup.add_assoc _ _ _
      _ = a + ((b + -a) + -b) := by rw [AddCommGroup.add_assoc b (-a) (-b)]
      _ = a + ((-a + b) + -b) := by rw [AddCommGroup.add_comm b (-a)]
      _ = a + (-a + (b + -b)) := by rw [AddCommGroup.add_assoc (-a) b (-b)]
      _ = a + (-a + 0) := by rw [add_neg']
      _ = a + -a := by rw [add_zero']
      _ = 0 := add_neg' _
  rw [lhs, rhs]

theorem neg_neg (a : Real) : -(-a) = a := by
  apply add_left_cancel' (-a); rw [add_neg', neg_add']

theorem neg_mul (a b : Real) : -a * b = -(a * b) := by
  apply add_left_cancel' (a * b)
  calc a * b + -a * b = (a + -a) * b := (CommRing.right_distrib a (-a) b).symm
    _ = 0 * b := by rw [add_neg']
    _ = 0 := zero_mul' b
    _ = a * b + -(a * b) := (add_neg' _).symm

theorem mul_neg (a b : Real) : a * (-b) = -(a * b) := by
  rw [MulCommMonoid.mul_comm a (-b), neg_mul, MulCommMonoid.mul_comm b a]

theorem mul_sub (a b c : Real) : a * (b - c) = a * b - a * c := by
  show a * (b + -c) = a * b + -(a * c)
  rw [CommRing.left_distrib, mul_neg]

-- ============================================================
-- 引き算の整理（sub は a + -b の略記——defeq の最初の実感）
-- ============================================================

theorem sub_self (a : Real) : a - a = 0 := add_neg' a

theorem sub_zero (a : Real) : a - 0 = a := by
  show a + -(0 : Real) = a
  rw [neg_zero, add_zero']

theorem neg_sub (a b : Real) : -(a - b) = b - a := by
  show -(a + -b) = b + -a
  rw [neg_add_distrib, neg_neg, add_comm]

theorem add_sub_cancel (a b : Real) : a + b - a = b := by
  calc a + b + -a = a + (b + -a) := AddCommGroup.add_assoc _ _ _
    _ = a + (-a + b) := by rw [AddCommGroup.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_cancel' (a b : Real) : a + (b - a) = b := by
  calc a + (b + -a) = a + (-a + b) := by rw [AddCommGroup.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_cancel_right (a b : Real) : a + b - b = a := by
  show a + b + -b = a
  rw [add_assoc, add_neg', add_zero']

theorem sub_add_cancel (a b : Real) : a - b + b = a := by
  show a + -b + b = a
  rw [AddCommGroup.add_assoc, neg_add', add_zero']

theorem add_sub_add' (a b c : Real) : a + b - (a + c) = (b - c) := by
  show a + b + -(a + c) = b + -c
  rw [show -(a + c) = -a + -c from neg_add_distrib a c]
  calc a + b + (-a + -c) = a + (b + (-a + -c)) := AddCommGroup.add_assoc _ _ _
    _ = a + (b + -a + -c) := by rw [AddCommGroup.add_assoc b (-a) (-c)]
    _ = a + (-a + b + -c) := by rw [AddCommGroup.add_comm b (-a)]
    _ = a + (-a + (b + -c)) := by rw [AddCommGroup.add_assoc (-a) b (-c)]
    _ = (a + -a) + (b + -c) := (AddCommGroup.add_assoc _ _ _).symm
    _ = 0 + (b + -c) := by rw [add_neg']
    _ = b + -c := zero_add' _

theorem add_sub_add (a b c d : Real) : a + b - (c + d) = (a - c) + (b - d) := by
  show a + b + -(c + d) = (a + -c) + (b + -d)
  rw [show -(c + d) = -c + -d from neg_add_distrib c d]
  calc a + b + (-c + -d) = a + (b + (-c + -d)) := AddCommGroup.add_assoc _ _ _
    _ = a + (b + -c + -d) := by rw [AddCommGroup.add_assoc b (-c) (-d)]
    _ = a + (-c + b + -d) := by rw [AddCommGroup.add_comm b (-c)]
    _ = a + (-c + (b + -d)) := by rw [AddCommGroup.add_assoc (-c) b (-d)]
    _ = (a + -c) + (b + -d) := (AddCommGroup.add_assoc _ _ _).symm

theorem sub_sub' (a b c : Real) : a - (b + c) = a - b - c := by
  show a + -(b + c) = a + -b + -c
  rw [neg_add_distrib]
  exact (add_assoc a (-b) (-c)).symm

theorem mul_sub_mul (a b c : Real) : a * b - c * b = (a - c) * b := by
  show a * b + -(c * b) = (a + -c) * b
  rw [show -(c * b) = (-c) * b from (neg_mul c b).symm]
  exact (CommRing.right_distrib a (-c) b).symm

theorem add_four_comm (a b c d : Real) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d) = a + (b + (c + d)) := add_assoc _ _ _
    _ = a + ((b + c) + d) := by rw [add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := (add_assoc _ _ _).symm

theorem telescope_2 (a b c : Real) : b - a = (c - a) + (b - c) := by
  show b + -a = (c + -a) + (b + -c)
  symm
  calc (c + -a) + (b + -c) = c + (-a + (b + -c)) := AddCommGroup.add_assoc _ _ _
    _ = c + (-a + b + -c) := by rw [AddCommGroup.add_assoc (-a) b (-c)]
    _ = c + (b + -a + -c) := by rw [AddCommGroup.add_comm (-a) b]
    _ = c + (b + (-a + -c)) := by rw [AddCommGroup.add_assoc b (-a) (-c)]
    _ = (c + b) + (-a + -c) := (AddCommGroup.add_assoc _ _ _).symm
    _ = (c + b) + -(a + c) := by rw [neg_add_distrib]
    _ = (b + c) + -(c + a) := by rw [AddCommGroup.add_comm c b, AddCommGroup.add_comm a c]
    _ = (b + c) + (-c + -a) := by rw [neg_add_distrib]
    _ = b + (c + (-c + -a)) := AddCommGroup.add_assoc _ _ _
    _ = b + ((c + -c) + -a) := by rw [(AddCommGroup.add_assoc c (-c) (-a)).symm]
    _ = b + (0 + -a) := by rw [add_neg']
    _ = b + -a := by rw [zero_add']

-- (z + h) − (h + h) = z − h（誤差の半分ずらし。Ch15 が消費）
theorem add_half_sub_full (z h : Real) : (z + h) - (h + h) = z - h := by
  show z + h + -(h + h) = z + -h
  rw [neg_add_distrib]
  calc z + h + (-h + -h) = z + (h + (-h + -h)) := add_assoc _ _ _
    _ = z + ((h + -h) + -h) := by rw [add_assoc h (-h) (-h)]
    _ = z + (0 + -h) := by rw [add_neg']
    _ = z + -h := by rw [zero_add']
