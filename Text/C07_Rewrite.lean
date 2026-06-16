-- Text/C07_Rewrite.lean — Ch7 書き換えと 2 つの等しさ（rw と defeq）
-- 等式/環の補題コーパスを rw/calc で獲得する。「sub は a + -b の略記」を通じて
-- defeq（計算で同じ）と構文的等しさ（rw が見る）の違いを掴む。
-- 自動化（simp で畳む）は Ch8、順序コーパスは Ch9、帰納法は Ch10。
import Text.C06_Tactics

-- ============================================================
-- 基本計算（消去・ゼロ・符号）
-- ============================================================

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
      = a + (b + (-a + -b)) := AddCommMonoid.add_assoc _ _ _
      _ = a + ((b + -a) + -b) := by rw [AddCommMonoid.add_assoc b (-a) (-b)]
      _ = a + ((-a + b) + -b) := by rw [AddCommMonoid.add_comm b (-a)]
      _ = a + (-a + (b + -b)) := by rw [AddCommMonoid.add_assoc (-a) b (-b)]
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
  calc a + b + -a = a + (b + -a) := AddCommMonoid.add_assoc _ _ _
    _ = a + (-a + b) := by rw [AddCommMonoid.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommMonoid.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_cancel' (a b : Real) : a + (b - a) = b := by
  calc a + (b + -a) = a + (-a + b) := by rw [AddCommMonoid.add_comm b (-a)]
    _ = (a + -a) + b := (AddCommMonoid.add_assoc _ _ _).symm
    _ = 0 + b := by rw [add_neg']
    _ = b := zero_add' _

theorem add_sub_cancel_right (a b : Real) : a + b - b = a := by
  show a + b + -b = a
  rw [add_assoc, add_neg', add_zero']

theorem sub_add_cancel (a b : Real) : a - b + b = a := by
  show a + -b + b = a
  rw [AddCommMonoid.add_assoc, neg_add', add_zero']

theorem add_sub_add' (a b c : Real) : a + b - (a + c) = (b - c) := by
  show a + b + -(a + c) = b + -c
  rw [show -(a + c) = -a + -c from neg_add_distrib a c]
  calc a + b + (-a + -c) = a + (b + (-a + -c)) := AddCommMonoid.add_assoc _ _ _
    _ = a + (b + -a + -c) := by rw [AddCommMonoid.add_assoc b (-a) (-c)]
    _ = a + (-a + b + -c) := by rw [AddCommMonoid.add_comm b (-a)]
    _ = a + (-a + (b + -c)) := by rw [AddCommMonoid.add_assoc (-a) b (-c)]
    _ = (a + -a) + (b + -c) := (AddCommMonoid.add_assoc _ _ _).symm
    _ = 0 + (b + -c) := by rw [add_neg']
    _ = b + -c := zero_add' _

theorem add_sub_add (a b c d : Real) : a + b - (c + d) = (a - c) + (b - d) := by
  show a + b + -(c + d) = (a + -c) + (b + -d)
  rw [show -(c + d) = -c + -d from neg_add_distrib c d]
  calc a + b + (-c + -d) = a + (b + (-c + -d)) := AddCommMonoid.add_assoc _ _ _
    _ = a + (b + -c + -d) := by rw [AddCommMonoid.add_assoc b (-c) (-d)]
    _ = a + (-c + b + -d) := by rw [AddCommMonoid.add_comm b (-c)]
    _ = a + (-c + (b + -d)) := by rw [AddCommMonoid.add_assoc (-c) b (-d)]
    _ = (a + -c) + (b + -d) := (AddCommMonoid.add_assoc _ _ _).symm

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
  calc (c + -a) + (b + -c) = c + (-a + (b + -c)) := AddCommMonoid.add_assoc _ _ _
    _ = c + (-a + b + -c) := by rw [AddCommMonoid.add_assoc (-a) b (-c)]
    _ = c + (b + -a + -c) := by rw [AddCommMonoid.add_comm (-a) b]
    _ = c + (b + (-a + -c)) := by rw [AddCommMonoid.add_assoc b (-a) (-c)]
    _ = (c + b) + (-a + -c) := (AddCommMonoid.add_assoc _ _ _).symm
    _ = (c + b) + -(a + c) := by rw [neg_add_distrib]
    _ = (b + c) + -(c + a) := by rw [AddCommMonoid.add_comm c b, AddCommMonoid.add_comm a c]
    _ = (b + c) + (-c + -a) := by rw [neg_add_distrib]
    _ = b + (c + (-c + -a)) := AddCommMonoid.add_assoc _ _ _
    _ = b + ((c + -c) + -a) := by rw [(AddCommMonoid.add_assoc c (-c) (-a)).symm]
    _ = b + (0 + -a) := by rw [add_neg']
    _ = b + -a := by rw [zero_add']

-- (z + h) − (h + h) = z − h（誤差の半分ずらし。発展部 E5 が消費）
theorem add_half_sub_full (z h : Real) : (z + h) - (h + h) = z - h := by
  show z + h + -(h + h) = z + -h
  rw [neg_add_distrib]
  calc z + h + (-h + -h) = z + (h + (-h + -h)) := add_assoc _ _ _
    _ = z + ((h + -h) + -h) := by rw [add_assoc h (-h) (-h)]
    _ = z + (0 + -h) := by rw [add_neg']
    _ = z + -h := by rw [zero_add']
