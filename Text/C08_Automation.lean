-- Text/C08_Automation.lean — Ch8 自動化と自作タクティク
-- 「コーパスを 1 本ずつ手で grind する」段を越える。core の simp / omega / ac_rfl と、
-- それらを束ねる macro で、機械に任せる工夫を作る。mathlib の ring/linarith/group は
-- 無いので、自分の hand-proved 補題から simp セットを作って ring-lite を自作する。
-- （反射ベースの本格 my_ring は付録 D。本章はその入口）
import Text.C07_Rewrite

-- ============================================================
-- §1 simp に環の等式を教える
--    Ch6/7 で手証明した群・環の恒等式を simp に渡すと、それらの合成でしかない
--    派生恒等式は simp が自動で閉じる。`simp only [...]` は渡した規則だけを使う
--    （既定の simp セットは触らない＝下流の証明の挙動を変えない規律）。
-- ============================================================

-- ANCHOR: simp_demo
-- Ch7 では calc/rw で数行かけた命題が、hand-proved 補題を simp に渡すと一発で閉じる
example (a b : Real) : (a + b) + -b = a := by
  simp only [add_assoc, add_neg', add_zero']
example (a : Real) : -(-a) + 0 = a := by simp only [neg_neg, add_zero']
example (a b : Real) : a * 0 + b = b := by simp only [mul_zero', zero_add']
-- ANCHOR_END: simp_demo

-- ============================================================
-- §2 omega: Nat の線形算術は決定手続きで閉じる
--    添字計算（Σ の境界・truncated subtraction）はこれで尽きる。
--    正体（決定手続き）は付録 D／Ch10 の sum_id_nat でも稼働。
-- ============================================================

-- ANCHOR: omega_demo
example (n : Nat) : n + 1 - 1 = n := by omega
example (a b : Nat) : a + b + 0 = b + a := by omega
-- ANCHOR_END: omega_demo

-- ============================================================
-- §3 ac_rfl: 結合・可換を「道具に教える」
--    + の結合性・可換性を Std のインスタンスとして与えると、ac_rfl が
--    任意の括弧・順序の差を吸収する——「タクティクに代数の事実を渡して自動化する」。
--    simp の方向的な書き換えでは捌けない並べ替えを、ac_rfl が引き受ける。
-- ============================================================

instance : Std.Associative (· + · : Real → Real → Real) := ⟨add_assoc⟩
instance : Std.Commutative (· + · : Real → Real → Real) := ⟨add_comm⟩

-- ANCHOR: ac_demo
example (a b c : Real) : a + b + c = c + (b + a) := by ac_rfl
example (a b c d : Real) : (a + b) + (c + d) = (a + c) + (b + d) := by ac_rfl
-- ANCHOR_END: ac_demo

-- ============================================================
-- §4 自作タクティク my_ring: simp セットの合成を 1 語に束ねる
--    「環の正規化」を 1 つのタクティクにする。macro はタクティクを綴る最小の自作
--    （Ch6 の『タクティクは項を書く機械』の発展）。これは方向的正規化の ring-lite で、
--    クロス項の相殺など並べ替えが要る等式は苦手——その限界を埋める反射版の本体は付録 D。
-- ============================================================

-- ANCHOR: my_ring
macro "my_ring" : tactic =>
  `(tactic| simp only [add_neg', neg_add', zero_add', add_zero', one_mul_b, mul_one_b,
      neg_neg, neg_zero, mul_zero', zero_mul', neg_add_distrib,
      add_assoc, mul_assoc, CommRing.left_distrib, CommRing.right_distrib])

example (a b : Real) : (a + b) + -b = a := by my_ring
example (a b c : Real) : a * (b + c) = a * b + a * c := by my_ring
example (a b c : Real) : (a + b) * c = a * c + b * c := by my_ring
-- ANCHOR_END: my_ring
