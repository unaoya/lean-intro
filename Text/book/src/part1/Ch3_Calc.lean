-- Text/book/src/part1/Ch5_Calc.lean — 第一部 Ch5 calc（等式の証明も項）
-- calc は「等式を 1 本ずつ繋ぐ」記法だが、その実体は Eq.trans（`.trans`）の連鎖の項。
-- Ch4 で定義した sumTo の閉じた式を calc で証明し、最後に「calc も項を作る記法」だと種明かしする。
-- パターンマッチ（→ brecOn・Ch4）と calc（→ Eq.trans）——記法はみな項を作る糖衣（CH 対応）。
import Ch2_Proposition

-- ============================================================
-- §5.1 calc ウォームアップ: 等式を 1 本ずつ繋ぐ（term mode・by は使わない）
--   各 := の右に「その 1 行を正当化する証明（項）」を置く。素材は Nat だけ（Real 不要）。
-- ============================================================

-- ANCHOR: calc_warmup
theorem add_swap_left (a b c : Nat) : a + (b + c) = b + (a + c) :=
  calc a + (b + c)
      = (a + b) + c := (Nat.add_assoc a b c).symm
    _ = (b + a) + c := congrArg (fun x => x + c) (Nat.add_comm a b)
    _ = b + (a + c) := Nat.add_assoc b a c
-- ANCHOR_END: calc_warmup

-- ============================================================
-- §5.2 交換則を calc で
--   Nat.add_assoc と Nat.add_comm だけで繋ぐ（第二部でこれを可換モノイドに 1 回抽象化する）。
-- ============================================================

-- ANCHOR: nat_interchange
theorem nat_interchange (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) :=
  calc (a + b) + (c + d)
      = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun x => a + x) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun x => a + (x + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun x => a + x) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm
-- ANCHOR_END: nat_interchange

-- ============================================================
-- §5.3 calc も項を作る: calc ≡ Eq.trans の連鎖
-- ============================================================

-- ANCHOR: calc_is_term
-- 2 段の calc は Eq.trans（`.trans`）の連鎖に **rfl で等しい**（calc が作っているのは
-- 1 個の等式の項そのもの）:
example (a b c : Nat) (h1 : a = b) (h2 : b = c) :
    (calc a = b := h1
          _ = c := h2) = h1.trans h2 := rfl
-- だから §5.3 の two_mul_sumTo の calc も、各段の証明を Eq.trans でつないだ 1 個の項にすぎない。
-- パターンマッチ（→ Nat.brecOn・Ch4）・calc（→ Eq.trans）・(後の) タクティク——記法はみな
-- 「項を作る」ための糖衣（CH 対応: 項＝証明）。
-- ANCHOR_END: calc_is_term

-- ============================================================
-- 演習: 乗法版 (a*b)*(c*d) = (a*c)*(b*d) を同じ calc で（解答は Solutions）
-- ============================================================
namespace Solutions

theorem nat_interchange_mul (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) :=
  calc (a * b) * (c * d)
      = a * (b * (c * d)) := Nat.mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := congrArg (fun x => a * x) (Nat.mul_assoc b c d).symm
    _ = a * ((c * b) * d) := congrArg (fun x => a * (x * d)) (Nat.mul_comm b c)
    _ = a * (c * (b * d)) := congrArg (fun x => a * x) (Nat.mul_assoc c b d)
    _ = (a * c) * (b * d) := (Nat.mul_assoc a c (b * d)).symm

end Solutions
