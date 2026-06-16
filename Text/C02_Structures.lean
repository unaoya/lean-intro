-- Text/C02_Structures.lean — Ch2 数学的構造と class の仕組み（machinery）
-- 構造をデータとして書く・一般構造で 1 回証明して複数インスタンスに適用する、を
-- 素の structure だけで体験する（class／instance の深い機構と ℝ の公理は Ch3 以降）。
-- import 連鎖の葉（core のみ・主線非依存）。

-- ============================================================
-- §1 数学的構造はデータ: 「α 上の構造」は型であり、住人が「構造ひとつ」
--   （Ch1 の ⟨⟩ ペアの大きい版・instance は使わない）
-- ============================================================

-- ANCHOR: structure_as_data
#check (Add Nat)                              -- Add Nat : Type（「α 上の加法構造」は型）
#check Add

-- Add α の住人とは「α 上の二項演算ひとつ」にすぎない（⟨⟩ で作れる）
example : Add Nat := ⟨Nat.add⟩               -- 普通の加法
example : Add Nat := ⟨fun a b => a * b⟩      -- 乗法も Nat 上の二項演算 → Add Nat の住人

-- 同じ集合 Nat に「構造」はいくつも載る。Add は法則を持たない——だから乗法すら
-- 住人になれてしまう。法則（結合律・単位律…）は構造の側が束ねる（次の §2）。
-- ANCHOR_END: structure_as_data

-- ============================================================
-- §1b Nat が標準ライブラリ（core）で持つ構造たち: 演算子クラスはすべて「構造＝データ」。
--   名前が記法 +/*/0/1/≤/< の担い手——だが法則（結合律…）はまだ付かない（法則は §2 以降）。
-- ============================================================

-- ANCHOR: nat_structures
#check (Add Nat)    -- 二項演算付き集合（+ の担い手）
#check (Mul Nat)    -- 二項演算付き集合（* の担い手）
#check (Zero Nat)   -- 点付き集合（0 の担い手）
#check (One Nat)    -- 点付き集合（1 の担い手）
#check (Sub Nat)    -- 引き算付き
#check (LE Nat)     -- 二項関係付き集合（≤ の担い手）
#check (LT Nat)     -- 二項関係付き集合（< の担い手）
-- いずれも `Type`——Add Nat と同じ「構造＝データ」。クラス名が記法と対応し、法則はまだ無い。
-- mathlib があれば法則付きの Monoid/CommRing/… も借りられるが、本書は core のみ＝法則は
-- 自分で束ねる（次の §2 の structure・Ch3 の class 階層）
-- ANCHOR_END: nat_structures

-- ============================================================
-- §2 一般構造で 1 回証明する: 可換モノイド構造を作り、その法則だけから
--   交換則を証明する。Nat の加法も乗法も可換モノイドだから、同じ定理が両方に効く。
-- ============================================================

-- ANCHOR: general_proof
-- 演算と「それが満たす法則の証明」を束ねたレコード型（structure キーワード）
structure CommMonoidStr (α : Type) where
  op : α → α → α
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)
  op_comm : ∀ a b : α, op a b = op b a

-- 交換則: (a⋆b)⋆(c⋆d) = (a⋆c)⋆(b⋆d)。結合律＋可換律だけから出る（公理ではない）
theorem interchange {α : Type} (M : CommMonoidStr α) (a b c d : α) :
    M.op (M.op a b) (M.op c d) = M.op (M.op a c) (M.op b d) :=
  calc M.op (M.op a b) (M.op c d)
      = M.op a (M.op b (M.op c d)) := M.op_assoc a b (M.op c d)
    _ = M.op a (M.op (M.op b c) d) := congrArg (M.op a) (M.op_assoc b c d).symm
    _ = M.op a (M.op (M.op c b) d) := congrArg (fun x => M.op a (M.op x d)) (M.op_comm b c)
    _ = M.op a (M.op c (M.op b d)) := congrArg (M.op a) (M.op_assoc c b d)
    _ = M.op (M.op a c) (M.op b d) := (M.op_assoc a c (M.op b d)).symm

-- Nat の 2 つの可換モノイド構造（加法と乗法）。法則は core の定理を渡すだけ
def natAdd : CommMonoidStr Nat := ⟨Nat.add, Nat.add_assoc, Nat.add_comm⟩
def natMul : CommMonoidStr Nat := ⟨Nat.mul, Nat.mul_assoc, Nat.mul_comm⟩

-- 1 回の証明が両方に効く（一般定理が + と * の具体形に defeq で一致する）
example (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) :=
  interchange natAdd a b c d
example (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) :=
  interchange natMul a b c d
-- ANCHOR_END: general_proof

-- ============================================================
-- §2.4 記法は付けられるか？（→ class の動機）
--   固定した構造には記法を当てられる（structure で OK）。だが「どんな型でも a+b」
--   のように Lean が構造を自動で探す多相な記法は、これでは作れない——class が要る。
-- ============================================================

-- ANCHOR: local_notation
-- 固定した natAdd の op に局所記法 ⋆ を当てる（structure のままで可能）
local infixl:65 " ⋆ " => natAdd.op

-- 一般定理がそのまま使える（⋆ は natAdd.op、interchange natAdd の型と一致）
example (a b c d : Nat) : (a ⋆ b) ⋆ (c ⋆ d) = (a ⋆ c) ⋆ (b ⋆ d) :=
  interchange natAdd a b c d

-- だが ⋆ は「natAdd という特定の構造」に固定されている。型ごとに構造を自動で選ぶ
-- 多相な `+`（ℝ でも Nat でも `a + b`）は、構造を探す仕組み＝class／instance が要る（§2.5）。
-- ANCHOR_END: local_notation

-- ============================================================
-- §3 種明かし: Ch1 から使ってきた ⟨⟩ も structure だった
-- ============================================================

-- ANCHOR: and_is_structure
#print And   -- structure And (a b : Prop) : Prop（⟨h.2, h.1⟩ の ⟨⟩ はこれ）
-- ANCHOR_END: and_is_structure
