-- Text/book/src/part1/Ch2_Proposition.lean — 第一部 Ch2 命題（論理結合子の導入則・除去則）
-- Ch1 で型を「作る」基本手段（積×・和⊕・関数→・依存関数Π・部分型・依存和Σ）を見た。本章は
-- 命題の論理結合子（→・∧・∨・¬・∀・∃）を、Ch1 の型構成と**一対一でパラレル**に並べる。
-- 各結合子に「導入則（その命題を作る＝項を構成）」と「除去則（その命題を使う）」があり、それは
-- Ch1 の型の導入除去とまったく同じ機構——これが Curry-Howard 対応（命題＝型・証明＝項）。
-- いちばん基本の「ならば →」（＝関数）から始める。
import Ch1_Types  -- 型（Ch1 の ×⊕→Π…）と命題（∧∨→¬∀∃）をパラレルに読む

-- 最初の証明: 命題 0=0 の証明は項 Eq.refl 0（証明＝項の最小例）。計算で閉じる等式は rfl
-- ANCHOR: my_first_theorem
theorem my_first_theorem : 0 = 0 := Eq.refl 0
#check Eq.refl
theorem my_first_theorem' : 0 = 0 := rfl
#check rfl
theorem my_second_theorem : 1 + 1 = 2 := rfl
theorem my_second_theorem' : 3 + 1 = 4 := rfl
theorem my_second_theorem'' (n : Nat) : n + 1 = n.succ := rfl
-- theorem my_second_theorem''' (n : Nat) : 1 + n = n.succ := rfl
-- ANCHOR_END: my_first_theorem

-- ============================================================
-- §2.1 ならば → ↔ 関数型 α→β（Ch1 §3）
--   いちばん基本: → は関数そのもの。導入則 = fun（λ抽象＝関数を作る）／除去則 = 適用
--   （modus ponens は関数適用）。「A→B を証明するには A から B を作る関数を与える」。
-- ============================================================
-- ANCHOR: imp_intro_elim
theorem modus_ponens (A B : Prop) (h : A → B) (a : A) : B := h a   -- 除去 = 適用
theorem imp_trans (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C := fun a => hbc (hab a)  -- 導入 fun
-- ANCHOR_END: imp_intro_elim

-- ============================================================
-- §2.2 かつ ∧ ↔ 積 ×（Ch1 §1）
--   導入則 = And.intro（⟨_, _⟩ で 2 つの証明を組む）／除去則 = .1 / .2（射影）。Ch1 の Prod と同じ。
--   「A∧B を証明するには A の証明と B の証明の組を与える」「A∧B が仮定なら A も B も使える」。
-- ============================================================
-- ANCHOR: and_intro_elim
example (A B : Prop) (a : A) (b : B) : A ∧ B := And.intro a b      -- 正式な導入 And.intro
theorem and_swap (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩    -- 除去 .2/.1・導入 ⟨,⟩（略記）
-- ANCHOR_END: and_intro_elim

-- ============================================================
-- §2.3 または ∨ ↔ 和 ⊕（Ch1 §2）
--   導入則 = Or.inl / Or.inr（2 つの構成子）／除去則 = .elim（場合分け＝cases）。∨ は非再帰なので
--   帰納法の仮定 (IH) は無い（「除去則=recursor」「再帰なら IH=induction」の全体像は Ch4）。
--   「A∨B を証明するには A か B のどちらかを与える」「(A∨B) から C を示すには A→C と B→C を与える」。
-- ============================================================
-- ANCHOR: or_intro_elim
theorem or_intro_left (A B : Prop) (a : A) : A ∨ B := Or.inl a     -- 導入 Or.inl
theorem or_swap (A B : Prop) (h : A ∨ B) : B ∨ A := h.elim Or.inr Or.inl  -- 除去 .elim（場合分け）
-- ANCHOR_END: or_intro_elim

-- ============================================================
-- §2.4 否定 ¬ ↔ → False
--   ¬A = A → False（False への関数）。だから ¬ も**関数**（導入=fun・除去=適用）。False（⊥）は
--   構成子 0 個の帰納型（Ch1 の Empty に対応）——除去 False.elim = 爆発律（全体像は Ch4）。
-- ============================================================
-- ANCHOR: neg
theorem double_neg_intro (A : Prop) (a : A) : ¬¬A := fun na => na a
theorem modus_tollens (A B : Prop) (h : A → B) (nb : ¬B) : ¬A := fun a => nb (h a)
-- 具体例: ¬(0 = 1)。¬ は「→ False」なので、仮定 h : 0 = 1 から False を作る関数を書けばよい。
--   Nat.noConfusion は「異なる構成子（0 と succ）は等しくない」から矛盾 False を取り出す
theorem not_zero_eq_one : ¬(0 = 1) := fun h => Nat.noConfusion h
-- ANCHOR_END: neg

-- ============================================================
-- §2.5 すべて ∀ ↔ 依存関数型 Π（Ch1 §3）
--   ∀ x, P x = (x : α) → P x（codomain が Prop の依存関数）。導入=fun・除去=適用。Ch1 の Π と同じ。
-- ============================================================
-- ANCHOR: forall_intro_elim
theorem forall_refl : ∀ n : Nat, n = n := fun n => Eq.refl n              -- 導入 fun
theorem forall_apply (P : Nat → Prop) (h : ∀ n, P n) (k : Nat) : P k := h k  -- 除去 適用
-- ANCHOR_END: forall_intro_elim

-- ============================================================
-- §2.6 存在 ∃ ↔ 依存和 Σ / 部分型（Ch1 §3b/§3c）
--   導入則 = ⟨witness, proof⟩（証拠と証明を組む）／除去則 = .elim（証拠を取り出して使う）。
--   ∃ は証明（Prop）・Σ/Subtype は値が取り出せるデータ（Type）——Ch1 の Subtype/Σ と同じ機構。
-- ============================================================
-- ANCHOR: exists_intro_elim
theorem exists_two : ∃ n : Nat, n = 2 := ⟨2, rfl⟩                         -- 導入 ⟨witness, proof⟩
theorem exists_elim (P : Nat → Prop) (Q : Prop) (h : ∃ n, P n)
    (k : ∀ n, P n → Q) : Q := h.elim k                                   -- 除去 .elim
-- ANCHOR_END: exists_intro_elim

-- ============================================================
-- 演習素材（読者版では sorry に置き換える）
-- ============================================================
-- ANCHOR: exercises
theorem and_assoc' (A B C : Prop) (h : (A ∧ B) ∧ C) : A ∧ (B ∧ C) := ⟨h.1.1, h.1.2, h.2⟩
theorem and_or_distrib (A B C : Prop) (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) :=
  h.2.elim (fun b => Or.inl ⟨h.1, b⟩) (fun c => Or.inr ⟨h.1, c⟩)
-- ANCHOR_END: exercises

-- 等式の証明も「項」だが、calc で等式を 1 本ずつ繋ぐ話は第一部 Ch3（calc）で扱う。
