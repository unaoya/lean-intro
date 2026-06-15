-- Text/C01_FirstProofs.lean — Ch1 最初の証明（命題=型・証明=項。Real 不要）
-- テキスト用ソース: MyProject には依存しない（執筆規約 1）

-- ANCHOR: my_first_theorem
theorem my_first_theorem : 1 = 1 := Eq.refl 1
-- ANCHOR_END: my_first_theorem

-- 論理結合子はすべて帰納型（非再帰）。各々に 導入規則（構成子＝作る）と
-- 除去規則（使う）がある。∧ の導入 = 無名コンストラクタ ⟨,⟩・除去 = 射影 .1 / .2
-- ANCHOR: and_swap
theorem and_swap (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩
-- ANCHOR_END: and_swap

-- ならば → = 関数（含意の証明は関数、modus ponens は関数適用）
theorem modus_ponens (A B : Prop) (h : A → B) (a : A) : B := h a

theorem imp_trans (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C :=
  fun a => hbc (hab a)

-- または ∨ = 直和。導入 = Or.inl / Or.inr（2 つの構成子）・除去 = .elim（場合分け）。
-- この .elim こそ ∨ の**除去規則 = 場合分け（cases）**——∨ は非再帰なので帰納法の仮定
-- (IH) は無い。「除去規則 = recursor」「再帰なら IH が付いて induction」の全体像は Ch4。
theorem or_intro_left (A B : Prop) (a : A) : A ∨ B := Or.inl a

theorem or_swap (A B : Prop) (h : A ∨ B) : B ∨ A :=
  h.elim Or.inr Or.inl

-- 否定 ¬ = False への関数
theorem double_neg_intro (A : Prop) (a : A) : ¬¬A := fun na => na a

theorem modus_tollens (A B : Prop) (h : A → B) (nb : ¬B) : ¬A := fun a => nb (h a)

-- 演習素材（読者版では sorry に置き換える）
theorem and_assoc' (A B C : Prop) (h : (A ∧ B) ∧ C) : A ∧ (B ∧ C) :=
  ⟨h.1.1, h.1.2, h.2⟩

theorem and_or_distrib (A B C : Prop) (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) :=
  h.2.elim (fun b => Or.inl ⟨h.1, b⟩) (fun c => Or.inr ⟨h.1, c⟩)

-- ============================================================
-- 等式の証明も「項」: calc で等式を 1 本ずつ繋ぐ（term mode・by は使わない）
--   素材は Nat だけ（Real 不要）。Ch2 でこの式を「構造の言葉」で 1 回に抽象化する。
-- ============================================================

-- ウォームアップ: 2 段の calc（各 := の右に「その 1 行を正当化する証明（項）」を置く）
-- ANCHOR: calc_warmup
theorem add_swap_left (a b c : Nat) : a + (b + c) = b + (a + c) :=
  calc a + (b + c)
      = (a + b) + c := (Nat.add_assoc a b c).symm
    _ = (b + a) + c := congrArg (fun x => x + c) (Nat.add_comm a b)
    _ = b + (a + c) := Nat.add_assoc b a c
-- ANCHOR_END: calc_warmup

-- 交換則: (a+b)+(c+d) = (a+c)+(b+d)。Nat.add_assoc と Nat.add_comm だけで繋ぐ。
-- Ch2 ではこれを「任意の可換モノイド」について 1 回証明し、+ と * の両方に効かせる。
-- ANCHOR: nat_interchange
theorem nat_interchange (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) :=
  calc (a + b) + (c + d)
      = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun x => a + x) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun x => a + (x + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun x => a + x) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm
-- ANCHOR_END: nat_interchange

-- 演習: 乗法版 (a*b)*(c*d) = (a*c)*(b*d) を同じ calc で（解答は下の Solutions）
namespace Solutions

theorem nat_interchange_mul (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) :=
  calc (a * b) * (c * d)
      = a * (b * (c * d)) := Nat.mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := congrArg (fun x => a * x) (Nat.mul_assoc b c d).symm
    _ = a * ((c * b) * d) := congrArg (fun x => a * (x * d)) (Nat.mul_comm b c)
    _ = a * (c * (b * d)) := congrArg (fun x => a * x) (Nat.mul_assoc c b d)
    _ = (a * c) * (b * d) := (Nat.mul_assoc a c (b * d)).symm

end Solutions
