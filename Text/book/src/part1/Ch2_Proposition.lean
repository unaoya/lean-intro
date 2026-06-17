-- Text/C01_FirstProofs.lean — Ch1 最初の証明（命題=型・証明=項。Real 不要）
-- テキスト用ソース: MyProject には依存しない（執筆規約 1）
import Ch1_Types  -- 命題（∧∨→¬∀∃）を型（Ch1 の ×⊕→Π…）とパラレルに読む

-- ANCHOR: my_first_theorem
theorem my_first_theorem : 1 = 1 := Eq.refl 1
-- ANCHOR_END: my_first_theorem

-- 論理結合子はすべて帰納型（非再帰）。各々に 導入規則（構成子＝作る）と
-- 除去規則（使う）がある。∧ の導入 = 無名コンストラクタ ⟨,⟩・除去 = 射影 .1 / .2
-- ANCHOR: and_swap
theorem and_swap (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩
-- ANCHOR_END: and_swap

-- ならば → = 関数（＝依存関数 Π の非依存版）。導入規則 = `fun`（λ抽象）・除去規則 = 適用。
-- 含意の証明は関数・modus ponens は関数適用。∀（Ch3）も同じ関数——codomain が依存するだけ
theorem modus_ponens (A B : Prop) (h : A → B) (a : A) : B := h a

theorem imp_trans (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C :=
  fun a => hbc (hab a)

-- または ∨ = 直和。導入 = Or.inl / Or.inr（2 つの構成子）・除去 = .elim（場合分け）。
-- この .elim こそ ∨ の**除去規則 = 場合分け（cases）**——∨ は非再帰なので帰納法の仮定
-- (IH) は無い。「除去規則 = recursor」「再帰なら IH が付いて induction」の全体像は Ch4。
theorem or_intro_left (A B : Prop) (a : A) : A ∨ B := Or.inl a

theorem or_swap (A B : Prop) (h : A ∨ B) : B ∨ A :=
  h.elim Or.inr Or.inl

-- 否定 ¬A = A → False（False への関数）。だから ¬ も**関数**（導入=fun・除去=適用）。
-- False（⊥）は構成子 0 の帰納型——除去 False.elim = 爆発律（全体像は Ch4）
theorem double_neg_intro (A : Prop) (a : A) : ¬¬A := fun na => na a

theorem modus_tollens (A B : Prop) (h : A → B) (nb : ¬B) : ¬A := fun a => nb (h a)

-- 演習素材（読者版では sorry に置き換える）
theorem and_assoc' (A B C : Prop) (h : (A ∧ B) ∧ C) : A ∧ (B ∧ C) :=
  ⟨h.1.1, h.1.2, h.2⟩

theorem and_or_distrib (A B C : Prop) (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) :=
  h.2.elim (fun b => Or.inl ⟨h.1, b⟩) (fun c => Or.inr ⟨h.1, c⟩)

-- 等式の証明も「項」だが、calc で等式を 1 本ずつ繋ぐ話は第一部 Ch5（calc）でまとめて扱う。
