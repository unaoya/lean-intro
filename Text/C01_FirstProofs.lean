-- Text/C01_FirstProofs.lean — Ch1 最初の証明（命題=型・証明=項。Real 不要）
-- テキスト用ソース: MyProject には依存しない（執筆規約 1）

-- ANCHOR: my_first_theorem
theorem my_first_theorem : 1 = 1 := Eq.refl 1
-- ANCHOR_END: my_first_theorem

-- かつ ∧ = ペア（無名コンストラクタ ⟨,⟩ と射影 .1 / .2）
-- ANCHOR: and_swap
theorem and_swap (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩
-- ANCHOR_END: and_swap

-- ならば → = 関数（含意の証明は関数、modus ponens は関数適用）
theorem modus_ponens (A B : Prop) (h : A → B) (a : A) : B := h a

theorem imp_trans (A B C : Prop) (hab : A → B) (hbc : B → C) : A → C :=
  fun a => hbc (hab a)

-- または ∨ = 直和（場合分けの正体 = recursor は Ch4 で）
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
