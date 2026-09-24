-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«02_Forall»

-- ✏ 練習 28 の解答

#check fun (P Q : Prop) (hP : P) (hPQ : P → Q) => hPQ hP

-- ✏ 練習 29 の解答

theorem use_imp (P Q : Prop) (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP

-- ✏ 練習 30 の解答

theorem imp_refl (P : Prop) : P → P :=
  fun hP => hP

-- ✏ 練習 31 の解答

theorem imp_trans3 (P Q R S : Prop)
    (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) : P → S :=
  fun hP => hRS (hQR (hPQ hP))

-- ✏ 練習 32 の解答

#check 3 < 5

#check 3 = 5

-- ✏ 練習 33 の解答

theorem two_add_three : 2 + 3 = 5 := rfl

-- ✏ 練習 34 の解答

-- ✏ 練習 35 の解答

theorem keep_left (P Q : Prop) : P → Q → P :=
  fun hP _ => hP

-- ✏ 練習 36 の解答

theorem use_two (P Q R : Prop)
    (h : P → Q → R) (hP : P) (hQ : Q) : R :=
  h hP hQ

-- ✏ 練習 37 の解答

section
variable {α β γ : Type} {f : α → β} {g : β → γ}
variable (hg : ∀ u v, g u = g v → u = v) (hf : ∀ x y, f x = f y → x = y)
variable (x y : α) (h : g (f x) = g (f y))

#check hg (f x) (f y) h

#check hf x y (hg (f x) (f y) h)

end

-- ✏ 練習 38 の解答

theorem id_injective (α : Type) : Function.Injective (fun x : α => x) :=
  fun x y h => (h : x = y)

-- ✏ 練習 39 の解答

#check applyForall all_mul_zero 7
