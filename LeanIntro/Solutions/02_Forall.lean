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

def apply2 {α : Type} : (α → α) → α → α := fun f a => f (f a)

theorem applyTwice {p : Prop} : (p → p) → p → p := fun f h => f (f h)

#check apply2

#check applyTwice

def apply2Binder {α : Type} (f : α → α) (a : α) : α := f (f a)

theorem applyTwiceBinder {p : Prop} (f : p → p) (h : p) : p := f (f h)

#check apply2Binder

#check applyTwiceBinder

-- ✏ 練習 36 の解答

theorem imp_swap {p q r : Prop} : (p → q → r) → q → p → r :=
  fun h hq hp => h hp hq

-- ✏ 練習 37 の解答

example : Nat → Nat := fun h => h

example : (1 = 1) → (1 = 1) := fun h => h

-- ✏ 練習 38 の解答

#check applyFun double 3

-- ✏ 練習 39 の解答

-- ✏ 練習 40 の解答

theorem id_injective (α : Type) : Function.Injective (fun x : α => x) :=
  fun x y h => (h : x = y)

-- ✏ 練習 41 の解答

#check applyForall all_mul_zero 7
