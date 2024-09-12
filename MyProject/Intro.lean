-- Lean入門

-- とりあえず証明を書く

theorem my_first_theorem : 1 + 1 = 2 := rfl

def my_first_theorem' : 1 + 1 = 2 := rfl

def x : Nat := 1

-- term : typeが基本的な書式

#check rfl

def my_first_theorem'' : Eq 1 1 := rfl

#check Eq 1 1

inductive MyEq : α → α → Prop where
  | refl (a : α) : MyEq a a

theorem my_first_theorem''' : MyEq 1 1 := MyEq.refl 1

theorem my_first_theorem'''' : MyEq (1 + 1) 2 := MyEq.refl _

-- 型と項
-- 命題も型
-- 項を作る = 証明する
-- 項を与える = 仮定する

-- 同じとは？

example (h : MyEq a b) : MyEq b a := by
  cases h
  exact MyEq.refl _

example (h : MyEq a b) : MyEq b a :=
  match h with
  | MyEq.refl a => MyEq.refl a


inductive MyEq' : α → α → Prop where
  | refl (a b : α) : MyEq' a b

example : MyEq' b a := MyEq'.refl _ _

#check MyEq.refl
#check MyEq'.refl

inductive MyPred : α → Prop where
  | pred (a : α) : MyPred a
