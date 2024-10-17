-- Lean入門

-- とりあえず証明を書く

-- term : typeが基本的な書式

def m : Nat := 1

-- 項の型を調べる

#check m

-- 項の「定義？」を調べる

#print m

#check 1

def my_first_theorem : 1 = 1 := Eq.refl 1

-- def my_first_theorem_error : 1 = 1 := asdfg

def my_first_theorem' : Eq 1 1 := Eq.refl 1

#check my_first_theorem

#print my_first_theorem

#check 1 = 1

#check Eq

#check Eq 1 1

#check Eq.refl

#print Eq.refl

def my_second_theorem : 1 + 1 = 2 := rfl

def x : Nat := 1

def y : Nat := 1

def my_third_theorem : x = y := rfl

-- 型と項
-- 命題も型
-- 項を作る = 証明する
-- 項を与える = 仮定する

-- 同じとは？

inductive MyEq : α → α → Prop where
  | refl (a : α) : MyEq a a

theorem my_first_theorem''' : MyEq 1 1 := MyEq.refl 1

theorem my_first_theorem'''' : MyEq (1 + 1) 2 := MyEq.refl _

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

-- tacticについて

-- ライブラリについて

#check Unit

#print Unit

#print PUnit

#check True

#print True

#check Prop

#check Sort

#check Sort 1

#check Type

#check Sort 2

#check Type 1

example (α β : Type) (f : α → β) (a b : α) (h : a = b) : f a = f b := congrArg f h

#check congrArg

#print congrArg


def total (a b c : Nat) (d : Bool) : Nat :=
  if d then a + b + c + 1 else a + b + c

def total' (a b c : Nat) (d : Bool) : Nat :=
  match d with
  | true => a + b + c + 1
  | false => a + b + c

#eval total 1 2 3 true

#eval total' 1 2 3 false
