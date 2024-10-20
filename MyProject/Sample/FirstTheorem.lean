-- Lean入門

def my_first_theorem : 1 = 1 := Eq.refl 1

-- def my_first_theorem_error : 1 = 1 := asdfg

-- term : typeが基本的な書式

def m : Nat := 1

-- 項の型と中身を調べる

#check m
#print m

#check 1

#check my_first_theorem

def twice : Nat → Nat := fun n => n + n

#check twice
#print twice

def twice' (n : Nat) : Nat := n + n

#check twice
#print twice

def n : Nat := twice 3

#check Eq.refl
#print Eq.refl

#check 1 = 1

#check Eq

#check Eq 1 1
