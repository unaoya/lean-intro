-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«01_TypesAndTerms»

-- ✏ 練習 1 の解答

#check Bool

#check Type 2

-- ✏ 練習 2 の解答

#check 3 < 5

#check 5 < 3

-- ✏ 練習 3 の解答

def z : Nat := 5

#check z

#eval z

#print z

-- ✏ 練習 4 の解答

-- ✏ 練習 5 の解答

def inc : Nat → Nat := fun n => n + 1

#check inc

#eval inc 4

-- ✏ 練習 6 の解答

def f : Nat → Nat := fun n => 2 * n + 3

#check f

#eval f 4

-- ✏ 練習 7 の解答

def triple (n : Nat) : Nat := n + n + n

#check triple

-- ✏ 練習 8 の解答

#eval double (double 5)

-- ✏ 練習 9 の解答

def inc' (n : Nat) : Nat := n + 1

#check inc'

#eval inc' 4

-- ✏ 練習 10 の解答

def f' (n : Nat) : Nat := 2 * n + 3

#check f'

#eval f' 4

-- ✏ 練習 11 の解答

def addThree : Nat → Nat := plus 3

#check addThree

#eval addThree 4

-- ✏ 練習 12 の解答

def g : Nat → Nat → Nat := fun a => fun b => 2 * a + 3 * b

#check g

#check g 2

#eval g 2 4

-- ✏ 練習 13 の解答

def g' (a : Nat) (b : Nat) : Nat := 2 * a + 3 * b

def g'' (a b : Nat) : Nat := 2 * a + 3 * b

#check g'

#check g''

#eval g' 2 4

#eval g'' 2 4

-- ✏ 練習 14 の解答

def twice (F : Nat → Nat) : Nat → Nat := fun n => F (F n)

#check twice

#check twice double

#eval twice double 3

-- ✏ 練習 15 の解答

def thrice (F : Nat → Nat) : Nat → Nat := fun n => F (F (F n))

#check thrice

#check thrice double

#eval thrice double 3

-- ✏ 練習 16 の解答

#check Map Nat Bool

def double2 : Map Nat Nat := double

#check double2

-- ✏ 練習 17 の解答

#check Map Nat

-- ✏ 練習 18 の解答

#check (3 + 4) * 2

#check plus (double 3)

#check applyTo21 (plus 3)

#check fun n : Nat => plus n n

-- ✏ 練習 19 の解答

#eval applyTo21 (plus 100)

-- ✏ 練習 20 の解答

def evalAt (F : Nat → Nat) (n : Nat) : Nat := F n

#check evalAt

#eval evalAt double 5

def shift (F : Nat → Nat) : Nat → Nat := fun n => F (n + 1)

#check shift

#eval shift double 3

-- ✏ 練習 21 の解答

def useF1 : (Nat → Nat) → Nat := fun F => F 21

def useF2 : (Nat → Nat) → Nat := fun _ => 0

#check useF1

#check useF2

-- ✏ 練習 22 の解答

def compose (A B C : Type) (G : B → C) (F : A → B) : A → C := fun a => G (F a)

#check compose

#eval compose Nat Nat Nat double (fun n => n + 1) 3

-- ✏ 練習 23 の解答

def evalAt' (A B : Type) (F : A → B) (a : A) : B := F a

def shift' (A : Type) (g : A → A) (F : A → A) : A → A := fun a => F (g a)

#check evalAt'

#check shift'

#eval evalAt' Nat Nat double 5

#eval shift' Nat (fun x => x + 1) double 3

-- ✏ 練習 24 の解答

#check idAt (Nat → Nat)

#eval idAt (Nat → Nat) double 21

-- ✏ 練習 25 の解答

def constAt (A B : Type) (a : A) : B → A := fun _ => a

#check constAt Nat Bool 5

#eval constAt Nat Bool 5 true

-- ✏ 練習 26 の解答

-- ✏ 練習 27 の解答

def repeatTuple (n : Nat) (a : Nat) : Tuple n := fun _ => a

#check repeatTuple 2 9
