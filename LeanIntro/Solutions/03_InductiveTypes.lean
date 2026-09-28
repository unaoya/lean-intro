-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«03_InductiveTypes»

-- ✏ 練習 40 の解答

def signalCode : Signal → Nat := fun s =>
  match s with
  | Signal.red => 0
  | Signal.yellow => 1
  | Signal.green => 2

-- ✏ 練習 44 の解答

def attachLast : Nat → Numbered := fun n =>
  Numbered.mk (n + 1) (Fin.last n)

-- ✏ 練習 46 の解答

def one_le_three : 1 ≤ 3 := Nat.le.step (Nat.le.step Nat.le.refl)

def two_le_four_again : 2 ≤ 4 := succLeSuccByMatch 1 3 one_le_three

-- ✏ 練習 41 の解答

def prev : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.yellow
  | Signal.yellow => Signal.green
  | Signal.green => Signal.red

-- ✏ 練習 42 の解答

def swapSum {A B : Type} : MySum A B → MySum B A := fun s =>
  match s with
  | MySum.inl a => MySum.inr a
  | MySum.inr b => MySum.inl b

-- ✏ 練習 43 の解答

def pairMaps (X A B : Type) (f : X → A) (g : X → B) : X → MyPair A B :=
  fun x => MyPair.mk (f x) (g x)

-- ✏ 練習 47 の解答

def graphOf (A : Type) (B : A → Type) (f : (a : A) → B a) :
    A → FamilyPair A B := fun a => FamilyPair.mk a (f a)

-- ✏ 練習 45 の解答

def toNat : MyNat → Nat := fun n =>
  match n with
  | MyNat.zero => 0
  | MyNat.succ k => toNat k + 1

-- ✏ 練習 48 の解答

def leAddRight : ∀ n k : Nat, n ≤ n + k := fun n k =>
  match k with
  | Nat.zero => Nat.le.refl
  | Nat.succ j => Nat.le.step (leAddRight n j)

-- ✏ 練習 49 の解答

def zeroLeOfEq (n m : Nat) (h : n = m) (hn : 0 ≤ n) : 0 ≤ m :=
  match h with
  | Eq.refl _ => hn
