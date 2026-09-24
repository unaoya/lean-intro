-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«05_MathematicalTools»

-- ✏ 練習 120 の解答

instance : Pointed Bool where
  point := false

example : Pointed Bool := inferInstance

example : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool

-- ✏ 練習 121 の解答

class Magma (α : Type) : Type where
  op : α → α → α

instance : Magma Nat where
  op := Nat.add

example : Magma Nat := inferInstance

-- ✏ 練習 122 の解答

def opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a

#eval opSelf Nat 3

-- ✏ 練習 123 の解答

instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β) where
  op p q := ⟨Magma.op p.fst q.fst, Magma.op p.snd q.snd⟩

#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd

-- ✏ 練習 124 の解答

instance : Mul Point where
  mul p q := ⟨p.x * q.x, p.y * q.y⟩

#eval (Point.mk 2 3 * Point.mk 4 5).x

-- ✏ 練習 125 の解答

syntax "⟬" term ", " term "⟭" : term

macro_rules
  | `(⟬$x, $y⟭) => `(Point.mk $x $y)

#check ⟬1, 2⟭

-- ✏ 練習 126 の解答

infixl:65 " ⊞ " => add

#reduce MyNat.zero.succ ⊞ MyNat.zero.succ

-- ✏ 練習 127 の解答

theorem Set.subset_trans {X : Type} {s t u : Set X}
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  fun a ha => htu a (hst a ha)

-- ✏ 練習 128 の解答

def evens : Set Nat := {n | IsEven n}

example : (4 : Nat) ∈ evens := ⟨2, rfl⟩

-- ✏ 練習 129 の解答

def allNat : Set Nat := {_n | True}

theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat :=
  fun _s _a _ha => True.intro

-- ✏ 練習 130 の解答

def odds : Set Nat := {n | ¬IsEven n}

#check (3 : Nat) ∈ odds

-- ✏ 練習 131 の解答

namespace Geometry

def unitX : Point := ⟨1, 0⟩

end Geometry

#check Geometry.unitX
