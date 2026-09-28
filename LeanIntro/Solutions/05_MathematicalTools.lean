-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«05_MathematicalTools»

-- ✏ 練習 56 の解答

def pairAt (A : Type) (f g : A → Nat) : A → Point :=
  fun a => Point.mk (f a) (g a)

#eval (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3).x
#eval (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3).y

-- ✏ 練習 57 の解答

structure Circle : Type where
  center : Point
  radius : Nat

def makeCircle : Point → Nat → Circle := fun p n => Circle.mk p n

#eval (makeCircle (Point.mk 1 2) 3).center.x
#eval (makeCircle (Point.mk 1 2) 3).radius

-- ✏ 練習 58 の解答

def mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType :=
  PointedType.mk p.carrier (f p.point)

#reduce (mapPointed pointedNat Nat.succ).point

-- ✏ 練習 59 の解答

def addEven (n m : EvenNat) : EvenNat :=
  Subtype.mk (n.val + m.val)
    (match n.property with
    | Exists.intro k hk =>
      match m.property with
      | Exists.intro l hl =>
        Exists.intro (k + l)
          (Eq.trans
            (Eq.trans (congrArg (fun x => x + m.val) hk)
              (congrArg (fun x => 2 * k + x) hl))
            (Eq.symm (Nat.mul_add 2 k l))))

#eval (addEven evenFour evenFour).val

-- ✏ 練習 62 の解答

instance : Pointed Bool where
  point := false

#check (inferInstance : Pointed Bool)

def pointPair_bool_fst : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool

-- ✏ 練習 63 の解答

class Magma (α : Type) : Type where
  op : α → α → α

instance : Magma Nat where
  op := Nat.add

#check (inferInstance : Magma Nat)

-- ✏ 練習 64 の解答

def opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a

#eval opSelf Nat 3

-- ✏ 練習 65 の解答

instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β) where
  op p q := ⟨Magma.op p.fst q.fst, Magma.op p.snd q.snd⟩

#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd

-- ✏ 練習 66 の解答

instance : Mul Point where
  mul p q := ⟨p.x * q.x, p.y * q.y⟩

#eval (Point.mk 2 3 * Point.mk 4 5).x

-- ✏ 練習 60 の解答

syntax "⟬" term ", " term "⟭" : term

macro_rules
  | `(⟬$x, $y⟭) => `(Point.mk $x $y)

#check ⟬1, 2⟭

-- ✏ 練習 67 の解答

infixl:65 " ⊞ " => Nat.add

#reduce 1 ⊞ 1

-- ✏ 練習 61 の解答

def Set.subset_trans {X : Type} {s t u : Set X}
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  fun a ha => htu a (hst a ha)

-- ✏ 練習 68 の解答

def evens : Set Nat := {n | IsEven n}

def four_mem_evens : (4 : Nat) ∈ evens := ⟨2, rfl⟩

-- ✏ 練習 69 の解答

def allNat : Set Nat := {_n | True}

def subset_allNat : ∀ s : Set Nat, s ⊆ allNat :=
  fun _s _a _ha => True.intro

-- ✏ 練習 70 の解答

def odds : Set Nat := {n | ¬IsEven n}

#check (3 : Nat) ∈ odds

-- ✏ 練習 71 の解答

namespace Geometry

def unitX : Point := ⟨1, 0⟩

end Geometry

#check Geometry.unitX
