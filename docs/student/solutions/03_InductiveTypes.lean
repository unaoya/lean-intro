-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«03_InductiveTypes»

-- ✏ 練習 42 の解答

#eval match Signal.yellow with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

#eval match Signal.green with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

-- ✏ 練習 43 の解答

def signalCode : Signal → Nat := fun s =>
  match s with
  | .red => 0
  | .yellow => 1
  | .green => 2

#eval signalCode Signal.yellow

-- ✏ 練習 44 の解答

def prev : Signal → Signal := fun s =>
  match s with
  | Signal.red    => Signal.yellow
  | Signal.yellow => Signal.green
  | Signal.green  => Signal.red

#eval prev (next Signal.red)

-- ✏ 練習 45 の解答

def isGreen : Signal → Bool := fun s =>
  match s with
  | Signal.green => true
  | _ => false

#eval isGreen Signal.red

-- ✏ 練習 46 の解答

def stopSignal : Signal := .red

#check stopSignal

#eval stopSignal

-- ✏ 練習 47 の解答

def tagOf : NatOrBool → Bool := fun x =>
  match x with
  | .nat _ => true
  | .bool _ => false

#eval tagOf (NatOrBool.nat 3)

-- ✏ 練習 48 の解答

#eval valueOf (NatOrBool.bool true)

-- ✏ 練習 49 の解答

def flagOf : NatOrBool → Bool := fun x =>
  match x with
  | .nat _  => false
  | .bool b => b

#eval flagOf (NatOrBool.bool true)

-- ✏ 練習 50 の解答

inductive NatPair : Type where
  | mk (a b : Nat) : NatPair

#check NatPair.mk

#check NatPair.mk 3 5

-- ✏ 練習 51 の解答

def firstNat : NatPair → Nat := fun p =>
  match p with
  | .mk a _ => a

def secondNat : NatPair → Nat := fun p =>
  match p with
  | .mk _ b => b

#check firstNat

#check secondNat

#eval firstNat (NatPair.mk 3 5)

#eval secondNat (NatPair.mk 3 5)

-- ✏ 練習 52 の解答

inductive FlaggedNat : Type where
  | mk (n : Nat) (flag : Bool) : FlaggedNat

#check FlaggedNat.mk

#check FlaggedNat.mk 3 true

-- ✏ 練習 53 の解答

def numberOf : FlaggedNat → Nat := fun p =>
  match p with
  | .mk n _ => n

def flagOfPair : FlaggedNat → Bool := fun p =>
  match p with
  | .mk _ flag => flag

#check numberOf

#check flagOfPair

#eval numberOf (FlaggedNat.mk 3 true)

#eval flagOfPair (FlaggedNat.mk 3 true)

-- ✏ 練習 54 の解答

inductive MixedData : Type where
  | pair (a b : Nat) : MixedData
  | flagged (n : Nat) (flag : Bool) : MixedData
  | empty : MixedData

#check MixedData.pair

#check MixedData.flagged

#check MixedData.empty

-- ✏ 練習 55 の解答

def readNumber : MixedData → Nat := fun x =>
  match x with
  | .pair a b => a + b
  | .flagged n _ => n
  | .empty => 0

#check readNumber

#eval readNumber (MixedData.pair 3 5)

#eval readNumber (MixedData.flagged 3 true)

#eval readNumber MixedData.empty

-- ✏ 練習 56 の解答

def mergeBool : MySum Bool Bool → Bool := fun x =>
  match x with
  | .inl b => b
  | .inr b => b

#eval mergeBool (MySum.inl true)

#eval mergeBool (MySum.inr false)

-- ✏ 練習 57 の解答

#eval getLeft 7 (MySum.inl 3 : MySum Nat Bool)

-- ✏ 練習 58 の解答

def isZeroMyNat : MyNat → Bool := fun n =>
  match n with
  | .zero => true
  | .succ _ => false

#eval isZeroMyNat MyNat.zero

#eval isZeroMyNat (MyNat.succ MyNat.zero)

-- ✏ 練習 59 の解答

def toN : MyNat → Nat := fun m =>
  match m with
  | .zero   => 0
  | .succ k => toN k + 1

#eval toN (MyNat.succ (MyNat.succ MyNat.zero))

-- ✏ 練習 60 の解答

def myThree : MyNat := MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero))

#reduce add myThree MyNat.zero

-- ✏ 練習 61 の解答

inductive Two : Type where
  | a : Two
  | b : Two

def toBool : Two → Bool := fun t =>
  match t with
  | .a => true
  | .b => false

def ofBool : Bool → Two := fun b =>
  match b with
  | true  => .a
  | false => .b

#eval toBool (ofBool true)

-- ✏ 練習 62 の解答

def g1 : Two → Bool := fun t =>
  match t with
  | .a => true
  | .b => true

def g2 : Two → Bool := fun t =>
  match t with
  | .a => true
  | .b => false

def g3 : Two → Bool := fun t =>
  match t with
  | .a => false
  | .b => true

def g4 : Two → Bool := fun t =>
  match t with
  | .a => false
  | .b => false

-- ✏ 練習 63 の解答

def mul : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | .zero   => .zero
  | .succ k => add (mul m k) m

#eval toN (mul myThree myThree)

-- ✏ 練習 64 の解答

def ofN : Nat → MyNat := fun n =>
  match n with
  | 0     => .zero
  | k + 1 => .succ (ofN k)

#eval toN (ofN 3)

-- ✏ 練習 65 の解答

def pairAt (A : Type) (f g : A → Nat) : A → Point :=
  fun a => Point.mk (f a) (g a)

#check pairAt

#eval Point.x (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3)

#eval Point.y (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3)

-- ✏ 練習 66 の解答

def moveRight (p : Point) : Point :=
  Point.mk (Point.x p + 1) (Point.y p)

#eval Point.x (moveRight (Point.mk 1 2))

-- ✏ 練習 67 の解答

def Point.zeroX (p : Point) : Point := .mk 0 p.y

#eval (Point.mk 1 2).zeroX.x

-- ✏ 練習 68 の解答

#eval (Point.mk 1 2).swap.swap.x

#eval Point.x (Point.swap (Point.swap (Point.mk 1 2)))

-- ✏ 練習 69 の解答

structure Circle : Type where
  center : Point
  radius : Nat

#check Circle.mk

#check Circle.center

-- ✏ 練習 70 の解答

def makeCircle : Point → Nat → Circle := fun p n => Circle.mk p n

#check makeCircle

#eval Circle.radius (makeCircle (Point.mk 1 2) 3)

-- ✏ 練習 71 の解答

def centerX : Circle → Nat := fun c => Point.x (Circle.center c)

#check centerX

#eval centerX (makeCircle (Point.mk 1 2) 3)

-- ✏ 練習 72 の解答

#eval Point.y (Point.mk 1 2)

#eval (Point.mk 1 2).y

-- ✏ 練習 73 の解答

structure Rect : Type where
  corner : Point
  width : Nat
  height : Nat

def r : Rect := ⟨⟨1, 2⟩, 10, 5⟩

#eval r.corner.x

-- ✏ 練習 74 の解答

def rectArea : Rect → Nat := fun s => s.width * s.height

#check rectArea

#eval rectArea r

-- ✏ 練習 75 の解答

#check Pair.mk true 0

-- ✏ 練習 76 の解答

def curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat := fun a b => F ⟨a, b⟩

def uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat := fun p => G p.fst p.snd

#check curryP

#check uncurryP

#eval curryP (fun p => p.fst + p.snd) 3 4

-- ✏ 練習 77 の解答

def pointedBool : PointedType := ⟨Bool, true⟩

#check PointedType.mk Nat

-- ✏ 練習 78 の解答

def attachNat : Nat → PointedType := fun n => ⟨Nat, n⟩

#check attachNat

#reduce (attachNat 3).point

-- ✏ 練習 79 の解答

def baseType : PointedType → Type := fun p => p.carrier

#check baseType

#reduce (types := true) baseType pointedNat

#reduce (types := true) baseType pointedBool

-- ✏ 練習 80 の解答

def mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType :=
  ⟨p.carrier, f p.point⟩

#check mapPointed

#reduce (mapPointed pointedNat Nat.succ).point

-- ✏ 練習 81 の解答

def getPoint (p : PointedType) : p.carrier := p.point

#check getPoint

#reduce getPoint pointedNat

#reduce getPoint pointedBool

-- ✏ 練習 82 の解答

def makePair (α β : Type) (a : α) (b : β) : Pair α β := Pair.mk a b

#check makePair Nat Bool 3 true

-- ✏ 練習 83 の解答

def swapAt (α β : Type) (a : α) (b : β) : Pair β α := Pair.mk b a

#check swapAt Nat Bool

-- ✏ 練習 84 の解答

#check idAt Signal

-- ✏ 練習 85 の解答

def flipNat (F : Nat → Nat → Nat) : Nat → Nat → Nat := fun a b => F b a

#eval flipNat (fun a b => a - b) 3 10

-- ✏ 練習 86 の解答

def iterate3 (F : Nat → Nat) : Nat → Nat := fun n => F (F (F n))

#eval iterate3 double 1

-- ✏ 練習 87 の解答

def boolToSignal : Bool → Signal := fun b =>
  match b with
  | true  => .green
  | false => .red

def signalToBool : Signal → Bool := fun s =>
  match s with
  | .green => true
  | _      => false

#eval signalToBool (boolToSignal true)

-- ✏ 練習 88 の解答

def mapPoint (F : Nat → Nat) (p : Point) : Point := ⟨F p.x, F p.y⟩

#eval (mapPoint double (Point.mk 2 3)).y

-- ✏ 練習 89 の解答

def swapMySum (A B : Type) : MySum A B → MySum B A := fun x =>
  match x with
  | .inl a => .inr a
  | .inr b => .inl b

#eval fromSum (swapMySum Bool Nat (MySum.inl true))

-- ✏ 練習 90 の解答

def pointedOf (A : Type) (a : A) : PointedType := ⟨A, a⟩

#check pointedOf Bool true

-- ✏ 練習 91 の解答

def applyN (A : Type) (F : A → A) (n : Nat) (a : A) : A :=
  match n with
  | 0     => a
  | k + 1 => F (applyN A F k a)

#eval applyN Nat double 3 1

-- ✏ 練習 92 の解答

def diag (A : Type) (a : A) : Pair A A := ⟨a, a⟩

#eval (diag Nat 3).fst
