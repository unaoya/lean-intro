import «05_MathematicalTools»

/-! `05_MathematicalTools.lean` の練習問題の解答。 -/

/-! SOL Trial5.structures-exercise-6e524f21:1 -/

def pairAt (A : Type) (f g : A → Nat) : A → Point :=
  fun a => Point.mk (f a) (g a)

#eval (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3).x
#eval (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3).y

/-!
    4
    6

同じ入力 `3` に `f` と `g` を適用し、それぞれの結果を成分としてまとめている。
本体は `⟨f a, g a⟩` と書いてもよい。
-/

/-! SOL Trial5.practice-review-1:1 -/

structure Circle : Type where
  center : Point
  radius : Nat

def makeCircle : Point → Nat → Circle := fun p n => Circle.mk p n

/-!
本体を `fun p n => ⟨p, n⟩` と書いてもよい。
期待される型 `Circle` から、構成子 `Circle.mk` が選ばれる。
-/

#eval (makeCircle (Point.mk 1 2) 3).center.x
#eval (makeCircle (Point.mk 1 2) 3).radius

/-!
    1
    3

`center : Point` を取り出してから、その `x : Nat` を取り出している。
-/

/-! SOL Trial5.practice-review-2:1 -/

def mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType :=
  PointedType.mk p.carrier (f p.point)

#reduce (mapPointed pointedNat Nat.succ).point

/-!
    1

`p.point : p.carrier` を `f` に渡し、同じ台の型と新しい点を組にして返す。
構成子の第二引数に要求される型は、第一引数の `p.carrier` によって決まる。
-/

/-! SOL Trial5.practice-review-3:1 -/

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

/-!
    8

第一成分に和を置くと、第二成分には `IsEven (n.val + m.val)` の証明が要求される。
二つの偶数性の証明を分解し、証人の和と等式の証明を組み立てて、この型の項を与えた。
-/

/-! SOL Trial5.practice:1 -/

instance : Pointed Bool where
  point := false

#check (inferInstance : Pointed Bool)

/-!
    inferInstance : Pointed Bool
-/

def pointPair_bool_fst : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool

/-!
登録した瞬間から、`inferInstance` の探索も、汎用関数 `pointPair` も、
一般的な定理 `pointPair_fst` も、すべて `Bool` で使えるようになる。
-/

/-! SOL Trial5.practice:2 -/

class Magma (α : Type) : Type where
  op : α → α → α

instance : Magma Nat where
  op := Nat.add

#check (inferInstance : Magma Nat)

/-!
    inferInstance : Magma Nat
-/

/-!
手順は `Pointed` とまったく同じ——クラスを宣言し、`instance` で登録簿に
載せれば、`inferInstance` が見つける。フィールドが「点」から「二項演算」に
変わっただけである。
-/

/-! SOL Trial5.practice:3 -/

def opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a

#eval opSelf Nat 3

/-!
    6

`Nat` の登録簿には `op := Nat.add` を載せたので、`opSelf Nat 3 = 3 + 3`。
-/

/-! SOL Trial5.practice:4 -/

instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β) where
  op p q := ⟨Magma.op p.fst q.fst, Magma.op p.snd q.snd⟩

#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd

/-!
    22

`Magma (Pair Nat Nat)` は直接は登録していないが、誘導 instance と
`Magma Nat` の連鎖で見つかる。`.snd` は `2 + 20`。
-/

/-! SOL Trial5.practice:5 -/

instance : Mul Point where
  mul p q := ⟨p.x * q.x, p.y * q.y⟩

#eval (Point.mk 2 3 * Point.mk 4 5).x

/-!
    8

`x` 成分どうしの積 `2 * 4`。登録すれば `*` がそのまま `Point` に使える。
-/

/-! SOL Trial5.practice-review-9:1 -/

syntax "⟬" term ", " term "⟭" : term

macro_rules
  | `(⟬$x, $y⟭) => `(Point.mk $x $y)

#check ⟬1, 2⟭

/-!
    { x := 1, y := 2 } : Point

読む方向だけの記法なので、表示では展開先の構成子の形が見える。
-/

/-! SOL Trial5.practice:6 -/

infixl:65 " ⊞ " => Nat.add

#reduce 1 ⊞ 1

/-!
    2

中置記法は `Nat.add` の適用に展開され、`1 + 1` が計算されている。
-/

/-! SOL Trial5.practice-review-11:1 -/

def Set.subset_trans {X : Type} {s t u : Set X}
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  fun a ha => htu a (hst a ha)

/-!
点 `a` と `ha : a ∈ s` を受け取り、`hst` で `a ∈ t`、続けて `htu` で
`a ∈ u` を得る——含意の連鎖と同じ形である。
-/

/-! SOL Trial5.practice:7 -/

def evens : Set Nat := {n | IsEven n}

def four_mem_evens : (4 : Nat) ∈ evens := ⟨2, rfl⟩

/-!
`4 ∈ evens` は定義を展開すると `IsEven 4` すなわち `∃ k, 4 = 2 * k`。
証人 `2` と `rfl` で作れる。
-/

/-! SOL Trial5.practice:8 -/

def allNat : Set Nat := {_n | True}

def subset_allNat : ∀ s : Set Nat, s ⊆ allNat :=
  fun _s _a _ha => True.intro

/-!
どの点でも示すべきは `True` なので、構成子 `True.intro` を返すだけ。
使わない引数は `_` 付きの名前にしてある。
-/

/-! SOL Trial5.practice:9 -/

def odds : Set Nat := {n | ¬IsEven n}

#check (3 : Nat) ∈ odds

/-!
    3 ∈ odds : Prop

集合への所属は命題。中身が `¬…` でも、`∈` の式全体の型は `Prop` である。
-/

/-! SOL Trial5.practice:10 -/

namespace Geometry

def unitX : Point := ⟨1, 0⟩

end Geometry

#check Geometry.unitX

/-!
    Geometry.unitX : Point

フルネームなら外から見える。接頭辞なしの `#check unitX` は
`Unknown identifier` というエラーになる。
-/
