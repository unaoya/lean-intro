import Intro2

/-!
`Intro2.lean` の ✏ 練習の解答。
-/

/-! SOL Intro2.classes:1 -/

instance : Pointed Bool where
  point := false

example : Pointed Bool := inferInstance

example : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool

/-!
登録した瞬間から、`inferInstance` の探索も、汎用関数 `pointPair` も、
一般的な定理 `pointPair_fst` も、すべて `Bool` で使えるようになる。
-/

/-! SOL Intro2.classes:2 -/

class Magma (α : Type) : Type where
  op : α → α → α

instance : Magma Nat where
  op := Nat.add

example : Magma Nat := inferInstance

/-!
手順は `Pointed` とまったく同じ——クラスを宣言し、`instance` で登録簿に
載せれば、`inferInstance` が見つける。フィールドが「点」から「二項演算」に
変わっただけである。
-/

/-! SOL Intro2.classes:3 -/

def opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a

#eval opSelf Nat 3

/-!
    6

`Nat` の登録簿には `op := Nat.add` を載せたので、`opSelf Nat 3 = 3 + 3`。
-/

/-! SOL Intro2.classes:4 -/

instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β) where
  op p q := ⟨Magma.op p.fst q.fst, Magma.op p.snd q.snd⟩

#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd

/-!
    22

`Magma (Pair Nat Nat)` は直接は登録していないが、誘導 instance と
`Magma Nat` の連鎖で見つかる。`.snd` は `2 + 20`。
-/

/-! SOL Intro2.classes:5 -/

instance : Mul Point where
  mul p q := ⟨p.x * q.x, p.y * q.y⟩

#eval (Point.mk 2 3 * Point.mk 4 5).x

/-!
    8

`x` 成分どうしの積 `2 * 4`。登録すれば `*` がそのまま `Point` に使える。
-/

/-! SOL Intro2.notation:1 -/

syntax "⟬" term ", " term "⟭" : term

macro_rules
  | `(⟬$x, $y⟭) => `(Point.mk $x $y)

#check ⟬1, 2⟭

/-!
    { x := 1, y := 2 } : Point

読む方向だけの記法なので、表示では展開先の構成子の形が見える。
-/

/-! SOL Intro2.notation:2 -/

infixl:65 " ⊞ " => add

#reduce MyNat.zero.succ ⊞ MyNat.zero.succ

/-!
    MyNat.zero.succ.succ

`1 + 1 = 2` にあたる `succ` 2つ。中置記法は `add` の適用に展開されている。
-/

/-! SOL Intro2.sets:1 -/

theorem Set.subset_trans {X : Type} {s t u : Set X}
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  fun a ha => htu a (hst a ha)

/-!
点 `a` と `ha : a ∈ s` を受け取り、`hst` で `a ∈ t`、続けて `htu` で
`a ∈ u` を得る——含意の連鎖と同じ形である。
-/

/-! SOL Intro2.sets:2 -/

def evens : Set Nat := {n | IsEven n}

example : (4 : Nat) ∈ evens := ⟨2, rfl⟩

/-!
`4 ∈ evens` は定義を展開すると `IsEven 4` すなわち `∃ k, 4 = 2 * k`。
証人 `2` と `rfl` で作れる。
-/

/-! SOL Intro2.sets:3 -/

def allNat : Set Nat := {_n | True}

theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat :=
  fun _s _a _ha => True.intro

/-!
どの点でも示すべきは `True` なので、構成子 `True.intro` を返すだけ。
使わない引数は `_` 付きの名前にしてある。
-/

/-! SOL Intro2.sets:4 -/

def odds : Set Nat := {n | ¬IsEven n}

#check (3 : Nat) ∈ odds

/-!
    3 ∈ odds : Prop

集合への所属は命題。中身が `¬…` でも、`∈` の式全体の型は `Prop` である。
-/

/-! SOL Intro2.namespaces:1 -/

namespace Geometry

def unitX : Point := ⟨1, 0⟩

end Geometry

#check Geometry.unitX

/-!
    Geometry.unitX : Point

フルネームなら外から見える。一方、接頭辞なしでは:

    #check unitX

    error: Unknown identifier `unitX`

`namespace` の中の名前には、外からは接頭辞が要る。
-/
