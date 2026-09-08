import Intro2

/-!
`Intro2.lean` の ✏ 練習の解答。
-/

/-! SOL 1.1 -/

instance : HasZero Bool where
  zero := false

example : HasZero Bool := inferInstance

#check zeroPair Bool

/-!
    zeroPair Bool : Pair Bool Bool

登録した瞬間から、`inferInstance` も `zeroPair Bool` のインスタンス引数の
自動解決も通るようになる。
-/

/-! SOL 1.2 -/

example : (zeroPair Bool).fst = HasZero.zero := zeroPair_fst Bool

/-!
`zeroPair_fst` は「ゼロが登録されたどんな型でも」成り立つ一般的な定理。
`Bool` を登録した瞬間から、その `Bool` での特殊化も使える。
-/

/-! SOL 1.3 -/

instance : Mul Point where
  mul p q := ⟨p.x * q.x, p.y * q.y⟩

#eval (Point.mk 2 3 * Point.mk 4 5).x

/-!
    8

`x` 成分どうしの積 `2 * 4`。登録すれば `*` がそのまま `Point` に使える。
-/

/-! SOL 2.1 -/

#check first 4

/-!
    first 4 : Fin (4 + 1)

定義どおり `Fin (4 + 1)`（計算すれば `Fin 5`）。
-/

#eval (first 4).val

/-!
    0

`first` は `n` によらず `0` を返す。
-/

/-! SOL 2.2 -/

#eval (5 : Fin 4)

/-!
    1

`(5 : Fin 3)` と同じ仕組みで、`5` を `4` で割った余りが入る。
-/

/-! SOL 2.3 -/

#check first 0

/-!
    first 0 : Fin (0 + 1)

`Fin (0 + 1)`——要素が1つしかない型で、その唯一の要素が `first 0` である。
-/

/-! SOL 2.4 -/

#eval (first 5).val + (2 : Fin 3).val

/-!
    2

`(first 5).val = 0`、`(2 : Fin 3).val = 2` で、和は `Nat` の `2`。
-/

/-! SOL 3.1 -/

syntax "⟬" term ", " term "⟭" : term

macro_rules
  | `(⟬$x, $y⟭) => `(Point.mk $x $y)

#check ⟬1, 2⟭

/-!
    { x := 1, y := 2 } : Point

読む方向だけの記法なので、表示では展開先の構成子の形が見える。
-/

/-! SOL 3.2 -/

infixl:65 " ⊞ " => add

#reduce MyNat.zero.succ ⊞ MyNat.zero.succ

/-!
    MyNat.zero.succ.succ

`1 + 1 = 2` にあたる `succ` 2つ。中置記法は `add` の適用に展開されている。
-/

/-! SOL 4.1 -/

theorem Set.subset_trans {X : Type} {s t u : Set X}
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  fun a ha => htu a (hst a ha)

/-!
点 `a` と `ha : a ∈ s` を受け取り、`hst` で `a ∈ t`、続けて `htu` で
`a ∈ u` を得る——含意の連鎖と同じ形である。
-/

/-! SOL 4.2 -/

def evens : Set Nat := {n | IsEven n}

example : (4 : Nat) ∈ evens := ⟨2, rfl⟩

/-!
`4 ∈ evens` は定義を展開すると `IsEven 4` すなわち `∃ k, 4 = 2 * k`。
証人 `2` と `rfl` で作れる。
-/

/-! SOL 4.3 -/

def allNat : Set Nat := {_n | True}

theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat :=
  fun _s _a _ha => True.intro

/-!
どの点でも示すべきは `True` なので、構成子 `True.intro` を返すだけ。
使わない引数は `_` 付きの名前にしてある。
-/

/-! SOL 4.4 -/

def odds : Set Nat := {n | ¬IsEven n}

#check (3 : Nat) ∈ odds

/-!
    3 ∈ odds : Prop

集合への所属は命題。中身が `¬…` でも、`∈` の式全体の型は `Prop` である。
-/

/-! SOL 5.1 -/

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
