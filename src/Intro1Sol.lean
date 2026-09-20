import Intro1

/-!
`Intro1.lean` の ✏ 練習の解答。`/-! SOL 節.番号 -/` の区切りごとに1問の解答で、
HTML では対応する練習の直下に折りたたみで埋め込まれる（このファイル自体は
公開ページにしない）。解答もすべて Lean の検査を通してある。
-/

/-! SOL 1.1 -/

#check Bool

/-!
    Bool : Type

`Bool` は型なので、その型は宇宙 `Type`。
-/

#check Type 2

/-!
    Type 2 : Type 3

宇宙の階段は1段のぼる: `Type n : Type (n + 1)`。
-/

/-! SOL 1.2 -/

#check 3 < 5

/-!
    3 < 5 : Prop

真偽によらず、命題であれば型は `Prop`。`3 < 5` が真かどうかを `#check` は
調べていない——「命題として文法・型が通っているか」だけを見ている。
-/

/-! SOL 2.1 -/

def five : Nat := 5

#check five

/-!
    five : Nat
-/

#eval five

/-!
    5
-/

#print five

/-!
    def five : Nat :=
    5

`#check` は型、`#eval` は計算した値、`#print` は宣言そのものを表示する。
-/

/-! SOL 2.2 -/

/-!
受理されない。`two` の型は `Nat` で、コロンの右の `Bool` と一致しないから
型検査が失敗する:

    def oops : Bool := two

    error: Type mismatch
      two
    has type
      Nat
    but is expected to have type
      Bool

本文の `def bad : Nat :=` の例と同じく、「`:=` の右の項の型を計算し、
宣言された型と照合する」という手順の破れがそのまま報告されている。
-/

/-! SOL 3.1 -/

def triple (n : Nat) : Nat := n + n + n

#check triple

/-!
    triple (n : Nat) : Nat

binder 形式のまま表示される。`triple : Nat → Nat` と読み替えられること。
-/

/-! SOL 3.2 -/

#eval double (double 5)

/-!
    20

内側から: `double 5 = 10`、`double 10 = 20`。
-/

/-! SOL 3.1 -/

/-!
型の計算: `(3 + 4) * 2` は `Nat`。`plus (double 3)` は `plus : Nat → Nat → Nat` に
第1引数だけ渡したので `Nat → Nat`（部分適用）。`applyTo21 (plus 3)` は
`applyTo21 : (Nat → Nat) → Nat` に関数を渡し切ったので `Nat`。
`fun n : Nat => plus n n` は `Nat` を受け取って `plus n n : Nat` を返すので
`Nat → Nat`。
-/

#check (3 + 4) * 2

/-!
    (3 + 4) * 2 : Nat
-/

#check plus (double 3)

/-!
    plus (double 3) : Nat → Nat
-/

#check applyTo21 (plus 3)

/-!
    applyTo21 (plus 3) : Nat
-/

#check fun n : Nat => plus n n

/-!
    fun n ↦ plus n n : Nat → Nat
-/

/-! SOL 3.2 -/

#eval applyTo21 (plus 100)

/-!
    121

`applyTo21 F` は `F 21` だから、`plus 100 21 = 121`。
-/

/-! SOL 3.3 -/

def evalAt (F : Nat → Nat) (x : Nat) : Nat := F x

#check evalAt

/-!
    evalAt (F : Nat → Nat) (x : Nat) : Nat
-/

#eval evalAt double 5

/-!
    10
-/

def shift (F : Nat → Nat) : Nat → Nat := fun x => F (x + 1)

#check shift

/-!
    shift (F : Nat → Nat) : Nat → Nat
-/

#eval shift double 3

/-!
    8

`shift double` は「`x` に対して `double (x + 1)` を返す関数」。
`x = 3` なら `double 4 = 8`。
-/

/-! SOL 3.4 -/

#check Map Nat Bool

/-!
    Map Nat Bool : Type

`Map Nat Bool` は計算すると `Nat → Bool` になるが、`#check` が表示するのは
まず「型である」ということ（`: Type`）。
-/

def double2 : Map Nat Nat := double

/-!
通る。`Map Nat Nat` を計算すると `Nat → Nat` で、`double` の型と一致する。
-/

/-! SOL 3.5 -/

def evalAt' (A B : Type) (F : A → B) (x : A) : B := F x

def shift' (A : Type) (g : A → A) (F : A → A) : A → A := fun x => F (g x)

#eval evalAt' Nat Nat double 5

/-!
    10
-/

#eval shift' Nat (fun x => x + 1) double 3

/-!
    8

どちらも元の版と同じ値。型を引数にすると、同じ中身が任意の型で使い回せる。
-/

/-! SOL 4.1 -/

def prev : Signal → Signal := fun s =>
  match s with
  | Signal.red    => Signal.yellow
  | Signal.yellow => Signal.green
  | Signal.green  => Signal.red

#reduce prev (next Signal.red)

/-!
    Signal.red

`next Signal.red = Signal.green`、`prev Signal.green = Signal.red` で戻ってくる。
-/

/-! SOL 4.2 -/

def isGreen : Signal → Bool := fun s =>
  match s with
  | Signal.green => true
  | _ => false

#eval isGreen Signal.red

/-!
    false
-/

/-! SOL 4.1 -/

#eval valueOf (NatOrBool.bool true)

/-!
    0

`bool` の札なので2つめの枝に入り、中身によらず `0` を返す。
-/

/-! SOL 4.2 -/

def flagOf : NatOrBool → Bool := fun x =>
  match x with
  | .nat _  => false
  | .bool b => b

#eval flagOf (NatOrBool.bool true)

/-!
    true
-/

/-! SOL 4.1 -/

#eval getLeft 7 (MySum.inl 3 : MySum Nat Bool)

/-!
    3

`inl` の札なので、既定値 `7` ではなく中身の `3` が返る。
-/

/-! SOL 4.1 -/

def myThree : MyNat := MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero))

#reduce add myThree MyNat.zero

/-!
    MyNat.zero.succ.succ.succ

`add m .zero => m` の枝に入るので、`myThree` そのものが返る。
-/

/-! SOL 4.2 -/

inductive Two where
  | a
  | b

def toBool : Two → Bool := fun t =>
  match t with
  | .a => true
  | .b => false

def ofBool : Bool → Two := fun b =>
  match b with
  | true  => .a
  | false => .b

#eval toBool (ofBool true)

/-!
    true
-/

/-! SOL 4.3 -/

def toN : MyNat → Nat := fun m =>
  match m with
  | .zero   => 0
  | .succ k => toN k + 1

def ofN : Nat → MyNat := fun n =>
  match n with
  | 0     => .zero
  | k + 1 => .succ (ofN k)

#eval toN (ofN 3)

/-!
    3

`ofN 3` は `succ (succ (succ zero))`、それを `toN` で戻すと `3`。
-/

/-! SOL 5.1 -/

structure Circle where
  center : Point
  radius : Nat

#check Circle.mk

/-!
    Circle.mk (center : Point) (radius : Nat) : Circle
-/

#check Circle.center

/-!
    Circle.center (self : Circle) : Point

構成子 `mk` と、フィールドごとの取り出し関数が自動で定義されている。
-/

/-! SOL 5.2 -/

#eval Point.y (Point.mk 1 2)

/-!
    2
-/

#eval (Point.mk 1 2).y

/-!
    2

同じ値。後ろに付けるドットは `Point.y (…)` の略記である。
-/

/-! SOL 5.1 -/

#check Pair.mk true 0

/-!
    { fst := true, snd := 0 } : Pair Bool Nat

第1引数 `true` から `α = Bool`、第2引数 `0` から `β = Nat` に決まる。
-/

/-! SOL 5.2 -/

def pointedBool : PointedType := ⟨Bool, true⟩

#check PointedType.mk Nat

/-!
    PointedType.mk Nat : Nat → PointedType

第1引数に `Nat` を渡した瞬間、残りの引数の型が `Nat` に決まる——
依存関数の部分適用である。
-/

/-! SOL 6.1 -/

#check idAt (Nat → Nat)

/-!
    idAt (Nat → Nat) : (Nat → Nat) → Nat → Nat

`A = Nat → Nat` を代入した `A → A`、つまり `(Nat → Nat) → Nat → Nat`。
右結合の約束で外側の括弧は表示されない。
-/

#eval idAt (Nat → Nat) double 21

/-!
    42

`idAt (Nat → Nat) double` は `double` そのもの。
-/

/-! SOL 6.2 -/

#check idAt Signal

/-!
    idAt Signal : Signal → Signal
-/

/-! SOL 6.1 -/

#check Map Nat

/-!
    Map Nat : Type → Type

2引数のうち1つだけ渡したので、「残り1つの型を受け取って型を返す」部分適用。
-/

/-! SOL 7.1 -/

#eval (Point.mk 1 2).swap.swap.x

/-!
    1

2回入れ替えて元どおり。フルネームでは
`Point.x (Point.swap (Point.swap (Point.mk 1 2)))` である:
-/

#eval Point.x (Point.swap (Point.swap (Point.mk 1 2)))

/-!
    1
-/

/-! SOL 7.2 -/

example : Signal := .red

/-!
期待される型が `Signal` なので、`.red` は `Signal.red` に解決される。
-/
