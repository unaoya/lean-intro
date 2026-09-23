import «01_TypesAndTerms»

/-!
`01_TypesAndTerms.lean` の練習の解答。本文の順に、型と項を確かめる。
-/

/-! SOL Intro1.terms-types:1 -/

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

/-! SOL Intro1.terms-types:2 -/

#check 3 < 5

/-!
    3 < 5 : Prop
-/

#check 5 < 3

/-!
    5 < 3 : Prop

`3 < 5` は真で `5 < 3` は偽だが、どちらも型は `Prop`。
`#check` は命題の真偽を調べていない——命題を表す項が型 `Prop` を持つことを
確認している。
-/

/-! SOL Intro1.definitions:1 -/

def z : Nat := 5

#check z

/-!
    z : Nat
-/

#eval z

/-!
    5
-/

#print z

/-!
    def z : Nat :=
    5

`#check` は型、`#eval` は計算した値、`#print` は宣言そのものを表示する。
-/

/-! SOL Intro1.definitions:2 -/

/-!
本文の `def x : Nat := 2` が使えることが前提である。この解答ファイルでは
`import Intro1` によって読み込まれている。別のファイルで単独で試すなら、先にその定義を書く。

受理されない。`x` の型は `Nat` で、コロンの右の `Bool` と一致しないから
型検査が失敗する:

    def oops : Bool := x

実行すると、次のエラーになる:

    error: Type mismatch
      x
    has type
      Nat
    but is expected to have type
      Bool

本文の `def bad : Nat :=` の例と同じく、「`:=` の右の項の型を計算し、
宣言された型と照合する」という手順の破れがそのまま報告されている。
-/

/-! SOL Intro1.functions:1 -/

def inc : Nat → Nat := fun n => n + 1

#check inc

/-!
    inc : Nat → Nat
-/

#eval inc 4

/-!
    5
-/

/-! SOL Intro1.functions:2 -/

def f : Nat → Nat := fun n => 2 * n + 3

#check f

/-!
    f : Nat → Nat
-/

#eval f 4

/-!
    11

`2 * 4 + 3 = 11`。数学の `2n` も、Lean では掛け算を明示して `2 * n` と書く。
-/

/-! SOL Intro1.functions:1 -/

def triple (n : Nat) : Nat := n + n + n

#check triple

/-!
    triple (n : Nat) : Nat

binder 形式のまま表示される。`triple : Nat → Nat` と読み替えられること。
-/

/-! SOL Intro1.functions:2 -/

#eval double (double 5)

/-!
    20

内側から: `double 5 = 10`、`double 10 = 20`。
-/

/-! SOL Intro1.functions:3 -/

def inc' (n : Nat) : Nat := n + 1

#check inc'

/-!
    inc' (n : Nat) : Nat
-/

#eval inc' 4

/-!
    5

表示は binder 形式になったが、型は `inc` と同じ `Nat → Nat`。値も同じである。
-/

/-! SOL Intro1.functions:4 -/

def f' (n : Nat) : Nat := 2 * n + 3

#check f'

/-!
    f' (n : Nat) : Nat
-/

#eval f' 4

/-!
    11

`f'` も `Nat → Nat` 型の関数であり、`f` と同じ計算をしている。
-/

/-! SOL Intro1.functions:1 -/

def addThree : Nat → Nat := plus 3

#check addThree

/-!
    addThree : Nat → Nat
-/

#eval addThree 4

/-!
    7
-/

/-! SOL Intro1.functions:2 -/

def g : Nat → Nat → Nat := fun a => fun b => 2 * a + 3 * b

#check g

/-!
    g : Nat → Nat → Nat
-/

#check g 2

/-!
    g 2 : Nat → Nat

1つ目の引数を渡したので、残りの引数を受け取る関数が返る。
-/

#eval g 2 4

/-!
    16
-/

/-! SOL Intro1.functions:1 -/

def g' (a : Nat) (b : Nat) : Nat := 2 * a + 3 * b

def g'' (a b : Nat) : Nat := 2 * a + 3 * b

#check g'

/-!
    g' (a b : Nat) : Nat
-/

#check g''

/-!
    g'' (a b : Nat) : Nat

宣言で型を別々に書いても、`#check` の表示では同じ型の引数がまとめられる。
いずれも `Nat → Nat → Nat` 型である。
-/

#eval g' 2 4

/-!
    16
-/

#eval g'' 2 4

/-!
    16
-/

/-! SOL Intro1.functions:1 -/

def twice (F : Nat → Nat) : Nat → Nat := fun n => F (F n)

#check twice

/-!
    twice (F : Nat → Nat) : Nat → Nat

矢印形式では `(Nat → Nat) → (Nat → Nat)`。数学でいう
Map(ℕ, ℕ) → Map(ℕ, ℕ) に対応している。
-/

#check twice double

/-!
    twice double : Nat → Nat
-/

#eval twice double 3

/-!
    12
-/

/-! SOL Intro1.functions:2 -/

def thrice (F : Nat → Nat) : Nat → Nat := fun n => F (F (F n))

#check thrice

/-!
    thrice (F : Nat → Nat) : Nat → Nat
-/

#check thrice double

/-!
    thrice double : Nat → Nat
-/

#eval thrice double 3

/-!
    24

`double` を3回適用するので、`3` → `6` → `12` → `24`。
-/

/-! SOL Intro1.functions:1 -/

#check Map Nat Bool

/-!
    Map Nat Bool : Type

`Map Nat Bool` は計算すると `Nat → Bool` になるが、`#check` が表示するのは
まず「型である」ということ（`: Type`）。
-/

def double2 : Map Nat Nat := double

#check double2

/-!
    double2 : Map Nat Nat

受理される。`Map Nat Nat` を計算すると `Nat → Nat` で、`double` の型と一致する。
表示には定義で指定した `Map Nat Nat` が残るが、同じ型として扱われている。
-/

/-! SOL Intro1.functions:2 -/

#check Map Nat

/-!
    Map Nat : Type → Type

2引数のうち1つだけ渡したので、「残り1つの型を受け取って型を返す」部分適用。
`plus 3 : Nat → Nat` と同じ形である。
-/

/-! SOL Intro1.functions:1 -/

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

/-! SOL Intro1.functions:2 -/

#eval applyTo21 (plus 100)

/-!
    121

`applyTo21 F` は `F 21` だから、`plus 100 21 = 121`。
-/

/-! SOL Intro1.functions:3 -/

def evalAt (F : Nat → Nat) (n : Nat) : Nat := F n

#check evalAt

/-!
    evalAt (F : Nat → Nat) (n : Nat) : Nat
-/

#eval evalAt double 5

/-!
    10
-/

def shift (F : Nat → Nat) : Nat → Nat := fun n => F (n + 1)

#check shift

/-!
    shift (F : Nat → Nat) : Nat → Nat
-/

#eval shift double 3

/-!
    8

`shift double` は「`n` に対して `double (n + 1)` を返す関数」。
`n = 3` なら `double 4 = 8`。
-/

/-! SOL Intro1.functions:4 -/

def useF1 : (Nat → Nat) → Nat := fun F => F 21

def useF2 : (Nat → Nat) → Nat := fun _ => 0

#check useF1

/-!
    useF1 : (Nat → Nat) → Nat
-/

#check useF2

/-!
    useF2 : (Nat → Nat) → Nat

どちらも同じ型を持つ。型は「関数を受け取って `Nat` を返す」という仕様だけを
決めており、返し方（中身）は何通りもある。
-/

/-! SOL Intro1.functions:5 -/

def compose (A B C : Type) (G : B → C) (F : A → B) : A → C := fun a => G (F a)

#check compose

/-!
    compose (A B C : Type) (G : B → C) (F : A → B) : A → C
-/

#eval compose Nat Nat Nat double (fun n => n + 1) 3

/-!
    8

内側から: `F = fun n => n + 1` で `3` が `4` に、`G = double` で `8` になる。
-/

/-! SOL Intro1.functions:6 -/

def evalAt' (A B : Type) (F : A → B) (a : A) : B := F a

def shift' (A : Type) (g : A → A) (F : A → A) : A → A := fun a => F (g a)

#check evalAt'

/-!
    evalAt' (A B : Type) (F : A → B) (a : A) : B
-/

#check shift'

/-!
    shift' (A : Type) (g F : A → A) : A → A
-/

#eval evalAt' Nat Nat double 5

/-!
    10
-/

#eval shift' Nat (fun x => x + 1) double 3

/-!
    8

どちらも元の版と同じ値。型を引数にすると、同じ中身が任意の型で使い回せる。
-/

/-! SOL Intro1.dependent-functions:1 -/

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

/-! SOL Intro1.dependent-functions:2 -/

def constAt (A B : Type) (a : A) : B → A := fun _ => a

#check constAt Nat Bool 5

/-!
    constAt Nat Bool 5 : Bool → Nat
-/

#eval constAt Nat Bool 5 true

/-!
    5

`idAt A` が恒等関数を返すのに対し、`constAt A B a` は定数関数を返す。
-/

/-! SOL Intro1.dependent-functions:1 -/

/-!
`Tuple 2` は `Fin 2 → Nat`。内側では番号 `i : Fin 2` を受け取り、自然数7を返す。
族 `Tuple` の行き先は `Type` だが、その型の項 `constTuple 2` の行き先は `Nat` である。
-/

/-! SOL Intro1.dependent-functions:2 -/

def repeatTuple (n : Nat) (a : Nat) : Tuple n := fun _ => a

#check repeatTuple 2 9

/-!
    repeatTuple 2 9 : Tuple 2

番号を一つ受け取り、どの番号にも a を返す。n は返す関数の定義域 `Fin n` を決めている。
-/
