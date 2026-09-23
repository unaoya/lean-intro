import Intro1

/-!
`Intro1.lean` の ✏ 練習の解答。`/-! SOL 固定ラベル:問題番号 -/` の区切りごとに1問の解答で、
HTML では対応する練習の直下に折りたたみで埋め込まれる（このファイル自体は
公開ページにしない）。解答もすべて Lean の検査を通してある。
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

/-! SOL Intro1.inductive-types:1 -/

#eval match Signal.yellow with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

/-!
    Signal.red
-/

#eval match Signal.green with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

/-!
    Signal.yellow

対象の構成子に対応する場合が選ばれる。`Signal.yellow` なら3つ目、
`Signal.green` なら2つ目の場合である。
-/

/-! SOL Intro1.inductive-types:1 -/

def signalCode : Signal → Nat := fun s =>
  match s with
  | .red => 0
  | .yellow => 1
  | .green => 2

#eval signalCode Signal.yellow

/-!
    1
-/

/-! SOL Intro1.inductive-types:1 -/

def prev : Signal → Signal := fun s =>
  match s with
  | Signal.red    => Signal.yellow
  | Signal.yellow => Signal.green
  | Signal.green  => Signal.red

#eval prev (next Signal.red)

/-!
    Signal.red

`next Signal.red = Signal.green`、`prev Signal.green = Signal.red` で戻ってくる。
-/

/-! SOL Intro1.inductive-types:2 -/

def isGreen : Signal → Bool := fun s =>
  match s with
  | Signal.green => true
  | _ => false

#eval isGreen Signal.red

/-!
    false
-/

/-! SOL Intro1.inductive-types:3 -/

def stopSignal : Signal := .red

#check stopSignal

/-!
    stopSignal : Signal
-/

#eval stopSignal

/-!
    Signal.red

宣言の `: Signal` から期待される型が分かるので、`.red` は `Signal.red` に解決される。
-/

/-! SOL Intro1.inductive-types:1 -/

def tagOf : NatOrBool → Bool := fun x =>
  match x with
  | .nat _ => true
  | .bool _ => false

#eval tagOf (NatOrBool.nat 3)

/-!
    true
-/

/-! SOL Intro1.inductive-types:1 -/

#eval valueOf (NatOrBool.bool true)

/-!
    0

`bool` の札なので2つ目の場合に当たり、中身によらず `0` を返す。
-/

/-! SOL Intro1.inductive-types:2 -/

def flagOf : NatOrBool → Bool := fun x =>
  match x with
  | .nat _  => false
  | .bool b => b

#eval flagOf (NatOrBool.bool true)

/-!
    true
-/

/-! SOL Intro1.inductive-types:1 -/

inductive NatPair : Type where
  | mk (a b : Nat) : NatPair

#check NatPair.mk

/-!
    NatPair.mk (a b : Nat) : NatPair
-/

#check NatPair.mk 3 5

/-!
    NatPair.mk 3 5 : NatPair
-/

/-! SOL Intro1.inductive-types:2 -/

def firstNat : NatPair → Nat := fun p =>
  match p with
  | .mk a _ => a

def secondNat : NatPair → Nat := fun p =>
  match p with
  | .mk _ b => b

#check firstNat

/-!
    firstNat : NatPair → Nat
-/

#check secondNat

/-!
    secondNat : NatPair → Nat
-/

#eval firstNat (NatPair.mk 3 5)

/-!
    3
-/

#eval secondNat (NatPair.mk 3 5)

/-!
    5
-/

/-! SOL Intro1.inductive-types:1 -/

inductive FlaggedNat : Type where
  | mk (n : Nat) (flag : Bool) : FlaggedNat

#check FlaggedNat.mk

/-!
    FlaggedNat.mk (n : Nat) (flag : Bool) : FlaggedNat
-/

#check FlaggedNat.mk 3 true

/-!
    FlaggedNat.mk 3 true : FlaggedNat
-/

/-! SOL Intro1.inductive-types:2 -/

def numberOf : FlaggedNat → Nat := fun p =>
  match p with
  | .mk n _ => n

def flagOfPair : FlaggedNat → Bool := fun p =>
  match p with
  | .mk _ flag => flag

#check numberOf

/-!
    numberOf : FlaggedNat → Nat
-/

#check flagOfPair

/-!
    flagOfPair : FlaggedNat → Bool
-/

#eval numberOf (FlaggedNat.mk 3 true)

/-!
    3
-/

#eval flagOfPair (FlaggedNat.mk 3 true)

/-!
    true
-/

/-! SOL Intro1.inductive-types:1 -/

inductive MixedData : Type where
  | pair (a b : Nat) : MixedData
  | flagged (n : Nat) (flag : Bool) : MixedData
  | empty : MixedData

#check MixedData.pair

/-!
    MixedData.pair (a b : Nat) : MixedData
-/

#check MixedData.flagged

/-!
    MixedData.flagged (n : Nat) (flag : Bool) : MixedData
-/

#check MixedData.empty

/-!
    MixedData.empty : MixedData
-/

/-! SOL Intro1.inductive-types:2 -/

def readNumber : MixedData → Nat := fun x =>
  match x with
  | .pair a b => a + b
  | .flagged n _ => n
  | .empty => 0

#check readNumber

/-!
    readNumber : MixedData → Nat
-/

#eval readNumber (MixedData.pair 3 5)

/-!
    8
-/

#eval readNumber (MixedData.flagged 3 true)

/-!
    3
-/

#eval readNumber MixedData.empty

/-!
    0
-/

/-! SOL Intro1.inductive-types:1 -/

def mergeBool : MySum Bool Bool → Bool := fun x =>
  match x with
  | .inl b => b
  | .inr b => b

#eval mergeBool (MySum.inl true)

/-!
    true
-/

#eval mergeBool (MySum.inr false)

/-!
    false
-/

/-! SOL Intro1.inductive-types:1 -/

#eval getLeft 7 (MySum.inl 3 : MySum Nat Bool)

/-!
    3

`inl` の札なので、既定値 `7` ではなく中身の `3` が返る。
-/

/-! SOL Intro1.inductive-types:1 -/

def isZeroMyNat : MyNat → Bool := fun n =>
  match n with
  | .zero => true
  | .succ _ => false

#eval isZeroMyNat MyNat.zero

/-!
    true
-/

#eval isZeroMyNat (MyNat.succ MyNat.zero)

/-!
    false
-/

/-! SOL Intro1.inductive-types:2 -/

def toN : MyNat → Nat := fun m =>
  match m with
  | .zero   => 0
  | .succ k => toN k + 1

#eval toN (MyNat.succ (MyNat.succ MyNat.zero))

/-!
    2
-/

/-! SOL Intro1.inductive-types:1 -/

def myThree : MyNat := MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero))

#reduce add myThree MyNat.zero

/-!
    MyNat.zero.succ.succ.succ

第2引数が `.zero` の場合なので、`myThree` そのものが返る。
-/

/-! SOL Intro1.inductive-types:2 -/

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

/-!
    true
-/

/-! SOL Intro1.inductive-types:3 -/

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

/-!
`g2` が前問の `toBool` と同じ対応である。2点 `a`・`b` それぞれに行き先が
2通りずつあるので、関数は 2 × 2 = 4 通り——`match` のそれぞれの場合に返す項の指定が
ちょうど対応表の書き方になっている。
-/

/-! SOL Intro1.inductive-types:4 -/

def mul : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | .zero   => .zero
  | .succ k => add (mul m k) m

#eval toN (mul myThree myThree)

/-!
    9

`add` と同じく、第2引数の構造にそった再帰である。3 × 3 = 9。
-/


/-! SOL Intro1.inductive-types:5 -/

def ofN : Nat → MyNat := fun n =>
  match n with
  | 0     => .zero
  | k + 1 => .succ (ofN k)

#eval toN (ofN 3)

/-!
    3

`ofN 3` は `succ (succ (succ zero))`、それを `toN` で戻すと `3`。
-/

/-! SOL Intro1.structures:1 -/

def pairAt (A : Type) (f g : A → Nat) : A → Point :=
  fun a => Point.mk (f a) (g a)

#check pairAt

/-!
    pairAt (A : Type) (f g : A → Nat) : A → Point
-/

#eval Point.x (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3)

/-!
    4
-/

#eval Point.y (pairAt Nat (fun n => n + 1) (fun n => 2 * n) 3)

/-!
    6

第1成分を取り出すと f(3) = 4、第2成分を取り出すと g(3) = 6 に戻る。
-/

/-! SOL Intro1.structures:1 -/

def moveRight (p : Point) : Point :=
  Point.mk (Point.x p + 1) (Point.y p)

#eval Point.x (moveRight (Point.mk 1 2))

/-!
    2
-/

/-! SOL Intro1.structures:1 -/

def Point.zeroX (p : Point) : Point := .mk 0 p.y

#eval (Point.mk 1 2).zeroX.x

/-!
    0
-/

/-! SOL Intro1.structures:2 -/

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

/-! SOL Intro1.structures:1 -/

structure Circle : Type where
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

/-! SOL Intro1.structures:2 -/

def makeCircle : Point → Nat → Circle := fun p n => Circle.mk p n

#check makeCircle

/-!
    makeCircle : Point → Nat → Circle
-/

#eval Circle.radius (makeCircle (Point.mk 1 2) 3)

/-!
    3
-/

/-! SOL Intro1.structures:3 -/

def centerX : Circle → Nat := fun c => Point.x (Circle.center c)

#check centerX

/-!
    centerX : Circle → Nat
-/

#eval centerX (makeCircle (Point.mk 1 2) 3)

/-!
    1

まず `Circle` 型の項から `Point` 型の中心を取り出し、次にその第1座標である `Nat` 型の項を取り出す。
関数適用をドットで書けば、本体は `c.center.x` とも書ける。
-/

/-! SOL Intro1.structures:1 -/

#eval Point.y (Point.mk 1 2)

/-!
    2
-/

#eval (Point.mk 1 2).y

/-!
    2

同じ値。後ろに付けるドットは `Point.y (…)` の略記である。
-/

/-! SOL Intro1.structures:2 -/

structure Rect : Type where
  corner : Point
  width : Nat
  height : Nat

def r : Rect := ⟨⟨1, 2⟩, 10, 5⟩

#eval r.corner.x

/-!
    1

外側の `⟨ ⟩` が `Rect` の3フィールド、内側の `⟨1, 2⟩` が `corner : Point` の
2フィールドに当たる。`r.corner.x` は `Point.x (Rect.corner r)` の略記である。
-/

/-! SOL Intro1.structures:3 -/

def rectArea : Rect → Nat := fun s => s.width * s.height

#check rectArea

/-!
    rectArea : Rect → Nat
-/

#eval rectArea r

/-!
    50
-/

/-! SOL Intro1.structures:1 -/

#check Pair.mk true 0

/-!
    { fst := true, snd := 0 } : Pair Bool Nat

第1引数 `true` から `α = Bool`、第2引数 `0` から `β = Nat` に決まる。
-/

/-! SOL Intro1.structures:2 -/

def curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat := fun a b => F ⟨a, b⟩

def uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat := fun p => G p.fst p.snd

#check curryP

/-!
    curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat
-/

#check uncurryP

/-!
    uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat
-/

#eval curryP (fun p => p.fst + p.snd) 3 4

/-!
    7

`curryP` は「1つずつ受け取って、組にしてから `F` に渡す」、`uncurryP` は
「組を受け取って、成分にばらしてから `G` に渡す」。[3節](#sec-Intro1.functions)の「2引数関数の正体は
1引数関数の入れ子」という話の、行き来を自分で書いたことになる。
-/

/-! SOL Intro1.structures:1 -/

def pointedBool : PointedType := ⟨Bool, true⟩

#check PointedType.mk Nat

/-!
    PointedType.mk Nat : Nat → PointedType

第1引数に `Nat` を渡した瞬間、残りの引数の型が `Nat` に決まる——
依存関数の部分適用である。
-/

/-! SOL Intro1.structures:1 -/

def attachNat : Nat → PointedType := fun n => ⟨Nat, n⟩

#check attachNat

/-!
    attachNat : Nat → PointedType
-/

#reduce (attachNat 3).point

/-!
    3
-/

/-! SOL Intro1.structures:2 -/

def baseType : PointedType → Type := fun p => p.carrier

#check baseType

/-!
    baseType : PointedType → Type
-/

#reduce (types := true) baseType pointedNat

/-!
    Nat
-/

#reduce (types := true) baseType pointedBool

/-!
    Bool

結果は型だが、`Type` の項を返すという意味では、これも通常の関数である。
`(types := true)` を付けたので、型を返す式も計算され、`Nat`・`Bool` と表示された。
-/

/-! SOL Intro1.structures:3 -/

def mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType :=
  ⟨p.carrier, f p.point⟩

#check mapPointed

/-!
    mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType
-/

#reduce (mapPointed pointedNat Nat.succ).point

/-!
    1

`pointedNat` の台は `Nat`、点は `0` なので、点を `Nat.succ 0` に取り替える。
-/

/-! SOL Intro1.structures:1 -/

def getPoint (p : PointedType) : p.carrier := p.point

#check getPoint

/-!
    getPoint (p : PointedType) : p.carrier

結果の型 `p.carrier` に引数 `p` が現れている。
-/

#reduce getPoint pointedNat

/-!
    0
-/

#reduce getPoint pointedBool

/-!
    true
-/


/-! SOL Intro1.dependent-functions:1 -/

def makePair (α β : Type) (a : α) (b : β) : Pair α β := Pair.mk a b

#check makePair Nat Bool 3 true

/-!
    makePair Nat Bool 3 true : Pair Nat Bool
-/

/-! SOL Intro1.dependent-functions:2 -/

def swapAt (α β : Type) (a : α) (b : β) : Pair β α := Pair.mk b a

#check swapAt Nat Bool

/-!
    swapAt Nat Bool : Nat → Bool → Pair Bool Nat
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

#check idAt Signal

/-!
    idAt Signal : Signal → Signal
-/

/-! SOL Intro1.dependent-functions:3 -/

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


/-! SOL Intro1.exercises:1 -/

def flipNat (F : Nat → Nat → Nat) : Nat → Nat → Nat := fun a b => F b a

#eval flipNat (fun a b => a - b) 3 10

/-!
    7

`flipNat F 3 10 = F 10 3 = 10 - 3`。
-/

/-! SOL Intro1.exercises:2 -/

def iterate3 (F : Nat → Nat) : Nat → Nat := fun n => F (F (F n))

#eval iterate3 double 1

/-!
    8

`1 → 2 → 4 → 8`。
-/

/-! SOL Intro1.exercises:3 -/

def boolToSignal : Bool → Signal := fun b =>
  match b with
  | true  => .green
  | false => .red

def signalToBool : Signal → Bool := fun s =>
  match s with
  | .green => true
  | _      => false

#eval signalToBool (boolToSignal true)

/-!
    true

`true → .green → true` と往復する（`false` 側も同様に戻る。ただし
`.yellow` から出発すると `false → .red` となり、往復では戻らない——
2点の型と3点の型なので、両方向の往復が恒等にはなりようがない）。
-/

/-! SOL Intro1.exercises:4 -/

def mapPoint (F : Nat → Nat) (p : Point) : Point := ⟨F p.x, F p.y⟩

#eval (mapPoint double (Point.mk 2 3)).y

/-!
    6
-/

/-! SOL Intro1.exercises:5 -/

def swapMySum (A B : Type) : MySum A B → MySum B A := fun x =>
  match x with
  | .inl a => .inr a
  | .inr b => .inl b

#eval fromSum (swapMySum Bool Nat (MySum.inl true))

/-!
    0

`.inl true : MySum Bool Nat` は札を掛け替えると `.inr true : MySum Nat Bool`。
`fromSum` は `.inr` の場合に `0` を返す。
-/

/-! SOL Intro1.exercises:6 -/

def pointedOf (A : Type) (a : A) : PointedType := ⟨A, a⟩

#check pointedOf Bool true

/-!
    pointedOf Bool true : PointedType

`pointedNat = pointedOf Nat 0`、`pointedBool = pointedOf Bool true` である。
-/

/-! SOL Intro1.exercises:7 -/

def applyN (A : Type) (F : A → A) (n : Nat) (a : A) : A :=
  match n with
  | 0     => a
  | k + 1 => F (applyN A F k a)

#eval applyN Nat double 3 1

/-!
    8

`iterate3` の一般化。`applyN Nat double 3 = iterate3 double` である。
-/

/-! SOL Intro1.exercises:8 -/

def diag (A : Type) (a : A) : Pair A A := ⟨a, a⟩

#eval (diag Nat 3).fst

/-!
    3

手持ちの `A` の項は `a` だけなので、`⟨a, a⟩` 以外に返せるものがない。
型が具体的（`(Nat → Nat) → Nat` など）だと中身の自由度が大きく、
型変数だけで書かれた仕様ほど中身が絞られる、という対比である。
-/
