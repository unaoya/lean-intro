/-!
# Lean 最小限の導入

この教材（Intro → CH → Top の3ファイル）の目標は、
**数学的概念やその証明をプログラムとして書くとはどういうことか**、そして
**なぜそれで証明の正しさを検証したと思えるのか**、を実感することにある。
Lean を網羅的に紹介することは目的ではない。このファイルでも、
`CH.lean`（型と命題の対応）と `Top.lean`（位相空間）を読むのに
最低限必要な機能しか説明しない。

このファイルで伝えたいことは2つ。

* Lean のもっとも基本の要素は**項**と**型**である。
  Lean に書くことはすべて「項 `a` は型 `α` を持つ」（`a : α` と書く）の組み立てである。
* 型を作る部品は実質2つ、**帰納型**（inductive type）と**依存関数型**である。
  ふだん目にする `→` `×` `∧` `∀` `structure` などは、すべてこの2つの現れである。
-/

/-! ## 1. 項と型

Lean に書くものの基本の単位を**項**（term）と呼ぶ。項とは何かの正確な定義は
ここでは与えないが、さしあたり **`#check` の右側に書けるものは項だと考えてよい**。
`#check e` は、項 `e` の**型**を調べて表示するコマンドである。
-/

#check 3

/-!
エディタ右側のパネル（Infoview）には、次のように表示される:

    3 : Nat

これは「項 `3` は型 `Nat`（自然数の型）を持つ」と読む。
-/

#check true

/-!
    Bool.true : Bool

「項 `true` は型 `Bool`（真偽値の型）を持つ」。表示が `Bool.true` となっているのは、
これが `true` の正式な名前だからである（`Bool` の項であることが名前に刻まれている。
この命名の仕組みは5節で見る）。

すべての項はちょうど1つの型を持つ。ここで大事な観察が1つある。
**型を表す表記それ自体もまた項である**。実際、`Nat` を `#check` の右に書くと:
-/

#check Nat

/-!
    Nat : Type

`Nat` という表記は、`Type` という型を持つ項なのである
（以下ではこのことを、少し縮めて「型も項である」と言う）。では `Type` は？
-/

#check Type

/-!
    Type : Type 1

`Type` もまた項であり、その型は `Type 1`。この階段は上へ続いていく:
-/

#check Type 1

/-!
    Type 1 : Type 2

`Type`, `Type 1`, `Type 2`, … の階層を宇宙（universe）と呼び、
`universe u` と宣言して任意の段 `Type u` を扱える。
この教材では宇宙には**深入りしない**。階層があること、そしてもう1つ、
次の宇宙があることだけ押さえれば足りる:
-/

#check Prop

/-!
    Prop : Type

`Prop` は**命題**たちの住む宇宙である（4節で主役になる）。

型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（8節）。

### 先取り: 演算と命題の記号

数の演算や、等式・不等式の記号も、ふつうに書ける。それぞれが正確には何者なのかは
後の節で説明することにして（`+` は3節、`=` と `<` は4節）、表示だけ先に見ておく。
-/

#check 3 + 4

/-!
    3 + 4 : Nat

数から作った式は、また数の項になる。
-/

#check 1 + 1 = 2

/-!
    1 + 1 = 2 : Prop

等式は**命題**の項になる——`Prop` の住人がさっそく現れた。
-/

#check 2 < 1

/-!
    2 < 1 : Prop

`2 < 1` のような**偽の命題も**、命題としては立派な項であることに注意
（真偽の話は4節で）。

この節で覚えるべきことは2つだけである:
**項の型はいつでも `#check` で調べられる**こと、そして**型も項である**こと。
-/

/-! ### ✏ 練習

1. `#check Bool` と `#check Type 2` の表示を予想してから確かめよ。
2. `#check 3 < 5` の表示を予想してから確かめよ（命題の真偽と、型が付くかどうかは
   別の話である）。
-/

/-! ## 2. def — 項に名前を付ける

    def 名前 : 型 := 項

と書くと項に名前が付き、以後どこでも使える。
-/

def two : Nat := 2

#check two

/-!
    two : Nat

名前を付けた項は、それ自体また項として使える:
-/

def alsoTwo : Nat := two

#check alsoTwo

/-!
    alsoTwo : Nat

項を扱うコマンドをあと2つ紹介する。`#eval` は項を**計算**して値を表示する:
-/

#eval two

/-!
    2

`#print` は、名前に付けられた**定義そのもの**を表示する:
-/

#print two

/-!
    def two : Nat :=
    2

さて、`def` の宣言を受理する前に、Lean は**型検査**を行っている:
`:=` の右に書いた項の型を計算し、コロンの右に書いた型と一致するかを調べる。
一致しなければ受理されない。例えば

    def bad : Nat := true

と書くと、Infoview には次のエラーが表示される:

    error: Type mismatch
      true
    has type
      Bool
    but is expected to have type
      Nat

「`true` の型は `Bool` であり、要求されている型 `Nat` と一致しない」という報告である。
-/

/-! ### ✏ 練習

1. `def five : Nat := 5` を自分で宣言し、`#check five`・`#eval five`・`#print five`
   の表示をそれぞれ予想してから確かめよ。
2. `def oops : Bool := two` は受理されるか。予想してから試し、
   エラーメッセージを本文の例と見比べよ。
-/

/-! ## 3. 関数

まず関数の**型**から。`Nat → Nat` は「`Nat` から `Nat` への関数の型」を表す。
一般に、型 `A` と型 `B` から、新しい型 `A → B`——「`A` から `B` への関数の型」——が
作れる。つまり矢印 `→` は、**2つの型から新しい型を1つ作る操作**を表す記号である。
それ自体が具体的な関数を定めるのではない。集合の言葉でいえば、`A → B` は
写像全体の集合 Map(A, B)（Hom(A, B)、B^A などとも書かれるもの）と同じ役割を持つ。

そして関数そのもの（`A → B` 型の項）は、`fun` という記法で記述される項によって
定義できる: `fun x => e` は「`x` を受け取って `e` を返す関数」である。
-/

def double : Nat → Nat := fun n => n + n

#check double    -- double : Nat → Nat

/-!
本体に出てきた `+`（1節で先取りした）について一言だけ注意しておく。
`+` は **notation（記法）**であり、その意味は **class／instance** という仕組みで
型ごとに決まっている（仕組みは7節で説明する）。ここでは `Nat` に対して
使っており、「2つの `Nat` から `Nat` を作る演算」と思えばよい。

### 適用の書き方

関数を使うには、`double 21` のように**関数と引数を並べて**書く（括弧は不要）。
数学で「f(x)」と書くとき、私たちは f が関数で x がその定義域の元であることを
前提している。Lean の `f x` も同じ約束の記法で、
**`f` が関数型を持ち、`x` がその定義域の型を持つこと**を要求する。

実際 `double 21` と書くと、Lean は2つのことを確かめる:

1. `double` の型は `Nat → Nat`（関数型である）——定義域は `Nat`
2. `21` の型は `Nat`——定義域と一致する

この2点が通るから `double 21` は**合法な書き方**であり、結果の型は
矢印の右側の `Nat` になる。この確認こそが、型検査という機能の中身である。
-/

#eval double 21    -- 42

/-!
`fun` の側の型検査も見ておく。`fun n => n + n` が型 `Nat → Nat` を
持つかを調べるときは、引数を `n : Nat` と**仮に置いて**、
そのもとで本体 `n + n` の型が `Nat` になるかを調べる。
「仮定を置いて中身を検査する」というこの形は、
含意 `p → q` の証明の形として `CH.lean` にそのまま現れる。
-/

/-- 引数を左に書く糖衣構文。上の `double` と同じもの。 -/
def double' (n : Nat) : Nat := n + n

#check double'   -- double' (n : Nat) : Nat

/-!
### 表示の読み方: binder 形式

いま `#check double'` の表示が `double' (n : Nat) : Nat` となったことに注意。
これは「引数の列をコロンの左に並べ、最後に結果の型を書く」**binder 形式**の
表示で、`#check` が関数を表示するときの標準の形である。

    double  : Nat → Nat            （矢印形式）
    double' (n : Nat) : Nat        （binder 形式）

この2つは**同じ型の2通りの表示**である。宣言の書き方も同様に2通りあって
（`def double : Nat → Nat := fun n => …` と `def double' (n : Nat) : Nat := …`）、
どちらで書いても同じものが定義される。以後どちらの表示も出てくるので、
読み替えられるようにしておくこと。
-/

/-! ### 多変数関数はカリー化で表す

Lean の関数はすべて1引数である。2引数の関数は、
「1つ目の引数を受け取ると、**残り1引数の関数を返す**」形（カリー化）で表す。
-/

def plus : Nat → Nat → Nat := fun a => fun b => a + b

#check plus        -- plus : Nat → Nat → Nat
#check plus 3      -- plus 3 : Nat → Nat（1つ渡すと、残り1引数の関数が返る）
#check plus 3 4    -- plus 3 4 : Nat
#eval plus 3 4     -- 7

/-!
ここで矢印の読み方の約束を確認しておく。`→` は**右結合**である:

    Nat → Nat → Nat　は　Nat → (Nat → Nat)　のこと

（「`Nat` を受け取って、関数 `Nat → Nat` を返す」）。逆に、適用は**左結合**:

    plus 3 4　は　(plus 3) 4　のこと

（まず `plus 3` で関数を作り、それに `4` を渡す）。
この2つの約束がかみ合っているおかげで、カリー化された関数を
括弧なしで自然に読み書きできる。

括弧を左側に付けた `(Nat → Nat) → Nat` は**まったく別の型**
（関数を受け取る関数）になることに注意。
-/

def applyTo21 (F : Nat → Nat) : Nat := F 21

#check applyTo21       -- applyTo21 (F : Nat → Nat) : Nat
#eval applyTo21 double -- 42（関数 double そのものを引数として渡している）

/-!
書き方の糖衣もまとめておく。次の3つは**まったく同じ宣言**である:

    def plus : Nat → Nat → Nat := fun a => fun b => a + b
    def plus : Nat → Nat → Nat := fun a b => a + b       -- fun は引数をまとめられる
    def plus (a b : Nat) : Nat := a + b                  -- binder 形式で書く
-/

/-- 3引数以上も同じことの繰り返し。
`Nat → Nat → Nat → Nat` は `Nat → (Nat → (Nat → Nat))` と読む。 -/
def addMul (a b c : Nat) : Nat := a + b * c

#check addMul      -- addMul (a b c : Nat) : Nat（binder 形式の表示）

/-!
### `+` をあらためて: ざっくり版と正確な版

カリー化を知ったいま、`+` にちゃんとした型が与えられる。以後、
裏に仕組みのあるものには**ざっくり**版と**正確には**版を併記する
（正確な版は初読では飛ばしてよい）。

* `+` — **ざっくり**: `Nat → Nat → Nat` という型の2引数関数で、
  `3 + 4` は `plus 3 4` と同じ形の適用を、中置の記法で書いたもの。
  **正確には**: `+` の読み先は汎用の演算 `HAdd.hAdd` で、「どの型の足し算か」は
  登録簿（7節の instance）から決まる。それを `Nat` に特殊化した姿がざっくり版である。
* 数字 `3` — **ざっくり**: そのまま自然数の項。
  **正確には**: 数字も記法であり、期待される型に応じて読み方が決まる
  （仕組みは7節、実例は8節の補足で見る）。何も指定がなければ `Nat` と読まれる。
-/

/-! ### 型は部分項から機械的に計算できる

2節で「型検査が走る」と述べ、この節の冒頭で `double 21` の2点確認を見た。
一般の形をまとめておく。適用についての規則はただ1つである:

    f : A → B　かつ　a : A　ならば　f a : B

この規則は、型の計算式であると同時に、**適用が合法かどうかの検査**でもある。
`f a` と書いてよいのは、`f` の型が矢印型 `A → B` であり、**かつ**引数 `a` の型が
その定義域 `A` と一致するときだけ。この2点を照合して初めて、
適用が合法だと分かり、結果の型 `B` が読み取れる。

例えば `double (plus 3 4)` なら:

1. `3 : Nat`、`4 : Nat`（数リテラル）
2. `plus : Nat → Nat → Nat`（宣言でそう決めた）
3. `plus 3` — 照合: `plus` の型は矢印型 `Nat → (Nat → Nat)` で、定義域は `Nat`。
   引数は `3 : Nat` だから一致する。よってこの適用は**合法**で、
   型は矢印の右側 `Nat → Nat`
4. `plus 3 4` — 照合: `plus 3 : Nat → Nat` の定義域 `Nat` に `4 : Nat` が一致。
   合法で、型は `Nat`
5. `double (plus 3 4)` — 照合: `double : Nat → Nat` の定義域 `Nat` に、
   部分項の型 `plus 3 4 : Nat` が一致。合法で、型は `Nat`

どの段階でも、見ているのは**直下の部分項の型と規則1つだけ**であり、
段階ごとに「一致するか」の照合が1回ずつ入っている。
すべての照合が通ったときにだけ、項の全体に型が付く——つまり
「型が付く」ことと「その項が意味を成す書き方である」ことは同じである。
この局所的な検査を項全体に再帰的に行うのが型検査で、
項がどれだけ大きくなっても手順は変わらない。

1節の `3 + 4 : Nat` も、ざっくり版の `+ : Nat → Nat → Nat` を使えば
同じ手順で確かめられる。そして以後に出てくる `#check` の表示は**すべて**、
「宣言された型」と「この規則」だけで、同じように自分の手で検算できる。
-/

#check double (plus 3 4)   -- 表示: double (plus 3 4) : Nat

/-!
照合が失敗すれば、破れた場所がそのままエラーになる。
`double` に（数ではなく）関数 `plus` を渡してみると:

    #check double plus

    error: Application type mismatch: The argument
      plus
    has type
      Nat → Nat → Nat
    but is expected to have type
      Nat

「引数の型 `Nat → Nat → Nat` が、要求される型 `Nat` と合わない」と、
規則が破れた部分項を名指しで教えてくれる。
-/

/-! ### ✏ 練習

1. `#check` する**前に**型を計算せよ: `(3 + 4) * 2`、`plus (double 3)`、
   `applyTo21 (plus 3)`、`fun n : Nat => plus n n`。それから確かめよ。
2. `#eval applyTo21 (plus 100)` の値を予想してから実行せよ。
3. 型 `Nat → (Nat → Nat) → Nat` を持つ関数を1つ自分で定義し、`#check` で確認せよ
   （`(Nat → Nat) → Nat → Nat` とは**別の型**であることに注意）。
-/

/-! ## 4. 命題と theorem

1節で `Prop`——命題たちの住む宇宙——に触れた。**命題も、`Prop` という型を持つ項**である。
命題を作る記号 `=` や `<` も、`+` と同じく**記法**であり、
意味はクラスの仕組みで型ごとに決まっている（7節）。

* `=` `<` — **ざっくり**: `Nat` の上では、どちらも `Nat → Nat → Prop` という型の
  関数とみなせばよい。`1 + 1 : Nat` と `2 : Nat` を渡すから `1 + 1 = 2 : Prop`。
  **正確には**: `=` はどの型でも使える `Eq : α → α → Prop`（`α` は両辺の型から
  決まる暗黙引数——7節の括弧のまとめで説明する。定義そのものは `CH.lean` の
  8節で見る）、`<` は型ごとに登録簿で意味が決まる演算である。

`2 < 1` のような偽の命題も、命題としては立派な項だった（1節）。
真であるとは「その命題の**証明**がある」ことである。

命題も型だから、2節とまったく同じ構文で「証明という項に名前を付ける」宣言が
書ける。型の位置に命題を、`:=` の右にその証明を書く。このとき `def` の代わりに
`theorem` と書くのが慣例で、意味は `def` と同じである。
-/

theorem one_add_one : 1 + 1 = 2 := rfl

#check one_add_one

/-!
    one_add_one : 1 + 1 = 2

`rfl` は「両辺が定義から計算して一致する」ことを理由にする等式の証明（詳しくは5節）。

ここでも型検査が同じ仕事をしていることに注意。
「項 `rfl` の型は命題 `1 + 1 = 2` と一致するか」という検査が、
そのまま**証明の検査**になっている。この見方が `CH.lean` の主題である。
-/

/-! ### ✏ 練習

1. `#check 3 < 5` と `#check 3 = 5` の表示を予想してから確かめよ。
2. `theorem two_add_three : 2 + 3 = 5 := rfl` を自分で宣言してみよ。
3. `theorem oops : 2 + 2 = 5 := rfl` は受理されるか。予想してから試し、
   エラーメッセージがどの規則の破れを指しているか読み取れ。
-/

/-! ## 5. 帰納型（inductive type）

型を作る部品の1つ目が、帰納型である。帰納型は**構成子（constructor）のリスト**で
型を定義する。構成子とは「その型の項の**作り方**」のことで、
帰納型の項は、構成子で作られたものが**すべて**である。

いちばん単純なのは、構成子がどれも引数を取らない**列挙型**である。
-/

inductive Signal where
  | red
  | yellow
  | green

#check Signal

#check Signal.red   -- Signal.red : Signal

/-!
この宣言の意味は「`Signal` の項は `Signal.red`, `Signal.yellow`, `Signal.green` の
3つが**すべて**であり、それ以外にはない」ということ。構成子の正式な名前は
`型名.構成子名` になる（1節の `Bool.true` はこれだった）。
作り方を列挙したら、それで型が決まる。集合のアナロジーでは、列挙型は
3点集合 {red, yellow, green} のような**有限集合**である。

「それ以外にない」からこそ、場合分け（`match`）が正当化される。
これが帰納型の項の使い方（除去）である。まず省略なしの書き方で:
-/

def next : Signal → Signal
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

#check next

/-!
期待される型が分かっている位置では、`Signal.red` を `.red` と省略できる
（この省略の仕組みは9節のドット記法で説明する）。以後は省略形も使う:
-/

def isRed : Signal → Bool
  | .red => true
  | .yellow => false
  | .green => false

#check isRed

/-!
`Bool` はまさにこの形の列挙型で、標準ライブラリ（Prelude）では
次のように定義されている:

    inductive Bool : Type where
      | false : Bool
      | true : Bool

構成子の個数を減らしていくと、おなじみの集合が現れる。構成子が1つ・引数なしなら
**一点集合**（Prelude の `Unit`。項は `Unit.unit` ただ1つ）。構成子を**1つも**
書かなければ**空集合**に当たる型になる。Prelude の `Empty` がそれである:

    inductive Empty : Type

項の作り方がないのだから、`Empty` の項は存在しない。

同じことは `Type` の世界だけでなく **`Prop` の世界でもできる**。命題の
`True` と `False` は、Prelude で帰納型として定義されている:

    inductive True : Prop where
      | intro : True

    inductive False : Prop

`True` は構成子をちょうど1つ持つ命題——`Prop` の世界では、構成子とは
「その命題の**証明の作り方**」だから、構成子 `True.intro` がそのまま証明である。
`False` は構成子を1つも持たない命題——だから証明がない。
なお、構成子が**複数**ある命題の帰納型の代表は「または」`Or` である
（2通りの証明の作り方を持つ命題。`CH.lean` の3節で扱う）。

まぎらわしいが、`true : Bool` と `True : Prop` は別物なので注意。
`true` は計算で使う**データ**であり、`True` は**命題**である。
この対比は `CH.lean` の4節で扱う。

### 構成子は引数を取れる

構成子に引数を持たせると、データを包む型が作れる。構成子の引数は、
`def` と同じくコロンの左に書ける（3節の binder 形式）:
-/

inductive NatOrBool where
  | nat (n : Nat) : NatOrBool
  | bool (b : Bool) : NatOrBool

#check NatOrBool.nat    -- NatOrBool.nat (n : Nat) : NatOrBool

/-!
矢印形式で書いても、まったく同じ型が定義される:

    inductive NatOrBool where
      | nat : Nat → NatOrBool
      | bool : Bool → NatOrBool

`NatOrBool` の項は「`nat` の札が付いた自然数」か「`bool` の札が付いた真偽値」の
どちらか。集合のアナロジーでは、`NatOrBool` は `Nat` と `Bool` の
**直和（非交和）**と思える。場合分けで札を見分け、中身を取り出す:
-/

def valueOf : NatOrBool → Nat
  | .nat n => n
  | .bool _ => 0    -- `_` は「この場合分けでは中身を使わない」という印

#check valueOf

/-!
### 型をパラメータにする

次の段階として、包む中身の型そのものをパラメータ `(α β : Type)` にできる:
-/

inductive MySum (α β : Type) where
  | inl (a : α) : MySum α β
  | inr (b : β) : MySum α β

#check MySum

#check MySum.inl    -- MySum.inl {α β : Type} (a : α) : MySum α β

/-!
`MySum α β` の項は、「`α` の項に `inl` の札を付けたもの」か
「`β` の項に `inr` の札を付けたもの」のどちらか。集合のアナロジーでは
**直和** α ⊔ β である——`NatOrBool` は `MySum Nat Bool` に相当する
（`CH.lean` に出てくる `⊕` は、標準ライブラリにあるこれと同じ型）。
-/

def fromSum : MySum Nat Bool → Nat
  | .inl n => n
  | .inr _ => 0

#check fromSum

/-!
取り出す側も、パラメータを持たせて一般的に書ける。次の `getLeft` は
「既定値 `d` を受け取り、左の札なら中身を、右の札なら `d` を返す」関数で、
`fromSum` はその `Nat`・`Bool`・`0` への特殊化に当たる
（`{α β : Type}` という波括弧の意味は7節でまとめて説明する。ここでは
「どんな型の組でも使える」という印と読めばよい）:
-/

def getLeft {α β : Type} (d : α) : MySum α β → α
  | .inl a => a
  | .inr _ => d

#check getLeft

#eval getLeft 0 (MySum.inr true)   -- 0

/-!
### 構成子は自分自身の型を引数に取れる（再帰）

構成子の引数に、いま定義している型そのものを使ってよい。
例として、自然数を自分で作ってみる。
-/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat

/-!
`MyNat` の項は、`zero` に `succ` を有限回適用したものがすべて。
列挙型と違って項は無限にあるが、どの項も**有限の手順**で作られている。
だから場合分けに加えて、構造が小さくなる方向への**再帰**が正当化される。

集合のアナロジーでは、`MyNat` は方程式

    X ≅ 1 ⊔ X   （zero の分の1点 ⊔ succ の引数の分）

を満たす**最小**の集合と読める。右辺に自分自身が現れるのが再帰の印で、
最小性は「`zero` に `succ` を有限回重ねたものがすべてで、それ以外にない」
ということの言い替えである。
-/

def add : MyNat → MyNat → MyNat
  | m, .zero   => m
  | m, .succ n => .succ (add m n)   -- 構造が小さくなる方向への再帰

#check add

/-!
次の `example` は**名前を付けない宣言**である。中身は `def`/`theorem` と同じで、
型検査もまったく同じように走るが、名前が付かないのであとから参照できない。
「この項がこの型を持つ」ことをその場で確かめるためだけに使う。
4節で見た `rfl` で、1 + 1 = 2 が計算だけで確かめられる。
-/

example : add (.succ .zero) (.succ .zero) = .succ (.succ .zero) := rfl

/-!
標準ライブラリの型はほとんどすべて帰納型である。
`Bool` `Unit` `Empty`（上で引用した）、`Nat`（リテラル `3` は
`succ (succ (succ zero))` の表示）、`CH.lean` に出てくる `×` `⊕`、
命題側の `And` `Or` `False` `Exists` `Eq` も全部そう。
`Eq` の構成子は `rfl` ただ1つで、4節から使っているのはこれである。

`Top.lean` では、`Nat` の再帰で集合の有限個の共通部分 `interFin` を定義し、
その性質もまた再帰で証明している。**再帰で書いた証明が数学的帰納法**である。
-/

/-! ### ✏ 練習

1. `Signal` の「逆回り」`prev : Signal → Signal` を `match` で定義し、
   `example : prev (next .red) = .red := rfl` が通ることを確かめよ
   （自分の定義が `next` と噛み合っているかを機械が検査してくれる）。
2. `MyNat` の項として 3 を `def myThree : MyNat := …`（`succ` 3回）と書き、
   `example : add myThree .zero = myThree := rfl` を確かめよ。
3. 2点の列挙型 `inductive Two where | a | b` を定義せよ。`Two` と `Bool` は
   集合としては同じ2点集合だが、型としては別物である。往復の関数
   `toBool : Two → Bool` と `ofBool : Bool → Two` を書き、
   `example : toBool (ofBool true) = true := rfl` を確かめよ。
4. 前問の `Nat` 版: `MyNat` と `Nat` も、型としては別物だが「同型」である。
   往復の関数 `toN : MyNat → Nat`（再帰で `+ 1` していく）と
   `ofN : Nat → MyNat`（パターン `| 0` と `| n + 1` の再帰）を書き、
   `example : toN (ofN 3) = 3 := rfl` を確かめよ。
   （**すべての** `n` で往復が恒等になることの証明には数学的帰納法が要る。
   `CH.lean` を読んだあとで戻ってくるとよい。）
-/

/-! ## 6. structure

構成子が**1つだけ**で、その構成子が**複数の引数**を受け取る帰納型は、
「成分をまとめて持ち運ぶ入れ物」としてよく使う。まず、ふつうの帰納型として書いてみる。
-/

inductive MyPoint where
  | mk (x y : Nat) : MyPoint

#check MyPoint

/-!
項の作り方は `MyPoint.mk 1 2` の一通りしかない。だから場合分けは常に1ケースで、
成分を取り出す関数がすぐに書ける。
-/

def MyPoint.x : MyPoint → Nat
  | .mk a _ => a

#check MyPoint.x

/-!
この「構成子1つの帰納型＋成分の取り出し関数」をひとまとめに書く構文が
`structure` である。structure では、構成子の各引数に名前を付けて宣言する。
この名前付きの成分を**フィールド**（field）と呼ぶ。利点は2つ:

* **フィールドに名前を付けられる**（その名前がそのまま取り出し関数になる）
* 構成子 `mk` と取り出し関数が**自動で定義される**（自分で書かなくてよい）
-/

structure Point where
  x : Nat
  y : Nat

#check Point

#check Point.mk    -- Point.mk (x y : Nat) : Point （自動定義された構成子。`⟨1, 2⟩` は略記）
#check Point.x     -- Point.x (self : Point) : Nat （自動定義された取り出し関数。`p.x` とも書ける——9節）

example : (Point.mk 1 2).x = 1 := rfl

/-!
structure は引数（パラメータ）を取ることもできる。
-/

structure Pair (α β : Type) where
  fst : α
  snd : β

#check Pair        -- Pair (α β : Type) : Type
#check Pair.mk     -- Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β
#check Pair.fst    -- Pair.fst {α β : Type} (self : Pair α β) : α

/-!
集合のアナロジーでは、`Point` は直積 Nat × Nat、`Pair α β` は直積 α × β である。
つまり structure は「**直積の各成分に名前を付けたもの**」と思ってよい。
実際、標準ライブラリの `×` 自身が `fst`/`snd` という2フィールドの
structure（名前は `Prod`）として定義されている。

前節の直和とここの直積をまとめると、帰納型の一般形は集合の言葉でこう読める:

    (構成子1の引数たちの直積) ⊔ (構成子2の引数たちの直積) ⊔ …

つまり**構成子の個数が直和の項数を、各構成子の引数が直積の因子を**与える。
`Signal` は 1 ⊔ 1 ⊔ 1（3点集合）、`MySum α β` は α ⊔ β（直和だけ）、
`Point` は Nat × Nat（直和が1項に退化して直積だけ）、
構成子が0個なら空集合（`Empty` や `False`）。
「structure は直積」と「帰納型は直和のようなもの」は矛盾しない——
直和を**使って**直積を定義しているのではなく、構成子の**個数**と**引数**という
直交した2つの軸が、それぞれ直和と直積に対応しているのである。

### フィールドは前のフィールドに依存してよい

もう1つ一般化がある: 後のフィールドの型は、前のフィールドに**依存してよい**。
そして、**フィールドの型は命題でもよい**（帰納型が `Prop` にも住めたことの
structure 版で、「証明を成分として持ち歩く」ことができる）。
標準ライブラリの `Fin` は、この2つを同時に使う実例である:

    structure Fin (n : Nat) where
      val : Nat
      isLt : val < n

`Fin n` の項は、値 `val` と「それが `n` 未満だという**証明** `isLt`」の組で、
第二フィールドの型（命題）が第一フィールドの**値**に依存している。
つまり `Fin n` は「`n` 未満の自然数」を、値と証明の抱き合わせで表した型である。
このように、述語で切り出した「値と証明の組」の型を**部分型**と呼ぶ
（依存する直積としての一般論は `CH.lean` の6節で、部分型の記法は `Top.lean` で扱う）。
項は構成子で `⟨2, 証明⟩` のように作り、`.val` で値を取り出す——8節で実際に使う。

なお structure 自体を `Prop` に住まわせることもできる
（フィールドがすべて命題なら、その「束」も1つの命題——`Top.lean` の
`Function.Bijective` がその例である）。
-/

/-! ### ✏ 練習

1. `structure Circle where center : Point; radius : Nat` のような
   自作の structure を1つ定義し、`#check` で構成子と取り出し関数が
   自動定義されていることを確かめよ。
2. `example : Point.y (Point.mk 1 2) = 2 := rfl` が通ることを確かめよ。
   さらに `(Point.mk 1 2).y` とも書けることを試せ（9節のドット記法の先取り）。
-/

/-! ## 7. class と instance

`class` は structure の変種で、「この型の項は `instance` として登録しておき、
必要になったら Lean が登録簿から探して使う」という使い方を宣言したもの。
-/

class HasZero (α : Type) where
  zero : α

#check HasZero

instance : HasZero Nat where
  zero := 0

/-!
`HasZero α` の項は「`α` のどの項をゼロと呼ぶかの指定」で、
`instance` 宣言によって `Nat` のゼロとして `0` を登録した。

`instance` も `example` と同じく**名前を付けない宣言**である
（中身は `def` と同じで、宣言と同時に登録簿へ載る）。
使う側は登録簿から探すだけで名前で呼ばないから、名前を書く必要がない。
実際には Lean が `instHasZeroNat` のような名前を自動で付けており、
`instance myZero : HasZero Nat where …` と自分で名前を付けることもできる。

登録簿から探す操作そのものを項として書いたのが `inferInstance` である。
型を見ると、インスタンス引数 `[i : α]` を受け取ってそのまま返すだけの関数で、
「探す」仕事は括弧 `[ ]` の仕組みがやっていることが分かる。
-/

#check @inferInstance   -- @inferInstance : {α : Sort u_1} → [i : α] → α

example : HasZero Nat := inferInstance   -- 登録してあるので見つかる

-- 登録していない型では失敗する:
--
--   example : HasZero Bool := inferInstance
--
--   error: failed to synthesize instance of type class
--     HasZero Bool

/-- インスタンス引数の使いどころ: 「ゼロが登録されたどんな型でも」働く関数が書ける。
`zeroPair Nat` と書くだけで、`HasZero Nat` の項は登録簿から自動で渡される。 -/
def zeroPair (α : Type) [HasZero α] : Pair α α := ⟨HasZero.zero, HasZero.zero⟩

#check zeroPair

#eval (zeroPair Nat).fst   -- 0

/-! ### 自作型にもインスタンスを与える

クラスの効き目は、**あとから自分の型を仲間に入れられる**ことにある。
6節で作った `Point` にゼロを登録してみる。
-/

instance : HasZero Point where
  zero := ⟨0, 0⟩

-- 登録した瞬間から、`HasZero` を使う汎用の道具がすべて `Point` でも使えるようになる
#check zeroPair Point   -- 表示: zeroPair Point : Pair Point Point
example : (zeroPair Point).fst = Point.mk 0 0 := rfl

/-! ### インスタンスを受け取る定理

インスタンス引数は `def` だけでなく `theorem` にも書ける。
「ゼロが登録されたどんな型でも成り立つ」一般的な定理が作れる:
-/

theorem zeroPair_fst (α : Type) [HasZero α] : (zeroPair α).fst = HasZero.zero := rfl

#check zeroPair_fst
-- 表示: `zeroPair_fst (α : Type) [HasZero α] : (zeroPair α).fst = HasZero.zero`
-- 読み: 使うときは `α` を指定するだけでよく、`HasZero α` の項は
-- 登録簿から自動で供給される。

-- 登録済みの型なら、どれにでも同じ定理が適用できる
example : (zeroPair Nat).fst = HasZero.zero := zeroPair_fst Nat
example : (zeroPair Point).fst = HasZero.zero := zeroPair_fst Point

/-! ### 記法もクラスで動いている

3節の「正確には」で、「`+` の正体は汎用の演算で、どの型の足し算かは
登録簿から決まる」と述べた。その登録簿が、標準ライブラリのクラス `Add` である:

    class Add (α : Type u) where
      add : α → α → α

`Point` に足し算を登録してみる:
-/

instance : Add Point where
  add p q := ⟨p.x + q.x, p.y + q.y⟩

#check Point.mk 1 2 + Point.mk 3 4
-- 表示: `{ x := 1, y := 2 } + { x := 3, y := 4 } : Point`
-- 登録した瞬間から、記法 `+` が `Point` でも通るようになった

example : Point.mk 1 2 + Point.mk 3 4 = Point.mk 4 6 := rfl

/-!
正確に言うと、`+` の読み先は `HAdd`（左右の型が違ってもよい、さらに一般の版）
なのだが、「`Add α` があれば `HAdd α α α` にもなる」という**橋渡しの
インスタンス**が標準ライブラリに用意されているので、`Add` を登録するだけで
記法まで使えるようになる。登録簿の検索は、このように**連鎖**する。

数字のリテラルにも同じ仕組みがあり、そちらは `OfNat` というクラスが担っている
（8節の補足で、`(2 : Fin 3)` のようなリテラルが通る理由として再登場する）。

なお、この教材の `HasZero` は練習用の自作クラスで、記法とは独立している
（登録しても `0` と書けるようにはならない）。mathlib にはよく似た `Zero` という
クラスがあり、そちらは `OfNat` への橋渡しを備えているので、
登録すると `0` と書けるようになる。

### 型の読み方と3種類の括弧

インスタンス引数まで出そろったので、`#check` が表示する型の読み方を
あらためてまとめておく。例えば

    Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β

は、コロンの左に引数の列が並び、最後の `: Pair α β` が結果の型、と読む
（3節で見た binder 形式である）。引数を1つ渡すたびに列の左から1つ消えていき、
全部渡すと結果の型の項が得られる。そして各段階で「渡した項の型が、引数の型と
一致するか」の型検査が走っている。2節からやってきたことの一般形である。

引数を包む括弧には3種類あり、「その引数を**誰が埋めるか**」を表している。

* `(fst : α)` — **明示引数**。使う側が自分で書く。
* `{α : Type}` — **暗黙引数**。使う側は書かない。型検査が、他の引数との
  つじつま合わせ（単一化）で埋める。`Pair.mk 1 true` と書けば
  `1 : Nat` と `true : Bool` から `α := Nat`、`β := Bool` が決まる。
* `[inst : C α]` — **インスタンス引数**。これも使う側は書かないが、埋め方が違う。
  型検査からは決まらず、`instance` として**登録された項**の中から Lean が探して埋める。
  この節の `zeroPair` の `[HasZero α]` がこれだった。
-/

#check Pair.mk 1 true   -- { fst := 1, snd := true } : Pair Nat Bool （暗黙引数が埋まった）

/-! ### ✏ 練習

1. 本文で `HasZero Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : HasZero Bool where zero := false` を登録し、
   `example : HasZero Bool := inferInstance` と `#check zeroPair Bool` が
   通るようになることを確かめよ。
-/

/-! ## 8. 依存関数型

関数の一般化がもう1段ある。**行き先の型が、入力に応じて変わってよい**とした
関数——依存関数——である。いちばん簡単な例は「型そのものを最初の引数として
受け取る」形で作れる。1節で見たとおり型も項なので、引数にできるのである。
-/

/-- どんな型の上でも使える恒等写像。第1引数として**型**を受け取り、
第2引数と結果の型が、その第1引数で決まる。 -/
def idAt (α : Type) (a : α) : α := a

#check idAt         -- 表示: idAt (α : Type) (a : α) : α
#check idAt Nat     -- 表示: idAt Nat : Nat → Nat
#check idAt Bool    -- 表示: idAt Bool : Bool → Bool
#eval idAt Nat 42   -- 42

/-!
`idAt Nat` と `idAt Bool` は**型が違う**。つまり `idAt` に1つ引数を渡すと、
「残りの型」がその引数の値で決まる。こうなるともう `A → B` の形では書けない。
この形の関数の型を**依存関数型**といい、

    idAt : (α : Type) → α → α

と書く（束縛した名前 `α` が矢印の右側に現れるのが目印）。これが Lean の
関数型の一般形で、`A → B` は「行き先が入力に依存しない特別な場合」の略記である。

なお、この「型を渡してから使う」仕組みこそ多相性の正体で、7節で説明した
暗黙引数 `{α : Type}` は、この第1引数を文脈から自動で埋めてもらう書き方である。

依存関数がさらに面白くなるのは、**型を返す関数**（型の族）と組み合わせたとき。
6節で中身（値と証明の組）を見た `Fin` は、「`n` 未満の自然数の型」を返す関数
という、もう1つの顔を持っている。
-/

#check Fin        -- Fin (n : Nat) : Type  （つまり Fin : Nat → Type）
#check Fin 3      -- Fin 3 : Type

/-!
族に沿って「番号 `n` を受け取り、型 `Fin (n + 1)` の項を返す」関数が書ける。
一般形 `(a : α) → P a` の `P` が定数でない、本格的な依存の例である。
`last 2` と `last 9` は**型が違う**ことに注意。
-/

def last : (n : Nat) → Fin (n + 1) := fun n => ⟨n, Nat.lt_succ_self n⟩

#check last
-- `⟨…⟩` は構成子に引数を渡す記法（6節）。`Fin` の項は「値」と「値 < n の証明」の組だった。

#check last 2     -- last 2 : Fin (2 + 1)
#check last 9     -- last 9 : Fin (9 + 1)

/-!
集合のアナロジーでは、依存関数型 `(a : α) → P a` は集合族 {P a} の
**直積** ∏ₐ P a に当たる。その項は「各 a に P a の要素を1つずつ選ぶ、選び方」
だからである。`α → β` ＝ B^A（すべての因子が同じ直積、すなわち冪）の、
因子が点ごとに変わってよい一般化になっている。
対になる**族の直和** ∐ₐ P a——「どの a か」の札付きで各 P a の要素を集めたもの——に
当たるのが、6節の部分型を一般化した**依存和** `(a : α) × P a` で、
`Pair`（直積）と `MySum`（直和）の共通の一般化である。`CH.lean` の6節で主役になる。
-/

/-! ### 補足: では `2 : Fin 3` なのか？

「`Fin 3` は 3 未満の自然数の型」と聞くと、集合 {0, 1, 2} ⊂ ℕ を思い浮かべて、
「自然数 `2` はそのまま `Fin 3` の項でもあるのか」と考えたくなる。そうではない。
1節で見たとおり**項はちょうど1つの型を持ち**、型どうしは集合のように重ならない
——集合のアナロジーの限界がここにある。`Fin 3` は `Nat` の部分集合ではなく、
「値と、それが 3 未満だという証明の組」からなる**別の型**である。

まぎらわしいことに、`(2 : Fin 3)` という書き方自体は通ってしまう:
-/

#check (2 : Nat)     -- 表示: 2 : Nat
#check (2 : Fin 3)   -- 表示: 2 : Fin 3

/-!
これは数字 `2` が**記法**であり、期待される型に応じて別々の項に読まれるからである
（`Fin` 用の読み方が instance として登録されている——7節で見た仕組みである）。
`(2 : Nat)` は自然数の項、`(2 : Fin 3)` は組 `⟨2, 証明⟩` の略記で、
**同じ字面の、別の項**なのである。所属判定をしているのではない証拠に、
`(5 : Fin 3)` すら通り、3 で割った**余り**として読まれる:
-/

#eval (5 : Fin 3)    -- 2 になる（リテラルの読みは登録された読み方次第）

-- 確認: `(2 : Fin 3)` の第一成分（値）を `.val` で取り出すと自然数の `2` に戻る
example : (2 : Fin 3).val = 2 := rfl

/-!
2つの `2` を等号で結ぼうとすると、面白いことが起きる:
-/

#check (2 : Nat) = (2 : Fin 3)   -- 表示: 2 = ↑2 : Prop

/-!
型エラーにはならないが、右辺に `↑` が付いた。これは**強制**（coercion）の印で、
Lean が `Fin 3 → Nat` の写像（`.val`）を自動で挟み、
「`Nat` の世界に持ち上げてから比べる」形に読み替えている。
逆向きはそうはいかない。`Fin 3` を期待する場所に `(2 : Nat)` を渡すと:

    error: Application type mismatch: The argument
      2
    has type
      Nat
    but is expected to have type
      Fin 3

`Nat → Fin 3` の向きには「3 未満」という証明が要るので、自動では埋められない。
まとめると、`Fin 3` と `Nat` の関係は「部分集合と全体」ではなく、
**写像 `.val` で結ばれた別々の型**である。
-/

/-!
型を返す関数が書けるのと同様に、**命題を返す関数**も書ける。
数学でいう述語である。
-/

def IsZero : Nat → Prop := fun n => n = 0

#check IsZero

#check IsZero 3   -- IsZero 3 : Prop（`n` ごとに1つの命題が決まる）

/-- そして「すべての `n` について…」の証明は、依存関数そのものになる:
各 `n` を受け取って、命題 `IsZero (n * 0)` の証明を返す関数である。
実際、`∀ n, Q n` は依存関数型 `(n : Nat) → Q n` の別記法にすぎない
（`CH.lean` の5節）。 -/
theorem all_mul_zero : ∀ n : Nat, IsZero (n * 0) := fun _ => rfl

#check all_mul_zero

/-!
`Top.lean` に出てくる「集合の族」 `U : I → Set X` や「型の族」 `P : α → Type` も、
すべてこの「型（や集合、命題）を返す関数」の例である。
-/

/-! ### ✏ 練習

1. `#check idAt (Nat → Nat)` の型を予想してから確かめよ（矢印の結合に注意）。
   `#eval idAt (Nat → Nat) double 21` はどうなるか。
2. `#check last 4` と `#check (last 4).val` の型を予想してから確かめよ
   （後者の表示に付く `↑` は、補足で見た強制の印である）。
3. `example : IsZero (0 * 5) := rfl` が通ることを確かめよ。
   `IsZero (5 * 0)` は `rfl` でも `all_mul_zero 5` でも証明できるか試せ。
-/

/-! ## 9. 宣言を支える小物 — variable・namespace・記法

最後に、`CH.lean` と `Top.lean` の見た目を決めている構文を紹介する。
（証明を書くもう1つの流儀「タクティク」は `CH.lean` の最後で扱う。）

### variable — 共通の引数の前置き

同じ引数を宣言のたびに書くかわりに、`variable` でまとめて前置きしておける。
以後の宣言は、その変数を**実際に使ったときだけ**引数として受け取る。
-/

section
variable {α : Type} (x y : α)

def toPair : Pair α α := ⟨x, y⟩

#check toPair    -- toPair {α : Type} (x y : α) : Pair α α（variable が引数に取り込まれた）

end

/-!
`section … end` は、`variable` の効き目をそこまでで区切るための囲いである。
なお `universe u` も同様の前置きで、宇宙の段の名前（1節）を宣言する。
`CH.lean` の冒頭はこの2つから始まっている。

### namespace — 名前の接頭辞

`namespace N … end N` で囲うと、中の宣言の本名に `N.` が付く。
-/

namespace Geometry

def origin : Point := ⟨0, 0⟩

#check origin

end Geometry

#check Geometry.origin    -- Geometry.origin : Point（外からはフルネームで呼ぶ）

/-!
### ドット記法

名前空間の仕組みの上に、便利な省略記法が載っている。向きの違う2つの用法が
あるので、まとめて押さえておく。

**値の後ろに付けるドット**: `p : Point` に対して `p.x` と書くと、Lean は
「`p` の型の名前 `Point` の名前空間から `x` を探し、`p` を最初の `Point` 型の
引数として渡す」と解釈する。つまり `p.x` は `Point.x p` の略記。
自動生成されるフィールドに限らず、`Point.〜` という名前の関数なら何でも使える。
-/

/-- ドット記法の実演用: 成分を入れ替える関数。名前を `Point.swap` にしたので
`p.swap` と呼べるようになる。 -/
def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

-- 確認: 後ろに付けるドットは、名前空間の関数の適用の略記にすぎない
example (p : Point) : p.swap = Point.swap p := rfl
example : (Point.mk 1 2).swap = Point.mk 2 1 := rfl

-- フィールドは番号でも取れる: `.1` `.2` は第1・第2フィールドの略記
example : (Point.mk 1 2).1 = 1 := rfl
example (q : Pair Nat Bool) : q.2 = q.snd := rfl

/-!
**型が分かっている場所で前に付けるドット**: 期待される型が `Point` だと
分かっている位置では、構成子 `Point.mk` を `.mk` と省略できる。
今度は「**期待される型**の名前空間から探す」という解決である。
5節のパターンマッチで使った `.red` や `.succ` もこの用法で、
`match` の各ケースは `Signal.red` などの略記だった。
-/

example : Point := .mk 1 2

/-!
`Top.lean` では `Set` の関数（`Set.ext` など）がこの形で、`s.ext` のように使われる。

### syntax と macro_rules — 記法の自作

`Top.lean` は `⋃₀ S` や `{a | p a}` といった数学記法を自作している。仕組みは:

* `syntax` — 「この書き方を受け付けよ」と構文を追加する
* `macro_rules` — 「その書き方はこの項の略記である」と展開を与える

試しに、6節の `Pair` のための記法を作ってみる。
-/

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

#check ⟪1, true⟫    -- { fst := 1, snd := true } : Pair Nat Bool

/-!
記法は項に展開されてから型検査されるので、検査の対象はあくまで項のままである。
単純な中置・前置の記法には `infixl` や `prefix` という略記もある（`Top.lean` で使用）。

これで `CH.lean` と `Top.lean` を読む準備は足りる。

なお正確には、Lean の核には依存関数型と帰納型のほかに商型（`Quot`）などもあるが、
この教材では使わない。
-/

/-! ### ✏ 練習

1. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
2. `example : (Point.mk 1 2).swap.swap = Point.mk 1 2 := rfl` が通ることを確かめよ
   （`.swap` を2回、後ろに付けている）。
3. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。
-/
