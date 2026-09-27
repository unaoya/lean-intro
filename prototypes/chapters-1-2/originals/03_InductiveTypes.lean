import «01_TypesAndTerms»

/-!
# 型と項 II — 帰納型と構造

`02_Forall.lean` では、関数を作り適用することで、ならば・全称の証明を読んだ。
この章では、項を作る道具を増やす。構成子で項を作り、場合分けや射影で使う仕組みを学ぶ。
次の `04_Exists.lean` では、それが「かつ」「または」「存在する」などの証明に対応する。

依存関数型と暗黙引数は既習である。構成子や取り出し関数も、その型を追って読もう。
-/

/-!
## 1. 帰納型（inductive type） {#sec-Intro1.inductive-types}

型を作る部品の2つ目が、帰納型である。帰納型は**構成子（constructor）のリスト**で
型を定義する。構成子とは「その型の項の**作り方**」のことで、
集合のアナロジーで先に言っておくと、帰納型は**集合の直和や集合の直積**にあたるものを
一挙に作れる部品である（節の中で順に見る）。

宣言には `inductive` を使う。`def` が既存の項を使って定義を導入するのに対し、
`inductive` は、**新しい型と、その型の項を作る構成子をまとめて導入する**宣言である。
型も項なので、これも項を導入する宣言の仲間だが、`def` の単なる別表記ではない。

いちばん単純なのは、構成子がどれも引数を取らない**列挙型**である。
集合の言葉では、要素を列挙して**有限集合を作る**ことにあたる。
-/

inductive Signal : Type where
  | red : Signal
  | yellow : Signal
  | green : Signal

#check Signal

/-!
    Signal : Type

では、構成子 `Signal.red` の型は何か。「`Signal` の項の作り方」なのだから、
作られるものの型 `Signal` のはずである:
-/

#check Signal.red

/-!
    Signal.red : Signal
-/

/-!
この宣言は、次の2つを保証する:

* `Signal` のどの項も、`Signal.red`・`Signal.yellow`・`Signal.green` のいずれかに等しい。
  つまり、この3つで**すべて**である。
* 異なる構成子で作った項は等しくない。例えば `Signal.red ≠ Signal.green` が、
  Lean の中で**証明できる**（証明の書き方は `04_Exists.lean` で扱う）。

どちらも名前についての約束ではなく、Lean の中で証明できる事実である。
両方がそろって、集合のアナロジーでは本当に3点集合 {red, yellow, green} になる。
構成子の正式な名前は `型名.構成子名` になる。
[`01_TypesAndTerms.lean` 1節](#sec-Intro1.terms-types)の `Bool.true` はこれだった。
-/

/-!
### `Bool` の定義を見に行く

`Bool` もこの形の列挙型である。今度は、標準ライブラリの定義を実際に見てみよう。
次の `#check Bool` の `Bool` にカーソルを置き、VS Code で右クリックして
**「定義へ移動」（Go to Definition）**を選ぶ。F12 でも同じ操作ができる。
このように、名前からその定義を参照できる。
-/

#check Bool

/-!
    Bool : Type

開かれる `Init/Prelude.lean` では、コメントを除くと次のように定義されている:

    inductive Bool : Type where
      | false : Bool
      | true : Bool

型 `Bool` と、構成子 `Bool.false`・`Bool.true` が一緒に導入されている。
その直後にある `export Bool (false true)` は、接頭辞なしの名前も用意する宣言である。
その意味と、ドットによる省略との違いを、次の補足で整理する。
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: `true` と `.true`、`red` と `.red`

`Bool.true` も `Signal.red` と同じく、帰納型の定義で付けられた構成子の名前である。
では、[`01_TypesAndTerms.lean` 1節](#sec-Intro1.terms-types)で `Bool.true` を単に `true` と書けたのはなぜか。
いま参照した標準ライブラリでは、`Bool` の定義に続けて次の宣言をしている:

    export Bool (false true)

これは `Bool.false` と `Bool.true` を、接頭辞なしの `false`・`true` という名前でも
使えるようにする宣言である。そのため `#check true` だけで型を調べられる。
`inductive` で定義しただけで、すべての構成子の接頭辞を省けるわけではない。

一方、`.red` は**期待される型を手がかりに、名前の接頭辞を補う**記法である
（[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)で見た、期待される型を上から伝える仕組みの1例）。
いまの `Signal` の定義だけをした状態では、次の違いがある:

| 書き方 | 結果と理由 |
|---|---|
| `#check Signal.red` | 通る。構成子の名前を接頭辞まで書いている。 |
| `#check red` | 通らない。接頭辞なしの名前 `red` は用意されていない。 |
| `#check (red : Signal)` | 通らない。型を書くだけでは、名前 `red` の接頭辞は補われない。 |
| `#check (.red : Signal)` | 通る。期待される型 `Signal` から `Signal.red` と分かる。 |
| `#check .red` | 通らない。接頭辞を補う手がかりとなる型が分からない。 |

`Bool` でも `#check (.true : Bool)` は通るが、`#check .true` だけでは
期待される型が分からず通らない。つまり `true` と `.true` は同じ項を指せても、
**短い名前を用意しておく仕組み**と、**期待される型から名前を補う仕組み**という違いがある。

`Signal` でも `export Signal (red)` と宣言すれば、その後は `red` という短い名前を
使える。また、`open Signal in` をコマンドの前に置くと、そのコマンドの中で
接頭辞なしの名前を使える:

    open Signal in
    #check red

こうした名前の管理の仕組みは、[`05_MathematicalTools.lean` 4節](#sec-Intro2.namespaces)で扱う。
このあと本文で使う `.red`・`.yellow`・`.green` は、`open` や `export` を
必要とせず、期待される型から名前を補う書き方である。

この違いは、これから見る `match` の場合分けでも大事になる。接頭辞なしの名前を
用意していない状態で `| red => ...` と書くと、`red` は構成子ではなく、
どの値でも受け取る**新しい変数の名前**になる。赤の場合を指定するには、
`| Signal.red => ...` または `| .red => ...` と書く。
-/


/-!
CALLOUT_END
-/

/-!
### 先取り（04_Exists）: 「全部」と「別々」を支える道具

先ほどの2つの事実を証明するための道具は、`inductive` の宣言に伴って
Lean が用意する。
`Signal.rec` は、3つの場合を扱えば `Signal` のすべての項について定義・証明できることを表す。
また `Signal.noConfusion` を使えば、異なる構成子で作った項が等しくないことを証明できる。
個々の主張の証明がすべて完成形で自動生成される、という意味ではなく、
**証明を組み立てるための道具が用意される**のである。
詳しい型や使い方は、[`04_Exists.lean` 6節](#sec-CH.nat-proofs)で見る。
-/

/-!
### 02_Forall との接続: 仮定として使う・結論として示す

命題を型と見ると、「作る・使う」という区別は「その命題の証明を仮定として使う」ことと、
「その命題を結論として、その証明を作る」ことに対応する。
この見方は [`04_Exists.lean` 7節](#sec-CH.introduction-elimination)で改めて説明する。
-/

/-!
### 項の作り方と使い方

関数型では、`fun` で項を**作り**、引数を渡す**適用**で項を使った。
帰納型でも、この二つの役割を対にして見よう。

型を読むときには、その型の項の**作り方**と**使い方**を対にして考えよう。
型を `T` とすると:

* **作る側**では、`T` の項を与える。例えば `Signal.red` は `Signal` の項を作る。
  関数なら、`A → T` のように**行き先が `T`** であり、必要な材料から `T` の項を作る。
* **使う側**では、`T` の項を受け取って別の項を作る。
  関数の型は `T → B` のように**定義域が `T`** になる。

帰納型の項を**構成子に応じて場合分けして使う**記法が **`match`** である。
構成子ごとに、それを受け取ったときに返す項を書く。
`Signal` なら、3つの構成子それぞれに対応して、返す項を1つずつ書けばよい。
集合の言葉では、3点集合からの写像を、各点の行き先を指定して定めるのと同じである。
-/

/-!
まず `match` だけを使ってみよう。`match 対象 with` のあとに、構成子ごとに
`| 構成子 => 返す項` を並べる。全体は1つの項で、対象の構成子に対応する
場合の項が値になる:
-/

#eval match Signal.red with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

/-!
    Signal.green

対象が `Signal.red` なので、1つ目の場合が選ばれて `Signal.green` になった。
-/

/-!
### ✏ 練習

1. 上の `match` の対象を `Signal.yellow` に変えた項と、`Signal.green` に変えた項を
   書き、それぞれの値を予想してから `#eval` で確かめよ。
-/

/-!
関数記法 `fun` と `match` を組み合わせて、次の信号を返す関数を書こう。
`fun` で受け取った `s : Signal` を、`match s with` で場合分けする:
-/

def Signal.next : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

#check Signal.next

/-!
    Signal.next : Signal → Signal
-/

/-!
定義した関数を試したい。まず `Signal.next Signal.red` という項を読む:
2点確認より型は `Signal`、値は定義の1行目（`Signal.red => Signal.green`）から
`Signal.green` になるはずである。

計算結果は `#eval` で確かめられる。いま作ったばかりの型の値も、
構成子の形で表示される:
-/

#eval Signal.next Signal.red

/-!
    Signal.green

たしかに赤の次は青になった。

ここで、**型を手がかりに名前の接頭辞を補うドット記法**を紹介する。
期待される型が `Signal` と分かっている位置では、`Signal.red` を `.red` と省略できる。
例えば `(.red : Signal)` なら、型注釈から接頭辞 `Signal` が補われる。
`.yellow`・`.green` も同じである。次の `match` では、場合分けする項の型から
構成子の接頭辞が分かる。先ほどの関数を、この省略形で書き直そう。
-/

def nextShort : Signal → Signal := fun s =>
  match s with
  | .red => .green
  | .green => .yellow
  | .yellow => .red

/-!
これは先ほどの `Signal.next` と同じ場合分けである。対象が `Signal` 型なので、
枝の `.red` などは `Signal.red` などと読まれる。返す型も `Signal` なので、
右辺でも同じ省略形を使える。
-/




/-!
### ✏ 練習

1. `Signal.red`・`Signal.yellow`・`Signal.green` をそれぞれ `0`・`1`・`2` に
   送る `signalCode : Signal → Nat` を `match` で書け。それぞれの場合に返す項が
   同じ型になることを確かめ、`#eval signalCode Signal.yellow` の値を予想してから実行せよ。
-/

def isRed : Signal → Bool := fun s =>
  match s with
  | .red => true
  | .yellow => false
  | .green => false

#check isRed

/-!
    isRed : Signal → Bool

パターンの `.red` が `Signal.red` の略と分かるのは、`isRed` の型から
「`match` している `s` は `Signal` 型のはず」と決まっているからである。
-/

/-!
### ✏ 練習

1. `Signal` の「逆回り」`prev : Signal → Signal` を `match` で定義し、
   `#eval prev (Signal.next Signal.red)` の表示を予想してから確かめよ
   （`Signal.red` に戻ってくるはずである）。
2. `isRed` にならって `isGreen : Signal → Bool` を書き、
   `#eval isGreen Signal.red` の値を予想してから確かめよ。
3. `def stopSignal : Signal := .red` を宣言し、`#check stopSignal` と
   `#eval stopSignal` の表示を予想してから確かめよ。
   `.red` の接頭辞がどこから分かるかを説明せよ。
-/

/-!
構成子の個数を減らしていくと、おなじみの集合が現れる。構成子が1つ・引数なしなら
**一点集合**（Prelude の `Unit`。項は `Unit.unit` ただ1つ）。構成子を**1つも**
書かなければ**空集合**に当たる型になる。Prelude の `Empty` がそれである:

    inductive Empty : Type

項の作り方がないのだから、`Empty` の項は存在しない。
（それでも `Empty` **から**の関数は書ける——場合分けすべき場合が1つもないので、
何も書かずに関数が完成する。空集合からの写像がただ1つあることに当たる。
[`04_Exists.lean` 4節](#sec-CH.empty-types)の `elimEmpty` で実物を見る。）

実は同じことが `Prop` の世界でもできて、命題の `True` と `False` は
帰納型として定義されている。命題の世界の帰納型の話は、このファイルでは
扱わず [`04_Exists.lean` 4節](#sec-CH.empty-types)でまとめて見る。

### 構成子は引数を取れる

構成子に引数を持たせることもできる。構成子の引数は、
`def` と同じくコロンの左に書ける（[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の binder 形式）:
-/

inductive NatOrBool : Type where
  | nat (n : Nat) : NatOrBool
  | bool (b : Bool) : NatOrBool

#check NatOrBool

/-!
    NatOrBool : Type
-/

/-!
構成子 `nat` の型を推測しよう。`Nat` の項を1つ受け取って `NatOrBool` の項を
作るのだから、`Nat → NatOrBool`——binder 表示なら `(n : Nat)` が左に出る——のはず:
-/

#check NatOrBool.nat

/-!
    NatOrBool.nat (n : Nat) : NatOrBool
-/

/-!
矢印形式で書いても、まったく同じ型が定義される:

    inductive NatOrBool : Type where
      | nat : Nat → NatOrBool
      | bool : Bool → NatOrBool

`NatOrBool` の項は「`nat` の札が付いた自然数」か「`bool` の札が付いた真偽値」の
どちらか。集合のアナロジーでは、`NatOrBool` は `Nat` と `Bool` の
**直和（非交和）**と思える。

帰納型の仕組みから、構成子の性質を証明できる。
例えば、異なる構成子で作った `NatOrBool.nat n` と `NatOrBool.bool b` は
等しくないことが証明できる。

各構成子が**単射であることも証明できる**。`NatOrBool.nat n = NatOrBool.nat m` ならば
`n = m`、同様に `NatOrBool.bool b = NatOrBool.bool c` ならば `b = c` である。
この単射性を表す補題 `NatOrBool.nat.inj` と `NatOrBool.bool.inj` は、
帰納型の宣言に伴って Lean が自動生成する。型と証明の本体を表示してみよう。
-/

#check NatOrBool.nat.inj

/-!
    NatOrBool.nat.inj {n n✝ : Nat} : NatOrBool.nat n = NatOrBool.nat n✝ → n = n✝
-/

#print NatOrBool.nat.inj

/-!
    theorem NatOrBool.nat.inj : ∀ {n n_1 : Nat}, NatOrBool.nat n = NatOrBool.nat n_1 → n = n_1 :=
    fun {n n_1} x => NatOrBool.nat.noConfusion x fun n_eq => n_eq

単射性が仮定として追加されたのではなく、証明の項を持つ補題が作られている。
`noConfusion` の仕組みは[`04_Exists.lean` 6節](#sec-CH.nat-proofs)の補足で見る。
-/

#check NatOrBool.bool.inj

/-!
    NatOrBool.bool.inj {b b✝ : Bool} : NatOrBool.bool b = NatOrBool.bool b✝ → b = b✝
-/

#print NatOrBool.bool.inj

/-!
    theorem NatOrBool.bool.inj : ∀ {b b_1 : Bool}, NatOrBool.bool b = NatOrBool.bool b_1 → b = b_1 :=
    fun {b b_1} x => NatOrBool.bool.noConfusion x fun b_eq => b_eq
-/

/-!
今度は `NatOrBool` の項を使う側である。ここで集合の**直和の普遍性**を思い出そう。
直和からある集合への写像は、各成分からその集合への写像を1本ずつ与えると定まる。
列挙型で各点の行き先を指定したのも、1点集合の直和と思えば同じ形である。

`match` の書き方も、列挙型から1段拡張される。
構成子に引数がある場合は、場合分けの左側で中身に名前を付け、右側でそれを使える。
次の `NatOrBool → Nat` 型の関数は、自然数の側では中身をそのまま返し、
真偽値の側では常に `0` を返す。`.nat n` の `n` は、取り出した `Nat` 型の中身である:
-/

def valueOf : NatOrBool → Nat := fun x =>
  match x with
  | .nat n => n
  | .bool _ => 0

#check valueOf

/-!
    valueOf : NatOrBool → Nat

2つ目の場合の左側に書いた `_` は、「この場合分けでは中身を**使わない**ので
名前を付けない」という印である（名前を付けてもよいが、使わない変数に
名前を付けると Lean が警告を出す）。
-/

/-!
### ✏ 練習

1. 中身の値には触れず、`.nat` の札なら `true`、`.bool` の札なら `false` を
   返す `tagOf : NatOrBool → Bool` を書け。不要な中身には `_` を使える。
   `#eval tagOf (NatOrBool.nat 3)` の値を予想してから確かめよ。

2. `#eval valueOf (NatOrBool.bool true)` の値を予想してから確かめよ
   （どちらの場合に当たるか）。
3. 「`bool` の札なら中身を、`nat` の札なら `false` を返す」関数
   `flagOf : NatOrBool → Bool` を書き、`#eval flagOf (NatOrBool.bool true)` で
   確かめよ。
-/

/-!
### 構成子の引数を複数にする

構成子は、引数を2つ以上受け取ってもよい。書き方は関数の binder 形式と同じで、
同じ型なら `(a b : Nat)`、異なる型なら `(n : Nat) (flag : Bool)` のように並べる。
`match` で使うときも、例えば `.mk a b` と、取り出す中身の名前を順に並べる。
まず構成子が1つの場合から練習しよう。
-/

/-!
### ✏ 練習

1. 自然数の組 `(a, b)` を表す型 `NatPair : Type` を `inductive` で定義せよ。
   構成子は `mk` の1つとし、自然数を2つ受け取るものとする。
   `#check NatPair.mk` と `#check NatPair.mk 3 5` の表示を予想して確かめよ。
2. 第1成分を返す写像 `firstNat : NatPair → Nat` と、第2成分を返す写像
   `secondNat : NatPair → Nat` を、それぞれ `match` で書け。
   両関数の型を `#check` し、`#eval firstNat (NatPair.mk 3 5)` と
   `#eval secondNat (NatPair.mk 3 5)` の値を予想して確かめよ。

3. 自然数 `n` と真偽値 `flag` の組を表す型 `FlaggedNat : Type` を
   `inductive` で定義せよ。構成子は `mk` の1つとする。
   `#check FlaggedNat.mk` と `#check FlaggedNat.mk 3 true` の表示を予想して確かめよ。
4. 自然数の成分を返す `numberOf : FlaggedNat → Nat` と、真偽値の成分を返す
   `flagOfPair : FlaggedNat → Bool` を `match` で書け。
   両関数の型を `#check` し、`FlaggedNat.mk 3 true` に適用した値を予想して
   `#eval` で確かめよ。
-/

/-!
さらに、構成子を複数にして、それぞれに異なる個数・型の引数を持たせることもできる。
-/

/-!
### ✏ 練習

1. 次の3種類のデータを表す型 `MixedData : Type` を `inductive` で定義せよ。
   構成子 `pair` は自然数を2つ、`flagged` は自然数と真偽値を受け取り、
   `empty` は引数を受け取らないものとする。
   3つの構成子の型を予想して `#check` で確かめよ。
2. 写像 `readNumber : MixedData → Nat` を、`pair a b` は `a + b` に、
   `flagged n flag` は `n` に、`empty` は `0` に送るものとして定める。
   これを `match` で書き、型を `#check` せよ。さらに `MixedData.pair 3 5`、
   `MixedData.flagged 3 true`、`MixedData.empty` に適用した値を予想して `#eval` で確かめよ。
-/

/-!
### 型をパラメータにする

次の段階として、包む中身の型そのものをパラメータ `(α β : Type)` にできる:
-/

inductive MySum (α β : Type) : Type where
  | inl (a : α) : MySum α β
  | inr (b : β) : MySum α β

#check MySum

/-!
    MySum (α β : Type) : Type

binder 形式を読み替えれば `MySum : Type → Type → Type`——[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の `Map` と
同じ形の「型を受け取って型を返す関数」でもある
（ギリシャ文字は `\a` `\b` で打てる。VS Code の Lean 拡張では、
入力済みの記号にマウスを重ねると、ホバー表示で入力方法を確認できる）。

構成子 `inl` の型はどうなるか。`NatOrBool.nat` からの類推では
`α → MySum α β` だが、今度は `α`・`β` 自身も決まらないと使えないはずである:
-/

#check MySum.inl

/-!
    MySum.inl {α β : Type} (a : α) : MySum α β

推測した引数 `(a : α)` に加えて、パラメータの分の引数 `{α β : Type}` が
先頭に付いた。これは [`01_TypesAndTerms.lean` の4節](#sec-Intro1.dependent-functions)で見た暗黙引数である。

* `(a : α)` は**明示引数**で、関数を使うときに自分で書く。
* `{α β : Type}` は**暗黙引数**で、通常は省略する。
  Lean が、ほかの引数の型や、結果に期待される型を手がかりに補う。

例えば、`MySum.inl 3` の結果に `MySum Nat Bool` という型を注釈しよう。
構成子の結果の型 `MySum α β` と、この期待される型を照合すると、
`α := Nat`・`β := Bool` と決まる。そして、明示引数 `3` が `α`、つまり `Nat` の項であることも確かめられる。
したがって、全体は `MySum Nat Bool` の項になるはずである:
-/

#check (MySum.inl 3 : MySum Nat Bool)

/-!
    MySum.inl 3 : MySum Nat Bool

右の構成子でも同じように、結果の型から `α := Nat`・`β := Bool` が決まり、
渡した `true` は `β = Bool` の項だから受理されるはずである:
-/

#check (MySum.inr true : MySum Nat Bool)

/-!
    MySum.inr true : MySum Nat Bool

暗黙引数が**いつでも**決まるわけではない。
`MySum.inl 3` では、中身 `3 : Nat` から `α` は分かっても、
使っていない右側の型 `β` は分からない。
`#check MySum.inl 3` だけでも表示は出るが、`β` の位置は未確定の型として残る。
上の例では、結果の型注釈がその不足を補っている。

なお、**どの関数の引数か**にも注意しよう。
型を作る関数 `MySum` の表示は `(α β : Type)` なので、`MySum Nat Bool` と型を2つ渡す。
一方、Lean が生成した構成子 `MySum.inl` では同じパラメータが `{α β : Type}` になっており、
`MySum.inl 3` のように通常は省略できる。引数が明示か暗黙かは、それぞれの関数の型の表示から読む。

この型でも、**引数 `α` の値が後ろの引数の型に現れる**。構成子も、
[`01_TypesAndTerms.lean` の4節](#sec-Intro1.dependent-functions)で学んだ依存関数として適用できる。
-/

/-!
`MySum α β` の項は、「`α` の項に `inl` の札を付けたもの」か
「`β` の項に `inr` の札を付けたもの」のどちらか。集合のアナロジーでは
**直和** $\alpha \sqcup \beta$ である——`NatOrBool` は `MySum Nat Bool` に相当する
（`04_Exists.lean` に出てくる `⊕` は、標準ライブラリにあるこれと同じ型）。

使う側の `match` も、`NatOrBool` と同じように書ける。
パラメータで中身の型を変えられるようになったが、構成子ごとに中身を取り出して使う仕組みは変わらない。
次の例では `α := Nat`・`β := Bool` としているので、
`.inl n` の中身 `n` は `Nat` 型であり、そのまま返せる:
-/

def fromSum : MySum Nat Bool → Nat := fun x =>
  match x with
  | .inl n => n
  | .inr _ => 0

#check fromSum

/-!
    fromSum : MySum Nat Bool → Nat

直和の普遍性との対応も同じで、`inl` の場合は `Nat` から `Nat` への恒等写像、
`inr` の場合は `Bool` から `Nat` への、常に `0` を返す写像を指定している。
-/

/-!
### ✏ 練習

1. `MySum Bool Bool` の左右どちらの札からも、中身の `Bool` をそのまま返す
   `mergeBool : MySum Bool Bool → Bool` を書け。
   `#eval mergeBool (MySum.inl true)` と
   `#eval mergeBool (MySum.inr false)` を予想してから確かめよ。
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 型をパラメータにした取り出し関数

取り出す側も、パラメータを持たせて一般的に書ける。次の `getLeft` は
「既定値 `d` を受け取り、左の札なら中身を、右の札なら `d` を返す」関数で、
`fromSum` はその `Nat`・`Bool`・`0` への特殊化に当たる。
先ほど見た構成子と同様に、`{α β : Type}` を暗黙引数として宣言しておけば、
この関数を使うときにも、ほかの引数の型などから `α`・`β` を補ってもらえる:
-/

def getLeft {α β : Type} (d : α) : MySum α β → α := fun x =>
  match x with
  | .inl a => a
  | .inr _ => d

#check getLeft

/-!
    getLeft {α β : Type} (d : α) : MySum α β → α

使ってみる。`getLeft 0 (MySum.inr true)` という項を読む: `d = 0 : Nat` から
`α = Nat` が、`true : Bool` から `β = Bool` が埋まり、全体の型は `Nat`。
値は「右の札」を渡したのだから、既定値 `0` が返るはずである:
-/

#eval getLeft 0 (MySum.inr true)

/-!
    0
-/

/-!
CALLOUT_END
-/

/-!
### ✏ 練習

1. `#eval getLeft 7 (MySum.inl 3 : MySum Nat Bool)` の値を予想してから
   確かめよ。（`MySum.inl 3` だけでは `β` が決まらないので、型注釈で教えている。）
-/

/-!
### 構成子は自分自身の型を引数に取れる（再帰）

構成子の引数に、いま定義している型そのものを使ってよい。
例として、自然数を自分で作ってみる。
-/

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat

/-!
    MyNat : Type
-/

/-!
`MyNat` の項は、`zero` に `succ` を有限回適用したものがすべて。
列挙型と違って項は無限にあるが、どの項も**有限の手順**で作られている。
ここでも、`MyNat.zero ≠ MyNat.succ n` や、「`succ m = succ n` ならば `m = n`」
（`succ` の単射性）が Lean の中で証明できる。
-/

/-!
### 補足: 集合の方程式としての再帰

集合のアナロジーでは、`MyNat` は方程式

$$X \cong 1 \sqcup X$$

を満たす**最小**の集合と読める（右辺の $1$ は `zero` の分の1点、$X$ は `succ` の引数の分）。右辺に自分自身が現れるのが再帰の印で、
最小性は「`zero` に `succ` を有限回重ねたものがすべてで、それ以外にない」
ということの言い替えである。
-/

/-!
使う側では、これまでと同じく `match` で構成子ごとに場合分けする。
今度は `.succ k` から取り出した `k` も `MyNat` の項なので、
その**ひと回り小さい項**に、いま定義している関数を再帰的に適用できる。
次の足し算は、2つ目の引数 `n` についてこの仕組みを使う:
-/

def add : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | .zero   => m
  | .succ k => .succ (add m k)   -- 構造が小さくなる方向への再帰

#check add

/-!
    add : MyNat → MyNat → MyNat
-/

/-!
### 補足: 再帰が止まることの検査

自分自身を呼ぶ定義は、何でも受理されるわけではない。再帰呼び出しがいつまでも
続くと、計算が終わらないからである。Lean は受理する前に、再帰呼び出しの引数が
構造的に小さくなっていること（`add` なら `.succ k` の中の `k`）を確かめ、
計算が必ず止まることを保証している。確かめられなければエラーになる:

    def loop (n : MyNat) : MyNat := loop n

    error: fail to show termination for
      loop
    with errors
    failed to infer structural recursion:
    Not considering parameter n of loop:
      it is unchanged in the recursive calls

「引数 `n` が再帰呼び出しで変わっていない」という報告である。
停止することも、型と同じく機械的な検査の対象なのである。
-/

/-!
`add` の計算を、今度は `#reduce`——項を計算して**構成子の形**で表示するコマンド——で確かめよう。「1 + 1」に当たる
`add (.succ .zero) (.succ .zero)` を読んでみよう。`match` の2つ目の場合から
`add m (succ zero) = succ (add m zero)`、さらに1つ目の場合から `add m zero = m`。
だから値は `succ (succ zero)`、つまり「2」のはずである:
-/

#reduce add (.succ .zero) (.succ .zero)

/-!
    MyNat.zero.succ.succ

`MyNat.zero.succ.succ` は `MyNat.succ (MyNat.succ MyNat.zero)` のこと
である。ここでも**型から名前の接頭辞を補う**ドット記法が使われている。
`.red` では期待される型を手がかりにしたが、今度は**ドットの左の項の型**が手がかりになる。
`n : MyNat` に対して `n.succ` と書くと、Lean は型 `MyNat` から関数 `MyNat.succ` を
見つけ、そこに `n` を渡す。つまり `n.succ` は関数適用 `MyNat.succ n` の略記である。

型を順に追うと、`MyNat.zero : MyNat`、`MyNat.zero.succ : MyNat`、
さらに `MyNat.zero.succ.succ : MyNat` となる。たしかに `succ` が2回重なった項、
つまり「2」が返ってきた。
-/

/-!
### ✏ 練習

1. `isZeroMyNat : MyNat → Bool` を `match` で書き、`.zero` なら `true`、
   `.succ _` なら `false` を返せ。`#eval isZeroMyNat MyNat.zero` と
   `#eval isZeroMyNat (MyNat.succ MyNat.zero)` の値を予想して確かめよ。
2. `toN : MyNat → Nat` を再帰で書け。`.zero` は `0`、`.succ k` は
   `toN k + 1` に送る。`#eval toN (MyNat.succ (MyNat.succ MyNat.zero))` の
   値を予想してから確かめよ。
-/

/-!
標準ライブラリの型はほとんどすべて帰納型である。
`Bool` `Unit` `Empty`（上で引用した）、`Nat`（リテラル `3` は
`succ (succ (succ zero))` の表示）、`04_Exists.lean` に出てくる `×` `⊕`、
さらには命題の側の `And` `Or` `Eq` すらもそうなのだが、命題の話は
`04_Exists.lean` に譲る。

`06_Topology.lean` では、`Nat` の再帰で集合の有限個の共通部分 `interFin` を定義し、
その性質もまた再帰で証明している。**再帰で書いた証明が数学的帰納法**である。
-/

/-!
### ✏ 練習

1. `MyNat` の項として 3 を `def myThree : MyNat := …`（`succ` 3回）と書き、
   `#reduce add myThree MyNat.zero` の表示を予想してから確かめよ。
2. 2点の列挙型 `inductive Two : Type where | a : Two | b : Two` を定義せよ。`Two` と `Bool` は
   集合としては同じ2点集合だが、型としては別物である。往復の関数
   `toBool : Two → Bool` と `ofBool : Bool → Two` を書き、
   `#eval toBool (ofBool true)` を確かめよ。
3. `Two → Bool` の関数は、集合のアナロジーで数えると $2 \times 2 = 4$ 通り
   あるはずである。その4つすべてを `def g1 : Two → Bool := …` から `g4` まで
   書け（前問の `toBool` はその1つ）。有限型の間の関数を書くことは、
   **値の対応表を書くこと**にほかならない。
4. （発展）掛け算 `mul : MyNat → MyNat → MyNat` を、本文の `add` の再帰に
   ならって書け（`m × 0 = 0`、`m × (k + 1) = m × k + m` を写す:
   `.zero` の場合は `.zero`、`.succ k` の場合は `add (mul m k) m` を返す）。
   `#eval toN (mul myThree myThree)` の値を予想してから確かめよ
   （`toN`・`myThree` は前の練習で書いたもの）。
5. （発展）上で書いた `toN : MyNat → Nat` の逆向きの関数
   `ofN : Nat → MyNat` を書き、`#eval toN (ofN 3)` の値を予想してから確かめよ。
   （`ofN` では `Nat` の項を `match n with | 0 => … | k + 1 => …` で
   場合分けできる。`| k + 1` は `| .succ k` と同じ「後続の自然数」の場合で、
   `k` は一つ前の自然数を表す。したがって `ofN k` は元の入力より小さい数への
   再帰である。これは方程式 `n = k + 1` を解く操作ではなく、`Nat` の構成子に
   よる場合分けである。この書き方はここが初出である。また、**すべての** `n` で
   往復が恒等になることの証明には数学的帰納法が要る。`04_Exists.lean` のあとで
   戻ってくるとよい。）
-/

/-!
## 2. structure {#sec-Intro1.structures}

構成子が**1つだけ**で、その構成子が**複数の引数**を受け取る帰納型は、
「成分をまとめて持ち運ぶ入れ物」としてよく使う。
[1節](#sec-Intro1.inductive-types)の練習では、`NatPair` や `FlaggedNat` を定義し、
`match` で成分を取り出す関数を書いた。そのうち、自然数を2つ持つ場合を
`MyPoint` という名前でもう一度確認しよう。
-/

inductive MyPoint : Type where
  | mk (x y : Nat) : MyPoint

#check MyPoint

/-!
    MyPoint : Type
-/

/-!
構成子は `MyPoint.mk` の1つだけである。もちろん引数を変えれば異なる項が作られるが、
構成子による場合分けは1ケースで済む。[1節](#sec-Intro1.inductive-types)で書いた
`firstNat` と同じように、第1成分を取り出す関数が書ける。
-/

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | .mk a _ => a

#check MyPoint.x

/-!
    MyPoint.x : MyPoint → Nat

帰納型の項を構成子に応じて場合分けするには `match` を使う——構成子が1つなら、
場合分けが1ケースになるだけで、原理は [1節](#sec-Intro1.inductive-types)と変わらない。
-/

/-!
この「構成子1つの帰納型＋成分の取り出し関数」をひとまとめに書く構文が
`structure` である。つまり structure は `inductive` の**構成子を1つだけ持つ特別な場合**であり、
`inductive` と同じく、新しい型を定義するやり方の1つである。
structure では、構成子の各引数に名前を付けて宣言する。
この名前付きの成分を**フィールド**（field）と呼ぶ。利点は2つ:

* **フィールドに名前を付けられる**（その名前がそのまま取り出し関数になる）
* 構成子 `mk` と取り出し関数が**自動で定義される**（自分で書かなくてよい）
-/

structure Point : Type where
  x : Nat
  y : Nat

#check Point

/-!
    Point : Type

自動定義されるものの型を推測しよう。構成子 `Point.mk` はフィールドを順に
受け取るから `Nat → Nat → Point`、取り出し関数 `Point.x` は
`Point → Nat` のはずである:
-/

#check Point.mk

/-!
    Point.mk (x y : Nat) : Point

自動定義された構成子。矢印形式に読み替えれば `Nat → Nat → Point`。
期待される型が `Point` と分かる位置では、`⟨1, 2⟩` とも書ける。
これは**匿名構成子記法**という組み込みの構文で、期待される型から構成子を決める
（これも[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の「上から伝える」仕組みである）。
この場合は `Point.mk 1 2` と解釈される。
`+` のように記法宣言で関数名に結び付けるものとは異なり、型に応じて構成子を選ぶ仕組みである。
structure 専用ではなく、構成子が1つの帰納型でも使える。

期待される型が `Point` と分かる位置では、`Point.mk` を `.mk` とも書ける。
[1節](#sec-Intro1.inductive-types)の `.red` と同じく、期待される型から名前の
接頭辞を補う。例えば次の宣言では、`: Point` がその手がかりになる:
-/

#check (⟨1, 2⟩ : Point)

/-!
    { x := 1, y := 2 } : Point

型注釈が `Point` なので、その構成子 `Point.mk` を使った項として読まれる。
-/

def pointFromDot : Point := .mk 1 2

def pointFromPair : Point := ⟨1, 2⟩

#check pointFromDot

/-!
    pointFromDot : Point

右辺は `Point.mk 1 2` と解釈され、その型が宣言どおり `Point` であると確認できた。
-/

#check Point.x

/-!
    Point.x (self : Point) : Nat

自動定義された取り出し関数。矢印形式では `Point → Nat`。

`p : Point` に対して、関数適用 `Point.x p` は `p.x` とも書ける。
Lean は `p` の型から関数 `Point.x` を見つけ、そこに `p` を引数として渡す。
これは[1節](#sec-Intro1.inductive-types)で見た `n.succ` と同じ読み方である。
`.mk` では**期待される型**を、`p.x` では**左の項の型**を手がかりにするが、
型から名前の接頭辞を補うという考え方は共通している。

例えば `(Point.mk 1 2).x` は `Point.x (Point.mk 1 2)` の略記。
`Point.mk 1 2 : Point` を `Point.x : Point → Nat` に渡すので、全体の型は `Nat`、
値は第1成分の `1` のはずである:
-/

#eval (Point.mk 1 2).x

/-!
    1

第1フィールドに入れた値が、そのまま返ってきた。
-/

/-!
### 直積の普遍性を思い出す

集合のアナロジーでは、`Point` は直積 $\mathrm{Nat} \times \mathrm{Nat}$ である。
**直積の普遍性**を思い出そう。同じ集合 $A$ からの2本の写像
$f, g : A \to \mathrm{Nat}$ を与えると、各 $a$ を組 $(f(a), g(a))$ に送る写像
$h : A \to \mathrm{Nat} \times \mathrm{Nat}$ がただ1つ定まる。逆に $h$ の各成分を取り出せば、$f$ と $g$ に戻る。

Lean では `Point.mk` が組を作る側、`Point.x`・`Point.y` が成分を取り出す側に当たる。
次の練習では、この対応をコードにし、具体的な入力で確認しよう。
一意性の証明までは求めない。
-/

/-!
### ✏ 練習

1. 型 `A` と2本の写像 `f g : A → Nat` が与えられたとする。
   $a$ を組 $(f(a), g(a))$ に送る写像 `pairAt A f g : A → Point` を定めたい。
   `pairAt (A : Type) (f g : A → Nat) : A → Point` を書き、`#check pairAt` で型を確認せよ。
   $A = \mathrm{Nat}$、$f(n) = n + 1$、$g(n) = 2n$ として `3` を渡したときの
   第1・第2成分を予想し、`Point.x`・`Point.y` と `#eval` で確かめよ。

2. `Point` の第1成分だけを1増やす `moveRight : Point → Point` を書け。
   成分の取り出しには `Point.x`・`Point.y`、作成には `Point.mk` を使う。
   `#eval Point.x (moveRight (Point.mk 1 2))` の値を予想して確かめよ。
-/

/-!
### 自分で定義した関数もドットで使える

この書き方は、自動生成される取り出し関数に限らない。
`Point` 型の項を受け取る関数を `Point.〜` という名前で定義すれば、同じように使える。
成分を入れ替える関数を作ってみよう:
-/

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

#check Point.swap

/-!
    Point.swap (p : Point) : Point

本体の `⟨p.y, p.x⟩` は、上で見た匿名構成子記法である。期待される型が `Point` なので、
`Point.mk p.y p.x` と読まれる（`⟨ ⟩` は `\<` `\>` で打てる）。

`Point.swap : Point → Point` なので、`p : Point` に対して `p.swap : Point`。
さらに `p.swap.x : Nat` と続けられる。内側から読むと、`p.swap.x` は
`Point.x (Point.swap p)` の略記である。次の値は、入れ替える前の第2成分 `2` のはずだ:
-/

#eval (Point.mk 1 2).swap.x

/-!
    2

`swap` で `x` と `y` が入れ替わった。ドットを使わずに
`#eval Point.x (Point.swap (Point.mk 1 2))` と書いても、同じ `2` が返る。
このような名前の付け方の一般論——名前空間——は、
[`05_MathematicalTools.lean` 4節](#sec-Intro2.namespaces)で扱う。
-/

/-!
### ✏ 練習

1. `Point.zeroX (p : Point) : Point` を定義し、第1成分だけを `0` にせよ。
   本体では `p.y` と `.mk` の両方を使う。`#eval (Point.mk 1 2).zeroX.x`
   の値を予想して確かめよ。
2. `#eval (Point.mk 1 2).swap.swap.x` の値を予想してから確かめよ
   （2回入れ替えると元に戻るはずである）。またこの式を、ドットを使わず
   フルネームの適用だけで書き直すと何になるか、紙に書いてから `#eval` で
   一致を確かめよ。

3. 次の structure を定義し、`#check` で構成子と取り出し関数が
   自動定義されていることを確かめよ:

       structure Circle : Type where
         center : Point
         radius : Nat

4. 点 p と自然数 n から、中心が p、半径が n の円を作る写像を、
   `makeCircle : Point → Nat → Circle` として書け。型を `#check` し、
   `#eval Circle.radius (makeCircle (Point.mk 1 2) 3)` の値を予想して確かめよ。
5. 円からその中心の第1座標を取り出す写像 `centerX : Circle → Nat` を書け。
   型を `#check` し、`#eval centerX (makeCircle (Point.mk 1 2) 3)` の値を予想して確かめよ。

6. `#eval Point.y (Point.mk 1 2)` の値を予想してから確かめよ。
   さらに `(Point.mk 1 2).y` とも書けることを試し、同じ値が返ることを確かめよ。
7. フィールドの型は、自作の structure でもよい。長方形

       structure Rect : Type where
         corner : Point
         width : Nat
         height : Nat

   を定義し、`def r : Rect := ⟨⟨1, 2⟩, 10, 5⟩` が受理されることを確かめよ
   （`⟨ ⟩` の入れ子が `corner : Point` の分である）。`#eval r.corner.x` の
   値を予想してから確かめよ。`r.corner`、`r.corner.x` の順に型を追うこと。
8. 長方形から幅と高さの積を返す写像 `rectArea : Rect → Nat` を書け。
   型を `#check` し、前問の `r` に対する `#eval rectArea r` の値を予想して確かめよ。
-/

/-!
### 型をパラメータにする structure

structure は引数（パラメータ）を取ることもできる。
-/

structure Pair (α β : Type) : Type where
  fst : α
  snd : β

#check Pair

/-!
    Pair (α β : Type) : Type

`Pair.mk` の型は? `MySum.inl` と同じく、パラメータの分の暗黙引数
`{α β : Type}` が付くはずである:
-/

#check Pair.mk

/-!
    Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β
-/

#check Pair.fst

/-!
    Pair.fst {α β : Type} (self : Pair α β) : α
-/

/-!
集合のアナロジーでは、`Point` は直積 $\mathrm{Nat} \times \mathrm{Nat}$、`Pair α β` は直積 $\alpha \times \beta$ である。
`p : Pair α β` は、`p.fst : α` と `p.snd : β` の二つを組にしたものであり、
逆に `a : α` と `b : β` から `Pair.mk a b` を作れる。
集合の直積で、組 $(a,b)$ を作り、二つの射影で $a$ と $b$ を取り出すことに対応する。
つまり structure は「**直積の各成分に名前を付けたもの**」と思ってよい。
実際、標準ライブラリの `×` 自身が `fst`/`snd` という2フィールドの
structure（名前は `Prod`）として定義されている。
-/

/-!
### ✏ 練習

1. `#check Pair.mk true 0` の表示を予想してから確かめよ
   （`α`・`β` は何に決まるか）。
2. （発展）[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の「カリー化」の正体を自分で書く。組を受け取る関数を
   「1つずつ受け取る」形に直す
   `curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat` と、その逆向き
   `uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat` を書け。
   `#check curryP`・`#check uncurryP` で型を確認し、
   `#eval curryP (fun p => p.fst + p.snd) 3 4` の値を予想してから確かめよ。
-/

/-!
### 補足: 帰納型を直和と直積で見る

前節の直和とここの直積をまとめると、ここまでの非再帰的で、
構成子の引数の型が互いに依存しない例は、集合の言葉でこう読める:

$$(\text{構成子1の引数たちの直積}) \sqcup (\text{構成子2の引数たちの直積}) \sqcup \cdots$$

つまり**構成子の個数が直和の項数を、各構成子の引数が直積の因子を**与える。
`Signal` は $1 \sqcup 1 \sqcup 1$（3点集合）、`MySum α β` は $\alpha \sqcup \beta$（直和だけ）、
`Point` は $\mathrm{Nat} \times \mathrm{Nat}$（直和が1項に退化して直積だけ）、
構成子が0個なら空集合（`Empty`）。
「structure は直積」と「帰納型は直和のようなもの」は矛盾しない——
直和を**使って**直積を定義しているのではなく、構成子の**個数**と**引数**という
直交した2つの軸が、それぞれ直和と直積に対応しているのである。

なおアナロジーの注意を1つ。集合と違って、型は**外延（要素の一致）では
同一視されない**。`Point` と `Pair Nat Nat` は「中身」は同じだが別の型である
（この話は [2節](#sec-Intro1.subtypes)の `Fin` の補足でも再登場する）。
-/

/-!
### 族の直積と直和では、何を選ぶのか

同じ集合族 $B(a)$ から、直積と直和を考えられる。違いは、要素を1つ指定するために
**すべての添字について選ぶのか、一つの添字を選ぶのか**にある。

**族の直積** $\prod_{a \in A} B(a)$ の要素は、各 $a \in A$ に対して
$f(a) \in B(a)$ を一つずつ選ぶ関数 $f$ である。
これが [`01_TypesAndTerms.lean` の4節](#sec-Intro1.dependent-functions)で見た依存関数である。

**族の直和** $\bigsqcup_{a \in A} B(a)$ の要素は、添字 $a \in A$ を一つ選び、
$b \in B(a)$ を一つ添えた組 $(a,b)$ である。
次に、型を一つ選び、その型の項を一つ添えた組を、structure で表してみる。
-/

/-!
### フィールドは前のフィールドに依存してよい

今度は、「どの集合を選ぶかで、その上に載せる構造の集まりも変わる」という状況を考えよう。
サイズの問題をいったん脇に置くと、群を1つ指定することは、集合 $X$ と、
その上の群構造を1つ指定することである。集合 $X$ ごとにその上の群構造全体を $\mathrm{Grp}(X)$ と書けば、
群全体は**集合族の直和** $\bigsqcup_{X} \mathrm{Grp}(X)$ として捉えられ、個々の群がその要素に当たる。
ここで群構造には、演算・単位元・逆元と、それらが満たす公理を含めている。
同様に、位相空間を1つ指定することも、集合 $X$ とその上の位相を1つ指定することである。

一般に、族の直和 $\bigsqcup_{a \in A} B(a)$ の要素は、
「$a$ を1つ選び、それに応じた $B(a)$ の要素を1つ添える」という組である。

族 $B(a)$ が $a$ によらない定数 $B$ のときは、$\bigsqcup_{a \in A} B = A \times B$ となる。
つまり、これまでの依存しないフィールドによる直積も、族の直和の構成子を1つだけ持つ特別な場合である。

structure でも、**後のフィールドの型を、前のフィールドに依存させる**ことで、
この形のデータを表せる。証明をフィールドに持たせる実例は `04_Exists.lean` で読み、
ここでは単純な**点付き集合**——集合と、その要素を1つ選んだ組——を例にしよう。

[`01_TypesAndTerms.lean` 1節](#sec-Intro1.terms-types)で見たとおり型も項だから、フィールドの値として**型そのもの**を持たせ、
次のフィールドの型をその値で決める、ということができる:
-/

structure PointedType : Type 1 where
  carrier : Type
  point : carrier

#check PointedType

/-!
    PointedType : Type 1

「型 `carrier` と、その要素 `point`」の組——数学でいう**点付き集合**である。
`carrier` に型そのものを入れるため、この入れ物の型は `Type 1` になる。
これは[`01_TypesAndTerms.lean` 1節](#sec-Intro1.terms-types)で見た `Type : Type 1` と対応している。
`mk` の型を推測しよう。フィールドの列そのまま……のはずで、[1節](#sec-Intro1.inductive-types)の `MySum.inl` と
同じく、**第2引数の型の中に第1引数の名前が現れる**ことになる:
-/

#check PointedType.mk

/-!
    PointedType.mk (carrier : Type) (point : carrier) : PointedType
-/

/--
例:「型 `Nat` と、その要素 `0`」の組。
-/

def pointedNat : PointedType := ⟨Nat, 0⟩

#check pointedNat

/-!
    pointedNat : PointedType
-/

/-!
第二フィールド `point` の型が、第一フィールド `carrier` の**値**で決まっている
（`pointedNat` では `point : Nat`）。
この例では、族の直和の添字として型 `carrier` を選び、
その型の項 `point` を1つ添えている。

-/

/-!
### 依存するフィールドも inductive で書ける

この場合も、structure が構成子1つの帰納型であることは変わらない。
同じ形のデータを、`inductive` で書いてみよう:
-/

inductive MyPointedType : Type 1 where
  | mk (carrier : Type) (point : carrier) : MyPointedType

/-!
構成子の引数を順に読むと、まず `carrier : Type` を受け取り、
次に**その `carrier` 型の** `point` を受け取る。型を確かめよう:
-/

#check MyPointedType.mk

/-!
    MyPointedType.mk (carrier : Type) (point : carrier) : MyPointedType

この構成子も**依存関数**である。最初に受け取る `carrier` によって、
次の引数 `point` の型が変わる。

`PointedType.mk` と同じ形で、最後の行き先だけが `MyPointedType` になっている。
別の名前で宣言したので `PointedType` と同一の型ではないが、持つデータは同じ形である。
`inductive` で書いた側では成分を取り出す関数を `match` で書くのに対し、
`structure` では `PointedType.carrier`・`PointedType.point` が自動生成される。
-/

/-!
### ✏ 練習

1. `def pointedBool : PointedType := ⟨Bool, true⟩` が受理されることを確かめよ。
   また `#check PointedType.mk Nat` の表示を予想してから確かめよ
   （第1引数を渡すと、第2引数の型が決まる）。

2. 自然数 n を点付き集合 (Nat, n) に送る写像 `attachNat : Nat → PointedType` を書け。
   型を `#check` し、`#reduce (attachNat 3).point` の値を予想して確かめよ。
3. 点付き集合 (A, a) から台となる型 A を取り出す写像 `baseType : PointedType → Type` を書け。
   型を `#check` し、`#reduce (types := true) baseType pointedNat` と
   `#reduce (types := true) baseType pointedBool` の表示を予想して確かめよ。
   ここで `(types := true)` は、型そのものも計算して表示させる指定である。
   通常の `#reduce` は型の計算を省くので、今回はこの指定を付ける。
4. 点付き集合 $(A, a)$ と写像 $f : A \to A$ から、点付き集合 $(A, f(a))$ を作る関数
   `mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType` を書け。
   型を `#check` し、`#reduce (mapPointed pointedNat Nat.succ).point` の値を予想して確かめよ。
-/

/-!
CALLOUT_START optional
-/

/-!
### 復習: 取り出す値の型も入力で変わる

台となる型だけでなく、その中の点を取り出す関数も読んでみよう。
`p : PointedType` の点は `p.carrier` 型なので、取り出し関数の結果の型は
**入力 `p` によって変わる**はずである:
-/

#check PointedType.point

/-!
    PointedType.point (self : PointedType) : self.carrier

たしかに、結果の型に引数 `self` が現れた。`PointedType → Nat` のように
固定した行き先では書けない。これは [`01_TypesAndTerms.lean` の4節](#sec-Intro1.dependent-functions)で学んだ依存関数型である。
-/

/-!
### ✏ 練習

1. 点付き集合 (A, a) から点 a を取り出す関数 `getPoint (p : PointedType) : p.carrier` を書け。
   `#check getPoint` の表示を予想して確かめ、結果の型が引数に依存している箇所を指摘せよ。
   さらに `#reduce getPoint pointedNat` と `#reduce getPoint pointedBool` の値を予想して確かめよ。
-/

/-!
CALLOUT_END
-/

/-!
### ✏ 練習

1. 型 α・β とその項 a・b から組を作る
   `makePair (α β : Type) (a : α) (b : β) : Pair α β` を書け。
   `#check makePair Nat Bool 3 true` を確かめよ。
2. 同じ引数から成分を交換した組を作る
   `swapAt (α β : Type) (a : α) (b : β) : Pair β α` を書け。
   `#check swapAt Nat Bool` で残りの型を確かめよ。
3. `#check idAt Signal` の表示を予想せよ。
-/

/-!
### 部分型 — 値と証明の組 {#sec-Intro1.subtypes}

`01_TypesAndTerms.lean` では「`n` 未満の番号の型」`Fin n` を使った。
後のフィールドの型が前のフィールドに依存するなら、その型が命題でもよい。
その場合は、値と、その値についての証明を一緒に持つ。`Fin` の定義を見よう:

    structure Fin (n : Nat) where
      val : Nat
      isLt : val < n

値 `val` と、「その値が `n` 未満だ」という**証明** `isLt` の組——
依存和の第二成分を命題にしたもの——である。このように、述語で切り出した
「値と証明の組」の型を**部分型**と呼ぶ（専用記法 `{x // p x}` は
`07_Exercises.lean` で使う）。

中身が分かれば、項も作れる。値が `n` に依存する依存関数の例として、
「`Fin (n + 1)` の**最後の**番号」を作ってみる:
-/

def last : (n : Nat) → Fin (n + 1) := fun n => ⟨n, Nat.lt_succ_self n⟩

#check last

/-!
    last (n : Nat) : Fin (n + 1)

値 `n` に、命題 n < n + 1 の証明（ライブラリの `Nat.lt_succ_self n`）を
添えて組にしている。
-/

#check last 2

/-!
    last 2 : Fin (2 + 1)

型の中の `n` に `2` が入った。
-/

#check last 9

/-!
    last 9 : Fin (9 + 1)
-/

/-!
同じ族に沿って、「番号 `n` を受け取り、`Fin (n + 1)` の**最初の**番号 0 を返す」関数も書ける:
-/

def first : (n : Nat) → Fin (n + 1) := fun _ => 0

#check first

/-!
    first (n : Nat) : Fin (n + 1)
-/

#check first 2

/-!
    first 2 : Fin (2 + 1)
-/

#check first 9

/-!
    first 9 : Fin (9 + 1)

値はどれも「0 番」だが、その `0` の住んでいる型が入力ごとに違う。
`0` と書けるのは、数字が期待される型に応じて読まれる記法だからである
（[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)）。
`last` と見比べてほしい。`first` の値は常に 0 番なので証明を書かずに済むが、
`last` は値 `n` が型の上限すれすれに依存するぶん、`n < n + 1` の証明を添える必要があった。
-/

/-! CALLOUT_START optional -/
/-! ### 補足: では `2 : Fin 3` なのか？

「`Fin 3` は 3 未満の番号の型」と聞くと、集合 $\{0, 1, 2\} \subset \mathbb{N}$ を思い浮かべて、
「自然数 `2` はそのまま `Fin 3` の項でもあるのか」と考えたくなる。そうではない。
`Fin 3` の項は、上で見たとおり値と証明の組であり、`Nat` の項とは**別の型の項**である。
集合のように、`Fin 3` が `Nat` の部分集合として含まれているわけではない。

まぎらわしいことに、`(2 : Fin 3)` という書き方自体は通る:
-/

#check (2 : Nat)

/-!
    2 : Nat
-/

#check (2 : Fin 3)

/-!
    2 : Fin 3
-/

/-!
これは数字 `2` が**記法**であり、期待される型に応じて別々の項に読まれるからである
（[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の `2 : Int` と同じ仕組み）。
`(2 : Nat)` は自然数の項、`(2 : Fin 3)` は `Fin 3` の「2 番」の項で、
**同じ字面の、別の項**なのである。所属を判定しているのではない証拠に、
`(5 : Fin 3)` すら通り、3 で割った**余り**として読まれる:
-/

#eval (5 : Fin 3)

/-!
    2

`2` になった。リテラルをどう読むかは、`Fin` 用に用意された読み方で決まる
（その仕組みは [`05_MathematicalTools.lean` 1節](#sec-Intro2.classes)の補足で見る）。

`.val` は「番号を自然数として取り出す」関数（`Fin n → Nat`）である:
-/

#eval (2 : Fin 3).val

/-!
    2
-/

/-!
2つの `2` を等号で結ぼうとすると、面白いことが起きる:
-/

#check (2 : Nat) = (2 : Fin 3)

/-!
    2 = ↑2 : Prop
-/

/-!
型エラーにはならないが、右辺に `↑` が付いた。これは**強制**（coercion）の印で、
Lean が `Fin 3 → Nat` の写像（`.val`）を自動で挟み、
「`Nat` の世界に持ち上げてから比べる」形に読み替えている。
逆向きはそうはいかない。`Fin 3` を引数に取る関数を用意して、`(2 : Nat)` を
渡してみると:

    def useFin (x : Fin 3) : Fin 3 := x
    #check useFin (2 : Nat)

    error: Application type mismatch: The argument
      2
    has type
      Nat
    but is expected to have type
      Fin 3
    in the application
      useFin 2

`Nat → Fin 3` の向きには「3 未満に収まっているか」の確認が要るので、
自動では埋められない。まとめると、`Fin 3` と `Nat` の関係は
「部分集合と全体」ではなく、**写像 `.val` で結ばれた別々の型**である。
-/
/-! CALLOUT_END -/

/-!
### ✏ 練習

1. `#check (last 4).val` の表示を予想してから確かめよ
   （表示に付く `↑` は**強制**の印——上の補足で説明した）。
2. `#check first 4` の表示と、`#eval (first 4).val` の値を予想してから確かめよ。
3. `#check first 0` の表示を予想してから確かめよ（`Fin (0 + 1)` は1点の型である）。
-/

/-! CALLOUT_START optional -/
/-!
### ✏ 練習

4. （補足の確認）`#eval (5 : Fin 4)` の表示を予想してから確かめよ。
5. （補足の確認）`#eval (first 5).val + (2 : Fin 3).val` の値を予想してから確かめよ。
-/
/-! CALLOUT_END -/

/-!
## 3. まとめ練習 — 小さな型つき言語で書く {#sec-Intro1.exercises}

ここまでの部品——`fun` と適用、`match`、`inductive`、`structure`、
型を引数に取る関数——だけで、Lean は小さな**型つきプログラミング言語**として
使える。仕上げに、**集合と写像の言葉で述べた仕様を、Lean の型と項として書く**総合練習を置く。

-/

/-!
### ✏ 練習

1. 写像 $F : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ に対して、$G(a, b) = F(b, a)$ で定まる写像
   $G : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ を対応させる操作を考える。
   この対応 $F \mapsto G$ を、カリー化を使って
   `flipNat (F : Nat → Nat → Nat) : Nat → Nat → Nat` として書け。
   `#eval flipNat (fun a b => a - b) 3 10` の値を予想してから確かめよ。
   次に、任意の型 `A` に対して `flipAt (A : Type) (F : A → A → A) : A → A → A` を書け。
   一般化した関数を `Signal` に適用し、
   `#eval flipAt Signal (fun a _ => a) Signal.red Signal.green` の値を確かめよ。
2. 写像の集合の間の写像 $T : \mathrm{Map}(\mathbb{N}, \mathbb{N}) \to \mathrm{Map}(\mathbb{N}, \mathbb{N})$ を、
   $T(F) = F \circ F \circ F$、すなわち $T(F)(n) = F(F(F(n)))$ で定める。
   $T$ を `iterate3 (F : Nat → Nat) : Nat → Nat` として書け。
   `#eval iterate3 double 1` の値を予想してから確かめよ。
   次に、`iterate3At (A : Type) (F : A → A) : A → A` として一般化せよ。
   `#eval iterate3At Signal Signal.next Signal.red` では何が返るか、
   信号の変化を3回たどってから確かめよ。
3. 2点集合 $B = \{\mathrm{true}, \mathrm{false}\}$ と3点集合 $S = \{\mathrm{red}, \mathrm{yellow}, \mathrm{green}\}$ を考える。
   写像 $f : B \to S$ を $f(\mathrm{true}) = \mathrm{green}$、$f(\mathrm{false}) = \mathrm{red}$ で定め、
   写像 $g : S \to B$ を $g(\mathrm{green}) = \mathrm{true}$、$g(\mathrm{red}) = g(\mathrm{yellow}) = \mathrm{false}$ で定める。
   $B$ を `Bool`、$S$ を `Signal` で表し、$f$ と $g$ をそれぞれ
   `boolToSignal : Bool → Signal`、`signalToBool : Signal → Bool` として書け。
   合成 $g \circ f$ の $\mathrm{true}$ における値を予想し、
   `#eval signalToBool (boolToSignal true)` で確かめよ。
4. 写像 $F : \mathbb{N} \to \mathbb{N}$ に対して、写像 $H : \mathbb{N} \times \mathbb{N} \to \mathbb{N} \times \mathbb{N}$ を
   $H(x, y) = (F(x), F(y))$ で定める。
   直積 $\mathbb{N} \times \mathbb{N}$ を `Point` で表し、この対応 $F \mapsto H$ を
   `mapPoint (F : Nat → Nat) (p : Point) : Point` として書け。
   `#eval (mapPoint double (Point.mk 2 3)).y` の値を予想してから確かめよ。
5. 集合 $A, B$ の直和の間の交換写像 $s : A \sqcup B \to B \sqcup A$ を考える。
   $A$ 側の要素 $a$ は、行き先の $A$ 側、すなわち右側の要素 $a$ に送り、
   $B$ 側の要素 $b$ は、行き先の $B$ 側、すなわち左側の要素 $b$ に送る。
   中身は変えず、左右の位置だけを入れ替える写像である。
   直和を `MySum` で表し、$A, B$ も引数として受け取る
   `swapMySum (A B : Type) : MySum A B → MySum B A` を書け。
   `#eval fromSum (swapMySum Bool Nat (MySum.inl true))` の値を予想してから
   確かめよ（`fromSum : MySum Nat Bool → Nat` は[1節](#sec-Intro1.inductive-types)で定義した）。
6. 各集合 $A$ に対して、その要素 $a$ を点付き集合 $(A, a)$ に送る写像を考える。
   点付き集合を `PointedType` で表し、$A$ も引数として受け取る
   `pointedOf (A : Type) (a : A) : PointedType` を書け。
   [2節](#sec-Intro1.structures)の `pointedNat` や練習の `pointedBool` を、
   どの型とその項からも作れるように一般化したものである。
   `#check pointedOf Bool true` の表示を予想してから確かめよ。
7. （発展）集合 $A$ と写像 $F : A \to A$ に対して、その反復 $F^n : A \to A$ を、
   $F^0 = \mathrm{id}_A$、$F^{n+1} = F \circ F^n$ と定める。ここで $\mathrm{id}_A$ は $A$ 上の恒等写像である。
   自然数 $n$ と要素 $a$ を $F^n(a)$ に送る写像 $\mathbb{N} \times A \to A$ を、$A, F$ も引数に取り、
   `applyN (A : Type) (F : A → A) (n : Nat) (a : A) : A` として書け。
   `n` の `match` は `| 0 => …`・`| k + 1 => …` の形（[1節](#sec-Intro1.inductive-types)の練習の
   `ofN` と同じ）。`#eval applyN Nat double 3 1` の値を予想してから確かめよ。
8. （発展）集合 $A$ の対角写像 $\Delta_A : A \to A \times A$ を、$\Delta_A(a) = (a, a)$ で定める。
   直積を `Pair` で表し、どの型 $A$ でも使える
   `diag (A : Type) (a : A) : Pair A A` を書け。
   `#eval (diag Nat 3).fst` の値を予想してから確かめよ。
   A の項として与えられているのは a だけであることにも注目せよ。
   [`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の練習（`(Nat → Nat) → Nat` の項を2つ書く）と比較し、
   **型の形によって、書ける項の自由度がどう変わるか**を考えよ。
-/

/-!
関数に加えて、構成子と場合分けで項を作り使う道具がそろった。
次の `04_Exists.lean` で、存在を含む証明を読もう。その後は `05_MathematicalTools.lean` → `06_Topology.lean` と進む。
-/

/-!
## 付録: 記号の打ち方まとめ

本文の初出時にも注記したが、よく使う記号をまとめておく（`\` 略記のあとに
空白か Tab で確定。エディタ上の記号へのホバーでも確認できる）。

| 記号 | 打ち方 |
|---|---|
| `→` | `\to` または `\r` |
| `×` | `\times` または `\x` |
| `⟨` `⟩` | `\<` と `\>`（`\<>` で両方いっぺんに出る） |
| `α` `β` `γ` | `\a` `\b` `\g` |
| `∀` ／ `∃` | `\all` ／ `\ex` |
| `∧` ／ `∨` ／ `¬` | `\and` ／ `\or` ／ `\not` |
| `∈` ／ `∪` ／ `∩` ／ `∅` | `\in` ／ `\cup` ／ `\cap` ／ `\empty` |
| `≠` ／ `≤` ／ `↔` | `\ne` ／ `\le` ／ `\iff` |
| `⊕` ／ `ᶜ` ／ `▸` | `\oplus` ／ `\^c` ／ `\t` |
| `⋃` ／ `⦃` `⦄` | `\bigcup` ／ `\{{` と `\}}` |
-/
