/-!
# 型と項 I — 関数と依存関数型

Lean が証明を検査する仕組みを知るために、まずコードの読み方から始めよう。
この章では、数や関数を例に、書かれた項がどんな型を持つかを一つずつ確かめる。
その読み方を、次の章で証明に当てはめていく。

### この教材の読み方

中心は、書かれたコードを解読することである。項を見るたびに型を予想し、
`#check` の出力で確かめよう。各節の練習には、予想を言葉にする問題と、
小さな項を書いて確かめる問題がある。型を追う手順をつかむことが目的である。
型検査がそのまま証明の検査になることを、次の章で経験する。
-/

/-!
## 1. 項と型 {#sec-Intro1.terms-types}

Lean に書くものの基本の単位を**項**（term）と呼ぶ。項とは何かの正確な定義は
ここでは与えないが、さしあたり **`#check` の右側に書いてエラーが出ないものは
項だと考えてよい**。

型（type）は、ひとまず**集合のようなもの**、その型の項は**要素のようなもの**と
思ってもよい。ただし、これは大まかなイメージであり、型や項には、それらを
作り、扱うための規則がある。以後、その規則を少しずつ見ていく。

`#check e` は、項 `e` の**型**を調べて表示するコマンドである。
ここで、調べる対象の `e` は項だが、`#check e` 全体は項ではなく、Lean に対する
指示である。後で使う `def` も、新しい定義を導入するコマンドであり、項とは区別する。
エディタ右側のパネル（Infoview）に表示される結果を、本文では独立した枠で示す。
-/

#check 3

/-!
    3 : Nat

これは「項 `3` は型 `Nat`（自然数の型）を持つ」と読む。
-/

#check true

/-!
    Bool.true : Bool

「項 `true` は型 `Bool`（真偽値の型）を持つ」。表示が `Bool.true` となっているのは、
これが正式な名前だからである。ここで `.` は名前の区切りで、接頭辞 `Bool` と
名前 `true` をつないでいる。Lean はこの区切りを使って名前を扱う。
標準ライブラリでは `true` という短い名前も用意されているので、どちらでも書ける
（名前の詳しい仕組みは[`03_InductiveTypes.lean` 1節](#sec-Intro1.inductive-types)で見る）。

すべての項は型を持つ。ここで大事な観察が1つある。
**型を表す表記それ自体もまた項である**。実際、`Nat` を `#check` の右に書くと:
-/

#check Nat

/-!
    Nat : Type

`Nat` という表記は、`Type` という型を持つ項なのである
（以下ではこのことを、少し縮めて「型も項である」と言う）。

では `Type` は？
-/

#check Type

/-!
    Type : Type 1

`Type` もまた項であり、その型は `Type 1`。
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 宇宙の階段
-/

#check Type 1

/-!
    Type 1 : Type 2

`Type`, `Type 1`, `Type 2`, … の階層を宇宙（universe）と呼ぶ。
この教材では宇宙には**深入りしない**。
-/

/-!
CALLOUT_END
-/

/-!
型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（[3節](#sec-Intro1.functions)の `Map` と[4節](#sec-Intro1.dependent-functions)）。

数の演算や、等式・不等式も項として書ける。それぞれにどんな型が付くかを見てみよう。
-/

#check 3 + 4

/-!
    3 + 4 : Nat

「`3 + 4` という項は `Nat` 型を持つ」と読む。
-/

#check 1 + 1 = 2

/-!
    1 + 1 = 2 : Prop

今度は、出力の型が `Nat` ではなく `Prop` になった。別の例も見てみよう。
-/

#check 2 < 1

/-!
    2 < 1 : Prop

こちらも型は `Prop` である。ここで現れた `Prop` は、**命題**たちの型である。
等式 `1 + 1 = 2` も不等式 `2 < 1` も命題なので、`Prop` 型の項になる。
`2 < 1` のような**偽の命題も**、命題としては立派な項であることに注意しよう。
`#check` は命題の真偽を判定しているわけではない（証明の話は `02_Forall.lean` で扱う）。

`Prop` 自身の型も調べてみよう:
-/

#check Prop

/-!
    Prop : Type

`Prop` 自身もまた項であり、その型は `Type` である。
-/

/-!
CALLOUT_START preview
-/

/-!
### 先取り（[3節](#sec-Intro1.functions)・02_Forall）: 演算と命題の記号の定義

`+`・`=`・`<` が正確には何を表し、どのように定義されているかは後で説明する。
`+` は[3節](#sec-Intro1.functions)で関数として読み、型に応じて演算を選ぶ仕組みは
[`05_MathematicalTools.lean` 1節](#sec-Intro2.classes)で扱う。`=` と `<` は
[`02_Forall.lean` 0節](#sec-CH.propositions)で説明する。今は、それぞれの項にどんな型が
付くかを追えばよい。
-/

/-!
CALLOUT_END
-/

/-!
ここまでで確かめたことは2つである:
**項の型はいつでも `#check` で調べられる**こと、そして**型も項である**こと。

`#check` という機能があることから分かるように、Lean には**項を与えると、その型を
機械的に計算する仕組み**がある。この仕組みを証明の検証に使うのが、冒頭で述べた
この教材の行き先である。命題 `P : Prop` に対して、その命題を型とする項 `h : P` を
作ることが、`P` の証明を与えることになる。だから、その項が型 `P` を持つかを
検査すれば、証明の検査になる。この対応を納得するのが `02_Forall.lean` の目標である。
まずこの章で関数の型を追い、次の `02_Forall.lean` で証明の例を読む。
-/

/-!
### 補足: `Nat` や `Bool` はどこから来たか——Prelude

`import` を1行も書いていないのに `Nat`・`Bool`・`+` が使えるのは、Lean が
起動時に **Prelude**——標準ライブラリの核——を自動で読み込んでいるからである。
この教材で「標準ライブラリ」と呼ぶものの実体はただの Lean のソースファイルで、
`Nat` も `Bool` も、[`03_InductiveTypes.lean` 1節](#sec-Intro1.inductive-types)・[`03_InductiveTypes.lean` 2節](#sec-Intro1.structures)で
自作する型とまったく同じ仕組みで定義されている。特別なのは
「最初から読み込まれている」ことだけである。
-/

/-!
### ✏ 練習

1. `#check Bool` と `#check Type 2` の表示を予想してから確かめよ。
2. `#check 3 < 5` と `#check 5 < 3` の表示をそれぞれ予想してから確かめよ。
   命題の真偽が異なっても、同じ型が付くことを説明せよ。
-/

/-!
## 2. def — 新しい項を定義する {#sec-Intro1.definitions}

    def 名前 : 型 := 項

と書くと、**項に新しい名前を付けて定義**できる。`:=` の右辺には、すでに使える項や、
それらを組み合わせた項を書く。定義した後は、左辺の名前自体を項として使える。
`def` 全体は、定義を導入するコマンドである。
-/

def x : Nat := 2

/-! -/

#check x

/-!
    x : Nat

「`x` という `Nat` 型の項を、`2` として定義した」と読む。型は注釈どおり `Nat`。
名前 `x` 自体が値を決めるのではなく、右辺の `2` が定義の中身を決めている。

定義した項は、それ自体また項として使える:
-/

def y : Nat := x

#check y

/-!
    y : Nat

項を扱うコマンドをあと2つ紹介する。`#eval` は項を**計算**して値を表示する:
-/

#eval x

/-!
    2

`#print` は、名前に付けられた**定義そのもの**を表示する:
-/

#print x

/-!
    def x : Nat :=
    2

さて、ここからが**この教材の最重要のテーマ**である。
Lean は `def` の宣言を受理する前に、**型検査**を行う。
`:=` の右の項が、コロンの右に指定した型を持つかを確かめる。
指定した型も手がかりとして使い、一致しなければ宣言を受理しない。

この教材では、項 `M` と型 `A` が与えられ、`M : A` が成り立つかを
確かめることを**型検査**という。項だけからその型を求めるのが**型の計算**で、
`#check` はこれを行う。読者がその計算を自分の手でなぞるのを**推測**と呼ぶ。
`def 名前 : 型 := 項` は、Lean に `項 : 型` の型検査を依頼する形である。

読む側の目線で言えば、次の定義の右辺には **`Nat` 型の項を期待**する:

    def bad : Nat := true
-/

/-!
    error: Type mismatch
      true
    has type
      Bool
    but is expected to have type
      Nat

`#check true` と同じく、`true` の型は `Bool`。
Infoview は、要求された `Nat` と合わないと報告している。
-/

/-!
### コメントと docstring

ソースには、Lean が読み飛ばす**コメント**を書き込める。

    def x : Nat := 2   -- `--` から行末まではコメント

    /- 複数行にわたる
       コメントはこう書く -/

この教材の地の文が入っている `/-! … -/` も、コメントの一種である。

もう1つ、宣言の直前に `/-- … -/` と書くと、**docstring**（その宣言の説明書き）になる:

    /-- 最初に定義した数。 -/
    def x : Nat := 2

docstring は直後の宣言に結び付けられ、エディタで名前にカーソルを乗せると、
型と一緒にこの説明がポップアップで表示される。以後のコードにも、
`--` のコメントや docstring で説明を添えていく。
-/

/-!
### ✏ 練習

1. `def z : Nat := 5` を自分で宣言し、`#check z`・`#eval z`・`#print z`
   の表示をそれぞれ予想してから確かめよ。
2. 本文の `def x : Nat := 2` が使える状態で、`def oops : Bool := x` は受理されるか。
   予想してから試し、エラーメッセージを本文の例と見比べよ。
   別のファイルで試す場合は、先に `def x : Nat := 2` を書くこと。
-/

/-!
## 3. 関数 {#sec-Intro1.functions}

集合 $A$・$B$ に対して写像全体の集合 $\mathrm{Map}(A, B)$ が定まるのと同様に、
型 `A`・`B` に対して「`A` から `B` への関数の型」`A → B` が定まる。
つまり矢印 `→` は、**2つの型から新しい型を1つ作る
操作**を表す記号であって、それ自体が具体的な関数を定めるのではない。
ただし集合の場合と違い、`A → B` は写像概念から**定義されたものではない**——
関数型は、これ以上さかのぼれない原始的な部品である。

### 記号の入力のしかた

VS Code の Lean 4 拡張では、`\to` の後に空白か Tab を押すと `→` を入力できる。
他の記号も **`\` から始まる略記**で入力する。**記号にマウスを乗せると打ち方を確認できる**。
以後も初出時に打ち方を添え、一覧を `03_InductiveTypes.lean` の付録に置く。

### fun 記法 — 関数を項として書く

関数そのもの（`A → B` 型の項）を書くには、`fun` という記法を使える。
`fun x => e` は「`x` を受け取って `e` を返す関数」であり、
**`=>` の右側の項 `e` を、関数の本体（body）と呼ぶ**。
この教材の表示設定では、出力中の `=>` が `↦` と表示される。同じ関数の書き方である。

この項の型は、次のように読む。引数に型を注釈して `fun (x : A) => e` と書けば、
`x` の型はその注釈から `A` と分かる。注釈を省略した場合も、関数全体に
期待されている型から分かることがある。次に、**`x : A` を前提として本体 `e` の型を
調べる**。そのもとで `e : B` ならば、`fun x => e` は関数型 `A → B` の項になる。

-/

def double : Nat → Nat := fun n => n + n

#check double

/-!
    double : Nat → Nat

表示された型は、注釈した `Nat → Nat` と一致している。
定義域の `Nat` が**外側から**伝わるので、型を書かなかった引数も `n : Nat` と決まる。
`fun (n : Nat) => n + n` と書いたのと同じである。
-/

/-!
### 先取り（詳しくは 05_MathematicalTools）: `+` の仕組み

本体の `+` は **notation（記法）**の仕組みで用意された記号で、ここでは自然数の足し算を表す。
この節の後半で、読み先の関数とその型を確認する。
型に応じて演算を選ぶ仕組みは、[`05_MathematicalTools.lean` 1節](#sec-Intro2.classes)で説明する。
-/

/-!
次に、**`n : Nat` を前提として、本体 `n + n` の型が `Nat` になるか**を検査する。
これが通るので、`fun n => n + n` は注釈どおり `Nat → Nat` 型の項になる。
[2節](#sec-Intro1.definitions)と同じく、この照合を経て `def` が受理される。

一致しなければ、もちろん受理されない。本体を `true` にしてみる:

    def bad2 : Nat → Nat := fun n => true
-/

/-!
    error: Type mismatch
      true
    has type
      Bool
    but is expected to have type
      Nat

「本体 `true` の型 `Bool` が、注釈から要求される行き先の型 `Nat` と一致しない」
という報告である。
-/

/-!
### 適用の書き方

数学ではふつう `f(x)` と書く関数適用を、Lean では **`f x` と、関数と引数を
半角スペースで区切って**書く。項を書く場所で、関数を表す項のあとに引数の項を
このように並べると、関数適用として読まれる。例えば `double 21` である。
数学で「$f(x)$」と書くとき、私たちは $f$ が関数で $x$ がその定義域の元であることを
前提している。Lean の `f x` も同じ約束の記法で、
**`f` が関数型を持ち、`x` がその定義域の型を持つこと**を要求する。

実際 `double 21` と書くと、Lean は2つのことを確かめる:

1. `double` の型は `Nat → Nat`（関数型である）——定義域は `Nat`
2. `21` の型は `Nat`——定義域と一致する

この2点が通るから `double 21` は**合法な書き方**であり、
項 `double 21` の型は矢印の右側の `Nat` になる。
この確認こそが、型検査という機能の中身である。
一方、`double true` は `true : Bool` が定義域 `Nat` と合わないので、型エラーになる。
-/

#check double 21

/-!
    double 21 : Nat

型が分かったところで、値も予想してから計算してみよう。`21 + 21` なので `42` のはずだ:
-/

#eval double 21

/-!
    42

一方、`double true` を調べると、引数の型が合わずエラーになる:

    #check double true
-/

/-!
    error: Application type mismatch: The argument
      true
    has type
      Bool
    but is expected to have type
      Nat
    in the application
      double true
-/

/-!
### ✏ 練習

1. 関数 $\mathrm{inc} : \mathbb{N} \to \mathbb{N}$ を $\mathrm{inc}(n) = n + 1$ で定める。これを `fun` を用いて Lean で定義せよ。
   `#check inc` の型と `#eval inc 4` の値を予想してから確かめよ。
2. 関数 $f : \mathbb{N} \to \mathbb{N}$ を $f(n) = 2n + 3$ で定める。これを `fun` を用いて Lean で定義せよ
   （掛け算は `*` と書く）。`#check f` の型と `#eval f 4` の値を予想してから確かめよ。
-/

/-!
### 表示の読み方: binder 形式

宣言には、引数を左に書く記法もある。次は上の `double` と同じものである:
-/

def double' (n : Nat) : Nat := n + n

#check double'

/-!
    double' (n : Nat) : Nat

表示が `double' (n : Nat) : Nat` となったことに注意。
これは「引数の列をコロンの左に並べ、最後に結果の型を書く」**binder 形式**の
表示で、`#check` が関数を表示するときの標準の形である。

    double  : Nat → Nat            （矢印形式）
    double' (n : Nat) : Nat        （binder 形式）

この2つは**同じ型の2通りの表示**である。宣言の書き方も同様に2通りあって
（`def double : Nat → Nat := fun n => …` と `def double' (n : Nat) : Nat := …`）、
どちらで書いても同じものが定義される。以後どちらの表示も出てくるので、
読み替えられるようにしておくこと。
-/

/-!
### ✏ 練習

1. 関数 $\mathrm{triple} : \mathbb{N} \to \mathbb{N}$、$\mathrm{triple}(n) = n + n + n$ を binder 形式で定義せよ。
   `#check triple` の表示を予想してから確かめよ。
2. `#eval double (double 5)` の値を予想してから実行せよ。
3. 先ほどの $\mathrm{inc}(n) = n + 1$ を、今度は binder 形式で `inc'` という名前で定義せよ。
   `#check inc'` の表示と `#eval inc' 4` の値を予想して確かめ、`inc` と比較せよ。
4. 同様に $f(n) = 2n + 3$ を、binder 形式で `f'` という名前で定義せよ。
   `#check f'` の表示と `#eval f' 4` の値を予想して確かめ、`f` と比較せよ。
-/

/-!
### 多変数関数はカリー化で表す

まず、ふつうの数学の話から始めよう。集合 $X$・$Y$・$Z$ に対して、写像全体の集合には
次の自然な1対1対応がある:

$$\mathrm{Map}(X \times Y, Z) \cong \mathrm{Map}(X, \mathrm{Map}(Y, Z))$$

左辺の写像 $f$ に、$x$ を固定して得られる写像「$y \mapsto f(x, y)$」を対応させる。
つまり $x \mapsto (y \mapsto f(x, y))$ という右辺の写像にする。この操作を**カリー化（currying）**、
逆に右辺の写像 $g$ から $(x, y) \mapsto g(x)(y)$ を作る操作を**アンカリー化（uncurrying）**と呼ぶ。

Lean では、多変数関数も1引数関数を重ねて表す。
2引数なら、1つ目を受け取って**残り1引数の関数を返す**。
例えば、数学でいう写像 $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$、$(a, b) \mapsto a + b$ をカリー化したものを、
`plus : Nat → Nat → Nat` として定義してみよう:
-/

def plus : Nat → Nat → Nat := fun a => fun b => a + b

/-!
読み方の約束を先に押さえる。`→` は**右結合**である:

    Nat → Nat → Nat　は　Nat → (Nat → Nat)　のこと

（「`Nat` を受け取って、関数 `Nat → Nat` を返す」）。

逆に、適用は**左結合**:

    plus 3 4　は　(plus 3) 4　のこと

（まず `plus 3` で関数を作り、それに `4` を渡す）。
この2つの約束がかみ合っているおかげで、カリー化された関数を
括弧なしで自然に読み書きできる。

括弧を左側に付けた `(Nat → Nat) → Nat` は**まったく別の型**
（関数を受け取る関数）になることに注意。

`plus` 自体の型は注釈のとおり:
-/

#check plus

/-!
    plus : Nat → Nat → Nat

では、**`plus 3` の型は何か**。表示を見る前に推測しよう。
`plus` の型を右結合で読めば `Nat → (Nat → Nat)`——定義域は `Nat`、
行き先は `Nat → Nat`。そこに `3 : Nat` を渡すのだから、適用の2点確認より
`plus 3 : Nat → Nat` のはずである:
-/

#check plus 3

/-!
    plus 3 : Nat → Nat

推測どおり。「1つ渡すと、残り1引数の関数が返る」ことが型にそのまま現れている。

もう1つ渡せば `Nat` になるはずで:
-/

#check plus 3 4

/-!
    plus 3 4 : Nat
-/

#eval plus 3 4

/-!
    7
-/

/-!
### ✏ 練習

1. 関数 $\mathrm{addThree} : \mathbb{N} \to \mathbb{N}$、$\mathrm{addThree}(n) = 3 + n$ を、`plus 3 : Nat → Nat` を使って
   Lean で定義せよ。`#check addThree` と `#eval addThree 4` の表示を予想してから確かめよ。
2. 関数 $g : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$、$g(a, b) = 2a + 3b$ を、カリー化して Lean で定義せよ。
   型は `Nat → Nat → Nat` とし、`fun a => fun b => …` を使うこと。
   `#check g`・`#check g 2` の型と `#eval g 2 4` の値を予想してから確かめよ。
-/

/-!
### 多変数関数の binder 形式

1変数のときと同じく、引数を宣言の左側に並べられる。例えば `plus` は
次のようにも定義できる（同じ名前を重ねて定義せず、いずれか1つを使う）:

    def plus (a : Nat) (b : Nat) : Nat := a + b

**同じ型の引数は、まとめて** `(a b : Nat)` と書いてもよい:

    def plus (a b : Nat) : Nat := a + b

`fun` の引数もまとめられる。次も、もとの定義と同じ関数を表す:

    def plus : Nat → Nat → Nat := fun a b => a + b

-/

/-!
### ✏ 練習

1. 先ほどの $g(a, b) = 2a + 3b$ を、binder 形式で2通りに書け。
   `g'` は `(a : Nat) (b : Nat)` と分け、`g''` は `(a b : Nat)` とまとめること。
   `#check g'`・`#check g''` の表示と、`#eval g' 2 4`・`#eval g'' 2 4` の値を
   予想してから確かめよ。
-/

/--
3引数以上も同じことの繰り返し。
`Nat → Nat → Nat → Nat` は `Nat → (Nat → (Nat → Nat))` と読む。
-/

def addMul (a b c : Nat) : Nat := a + b * c

#check addMul

/-!
    addMul (a b c : Nat) : Nat

これは `Nat` 型の引数を3つ受け取って `Nat` 型の項を返す、という binder 形式の表示である。
矢印形式では `addMul : Nat → Nat → Nat → Nat` と読める。
-/

/-!
### 関数を引数として受け取る

数学でいう写像 $\mathrm{Map}(\mathbb{N}, \mathbb{N}) \to \mathbb{N}$、$F \mapsto F(21)$ を Lean で定義してみよう。
引数 `F` の型は、数の型 `Nat` ではなく関数型 `Nat → Nat` になる:
-/

def applyTo21 (F : Nat → Nat) : Nat := F 21

#check applyTo21

/-!
    applyTo21 (F : Nat → Nat) : Nat

`applyTo21 double` という項を読んでみよう。定義域は `Nat → Nat` で、
`double : Nat → Nat` がちょうど一致する——**関数そのものを引数として渡す**
適用であり、型は `Nat`。値は `double 21`、つまり `42` のはずである:
-/

#eval applyTo21 double

/-!
    42
-/

/-!
### 型の異なる引数の binder 形式

引数の型が異なる場合は、型ごとに括弧を分ける。$F(n)$ を返す関数なら、
`F : Nat → Nat` と `n : Nat` を別々に注釈する:
-/

def applyAt (F : Nat → Nat) (n : Nat) : Nat := F n
#check applyAt

/-!
    applyAt (F : Nat → Nat) (n : Nat) : Nat

矢印形式では `(Nat → Nat) → Nat → Nat` である。`F` を1つ渡すと、
残りの引数 `n : Nat` を受け取る関数が返る。`(F n : Nat)` とまとめてしまうと
両方が `Nat` 型という指定になるので、ここでは使えない。
-/

/-!
### ✏ 練習

1. 写像 $\mathrm{twice} : \mathrm{Map}(\mathbb{N}, \mathbb{N}) \to \mathrm{Map}(\mathbb{N}, \mathbb{N})$ を、$F \mapsto (n \mapsto F(F(n)))$ で定める。
   つまり、$F$ を同じ入力に2回使うのではなく、1回目の結果にもう一度 $F$ を適用する。
   これを Lean で `def twice (F : Nat → Nat) : Nat → Nat := …` と定義せよ。
   `#check twice`・`#check twice double` の表示と `#eval twice double 3` の値を
   予想してから確かめよ。
2. 写像 $\mathrm{thrice} : \mathrm{Map}(\mathbb{N}, \mathbb{N}) \to \mathrm{Map}(\mathbb{N}, \mathbb{N})$ を、$F \mapsto (n \mapsto F(F(F(n))))$ で定める。
   これを Lean で定義し、`#check thrice`・`#check thrice double` の表示と
   `#eval thrice double 3` の値を予想してから確かめよ。
-/

/-!
### 定義域や行き先が型でもよい

[1節](#sec-Intro1.terms-types)で見たように型も項なので、**型を受け取る関数・型を返す関数**も作れる。
例えば `Nat → Type` は、自然数を受け取って型を返す関数の型である。
ここでは2つの型 `A`・`B` を受け取り、関数型 `A → B` を返してみよう:
-/

def Map : Type → Type → Type := fun A B => A → B

#check Map

/-!
    Map : Type → Type → Type

数学の $\mathrm{Map}(A, B)$ に対応する関数型を返す操作を、Lean の項 `Map` として定義した。
`Map Nat Nat` は計算すると `Nat → Nat` なので、`double` はその項でもある（直後の練習で確かめよう）。
型を扱う関数は、[4節](#sec-Intro1.dependent-functions)でも使う。
-/

/-!
### ✏ 練習

1. `#check Map Nat Bool` の表示を予想してから確かめよ。また、数学でいう
   関数 $\mathrm{double} : \mathbb{N} \to \mathbb{N}$、$\mathrm{double}(n) = n + n$ を、`Map Nat Nat` 型の項としても使えるか考えよ。
   `def double2 : Map Nat Nat := double` が受理されるか予想してから試せ。
   受理されたら、`#check double2` の表示も予想してから確かめよ。
2. `#check Map Nat` の表示を予想してから確かめよ
   （`Map` に1つだけ渡すと、何が返るか。`plus 3` の型を読んだのと同じ手順で考える）。
-/

/-!
### `+` をあらためて

カリー化を知ったいま、自然数の足し算を表す関数の型は `Nat → Nat → Nat` と読める。
`3 + 4` も、2引数の関数適用を中置の記法で書いたものと考えればよい。
ここまで使ってきた自然数の掛け算も同様に、`Nat → Nat → Nat` 型の関数である。
-/

/-!
CALLOUT_START preview
-/

/-!
### 先取り（詳しくは 05_MathematicalTools）: `Nat.add` と `HAdd.hAdd`

自然数の足し算そのものは `Nat.add` という名前で定義されている。
自然数を2つ受け取って自然数を返すので、型は `Nat → Nat → Nat` のはずである:
-/

#check Nat.add

/-!
    Nat.add : Nat → Nat → Nat

一方、記法 `a + b` の読み先は `HAdd.hAdd a b` である。
`HAdd` は型に応じた足し算を指定するための **class（クラス）**、
`HAdd.hAdd` はそこで指定された足し算を使う関数である。
これを自然数2つから自然数を返す関数として使ってみよう。
次の括弧内の `: Nat → Nat → Nat` は、その型を指定する注釈である:
-/

#check (HAdd.hAdd : Nat → Nat → Nat)

/-!
    HAdd.hAdd : Nat → Nat → Nat

Lean は指定された型に合う **instance（インスタンス）**を自動的に補う。
標準環境では、同じ型どうしの足し算を指定する `Add` というクラスを経由して、
`Nat.add` が使われる。このつながりは標準ライブラリの定義によるものであり、
上の2つの型が同じだから、という理由ではない。同じ型の関数でも中身は異なり得る。

ここでは「`+` は記法で、型に応じて演算が選ばれ、自然数では `Nat.add` が使われる」
と押さえておけばよい。ここでは `HAdd.hAdd` の一般的な型には立ち入らない。
クラスやインスタンスの定義・選択の仕組みは、[`05_MathematicalTools.lean` 1節](#sec-Intro2.classes)で扱う。
数字も型に応じて解釈される記法であり、その仕組みは `OfNat` というクラスが担う
（[`05_MathematicalTools.lean` 1節](#sec-Intro2.classes)の補足で見る）。
今は、ほかの型の指定がなければ `3` などを `Nat` の項として読めばよい。
-/

/-!
CALLOUT_END
-/

/-!
### 型はどう決まるか——下から計算し、上から期待を伝える

[2節](#sec-Intro1.definitions)で「型検査が走る」と述べ、この節の冒頭で `double 21` の2点確認を見た。
一般の形をまとめておく。適用についての規則はただ1つである:

    f : A → B　かつ　a : A　ならば　f a : B

この規則は、**適用が合法かどうかの検査**でもある。`f` が関数型 `A → B` を持ち、
引数 `a` の型が定義域 `A` と一致するときに、適用 `f a` が認められ、結果の型 `B` が分かる。

`A`・`B` 自体が関数型でも同じである。`applyTo21 double` なら、
`A = Nat → Nat`、`B = Nat`。引数 `double` の型が `A` と一致し、結果は `Nat` 型になる。
行き先 `B` が関数型になる例が `plus 3` である。

例えば `double (plus 3 4)` なら:

1. `3 : Nat`、`4 : Nat`
2. `plus : Nat → (Nat → Nat)`（宣言された型）
3. `plus 3`：`3 : Nat` が定義域と一致 → `Nat → Nat`
4. `(plus 3) 4`：`4 : Nat` が定義域と一致 → `Nat`
5. `double (plus 3 4)`：`plus 3 4 : Nat` が定義域と一致 → `Nat`

どの段階でも、見ているのは**直下の部分項の型と規則1つだけ**である。
各照合が通るときにだけ全体に型が付き、その書き方が認められる。
この局所的な検査を項全体に再帰的に行うのが型検査で、項が大きくなっても手順は変わらない。

ここまでは、部分項の型から全体の型を求める**下から**の計算だった。
Lean は逆向きの情報も使う。項を置く場所で型が期待されていれば、その型を
部分項へ**上から**伝えて、読み方や省略された部分を決める。すでに2つ見ている:

* `def double : Nat → Nat := fun n => n + n` では、注釈 `Nat → Nat` が `fun` の
  引数へ伝わって `n : Nat` が決まった。
* [1節](#sec-Intro1.terms-types)で触れた数字も同じ仕組みで読まれる。
  何も期待されていなければ `2` は `Nat` の項として読まれるが、
  型注釈で `Int`（整数の型）を期待すると、`Int` の項として読まれる:
-/

#check 2

/-!
    2 : Nat
-/

#check (2 : Int)

/-!
    2 : Int

期待される型は部分項の奥まで伝わる。`(2 + 3 : Int)` なら、`2` と `3` も
`Int` の項として読まれ、全体の型は `Int` になる:
-/

#check (2 + 3 : Int)

/-!
    2 + 3 : Int

このあとの節でも、期待される型から構成子の名前を補う `.red`
（[`03_InductiveTypes.lean` 1節](#sec-Intro1.inductive-types)）や `⟨1, 2⟩`（[`03_InductiveTypes.lean` 2節](#sec-Intro1.structures)）、
暗黙引数の補完（[4節](#sec-Intro1.dependent-functions)）が出てくる。
どれもこの「上から伝える」仕組みの例である。

Lean は、この2つの向きを組み合わせて、書かれた文字列を1つの項として読み、
型検査を行う。`M : A` の型検査は、期待される型 `A` を上から伝えつつ
部分項の型を下から計算し、両者が出会うところで一致を確かめる作業である。

そして、どちらの向きの手順も**完全に機械的**で、ひらめきや解釈は要らない。
これを実行するのが Lean の型検査器であり、読者の「型の推測」は同じ手順を
自分の手でなぞることである。

この後の節で新しい項の作り方（`match`・依存関数など）を導入するたびに、
型の規則も増える。それでも、`#check` の表示は「宣言された型」と
「そこまでの規則」だけで、同じように自分の手で検算できる。

なお読むときの目印として、**項のあとにスペースを挟んで項が続いたら、
それは関数適用**である。`double (plus 3 4)` を見た瞬間に「`double` を
`plus 3 4` に適用している」と分解できる。
-/

#check double (plus 3 4)

/-!
    double (plus 3 4) : Nat
-/

/-!
照合が失敗すれば、その場所がエラーになる。`double` に関数 `plus` を渡してみる:

    #check double plus
-/

/-!
    error: Application type mismatch: The argument
      plus
    has type
      Nat → Nat → Nat
    but is expected to have type
      Nat
    in the application
      double plus

「引数の型 `Nat → Nat → Nat` が、要求される型 `Nat` と合わない」と、
規則が破れた部分項を名指しで教えてくれる。
エラーの下にはさらに `double sorry : Nat` という表示も出る。ここで初めて出てきた
**`sorry`** は、「この部分は未完成」という印の項で、どんな型の項の代わりにも置ける。
`#check` は、エラーになった引数を `sorry` で置き換えて、残りの部分の型の計算を
続けてくれたのである。自分で書くこともできる。例えば

    def later : Nat := sorry

は受理されるが、``warning: declaration uses `sorry` `` という警告が出る。
未完成のまま進めても、そのことを Lean は見逃さない。

では `double plus 3 4` と括弧なしで書いたらどうなるか。適用は左結合なので
これは `((double plus) 3) 4` と読まれ、最初の `double plus` の時点で
上と同じエラーになる。`double (plus 3 4)` の括弧は省略できない。
-/

/-!
### ✏ 練習

1. `#check` する**前に**型を計算せよ: `(3 + 4) * 2`、`plus (double 3)`、
   `applyTo21 (plus 3)`、`fun n : Nat => plus n n`。それから確かめよ。
2. `#eval applyTo21 (plus 100)` の値を予想してから実行せよ。
3. 次の2つの写像を Lean で定義し、`#check` の表示を予想してから確かめよ:
   * $\mathrm{evalAt} : \mathrm{Map}(\mathbb{N}, \mathbb{N}) \times \mathbb{N} \to \mathbb{N}$、$\mathrm{evalAt}(F, n) = F(n)$。カリー化して定義すること。
     `#eval evalAt double 5` の値も予想してから実行せよ。
   * $\mathrm{shift} : \mathrm{Map}(\mathbb{N}, \mathbb{N}) \to \mathrm{Map}(\mathbb{N}, \mathbb{N})$、$F \mapsto (n \mapsto F(n + 1))$。
     関数を受け取って**関数を返す**関数である。
     `#eval shift double 3` の値も予想してから実行せよ。
4. 「型から項を書く」練習: $\mathrm{Map}(\mathbb{N}, \mathbb{N}) \to \mathbb{N}$ という写像を、**中身の違うもので2つ**考えよ
   （例えば $F \mapsto F(21)$ と $F \mapsto 0$）。それらを Lean で `useF1`・`useF2` と名付けて定義し、
   型を予想してから `#check` で確かめよ。どちらも `(Nat → Nat) → Nat` 型になるはずである。
   同じ型に項は何通りもある——型は仕様であって、中身までは決めない。
5. （発展）写像 $G : B \to C$ と $F : A \to B$ に合成 $G \circ F : A \to C$ を対応させる写像を考える。
   型 $A$・$B$・$C$ も引数に取り、これを Lean で
   `compose (A B C : Type) (G : B → C) (F : A → B) : A → C` と定義せよ。
   `#check compose` の表示と、
   `#eval compose Nat Nat Nat double (fun n => n + 1) 3` の値を予想してから
   確かめよ。
6. （発展）`evalAt` と `shift` を一般化し、任意の $A$・$B$ に対する写像 $\mathrm{Map}(A, B) \times A \to B$、$(F, a) \mapsto F(a)$ と、
   写像 $g : A \to A$ に対する変換 $\mathrm{Map}(A, A) \to \mathrm{Map}(A, A)$、$F \mapsto (a \mapsto F(g(a)))$ を考える。
   型や $g$ も引数として受け取るように、Lean で
   `evalAt' (A B : Type) (F : A → B) (a : A) : B` と
   `shift' (A : Type) (g : A → A) (F : A → A) : A → A` を定義せよ。
   両者の `#check` の表示と、
   `#eval evalAt' Nat Nat double 5` と `#eval shift' Nat (fun x => x + 1) double 3`
   の値を予想してから確かめ、元の版と比較せよ。
-/

/-!
## 4. 依存関数型 — 入力によって結果の型が変わる {#sec-Intro1.dependent-functions}

まず集合族で考えよう。集合 $A$ を添字集合とする集合族 $(X_a)_{a \in A}$ に対して、
その直積 $\prod_{a \in A} X_a$ の要素は、各 $a$ に $X_a$ の要素を一つずつ指定するものである。
これを**依存関数**と思えばよい。値 $f(a)$ の所属先 $X_a$ が、入力 $a$ に依存している。

族が定数、つまりすべての $X_a$ が同じ集合 $X$ ならば、これは普通の関数 $A \to X$ であり、
$\prod_{a \in A} X = \mathrm{Map}(A, X)$ となる。

### 直和への関数と切断

族が定数でない場合も、直和 $E = \coprod_{a \in A} X_a$ を使えば、普通の関数として表せる。
この直和の要素は、添字と要素の組 $(a, x)$（$x \in X_a$）である。

依存関数 $f$ を $s(a) = (a, f(a))$ という関数 $s : A \to E$ に読み替える。
射影 $\pi : E \to A$、$\pi(a, x) = a$ に対して、これは
$\pi \circ s = \mathrm{id}_A$ を満たす。このような $s$ を $\pi$ の**切断（section）**と呼ぶ。

逆に、全射 $F : E \to A$ の切断 $s$ を考えてもよい。$F \circ s = \mathrm{id}_A$ という条件は、
各 $a$ について $s(a) \in F^{-1}(a)$ という条件である。したがって切断とは、
ファイバーを集合族 $(F^{-1}(a))_{a \in A}$ と見たときの依存関数である。

### 型の族と依存関数

Lean では、`B : A → Type` が各 `a : A` に型 `B a` を割り当てる**型の族**を表す。
この族の各型から項を一つずつ返す関数の型を**依存関数型**といい、次のように書く:

    (a : A) → B a

集合族の直積 $\prod_{a \in A} B(a)$ に対応する型である。
族 `B` の行き先はいつも `Type` だが、依存関数の結果の型 `B a` は入力 `a` に応じて変わる。
結果の型が入力に依存しない特別な場合が、これまでの `A → C` である。

### 各集合に恒等写像を割り当てる

数学の例として、ある範囲の集合を集めた $\mathcal{U}$ を考える。
各 $X \in \mathcal{U}$ に集合 $\mathrm{Map}(X, X)$ を対応させると、これも集合族になる。
その中から恒等写像 $\mathrm{id}_X \in \mathrm{Map}(X, X)$ を選ぶのが、依存関数の例である。

直和への関数で書けば、$X \mapsto (X, \mathrm{id}_X)$ という関数
$\mathcal{U} \to \coprod_{X \in \mathcal{U}} \mathrm{Map}(X, X)$ である。
これは添字 $X$ への射影の切断になっている。
Lean でも、各型 `α` に恒等関数という `α → α` 型の項を割り当ててみよう。
-/

/-!
次の `idAt` は、どんな型の上でも使える恒等写像である。第1引数として
**型そのもの**を受け取り、第2引数と結果の型が、その第1引数で決まる:
-/

def idAt (α : Type) (a : α) : α := a

#check idAt

/-!
    idAt (α : Type) (a : α) : α

では、**`idAt Nat` の型は何か**。第1引数として `α := Nat` を渡したのだから、
残りは「`Nat` を受け取って `Nat` を返す」——`Nat → Nat` のはずである:
-/

#check idAt Nat

/-!
    idAt Nat : Nat → Nat

推測どおり。同じ理屈で、`idAt Bool` なら `Bool → Bool` になるはず:
-/

#check idAt Bool

/-!
    idAt Bool : Bool → Bool
-/

#eval idAt Nat 42

/-!
    42

（この行にも型検査が走っている: `idAt Nat : Nat → Nat` に `42 : Nat` を
渡すのは合法、というおなじみの2点確認である。）
-/

/-!
`idAt Nat` と `idAt Bool` は**型が違う**。つまり `idAt` に1つ引数を渡すと、
「残りの型」がその引数の値で決まる。こうなるともう `A → B` の形では書けない。
この形の関数の型を**依存関数型**といい、

    idAt : (α : Type) → α → α

と書く（束縛した名前 `α` が矢印の右側に現れるのが目印）。これが Lean の
関数型の一般形で、`A → B` は「行き先が入力に依存しない特別な場合」の略記である。
-/

/-!
### 数を添字にする型の族

依存する入力は、型そのものでなくてもよい。自然数 $n$ ごとに「自然数の $n$ 個組の型」を
考えよう。数学では $\mathbb{N}^n$ を、$n$ 点集合から $\mathbb{N}$ への写像全体として表せる。

まず、標準環境の `Fin` 自体の型を調べよう。
-/

#check Fin

/-!
    Fin (n : Nat) : Type

binder 形式を読み替えると `Fin : Nat → Type`。`Fin` 自体は、自然数を受け取って
型を返す**普通の関数**であり、自然数を添字とする型の族を与える。

`Fin n` は、集合 $\{0, 1, \ldots, n-1\}$ に対応する型と思ってよい
（`Fin 0` には要素がない）。正確には、0 以上 n 未満の値と、その範囲に入る証明を組にする。
この見方は、[`03_InductiveTypes.lean` の2節](#sec-Intro1.subtypes)で部分型（サブタイプ）として説明する。
-/

def Tuple : Nat → Type := fun n => Fin n → Nat

#check Tuple

/-!
    Tuple : Nat → Type
-/

#check Tuple 3

/-!
    Tuple 3 : Type

`Tuple 3` は、定義を展開すると `Fin 3 → Nat` である。
三つの番号にそれぞれ自然数を割り当てる関数を、自然数の3個組と読む。
`Tuple` 自身は、自然数を受け取って型を返す**普通の関数**である。

では、各 n について、すべての成分が7である n 個組を作ってみよう。
**型の族 `Tuple` に対する依存関数**になるのが、次の `constTuple` である。
-/

def constTuple : (n : Nat) → Tuple n :=
  fun n => fun (_i : Fin n) => 7

#check constTuple

/-!
    constTuple (n : Nat) : Tuple n

外側の `fun` は個数 `n : Nat` を受け取る。すると作るべき型は `Tuple n`、
つまり `Fin n → Nat` に決まる。内側の `fun` は番号 `_i : Fin n` を受け取り、7を返す。
番号そのものを計算に使わなくても、受け取れる番号の**型**は n によって変わる。
`_i` のように名前を `_` で始めるのは、値を使わない引数であることを示す書き方である。
-/

#check constTuple 3

/-!
    constTuple 3 : Tuple 3
-/

#check constTuple 4

/-!
    constTuple 4 : Tuple 4

`Tuple` は型を返し、`constTuple` は**その型の項を返す**。この違いを区別しよう。
`constTuple 3` は3個組、`constTuple 4` は4個組であり、結果の型が違う。

### 数を返す依存関数の例

もう一つ、各 n について集合 $\{0, 1, \ldots, n\}$ の要素 0 を選ぶ例を考えよう。
所属先の型は `Fin (n + 1)` なので、これも依存関数になる:
-/

def zeroIndex : (n : Nat) → Fin (n + 1) := fun _ => 0

#check zeroIndex

/-!
    zeroIndex (n : Nat) : Fin (n + 1)

返す番号はいつも 0 でも、**結果の型が入力に依存**している:
-/

#check zeroIndex 2

/-!
    zeroIndex 2 : Fin (2 + 1)
-/

#check zeroIndex 4

/-!
    zeroIndex 4 : Fin (4 + 1)

前者は3点の型、後者は5点の型の要素である。`Fin` が型の族を与え、
`zeroIndex` はその族の `Fin (n + 1)` に属する項を返している。
0 がこの型の項として使える仕組みは、部分型を扱うときに見る。

### 依存する適用の規則

冒頭の一般形 `(a : A) → B a` に戻ろう。
`idAt` では `A = Type`、`B α = α → α`、
`constTuple` では `A = Nat`、`B = Tuple`、
`zeroIndex` では `A = Nat`、`B n = Fin (n + 1)` と読める。

適用の規則も、それに合わせて一般化される:

    f : (a : A) → B a    x : A
    -------------------------
             f x : B x

入力の型が合うかを確かめたうえで、結果の型の中の `a` にも実引数 `x` を入れる。
`constTuple 3` の型が `Tuple 3` になったのは、この代入である。
結果の型が入力によらない場合が、これまでの `A → C` である。

-/

/-!
### ✏ 練習

1. `#check idAt (Nat → Nat)` の表示と、`#eval idAt (Nat → Nat) double 21` の値を予想せよ。
2. 集合 A の要素 a に対して、集合 B 上の定数写像を対応させる
   `constAt (A B : Type) (a : A) : B → A` を書け。
   `#check constAt Nat Bool 5` と `#eval constAt Nat Bool 5 true` を確かめよ。

3. `Tuple 2` を定義で展開すると、どんな型になるか。
   `constTuple 2` の内側の引数と結果の型を答えよ。
4. n と自然数 a を受け取り、すべての成分が a である n 個組を返す
   `repeatTuple (n : Nat) (a : Nat) : Tuple n` を書け。
-/

/-!
### 型引数を補ってもらう — 明示引数と暗黙引数

`idAt Nat 3` では型 `Nat` を明示した。しかし、渡す項3の型からも `Nat` が分かる。
型引数を `{ }` で宣言すると、Lean にその引数を補ってもらえる。
-/

def idImplicit {α : Type} (a : α) : α := a

#check idImplicit

/-!
    idImplicit {α : Type} (a : α) : α

`(a : α)` は**明示引数**で、呼び出す側が渡す。`{α : Type}` は**暗黙引数**で、
ほかの引数の型や、結果に期待される型を手がかりに Lean が補う。
依存関数そのものの仕組みは変わらず、型引数を誰が指定するかが変わったのである。
-/

#check idImplicit 3

/-!
    idImplicit 3 : Nat
-/

#check idImplicit true

/-!
    idImplicit true : Bool

省略を補う前処理は**エラボレーション**と呼ぶ。暗黙引数は、その後の型の照合では
ほかの引数と同じように扱われる。手がかりが足りなければ補えない場合もある。
結果の型を注釈して補う例は、[`03_InductiveTypes.lean` の1節](#sec-Intro1.inductive-types)で見る。
括弧 `[ ]` は `05_MathematicalTools.lean` の class とともに説明する。

省略した引数など未確定の部分は、出力では `_` や `?m.…` と表示されることがある。
項を書く位置に自分で `_` を置くと、Lean にその部分の補完を求められる。
`fun _ => …` の `_` は別の用法で、受け取る引数に名前を付けないという意味である。
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: ライブラリにもある型の族

標準環境の `Vector Nat n` は、長さが n と決まった自然数の列の型である。
`Vector Nat : Nat → Type` は、`Tuple` と同じ形の族である。
-/

#check Vector Nat 3

/-!
    Vector Nat 3 : Type

同じ値を指定回数並べる関数が `Vector.replicate` である。
自然数の列を作る場合、その型は次の形として読める:

    (n : Nat) → Nat → Vector Nat n

一般には要素の型 α を暗黙引数に持ち、並べる値0の型 `Nat` から α が決まる。
-/

def zeros : (n : Nat) → Vector Nat n := fun n => Vector.replicate n 0

#check zeros 3

/-!
    zeros 3 : Vector Nat 3
-/

#check zeros 4

/-!
    zeros 4 : Vector Nat 4

ここでは型の変化を確かめればよい。列の内部の構造や表示方法は必要ない。
-/

/-!
CALLOUT_END
-/

/-!
このあと命題の族 `Q : A → Prop` に移ると、「各 a について `Q a` の証明を返す」
依存関数が全称命題の証明になる。次の `02_Forall.lean` では、この対応を実際の証明で読む。
-/
