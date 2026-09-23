/-!
# Lean 最小限の導入 I — 型と項の言語

このファイル（Intro1）は、主に**目標1**を担当する。

このファイルで伝えたいことは2つ。

* Lean のもっとも基本の要素は**項**と**型**である。
  Lean に書くことはすべて「項 `a` は型 `α` を持つ」（`a : α` と書く）の組み立てである。
* 型を作る部品は実質2つ、**帰納型**（inductive type）と
  **依存関数型**（dependent function type）である。

なお、このファイルは**型の世界**に集中する。命題と証明の世界は、
[1節](#sec-Intro1.terms-types)で顔だけ見せたあとは極力持ち込まず、`CH.lean` でまとめて扱う。

### この教材の読み方

中心的な練習は、**書かれたコードを解読すること**である。その基本動作が
「与えられた項の型を推測する」こと。そこで以後、項を書くたびに
「この項の型はこうなるはずだ」とまず推測し、`#check` で答え合わせをする、
というプロセスを繰り返す。読者も、出力の枠を読む前にいったん止まって、
自分の推測を立ててから確かめてほしい。この積み重ねの先で、
同じ仕組みがそのまま証明の検証になる（目標2、`CH.lean`）。

各節末の ✏ 練習も、**書いた項に、自分が予想した型が付くかどうかを、
機械に答え合わせさせる**ためのものである。
-/

/-! ## 1. 項と型 {#sec-Intro1.terms-types}

Lean に書くものの基本の単位を**項**（term）と呼ぶ。項とは何かの正確な定義は
ここでは与えないが、さしあたり **`#check` の右側に書いてエラーが出ないものは
項だと考えてよい**。

型（type）は、ひとまず**集合のようなもの**、その型の項は**要素のようなもの**と
考えてよい。ただし、集合を公理に従って扱うのと同様に、型や項にも、それらを
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
（この命名と省略の仕組みは[4節](#sec-Intro1.inductive-types)で見る）。

すべての項はちょうど1つの型を持つ（厳密には、定義から計算して一致する型を
同一視する、などの但し書きが要るが、この教材の範囲では「ちょうど1つ」と
考えて差し支えない）。ただし、数字の `2` のような**記法**は、書いた文字列の
段階ではまだどの型の項か決まっておらず、置かれた場所で期待される型に応じて
`Nat` の `2` とも `Int` の `2` とも読まれる。読み方が決まった項には、
型がちょうど1つ付く（この「読み方の決まり方」は[3節](#sec-Intro1.functions)で扱う）。ここで大事な観察が1つある。
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

/-! CALLOUT_START optional -/
/-! ### 補足（初読は飛ばしてよい）: 宇宙の階段 -/

#check Type 1

/-!
    Type 1 : Type 2

`Type`, `Type 1`, `Type 2`, … の階層を宇宙（universe）と呼ぶ。
この教材では宇宙には**深入りしない**。
-/

/-! CALLOUT_END -/

/-!
型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（[3節](#sec-Intro1.functions)の `Map` と[6節](#sec-Intro1.dependent-functions)）。

数の演算や、等式・不等式も項として書ける。それぞれにどんな型が付くかを見てみよう。
-/

#check 3 + 4

/-!
    3 + 4 : Nat

「`3 + 4` という項は `Nat` 型を持つ」——数から作った式は、また数の項になる。
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
`#check` は命題の真偽を判定しているわけではない（証明の話は `CH.lean` で扱う）。

`Prop` 自身の型も調べてみよう:
-/

#check Prop

/-!
    Prop : Type

`Prop` 自身もまた項であり、その型は `Type` である。
-/

/-! CALLOUT_START preview -/
/-! ### 先取り（[3節](#sec-Intro1.functions)・CH）: 演算と命題の記号の定義

`+`・`=`・`<` が正確には何を表し、どのように定義されているかは後で説明する。
`+` は[3節](#sec-Intro1.functions)で関数として読み、型に応じて演算を選ぶ仕組みは
[`Intro2.lean` 1節](#sec-Intro2.classes)で扱う。`=` と `<` は
[`CH.lean` 1節](#sec-CH.propositions)で説明する。今は、それぞれの項にどんな型が
付くかを追えばよい。
-/

/-! CALLOUT_END -/

/-!
ここまでで確かめたことは2つである:
**項の型はいつでも `#check` で調べられる**こと、そして**型も項である**こと。

`#check` という機能があることから分かるように、Lean には**項を与えると、その型を
機械的に計算する仕組み**がある。この仕組みを証明の検証に使うのが、冒頭で述べた
この教材の行き先である。命題 `P : Prop` に対して、その命題を型とする項 `h : P` を
作ることが、`P` の証明を与えることになる。だから、その項が型 `P` を持つかを
検査すれば、証明の検査になる。この対応を納得するのが `CH.lean` の目標である。
以下の先取りでは、具体例を1つだけ見ておく。
-/

/-! CALLOUT_START preview -/
/-! ### 先取り（CH）: 型の推測が証明の検証になる

最後に、この教材の行き先を、例を1つだけ挙げて予告しておく。
次の項は `fun`（関数を作る記法、[3節](#sec-Intro1.functions)）で書かれている。読み方だけ添えると、
`p q r : Prop` は3つの命題、`hpq : p → q` は「`p` ならば `q`」の証明、
`hp : p` は `p` の証明である。細部はまだ追わなくてよい。
**項全体の型はどこにも書いていない**のに、Lean がどんな型を付けるかを見てみよう:
-/

#check fun (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) => hqr (hpq hp)

/-!
    fun p q r hpq hqr hp ↦ hqr (hpq hp) : ∀ (p q r : Prop), (p → q) → (q → r) → p → r

（書くときの `=>` が、表示では `↦` に変わっている。このプロジェクトの
表示設定によるもので、同じものである。以後もこの流儀で引用する。）

計算された型を読んでみると——「任意の命題 `p`, `q`, `r` について、
`p` ならば `q`、`q` ならば `r` が成り立つなら、`p` ならば `r`」。
**含意の推移律**という定理の主張である。つまり、いま書いた項はこの定理の
**証明**であり、機械が型を計算できたということは、この証明を
**検証できた**ということなのである。

本体 `hqr (hpq hp)` では、証明がふつうの関数と同じように適用されている:
`hpq` に `p` の証明 `hp` を渡して `q` の証明を作り、それを `hqr` に渡して
`r` の証明を作る。「含意の証明は関数であり、仮定を使うことは関数適用である」
——この対応の種明かしが `CH.lean` である。

次の節からは、この「型の推測」を自分の手でできるようになるための道具立てを、
順に説明していく。
-/

/-! CALLOUT_END -/

/-! ### 補足（初読は飛ばしてよい）: `Nat` や `Bool` はどこから来たか——Prelude

`import` を1行も書いていないのに `Nat`・`Bool`・`+` が使えるのは、Lean が
起動時に **Prelude**——標準ライブラリの核——を自動で読み込んでいるからである。
この教材で「標準ライブラリ」と呼ぶものの実体はただの Lean のソースファイルで、
`Nat` も `Bool` も、[4節](#sec-Intro1.inductive-types)・[5節](#sec-Intro1.structures)で
自作する型とまったく同じ仕組みで定義されている。特別なのは
「最初から読み込まれている」ことだけである。
-/

/-! ### ✏ 練習

1. `#check Bool` と `#check Type 2` の表示を予想してから確かめよ。
2. `#check 3 < 5` と `#check 5 < 3` の表示をそれぞれ予想してから確かめよ。
   命題の真偽が異なっても、同じ型が付くことを説明せよ。
-/

/-! ## 2. def — 新しい項を定義する {#sec-Intro1.definitions}

    def 名前 : 型 := 項

と書くと、**項に新しい名前を付けて定義**できる。`:=` の右辺には、すでに使える項や、
それらを組み合わせた項を書く。左辺の「名前」は、これから導入する新しい項の名前である。
定義した後は、その名前自体を項として使える。`def` 全体は、その定義を導入する
コマンドである。
-/

def x : Nat := 2

#check x

/-!
    x : Nat

「`x` という `Nat` 型の項を、`2` として定義した」——宣言に `: Nat` と
書いたのだから型は `Nat` のはずで、表示もそのとおりである。
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
`def` の宣言を受理する前に、Lean は**型検査**を行っている:
`#check` と同じ、項の型を調べる仕組みを使って、`:=` の右に書いた項が
コロンの右に指定した型を持つかを確かめる。指定した型も手がかりとして使われる。
右辺の項の型が指定と合わなければ、宣言は受理されない。

この教材では言葉を次のように使い分ける。項 `M` と型 `A` が与えられて、
`M : A` が成り立つかを確かめることを**型検査**という。項だけが与えられて、
その型を求めることを**型の計算**という（`#check` がしているのはこちら）。
読者が「この項の型はこうなるはず」と考えるのは、型の計算を自分の手で
なぞる**推測**である。`def 名前 : 型 := 項` は、Lean に `項 : 型` の型検査を
依頼する形になっている。

読む側の目線で言えば、`def bad : Nat :=` まで読んだ時点で、
「この先には `Nat` 型の項が来るはずだ」という**期待**が立つ。例えば

    def bad : Nat := true

と書くと、`true` はその期待に合わないので、Infoview には次のエラーが表示される:

    error: Type mismatch
      true
    has type
      Bool
    but is expected to have type
      Nat

`#check true` で調べたときと同じく、右辺の `true` の型は `Bool` と分かる。
「その型が、要求されている型 `Nat` と一致しない」という報告である。
-/

/-! ### コメントと docstring

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

/-! ### ✏ 練習

1. `def z : Nat := 5` を自分で宣言し、`#check z`・`#eval z`・`#print z`
   の表示をそれぞれ予想してから確かめよ。
2. 本文の `def x : Nat := 2` が使える状態で、`def oops : Bool := x` は受理されるか。
   予想してから試し、エラーメッセージを本文の例と見比べよ。
   別のファイルで試す場合は、先に `def x : Nat := 2` を書くこと。
-/

/-! ## 3. 関数 {#sec-Intro1.functions}

集合 A・B に対して写像全体の集合 Map(A, B) が定まるのと同様に、
型 `A`・`B` に対して「`A` から `B` への関数の型」`A → B` が定まる。
つまり矢印 `→` は、**2つの型から新しい型を1つ作る
操作**を表す記号であって、それ自体が具体的な関数を定めるのではない。
ただし集合の場合と違い、`A → B` は写像概念から**定義されたものではない**——
関数型は、これ以上さかのぼれない原始的な部品である。

### 記号の入力のしかた

矢印 `→` を入力するには、VS Code の Lean 4 拡張で `\to` と打ち、
続けて空白を打つか Tab を押す。このように、**バックスラッシュ `\` で始まる略記**で
記号を入力できる。以後も記号の初出時に打ち方を添え、まとめの表をこのファイルの
末尾に置く。**エディタ上の記号にマウスを乗せると打ち方がポップアップに表示される**
ので、出会った記号はホバーで確かめてもよい。

### fun 記法 — 関数を項として書く

関数そのもの（`A → B` 型の項）を書くには、`fun` という記法を使える。
`fun x => e` は「`x` を受け取って `e` を返す関数」であり、
**`=>` の右側の項 `e` を、関数の本体（body）と呼ぶ**。

この項の型は、次のように読む。引数に型を注釈して `fun (x : A) => e` と書けば、
`x` の型はその注釈から `A` と分かる。注釈を省略した場合も、関数全体に
期待されている型から分かることがある。次に、**`x : A` を前提として本体 `e` の型を
調べる**。そのもとで `e : B` ならば、`fun x => e` は関数型 `A → B` の項になる。

名前を付けて定義してみる:
-/

def double : Nat → Nat := fun n => n + n

#check double

/-!
    double : Nat → Nat

表示された型は、注釈した `Nat → Nat` と一致している。
`fun n => n + n` の `n` には型を書いていないが、注釈 `Nat → Nat` の
定義域から `n : Nat` と決まっている——注釈した型が、**外側から** `fun` の引数へ
伝わっているのである（`fun (n : Nat) => n + n` と書いたのと同じ）。さらに、**`n : Nat` を前提として使うことで、本体 `n + n` も
`Nat` 型だと分かる**。この2段階から、関数全体の型が `Nat → Nat` になる。
-/

/-! ### 先取り（詳しくは Intro2）: `+` の仕組み

本体の `+` は **notation（記法）**の仕組みで用意された記号で、ここでは自然数の足し算を表す。
この節の後半で、読み先の関数とその型を確認する。
型に応じて演算を選ぶ仕組みは、[`Intro2.lean` 1節](#sec-Intro2.classes)で説明する。
-/

/-!
この `def` を受理する前の型検査では、[2節](#sec-Intro1.definitions)と同じ照合が走っている。
コロンの右に注釈した型 `Nat → Nat` から「引数は `n : Nat`」と仮に置き、
そのもとで本体 `n + n` の型が行き先の `Nat` になるかを調べる。つまり
**`fun` 記法で書かれた項の型が、注釈した関数型と一致するか**が検査されている。

一致しなければ、もちろん受理されない。`fun n => e` の**本体 `e`**を、
`Nat` 型ではない `true` にしてみると:

    def bad2 : Nat → Nat := fun n => true

これはエラーになり、Infoview には次のように表示される:

    error: Type mismatch
      true
    has type
      Bool
    but is expected to have type
      Nat

「本体 `true` の型 `Bool` が、注釈から要求される行き先の型 `Nat` と一致しない」
という報告である。
-/

/-! ### 適用の書き方

数学ではふつう `f(x)` と書く関数適用を、Lean では **`f x` と、関数と引数を
半角スペースで区切って**書く。項を書く場所で、関数を表す項のあとに引数の項を
このように並べると、関数適用として読まれる。例えば `double 21` である。
数学で「f(x)」と書くとき、私たちは f が関数で x がその定義域の元であることを
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
-/

/-! ### ✏ 練習（書く）

1. 関数 inc : ℕ → ℕ を inc(n) = n + 1 で定める。これを `fun` を用いて Lean で定義せよ。
   `#check inc` の型と `#eval inc 4` の値を予想してから確かめよ。
2. 関数 f : ℕ → ℕ を f(n) = 2n + 3 で定める。これを `fun` を用いて Lean で定義せよ
   （掛け算は `*` と書く）。`#check f` の型と `#eval f 4` の値を予想してから確かめよ。
-/

/-! ### 表示の読み方: binder 形式

宣言には、引数を左に書く糖衣構文もある。次は上の `double` と同じものである:
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

/-! ### ✏ 練習

1. 関数 triple : ℕ → ℕ、triple(n) = n + n + n を binder 形式で定義せよ。
   `#check triple` の表示を予想してから確かめよ。
2. `#eval double (double 5)` の値を予想してから実行せよ。
3. 先ほどの inc(n) = n + 1 を、今度は binder 形式で `inc'` という名前で定義せよ。
   `#check inc'` の表示と `#eval inc' 4` の値を予想して確かめ、`inc` と比較せよ。
4. 同様に f(n) = 2n + 3 を、binder 形式で `f'` という名前で定義せよ。
   `#check f'` の表示と `#eval f' 4` の値を予想して確かめ、`f` と比較せよ。
-/

/-! ### 多変数関数はカリー化で表す

まず、ふつうの数学の話から始めよう。集合 X・Y・Z に対して、写像全体の集合には
次の自然な1対1対応がある:

    Map(X × Y, Z) ≅ Map(X, Map(Y, Z))

左辺の写像 f に、x を固定して得られる写像「y ↦ f(x, y)」を対応させる。
つまり x ↦ (y ↦ f(x, y)) という右辺の写像にする。この操作を**カリー化（currying）**、
逆に右辺の写像 g から (x, y) ↦ g(x)(y) を作る操作を**アンカリー化（uncurrying）**と呼ぶ。

Lean では、この対応を使い、多変数関数も基本的に1引数関数を重ねた形で表す。
2引数なら、「1つ目の引数を受け取ると、**残り1引数の関数を返す**」形になる。
例えば、数学でいう写像 ℕ × ℕ → ℕ、(a, b) ↦ a + b をカリー化したものを、
`plus : Nat → Nat → Nat` として定義してみよう:
-/

def plus : Nat → Nat → Nat := fun a => fun b => a + b

/-!
読み方の約束を先に押さえる。`→` は**右結合**である:

    Nat → Nat → Nat　は　Nat → (Nat → Nat)　のこと

（「`Nat` を受け取って、関数 `Nat → Nat` を返す」）。逆に、適用は**左結合**:

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

/-! ### ✏ 練習（書く）

1. 関数 addThree : ℕ → ℕ、addThree(n) = 3 + n を、`plus 3 : Nat → Nat` を使って
   Lean で定義せよ。`#check addThree` と `#eval addThree 4` の表示を予想してから確かめよ。
2. 関数 g : ℕ × ℕ → ℕ、g(a, b) = 2a + 3b を、カリー化して Lean で定義せよ。
   型は `Nat → Nat → Nat` とし、`fun a => fun b => …` を使うこと。
   `#check g`・`#check g 2` の型と `#eval g 2 4` の値を予想してから確かめよ。
-/

/-! ### 多変数関数の binder 形式

1変数のときと同じく、引数を宣言の左側に並べられる。例えば `plus` は
次のようにも定義できる（同じ名前を重ねて定義せず、いずれか1つを使う）:

    def plus (a : Nat) (b : Nat) : Nat := a + b

**同じ型の引数は、まとめて** `(a b : Nat)` と書いてもよい:

    def plus (a b : Nat) : Nat := a + b

`fun` の引数もまとめられる。次も、もとの定義と同じ関数を表す:

    def plus : Nat → Nat → Nat := fun a b => a + b

また `fun` の引数には、`fun n : Nat => e` のように括弧なしで型を注釈してもよい。
-/

/-! ### ✏ 練習（書く）

1. 先ほどの g(a, b) = 2a + 3b を、binder 形式で2通りに書け。
   `g'` は `(a : Nat) (b : Nat)` と分け、`g''` は `(a b : Nat)` とまとめること。
   `#check g'`・`#check g''` の表示と、`#eval g' 2 4`・`#eval g'' 2 4` の値を
   予想してから確かめよ。
-/

/-- 3引数以上も同じことの繰り返し。
`Nat → Nat → Nat → Nat` は `Nat → (Nat → (Nat → Nat))` と読む。 -/
def addMul (a b c : Nat) : Nat := a + b * c

#check addMul

/-!
    addMul (a b c : Nat) : Nat

これは `Nat` 型の引数を3つ受け取って `Nat` 型の項を返す、という binder 形式の表示である。
矢印形式では `addMul : Nat → Nat → Nat → Nat` と読める。
-/

/-! ### 関数を引数として受け取る

数学でいう写像 Map(ℕ, ℕ) → ℕ、F ↦ F(21) を Lean で定義してみよう。
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

/-! ### 型の異なる引数の binder 形式

引数の型が異なる場合は、型ごとに括弧を分けて書く。例えば、F と n を受け取って
F(n) を返す関数では、`F : Nat → Nat` と `n : Nat` を別々に注釈する:
-/

def applyAt (F : Nat → Nat) (n : Nat) : Nat := F n

#check applyAt

/-!
    applyAt (F : Nat → Nat) (n : Nat) : Nat

矢印形式では `(Nat → Nat) → Nat → Nat` である。`F` を1つ渡すと、
残りの引数 `n : Nat` を受け取る関数が返る。`(F n : Nat)` とまとめてしまうと
両方が `Nat` 型という指定になるので、ここでは使えない。
-/

/-! ### ✏ 練習（書く）

1. 写像 twice : Map(ℕ, ℕ) → Map(ℕ, ℕ) を、F ↦ (n ↦ F(F(n))) で定める。
   つまり、F を同じ入力に2回使うのではなく、1回目の結果にもう一度 F を適用する。
   これを Lean で `def twice (F : Nat → Nat) : Nat → Nat := …` と定義せよ。
   `#check twice`・`#check twice double` の表示と `#eval twice double 3` の値を
   予想してから確かめよ。
2. 写像 thrice : Map(ℕ, ℕ) → Map(ℕ, ℕ) を、F ↦ (n ↦ F(F(F(n)))) で定める。
   これを Lean で定義し、`#check thrice`・`#check thrice double` の表示と
   `#eval thrice double 3` の値を予想してから確かめよ。
-/

/-! ### 定義域や行き先が型でもよい

[1節](#sec-Intro1.terms-types)で「型も項である」と述べた。だから、**定義域や行き先が `Type` であるような
関数**も、まったく同じ書き方で作れる。例えば `Nat → Type` は、自然数を受け取って
型を返す関数の型である。返すものが数ではなく型でも、関数であることに変わりはない。
まずは、「2つの型 `A`・`B` を受け取り、
関数型 `A → B` を返す」関数:
-/

def Map : Type → Type → Type := fun A B => A → B

#check Map

/-!
    Map : Type → Type → Type

節の冒頭で「`A → B` は写像全体の集合 Map(A, B) と同じ役割を持つ」と述べたが、
その Map を、いま Lean の項として定義したことになる。`Map Nat Nat` は
計算すると `Nat → Nat` になるから、`double` は `Map Nat Nat` の項でもある
（直後の練習で確かめよう）。「型を受け取る関数」「型を返す関数」は、
[6節](#sec-Intro1.dependent-functions)（依存関数型）でさらに主役になる。
-/

/-! ### ✏ 練習

1. `#check Map Nat Bool` の表示を予想してから確かめよ。また、数学でいう
   関数 double : ℕ → ℕ、double(n) = n + n を、`Map Nat Nat` 型の項としても使えるか考えよ。
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

/-! CALLOUT_START preview -/
/-! ### 先取り（詳しくは Intro2）: `Nat.add` と `HAdd.hAdd`

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
クラスやインスタンスの定義・選択の仕組みは、[`Intro2.lean` 1節](#sec-Intro2.classes)で扱う。
数字も型に応じて解釈される記法であり、その仕組みは `OfNat` というクラスが担う。
今は、ほかの型の指定がなければ `3` などを `Nat` の項として読めばよい。
-/

/-! CALLOUT_END -/

/-! ### 型はどう決まるか——下から計算し、上から期待を伝える

[2節](#sec-Intro1.definitions)で「型検査が走る」と述べ、この節の冒頭で `double 21` の2点確認を見た。
一般の形をまとめておく。適用についての規則はただ1つである:

    f : A → B　かつ　a : A　ならば　f a : B

この規則は、型の計算式であると同時に、**適用が合法かどうかの検査**でもある。
`f a` と書いてよいのは、`f` の型が矢印型 `A → B` であり、**かつ**引数 `a` の型が
その定義域 `A` と一致するときだけ。この2点を照合して初めて、
適用が合法だと分かり、結果の型 `B` が読み取れる。

ここで `A`・`B` は、`Nat` のような型に限らない。`A = C → D` のように、
関数型を当てはめても同じ規則が使える。例えば `applyTo21 double` なら、
`A = Nat → Nat`、`B = Nat` と読めばよい。引数 `double` の型が `A` と一致するので、
結果は `B`、つまり `Nat` 型になる。`B` が関数型でも同じで、`plus 3` がその例である。

例えば `double (plus 3 4)` なら:

1. `3 : Nat`、`4 : Nat`
2. `plus : Nat → Nat → Nat`（宣言でそう決めた）
3. `plus 3` — 照合: `plus` の型は関数型 `Nat → (Nat → Nat)` で、定義域は `Nat`。
   引数は `3 : Nat` だから一致する。よってこの適用は**合法**で、
   型は矢印の右側 `Nat → Nat`
4. `(plus 3) 4` — 照合: `plus 3 : Nat → Nat` の定義域 `Nat` に `4 : Nat` が一致。
   合法で、型は `Nat`
5. `double (plus 3 4)` — 照合: `double : Nat → Nat` の定義域 `Nat` に、
   部分項の型 `plus 3 4 : Nat` が一致。合法で、型は `Nat`

どの段階でも、見ているのは**直下の部分項の型と規則1つだけ**であり、
段階ごとに「一致するか」の照合が1回ずつ入っている。
すべての照合が通ったときにだけ、項の全体に型が付く——つまり
「型が付く」ことと「その項が意味を成す書き方である」ことは同じである。
この局所的な検査を項全体に再帰的に行うのが型検査で、
項がどれだけ大きくなっても手順は変わらない。

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
（[4節](#sec-Intro1.inductive-types)）や `⟨1, 2⟩`（[5節](#sec-Intro1.structures)）、
暗黙引数の補完（[4節](#sec-Intro1.inductive-types)・[6節](#sec-Intro1.dependent-functions)）が出てくる。
どれもこの「上から伝える」仕組みの例である。

Lean は、この2つの向きを組み合わせて、書かれた文字列を1つの項として読み、
型検査を行う。`M : A` の型検査は、期待される型 `A` を上から伝えつつ
部分項の型を下から計算し、両者が出会うところで一致を確かめる作業である。

そして、どちらの向きの手順にもひらめきも解釈も要らない——**完全に機械的**である。
だからコンピュータに実行させることができ、実際にそれをやっているのが
Lean の型検査器である。読者がこの教材で行う「型の推測」は、
機械のこの手順を暗算でなぞることに他ならない（目標1）。

この後の節で新しい項の作り方（`match`・依存関数など）を
導入するたびに、型の付け方の規則も1つずつ増える。それでも事情は同じで、
以後の `#check` の表示は「宣言された型」と「そこまでに出た小さな規則集」だけで、
同じように自分の手で検算できる。

なお読むときの目印として、**項のあとにスペースを挟んで項が続いたら、
それは関数適用**である。`double (plus 3 4)` を見た瞬間に「`double` を
`plus 3 4` に適用している」と分解できる。
-/

#check double (plus 3 4)

/-!
    double (plus 3 4) : Nat
-/

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
未完成の部分を残したまま先へ進めるが、完成していないことを Lean は見逃さない。

では `double plus 3 4` と括弧なしで書いたらどうなるか。適用は左結合なので
これは `((double plus) 3) 4` と読まれ、最初の `double plus` の時点で
上と同じエラーになる。`double (plus 3 4)` の括弧は省略できない。
-/

/-! ### ✏ 練習

1. `#check` する**前に**型を計算せよ: `(3 + 4) * 2`、`plus (double 3)`、
   `applyTo21 (plus 3)`、`fun n : Nat => plus n n`。それから確かめよ。
2. `#eval applyTo21 (plus 100)` の値を予想してから実行せよ。
3. 次の2つの写像を Lean で定義し、`#check` の表示を予想してから確かめよ:
   * evalAt : Map(ℕ, ℕ) × ℕ → ℕ、evalAt(F, n) = F(n)。カリー化して定義すること。
     `#eval evalAt double 5` の値も予想してから実行せよ。
   * shift : Map(ℕ, ℕ) → Map(ℕ, ℕ)、F ↦ (n ↦ F(n + 1))。
     関数を受け取って**関数を返す**関数である。
     `#eval shift double 3` の値も予想してから実行せよ。
4. 「型から項を書く」練習: Map(ℕ, ℕ) → ℕ という写像を、**中身の違うもので2つ**考えよ
   （例えば F ↦ F(21) と F ↦ 0）。それらを Lean で `useF1`・`useF2` と名付けて定義し、
   型を予想してから `#check` で確かめよ。どちらも `(Nat → Nat) → Nat` 型になるはずである。
   同じ型に項は何通りもある——型は仕様であって、中身までは決めない。
5. （発展）写像 G : B → C と F : A → B に合成 G ∘ F : A → C を対応させる写像を考える。
   型 A・B・C も引数に取り、これを Lean で
   `compose (A B C : Type) (G : B → C) (F : A → B) : A → C` と定義せよ。
   `#check compose` の表示と、
   `#eval compose Nat Nat Nat double (fun n => n + 1) 3` の値を予想してから
   確かめよ。
6. （発展）練習 3 を一般化し、任意の A・B に対する写像 Map(A, B) × A → B、(F, a) ↦ F(a) と、
   写像 g : A → A に対する変換 Map(A, A) → Map(A, A)、F ↦ (a ↦ F(g(a))) を考える。
   型や g も引数として受け取るように、Lean で
   `evalAt' (A B : Type) (F : A → B) (a : A) : B` と
   `shift' (A : Type) (g : A → A) (F : A → A) : A → A` を定義せよ。
   両者の `#check` の表示と、
   `#eval evalAt' Nat Nat double 5` と `#eval shift' Nat (fun x => x + 1) double 3`
   の値を予想してから確かめ、元の版と比較せよ。
-/

/-! ## 4. 帰納型（inductive type） {#sec-Intro1.inductive-types}

型を作る部品の1つ目が、帰納型である。帰納型は**構成子（constructor）のリスト**で
型を定義する。構成子とは「その型の項の**作り方**」のことで、
帰納型の項は、構成子で作られたものが**すべて**である。
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
  Lean の中で**証明できる**（証明の書き方は `CH.lean` で扱う）。

どちらも名前についての約束ではなく、Lean の中で証明できる事実である。
両方がそろって、集合のアナロジーでは本当に3点集合 {red, yellow, green} になる。
構成子の正式な名前は `型名.構成子名` になる。
[1節](#sec-Intro1.terms-types)の `Bool.true` はこれだった。
-/

/-! ### `Bool` の定義を見に行く

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

/-! CALLOUT_START optional -/
/-! ### 補足（初読は飛ばしてよい）: `true` と `.true`、`red` と `.red`

`Bool.true` も `Signal.red` と同じく、帰納型の定義で付けられた構成子の名前である。
では、[1節](#sec-Intro1.terms-types)で `Bool.true` を単に `true` と書けたのはなぜか。
いま参照した標準ライブラリでは、`Bool` の定義に続けて次の宣言をしている:

    export Bool (false true)

これは `Bool.false` と `Bool.true` を、接頭辞なしの `false`・`true` という名前でも
使えるようにする宣言である。そのため `#check true` だけで型を調べられる。
`inductive` で定義しただけで、すべての構成子の接頭辞を省けるわけではない。

一方、`.red` は**期待される型を手がかりに、名前の接頭辞を補う**記法である
（[3節](#sec-Intro1.functions)で見た、期待される型を上から伝える仕組みの1例）。
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

こうした名前の管理の仕組みは、[`Intro2.lean` 5節](#sec-Intro2.namespaces)で扱う。
このあと本文で使う `.red`・`.yellow`・`.green` は、`open` や `export` を
必要とせず、期待される型から名前を補う書き方である。

この違いは、これから見る `match` の場合分けでも大事になる。接頭辞なしの名前を
用意していない状態で `| red => ...` と書くと、`red` は構成子ではなく、
どの値でも受け取る**新しい変数の名前**になる。赤の場合を指定するには、
`| Signal.red => ...` または `| .red => ...` と書く。
-/
/-! CALLOUT_END -/

/-! ### 先取り（CH）: 「全部」と「別々」を支える道具

先ほどの2つの事実を証明するための道具は、`inductive` の宣言に伴って
Lean が用意する。
`Signal.rec` は、3つの場合を扱えば `Signal` のすべての項について定義・証明できることを表す。
また `Signal.noConfusion` を使えば、異なる構成子で作った項が等しくないことを証明できる。
個々の主張の証明がすべて完成形で自動生成される、という意味ではなく、
**証明を組み立てるための道具が用意される**のである。
詳しい型や使い方は、[`CH.lean` 9節](#sec-CH.nat-proofs)で見る。
-/

/-! ### 項の作り方と使い方

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

/-! ### 先取り（CH）: 仮定として使う・結論として示す

命題を型と見ると、この区別は「その命題の証明を仮定として使う」ことと、
「その命題を結論として、その証明を作る」ことに対応する。
この見方は [`CH.lean` 8節](#sec-CH.introduction-elimination)で改めて説明する。
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

/-! ### ✏ 練習

1. 上の `match` の対象を `Signal.yellow` に変えた項と、`Signal.green` に変えた項を
   書き、それぞれの値を予想してから `#eval` で確かめよ。
-/

/-!
対象を変えるたびに `match` 全体を書き直すのは手間である。対象を変数 `s` にして、
`fun` で受け取ることにすれば、どの信号にも使える**関数**になる。
こうして、`Signal` の項を受け取って次の信号を返す関数を書こう。
`fun` で受け取った `s` を、`match s with` で場合分けする。
次の関数は `Signal → Signal` 型なので、受け取った `Signal` の項を**使い**、
返す `Signal` の項を**作る**という両方の役割を持つ:
-/

def next : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

#check next

/-!
    next : Signal → Signal
-/

/-!
定義した関数を試したい。まず `next Signal.red` という項を読む:
2点確認より型は `Signal`、値は定義の1行目（`Signal.red => Signal.green`）から
`Signal.green` になるはずである。

計算結果は `#eval` で確かめられる。いま作ったばかりの型の値も、
構成子の形で表示される:
-/

#eval next Signal.red

/-!
    Signal.green

たしかに赤の次は青になった。

ここで、**型を手がかりに名前の接頭辞を補うドット記法**を紹介する。
期待される型が `Signal` と分かっている位置では、`Signal.red` を `.red` と省略できる。
例えば `(.red : Signal)` なら、型注釈から接頭辞 `Signal` が補われる。
`.yellow`・`.green` も同じである。次の `match` では、場合分けする項の型から
構成子の接頭辞が分かる。まず練習で試し、そのあと本文でも省略形を使う。
-/

/-! ### ✏ 練習（書く）

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

/-! ### ✏ 練習

1. `Signal` の「逆回り」`prev : Signal → Signal` を `match` で定義し、
   `#eval prev (next Signal.red)` の表示を予想してから確かめよ
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
[`CH.lean` 5節](#sec-CH.empty-types)の `elimEmpty` で実物を見る。）

実は同じことが `Prop` の世界でもできて、命題の `True` と `False` は
帰納型として定義されている。命題の世界の帰納型の話は、このファイルでは
扱わず [`CH.lean` 5節](#sec-CH.empty-types)でまとめて見る。

### 構成子は引数を取れる

構成子に引数を持たせることもできる。構成子の引数は、
`def` と同じくコロンの左に書ける（[3節](#sec-Intro1.functions)の binder 形式）:
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

引数付きの構成子にも、帰納型の仕組みによる保証がある。
異なる構成子で作った `NatOrBool.nat n` と `NatOrBool.bool b` は、決して等しくならない。
さらに、**同じ構成子でも、中身が違えば作られる項は異なる**。
例えば `NatOrBool.nat 3` と `NatOrBool.nat 5` は異なる項である。
逆に `NatOrBool.nat n` と `NatOrBool.nat m` が等しければ、`n` と `m` も等しい。
つまり、構成子 `NatOrBool.nat : Nat → NatOrBool` は**単射**である。
もう一方の `NatOrBool.bool : Bool → NatOrBool` も単射であり、
`NatOrBool.bool b` と `NatOrBool.bool c` が等しければ、`b` と `c` も等しい。
このように、どちらの構成子も中身の違いを保ったまま `NatOrBool` の項を作る。
-/

/-! ### 先取り（CH）: 構成子の単射性を表す補題

この単射性は、Lean が用意する `NatOrBool.nat.inj` という補題として使える。
その主張は「`NatOrBool.nat n = NatOrBool.nat m` ならば `n = m`」である。
同様に、`NatOrBool.bool.inj` は
「`NatOrBool.bool b = NatOrBool.bool c` ならば `b = c`」という補題である。
これらの補題は、帰納型の宣言に伴って Lean が用意する。
異なる構成子を区別する性質と、各構成子の単射性を扱う道具が `NatOrBool.noConfusion` である。
これらは追加の公理として仮定するのではなく、帰納型の仕組みから得られる。
証明の読み方は、[`CH.lean` 9節](#sec-CH.nat-proofs)で扱う。
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

/-! ### ✏ 練習（書く）

1. 中身の値には触れず、`.nat` の札なら `true`、`.bool` の札なら `false` を
   返す `tagOf : NatOrBool → Bool` を書け。不要な中身には `_` を使える。
   `#eval tagOf (NatOrBool.nat 3)` の値を予想してから確かめよ。
-/

/-! ### ✏ 練習

1. `#eval valueOf (NatOrBool.bool true)` の値を予想してから確かめよ
   （どちらの場合に当たるか）。
2. 「`bool` の札なら中身を、`nat` の札なら `false` を返す」関数
   `flagOf : NatOrBool → Bool` を書き、`#eval flagOf (NatOrBool.bool true)` で
   確かめよ。
-/

/-! ### 構成子の引数を複数にする

構成子は、引数を2つ以上受け取ってもよい。書き方は関数の binder 形式と同じで、
同じ型なら `(a b : Nat)`、異なる型なら `(n : Nat) (flag : Bool)` のように並べる。
`match` で使うときも、例えば `.mk a b` と、取り出す中身の名前を順に並べる。
まず構成子が1つの場合から練習しよう。
-/

/-! ### ✏ 練習（書く）

1. 自然数の組 `(a, b)` を表す型 `NatPair : Type` を `inductive` で定義せよ。
   構成子は `mk` の1つとし、自然数を2つ受け取るものとする。
   `#check NatPair.mk` と `#check NatPair.mk 3 5` の表示を予想して確かめよ。
2. 第1成分を返す写像 `firstNat : NatPair → Nat` と、第2成分を返す写像
   `secondNat : NatPair → Nat` を、それぞれ `match` で書け。
   両関数の型を `#check` し、`#eval firstNat (NatPair.mk 3 5)` と
   `#eval secondNat (NatPair.mk 3 5)` の値を予想して確かめよ。
-/

/-!
引数の型が異なっても、同じように作り、同じように取り出せる。
-/

/-! ### ✏ 練習（書く）

1. 自然数 `n` と真偽値 `flag` の組を表す型 `FlaggedNat : Type` を
   `inductive` で定義せよ。構成子は `mk` の1つとする。
   `#check FlaggedNat.mk` と `#check FlaggedNat.mk 3 true` の表示を予想して確かめよ。
2. 自然数の成分を返す `numberOf : FlaggedNat → Nat` と、真偽値の成分を返す
   `flagOfPair : FlaggedNat → Bool` を `match` で書け。
   両関数の型を `#check` し、`FlaggedNat.mk 3 true` に適用した値を予想して
   `#eval` で確かめよ。
-/

/-!
さらに、構成子を複数にして、それぞれに異なる個数・型の引数を持たせることもできる。
-/

/-! ### ✏ 練習（書く）

1. 次の3種類のデータを表す型 `MixedData : Type` を `inductive` で定義せよ。
   構成子 `pair` は自然数を2つ、`flagged` は自然数と真偽値を受け取り、
   `empty` は引数を受け取らないものとする。
   3つの構成子の型を予想して `#check` で確かめよ。
2. 写像 `readNumber : MixedData → Nat` を、`pair a b` は `a + b` に、
   `flagged n flag` は `n` に、`empty` は `0` に送るものとして定める。
   これを `match` で書き、型を `#check` せよ。さらに `MixedData.pair 3 5`、
   `MixedData.flagged 3 true`、`MixedData.empty` に適用した値を予想して `#eval` で確かめよ。
-/

/-! ### 型をパラメータにする

次の段階として、包む中身の型そのものをパラメータ `(α β : Type)` にできる:
-/

inductive MySum (α β : Type) : Type where
  | inl (a : α) : MySum α β
  | inr (b : β) : MySum α β

#check MySum

/-!
    MySum (α β : Type) : Type

binder 形式を読み替えれば `MySum : Type → Type → Type`——[3節](#sec-Intro1.functions)の `Map` と
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
先頭に付いた。ここで、引数を包む括弧の違いを説明しよう。

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

よく見るとこの型は、**引数 `α` の値が後ろの引数の型に現れる**——[6節](#sec-Intro1.dependent-functions)で主役になる
依存関数型の、最初の実物である。暗黙引数の仕組みも、そこでこの一般的な関数型の中に位置づけ直す。
-/

/-!
`MySum α β` の項は、「`α` の項に `inl` の札を付けたもの」か
「`β` の項に `inr` の札を付けたもの」のどちらか。集合のアナロジーでは
**直和** α ⊔ β である——`NatOrBool` は `MySum Nat Bool` に相当する
（`CH.lean` に出てくる `⊕` は、標準ライブラリにあるこれと同じ型）。

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

/-! ### ✏ 練習（書く）

1. `MySum Bool Bool` の左右どちらの札からも、中身の `Bool` をそのまま返す
   `mergeBool : MySum Bool Bool → Bool` を書け。
   `#eval mergeBool (MySum.inl true)` と
   `#eval mergeBool (MySum.inr false)` を予想してから確かめよ。
-/

/-! CALLOUT_START optional -/
/-! ### 補足（初読は飛ばしてよい）: 型をパラメータにした取り出し関数

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

/-! CALLOUT_END -/

/-! ### ✏ 練習

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

/-! ### 補足（初読は飛ばしてよい）: 集合の方程式としての再帰

集合のアナロジーでは、`MyNat` は方程式

    X ≅ 1 ⊔ X   （zero の分の1点 ⊔ succ の引数の分）

を満たす**最小**の集合と読める。右辺に自分自身が現れるのが再帰の印で、
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

/-! ### 補足（初読は飛ばしてよい）: 再帰が止まることの検査

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

/-! ### ✏ 練習（書く）

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
`succ (succ (succ zero))` の表示）、`CH.lean` に出てくる `×` `⊕`、
さらには命題の側の `And` `Or` `Eq` すらもそうなのだが、命題の話は
`CH.lean` に譲る。

`Top.lean` では、`Nat` の再帰で集合の有限個の共通部分 `interFin` を定義し、
その性質もまた再帰で証明している。**再帰で書いた証明が数学的帰納法**である。
-/

/-! ### ✏ 練習

1. `MyNat` の項として 3 を `def myThree : MyNat := …`（`succ` 3回）と書き、
   `#reduce add myThree MyNat.zero` の表示を予想してから確かめよ。
2. 2点の列挙型 `inductive Two : Type where | a : Two | b : Two` を定義せよ。`Two` と `Bool` は
   集合としては同じ2点集合だが、型としては別物である。往復の関数
   `toBool : Two → Bool` と `ofBool : Bool → Two` を書き、
   `#eval toBool (ofBool true)` を確かめよ。
3. `Two → Bool` の関数は、集合のアナロジーで数えると 2 × 2 = 4 通り
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
   往復が恒等になることの証明には数学的帰納法が要る。`CH.lean` のあとで
   戻ってくるとよい。）
-/

/-! ## 5. structure {#sec-Intro1.structures}

構成子が**1つだけ**で、その構成子が**複数の引数**を受け取る帰納型は、
「成分をまとめて持ち運ぶ入れ物」としてよく使う。
[4節](#sec-Intro1.inductive-types)の練習では、`NatPair` や `FlaggedNat` を定義し、
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
構成子による場合分けは1ケースで済む。[4節](#sec-Intro1.inductive-types)で書いた
`firstNat` と同じように、第1成分を取り出す関数が書ける。
-/

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | .mk a _ => a

#check MyPoint.x

/-!
    MyPoint.x : MyPoint → Nat

帰納型の項を構成子に応じて場合分けするには `match` を使う——構成子が1つなら、
場合分けが1ケースになるだけで、原理は [4節](#sec-Intro1.inductive-types)と変わらない。
-/

/-!
この「構成子1つの帰納型＋成分の取り出し関数」をひとまとめに書く構文が
`structure` である。つまり structure は `inductive` の**特別な場合**であり、
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
（これも[3節](#sec-Intro1.functions)の「上から伝える」仕組みである）。
この場合は `Point.mk 1 2` と解釈される。
`+` のように記法宣言で関数名に結び付けるものとは異なり、型に応じて構成子を選ぶ仕組みである。
structure 専用ではなく、構成子が1つの帰納型でも使える。

期待される型が `Point` と分かる位置では、`Point.mk` を `.mk` とも書ける。
[4節](#sec-Intro1.inductive-types)の `.red` と同じく、期待される型から名前の
接頭辞を補う。例えば次の宣言では、`: Point` がその手がかりになる:
-/

def pointFromDot : Point := .mk 1 2

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
これは[4節](#sec-Intro1.inductive-types)で見た `n.succ` と同じ読み方である。
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

/-! ### 直積の普遍性を思い出す

集合のアナロジーでは、`Point` は直積 Nat × Nat である。
**直積の普遍性**を思い出そう。同じ集合 A からの2本の写像
f, g : A → Nat を与えると、各 a を組 (f(a), g(a)) に送る写像
h : A → Nat × Nat がただ1つ定まる。逆に h の各成分を取り出せば、f と g に戻る。

Lean では `Point.mk` が組を作る側、`Point.x`・`Point.y` が成分を取り出す側に当たる。
次の練習では、この対応をコードにし、具体的な入力で確認しよう。
一意性の証明までは求めない。
-/

/-! ### ✏ 練習（書く）

1. 型 `A` と2本の写像 `f g : A → Nat` が与えられたとする。
   a を組 (f(a), g(a)) に送る写像 `pairAt A f g : A → Point` を定めたい。
   `pairAt (A : Type) (f g : A → Nat) : A → Point` を書き、`#check pairAt` で型を確認せよ。
   A = Nat、f(n) = n + 1、g(n) = 2n として `3` を渡したときの
   第1・第2成分を予想し、`Point.x`・`Point.y` と `#eval` で確かめよ。
-/

/-! ### ✏ 練習（書く）

1. `Point` の第1成分だけを1増やす `moveRight : Point → Point` を書け。
   成分の取り出しには `Point.x`・`Point.y`、作成には `Point.mk` を使う。
   `#eval Point.x (moveRight (Point.mk 1 2))` の値を予想して確かめよ。
-/

/-! ### 自分で定義した関数もドットで使える

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
[`Intro2.lean` 5節](#sec-Intro2.namespaces)で扱う。
-/

/-! ### ✏ 練習

1. `Point.zeroX (p : Point) : Point` を定義し、第1成分だけを `0` にせよ。
   本体では `p.y` と `.mk` の両方を使う。`#eval (Point.mk 1 2).zeroX.x`
   の値を予想して確かめよ。
2. `#eval (Point.mk 1 2).swap.swap.x` の値を予想してから確かめよ
   （2回入れ替えると元に戻るはずである）。またこの式を、ドットを使わず
   フルネームの適用だけで書き直すと何になるか、紙に書いてから `#eval` で
   一致を確かめよ。
-/

/-! ### ✏ 練習

1. 次の structure を定義し、`#check` で構成子と取り出し関数が
   自動定義されていることを確かめよ:

       structure Circle : Type where
         center : Point
         radius : Nat

2. 点 p と自然数 n から、中心が p、半径が n の円を作る写像を、
   `makeCircle : Point → Nat → Circle` として書け。型を `#check` し、
   `#eval Circle.radius (makeCircle (Point.mk 1 2) 3)` の値を予想して確かめよ。
3. 円からその中心の第1座標を取り出す写像 `centerX : Circle → Nat` を書け。
   型を `#check` し、`#eval centerX (makeCircle (Point.mk 1 2) 3)` の値を予想して確かめよ。
-/

/-! ### ✏ 練習

1. `#eval Point.y (Point.mk 1 2)` の値を予想してから確かめよ。
   さらに `(Point.mk 1 2).y` とも書けることを試し、同じ値が返ることを確かめよ。
2. フィールドの型は、自作の structure でもよい。長方形

       structure Rect : Type where
         corner : Point
         width : Nat
         height : Nat

   を定義し、`def r : Rect := ⟨⟨1, 2⟩, 10, 5⟩` が受理されることを確かめよ
   （`⟨ ⟩` の入れ子が `corner : Point` の分である）。`#eval r.corner.x` の
   値を予想してから確かめよ。`r.corner`、`r.corner.x` の順に型を追うこと。
3. 長方形から幅と高さの積を返す写像 `rectArea : Rect → Nat` を書け。
   型を `#check` し、前問の `r` に対する `#eval rectArea r` の値を予想して確かめよ。
-/

/-! ### 型をパラメータにする structure

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

/-! ### フィールドを番号で指定する

フィールドは番号でも取れる。`p : Pair α β` に対して、`p.1` は `p.fst`、
`p.2` は `p.snd` と同じものである。`.1`・`.2` は第1・第2フィールドを指定する
書き方で、名前を覚えていなくても位置で取り出せる。
`Point` でも `(Point.mk 1 2).1` は `(Point.mk 1 2).x` と同じ。型は `Nat`、値は `1` のはずである:
-/

#eval (Point.mk 1 2).1

/-!
    1

次は `Pair Nat Bool` の第2フィールドなので、型は `Bool`、値は `true` のはずである:
-/

#eval (Pair.mk 1 true).2

/-!
    true
-/

/-!
集合のアナロジーでは、`Point` は直積 Nat × Nat、`Pair α β` は直積 α × β である。
つまり structure は「**直積の各成分に名前を付けたもの**」と思ってよい。
実際、標準ライブラリの `×` 自身が `fst`/`snd` という2フィールドの
structure（名前は `Prod`）として定義されている。
-/

/-! ### ✏ 練習

1. `#check Pair.mk true 0` の表示を予想してから確かめよ
   （`α`・`β` は何に決まるか）。
2. （発展）[3節](#sec-Intro1.functions)の「カリー化」の正体を自分で書く。組を受け取る関数を
   「1つずつ受け取る」形に直す
   `curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat` と、その逆向き
   `uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat` を書け。
   `#check curryP`・`#check uncurryP` で型を確認し、
   `#eval curryP (fun p => p.fst + p.snd) 3 4` の値を予想してから確かめよ。
-/

/-! ### 補足（初読は飛ばしてよい）: 帰納型を直和と直積で見る

前節の直和とここの直積をまとめると、ここまでの非再帰的で、
構成子の引数の型が互いに依存しない例は、集合の言葉でこう読める:

    (構成子1の引数たちの直積) ⊔ (構成子2の引数たちの直積) ⊔ …

つまり**構成子の個数が直和の項数を、各構成子の引数が直積の因子を**与える。
`Signal` は 1 ⊔ 1 ⊔ 1（3点集合）、`MySum α β` は α ⊔ β（直和だけ）、
`Point` は Nat × Nat（直和が1項に退化して直積だけ）、
構成子が0個なら空集合（`Empty`）。
「structure は直積」と「帰納型は直和のようなもの」は矛盾しない——
直和を**使って**直積を定義しているのではなく、構成子の**個数**と**引数**という
直交した2つの軸が、それぞれ直和と直積に対応しているのである。

なおアナロジーの注意を1つ。集合と違って、型は**外延（要素の一致）では
同一視されない**。`Point` と `Pair Nat Nat` は「中身」は同じだが別の型である
（この話は `Intro2.lean` の `Fin` の補足でも再登場する）。
-/

/-! ### フィールドは前のフィールドに依存してよい

今度は、「どの集合を選ぶかで、その上に載せる構造の集まりも変わる」という状況を考えよう。
サイズの問題をいったん脇に置くと、群を1つ指定することは、集合 X と、
その上の群構造を1つ指定することである。集合 X ごとにその上の群構造全体を Grp(X) と書けば、
群全体は**集合族の直和** ⊔_{X} Grp(X) として捉えられ、個々の群がその要素に当たる。
ここで群構造には、演算・単位元・逆元と、それらが満たす公理を含めている。
同様に、位相空間を1つ指定することも、集合 X とその上の位相を1つ指定することである。

一般に、族の直和 ⊔_{a ∈ A} B(a) の要素は、
「a を1つ選び、それに応じた B(a) の要素を1つ添える」という組である。
structure でも、**後のフィールドの型を、前のフィールドに依存させる**ことで、
この形のデータを表せる。公理を証明として持たせる話は `CH.lean` 以降に譲り、
ここでは単純な**点付き集合**——集合と、その要素を1つ選んだ組——を例にしよう。

[1節](#sec-Intro1.terms-types)で見たとおり型も項だから、フィールドの値として**型そのもの**を持たせ、
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
これは[1節](#sec-Intro1.terms-types)で見た `Type : Type 1` と対応している。
`mk` の型を推測しよう。フィールドの列そのまま……のはずで、[4節](#sec-Intro1.inductive-types)の `MySum.inl` と
同じく、**第2引数の型の中に第1引数の名前が現れる**ことになる:
-/

#check PointedType.mk

/-!
    PointedType.mk (carrier : Type) (point : carrier) : PointedType
-/

/-- 例:「型 `Nat` と、その要素 `0`」の組。 -/
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

族 B(a) が a によらない定数 B のときは、⊔_{a ∈ A} B = A × B となる。
つまり、これまでの依存しないフィールドによる直積も、族の直和の特別な場合である。
-/

/-! ### 依存するフィールドも inductive で書ける

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

`PointedType.mk` と同じ形で、最後の行き先だけが `MyPointedType` になっている。
別の名前で宣言したので `PointedType` と同一の型ではないが、持つデータは同じ形である。
`inductive` で書いた側では成分を取り出す関数を `match` で書くのに対し、
`structure` では `PointedType.carrier`・`PointedType.point` が自動生成される。
-/

/-! ### ✏ 練習

1. `def pointedBool : PointedType := ⟨Bool, true⟩` が受理されることを確かめよ。
   また `#check PointedType.mk Nat` の表示を予想してから確かめよ
   （第1引数を渡すと、第2引数の型が決まる）。
-/

/-! ### ✏ 練習（書く）

1. 自然数 n を点付き集合 (Nat, n) に送る写像 `attachNat : Nat → PointedType` を書け。
   型を `#check` し、`#reduce (attachNat 3).point` の値を予想して確かめよ。
2. 点付き集合 (A, a) から台となる型 A を取り出す写像 `baseType : PointedType → Type` を書け。
   型を `#check` し、`#reduce (types := true) baseType pointedNat` と
   `#reduce (types := true) baseType pointedBool` の表示を予想して確かめよ。
   ここで `(types := true)` は、型そのものも計算して表示させる指定である。
   通常の `#reduce` は型の計算を省くので、今回はこの指定を付ける。
3. 点付き集合 (A, a) と写像 f : A → A から、点付き集合 (A, f(a)) を作る関数
   `mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType` を書け。
   型を `#check` し、`#reduce (mapPointed pointedNat Nat.succ).point` の値を予想して確かめよ。
-/

/-! CALLOUT_START preview -/
/-! ### 先取り（[6節](#sec-Intro1.dependent-functions)）: 取り出す値の型も入力で変わる

台となる型だけでなく、その中の点を取り出す関数も読んでみよう。
`p : PointedType` の点は `p.carrier` 型なので、取り出し関数の結果の型は
**入力 `p` によって変わる**はずである:
-/

#check PointedType.point

/-!
    PointedType.point (self : PointedType) : self.carrier

たしかに、結果の型に引数 `self` が現れた。`PointedType → Nat` のように
固定した行き先では書けない。この形を依存関数型と呼び、次節で説明する。
-/

/-! ### ✏ 練習（書く）

1. 点付き集合 (A, a) から点 a を取り出す関数 `getPoint (p : PointedType) : p.carrier` を書け。
   `#check getPoint` の表示を予想して確かめ、結果の型が引数に依存している箇所を指摘せよ。
   さらに `#reduce getPoint pointedNat` と `#reduce getPoint pointedBool` の値を予想して確かめよ。
-/
/-! CALLOUT_END -/

/-! ### 先取り（CH）: 証明をフィールドに持つ構造

この「後の成分が前の成分に依存する組」の一般論は、[`CH.lean` の7節](#sec-CH.dependent-sums)（依存和）で
扱う。特に、第二成分を**命題の証明**にしたもの（部分型）はそこで主役になり、
`Top.lean` でも「分離データの束」`SeparatingPair` として活躍する。
群の公理などを証明としてフィールドに持たせることも、この仕組みでできる。
-/

/-! ## 6. 依存関数型（dependent function type） {#sec-Intro1.dependent-functions}

前節では、集合族 B(a) の**直和**を考えた。今度は**直積** ∏_{a ∈ A} B(a) を考えよう。
その要素は、各 a に対して B(a) の要素を1つずつ指定するものである。
つまり、a を受け取って B(a) の要素を返す関数であり、**行き先が入力によって変わる**。
これは、直和 ⊔_{a ∈ A} B(a) から添字集合 A への射影 (a, b) ↦ a の
**切断**を与えることとも同じである——各 a に、その上にある組 (a, b) を1つずつ対応させる。

型でも同じように、入力に応じた型の項を返す**依存関数**を考えられる。
まずは「型そのものを最初の引数として受け取る」例で見よう。
型が引数にできることは、[3節](#sec-Intro1.functions)の `Map` で見たとおりである。
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
集合族の言葉で読むと、`idAt` は、各型 `α` に対して関数型 `α → α` の項を1つ選んでいる。
その選び方が「各型の上の恒等写像を選ぶ」である。

[5節](#sec-Intro1.structures)の先取りで見た取り出し関数も、同じ形の型を持つ:

    PointedType.point : (p : PointedType) → p.carrier

`p` を1つ渡すと、行き先の型はその `p.carrier` に決まる。
例えば `pointedNat` なら `Nat` 型の `0`、`pointedBool` なら `Bool` 型の `true` を返す。
そこで書いた `getPoint` も、この依存関数型を持つ関数だったのである。
-/

/-!
なお、この「型を渡してから使う」仕組みこそ、ここで見てきた多相性の正体である。
[4節](#sec-Intro1.inductive-types)で説明した暗黙引数 `{α : Type}` は、この型の引数を
文脈から補ってもらう書き方だった。以下では、その表示の読み方を依存関数型の立場から整理する。
-/

/-! ### ✏ 練習（書く）

1. 型 `α`・`β` とその項 `a : α`・`b : β` を受け取る
   `makePair (α β : Type) (a : α) (b : β) : Pair α β` を書け。
   `#check makePair Nat Bool 3 true` の型を予想して確かめよ。
2. 同じ引数から成分の順を入れ替えた `Pair β α` を返す
   `swapAt (α β : Type) (a : α) (b : β) : Pair β α` を書け。
   `#check swapAt Nat Bool` で残りの関数型を予想して確かめよ。
-/

/-! ### ✏ 練習

1. `#check idAt (Nat → Nat)` の型を予想してから確かめよ（矢印の結合に注意）。
   `#eval idAt (Nat → Nat) double 21` はどうなるか。
2. `#check idAt Signal` の表示を予想してから確かめよ。
3. 「2つめの引数を無視する」依存関数 `constAt (A B : Type) (a : A) : B → A` を
   書け（`idAt` と同じく、型を受け取ってから中身が始まる）。
   `#check constAt Nat Bool 5` の型と `#eval constAt Nat Bool 5 true` の値を
   予想してから確かめよ。
-/

/-! ### 型の読み方と括弧 `( )`・`{ }`

[4節](#sec-Intro1.inductive-types)の明示引数・暗黙引数の区別を踏まえて、
`#check` が表示する型の読み方をまとめておく。例えば

    Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β

は、コロンの左に引数の列が並び、最後の `: Pair α β` が結果の型、と読む
（[3節](#sec-Intro1.functions)で見た binder 形式である）。Lean が補う暗黙引数も含め、
引数を1つ渡すたびに列の左から1つ消えていき、
全部渡すと結果の型の項が得られる。そして各段階で「渡した項の型が、引数の型と
一致するか」の型検査が走っている。[2節](#sec-Intro1.definitions)からやってきたことの一般形である。

引数を包む括弧は、「その引数を**誰が埋めるか**」を表している。

* `(fst : α)` — **明示引数**。使う側が自分で書く。
* `{α : Type}` — **暗黙引数**。使う側は通常、省略する。Lean が読み込みの段階で、
  他の引数の型や、結果に期待される型とのつじつま合わせ（単一化）から補う（この前処理を
  **エラボレーション**と呼ぶ。型検査との関係は [`CH.lean` 10節](#sec-CH.type-checking)で整理する）。
  `Pair.mk 1 true` と書けば `1 : Nat` と `true : Bool` から
  `α := Nat`、`β := Bool` が決まる。

手がかりが足りなければ、暗黙引数は決まらない。[4節](#sec-Intro1.inductive-types)の
`(MySum.inl 3 : MySum Nat Bool)` のように、型注釈で情報を補える。

括弧にはもう1種類 `[ ]` があるが、それは `Intro2.lean` の class とともに説明する。
-/

#check Pair.mk 1 true

/-!
    { fst := 1, snd := true } : Pair Nat Bool

暗黙引数が埋まって `Pair Nat Bool` になった。なお表示の
`{ fst := 1, snd := true }` は `Pair.mk 1 true` の**別表示**である
（フィールド名付きの structure リテラル。書くときにも使える）。
-/

/-!
行き先の型は、`Type` の住人でなくてもよい。**命題を返す関数**（数学でいう述語）を
作り、「すべての `n` について…」の証明そのものを依存関数として書く——それが
[`CH.lean` の6節](#sec-CH.dependent-products)の主題である。`Top.lean` に出てくる「集合の族」 `U : I → Set X` や
「型の族」 `P : α → Type` も、この「型（や集合、命題）を返す関数」の仲間である。
-/

/-! ## 7. まとめ練習 — 小さな型つき言語で書く {#sec-Intro1.exercises}

ここまでの部品——`fun` と適用、`match`、`inductive`、`structure`、
型を引数に取る関数——だけで、Lean は小さな**型つきプログラミング言語**として
使える。仕上げに、**集合と写像の言葉で述べた仕様を、Lean の型と項として書く**総合練習を置く。

以下では、ℕ は 0 を含む自然数の集合、Map(X, Y) は X から Y への写像全体を表す。
まず数学的な対応を読み、そのあと指定された名前と型で Lean のコードにしよう。
ℕ × ℕ のような直積を定義域とする写像は、[3節](#sec-Intro1.functions)で見たカリー化によって
`Nat → Nat → Nat` のように1引数ずつ受け取る形でも表せる。

どの問題も、書いたら `#check` で型を、`#eval` で値を、機械に答え合わせ
させること。行き詰まったら、まず矢印の形に合わせて `fun` の引数を並べ、
返すべきものの型を確かめるとよい——**型が設計図である**。
-/

/-! ### ✏ 練習

1. 写像 F : ℕ × ℕ → ℕ に対して、G(a, b) = F(b, a) で定まる写像
   G : ℕ × ℕ → ℕ を対応させる操作を考える。
   この対応 F ↦ G を、カリー化を使って
   `flipNat (F : Nat → Nat → Nat) : Nat → Nat → Nat` として書け。
   `#eval flipNat (fun a b => a - b) 3 10` の値を予想してから確かめよ。
2. 写像の集合の間の写像 T : Map(ℕ, ℕ) → Map(ℕ, ℕ) を、
   T(F) = F ∘ F ∘ F、すなわち T(F)(n) = F(F(F(n))) で定める。
   T を `iterate3 (F : Nat → Nat) : Nat → Nat` として書け。
   `#eval iterate3 double 1` の値を予想してから確かめよ。
3. 2点集合 B = {true, false} と3点集合 S = {red, yellow, green} を考える。
   写像 f : B → S を f(true) = green、f(false) = red で定め、
   写像 g : S → B を g(green) = true、g(red) = g(yellow) = false で定める。
   B を `Bool`、S を `Signal` で表し、f と g をそれぞれ
   `boolToSignal : Bool → Signal`、`signalToBool : Signal → Bool` として書け。
   合成 g ∘ f の true における値を予想し、
   `#eval signalToBool (boolToSignal true)` で確かめよ。
4. 写像 F : ℕ → ℕ に対して、写像 H : ℕ × ℕ → ℕ × ℕ を
   H(x, y) = (F(x), F(y)) で定める。
   直積 ℕ × ℕ を `Point` で表し、この対応 F ↦ H を
   `mapPoint (F : Nat → Nat) (p : Point) : Point` として書け。
   `#eval (mapPoint double (Point.mk 2 3)).y` の値を予想してから確かめよ。
5. 集合 A, B の直和の間の交換写像 s : A ⊔ B → B ⊔ A を考える。
   A 側の要素 a は、行き先の A 側、すなわち右側の要素 a に送り、
   B 側の要素 b は、行き先の B 側、すなわち左側の要素 b に送る。
   中身は変えず、左右の位置だけを入れ替える写像である。
   直和を `MySum` で表し、A, B も引数として受け取る
   `swapMySum (A B : Type) : MySum A B → MySum B A` を書け。
   `#eval fromSum (swapMySum Bool Nat (MySum.inl true))` の値を予想してから
   確かめよ（`fromSum : MySum Nat Bool → Nat` は[4節](#sec-Intro1.inductive-types)で定義した）。
6. 各集合 A に対して、その要素 a を点付き集合 (A, a) に送る写像を考える。
   点付き集合を `PointedType` で表し、A も引数として受け取る
   `pointedOf (A : Type) (a : A) : PointedType` を書け。
   [5節](#sec-Intro1.structures)の `pointedNat` や練習の `pointedBool` を、
   どの型とその項からも作れるように一般化したものである。
   `#check pointedOf Bool true` の表示を予想してから確かめよ。
7. （発展）集合 A と写像 F : A → A に対して、その反復 Fⁿ : A → A を、
   F⁰ = id_A、Fⁿ⁺¹ = F ∘ Fⁿ と定める。ここで id_A は A 上の恒等写像である。
   自然数 n と要素 a を Fⁿ(a) に送る写像 ℕ × A → A を、A, F も引数に取り、
   `applyN (A : Type) (F : A → A) (n : Nat) (a : A) : A` として書け。
   `n` の `match` は `| 0 => …`・`| k + 1 => …` の形（[4節](#sec-Intro1.inductive-types)の練習の
   `ofN` と同じ）。`#eval applyN Nat double 3 1` の値を予想してから確かめよ。
8. （発展）集合 A の対角写像 Δ_A : A → A × A を、Δ_A(a) = (a, a) で定める。
   直積を `Pair` で表し、どの型 A でも使える
   `diag (A : Type) (a : A) : Pair A A` を書け。
   `#eval (diag Nat 3).fst` の値を予想してから確かめよ。
   A の項として与えられているのは a だけであることにも注目せよ。
   [3節](#sec-Intro1.functions)の練習（`(Nat → Nat) → Nat` の項を2つ書く）と比較し、
   **型の形によって、書ける項の自由度がどう変わるか**を考えよ。
-/

/-!
これで `CH.lean` を読む準備が整った。`CH.lean` のあとは `Intro2.lean` →
`Top.lean` と進んでほしい。
-/

/-! ## 付録: 記号の打ち方まとめ

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
