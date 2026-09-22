/-!
# Lean 最小限の導入 I — 型と項の言語

教材全体の目標はトップページ（index）に掲げた。このファイル（Intro1）は
主に**目標1**を担当し、`CH.lean` を読むために必要な最低限の言語機能だけを
説明する。読む順は Intro1 → `CH.lean` → Intro2 → `Top.lean`。

このファイルで伝えたいことは2つ。

* Lean のもっとも基本の要素は**項**と**型**である。
  Lean に書くことはすべて「項 `a` は型 `α` を持つ」（`a : α` と書く）の組み立てである。
* 型を作る部品は実質2つ、**帰納型**（inductive type）と**依存関数型**である。

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

/-! ### 補足（初読は飛ばしてよい）: 記号の入力のしかた

Lean のコードには `→` や `⟨ ⟩` のような記号が多く出てくる。VS Code の
Lean 4 拡張では、**バックスラッシュ `\` で始まる略記**を打つと記号に変換される
（例えば `\to` と打って、続けて空白を打つか Tab を押すと `→` になる）。
本文では、記号の初出時に打ち方を添え、まとめの表をこのファイルの末尾に置く。
**エディタ上の記号にマウスを乗せると打ち方がポップアップに表示される**ので、
出会った記号はホバーで確かめてもよい。
-/

/-! ## 1. 項と型 {#sec-Intro1.terms-types}

Lean に書くものの基本の単位を**項**（term）と呼ぶ。項とは何かの正確な定義は
ここでは与えないが、さしあたり **`#check` の右側に書いてエラーが出ないものは
項だと考えてよい**。
`#check e` は、項 `e` の**型**を調べて表示するコマンドである。
-/

#check 3

/-!
    3 : Nat
エディタ右側のパネル（Infoview）には、次のように表示される:

    3 : Nat

これは「項 `3` は型 `Nat`（自然数の型）を持つ」と読む。
-/

#check true

/-!
    Bool.true : Bool

「項 `true` は型 `Bool`（真偽値の型）を持つ」。表示が `Bool.true` となっているのは、
これが `true` の正式な名前だからである（この命名の仕組みは[4節](#sec-Intro1.inductive-types)で見る）。

すべての項はちょうど1つの型を持つ（厳密には、定義から計算して一致する型を
同一視する、などの但し書きが要るが、この教材の範囲では「ちょうど1つ」と
考えて差し支えない）。ここで大事な観察が1つある。
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

/-! もう1つ、次の宇宙がある: -/

#check Prop

/-!
    Prop : Type

`Prop` は**命題**たちの住む宇宙である（このファイルでは深入りしない。
`CH.lean` の主題である）。

型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（[3節](#sec-Intro1.functions)の `Map` と[6節](#sec-Intro1.dependent-functions)）。

-/

/-! CALLOUT_START preview -/
/-! ### 先取り（[3節](#sec-Intro1.functions)・CH）: 演算と命題の記号

数の演算や、等式・不等式の記号も、ふつうに書ける。それぞれが正確には何者なのかは
後で説明することにして（`+` は[3節](#sec-Intro1.functions)。`=` と `<` はこのファイルでは深入りせず、
`CH.lean` で主役になる）、表示だけ先に見ておく。
-/

#check 3 + 4

/-!
    3 + 4 : Nat

「`3 + 4` という項は `Nat` 型を持つ」——数から作った式は、また数の項になる。
-/

#check 1 + 1 = 2

/-!
    1 + 1 = 2 : Prop

「`1 + 1 = 2` という項は `Prop` 型を持つ」——等式は**命題**の項になる。
`Prop` の住人がさっそく現れた。
-/

#check 2 < 1

/-!
    2 < 1 : Prop

「`2 < 1` という項は `Prop` 型を持つ」。`2 < 1` のような**偽の命題も**、命題としては立派な項であることに注意
（真偽と証明の話は `CH.lean` で）。
-/

/-! CALLOUT_END -/

/-!
この節で覚えるべきことは2つだけである:
**項の型はいつでも `#check` で調べられる**こと、そして**型も項である**こと。
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

推測された型を読んでみると——「任意の命題 `p`, `q`, `r` について、
`p` ならば `q`、`q` ならば `r` が成り立つなら、`p` ならば `r`」。
**含意の推移律**という定理の主張である。つまり、いま書いた項はこの定理の
**証明**であり、型を推測できたということは、機械がこの証明を
**検証できた**ということなのである。

本体 `hqr (hpq hp)` では、証明がふつうの関数と同じように適用されている:
`hpq` に `p` の証明 `hp` を渡して `q` の証明を作り、それを `hqr` に渡して
`r` の証明を作る。「含意の証明は関数であり、仮定を使うことは関数適用である」
——この対応の種明かしが `CH.lean` である。

項の型を自動で推測できる、というだけの機能が、そのまま定理の証明の検証に
使える——これが目標2の意味である。次の節からは、この「型の推測」を
自分の手でできるようになるための道具立てを、順に説明していく。
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
2. `#check 3 < 5` の表示を予想してから確かめよ（命題の真偽と、型が付くかどうかは
   別の話である）。
-/

/-! ## 2. def — 新しい項を定義する {#sec-Intro1.definitions}

    def 名前 : 型 := 項

と書くと、**新しい項を定義**できる。定義した名前は、以後どこでも使える。
-/

def two : Nat := 2

#check two

/-!
    two : Nat

「`two` という `Nat` 型の項を、`2` として定義した」——宣言に `: Nat` と
書いたのだから型は `Nat` のはずで、表示もそのとおりである。
定義した項は、それ自体また項として使える:
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

さて、ここからが**この教材の最重要のテーマ**である。
`def` の宣言を受理する前に、Lean は**型検査**を行っている:
`:=` の右に書いた項の型を計算し、コロンの右に書いた型と一致するかを調べる。
一致しなければ受理されない。

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

「`true` の型は `Bool` であり、要求されている型 `Nat` と一致しない」という報告である。
-/

/-! ### ✏ 練習

1. `def five : Nat := 5` を自分で宣言し、`#check five`・`#eval five`・`#print five`
   の表示をそれぞれ予想してから確かめよ。
2. `def oops : Bool := two` は受理されるか。予想してから試し、
   エラーメッセージを本文の例と見比べよ。
-/

/-! ## 3. 関数 {#sec-Intro1.functions}

集合 A・B に対して写像全体の集合 Map(A, B) が定まるのと同様に、
型 `A`・`B` に対して「`A` から `B` への関数の型」`A → B` が定まる
（矢印は `\to` と打つ）。つまり矢印 `→` は、**2つの型から新しい型を1つ作る
操作**を表す記号であって、それ自体が具体的な関数を定めるのではない。
ただし集合の場合と違い、`A → B` は写像概念から**定義されたものではない**——
関数型は、これ以上さかのぼれない原始的な部品である。

### fun 記法 — 関数を項として書く

関数そのもの（`A → B` 型の項）は、`fun` という記法で記述される項によって
定義できる: `fun x => e` は「`x` を受け取って `e` を返す関数」である。

この項の型は、次のように決まる。`fun x => e` を読むとき、Lean は
引数 `x` の型と本体 `e` の型を**同時に**検査する。`x` の型が `A` で、
そのもとで本体 `e` の型が `B` ならば、`fun x => e` は関数型 `A → B` の項になる。
「引数を仮に置いて、そのもとで本体を検査する」というこの形は、
含意 `p → q` の証明の形として `CH.lean` にそのまま現れる。

名前を付けて定義してみる:
-/

def double : Nat → Nat := fun n => n + n

#check double

/-!
    double : Nat → Nat

注釈した型が、そのまま `double` の型になっている。
`fun n => n + n` の `n` には型を書いていないが、注釈 `Nat → Nat` の
定義域から `n : Nat` と**推論**されている（`fun (n : Nat) => n + n` と
書いたのと同じ）。
-/

/-! ### 先取り（詳しくは Intro2）: `+` の仕組み

本体の `+`（[1節](#sec-Intro1.terms-types)で先取りした）は **notation（記法）**であり、
その意味は **class／instance** という仕組みで型ごとに決まっている
（正確な仕組みは `Intro2.lean` で説明する）。ここでは `Nat` に対して使っており、
ざっくり **`+ : Nat → Nat → Nat` という型の2引数関数**と思えばよい
（2引数の型の読み方はこの節の後半で）。
-/

/-!
この `def` を受理する前の型検査では、[2節](#sec-Intro1.definitions)と同じ照合が走っている。
コロンの右に注釈した型 `Nat → Nat` から「引数は `n : Nat`」と仮に置き、
そのもとで本体 `n + n` の型が行き先の `Nat` になるかを調べる。つまり
**`fun` 記法で書かれた項の型が、注釈した関数型と一致するか**が検査されている。

一致しなければ、もちろん受理されない。本体の型を間違えてみると:

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

関数を使うには、`double 21` のように**関数と引数を並べて**書く（括弧は不要）。
数学で「f(x)」と書くとき、私たちは f が関数で x がその定義域の元であることを
前提している。Lean の `f x` も同じ約束の記法で、
**`f` が関数型を持ち、`x` がその定義域の型を持つこと**を要求する。

実際 `double 21` と書くと、Lean は2つのことを確かめる:

1. `double` の型は `Nat → Nat`（関数型である）——定義域は `Nat`
2. `21` の型は `Nat`——定義域と一致する

この2点が通るから `double 21` は**合法な書き方**であり、
項 `double 21` の型は矢印の右側の `Nat` になる。
この確認こそが、型検査という機能の中身である。
-/

#eval double 21

/-!
    42
-/

/-! ### ✏ 練習（書く）

1. `def inc : Nat → Nat := fun n => …` の本体を埋めて、入力を1増やす関数を
   書け。`#check inc` の型と `#eval inc 4` の値を予想してから確かめよ。
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

1. `def triple (n : Nat) : Nat := n + n + n` を宣言し、`#check triple` の
   表示（binder 形式）を予想してから確かめよ。
2. `#eval double (double 5)` の値を予想してから実行せよ。
-/

/-! ### 多変数関数はカリー化で表す

Lean の関数はすべて1引数である。2引数の関数は、
「1つ目の引数を受け取ると、**残り1引数の関数を返す**」形（カリー化）で表す。
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

1. `plus 3 : Nat → Nat` を利用して、`def addThree : Nat → Nat := …` を
   書け。`#check addThree` と `#eval addThree 4` の表示を予想してから確かめよ。
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

/-! ### ✏ 練習（書く）

1. `F : Nat → Nat` を受け取り、入力 `n` に `F` を2回適用する
   `def twice (F : Nat → Nat) : Nat → Nat := …` を書け。
   `#check twice double` の型と `#eval twice double 3` の値を
   予想してから確かめよ。
-/

/-!
書き方の糖衣もまとめておく。次の3つは**まったく同じ宣言**である:

    def plus : Nat → Nat → Nat := fun a => fun b => a + b
    def plus : Nat → Nat → Nat := fun a b => a + b       -- fun は引数をまとめられる
    def plus (a b : Nat) : Nat := a + b                  -- binder 形式で書く

また `fun` の引数には、`fun n : Nat => e` のように括弧なしで型を注釈してもよい。
-/

/-- 3引数以上も同じことの繰り返し。
`Nat → Nat → Nat → Nat` は `Nat → (Nat → (Nat → Nat))` と読む。 -/
def addMul (a b c : Nat) : Nat := a + b * c

#check addMul

/-!
    addMul (a b c : Nat) : Nat

binder 形式の表示
-/

/-! ### 定義域や行き先が型でもよい

[1節](#sec-Intro1.terms-types)で「型も項である」と述べた。だから、**定義域や行き先が `Type` であるような
関数**も、まったく同じ書き方で作れる。例えば「2つの型 `A`・`B` を受け取り、
関数型 `A → B` を返す」関数:
-/

def Map : Type → Type → Type := fun A B => A → B

#check Map

/-!
    Map : Type → Type → Type

節の冒頭で「`A → B` は写像全体の集合 Map(A, B) と同じ役割を持つ」と述べたが、
その Map を、いま Lean の項として定義したことになる。`Map Nat Nat` は
計算すると `Nat → Nat` になるから、`double` は `Map Nat Nat` の項でもある
（練習で確かめよ）。「型を受け取る関数」「型を返す関数」は、
[6節](#sec-Intro1.dependent-functions)（依存関数型）でさらに主役になる。
-/

/-!
### `+` をあらためて

カリー化を知ったいま、`+` の型がちゃんと書ける:
**`+` はざっくり `Nat → Nat → Nat` という型の2引数関数**で、`3 + 4` は
`plus 3 4` と同じ形の適用を、中置の記法で書いたものである。
`*` も同様（ざっくり `Nat → Nat → Nat`）。数字 `3` はざっくり
「そのまま自然数の項」でよい（何も指定がなければ `Nat` と読まれる）。

「ざっくり」と断ったのは、正確には `+` も数字も**記法**であり、
「どの型の演算・どの型の数として読むか」が登録簿で決まる仕組みだからである。
その正確な仕組み（`HAdd`・`OfNat`）は `Intro2.lean` で説明する。
-/

/-! ### 型は部分項から機械的に計算できる

[2節](#sec-Intro1.definitions)で「型検査が走る」と述べ、この節の冒頭で `double 21` の2点確認を見た。
一般の形をまとめておく。適用についての規則はただ1つである:

    f : A → B　かつ　a : A　ならば　f a : B

この規則は、型の計算式であると同時に、**適用が合法かどうかの検査**でもある。
`f a` と書いてよいのは、`f` の型が矢印型 `A → B` であり、**かつ**引数 `a` の型が
その定義域 `A` と一致するときだけ。この2点を照合して初めて、
適用が合法だと分かり、結果の型 `B` が読み取れる。

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

そして、この手順にはひらめきも解釈も要らない——**完全に機械的**である。
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
（エラーの下にはさらに `double sorry : Nat` という表示も出る。`#check` は、
エラーになった引数を仮の穴 `sorry` で埋めた結果まで見せてくれるのである。）

では `double plus 3 4` と括弧なしで書いたらどうなるか。適用は左結合なので
これは `((double plus) 3) 4` と読まれ、最初の `double plus` の時点で
上と同じエラーになる。`double (plus 3 4)` の括弧は省略できない。
-/

/-! ### ✏ 練習

1. `#check` する**前に**型を計算せよ: `(3 + 4) * 2`、`plus (double 3)`、
   `applyTo21 (plus 3)`、`fun n : Nat => plus n n`。それから確かめよ。
2. `#eval applyTo21 (plus 100)` の値を予想してから実行せよ。
3. 次の2つの関数を定義し、`#check` で型を確かめよ:
   * `evalAt` — 関数 `F : Nat → Nat` と数 `x : Nat` を受け取り、`F x` を返す。
     定義できたら `#eval evalAt double 5` の値を予想してから実行せよ。
   * `shift` — 関数 `F : Nat → Nat` を受け取り、「`x` に対して `F (x + 1)` を
     返す関数」を返す（関数を受け取って**関数を返す**関数である）。
     定義できたら `#eval shift double 3` の値を予想してから実行せよ。
4. `#check Map Nat Bool` の表示を予想してから確かめよ。また
   `def double2 : Map Nat Nat := double` が通るかどうか試せ
   （`Map Nat Nat` は計算すると `Nat → Nat` になる）。
5. 「型から項を書く」練習: `(Nat → Nat) → Nat` という型を持つ項を、
   **中身の違うもので2つ**書け（例えば「21 に適用する」と「関数を無視して
   `0` を返す」）。`def useF1 : (Nat → Nat) → Nat := …` の形で宣言し、
   `#check` で型を確かめよ。同じ型に項は何通りもある——型は仕様であって、
   中身までは決めない。
6. （発展）合成関数 `compose (A B C : Type) (G : B → C) (F : A → B) : A → C` を
   書け（数学の G ∘ F。返すのは「`a` を受け取って `G (F a)` を返す関数」である）。
   `#eval compose Nat Nat Nat double (fun n => n + 1) 3` の値を予想してから
   確かめよ。
7. （発展）練習 3 の `evalAt` と `shift` を、`Nat` 限定でなく**どんな型でも**
   使えるように一般化せよ: `evalAt' (A B : Type) (F : A → B) (x : A) : B` と、
   ずらし方も引数にした `shift' (A : Type) (g : A → A) (F : A → A) : A → A` である。
   `#eval evalAt' Nat Nat double 5` と `#eval shift' Nat (fun x => x + 1) double 3`
   が元の版と同じ値になることを確かめよ。
-/

/-! ## 4. 帰納型（inductive type） {#sec-Intro1.inductive-types}

型を作る部品の1つ目が、帰納型である。帰納型は**構成子（constructor）のリスト**で
型を定義する。構成子とは「その型の項の**作り方**」のことで、
帰納型の項は、構成子で作られたものが**すべて**である。
集合のアナロジーで先に言っておくと、帰納型は**直和や直積**にあたるものを
一挙に作れる部品である（節の中で順に見る）。

いちばん単純なのは、構成子がどれも引数を取らない**列挙型**である。
-/

inductive Signal where
  | red
  | yellow
  | green

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
この宣言の意味は「`Signal` の項は `Signal.red`, `Signal.yellow`, `Signal.green` の
3つが**すべて**であり、それ以外にはない」ということ。構成子の正式な名前は
`型名.構成子名` になる（[1節](#sec-Intro1.terms-types)の `Bool.true` はこれだった）。
作り方を列挙したら、それで型が決まる。集合のアナロジーでは、列挙型は
3点集合 {red, yellow, green} のような**有限集合**である。

もう1つ、対になる保証がある: この3つは互いに**別のもの**である
（`Signal.red` と `Signal.green` が実は同じだった、ということは起きない。
`MyNat` のような引数つきの構成子では「中身が違えば違う」まで含む）。
「作れるものが全部」と「違う作り方のものは別々」の2つが合わさって、
はじめて `Signal` は本当に3点集合になる。この2つは約束ではなくどちらも
**証明できる事実**であり、しかも証明の道具は宣言を受理したときに Lean が
自動で用意する——実物は [`CH.lean` 9節](#sec-CH.nat-proofs)で見る。

「それ以外にない」からこそ、場合分け（`match`）が正当化される。
これが帰納型の項の使い方である。`fun` で受け取った `s` を、
`match s with` で場合分けする:
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

計算結果を見たいが、ここでは `#eval` が使えない——`#eval` は値の表示の仕組み
（`Repr`）が登録された型でしか使えず、いま作ったばかりの `Signal` には
登録がないからである。こういうときは `#reduce`——項を計算して、
**構成子の形**で表示するコマンド——が使える:
-/

#reduce next Signal.red

/-!
    Signal.green

たしかに赤の次は青になった。

期待される型が分かっている位置では、`Signal.red` を `.red` と省略できる
（この省略の仕組みは[7節](#sec-Intro1.dot-notation)のドット記法で説明する）。まず練習で試し、
そのあと本文でも省略形を使う。
-/

/-! ### ✏ 練習（書く）

1. `Signal.red`・`Signal.yellow`・`Signal.green` をそれぞれ `0`・`1`・`2` に
   送る `signalCode : Signal → Nat` を `match` で書け。各枝の結果が同じ型に
   なることを確かめ、`#eval signalCode Signal.yellow` の値を予想してから実行せよ。
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
   `#reduce prev (next Signal.red)` の表示を予想してから確かめよ
   （`Signal.red` に戻ってくるはずである）。
2. `isRed` にならって `isGreen : Signal → Bool` を書き、
   `#eval isGreen Signal.red` の値を予想してから確かめよ。
-/

/-!
`Bool` はまさにこの形の列挙型で、標準ライブラリ（Prelude）では
次のように定義されている:

    inductive Bool : Type where
      | false : Bool
      | true : Bool

なお `inductive Signal where` は結果の型を省略した書き方で、正確には
`inductive Signal : Type where` の略である。ここを `: Prop` にすれば
**命題**を帰納型として作ることもできる（[`CH.lean` 5節](#sec-CH.empty-types)で見る）。

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

inductive NatOrBool where
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

    inductive NatOrBool where
      | nat : Nat → NatOrBool
      | bool : Bool → NatOrBool

`NatOrBool` の項は「`nat` の札が付いた自然数」か「`bool` の札が付いた真偽値」の
どちらか。集合のアナロジーでは、`NatOrBool` は `Nat` と `Bool` の
**直和（非交和）**と思える。場合分けで札を見分け、中身を取り出す:
-/

def valueOf : NatOrBool → Nat := fun x =>
  match x with
  | .nat n => n
  | .bool _ => 0

#check valueOf

/-!
    valueOf : NatOrBool → Nat

2つ目の枝のパターンに書いた `_` は、「この場合分けでは中身を**使わない**ので
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
   （どちらの枝に入るか）。
2. 「`bool` の札なら中身を、`nat` の札なら `false` を返す」関数
   `flagOf : NatOrBool → Bool` を書き、`#eval flagOf (NatOrBool.bool true)` で
   確かめよ。
-/

/-!
### 型をパラメータにする

次の段階として、包む中身の型そのものをパラメータ `(α β : Type)` にできる:
-/

inductive MySum (α β : Type) where
  | inl (a : α) : MySum α β
  | inr (b : β) : MySum α β

#check MySum

/-!
    MySum (α β : Type) : Type

binder 形式を読み替えれば `MySum : Type → Type → Type`——[3節](#sec-Intro1.functions)の `Map` と
同じ形の「型を受け取って型を返す関数」でもある
（ギリシャ文字は `\a` `\b` で打てる）。

構成子 `inl` の型はどうなるか。`NatOrBool.nat` からの類推では
`α → MySum α β` だが、今度は `α`・`β` 自身も決まらないと使えないはずである:
-/

#check MySum.inl

/-!
    MySum.inl {α β : Type} (a : α) : MySum α β

推測した引数 `(a : α)` に加えて、パラメータの分の引数 `{α β : Type}` が
先頭に付いた。波括弧は「文脈から自動で埋まる引数」の印である（[6節](#sec-Intro1.dependent-functions)で説明する）。
よく見るとこの型は、**引数 `α` の値が後ろの引数の型に現れる**——[6節](#sec-Intro1.dependent-functions)で主役になる
依存関数型の、最初の実物である。
-/

/-!
`MySum α β` の項は、「`α` の項に `inl` の札を付けたもの」か
「`β` の項に `inr` の札を付けたもの」のどちらか。集合のアナロジーでは
**直和** α ⊔ β である——`NatOrBool` は `MySum Nat Bool` に相当する
（`CH.lean` に出てくる `⊕` は、標準ライブラリにあるこれと同じ型）。
-/

def fromSum : MySum Nat Bool → Nat := fun x =>
  match x with
  | .inl n => n
  | .inr _ => 0

#check fromSum

/-!
    fromSum : MySum Nat Bool → Nat
-/

/-! ### ✏ 練習（書く）

1. `MySum Bool Bool` の左右どちらの札からも、中身の `Bool` をそのまま返す
   `mergeBool : MySum Bool Bool → Bool` を書け。
   `#eval mergeBool (MySum.inl true)` と
   `#eval mergeBool (MySum.inr false)` を予想してから確かめよ。
-/

/-!
ここで書き方を一般に述べておく: **帰納型からの関数は `match` で書く**。
枝は構成子ごとに1本ずつで、全部の枝を与えれば関数が1つ決まる。

集合のアナロジーの側でこれに当たるのは、**直和の普遍性**である:
直和 α ⊔ β からの写像を与えることは、α からの写像と β からの写像を
1本ずつ与えることにほかならない。`fromSum` では `inl` の枝が
「α = Nat からの写像」（中身をそのまま返す）、`inr` の枝が
「β = Bool からの写像」（`0` を返す）に当たる。`Signal` のような列挙型で
「各点の行き先を1つずつ指定する」のも、1点集合の直和と思えば同じ形である。
`match` の書式を見たら、直和の普遍性を連想してほしい。
-/

/-! CALLOUT_START preview -/
/-! ### 先取り（[6節](#sec-Intro1.dependent-functions)）: 暗黙引数を使う汎用版

取り出す側も、パラメータを持たせて一般的に書ける。次の `getLeft` は
「既定値 `d` を受け取り、左の札なら中身を、右の札なら `d` を返す」関数で、
`fromSum` はその `Nat`・`Bool`・`0` への特殊化に当たる
（`{α β : Type}` という波括弧の意味は[6節](#sec-Intro1.dependent-functions)でまとめて説明する。ここでは
「どんな型の組でも使える」という印と読めばよい）:
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

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat

/-!
    MyNat : Type
-/

/-!
`MyNat` の項は、`zero` に `succ` を有限回適用したものがすべて。
列挙型と違って項は無限にあるが、どの項も**有限の手順**で作られている。
だから場合分けに加えて、構造が小さくなる方向への**再帰**が正当化される。
-/

/-! ### 補足（初読は飛ばしてよい）: 集合の方程式としての再帰

集合のアナロジーでは、`MyNat` は方程式

    X ≅ 1 ⊔ X   （zero の分の1点 ⊔ succ の引数の分）

を満たす**最小**の集合と読める。右辺に自分自身が現れるのが再帰の印で、
最小性は「`zero` に `succ` を有限回重ねたものがすべてで、それ以外にない」
ということの言い替えである。
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
`add` の計算も `#reduce` で確かめられる。「1 + 1」に当たる
`add (.succ .zero) (.succ .zero)` を読んでみよう。`match` の2つ目の枝から
`add m (succ zero) = succ (add m zero)`、さらに1つ目の枝から `add m zero = m`。
だから値は `succ (succ zero)`、つまり「2」のはずである:
-/

#reduce add (.succ .zero) (.succ .zero)

/-!
    MyNat.zero.succ.succ

`MyNat.zero.succ.succ` は `MyNat.succ (MyNat.succ MyNat.zero)` のこと
（値の後ろにドットで関数をつなぐ表示——仕組みは[7節](#sec-Intro1.dot-notation)のドット記法で見る）。
たしかに `succ` が2回重なった項、つまり「2」が返ってきた。
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
2. 2点の列挙型 `inductive Two where | a | b` を定義せよ。`Two` と `Bool` は
   集合としては同じ2点集合だが、型としては別物である。往復の関数
   `toBool : Two → Bool` と `ofBool : Bool → Two` を書き、
   `#eval toBool (ofBool true)` を確かめよ（`Bool` は表示の仕組みが
   登録済みなので `#eval` が使える）。
3. `Two → Bool` の関数は、集合のアナロジーで数えると 2 × 2 = 4 通り
   あるはずである。その4つすべてを `def g1 : Two → Bool := …` から `g4` まで
   書け（前問の `toBool` はその1つ）。有限型の間の関数を書くことは、
   **値の対応表を書くこと**にほかならない。
4. （発展）掛け算 `mul : MyNat → MyNat → MyNat` を、本文の `add` の再帰に
   ならって書け（`m × 0 = 0`、`m × (k + 1) = m × k + m` を写す:
   `.zero` の枝は `.zero`、`.succ k` の枝は `add (mul m k) m`）。
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
「成分をまとめて持ち運ぶ入れ物」としてよく使う。まず、ふつうの帰納型として書いてみる。
-/

inductive MyPoint where
  | mk (x y : Nat) : MyPoint

#check MyPoint

/-!
    MyPoint : Type
-/

/-!
項の作り方は `MyPoint.mk 1 2` の一通りしかない。だから場合分けは常に1ケースで、
成分を取り出す関数がすぐに書ける。
-/

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | .mk a _ => a

#check MyPoint.x

/-!
    MyPoint.x : MyPoint → Nat

帰納型の項の使い方はいつでも `match` である——構成子が1つなら、
場合分けが1ケースになるだけで、原理は [4節](#sec-Intro1.inductive-types)と変わらない。
（`⟨ ⟩` は `\<` `\>` で打てる。）
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

structure Point where
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
`⟨1, 2⟩` は `Point.mk 1 2` の略記である
-/

#check Point.x

/-!
    Point.x (self : Point) : Nat

自動定義された取り出し関数。矢印形式では `Point → Nat`。
`p.x` とも書ける——[7節](#sec-Intro1.dot-notation)
-/

#eval (Point.mk 1 2).x

/-!
    1

第1フィールドに入れた値が、そのまま返ってきた。
-/

/-! ### ✏ 練習（書く）

1. `Point` の第1成分だけを1増やす `moveRight : Point → Point` を書け。
   成分の取り出しには `Point.x`・`Point.y`、作成には `Point.mk` を使う。
   `#eval Point.x (moveRight (Point.mk 1 2))` の値を予想して確かめよ。
-/

/-! ### ✏ 練習

1. 次の structure を定義し、`#check` で構成子と取り出し関数が
   自動定義されていることを確かめよ:

       structure Circle where
         center : Point
         radius : Nat

2. `#eval Point.y (Point.mk 1 2)` の値を予想してから確かめよ。
   さらに `(Point.mk 1 2).y` とも書けることを試せ（[7節](#sec-Intro1.dot-notation)のドット記法の先取り）。
3. フィールドの型は、自作の structure でもよい。長方形

       structure Rect where
         corner : Point
         width : Nat
         height : Nat

   を定義し、`def r : Rect := ⟨⟨1, 2⟩, 10, 5⟩` が受理されることを確かめよ
   （`⟨ ⟩` の入れ子が `corner : Point` の分である）。`#eval r.corner.x` の
   値を予想してから確かめよ（後ろドットの入れ子。これも[7節](#sec-Intro1.dot-notation)の先取り）。
-/

/-!
structure は引数（パラメータ）を取ることもできる。
-/

structure Pair (α β : Type) where
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
集合のアナロジーでは、`Point` は直積 Nat × Nat、`Pair α β` は直積 α × β である。
つまり structure は「**直積の各成分に名前を付けたもの**」と思ってよい。
実際、標準ライブラリの `×` 自身が `fst`/`snd` という2フィールドの
structure（名前は `Prod`）として定義されている。
-/

/-! ### 補足（初読は飛ばしてよい）: 帰納型を直和と直積で見る

前節の直和とここの直積をまとめると、帰納型の一般形は集合の言葉でこう読める:

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

もう1つ一般化がある: 後のフィールドの型は、前のフィールドに**依存してよい**。
[1節](#sec-Intro1.terms-types)で見たとおり型も項だから、フィールドの値として**型そのもの**を持たせ、
次のフィールドの型をその値で決める、ということができる:
-/

structure PointedType where
  carrier : Type
  point : carrier

/-!
「型 `carrier` と、その要素 `point`」の組——数学でいう**点付き集合**である。
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
（`pointedNat` では `point : Nat`）。なお `#check PointedType` とすると
`PointedType : Type 1` と表示される——中身に `Type` の項を入れたので、
入れ物は[1節](#sec-Intro1.terms-types)で見た `Type : Type 1` の1段上になるのである。
-/

/-! ### 補足（初読は飛ばしてよい）: 依存するフィールドと族の直和

集合のアナロジーもここで1段更新される。フィールドが依存しない範囲では
「structure は直積」だったが、依存を許した一般形が作るのは**族の直和**
（非交和）である:

    ⊔_{a ∈ A} B(a) —— 「a を1つ選び、それに応じた B(a) の要素を1つ添える」組の全体

`PointedType` はまさにこの形——「型を1つ選ぶごとに、その型自身（の要素の集まり）が
対応する」という族の直和である。そして族 B(a) が a によらない定数 B のときは
⊔_{a ∈ A} B = A × B となって、直積に戻る。つまり structure は
**基本は直積、一般には族の直和**を作るもので、直積はその特別な場合
（定数族の直和）なのである。

この「後の成分が前の成分に依存する組」の一般論は、[`CH.lean` の7節](#sec-CH.dependent-sums)（依存和）で
扱う。特に、第二成分を**命題の証明**にしたもの（部分型）はそこで主役になり、
`Top.lean` でも「分離データの束」`SeparatingPair` として活躍する。
命題の話なので、ここではこれ以上踏み込まない。
-/

/-! ### ✏ 練習

1. `#check Pair.mk true 0` の表示を予想してから確かめよ
   （`α`・`β` は何に決まるか）。
2. `def pointedBool : PointedType := ⟨Bool, true⟩` が受理されることを確かめよ。
   また `#check PointedType.mk Nat` の表示を予想してから確かめよ
   （第1引数を渡すと、第2引数の型が決まる）。
3. （発展）[3節](#sec-Intro1.functions)の「カリー化」の正体を自分で書く。組を受け取る関数を
   「1つずつ受け取る」形に直す
   `curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat` と、その逆向き
   `uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat` を書け。
   `#eval curryP (fun p => p.fst + p.snd) 3 4` の値を予想してから確かめよ。
-/

/-! ## 6. 依存関数型 {#sec-Intro1.dependent-functions}

関数の一般化がもう1段ある。**行き先の型が、入力に応じて変わってよい**とした
関数——依存関数——である。いちばん簡単な例は「型そのものを最初の引数として
受け取る」形で作れる。型が引数にできることは、[3節](#sec-Intro1.functions)の `Map` で見たとおりである。
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

/-! ### 補足（初読は飛ばしてよい）: 依存関数型と集合族の直積

集合のアナロジーでは、依存関数型は**集合族の直積** ∏ にあたる
（各点 `a` ごとに「行き先の集合」から要素を1つずつ選ぶ選び方、と読める）。
-/

/-!
なお、この「型を渡してから使う」仕組みこそ多相性の正体で、これまでも表示に
顔を出してきた暗黙引数 `{α : Type}`（すぐ下でまとめる）は、この第1引数を
文脈から自動で埋めてもらう書き方である。
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

ここで、`#check` が表示する型の読み方をまとめておく。例えば

    Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β

は、コロンの左に引数の列が並び、最後の `: Pair α β` が結果の型、と読む
（[3節](#sec-Intro1.functions)で見た binder 形式である）。引数を1つ渡すたびに列の左から1つ消えていき、
全部渡すと結果の型の項が得られる。そして各段階で「渡した項の型が、引数の型と
一致するか」の型検査が走っている。[2節](#sec-Intro1.definitions)からやってきたことの一般形である。

引数を包む括弧は、「その引数を**誰が埋めるか**」を表している。

* `(fst : α)` — **明示引数**。使う側が自分で書く。
* `{α : Type}` — **暗黙引数**。使う側は書かない。Lean が読み込みの段階で、
  他の引数とのつじつま合わせ（単一化）から埋める（この前処理を
  **エラボレーション**と呼ぶ。型検査との関係は [`CH.lean` 10節](#sec-CH.type-checking)で整理する）。
  `Pair.mk 1 true` と書けば `1 : Nat` と `true : Bool` から
  `α := Nat`、`β := Bool` が決まる。

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

/-! ### ✏ 練習

1. `#check Map Nat` の表示を予想してから確かめよ
   （`Map` に1つだけ渡すと、何が返るか）。
-/

/-! ## 7. ドット記法 {#sec-Intro1.dot-notation}

`CH.lean` の証明では、`h.1` や `.inl` のようなドットの略記が頻繁に使われる。
向きの違う2つの用法があるので、まとめて押さえておく。

**値の後ろに付けるドット**: `p : Point` に対して `p.x` と書くと、Lean は
「`p` の型の名前 `Point` を接頭辞に持つ関数 `Point.x` を探し、`p` を最初の
`Point` 型の引数として渡す」と解釈する。つまり `p.x` は `Point.x p` の略記。
自動生成されるフィールドに限らず、`Point.〜` という名前の関数なら何でも使える
（`型名.関数名` という名前の仕組みの一般論——名前空間——は `Intro2.lean` で扱う）。
-/

/-- 成分を入れ替える関数。名前を `Point.swap` にした。 -/
def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

/-!
確認してみる。後ろに付けるドットは、名前空間の関数の適用の略記にすぎない:
-/

#eval (Point.mk 1 2).swap.x

/-!
    2

`swap` で `x` と `y` が入れ替わった。フルネーム版の
`#eval (Point.swap (Point.mk 1 2)).x` でも、同じ `2` が返る。

フィールドは番号でも取れる。`.1` `.2` は第1・第2フィールドの略記で、
`(Point.mk 1 2).1` は `(Point.mk 1 2).x` と同じものである
（名前を覚えていなくても位置で取れる、という略記）:
-/

#eval (Point.mk 1 2).1

/-!
    1
-/

#eval (Pair.mk 1 true).2

/-!
    true
-/

/-!
[4節](#sec-Intro1.inductive-types)の `#reduce` の表示 `MyNat.zero.succ.succ` も、この「値の後ろに付けるドット」の
連鎖だった（`.succ` は `MyNat.succ` の略記で、`MyNat.zero` に2回適用されている）。

**型が分かっている場所で前に付けるドット**: 期待される型が `Point` だと
分かっている位置では、構成子 `Point.mk` を `.mk` と省略できる。
今度は「**期待される型**の名前空間から探す」という解決である。
[4節](#sec-Intro1.inductive-types)のパターンマッチで使った `.red` や `.succ` もこの用法で、
`match` の各ケースは `Signal.red` などの略記だった。
-/

example : Point := .mk 1 2

/-! ### ✏ 練習（書く）

1. `Point.zeroX (p : Point) : Point` を定義し、第1成分だけを `0` にせよ。
   本体では `p.y` と `.mk` の両方を使う。`#eval (Point.mk 1 2).zeroX.x`
   の値を予想して確かめよ。
-/

/-!
証明でもこの記法が多用される。`CH.lean` では `h.1`・`h.elim`、`Top.lean` では
`hK : IsCompact K` に対する `hK.image hf`（＝ `IsCompact.image hK hf`）の
ような形で登場する。

これで `CH.lean` を読む準備が整った。`CH.lean` のあとは `Intro2.lean` →
`Top.lean` と進んでほしい。
-/

/-! ### ✏ 練習

1. `#eval (Point.mk 1 2).swap.swap.x` の値を予想してから確かめよ
   （2回入れ替えると元に戻るはずである）。またこの式を、ドットを使わず
   フルネームの適用だけで書き直すと何になるか、紙に書いてから `#eval` で
   一致を確かめよ。
2. `example : Point := .mk 1 2` にならって、`example : Signal := .red` が
   通ることを確かめよ（前ドットが「期待される型」から解決されている）。
-/

/-! ## 8. まとめ練習 — 小さな型つき言語で書く {#sec-Intro1.exercises}

ここまでの部品——`fun` と適用、`match`、`inductive`、`structure`、
型を引数に取る関数——だけで、Lean は小さな**型つきプログラミング言語**として
使える。仕上げに、**型を仕様書として読み、それに合う項を書く**総合練習を置く。

どの問題も、書いたら `#check` で型を、`#eval` で値を、機械に答え合わせ
させること。行き詰まったら、まず矢印の形に合わせて `fun` の引数を並べ、
返すべきものの型を確かめるとよい——**型が設計図である**。
-/

/-! ### ✏ 練習

1. 引数の順序を入れ替える `flipNat (F : Nat → Nat → Nat) : Nat → Nat → Nat`
   （`flipNat F a b` が `F b a` になる）を書け。
   `#eval flipNat (fun a b => a - b) 3 10` の値を予想してから確かめよ。
2. `iterate3 (F : Nat → Nat) : Nat → Nat`（`F` を3回適用する関数を返す）を
   書け。`#eval iterate3 double 1` の値を予想してから確かめよ。
3. `boolToSignal : Bool → Signal`（`true` は `.green` に、`false` は `.red` に
   送る）と、`signalToBool : Signal → Bool`（`.green` のときだけ `true`）を
   書け。`#eval signalToBool (boolToSignal true)` を確かめよ。
4. 両成分に同じ関数を適用する `mapPoint (F : Nat → Nat) (p : Point) : Point` を
   書け。`#eval (mapPoint double (Point.mk 2 3)).y` の値を予想してから確かめよ。
5. 札を掛け替える `swapMySum (A B : Type) : MySum A B → MySum B A` を書け。
   `#eval fromSum (swapMySum Bool Nat (MySum.inl true))` の値を予想してから
   確かめよ（`fromSum : MySum Nat Bool → Nat` は[4節](#sec-Intro1.inductive-types)で定義した）。
6. `pointedOf (A : Type) (a : A) : PointedType` を書け（[5節](#sec-Intro1.structures)の `pointedNat` や
   練習の `pointedBool` を、どの型でも作れるように一般化したもの）。
   `#check pointedOf Bool true` の表示を予想してから確かめよ。
7. （発展）回数も引数にした
   `applyN (A : Type) (F : A → A) (n : Nat) (a : A) : A`（`F` を `n` 回適用）を
   書け。`n` の `match` は `| 0 => …`・`| k + 1 => …` の形（[4節](#sec-Intro1.inductive-types)の練習の
   `ofN` と同じ）。`#eval applyN Nat double 3 1` の値を予想してから確かめよ。
8. （発展）型だけで中身がほぼ決まる例: `diag (A : Type) (a : A) : Pair A A` を
   書け。この型に合う項は、実質1通りしか書きようがない——書いたうえで
   `#eval (diag Nat 3).fst` を確かめよ。[3節](#sec-Intro1.functions)の練習（`(Nat → Nat) → Nat` の項を
   2つ書く）とは対照的に、**型が中身をどこまで決めるかは型の形による**のである。
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
