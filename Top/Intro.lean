/-!
# Lean 最小限の導入

この教材（Intro → CH → Top の3ファイル）の目標は2つある。

* **目標1 — Lean を読めるようになる**。Lean のコードを読むとは、書かれた
  **項の型を推測する**ことである。そしてこの推測は**機械的な手順**で実行できる
  ——だからコンピュータにも実行できる。実際に自分の手で型を推測できるように
  なること、少なくとも「これなら機械にもできそうだ」という感覚を持つことを目指す。
* **目標2 — 検証の仕組みを納得する**。項の型を推測するこの仕組みが、
  **定理の証明の検証にそのまま使える**ことを納得する。「なぜそれで証明の正しさを
  検証したと思えるのか」への答えがここにある。

目標1が主にこのファイル（Intro）の、目標2が `CH.lean` の担当で、
`Top.lean` では現物の数学（位相空間の主定理）について両方を実感する。
Lean を網羅的に紹介することは目的ではなく、そのために必要な
最低限の機能しか説明しない。

このファイルで伝えたいことは2つ。

* Lean のもっとも基本の要素は**項**と**型**である。
  Lean に書くことはすべて「項 `a` は型 `α` を持つ」（`a : α` と書く）の組み立てである。
* 型を作る部品は実質2つ、**帰納型**（inductive type）と**依存関数型**である。
  ふだん目にする `→` `×` `structure` などは、すべてこの2つの現れである。

なお、このファイルは**型の世界**に集中する。命題と証明の世界は、
1節で顔だけ見せたあとは極力持ち込まず、`CH.lean` でまとめて扱う。

### この教材の読み方

中心的な練習は、**書かれたコードを解読すること**である。その基本動作が
「与えられた項の型を推測する」こと。そこで以後、項を書くたびに
「この項の型はこうなるはずだ」とまず推測し、`#check` で答え合わせをする、
というプロセスを繰り返す。読者も、出力の枠を読む前にいったん止まって、
自分の推測を立ててから確かめてほしい。この積み重ねの先で、
同じ仕組みがそのまま証明の検証になる（目標2、`CH.lean`）。

各節末の ✏ 練習で手を動かすのも、書ける人になるためではなく、
**読みの検算**のためである——予想を立てて、機械に答え合わせをさせるための
最小限の写経だと思ってほしい（コードを書く仕事は、AI に任せてよい）。

### 補足: 記号の入力のしかた

Lean のコードには `→` `⟨` `⟩` `∀` のような記号が多く出てくる。VS Code の
Lean 4 拡張では、**バックスラッシュ `\` で始まる略記**を打つと記号に変換される。
例えば `\to` と打って、続けて空白などを打つ（または Tab を押す）と `→` になる。
よく使うものだけ挙げておく:

| 記号 | 打ち方 |
|---|---|
| `→` | `\to` または `\r` |
| `×` | `\times` または `\x` |
| `⟨` `⟩` | `\<` と `\>`（`\<>` で両方いっぺんに出る） |
| `α` `β` `γ` | `\a` `\b` `\g` |
| `∀` ／ `∃` | `\all` ／ `\ex` |
| `∧` ／ `∨` ／ `¬` | `\and` ／ `\or` ／ `\not` |
| `∈` ／ `∪` ／ `∩` ／ `∅` | `\in` ／ `\cup` ／ `\cap` ／ `\empty` |
| `≠` | `\ne` |

すべて覚える必要はない。**エディタ上の記号にマウスを乗せると、その記号の
打ち方がポップアップに表示される**ので、真似したい記号に出会ったら
ホバーして確かめればよい。
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
この命名の仕組みは4節で見る）。

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

`Prop` は**命題**たちの住む宇宙である（このファイルでは深入りしない。
`CH.lean` の主題である）。

型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（3節の `Map` と7節）。

### 先取り: 演算と命題の記号

数の演算や、等式・不等式の記号も、ふつうに書ける。それぞれが正確には何者なのかは
後で説明することにして（`+` は3節。`=` と `<` はこのファイルでは深入りせず、
`CH.lean` で主役になる）、表示だけ先に見ておく。
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
（真偽と証明の話は `CH.lean` で）。

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

宣言に `: Nat` と書いたのだから型は `Nat` のはずで、表示もそのとおりである。
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

本体に出てきた `+`（1節で先取りした）について一言だけ注意しておく。
`+` は **notation（記法）**であり、その意味は **class／instance** という仕組みで
型ごとに決まっている（仕組みは6節で説明する）。ここでは `Nat` に対して
使っており、「2つの `Nat` から `Nat` を作る演算」と思えばよい。

この `def` を受理する前の型検査では、2節と同じ照合が走っている。
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

#eval double 21

/-!
    42
-/

/-- 引数を左に書く糖衣構文。上の `double` と同じもの。 -/
def double' (n : Nat) : Nat := n + n

#check double'

/-!
    double' (n : Nat) : Nat

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
書き方の糖衣もまとめておく。次の3つは**まったく同じ宣言**である:

    def plus : Nat → Nat → Nat := fun a => fun b => a + b
    def plus : Nat → Nat → Nat := fun a b => a + b       -- fun は引数をまとめられる
    def plus (a b : Nat) : Nat := a + b                  -- binder 形式で書く
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

1節で「型も項である」と述べた。だから、**定義域や行き先が `Type` であるような
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
7節（依存関数型）でさらに主役になる。
-/

/-!
### `+` をあらためて: ざっくり版と正確な版

カリー化を知ったいま、`+` にちゃんとした型が与えられる。以後、
裏に仕組みのあるものには**ざっくり**版と**正確には**版を併記する
（正確な版は初読では飛ばしてよい）。

* `+` — **ざっくり**: `Nat → Nat → Nat` という型の2引数関数で、
  `3 + 4` は `plus 3 4` と同じ形の適用を、中置の記法で書いたもの。
  **正確には**: `+` の読み先は汎用の演算 `HAdd.hAdd` で、「どの型の足し算か」は
  登録簿（6節の instance）から決まる。それを `Nat` に特殊化した姿がざっくり版である。
* 数字 `3` — **ざっくり**: そのまま自然数の項。
  **正確には**: 数字も記法であり、期待される型に応じて読み方が決まる
  （仕組みは6節、実例は7節の補足で見る）。何も指定がなければ `Nat` と読まれる。
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

そして、この手順にはひらめきも解釈も要らない——**完全に機械的**である。
だからコンピュータに実行させることができ、実際にそれをやっているのが
Lean の型検査器である。読者がこの教材で行う「型の推測」は、
機械のこの手順を暗算でなぞることに他ならない（目標1）。

1節の `3 + 4 : Nat` も、ざっくり版の `+ : Nat → Nat → Nat` を使えば
同じ手順で確かめられる。そして以後に出てくる `#check` の表示は**すべて**、
「宣言された型」と「この規則」だけで、同じように自分の手で検算できる。
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

「引数の型 `Nat → Nat → Nat` が、要求される型 `Nat` と合わない」と、
規則が破れた部分項を名指しで教えてくれる。
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
5. （発展）前問の `evalAt` と `shift` を、`Nat` 限定でなく**どんな型でも**
   使えるように一般化せよ: `evalAt' (A B : Type) (F : A → B) (x : A) : B` と、
   ずらし方も引数にした `shift' (A : Type) (g : A → A) (F : A → A) : A → A` である。
   `#eval evalAt' Nat Nat double 5` と `#eval shift' Nat (fun x => x + 1) double 3`
   が元の版と同じ値になることを確かめよ。
-/

/-! ## 4. 帰納型（inductive type）

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
（この省略の仕組みは8節のドット記法で説明する）。以後は省略形も使う:
-/

def isRed : Signal → Bool
  | .red => true
  | .yellow => false
  | .green => false

#check isRed

/-!
    isRed : Signal → Bool
-/

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

実は同じことが `Prop` の世界でもできて、命題の `True` と `False` は
帰納型として定義されている。命題の世界の帰納型の話は、このファイルでは
扱わず `CH.lean`（4節）でまとめて見る。

### 構成子は引数を取れる

構成子に引数を持たせると、データを包む型が作れる。構成子の引数は、
`def` と同じくコロンの左に書ける（3節の binder 形式）:
-/

inductive NatOrBool where
  | nat (n : Nat) : NatOrBool
  | bool (b : Bool) : NatOrBool

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

def valueOf : NatOrBool → Nat
  | .nat n => n
  | .bool _ => 0    -- `_` は「この場合分けでは中身を使わない」という印

#check valueOf

/-!
    valueOf : NatOrBool → Nat
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

構成子 `inl` の型はどうなるか。`NatOrBool.nat` からの類推では
`α → MySum α β` だが、今度は `α`・`β` 自身も決まらないと使えないはずである:
-/

#check MySum.inl

/-!
    MySum.inl {α β : Type} (a : α) : MySum α β

推測した引数 `(a : α)` に加えて、パラメータの分の引数 `{α β : Type}` が
先頭に付いた。波括弧は「文脈から自動で埋まる引数」の印である（6節で説明する）。
-/

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
    fromSum : MySum Nat Bool → Nat
-/

/-!
取り出す側も、パラメータを持たせて一般的に書ける。次の `getLeft` は
「既定値 `d` を受け取り、左の札なら中身を、右の札なら `d` を返す」関数で、
`fromSum` はその `Nat`・`Bool`・`0` への特殊化に当たる
（`{α β : Type}` という波括弧の意味は6節でまとめて説明する。ここでは
「どんな型の組でも使える」という印と読めばよい）:
-/

def getLeft {α β : Type} (d : α) : MySum α β → α
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
    add : MyNat → MyNat → MyNat
-/

/-!
`add` の計算も `#reduce` で確かめられる。「1 + 1」に当たる
`add (.succ .zero) (.succ .zero)` を読んでみよう。定義の2行目から
`add m (succ zero) = succ (add m zero)`、さらに1行目から `add m zero = m`。
だから値は `succ (succ zero)`、つまり「2」のはずである:
-/

#reduce add (.succ .zero) (.succ .zero)

/-!
    MyNat.zero.succ.succ

`MyNat.zero.succ.succ` は `MyNat.succ (MyNat.succ MyNat.zero)` のこと
（値の後ろにドットで関数をつなぐ表示——仕組みは8節のドット記法で見る）。
たしかに `succ` が2回重なった項、つまり「2」が返ってきた。

標準ライブラリの型はほとんどすべて帰納型である。
`Bool` `Unit` `Empty`（上で引用した）、`Nat`（リテラル `3` は
`succ (succ (succ zero))` の表示）、`CH.lean` に出てくる `×` `⊕`、
さらには命題の側の `And` `Or` `Eq` すらもそうなのだが、命題の話は
`CH.lean` に譲る。

`Top.lean` では、`Nat` の再帰で集合の有限個の共通部分 `interFin` を定義し、
その性質もまた再帰で証明している。**再帰で書いた証明が数学的帰納法**である。
-/

/-! ### ✏ 練習

1. `Signal` の「逆回り」`prev : Signal → Signal` を `match` で定義し、
   `#reduce prev (next Signal.red)` の表示を予想してから確かめよ
   （`Signal.red` に戻ってくるはずである）。
2. `MyNat` の項として 3 を `def myThree : MyNat := …`（`succ` 3回）と書き、
   `#reduce add myThree MyNat.zero` の表示を予想してから確かめよ。
3. 2点の列挙型 `inductive Two where | a | b` を定義せよ。`Two` と `Bool` は
   集合としては同じ2点集合だが、型としては別物である。往復の関数
   `toBool : Two → Bool` と `ofBool : Bool → Two` を書き、
   `#eval toBool (ofBool true)` を確かめよ（`Bool` は表示の仕組みが
   登録済みなので `#eval` が使える）。
4. 前問の `Nat` 版: `MyNat` と `Nat` も、型としては別物だが「同型」である。
   往復の関数 `toN : MyNat → Nat`（再帰で `+ 1` していく）と
   `ofN : Nat → MyNat`（パターン `| 0` と `| n + 1` の再帰）を書き、
   `#eval toN (ofN 3)` の値を予想してから確かめよ。
   （**すべての** `n` で往復が恒等になることの証明には数学的帰納法が要る。
   `CH.lean` を読んだあとで戻ってくるとよい。）
-/

/-! ## 5. structure

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

def MyPoint.x : MyPoint → Nat
  | .mk a _ => a

#check MyPoint.x

/-!
    MyPoint.x : MyPoint → Nat
-/

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

/-!
    Point : Type

自動定義されるものの型を推測しよう。構成子 `Point.mk` はフィールドを順に
受け取るから `Nat → Nat → Point`、取り出し関数 `Point.x` は
`Point → Nat` のはずである:
-/

#check Point.mk

/-!
    Point.mk (x y : Nat) : Point

自動定義された構成子。`⟨1, 2⟩` は略記
-/

#check Point.x

/-!
    Point.x (self : Point) : Nat

自動定義された取り出し関数。`p.x` とも書ける——8節
-/

#eval (Point.mk 1 2).x

/-!
    1

第1フィールドに入れた値が、そのまま返ってきた。
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

前節の直和とここの直積をまとめると、帰納型の一般形は集合の言葉でこう読める:

    (構成子1の引数たちの直積) ⊔ (構成子2の引数たちの直積) ⊔ …

つまり**構成子の個数が直和の項数を、各構成子の引数が直積の因子を**与える。
`Signal` は 1 ⊔ 1 ⊔ 1（3点集合）、`MySum α β` は α ⊔ β（直和だけ）、
`Point` は Nat × Nat（直和が1項に退化して直積だけ）、
構成子が0個なら空集合（`Empty`）。
「structure は直積」と「帰納型は直和のようなもの」は矛盾しない——
直和を**使って**直積を定義しているのではなく、構成子の**個数**と**引数**という
直交した2つの軸が、それぞれ直和と直積に対応しているのである。

### フィールドは前のフィールドに依存してよい

もう1つ一般化がある: 後のフィールドの型は、前のフィールドに**依存してよい**。
1節で見たとおり型も項だから、フィールドの値として**型そのもの**を持たせ、
次のフィールドの型をその値で決める、ということができる:
-/

structure PointedType where
  carrier : Type
  point : carrier

/-!
`mk` の型を推測しよう。フィールドの列そのまま……のはずだが、今度は
**第2引数の型の中に、第1引数の名前が現れる**ことになる:
-/

#check PointedType.mk

/-!
    PointedType.mk (carrier : Type) (point : carrier) : PointedType
-/

/-- 例:「型 `Nat` と、その要素 `0`」の組。数学でいう「点付き集合」である。 -/
def pointedNat : PointedType := ⟨Nat, 0⟩

#check pointedNat

/-!
    pointedNat : PointedType
-/

/-!
第二フィールド `point` の型が、第一フィールド `carrier` の**値**で決まっている
（`pointedNat` では `point : Nat`）。なお `#check PointedType` とすると
`PointedType : Type 1` と表示される——中身に `Type` の項を入れたので、
入れ物は1節の宇宙の階段を1段のぼるのである。

この「後の成分が前の成分に依存する組」の一般論は、`CH.lean` の6節（依存和）で
扱う。特に、第二成分を**命題の証明**にした「部分型」が `Top.lean` の主役級の
道具になるのだが、命題の話なのでここでは踏み込まない。
-/

/-! ### ✏ 練習

1. `structure Circle where center : Point; radius : Nat` のような
   自作の structure を1つ定義し、`#check` で構成子と取り出し関数が
   自動定義されていることを確かめよ。
2. `#eval Point.y (Point.mk 1 2)` の値を予想してから確かめよ。
   さらに `(Point.mk 1 2).y` とも書けることを試せ（8節のドット記法の先取り）。
-/

/-! ## 6. class と instance

`class` は structure の変種で、「この型の項は `instance` として登録しておき、
必要になったら Lean が登録簿から探して使う」という使い方を宣言したもの。
-/

class HasZero (α : Type) where
  zero : α

#check HasZero

/-!
    HasZero (α : Type) : Type
-/

instance : HasZero Nat where
  zero := 0

/-!
`HasZero α` の項は「`α` のどの項をゼロと呼ぶかの指定」で、
`instance` 宣言によって `Nat` のゼロとして `0` を登録した。

`instance` は**名前を付けない宣言**である（中身は `def` と同じで、
宣言と同時に登録簿へ載る）。使う側は登録簿から探すだけで名前で呼ばないから、
名前を書く必要がない。実際には Lean が `instHasZeroNat` のような名前を
自動で付けており、`instance myZero : HasZero Nat where …` と
自分で名前を付けることもできる。

登録簿から探す操作そのものを項として書いたのが `inferInstance` である。
型を見ると、インスタンス引数 `[i : α]` を受け取ってそのまま返すだけの関数で、
「探す」仕事は括弧 `[ ]` の仕組みがやっていることが分かる。
-/

#check @inferInstance

/-!
    @inferInstance : {α : Sort u_1} → [i : α] → α
-/

/-!
確かめてみる。次の `example` も名前を付けない宣言で、こちらは登録簿にも
載らない。「この型の項が確かに作れる」ことをその場で確かめるためだけに使う。
-/

example : HasZero Nat := inferInstance

/-!
登録してあるので、これは見つかって受理される（`example` は受理されると
Infoview には何も表示しない）。登録していない型では失敗する:

    example : HasZero Bool := inferInstance

    error: failed to synthesize instance of type class
      HasZero Bool
-/

/-- インスタンス引数の使いどころ: 「ゼロが登録されたどんな型でも」働く関数が書ける。
`zeroPair Nat` と書くだけで、`HasZero Nat` の項は登録簿から自動で渡される。 -/
def zeroPair (α : Type) [HasZero α] : Pair α α := ⟨HasZero.zero, HasZero.zero⟩

#check zeroPair

/-!
    zeroPair (α : Type) [HasZero α] : Pair α α

`(zeroPair Nat).fst` の値は、登録簿に載せた `zero`——つまり `0`——のはずである:
-/

#eval (zeroPair Nat).fst

/-!
    0
-/

/-! ### 自作型にもインスタンスを与える

クラスの効き目は、**あとから自分の型を仲間に入れられる**ことにある。
5節で作った `Point` にゼロを登録してみる。
-/

instance : HasZero Point where
  zero := ⟨0, 0⟩

#check zeroPair Point

/-!
    zeroPair Point : Pair Point Point

登録した瞬間から、`HasZero` を使う汎用の道具がすべて `Point` でも
使えるようになった。
-/

#eval (zeroPair Point).fst.x

/-!
    0
-/

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

/-!
    { x := 1, y := 2 } + { x := 3, y := 4 } : Point

登録した瞬間から、記法 `+` が `Point` でも通るようになった。
`x` 成分は `1 + 3` で `4` のはずである:
-/

#eval (Point.mk 1 2 + Point.mk 3 4).x

/-!
    4
-/

/-!
正確に言うと、`+` の読み先は `HAdd`（左右の型が違ってもよい、さらに一般の版）
なのだが、「`Add α` があれば `HAdd α α α` にもなる」という**橋渡しの
インスタンス**が標準ライブラリに用意されているので、`Add` を登録するだけで
記法まで使えるようになる。登録簿の検索は、このように**連鎖**する。

数字のリテラルにも同じ仕組みがあり、そちらは `OfNat` というクラスが担っている
（7節の補足で、`(2 : Fin 3)` のようなリテラルが通る理由として再登場する）。

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

#check Pair.mk 1 true

/-!
    { fst := 1, snd := true } : Pair Nat Bool

暗黙引数が埋まった
-/

/-! ### ✏ 練習

1. 本文で `HasZero Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : HasZero Bool where zero := false` を登録し、
   `example : HasZero Bool := inferInstance` と `#check zeroPair Bool` が
   通るようになることを確かめよ。
-/

/-! ## 7. 依存関数型

関数の一般化がもう1段ある。**行き先の型が、入力に応じて変わってよい**とした
関数——依存関数——である。いちばん簡単な例は「型そのものを最初の引数として
受け取る」形で作れる。型が引数にできることは、3節の `Map` で見たとおりである。
-/

/-- どんな型の上でも使える恒等写像。第1引数として**型**を受け取り、
第2引数と結果の型が、その第1引数で決まる。 -/
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
-/

/-!
`idAt Nat` と `idAt Bool` は**型が違う**。つまり `idAt` に1つ引数を渡すと、
「残りの型」がその引数の値で決まる。こうなるともう `A → B` の形では書けない。
この形の関数の型を**依存関数型**といい、

    idAt : (α : Type) → α → α

と書く（束縛した名前 `α` が矢印の右側に現れるのが目印）。これが Lean の
関数型の一般形で、`A → B` は「行き先が入力に依存しない特別な場合」の略記である。

なお、この「型を渡してから使う」仕組みこそ多相性の正体で、6節で説明した
暗黙引数 `{α : Type}` は、この第1引数を文脈から自動で埋めてもらう書き方である。

依存関数がさらに面白くなるのは、**型を返す関数**（型の族）と組み合わせたとき。
標準ライブラリの `Fin` は「`n` 未満の番号の型」を返す関数である
（`Fin 3` の項は 0 番・1 番・2 番の3つ。この型が**どう作られているか**は
`CH.lean` の6節で見る）。
-/

#check Fin

/-!
    Fin (n : Nat) : Type

つまり Fin : Nat → Type
-/

#check Fin 3

/-!
    Fin 3 : Type
-/

/-!
族に沿って「番号 `n` を受け取り、型 `Fin (n + 1)` の項を返す」関数が書ける。
一般形 `(a : α) → P a` の `P` が定数でない、本格的な依存の例である。
`first 2` と `first 9` は**型が違う**ことに注意。
-/

def first : (n : Nat) → Fin (n + 1) := fun _ => 0

#check first

/-!
    first (n : Nat) : Fin (n + 1)

適用すれば、型の中の `n` に渡した数が入るはずである:
-/

#check first 2

/-!
    first 2 : Fin (2 + 1)
-/

#check first 9

/-!
    first 9 : Fin (9 + 1)
-/

/-!
値はどれも「0 番」だが、その `0` の住んでいる型が入力ごとに違う。
（`0` と書けるのは `Fin` 用のリテラルの読みが登録されているからで、
すぐ下の補足で詳しく見る。）

集合のアナロジーでは、依存関数型 `(a : α) → P a` は集合族 {P a} の
**直積** ∏ₐ P a に当たる。その項は「各 a に P a の要素を1つずつ選ぶ、選び方」
だからである。`α → β` ＝ B^A（すべての因子が同じ直積、すなわち冪）の、
因子が点ごとに変わってよい一般化になっている。
対になる**族の直和** ∐ₐ P a——「どの a か」の札付きで各 P a の要素を集めたもの——に
当たる**依存和** `(a : α) × P a` もあり、`Pair`（直積）と `MySum`（直和）の
共通の一般化である。`CH.lean` の6節で主役になる。
-/

/-! ### 補足: では `2 : Fin 3` なのか？

「`Fin 3` は 3 未満の番号の型」と聞くと、集合 {0, 1, 2} ⊂ ℕ を思い浮かべて、
「自然数 `2` はそのまま `Fin 3` の項でもあるのか」と考えたくなる。そうではない。
1節で見たとおり**項はちょうど1つの型を持ち**、型どうしは集合のように重ならない
——集合のアナロジーの限界がここにある。`Fin 3` は `Nat` の部分集合ではなく、
`Nat` とは**別に作られた型**である（作りは `CH.lean` の6節で見る）。

まぎらわしいことに、`(2 : Fin 3)` という書き方自体は通ってしまう:
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
（`Fin` 用の読み方が instance として登録されている——6節で見た仕組みである）。
`(2 : Nat)` は自然数の項、`(2 : Fin 3)` は `Fin 3` の「2 番」の項で、
**同じ字面の、別の項**なのである。所属判定をしているのではない証拠に、
`(5 : Fin 3)` すら通り、3 で割った**余り**として読まれる:
-/

#eval (5 : Fin 3)

/-!
    2

`2` になった——リテラルの読みは、登録された読み方次第である。

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
逆向きはそうはいかない。`Fin 3` を期待する場所に `(2 : Nat)` を渡すと:

    error: Application type mismatch: The argument
      2
    has type
      Nat
    but is expected to have type
      Fin 3

`Nat → Fin 3` の向きには「3 未満に収まっているか」の確認が要るので、
自動では埋められない。まとめると、`Fin 3` と `Nat` の関係は
「部分集合と全体」ではなく、**写像 `.val` で結ばれた別々の型**である。
-/

/-!
行き先の型は、`Type` の住人でなくてもよい。**命題を返す関数**（数学でいう述語）を
作り、「すべての `n` について…」の証明そのものを依存関数として書く——それが
`CH.lean` の5節の主題である。`Top.lean` に出てくる「集合の族」 `U : I → Set X` や
「型の族」 `P : α → Type` も、この「型（や集合、命題）を返す関数」の仲間である。
-/

/-! ### ✏ 練習

1. `#check idAt (Nat → Nat)` の型を予想してから確かめよ（矢印の結合に注意）。
   `#eval idAt (Nat → Nat) double 21` はどうなるか。
2. `#check first 4` の表示と、`#eval (first 4).val` の値を予想してから確かめよ。
-/

/-! ## 8. 宣言を支える小物 — variable・namespace・記法

最後に、`CH.lean` と `Top.lean` の見た目を決めている構文を紹介する。
（証明を書くもう1つの流儀「タクティク」は `CH.lean` の最後で扱う。）

### variable — 共通の引数の前置き

同じ引数を宣言のたびに書くかわりに、`variable` でまとめて前置きしておける。
以後の宣言は、その変数を**実際に使ったときだけ**引数として受け取る。
-/

section
variable {α : Type} (x y : α)

def toPair : Pair α α := ⟨x, y⟩

#check toPair

/-!
    toPair {α : Type} (x y : α) : Pair α α

variable が引数に取り込まれた
-/

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

/-!
    Geometry.origin : Point
-/

end Geometry

#check Geometry.origin

/-!
    Geometry.origin : Point

外からはフルネームで呼ぶ
-/

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

/-!
確認してみる。後ろに付けるドットは、名前空間の関数の適用の略記にすぎない:
-/

#eval (Point.mk 1 2).swap.x

/-!
    2

`swap` で `x` と `y` が入れ替わった。フルネーム版の
`#eval (Point.swap (Point.mk 1 2)).x` でも、同じ `2` が返る。

フィールドは番号でも取れる。`.1` `.2` は第1・第2フィールドの略記である:
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
4節の `#reduce` の表示 `MyNat.zero.succ.succ` も、この「値の後ろに付けるドット」の
連鎖だった（`.succ` は `MyNat.succ` の略記で、`MyNat.zero` に2回適用されている）。

**型が分かっている場所で前に付けるドット**: 期待される型が `Point` だと
分かっている位置では、構成子 `Point.mk` を `.mk` と省略できる。
今度は「**期待される型**の名前空間から探す」という解決である。
4節のパターンマッチで使った `.red` や `.succ` もこの用法で、
`match` の各ケースは `Signal.red` などの略記だった。
-/

example : Point := .mk 1 2

/-!
`Top.lean` では `Set` の関数（`Set.ext` など）がこの形で、`s.ext` のように使われる。

### syntax と macro_rules — 記法の自作

`Top.lean` は `⋃₀ S` や `{a | p a}` といった数学記法を自作している。仕組みは:

* `syntax` — 「この書き方を受け付けよ」と構文を追加する
* `macro_rules` — 「その書き方はこの項の略記である」と展開を与える

試しに、5節の `Pair` のための記法を作ってみる。
-/

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

/-!
`⟪1, true⟫` は `Pair.mk 1 true` に展開されてから型検査されるので、
型は `Pair Nat Bool` のはずである:
-/

#check ⟪1, true⟫

/-!
    { fst := 1, snd := true } : Pair Nat Bool
-/

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
2. `#eval (Point.mk 1 2).swap.swap.x` の値を予想してから確かめよ
   （2回入れ替えると元に戻るはずである）。
3. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。
-/
