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
* 型を作る部品は実質2つ、**依存関数型**と**帰納型**（inductive type）である。
  ふだん目にする `→` `×` `∧` `∀` `structure` などは、すべてこの2つの現れである。
-/

/-! ## 1. 項と型

`#check e` は項 `e` の型を表示する。
-/

#check 3         -- 3 : Nat
#check 3 + 4     -- 3 + 4 : Nat
#check true      -- Bool.true : Bool

/-!
この表示を、読むたびに自分で確かめられるようにしておきたい。そのために以後、
**ざっくり**版と**正確には**版を併記する。正確な版は初読では飛ばしてよい。

* `3 : Nat` — **ざっくり**: 数字はそのまま自然数の項。
  **正確には**: 数字は記法であり、期待される型に応じて読み方が決まる
  （4節の補足と5節で見る）。何も指定がなければ `Nat` と読まれる。
* `3 + 4 : Nat` — **ざっくり**: `+` は `Nat → Nat → Nat` という型の関数だと
  みなしてよい。`Nat` の項を2つ渡すから、結果も `Nat`
  （この計算の規則は3節で正式に述べる）。
  **正確には**: `+` の正体は汎用の演算 `HAdd.hAdd` で、「どの型の足し算か」は
  登録簿（5節の instance）から決まる。それを `Nat` に特殊化した姿がざっくり版である。

すべての項はちょうど1つの型を持つ。ここで重要なのは、**型もまた項である**こと。
`Nat` 自身も `Type` という型を持つ項であり、`Type` も `Type 1` を持つ項である。
-/

#check Nat       -- Nat : Type
#check Type      -- Type : Type 1
#check Type 1    -- Type 1 : Type 2
#check Prop      -- Prop : Type

/-!
`Type`, `Type 1`, `Type 2`, … の階層を宇宙（universe）と呼び、
`universe u` と宣言して任意の段 `Type u` を扱える。

最後の `Prop` は命題たちの住む宇宙。つまり**命題も、`Prop` という型を持つ項**である。
-/

#check 1 + 1 = 2   -- 1 + 1 = 2 : Prop
#check 2 < 1       -- 2 < 1 : Prop

/-!
この2つも確かめられる。**ざっくり**: `=` や `<` は `Nat → Nat → Prop` という型の
関数とみなせばよい。`1 + 1 : Nat` と `2 : Nat` を渡すから `1 + 1 = 2 : Prop`。
**正確には**: `=` はどの型でも使える `Eq : α → α → Prop`（`α` は両辺の型から
決まる暗黙引数。定義そのものは `CH.lean` の8節で見る）、
`<` は型ごとに登録簿で意味が決まる演算である。

`2 < 1` のような偽の命題も、命題としては立派な項であることに注意。
真であるとは「その命題の証明がある」ことであり、それは次の節で見る。

型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（4節）。
-/

/-! ## 2. def と theorem — 項に名前を付ける

    def 名前 : 型 := 項

と書くと項に名前が付き、以後どこでも使える。
-/

def two : Nat := 2

#check two

def three : Nat := two + 1

#check three

#eval three      -- 3 （`#eval` は項を計算する）

/-!
この宣言を受理する前に、Lean は**型検査**を行っている:
`:=` の右に書いた項の型を計算し、コロンの右に書いた型と一致するかを調べる。
一致しなければ受理されない。

    def bad : Nat := true

    error: Type mismatch
      true
    has type
      Bool
    but is expected to have type
      Nat

命題も型だから、まったく同じ構文で「証明という項に名前を付ける」宣言が書ける。
型の位置に命題を、`:=` の右にその証明を書く。このとき `def` の代わりに
`theorem` と書くのが慣例で、意味は `def` と同じである。
-/

theorem one_add_one : 1 + 1 = 2 := rfl

#check one_add_one

/-!
`rfl` は「両辺が定義から計算して一致する」ことを理由にする等式の証明（詳しくは5節）。

ここでも型検査が同じ仕事をしていることに注意。
「項 `rfl` の型は命題 `1 + 1 = 2` と一致するか」という検査が、
そのまま**証明の検査**になっている。この見方が `CH.lean` の主題である。
-/

/-! ## 3. 関数

関数もまた項であり、`fun x => e` という式で作る。適用は括弧なしで `f a` と並べる。
-/

def double : Nat → Nat := fun n => n + n

#check double

#eval double 21    -- 42

/-!
ここでの型検査の中身も見ておく。`fun n => n + n` が型 `Nat → Nat` を
持つかを調べるときは、引数を `n : Nat` と**仮に置いて**、
そのもとで本体 `n + n` の型が `Nat` になるかを調べる。
「仮定を置いて中身を検査する」というこの形は、
含意 `p → q` の証明の形として `CH.lean` にそのまま現れる。
-/

/-- 引数を左に書く糖衣構文。上の `double` と同じもの。 -/
def double' (n : Nat) : Nat := n + n

#check double'

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
書き方の糖衣もここでまとめておく。次の3つは**まったく同じ宣言**である:

    def plus : Nat → Nat → Nat := fun a => fun b => a + b
    def plus : Nat → Nat → Nat := fun a b => a + b       -- fun は引数をまとめられる
    def plus (a b : Nat) : Nat := a + b                  -- 引数を名前ごと左に書く

`#check` の表示もこれに対応して、`plus : Nat → Nat → Nat` という矢印形式と
`plus (a b : Nat) : Nat` という binder 形式は同じ型の2通りの表示である。
以後どちらの表示も出てくるので、読み替えられるようにしておくこと。
-/

/-- 3引数以上も同じことの繰り返し。
`Nat → Nat → Nat → Nat` は `Nat → (Nat → (Nat → Nat))` と読む。 -/
def addMul (a b c : Nat) : Nat := a + b * c

#check addMul      -- addMul (a b c : Nat) : Nat（binder 形式の表示）

/-! ### 型は部分項から機械的に計算できる

2節で「型検査が走る」と述べた。その中身をここで見ておく。
適用についての規則はただ1つである:

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

/-! ## 4. 依存関数型

1節で見たとおり型も項なので、**型を返す関数**が書ける。
例えば標準ライブラリの `Fin` は「`n` 未満の自然数の型」を返す関数である。
-/

#check Fin        -- Fin (n : Nat) : Type  （つまり Fin : Nat → Type）
#check Fin 3      -- Fin 3 : Type

/-!
すると「入力ごとに行き先の型が変わる関数」が考えられる。それが依存関数型
`(a : α) → P a` で、Lean の関数型の一般形はこちらである。

次の `last` は `n` を受け取って `Fin (n + 1)` の項を返す。
`last 2` と `last 9` は**型が違う**ことに注意。
-/

def last : (n : Nat) → Fin (n + 1) := fun n => ⟨n, Nat.lt_succ_self n⟩

#check last
-- `⟨…⟩` は構成子に引数を渡す記法（5節）。`Fin` の項は「値」と「値 < n の証明」の組。

#check last 2     -- last 2 : Fin (2 + 1)
#check last 9     -- last 9 : Fin (9 + 1)

/-! ### 補足: では `2 : Fin 3` なのか？

「`Fin 3` は 3 未満の自然数の型」と聞くと、集合 {0, 1, 2} ⊂ ℕ を思い浮かべて、
「自然数 `2` はそのまま `Fin 3` の項でもあるのか」と考えたくなる。そうではない。
1節で見たとおり**項はちょうど1つの型を持ち**、型どうしは集合のように重ならない。
`Fin 3` は `Nat` の部分集合ではなく、「値と、それが 3 未満だという証明の組」
からなる**別の型**である。

まぎらわしいことに、`(2 : Fin 3)` という書き方自体は通ってしまう:
-/

#check (2 : Nat)     -- 表示: 2 : Nat
#check (2 : Fin 3)   -- 表示: 2 : Fin 3

/-!
これは数字 `2` が**記法**であり、期待される型に応じて別々の項に読まれるからである
（`Fin` 用の読み方が登録されている。仕組みは5節で見る instance）。
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
ふつうの関数型はこの特殊な場合にすぎない:
`α → β` は、行き先が入力に依存しない `(_ : α) → β` の略記である。

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

/-! ## 5. 帰納型（inductive type）

もう1つの部品が帰納型。**構成子（constructor）のリスト**で型を定義する。
いちばん単純なのは、構成子がどれも引数を取らない列挙型である。
-/

inductive Signal where
  | red
  | yellow
  | green

#check Signal

#check Signal.red   -- Signal.red : Signal

/-!
この宣言の意味は「`Signal` の項は `red`, `yellow`, `green` の3つが**すべて**であり、
それ以外にはない」ということ。作り方を列挙したら、それで型が決まる。
つまり列挙型は、3点集合のような**有限集合**である。

「それ以外にない」からこそ、場合分け（`match`）が正当化される。
これが帰納型の項の使い方（除去）である。
-/

def next : Signal → Signal
  | .red => .green
  | .green => .yellow
  | .yellow => .red

#check next

/-!
`Bool` はまさにこの形で、`false` と `true` の2つを列挙した型である。

紛らわしいが、命題の `False` と `True`（どちらも `Prop` の項）は別物なので注意。
`true : Bool` は計算で使う**データ**であり、`True : Prop` は**命題**である。
実は命題の側も帰納型で作られている: `True` は構成子をちょうど1つ持つ命題
（その構成子 `True.intro` が証明）、`False` は構成子を**1つも持たない**命題
（だから証明がない）。この対比は `CH.lean` の4節で扱う。

### 構成子は引数を取れる

構成子に引数を持たせると、データを包む型が作れる。型をパラメータにしてもよい。
-/

inductive MySum (α β : Type) where
  | inl : α → MySum α β
  | inr : β → MySum α β

#check MySum

#check MySum.inl    -- MySum.inl {α β : Type} : α → MySum α β

/-!
`MySum α β` の項は、「`α` の項に `inl` の札を付けたもの」か
「`β` の項に `inr` の札を付けたもの」のどちらか。数学でいう直和である
（`CH.lean` に出てくる `⊕` は、標準ライブラリにあるこれと同じ型）。
場合分けで札を見分け、中身を取り出す。
-/

def fromSum : MySum Nat Bool → Nat
  | .inl n => n
  | .inr _ => 0

#check fromSum

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
-/

def add : MyNat → MyNat → MyNat
  | m, .zero   => m
  | m, .succ n => .succ (add m n)   -- 構造が小さくなる方向への再帰

#check add

/-!
次の `example` は**名前を付けない宣言**である。中身は `def`/`theorem` と同じで、
型検査もまったく同じように走るが、名前が付かないのであとから参照できない。
「この項がこの型を持つ」ことをその場で確かめるためだけに使う。
2節で見た `rfl` で、1 + 1 = 2 が計算だけで確かめられる。
-/

example : add (.succ .zero) (.succ .zero) = .succ (.succ .zero) := rfl

/-!
標準ライブラリの型はほとんどすべて帰納型である。
`Bool`（列挙型）、`Nat`（リテラル `3` は `succ (succ (succ zero))` の表示）、`Fin`、
`CH.lean` に出てくる `×` `⊕` `Empty`、命題側の `And` `Or` `False` `Exists` `Eq` も全部そう。
`Eq` の構成子は `rfl` ただ1つで、2節から使っているのはこれである。

`Top.lean` では、`Nat` の再帰で集合の有限個の共通部分 `interFin` を定義し、
その性質もまた再帰で証明している。**再帰で書いた証明が数学的帰納法**である。

### structure — 構成子が1つの帰納型

構成子が**1つだけ**で、その構成子が**複数の引数**を受け取る帰納型を考える。
-/

inductive MyPoint where
  | mk : Nat → Nat → MyPoint

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
`structure` である。フィールド名がそのまま取り出し関数になる。
-/

structure Point where
  x : Nat
  y : Nat

#check Point

#check Point.mk    -- Point.mk (x y : Nat) : Point （構成子。`⟨1, 2⟩` は `Point.mk 1 2` の略記）
#check Point.x     -- Point.x (self : Point) : Nat （取り出し関数。`p.x` とも書ける）

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
この `Pair α β` は、数学でいう直積 `α × β` と中身が同じものである。
つまり structure は「**直積の各成分に名前を付けたもの**」と思ってよい。
実際、標準ライブラリの `×` 自身が `fst`/`snd` という2フィールドの
structure（名前は `Prod`）として定義されている。

1つだけ一般化がある: 後のフィールドの型は、前のフィールドに**依存してよい**。
例えば4節の `Fin n` は `val : Nat` と `isLt : val < n` の2フィールドの
structure で、第二成分の型（証明の命題）が第一成分の値に依存している。
このような「依存する直積」が何かは `CH.lean` の6節（依存和）で扱う。

### 型の読み方と3種類の括弧

ここで、`#check` が表示する型の読み方をあらためてまとめておく。例えば

    Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β

は、コロンの左に引数の列が並び、最後の `: Pair α β` が結果の型、と読む。
引数を1つ渡すたびに列の左から1つ消えていき、全部渡すと結果の型の項が得られる。
そして各段階で「渡した項の型が、引数の型と一致するか」の型検査が走っている。
2節からやってきたことの一般形である。

引数を包む括弧には3種類あり、「その引数を**誰が埋めるか**」を表している。

* `(fst : α)` — **明示引数**。使う側が自分で書く。
* `{α : Type}` — **暗黙引数**。使う側は書かない。型検査が、他の引数との
  つじつま合わせ（単一化）で埋める。`Pair.mk 1 true` と書けば
  `1 : Nat` と `true : Bool` から `α := Nat`、`β := Bool` が決まる。
* `[inst : C α]` — **インスタンス引数**。これも使う側は書かないが、埋め方が違う。
  型検査からは決まらず、`instance` として**登録された項**の中から Lean が探して埋める。
  すぐ下の class で使う。
-/

#check Pair.mk 1 true   -- { fst := 1, snd := true } : Pair Nat Bool （暗黙引数が埋まった）

/-!
### ドット記法

名前空間（7節）に置かれた関数は、ドットを挟んだ短い書き方で呼べる。
向きの違う2つの用法があるので、ここでまとめて押さえておく。

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
5節のパターンマッチに現れた `.red` や `.succ` もこの用法で、
`match` の各ケースは `Signal.red` などの略記だった。
-/

example : Point := .mk 1 2

/-!
### class と instance

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
この節で作った `Point` にゼロを登録してみる。
-/

instance : HasZero Point where
  zero := ⟨0, 0⟩

-- 登録した瞬間から、`HasZero` を使う汎用の道具がすべて `Point` でも使えるようになる
#check zeroPair Point   -- 表示: zeroPair Point : Pair Point Point
example : (zeroPair Point).fst = Point.mk 0 0 := rfl

/-! ### 数字の記法もクラスで動いている

4節の補足で「数字リテラルは、期待される型に応じて読み方が登録された記法だ」と
述べた。その登録簿の正体もクラスで、標準ライブラリの `OfNat` である:

    class OfNat (α : Type u) (n : Nat) where
      ofNat : α

つまり `(0 : Point)` と書けるようにしたければ、`OfNat Point 0` を登録すればよい:
-/

instance : OfNat Point 0 where
  ofNat := HasZero.zero

#check (0 : Point)   -- 表示: 0 : Point（記法 `0` が Point でも通るようになった）
example : (0 : Point) = Point.mk 0 0 := rfl

/-!
4節の補足で `(2 : Fin 3)` が通ったのも、`Fin` にこの `OfNat` のインスタンスが
あらかじめ用意されていたからである。記法の意味は登録簿が決めている。
-/

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

/-! ## 6. 型と集合のアナロジー

ここまでに出てきた型を、集合の言葉で見直しておく。
「型 ↔ 集合、項 ↔ 要素」という対応で眺めると、
型を作る部品はどれも、見慣れた集合の構成に対応している。
ただしアナロジーには限界もある。集合と違って型どうしは重ならない——
`Fin 3` は `Nat` の部分集合ではない（4節の補足）。

| 型 | 集合 |
|---|---|
| `A → B` | 写像全体の集合。Map(A, B)、Hom(A, B)、B^A などと書かれるもの |
| 列挙型 `Signal` | 有限集合 {red, yellow, green} |
| `MySum α β` | 直和（非交和）α ⊔ β |
| `Point`、`Pair α β` | 直積 Nat × Nat、α × β |
| `(a : α) → P a` | 集合族の直積 ∏ₐ P a（下述） |

### 帰納型は「直和」と「直積」の重ね合わせ

帰納型の一般形は、集合の言葉ではこう読める:

    (構成子1の引数たちの直積) ⊔ (構成子2の引数たちの直積) ⊔ …

つまり**構成子の個数が直和の項数を、各構成子の引数が直積の因子を**与える。

* `Signal` — 引数なしの構成子が3つ: 1 ⊔ 1 ⊔ 1（3点集合）
* `MySum α β` — 1引数の構成子が2つ: α ⊔ β（直和だけが現れる）
* `Point` — 2引数の構成子が1つ: Nat × Nat（直和が1項に退化して、直積だけが現れる）
* 構成子が0個なら空集合（`CH.lean` に出てくる `Empty` や `False`）

だから「structure は直積」（5節）と「帰納型は直和のようなもの」は矛盾しない。
直和を**使って**直積を定義しているのではなく、構成子の**個数**と
構成子の**引数**という直交した2つの軸が、それぞれ直和と直積に対応している。

再帰的な帰納型には但し書きが要る。`MyNat` に上の読みを当てると

    MyNat ≅ 1 ⊔ MyNat   （zero の分の1点 ⊔ succ の引数の分）

と、右辺に自分自身が現れる。この場合の帰納型は「この方程式を満たす**最小**の
集合」と読む。最小性は、「`zero` に `succ` を有限回重ねたものがすべてで、
それ以外にない」という5節の説明の言い替えである。

### 依存版: 族の直積と族の直和

依存関数型 `(a : α) → P a` は、集合族 {P a} の**直積** ∏ₐ P a に当たる。
その項は「各 a に P a の要素を1つずつ選ぶ、選び方」だからである。
`α → β` ＝ B^A（すべての因子が同じ直積、すなわち冪）の、
因子が点ごとに変わってよい一般化になっている。

直積があれば、**族の直和** ∐ₐ P a——「どの a か」の札付きで各 P a の要素を
集めたもの——も考えたくなる。これに当たる型もあり、**依存和** `(a : α) × P a` と書く。
`Pair`（直積）と `MySum`（直和）の共通の一般化であり、`CH.lean` の6節で主役になる。
-/

/-! ## 7. 宣言を支える小物 — variable・namespace・記法

最後に、`CH.lean` と `Top.lean` の見た目を決めている構文を3つ紹介する。
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
5節のドット記法は、この名前空間の仕組みの上に載っている:
`p.x` が効くのは、`x` が**型名と同じ名前空間** `Point` に置かれているからである。
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

#check ⟪1, true⟫    -- { fst := 1, snd := true } : Pair Nat Bool

/-!
記法は項に展開されてから型検査されるので、検査の対象はあくまで項のままである。
単純な中置・前置の記法には `infixl` や `prefix` という略記もある（`Top.lean` で使用）。

これで `CH.lean` と `Top.lean` を読む準備は足りる。

なお正確には、Lean の核には依存関数型と帰納型のほかに商型（`Quot`）などもあるが、
この教材では使わない。
-/
