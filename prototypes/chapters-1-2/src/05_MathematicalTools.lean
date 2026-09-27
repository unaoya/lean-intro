import «03_InductiveTypes»
import «04_Exists»

/-!
# 数学を記述する道具

第3章では、構成子で組を作り、`match` で成分を取り出した。
第4章では、同じ仕組みで証明を作ったり使ったりした。
この章では、その上に、数学の対象を短く読みやすく書くための道具を加える。

まず、名前の付いた成分をまとめる `structure` と、構成子の略記 `⟨…⟩` を扱う。
次に、値に証明を添える部分型を、`Fin` の例と結び付けて読む。
そこから `class` と `instance`、記法の自作、集合 `Set`、名前空間へ進み、
第6章で位相空間を記述するための準備をする。
-/

/-! ## 1. structure — フィールドを持つ型 {#sec-Trial5.structures}

第3章の `MyPair` は、構成子を一つ持つ帰納型だった。
その成分を取り出す `pairFirst` は、`match` の一つの枝で定義した。
自然数を二つまとめる型でも、同じように書ける。
-/

inductive MyPoint : Type where
  | mk (x y : Nat) : MyPoint

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | MyPoint.mk a _ => a

/-!
この「構成子一つの帰納型」と「成分を取り出す関数」をまとめて宣言する構文が
`structure` である。名前の付いた成分を **フィールド** と呼ぶ。
自然数の組を、二つのフィールド `x`・`y` を持つ型として定義しよう。
-/

structure Point : Type where
  x : Nat
  y : Nat

/-!
`Point` は新しく定義した型であり、先ほどの `MyPoint` とは別の型である。
持つデータの形は同じだが、こちらでは構成子と取り出し関数が自動で用意される。

### 構成子で作り、フィールドを取り出す

構成子 `Point.mk` は二つの自然数を順に受け取る。
取り出し関数 `Point.x` は、できた `Point` の項から第一成分を返す。
-/

#check Point.mk
#check Point.x

/-!
    Point.mk (x y : Nat) : Point
    Point.x (self : Point) : Nat

矢印形式なら、それぞれ `Nat → Nat → Point` と `Point → Nat` である。
`Point.y : Point → Nat` も同時に定義される。
-/

#eval Point.x (Point.mk 1 2)

/-!
    1

二つの値を渡して作り、そのうち一つを取り出した。
構成子と `match` で行っていた操作を、名前の付いた関数で書けるようになった。

### ドット記法で関数を適用する

`p : Point` に対して、`Point.x p` は `p.x` とも書ける。
Lean は `p` の型から `Point.x` を見つけ、`p` を引数として渡す。
-/

#eval (Point.mk 1 2).x

/-!
    1

したがって `.x` は値を取り出す別の原理ではなく、関数適用の略記である。
番号で成分を指定する代わりに、`x`・`y` のような名前を使って読む。

### 匿名構成子 — 期待される型から構成子を決める

期待される型が `Point` と分かる位置では、`Point.mk 1 2` を `⟨1, 2⟩` と書ける。
これを **匿名構成子記法** という。`⟨`・`⟩` は `\<`・`\>` で入力できる。
-/

def pointFromPair : Point := ⟨1, 2⟩
def pointFromDot : Point := .mk 1 2

#check (⟨1, 2⟩ : Point)

/-!
    { x := 1, y := 2 } : Point

どちらの定義の右辺も `Point.mk 1 2` と読まれる。
`⟨…⟩` は期待される型から構成子を選び、`.mk` は期待される型から名前の接頭辞を補う。
第1章で見た、周囲から型を伝える仕組みを使っている。

### フィールド名を付けて書く

表示された `{ x := 1, y := 2 }` は、フィールド名を付けて構造体の項を書く記法である。
これを入力に使うこともできる。次の三つは、同じ構成子の適用を表している。
-/

def point_pair_eq_mk : (⟨1, 2⟩ : Point) = Point.mk 1 2 := rfl
def point_fields_eq_mk : ({ x := 1, y := 2 } : Point) = Point.mk 1 2 := rfl

/-!
匿名構成子記法は `structure` 専用ではない。
構成子が一つの型なら、第4章の「かつ」や存在の証明でも使える。
-/

def exists_two : ∃ n : Nat, n = 2 := ⟨2, rfl⟩

/-!
これは `Exists.intro 2 rfl` の略記であり、証人とその根拠を渡す仕組みは同じである。
略記を見たら、期待される型と、補われる構成子を確かめよう。

### 自分で定義した関数もドットで使える

`Point` の項を受け取る関数を `Point.〜` という名前で定義すれば、
取り出し関数と同じようにドット記法で使える。
-/

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

#eval (Point.mk 1 2).swap.x

/-!
    2

`p.swap.x` は `Point.x (Point.swap p)` の略記である。
二つの成分を交換してから、第一成分を取り出している。
この名前の付け方を支える名前空間は、[7節](#sec-Intro2.namespaces)で扱う。

### ✏ 練習

1. 型 `A` と二つの写像 `f g : A → Nat` から、各 `a` を組 `(f a, g a)` に送る
   `pairAt (A : Type) (f g : A → Nat) : A → Point` を定義せよ。
   `A = Nat`、`f n = n + 1`、`g n = 2 * n` とし、`3` を渡した結果の
   `x`・`y` を `#eval` で確かめよ。これは直積へ向かう写像を、成分の写像から作る操作である。
-/

/-!
### 型をパラメータにする structure

フィールドの型を固定せず、パラメータで受け取ることもできる。
第3章の `MyPair A B` と同じ形の組を、`structure` で定義しよう。
-/

structure Pair (α β : Type) : Type where
  fst : α
  snd : β

#check Pair.mk
#check Pair.fst

/-!
    Pair.mk {α β : Type} (fst : α) (snd : β) : Pair α β
    Pair.fst {α β : Type} (self : Pair α β) : α

構成子の `α`・`β` は暗黙引数なので、普通は渡す成分から推測される。
自作の `Pair` と `MyPair` は別の型だが、同じ形のデータを持つ。

### 二つの異なる型の項をまとめる
-/

def natBoolPair : Pair Nat Bool := Pair.mk 3 true

#eval natBoolPair.fst
#eval natBoolPair.snd

/-!
    3
    true

匿名構成子なら、この定義の右辺を `⟨3, true⟩` と書ける。
標準の直積 `α × β`、すなわち `Prod α β` も、同じ形の構造体である。
`Prod.mk` で作り、`Prod.fst`・`Prod.snd`（または `.fst`・`.snd`）で取り出せる。
-/

/-! ## 2. 依存するフィールド {#sec-Trial5.dependent-fields}

第3章の `Numbered` は、`n : Nat` と、その `n` に応じた `Fin n` の項を持っていた。
`structure` でも、後のフィールドの型に前のフィールドを使える。
今度は、型そのものと、その型の項を一つまとめよう。
-/

structure PointedType : Type 1 where
  carrier : Type
  point : carrier

#check PointedType.mk

/-!
    PointedType.mk (carrier : Type) (point : carrier) : PointedType

これは点付き集合 $(A,a)$ に対応する。
最初に `carrier` を決めると、次に渡す `point` の型が決まる。
`Type` 自体をフィールドに持つので、全体の型は `Type 1` に置いている。

### 点付き集合を作る
-/

def pointedNat : PointedType := ⟨Nat, 0⟩
def pointedBool : PointedType := ⟨Bool, true⟩

#check PointedType.mk Nat

/-!
    PointedType.mk Nat : Nat → PointedType

第一引数に `Nat` を渡すと、残りの引数は `Nat` の項になった。
`⟨Nat, 0⟩` は `PointedType.mk Nat 0`、`⟨Bool, true⟩` は `PointedType.mk Bool true` の略記である。

### 取り出す項の型も入力に依存する
-/

#check PointedType.carrier
#check PointedType.point

/-!
    PointedType.carrier (self : PointedType) : Type
    PointedType.point (self : PointedType) : self.carrier

`p : PointedType` に対して、`p.carrier` は型であり、`p.point` はその型の項である。
`PointedType.point` の結果の型は入力 `p` によって変わる。
第3章の `Numbered.index` と同じ依存関数が、自動で用意されたのである。
-/

#reduce pointedNat.point
#reduce pointedBool.point

/-!
    0
    true
-/

/-! ## 3. 部分型 — 値と証明の組 {#sec-Trial5.subtypes}

後のフィールドの型が前の値に依存するとき、その型が命題でもよい。
例えば「偶数である自然数」を持ち歩きたければ、自然数 `n` と
`IsEven n` の証明を一緒に持てばよい。こうした値と証明の組を扱うのが **部分型** である。

標準の `Subtype` の定義は、宇宙の指定を省けば次の形になっている。

    structure Subtype {α : Type} (p : α → Prop) where
      val : α
      property : p val

述語 `p` はパラメータであり、値 `val` を決めると、必要な証明の型 `p val` が決まる。
`Subtype p` は `{x // p x}` とも書く。

### 偶数という条件を付けた型
-/

def EvenNat : Type := {n : Nat // IsEven n}

def evenFour : EvenNat := Subtype.mk 4 (Exists.intro 2 rfl)

#check evenFour.val
#check evenFour.property

/-!
    evenFour.val : Nat
    evenFour.property : IsEven evenFour.val

`evenFour` は「自然数 `4`」と「`4` は偶数だという証明」の組である。
内側の `Exists.intro 2 rfl` は、第4章で学んだ偶数性の証明を作っている。

### 値と、値についての保証を取り出す
-/

#eval evenFour.val

/-!
    4

`evenFour.property` を使えば、取り出した自然数の偶数性も使える。
例えば、二つの偶数の和が偶数であるという第4章の結果を適用できる。
-/

def evenFourPlusFour : IsEven (evenFour.val + evenFour.val) :=
  isEven_add evenFour.property evenFour.property

/-!
`EvenNat` と `Nat` は別の型である。`evenFour : EvenNat` から自然数を使いたいときは
`.val` で取り出す。数学で部分集合を考えるイメージと、Lean の型の区別を分けて読もう。

### 存在の証明との違い

`∃ n : Nat, IsEven n` の証明も、自然数とその偶数性の証明から作れる。
どちらも二つの成分を使うが、全体の型が違う。

* `EvenNat : Type` は、条件を満たす値をデータとして使うための型である。
  `.val` で自然数を取り出し、計算に使える。
* `(∃ n : Nat, IsEven n) : Prop` は、そのような値が存在するという命題である。
  第4章のように `match` で証人を使って別の命題を証明できるが、
  一般にはその証明を場合分けして自然数を返す関数は定義できない。

条件付きの値を計算に渡したいのか、存在することを証明したいのかに応じて使い分ける。

### Fin も値に範囲の証明を添えている

第1章から使ってきた `Fin n` の定義は、次の構造体である。

    structure Fin (n : Nat) where
      val : Nat
      isLt : val < n

`Fin n` も「値と、その値についての証明」を持つ。
`Subtype` の単なる別名ではなく、同じ考え方で個別に定義された型である。
`i : Fin n` からは、`i.val : Nat` と `i.isLt : i.val < n` を取り出せる。

### 不等式の証明を渡して番号を作る

第3章で見たように、自然数の不等式も証明の型である。
ここでは、標準ライブラリの `Nat.lt_succ_self` が `n < n + 1` の証明を与える。
-/

#check Nat.lt_succ_self

/-!
    Nat.lt_succ_self (n : Nat) : n < n.succ

`n.succ` と `n + 1` は計算上等しいので、この証明を `Fin.mk` に渡せる。
-/

def lastFromProof : (n : Nat) → Fin (n + 1) :=
  fun n => Fin.mk n (Nat.lt_succ_self n)

#check lastFromProof 2
#eval (lastFromProof 2).val

/-!
    lastFromProof 2 : Fin (2 + 1)
    2

### 第1章の依存関数を、構成子まで読む

`lastFromProof` の本体は `⟨n, Nat.lt_succ_self n⟩` と略記することもできる。
自然数 `n` を受け取り、値 `n` と範囲の証明から `Fin (n + 1)` の項を作っている。
第1章の `lastIndex` と同じ「最後の番号」を、今度は中身まで書いた。
-/

def lastFromProof_val (n : Nat) : (lastFromProof n).val = n := rfl
def lastFromProof_eq_lastIndex (n : Nat) : lastFromProof n = lastIndex n := rfl

/-!
入力に応じて結果の型が変わるので、これは依存関数である。
その結果として返す `Fin (n + 1)` の項の内部には、値とその値の保証が入っている。
型の族に沿って項を与える話と、依存する組の話が、ここでつながった。
-/

/-! CALLOUT_START optional -/

/-! ### 補足: Fin の数値リテラル

`Fin 3` の項は、自然数の値と、その値が3未満である証明の組である。
`Nat` の項とは別の型の項だが、数字は期待される型に応じて読まれるので、
`(2 : Fin 3)` と書けば `Fin 3` の「2番」の項になる。
さらに、`(5 : Fin 3)` も受理される。
-/

#eval (5 : Fin 3)

/-!
    2

正の `n` に対して、`Fin n` の数値リテラルは、`n` で割った**余り**として読まれる。
ここでは5を3で割った余りの2が、範囲の証明とともに `Fin 3` の項になる。

第1章の章末問題の `repeatTuple (n : Nat) (a : Nat) : Tuple n` でも同じことが起きる。
`repeatTuple 3 4 5` と書くと、最初の3が個数、次の4が各成分の値であり、
最後に渡す番号の型は `Fin 3` である。したがって数字の5は「2番」として読まれ、
その成分の値4が返る。

一方、既に `Nat` 型と指定した `(5 : Nat)` を、この番号の引数として渡すと型エラーになる。
数字を `Fin 3` の項として読めることと、`Nat` 型の項をそのまま渡せることは別である。
数値リテラルの読み方を決める仕組みは、[4節](#sec-Intro2.classes)の補足で説明する。
-/

/-! CALLOUT_END -/


/-! ## 4. class と instance {#sec-Intro2.classes}

ここまでは構造体の項を明示して渡していた。
`class` を使うと、型ごとに決めた項を `instance` として登録し、
必要な場所で Lean に探してもらえる。宣言の形は `structure` と同じである。

[2節](#sec-Trial5.dependent-fields)の `PointedType` は、型とその中の点を一つに束ねた。
今度は型 `α` をパラメータにし、その中の点だけをフィールドにする。
-/

class Pointed (α : Type) : Type where
  point : α

#check Pointed

/-!
    Pointed (α : Type) : Type

`carrier` がパラメータ `α` に移り、フィールドは点だけになった。
パラメータを取ること自体は `structure` でもできる。
`class` にした意味は、この項を登録して、必要な場所へ自動で渡してもらえることにある。

登録は `instance` 宣言で行う:
-/

instance : Pointed Nat where
  point := 0

/-!
`Pointed α` の項は「`α` のどの項を**基点**と呼ぶかの指定」で、
`instance` 宣言によって `Nat` の基点として `0` を登録した。

`instance` は、項を定義すると同時に登録簿へ載せる宣言である。
使う側は登録簿から探してもらえるので、宣言の名前を省略できる。実際には Lean が `instPointedNat` のような名前を
自動で付けており、`instance myPoint : Pointed Nat where …` と
自分で名前を付けることもできる。

登録簿から探す操作そのものを項として書いたのが `inferInstance` である。
型を見ると、インスタンス引数 `[i : α]` を受け取ってそのまま返すだけの関数で、
「探す」仕事は括弧 `[ ]` の仕組みがやっていることが分かる。

これで括弧が3種類そろった。[`01_TypesAndTerms.lean` 4節](#sec-Intro1.dependent-functions)の `( )`（明示）・`{ }`（暗黙）に
加えて、`[inst : C α]` が**インスタンス引数**である——他の引数との単一化だけでは
決まらず、エラボレータが `instance` として登録された項の中から探索して埋める。
-/

#check @inferInstance

/-!
    @inferInstance : {α : Sort u_1} → [i : α] → α

頭の `@` は「暗黙引数も省略せずに表示・指定する」
という印で、`@inferInstance` は `inferInstance` の省略なし版である。
`Sort u` は、第3章で `Eq` の型を読むときに見た、`Prop` や `Type`、`Type 1` などを
まとめて扱う宇宙の表記である。つまりこの関数は、命題も通常の型も対象にできる。
-/

/-!
確かめてみる。`inferInstance` に型 `Pointed Nat` を指定して、`#check` で調べる。
これは登録済みのインスタンスを探す項であり、新しいインスタンスの登録は行わない。
-/

#check (inferInstance : Pointed Nat)

/-!
    inferInstance : Pointed Nat

`Nat` には基点が登録してあるので、対応する項が見つかり、型が確認できる。
登録していない型では失敗する:

    #check (inferInstance : Pointed Bool)

    error(lean.synthInstanceFailed): failed to synthesize instance of type class
      Pointed Bool

-/

/-- インスタンス引数の使いどころ: 「基点が登録されたどんな型でも」働く関数が書ける。
`pointPair Nat` と書くだけで、`Pointed Nat` の項は登録簿から自動で渡される。 -/
def pointPair (α : Type) [Pointed α] : Pair α α := ⟨Pointed.point, Pointed.point⟩

#check pointPair

/-!
    pointPair (α : Type) [Pointed α] : Pair α α

`(pointPair Nat).fst` の値は、登録簿に載せた `point`——つまり `0`——のはずである:
-/

#eval (pointPair Nat).fst

/-!
    0
-/

/-! ### 自作型にもインスタンスを与える

クラスの効き目は、**あとから自分の型を仲間に入れられる**ことにある。
[1節](#sec-Trial5.structures)で作った `Point` に基点（原点）を登録してみる。
-/

instance : Pointed Point where
  point := ⟨0, 0⟩

#check pointPair Point

/-!
    pointPair Point : Pair Point Point

登録した瞬間から、`Pointed` を使う汎用の道具がすべて `Point` でも
使えるようになった。
-/

#eval (pointPair Point).fst.x

/-!
    0
-/

/-! ### インスタンスを受け取る定理

インスタンス引数は、証明を定義する `def` にも書ける。
「基点が登録されたどんな型でも成り立つ」一般的な定理を証明してみよう:
-/

def pointPair_fst (α : Type) [Pointed α] :
    (pointPair α).fst = Pointed.point := rfl

#check pointPair_fst

/-!
    pointPair_fst (α : Type) [Pointed α] : (pointPair α).fst = Pointed.point

使うときは `α` を指定するだけでよく、基点の指定である `Pointed α` の項は登録簿から
自動で供給される。
-/

def pointPair_nat_fst : (pointPair Nat).fst = Pointed.point := pointPair_fst Nat
def pointPair_point_fst : (pointPair Point).fst = Pointed.point := pointPair_fst Point

/-! ### 積に構造を誘導する

登録簿のもう1つの効き目は、**インスタンスからインスタンスを作れる**ことである。
基点付きの型が2つあれば、その積にも「基点の組」という自然な基点が決まる。
この「積への構造の誘導」も、前提にインスタンス引数を取る instance として
登録できる:
-/

instance {α β : Type} [Pointed α] [Pointed β] : Pointed (Pair α β) where
  point := ⟨Pointed.point, Pointed.point⟩

#eval (Pointed.point : Pair Nat Point).snd.x

/-!
    0

`Pair Nat Point` の基点はどこにも直接は登録していないのに、見つかった。
探索が**連鎖**するからである: `Pointed (Pair Nat Point)` を探す → 上の誘導
instance が形に合う → その前提 `Pointed Nat`・`Pointed Point` をさらに
登録簿から探す——と、機械が自動でつないでいく。`07_Exercises.lean` の発展演習で
「積空間 `X × Y` に位相が自動で載る」のも、これと同じ仕組みである。
-/

/-! ### 記法もクラスで動いている

[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の先取りで、`+` は `HAdd.hAdd` を使う記法であり、
型に応じて演算が選ばれると述べた。同じ型どうしの足し算を指定するために、
標準ライブラリにはクラス `Add` が用意されている:

    class Add (α : Type u) where
      add : α → α → α

`Point` に足し算を登録してみる:
-/

instance : Add Point where
  add p q := ⟨p.x + q.x, p.y + q.y⟩

#check Point.mk 1 2 + Point.mk 3 4

/-!
    { x := 1, y := 2 } + { x := 3, y := 4 } : Point

表示の `{ x := 1, y := 2 }` は `Point.mk 1 2` の**別表示**である
（フィールド名付きの structure リテラル。書くときにも使える）。
登録した瞬間から、記法 `+` が `Point` でも通るようになった。
`x` 成分は `1 + 3` で `4` のはずである:
-/

#eval (Point.mk 1 2 + Point.mk 3 4).x

/-!
    4
-/

/-! ### 補足: `+` と数値リテラルの登録簿

正確に言うと、`+` の読み先は、左右の型が違ってもよいクラス `HAdd` の関数
`HAdd.hAdd` である。「`Add α` があれば `HAdd α α α` にもなる」という**橋渡しの
インスタンス**が標準ライブラリに用意されているので、`Add` を登録するだけで
記法まで使えるようになる。登録簿の検索は、このように**連鎖**する。

数字のリテラルにも同じ仕組みがある。数字 `2` は `OfNat.ofNat 2` の略記で、
クラス `OfNat` の instance が、期待される型ごとに読み方を決めている。
[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)で `2` が `Nat` とも `Int` とも読まれたのも、
[3節](#sec-Trial5.subtypes)の補足で `(5 : Fin 3)` が 3 で割った余りの `2` と
読まれたのも、`Nat`・`Int`・`Fin n` それぞれの `OfNat` の instance がそう実装されているから
である。「記法はクラスで動く」という、この節の主題の一例である。

なお、この教材の `Pointed` は練習用の自作クラスである。標準ライブラリにも
同じ形のクラス `Inhabited`（フィールド名は `default`）があり、
「少なくとも1つ項を持つ型」の既定値として広く使われている。
-/

/-! CALLOUT_START optional -/

/-! ### 補足: 命題の `#eval` と `def` の展開

命題の中には、真偽を計算して判定できるものがある。例えば次は `true` と表示される。
-/

#eval 2 < 3

/-!
    true

このとき `#eval` は、`2 < 3` の真偽を判定するためのインスタンスを探し、
その判定を実行している。そのインスタンスの型は `Decidable (2 < 3)` である。
`Decidable` は、命題について、証明か否定の証明を持つ判定結果を表すクラスで、
自然数の不等式には計算可能な判定の仕組みが用意されている。

ところが、この命題に `def` で名前を付けると、同じようには表示できない。
-/

def z : Prop := 2 < 3

/-!
    #eval z

    error: failed to synthesize
      Decidable z

`z` は定義を展開すれば `2 < 3` であり、命題が変わったわけではない。
ここで失敗したのは、`Decidable z` のインスタンスの自動探索である。

**定義をどこまで展開するかは、行っている処理によって異なる。**
通常の型検査では、必要に応じて `def` の中身を展開して型を照合する。
例えば次の `def` は受理される。
-/

def zFromLt (h : 2 < 3) : z := h

/-!
`h` の型は `2 < 3`、要求される型は `z` だが、定義を展開すれば一致する。
一方、インスタンス探索では展開する定義が制限されており、
この通常の `def z` は展開されない。そのため、既にある自然数の不等式の判定へ
自動ではたどり着けない。「型検査で展開して一致を確かめられること」と
「インスタンス探索がその定義を展開して探すこと」は区別して読む必要がある。

この場合は、元の命題の判定を使って `Decidable z` を明示的に登録できる。
-/

instance : Decidable z := inferInstanceAs (Decidable (2 < 3))

#eval z

/-!
    true

`inferInstanceAs (Decidable (2 < 3))` は、指定した型のインスタンスを探す項である。
ここでは探索する型を `Decidable (2 < 3)` と明示したので、標準の判定が見つかる。
その項を `Decidable z` として使えるかの型検査では `z` の定義が展開されるため、
登録が受理される。以後は `Decidable z` 自体が見つかり、`#eval z` も実行できる。
-/

/-! CALLOUT_END -/

/-! ## 5. 記法の自作 — syntax と macro_rules {#sec-Intro2.notation}

`06_Topology.lean` は `⋃₀ S` や `{a | p a}` といった数学記法を自作している。仕組みは:

* `syntax` — 「この書き方を受け付けよ」と構文を追加する
* `macro_rules` — 「その書き方はこの項の略記である」と展開を与える

試しに、[1節](#sec-Trial5.structures)の `Pair` のための記法を作ってみる。
-/

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

/-!
`macro_rules` の行はこう読む。`` `(…) `` は**構文の断片**を作る引用符、
`$x`・`$y` は受け取った断片をそこへ埋め込む印である。つまりこの行は
「`⟪x, y⟫` と書かれたら、`Pair.mk x y` と書かれたことにせよ」と読める。

すると `⟪1, true⟫` は `Pair.mk 1 true` に展開されてから型検査されるので、
型は `Pair Nat Bool` のはずである:
-/

#check ⟪1, true⟫

/-!
    { fst := 1, snd := true } : Pair Nat Bool
-/

/-!
記法は項に展開されてから型検査されるので、検査の対象はあくまで項のままである。
単純な中置・前置の記法には `infixl` や `prefix` という略記もある
（次節と `06_Topology.lean` で使用）。
-/



/-! ## 6. 集合 — `Set` を自作する {#sec-Intro2.sets}

次の章では、集合の上に位相を組み立てる。その土台となる集合をここで作ろう。
第2・4章で身につけた証明の書き方を、ここで使ってみる。
[3節](#sec-Trial5.subtypes)では、述語を満たす値と証明を組にした。
ここでは、値を切り出す条件である述語そのものを、一つの集合として扱う。

`X` の部分集合を1つ指定することは、「各 `a : X` が入っているかどうか」を
決めること——つまり **`X` 上の述語を1つ与えること**と同じである。そこで:
-/

/-- `X` の部分集合の型。実体は述語 `X → Prop` そのもので、新しいデータは何もない。 -/
def Set (X : Type) : Type := X → Prop

#check Set

/-!
    Set (X : Type) : Type

[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の `Map` と同じく、「型を受け取って型を返す関数」である。

述語 `p` を集合とみなすときの「宣言」も1つ用意する。定義上は恒等関数だが、
「述語を集合と読み替えました」という意思表示をこの名前が担う:
-/

def setOf {X : Type} (p : X → Prop) : Set X := p

#check setOf

/-!
    setOf {X : Type} (p : X → Prop) : Set X

数学の内包記法 `{a | p a}` も、[5節](#sec-Intro2.notation)の道具でそのまま自作できる:
-/

syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

/-!
所属の記号 `∈`（`\in` と打つ）は、標準ライブラリの記法用クラス `Membership` に
instance 登録すると使えるようになる——[4節](#sec-Intro2.classes)で見た「記法はクラスで動く」の実戦である。
中身は「集合（＝述語）`s` に点 `a` を適用する」だけ。
まずクラスそのものを見ておく:
-/

#check Membership

/-!
    Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)

`Membership α γ` は「入れ物 `γ` に要素 `α` が属する」という記法 `∈` のための
クラスである。次の登録は `γ := Set X`・`α := X` の場合に当たる。
-/

/-! ### 補足: `Membership` の宇宙変数と `outParam`

表示は宇宙変数付きだが、この教材の範囲ではどれも `Type` と読んでよい
（[`01_TypesAndTerms.lean` 1節](#sec-Intro1.terms-types)）。`outParam` は instance 探索へのヒントで、
「`∈` の右の入れ物の型 `γ` が分かれば、左の要素の型 `α` はそこから自動で
決まる」という指定である。
-/

instance {X : Type} : Membership X (Set X) := ⟨fun s a => s a⟩

#check (1 : Nat) ∈ ({n | n = 1} : Set Nat)

/-!
    1 ∈ setOf fun n ↦ n = 1 : Prop

型が `Prop` と付いた＝登録に成功している。読むときの注意を2つ。

第一に、ここでは `1 : Nat` と `… : Set Nat` の二つの型注釈で、
どの型の話かを明示している。数字や内包記法を読むときにも、
周囲から伝わる型が手がかりになる。

第二に、表示が `{n | n = 1}` に戻らず `setOf fun n ↦ n = 1` になる理由:
自作した記法は**構文解析（読む方向）専用**で、表示（書く方向）の規則までは
作っていないからである。以後の表示の枠でも、展開先がそのまま見える。

「`a ∈ s` である」ことの証明は、定義を展開すればただの `s a` である。
実際に確かめてみる:
-/

def one_mem_singleton : (1 : Nat) ∈ ({n | n = 1} : Set Nat) := rfl

/-!
`∈` と `setOf` を定義に沿って展開すると、この命題は `1 = 1` そのものになる。
だから `rfl` で閉じる——型検査が**定義を展開して**照合してくれるのである。

包含 `⊆` も同じやり方で登録する。「`s` のどの要素も `t` の要素」——
`∀` と `→` で書けるようになった言明である:
-/

instance {X : Type} : HasSubset (Set X) := ⟨fun s t => ∀ a, a ∈ s → a ∈ t⟩

#check ({n | n = 1} : Set Nat) ⊆ {n | n = 2}

/-!
    (setOf fun n ↦ n = 1) ⊆ setOf fun n ↦ n = 2 : Prop

型は `Prop`——包含は命題である。`s ⊆ t` の証明とは、定義から
「各点で、`s a` の証明から `t a` の証明を作る関数」に他ならない。

最初の性質を証明してみよう。反射律は「各点で仮定をそのまま返す」だけである:
-/

def Set.subset_refl {X : Type} (s : Set X) : s ⊆ s := fun _ ha => ha

#check Set.subset_refl

/-!
    Set.subset_refl {X : Type} (s : Set X) : s ⊆ s

`s ⊆ s` を展開すれば `∀ a, a ∈ s → a ∈ s` である。
点 `a` と `ha : a ∈ s` を受け取り、その `ha` を結論の証明として返している。
第2章で学んだ、全称量化と含意を関数として読む方法を使った。名前を `Set.〜` にしたのは
ドット記法（[1節](#sec-Trial5.structures)で見た関数適用の略記）のためで、
この命名の仕組みは次節で説明する。

`06_Topology.lean` はこの `Set` を土台に、`∩`・`∪`・補集合・像・逆像・集合族……と
道具を足していく。
-/



/-! ## 7. namespace — 名前の接頭辞 {#sec-Intro2.namespaces}

[1節](#sec-Trial5.structures)のドット記法や、前節の `Set.subset_refl` という名前を
支えている**名前空間**の仕組みを見ておく。
`namespace N … end N` で囲うと、中の宣言の本名に `N.` が付く:
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

外からはフルネームで呼ぶ。
-/

/-!
`p.x` が効くのは、`x` が**型名と同じ名前空間** `Point` に置かれているから
である。`06_Topology.lean` では `namespace Set` の中に集合の関数（`Set.ext` など）を
置いていく——`s.ext` のようなドット記法が効くのはそのためである。
逆に、名前空間の**中**の名前を接頭辞なしで使えるようにする `export N (名前)`
という宣言もある（`06_Topology.lean` が `TopologicalSpace.IsOpen` を
`IsOpen` と書くために使っている）。

これで `06_Topology.lean` を読む準備が整った。
-/

/-! ### 先取り（06_Topology の公理監査）: 商型 `Quot`

Lean の核には依存関数型と帰納型のほかに商型（`Quot`）などもある。
本編では商型を直接は使わないが、関数の外延性 `funext` が商型の上に
建っているため、`06_Topology.lean` 末尾の公理の一覧には顔を出す
（発展演習 `07_Exercises.lean` では商型を直接使う）。
-/

/-! ## 8. ✏ 練習 — 章末問題 {#sec-Trial5.practice}

1. `center : Point`、`radius : Nat` を持つ構造体 `Circle` を定義せよ。
   `makeCircle : Point → Nat → Circle` を構成子名と `⟨…⟩` の両方で書き、
   点 `(1,2)`、半径 `3` の円の `center.x` と `radius` を `#eval` で確かめよ。

2. 点付き集合 $(A,a)$ と写像 $f:A\to A$ から $(A,f(a))$ を作る
   `mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType` を書け。
   `#reduce (mapPointed pointedNat Nat.succ).point` の結果を予想して確かめよ。

3. 二つの偶数の和を、偶数という条件を持つ値として返す
   `addEven (n m : EvenNat) : EvenNat` を書け。
   ヒント：値は `n.val + m.val`、その根拠は `isEven_add n.property m.property` である。
   `#eval (addEven evenFour evenFour).val` を確かめよ。

4. 本文で `Pointed Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : Pointed Bool where point := false` を登録し、
   `#check (inferInstance : Pointed Bool)` と
   `def pointPair_bool_fst : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool` が
   通るようになることを確かめよ（登録した瞬間から、一般的な定理も適用できる）。

5. `Pointed` と同じ手順でマグマを自作する:
   `class Magma (α : Type) : Type where op : α → α → α` を宣言し、
   `instance : Magma Nat where op := Nat.add` を登録して、
   `#check (inferInstance : Magma Nat)` が通ることを確かめよ。

6. `pointPair` にならって、汎用関数
   `opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a` を書き、
   `#eval opSelf Nat 3` の値を予想してから確かめよ。

7. 本文の「積に構造を誘導する」にならって、成分ごとに演算する
   `instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β)` を登録し、
   `#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd` の値を
   予想してから確かめよ（探索の連鎖まで含めて、`Pointed` と同じに動く）。

8. `Add` にならって `instance : Mul Point where mul p q := ⟨p.x * q.x, p.y * q.y⟩`
   を登録し、`#eval (Point.mk 2 3 * Point.mk 4 5).x` の値を予想してから確かめよ。

9. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。

10. `infixl:65 " ⊞ " => myAdd` で、`03_InductiveTypes.lean` の `myAdd`（`MyNat` の足し算）に
   中置記法を与え、`#reduce MyNat.zero.succ ⊞ MyNat.zero.succ` の表示を
   予想してから確かめよ。

11. 推移律を項で書け（各点で2つの仮定を順に適用する）:

       def Set.subset_trans {X : Type} {s t u : Set X}
           (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u

12. `def evens : Set Nat := {n | IsEven n}` と宣言せよ（`IsEven` は [第4章1節](#sec-Trial4.existence)の述語）。`def four_mem_evens : (4 : Nat) ∈ evens := ⟨2, rfl⟩` が通ることを確かめよ。

13. 全体集合 `def allNat : Set Nat := {_n | True}` を定義し、
   `def subset_allNat : ∀ s : Set Nat, s ⊆ allNat` を書け
   （各点の証明は `True.intro`。束縛子 `_n` の `_` は「使わない」印である）。

14. `def odds : Set Nat := {n | ¬IsEven n}` を宣言し、
   `#check (3 : Nat) ∈ odds` の表示を予想してから確かめよ。

15. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
-/
