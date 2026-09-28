/-!
# 型と項 II — 帰納型

第1・2章では、`fun` で関数を作り、適用でその関数を使った。
この章では、**構成子で項を作り、`match` でその項を使う**という道具を加える。
有限集合、直和、直積、集合族の直和を、同じ仕組みで表していこう。

自然数のように再帰的に作られる型も扱う。
最後に、第2章で使った等式と自然数の不等式を帰納型として読み、
証明の項をどのように作り、使うのかを確かめる。
-/

/-!
## 1. 構成子と場合分け {#sec-Trial3.constructors}

`inductive` は、新しい型と、その型の項を作る**構成子**を一緒に導入する。
まず、三つの色を表す型を定義しよう。構成子の名前は `型名.構成子名` になる。
-/
inductive Signal : Type where
  | red : Signal
  | yellow : Signal
  | green : Signal

#check Signal.red
/-!
    Signal.red : Signal

この宣言によって、新しい型 `Signal` と三つの項 `Signal.red`、`Signal.yellow`、`Signal.green` が一緒に導入された。
それぞれを赤・黄・緑と読むのは人間が与える解釈であり、名前だけで色の性質や信号の動きが決まるわけではない。
集合の言葉では、三点集合を作ったと思えばよい。
三つの構成子で場合を尽くせること、異なる構成子が等しくないことは、帰納型の仕組みに基づく。
「これらで全部」を使うための再帰・帰納法の原理が `Signal.rec` であり、`match` もこの原理に基づく。
「互いに別々」であることの証明には `Signal.noConfusion` を使える。後者と同じ仕組みを、否定を扱う第4章で `Bool` を例に見る。
-/

/-!
### match で項を使う

`match 対象 with` の後に、構成子ごとに `| 構成子 => 返す項` を並べる。
**`match … with …` 全体が一つの項**であり、対象に対応する枝の項が結果になる。
-/
#eval match Signal.red with
  | Signal.red => 0
  | Signal.yellow => 1
  | Signal.green => 2
/-!
    0

ここでは、どの枝でも `Nat` の項を返しているので、全体の型は `Nat` である。
`match`、`with`、`|`、`=>` は、この項を組み立てるための特別な記号である。
-/

/-!
### 関数の本体で場合分けする

関数記法 `fun` と `match` を組み合わせ、次の信号を返す関数を書こう。
対象 `s : Signal` を受け取り、その構成子によって返す色を決める。
-/
def Signal.next : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.green
  | Signal.yellow => Signal.red
  | Signal.green => Signal.yellow

#eval Signal.next Signal.red
/-!
    Signal.green

`fun` が入力を受け取り、その本体の `match` が値を選ぶ。
有限集合からの写像を、各点の行き先を指定して定義するのと同じ形である。
`match` で場合分けする対象や結果の型は、有限集合に限らない。後では自然数についても使う。
-/

/-!
### ✏ 練習 {#sec-Trial3.constructors-exercise-42721aca}

1. `Signal.red`、`Signal.yellow`、`Signal.green` をそれぞれ `0`、`1`、`2` に送る
   `signalCode : Signal → Nat` を定義せよ。各枝の型を確かめ、`signalCode Signal.yellow` の値を予想せよ。

2. `Signal.next` と逆向きに色を送る `prev : Signal → Signal` を書け。
   `prev (Signal.next Signal.red)` の値を確かめよ。
-/

/-!
### 一点の型と空の型

構成子が一つで引数を取らない型を自作すると、一点集合に対応する。
-/
inductive MyUnit : Type where
  | unit : MyUnit

/-!
構成子を一つも持たない型は、空集合に対応する。
-/
inductive MyEmpty : Type

/-!
空の型にも使い方はある。項を受け取ったとして、場合分けすべき構成子が一つもなければよい。
その場合分けを `nomatch` と書く。
-/
def emptyToNat (e : MyEmpty) : Nat := nomatch e
/-!
これは `MyEmpty` の項を作ったのではなく、`MyEmpty → Nat` という関数を作ったのである。
-/

/-!
### 補足: Prelude にある型

標準環境には、同じ形の型 `Unit` と `Empty` が既に用意されている。
`Unit` の構成子は `Unit.unit` で、`Empty` には構成子がない。
二点の型 `Bool` も、構成子 `Bool.false` と `Bool.true` を持つ帰納型である。
これらは標準で読み込まれる Prelude に含まれるので、使う側で定義し直す必要はない。
-/

/-!
## 2. 直和と直積 {#sec-Trial3.sums-products}

構成子も関数なので、引数を受け取れる。
次は「自然数に札を付けたもの」と「真偽値に札を付けたもの」をまとめた型である。
構成子の名前を `inn`・`inb` とし、自然数から入れる場合と真偽値から入れる場合を区別する。
-/
inductive TaggedSum : Type where
  | inn (n : Nat) : TaggedSum
  | inb (b : Bool) : TaggedSum

#check TaggedSum.inn
/-!
    TaggedSum.inn (n : Nat) : TaggedSum

構成子 `TaggedSum.inn` は `Nat → TaggedSum` という関数である。
集合の言葉では、この型は自然数と真偽値の**直和（非交和）**に対応する。
-/

#check TaggedSum.inb
/-!
    TaggedSum.inb (b : Bool) : TaggedSum

同様に、`TaggedSum.inb` は `Bool → TaggedSum` という関数である。
この構成子そのものは関数であり、それに `true : Bool` を渡した `TaggedSum.inb true` は、
できあがった `TaggedSum` 型の項である。
`true` 自体は `Bool` 型なので、`TaggedSum` 型の項が必要な場所では `TaggedSum.inb true` と書く。
この例では、構成子の適用を省略しても自動で補われるわけではない。
-/

/-!
### 中身を受け取る場合分け

`match` の枝で `TaggedSum.inn n` と書くと、その構成子に渡された自然数に `n` と名前を付けられる。
返す項では、その名前を使ってよい。
-/
def valueOf : TaggedSum → Nat := fun x =>
  match x with
  | TaggedSum.inn n => n
  | TaggedSum.inb _ => 0

#eval valueOf (TaggedSum.inn 7)
/-!
    7

枝の `TaggedSum.inb _` にある `_` は、その位置にはどの値が来てもよく、その値に名前を付けないことを表す。
ここでは `true` と `false` のどちらも同じ枝で扱い、その値を使わずに `0` を返している。
直和からの写像は、左側と右側のそれぞれについて行き先を定めることで作れる。
-/

#eval valueOf (TaggedSum.inb true)
/-!
    0

まず `TaggedSum.inb true` という項を作り、それを `valueOf` に渡すので、括弧でまとめている。
括弧を外した `valueOf TaggedSum.inb true` は `(valueOf TaggedSum.inb) true` と読まれ、
`valueOf` に必要な `TaggedSum` 型の項の代わりに構成子そのものを渡すことになり、型が合わない。
-/

/-!
### 構成子が違う場合と、同じ場合

`TaggedSum.inn n` と `TaggedSum.inb b` が等しくないことも、
`TaggedSum.inn n = TaggedSum.inn m` から `n = m` が言えることも、Leanで証明できる。
後者を表す補題は、帰納型の宣言に伴って生成される。
-/
#check TaggedSum.inn.inj
/-!
    TaggedSum.inn.inj {n n✝ : Nat} : TaggedSum.inn n = TaggedSum.inn n✝ → n = n✝

第2章で見た単射性と同じく、像の等式の証明を受け取り、中身の等式の証明を返す関数である。
「構成子は単射」と仮定を付け足したのではなく、その証明を帰納型の仕組みから得ている。
`TaggedSum.inb` についても同様である。集合の言葉では、この二つの構成子は、
それぞれの集合から直和への標準的な単射に対応する。
-/

/-!
### 中身の型をパラメータにする

自然数と真偽値に限定せず、任意の型 `A` と `B` の直和を同じように作れる。
-/
inductive MySum (A B : Type) : Type where
  | inl (a : A) : MySum A B
  | inr (b : B) : MySum A B

#check MySum.inl
/-!
    MySum.inl {A B : Type} (a : A) : MySum A B

型を作る `MySum` には `MySum Nat Bool` と二つの型を渡す。
構成子の型引数は暗黙引数になっている。例えば `(MySum.inl 3 : MySum Nat Bool)` では、
結果の型注釈から `A := Nat`、`B := Bool` が決まる。
標準の直和型 `A ⊕ B` と、その構成子 `Sum.inl`・`Sum.inr` も同じ形で使う。
-/

/-! CALLOUT_START optional -/
/-!
### 補足: 型をパラメータにした取り出し関数

`valueOf` と同じ形で、一般の直和から項を取り出す関数も書ける。
左側ならその項を、右側ならあらかじめ受け取った既定値 `d` を返す。
-/
def getLeft {A B : Type} (d : A) : MySum A B → A := fun x =>
  match x with
  | MySum.inl a => a
  | MySum.inr _ => d

#check getLeft
/-!
    getLeft {A B : Type} (d : A) : MySum A B → A

`A` と `B` は暗黙引数である。次の適用では、`0` と `true` の型からそれぞれ補われる。
-/
#eval getLeft 0 (MySum.inr true)
/-!
    0
-/
/-! CALLOUT_END -/

/-!
### ✏ 練習 {#sec-Trial3.practice-review-2}

1. `swapSum : MySum A B → MySum B A` を定義せよ。
   左側から来た項は右側へ、右側から来た項は左側へ送ること。
-/

/-!
### 組も帰納型で作る

今度は、`A` の項と `B` の項を**両方**持つ組を作りたい。
構成子を一つにし、その構成子に二つの引数を渡す。
-/
inductive MyPair (A B : Type) : Type where
  | mk (a : A) (b : B) : MyPair A B

#check (MyPair.mk 3 true : MyPair Nat Bool)
/-!
    MyPair.mk 3 true : MyPair Nat Bool

直和ではどちらかの構成子を選んだ。直積では、一つの構成子に両方の材料を渡す。
型が同じ引数を二つ取る場合も、異なる型の引数を取る場合も、この書き方で扱える。
-/

/-!
### 組を使うときも match

構成子が一つなら、場合分けは一つの枝で済む。
第1成分を返す関数を書いてみよう。
-/
def pairFirst {A B : Type} : MyPair A B → A := fun p =>
  match p with
  | MyPair.mk a _ => a

#eval pairFirst (MyPair.mk 3 true)
/-!
    3

標準の直積 `A × B` も `Prod.mk a b` で作り、`match` の `Prod.mk a b` の枝で使える。
例えば次は、二つの成分を交換する関数である。
-/
def swapPair {A B : Type} : A × B → B × A := fun p =>
  match p with
  | Prod.mk a b => Prod.mk b a

/-!
### ✏ 練習 {#sec-Trial3.practice-review-3}

1. 写像 `f : X → A` と `g : X → B` から、`x` を組 `(f x, g x)` に送る
   `pairMaps : X → MyPair A B` を定義せよ。型 `X A B` と写像 `f g` も引数に取ること。
-/

/-!
### 補足: 帰納型を直和と直積で見る

`MySum A B` では、構成子をどちらか一つ選ぶ。これは直和に対応する。
`MyPair A B` では、一つの構成子に `A` の項と `B` の項を両方渡す。これは直積に対応する。
一般にも、構成子の選択を直和、それぞれの構成子が受け取る材料を直積として読むと、
帰納型がどんな項を作るかを見通しやすい。引数の型が前の引数に依存する場合は、次に見る依存する組になる。
-/

/-!
## 3. 依存する組 {#sec-Trial3.dependent-pairs}

集合族 $(B(a))_{a\in A}$ の直和 $\bigsqcup_{a\in A} B(a)$ の要素は、
添字 $a$ を一つ選び、さらにその集合の要素 $b\in B(a)$ を一つ選んだ組 $(a,b)$ である。
第二成分を選ぶ集合は、第一成分の値によって決まる。

第1章で使った `Fin n` を例にしよう。
「自然数 `n` と、`n` 未満の番号を一つ選んだ組」を次のように定義できる。
-/
inductive Numbered : Type where
  | mk (n : Nat) (i : Fin n) : Numbered

#check Numbered.mk
/-!
    Numbered.mk (n : Nat) (i : Fin n) : Numbered

構成子は、`n` を受け取ってから **`Fin n` 型の**項を受け取る依存関数である。
-/

/-!
### 依存する組を作る

`n := 3` を選ぶなら、次に渡す項は `Fin 3` 型でなければならない。
-/
def numberedThree : Numbered := Numbered.mk 3 (2 : Fin 3)
def numberedFive : Numbered := Numbered.mk 5 (4 : Fin 5)

#check Numbered.mk 3
/-!
    Numbered.mk 3 : Fin 3 → Numbered

二つの組はどちらも `Numbered` 型だが、中に持つ番号の型は違う。
`Fin 0` は空なので、第一成分を `0` にした組は作れない。
ここでは `Fin n` の内部の定義には立ち入らず、第1章で使った型の族として扱う。
-/

/-!
### 第一成分を取り出す

`Numbered` の構成子は一つなので、使うときも一つの枝でよい。
まず、大きさを取り出す関数を書く。
-/
def Numbered.size : Numbered → Nat := fun p =>
  match p with
  | Numbered.mk n _ => n

#eval Numbered.size numberedThree
/-!
    3

この関数の行き先は固定した `Nat` である。
枝に入ると `n : Nat` と `i : Fin n` が使えるが、ここでは `n` だけを返している。
-/

/-!
### 第二成分の型も入力から決まる

番号を取り出す関数の行き先は、入力された組の大きさで変わる。
したがって、その型にも入力 `p` が現れる。関数全体の型は、次の依存関数型である。

    Numbered.index : (p : Numbered) → Fin (Numbered.size p)

第一成分を返す `Numbered.size : Numbered → Nat` とは異なり、結果の型が入力ごとに変わる。
-/
def Numbered.index (p : Numbered) : Fin (Numbered.size p) :=
  match p with
  | Numbered.mk _ i => i

#check Numbered.index numberedThree
/-!
    numberedThree.index : Fin numberedThree.size

`Numbered.mk n i` の枝では `Numbered.size p` が `n` に計算される。
要求される型は `Fin n` になり、手元の `i : Fin n` をそのまま返せる。
-/

/-!
### 一般の依存和

任意の型の族 `B : A → Type` に対しても、同じ構成子を書ける。
-/
inductive FamilyPair (A : Type) (B : A → Type) : Type where
  | mk (a : A) (b : B a) : FamilyPair A B
/-!
標準の型では、これに対応する依存和を `Sigma B`、または `(a : A) × B a` と書き、
`Sigma.mk a b` で項を作る。
特に `(n : Nat) × Fin n` は、自然数 `n` を一つ選び、続いて **その `n` に対応する `Fin n`** の項を選んだ組の型である。
第一成分と第二成分の型を独立に決める普通の直積 `Nat × B` との違いは、この依存にある。
-/
def numberedSigma : (n : Nat) × Fin n := Sigma.mk 3 (2 : Fin 3)

#check numberedSigma
/-!
    numberedSigma : (n : Nat) × Fin n

族が定数なら、第二成分の型は第一成分によらない。普通の直積もこの形の特別な場合である。
-/

/-!
### すべての添字で選ぶか、一つの添字を選ぶか

同じ族 `B : A → Type` に対して、二通りの項の作り方がある。

| 型 | 項を作る | 項を使う |
|---|---|---|
| 依存関数 `(a : A) → B a` | `fun a => …` で、どの `a` にも答えを用意する | `f a` と対象を渡す |
| 依存和 `(a : A) × B a` | `Sigma.mk a b` で、一つの `a` と `b : B a` をまとめる | `match` で `a` と `b` に名前を付ける |

第4章では、型の族を命題の族に置き換えて、全称量化と存在量化の証明を読む。
-/

/-!
### ✏ 練習 {#sec-Trial3.dependent-pairs-exercise-baf1c270}

1. `n : Nat` から、大きさが `n + 1` で番号が最後の `n` である組を返す
   `attachLast : Nat → Numbered` を定義せよ。標準の `Fin.last : (n : Nat) → Fin (n + 1)` を使ってよい。
   `Numbered.size (attachLast 3)` と `Numbered.index (attachLast 3)` の値も確かめよ。
-/

/-!
## 4. 自然数と再帰 {#sec-Trial3.recursion}

構成子の引数に、いま定義している型自身を使える。
自然数を、零と「一つ次の数を作る操作」で定義してみよう。
-/
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat.succ (MyNat.succ MyNat.zero)
/-!
    MyNat.zero.succ.succ : MyNat

表示の `MyNat.zero.succ.succ` は、`MyNat.succ (MyNat.succ MyNat.zero)` のことである。
この型の項は、`zero` に `succ` を有限回重ねて作る。標準の `Nat` も同じ形で定義されている。
-/

/-!
### 補足: 集合の方程式としての再帰

集合の言葉では、零のための一点と、次の数を作るためのコピーを合わせるので、
$X \cong 1 \sqcup X$ という形が現れる。
ただし、この方程式だけで自然数が決まるわけではない。
帰納型では、`zero` から `succ` を有限回使って作ったものですべて、という条件が付く。
これが、構成子から生成される最小のもの、という見方である。
-/

/-!
### 自分より小さい項を使う

加法を、第二引数について場合分けして定義しよう。
`succ k` の場合は、中に入っていた小さい項 `k` への加法を使う。
-/
def myAdd : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | MyNat.zero => m
  | MyNat.succ k => MyNat.succ (myAdd m k)
/-!
`m + 0 = m`、`m + (k + 1) = (m + k) + 1` を項の作り方として書いている。
再帰呼び出しが構造的に小さい項へ進むことをLeanが確かめる。
-/
#reduce myAdd (MyNat.succ MyNat.zero) (MyNat.succ MyNat.zero)
/-!
    MyNat.zero.succ.succ
-/

/-!
### 補足: 再帰が止まることの検査

同じ入力のまま自分を呼ぶ、次の定義は受理されない。

    def loop (n : MyNat) : MyNat := loop n

再帰呼び出しで引数が変わらず、停止することを確かめられないためである。
`myAdd` では `MyNat.succ k` の中の `k` へ進むので、構造が小さくなることを確認できる。
Lean は、このように再帰が止まる根拠も検査している。
-/

/-!
### ✏ 練習 {#sec-Trial3.practice-review-5}

1. `MyNat.zero` を `0` に、`MyNat.succ k` を `toNat k + 1` に送る
   `toNat : MyNat → Nat` を再帰で定義せよ。
-/

/-!
### 各自然数への証明を再帰で作る

同じ再帰を使い、自然数ごとの等式の証明も作れる。
標準の `Nat` で、`0 + n = n` を証明しよう。

零の場合は計算で一致する。`k + 1` の場合は、`0 + k = k` の両辺に一つ加えればよい。
この「`k` の場合の証明」が、次のコードの再帰呼び出しである。
-/
def zero_add_by_rec : ∀ n : Nat, 0 + n = n := fun n =>
  match n with
  | Nat.zero => rfl
  | Nat.succ k => congrArg Nat.succ (zero_add_by_rec k)
/-!
`congrArg` が返す型は `Nat.succ (0 + k) = Nat.succ k`。
これは `0 + Nat.succ k = Nat.succ k` と計算で一致する。
**証明を返す依存関数を再帰で作ることが、数学的帰納法による証明になっている。**
-/

/-! CALLOUT_START optional -/
/-!
### 補足: 定義から計算して一致することと、等式を証明すること

自然数の加法は第二引数について再帰する。そのため `n + 0` は `n` に計算される。
一方、変数 `n` に対する `0 + n` は、`n` がどの構成子でできているか分からず、計算を進められない。
-/
def add_zero_by_rfl (n : Nat) : n + 0 = n := rfl
/-!
次の形では、`rfl` だけでは証明できない。

    def zero_add_bad (n : Nat) : 0 + n = n := rfl

そこで本文の `zero_add_by_rec` では、`n` について場合分けし、帰納法で等式を証明した。
定義を展開して計算すると一致することを**定義的に等しい**という。
型の照合ではこの等しさを使えるが、証明された等式がすべて定義的な等しさになるわけではない。

同じ理由で、乗法も `0 * n = 0` を `rfl` だけで証明できるわけではない。
第二引数の作られ方に沿って、証明を再帰で作れる。
-/
def zero_mul_by_rec : ∀ n : Nat, 0 * n = 0 := fun n =>
  match n with
  | Nat.zero => rfl
  | Nat.succ k => zero_mul_by_rec k
/-!
次の数の枝では `0 * Nat.succ k` が `0 * k + 0`、さらに `0 * k` に計算されるので、
再帰呼び出しで得た証明をそのまま使える。
-/
/-! CALLOUT_END -/

/-! CALLOUT_START optional -/
/-!
### 補足: 2n = n + n を定義から証明する {#sec-Trial3.two-mul}

第4章では `Nat.two_mul` を既知の定理として使う。その内容も、再帰と等式の操作から証明できる。
数学的帰納法で考えると、零のときは両辺とも零である。
`2 * k = k + k` を仮定すれば、$2(k+1)=2k+2=(k+k)+2=(k+1)+(k+1)$ となる。

最後の並べ替えには、$(n+1)+m=(n+m)+1$ を使った。
これも `m` に関する帰納法で証明しておこう。
-/
def succ_add_from_scratch : ∀ n m : Nat, (n + 1) + m = (n + m) + 1 := fun n m =>
  match m with
  | Nat.zero => rfl
  | Nat.succ k => congrArg (fun x => x + 1) (succ_add_from_scratch n k)

/-!
零の枝は計算で一致する。次の数の枝は、一つ前の等式の両辺に1を加えた証明である。
これを使うと、二倍の等式の帰納段階も書ける。
-/
def two_mul_from_scratch : ∀ n : Nat, 2 * n = n + n := fun n =>
  match n with
  | Nat.zero => rfl
  | Nat.succ k =>
    Eq.trans (congrArg (fun x => x + 2) (two_mul_from_scratch k))
      (Eq.symm (congrArg (fun x => x + 1) (succ_add_from_scratch k k)))

#check two_mul_from_scratch
/-!
    two_mul_from_scratch (n : Nat) : 2 * n = n + n

帰納法の仮定は、自分自身への再帰呼び出しで得ている。
計算だけで一致しない箇所を、`congrArg` と `Eq.trans` でつないだ。
-/
#print axioms two_mul_from_scratch
/-!
    'two_mul_from_scratch' does not depend on any axioms

「既知の定理」も、定義と計算までたどれば、検査済みの証明の項として与えられている。
-/
/-! CALLOUT_END -/

/-!
## 5. 等式と自然数の不等式 {#sec-Trial3.indexed}

ここまでは、構成子が `Signal` や `MyNat` という一つの型の項を返していた。
次は、構成子が**型の族のどの型に項を作るか**にも注目する。

`Eq a b` は、対象 `a` と `b` ごとに変わる命題である。
`Nat.le n m` も、自然数 `n` と `m` ごとに変わる命題である。
第2章で見た「述語は型の族」という見方で、これらの族を帰納的に定義する。

依存する組では、第二引数の型に第一引数が現れた。
ここではさらに、構成子の**結果の型**にも、引数として受け取った対象が現れる。
-/

/-!
### Eq の構成子を読む

`a = b` は `Eq a b` の記法である。型引数を明示すると、定義は次の形になる。

    inductive Eq {A : Sort u} : A → A → Prop where
      | refl (a : A) : Eq a a

`Sort u` は `Prop` や `Type` などをまとめて扱う表記で、等式は特定の型に限定されない。
唯一の構成子 `Eq.refl` が直接作るのは、両辺が同じ `Eq a a` の証明である。

第2章の「最小の反射的関係」という見方と結び付けると、構成子は対角に証明を作っている。
ただしLeanで等式を使う際には、帰納型の除去の原理に従って項を組み立てる。
`rfl` と `Eq.refl` の関係は、第2章で説明したとおりである。
-/

/-!
### 対称性を自分で証明する

`h : a = b` を受け取り、`b = a` の証明を返す関数を作ろう。
等式の構成子は `Eq.refl` の一つなので、その場合を扱う。
-/
def eqSymmByMatch {A : Sort u} {a b : A} (h : a = b) : b = a :=
  match h with
  | Eq.refl _ => Eq.refl a
/-!
この枝では `b` が `a` に特殊化される。
返すべき型 `b = a` も `a = a` となるので、`Eq.refl a` を返せる。
パターンの `_` は、この構成子の引数が添字から決まるため、名前を付けずに書いている。

単なる構成子の名前の判別だけでなく、**その構成子の結果の型に合わせて、枝の中の型も変わる**。
これが、等式の証明を使うときの要点である。
-/

/-!
### 推移性を証明する

次は `a = b` と `b = c` の証明を受け取り、`a = c` の証明を返す。
第二の等式について場合分けすればよい。
-/
def eqTransByMatch {A : Sort u} {a b c : A}
    (hab : a = b) (hbc : b = c) : a = c :=
  match hbc with
  | Eq.refl _ => hab
/-!
この枝では `c` が `b` に特殊化され、結論の型が `a = b` になる。
そこで、すでに持っている `hab` を返せる。
これが第2章で使った `Eq.trans` に相当する証明である。
-/

/-!
### congrArg に相当する関数を作る

等しい二つの対象を同じ関数で送ると、結果も等しい。
この証明も、等式の構成子による場合分けで作れる。
-/
def congrArgByMatch {A : Sort u} {B : Sort v}
    (f : A → B) {a b : A} (h : a = b) : f a = f b :=
  match h with
  | Eq.refl _ => Eq.refl (f a)
/-!
枝の中で要求される型は `f a = f a` になる。
対称性・推移性・合同性を新しい仮定として加える必要はなく、等式の帰納型の仕組みから証明できた。
-/
#print axioms eqSymmByMatch
/-!
    'eqSymmByMatch' does not depend on any axioms
-/

/-! CALLOUT_START optional -/
/-!
### 補足: 等式をもう一つ作る実験

`Eq` と同じ形の帰納型を自作し、その証明を `match` で使ってみよう。
ここでは型の範囲を `Type` に限っている。
-/
inductive MyEq {A : Type} (a : A) : A → Prop where
  | refl : MyEq a a

#check MyEq
/-!
    MyEq {A : Type} (a : A) : A → Prop

対称性の結論は `MyEq b a` だが、構成子の枝では `b` が `a` にそろうため、`MyEq.refl` を返せる。
`match` は、構成子がどの添字の型の項を作るかも使って、枝の中で要求する型を決める。
-/
def MyEq.symm {A : Type} {a b : A} (h : MyEq a b) : MyEq b a :=
  match h with
  | MyEq.refl => MyEq.refl

def MyEq.trans {A : Type} {a b c : A} (h₁ : MyEq a b) (h₂ : MyEq b c) : MyEq a c :=
  match h₁ with
  | MyEq.refl => h₂

/-!
推移性の枝では、第二の仮定の型が `MyEq a c` になるので、そのまま返せる。
標準の等式と自作の等式の間にも、互いの証明を受け取る関数を書ける。
-/
def MyEq.toEq {A : Type} {a b : A} (h : MyEq a b) : a = b :=
  match h with
  | MyEq.refl => Eq.refl a

def MyEq.ofEq {A : Type} {a b : A} (h : a = b) : MyEq a b :=
  match h with
  | Eq.refl _ => MyEq.refl
/-!
いずれも新しい公理を加えず、構成子と場合分けだけで作れた。
自作の等式の証明も、標準の等式の証明も、帰納型の同じ原理で扱っている。
-/
/-! CALLOUT_END -/

/-!
### 自然数の不等式 Nat.le

自然数の `n ≤ m` は `Nat.le n m` の記法である。定義の中心は次の二つの構成子である。

    inductive Nat.le (n : Nat) : Nat → Prop where
      | refl : Nat.le n n
      | step {m} : Nat.le n m → Nat.le n (Nat.succ m)

集合の言葉では、これは次の二条件を満たす**最小の二項関係**と考えられる。

* すべての自然数 `n` について `n ≤ n` が成り立つ。
* `n ≤ m` が成り立てば `n ≤ m + 1` も成り立つ。

第一の条件が `refl`、第二の条件が `step` に対応する。
構成子から生成される証明だけを使う、という帰納型の仕組みが、この最小性を表している。

`n` を固定すると、`Nat.le n` は右辺の自然数を添字に持つ命題の族になる。
`refl` は添字 `n` のところに証明を作り、`step` は添字 `m` の証明から添字 `m + 1` の証明を作る。

`Nat.succ m` は `m + 1` に当たる。
自然数を `zero` と `succ` で作ったのと同じように、不等式の証明を `refl` と `step` で作る。
-/

/-!
### 2 ≤ 4 の証明を作る

まず `2 ≤ 2` の証明を作り、`step` を二回使う。
-/
def two_le_four : 2 ≤ 4 := Nat.le.step (Nat.le.step Nat.le.refl)
/-!
内側から、`Nat.le.refl : 2 ≤ 2`、一回目の `step` の結果が `2 ≤ 3`、二回目の結果が `2 ≤ 4` である。
このように、証明にも組み立て方がある。
使える構成子を並べただけでなく、各適用の入力と結果の型が合っていることを確かめよう。
-/
#check Nat.le.step two_le_four
/-!
    Nat.le.step two_le_four : Nat.le 2 (Nat.succ 4)
-/

/-!
### 両辺に一つ加えても順序は保たれる

`n ≤ m` の証明から `n + 1 ≤ m + 1` の証明を作る。
数学の言葉で、**不等式の証明の作られ方に関する帰納法**を書いてみよう。

* 出発点 `n ≤ n` から作る場合、結論は `n + 1 ≤ n + 1` なので、反射性から言える。
* `n ≤ k` の証明から一段進んで `n ≤ k + 1` を作った場合を考える。
  一つ前の証明に対しては帰納法の仮定から `n + 1 ≤ k + 1` が得られる。
  その右辺をもう一つ増やせば、必要な `n + 1 ≤ (k + 1) + 1` が得られる。

どの証明もこの二通りで作られるので、これで全場合を扱った。
一つ前の証明に帰納法の仮定を使う操作を、次のコードでは再帰呼び出しで書く。
-/
def succLeSuccByMatch (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 :=
  match h with
  | Nat.le.refl => Nat.le.refl
  | Nat.le.step h' => Nat.le.step (succLeSuccByMatch n _ h')
/-!
`step` の枝では、`h'` は `n ≤ k` の証明、もとの右辺は `k + 1` である。
再帰呼び出しで `n + 1 ≤ k + 1` を得て、`step` で右辺をもう一つ増やす。
不等式の証明の構造についての帰納法を、そのまま再帰で書いている。
-/

/-!
### ✏ 練習 {#sec-Trial3.indexed-exercise-884af91c}

1. `1 ≤ 3` の証明を `Nat.le.refl` と `Nat.le.step` だけで作れ。
   次に、それを `succLeSuccByMatch` に渡して得られる証明の型を答えよ。
-/

/-!
## 6. ✏ 練習 — 章末問題 {#sec-Trial3.practice}

構成子を使って項を作ることと、`match` で使うことを組み合わせよう。
本体を書く前に、受け取る項と返す項の型を確認する。

1. 族 `B : A → Type` と依存関数 `f : (a : A) → B a` がある。
   各 `a` に組 `(a, f a)` を対応させる `graphOf` を、`FamilyPair` の構成子で定義せよ。

2. `leAddRight : ∀ n k : Nat, n ≤ n + k` を、`k` に関する再帰で証明せよ。
   零の場合は `Nat.le.refl`、次の数の場合は再帰呼び出しと `Nat.le.step` を使う。

3. 自然数 `n m` と、`h : n = m`、`hn : 0 ≤ n` を受け取り、`0 ≤ m` を返す
   `zeroLeOfEq` を定義せよ。`h` を `match` で使い、枝の中で要求される型を説明せよ。
-/
