import «02_Forall»

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
後者の証明は否定を扱う第4章で見る。
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
### ✏ 練習

1. `Signal.red`、`Signal.yellow`、`Signal.green` をそれぞれ `0`、`1`、`2` に送る
   `signalCode : Signal → Nat` を定義せよ。各枝の型を確かめ、`signalCode Signal.yellow` の値を予想せよ。
-/

/-!
### 一点の型と空の型

標準の `Bool` も、構成子 `Bool.false` と `Bool.true` を持つ帰納型である。
構成子が一つで引数を取らない場合は、一点集合に対応する `Unit` になる。
構成子を一つも持たない場合は、空集合に対応する `Empty` になる。

    inductive Unit : Type where
      | unit : Unit

    inductive Empty : Type

空の型にも使い方はある。項を受け取ったとして、場合分けすべき構成子が一つもなければよい。
その場合分けを `nomatch` と書く。
-/
def emptyToNat (e : Empty) : Nat := nomatch e
/-!
これは `Empty` の項を作ったのではなく、`Empty → Nat` という関数を作ったのである。
-/

/-!
## 2. 直和と直積 {#sec-Trial3.sums-products}

構成子も関数なので、引数を受け取れる。
次は「自然数に札を付けたもの」と「真偽値に札を付けたもの」をまとめた型である。
構成子の名前 `inl`・`inr` は、それぞれ左側・右側から項を入れることを表す。
-/
inductive TaggedSum : Type where
  | inl (n : Nat) : TaggedSum
  | inr (b : Bool) : TaggedSum

#check TaggedSum.inl
/-!
    TaggedSum.inl (n : Nat) : TaggedSum

構成子 `TaggedSum.inl` は `Nat → TaggedSum` という関数である。
集合の言葉では、この型は自然数と真偽値の**直和（非交和）**に対応する。
-/

#check TaggedSum.inr
/-!
    TaggedSum.inr (b : Bool) : TaggedSum

同様に、`TaggedSum.inr` は `Bool → TaggedSum` という関数である。
この構成子そのものは関数であり、それに `true : Bool` を渡した `TaggedSum.inr true` は、
できあがった `TaggedSum` 型の項である。
`true` 自体は `Bool` 型なので、`TaggedSum` 型の項が必要な場所では `TaggedSum.inr true` と書く。
この例では、構成子の適用を省略しても自動で補われるわけではない。
-/

/-!
### 中身を受け取る場合分け

`match` の枝で `TaggedSum.inl n` と書くと、その構成子に渡された自然数に `n` と名前を付けられる。
返す項では、その名前を使ってよい。
-/
def valueOf : TaggedSum → Nat := fun x =>
  match x with
  | TaggedSum.inl n => n
  | TaggedSum.inr _ => 0

#eval valueOf (TaggedSum.inl 7)
/-!
    7

枝の `TaggedSum.inr _` にある `_` は、その位置にはどの値が来てもよく、その値に名前を付けないことを表す。
ここでは `true` と `false` のどちらも同じ枝で扱い、その値を使わずに `0` を返している。
直和からの写像は、左側と右側のそれぞれについて行き先を定めることで作れる。
-/

#eval valueOf (TaggedSum.inr true)
/-!
    0

まず `TaggedSum.inr true` という項を作り、それを `valueOf` に渡すので、括弧でまとめている。
括弧を外した `valueOf TaggedSum.inr true` は `(valueOf TaggedSum.inr) true` と読まれ、
`valueOf` に必要な `TaggedSum` 型の項の代わりに構成子そのものを渡すことになり、型が合わない。
-/

/-!
### 構成子が違う場合と、同じ場合

`TaggedSum.inl n` と `TaggedSum.inr b` が等しくないことも、
`TaggedSum.inl n = TaggedSum.inl m` から `n = m` が言えることも、Leanで証明できる。
後者を表す補題は、帰納型の宣言に伴って生成される。
-/
#check TaggedSum.inl.inj
/-!
    TaggedSum.inl.inj {n n✝ : Nat} : TaggedSum.inl n = TaggedSum.inl n✝ → n = n✝

第2章で見た単射性と同じく、像の等式の証明を受け取り、中身の等式の証明を返す関数である。
「構成子は単射」と仮定を付け足したのではなく、その証明を帰納型の仕組みから得ている。
`TaggedSum.inr` についても同様である。集合の言葉では、この二つの構成子は、
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
したがって、その型にも入力 `p` が現れる。
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
### ✏ 練習

1. `n : Nat` から、大きさが `n + 1` で番号が最後の `n` である組を返す
   `attachLast : Nat → Numbered` を定義せよ。第1章の `lastIndex n : Fin (n + 1)` を使ってよい。
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

/-!
### 自然数の不等式 Nat.le

自然数の `n ≤ m` は `Nat.le n m` の記法である。定義の中心は次の二つの構成子である。

    inductive Nat.le (n : Nat) : Nat → Prop where
      | refl : Nat.le n n
      | step {m} : Nat.le n m → Nat.le n (Nat.succ m)

`n` を固定すると、`Nat.le n` は右辺の自然数を添字に持つ命題の族になる。
`refl` は添字 `n` のところに証明を作り、`step` は添字 `m` の証明から添字 `m + 1` の証明を作る。

`Nat.succ m` は `m + 1` に当たる。
自然数を `zero` と `succ` で作ったのと同じように、不等式の証明を `refl` と `step` で作る。
-/

/-!
### 2 ≤ 4 の証明を作る

まず `2 ≤ 2` の証明を作り、`step` を二回使う。
-/
def two_le_two : 2 ≤ 2 := Nat.le.refl
def two_le_three : 2 ≤ 3 := Nat.le.step two_le_two
def two_le_four : 2 ≤ 4 := Nat.le.step two_le_three
/-!
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
`refl` の場合は同じ数どうしになり、`step` の場合は一つ前の証明に戻って考えられる。
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
### ✏ 練習

1. `1 ≤ 3` の証明を `Nat.le.refl` と `Nat.le.step` だけで作れ。
   次に、それを `succLeSuccByMatch` に渡して得られる証明の型を答えよ。
-/

/-!
## 6. ✏ 練習 — 章末問題 {#sec-Trial3.practice}

構成子を使って項を作ることと、`match` で使うことを組み合わせよう。
本体を書く前に、受け取る項と返す項の型を確認する。

1. `Signal.next` と逆向きに色を送る `prev : Signal → Signal` を書け。
   `prev (Signal.next Signal.red)` の値を確かめよ。

2. `swapSum : MySum A B → MySum B A` を定義せよ。
   左側から来た項は右側へ、右側から来た項は左側へ送ること。

3. 写像 `f : X → A` と `g : X → B` から、`x` を組 `(f x, g x)` に送る
   `pairMaps : X → MyPair A B` を定義せよ。型 `X A B` と写像 `f g` も引数に取ること。

4. 族 `B : A → Type` と依存関数 `f : (a : A) → B a` がある。
   各 `a` に組 `(a, f a)` を対応させる `graphOf` を、`FamilyPair` の構成子で定義せよ。

5. `MyNat.zero` を `0` に、`MyNat.succ k` を `toNat k + 1` に送る
   `toNat : MyNat → Nat` を再帰で定義せよ。

6. `leAddRight : ∀ n k : Nat, n ≤ n + k` を、`k` に関する再帰で証明せよ。
   零の場合は `Nat.le.refl`、次の数の場合は再帰呼び出しと `Nat.le.step` を使う。

7. 自然数 `n m` と、`h : n = m`、`hn : 0 ≤ n` を受け取り、`0 ≤ m` を返す
   `zeroLeOfEq` を定義せよ。`h` を `match` で使い、枝の中で要求される型を説明せよ。
-/
