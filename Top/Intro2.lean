import Intro1
import CH

/-!
# Lean 最小限の導入 II — Top のための道具

`Intro1.lean` と `CH.lean` を読み終えた人のためのファイルで、
`Top.lean`（位相空間）を読むのに必要な残りの道具を揃える:
class と instance、型の族としての `Fin`、記法の自作、集合 `Set` の構築、名前空間。

`CH.lean` を経由したので、ここからは**命題と証明も自由に使う**。
読み方は今までどおり——項を見たら型を推測し、表示の枠で答え合わせをする。
-/

/-! ## 1. class と instance

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

これで括弧が3種類そろった。`Intro1.lean` 6節の `( )`（明示）・`{ }`（暗黙）に
加えて、`[inst : C α]` が**インスタンス引数**である——他の引数との単一化だけでは
決まらず、エラボレータが `instance` として登録された項の中から探索して埋める。
-/

#check @inferInstance

/-!
    @inferInstance : {α : Sort u_1} → [i : α] → α

表示に、初めて見る記法が2つある。頭の `@` は「暗黙引数も省略せずに表示・指定する」
という印で、`@inferInstance` は `inferInstance` の省略なし版である。
`Sort u` は `Prop` と `Type` たちを束ねる書き方で、`Prop = Sort 0`、
`Type = Sort 1`、`Type 1 = Sort 2`、…と読む。つまりこの関数は
どの宇宙の型に対しても使える、ということである。
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

    error(lean.synthInstanceFailed): failed to synthesize instance of type class
      HasZero Bool

    Hint: Type class instance resolution failures can be inspected with the
    `set_option trace.Meta.synthInstance true` command.

（`error(…)` の丸括弧はエラーの分類名。`Hint:` は調査のヒントで、
以後の引用ではどちらも省略することがある。）
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
`Intro1.lean` 5節で作った `Point` にゼロを登録してみる。
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

/-! ### インスタンスを受け取る定理

インスタンス引数は `def` だけでなく `theorem` にも書ける。
「ゼロが登録されたどんな型でも成り立つ」一般的な定理が作れる:
-/

theorem zeroPair_fst (α : Type) [HasZero α] : (zeroPair α).fst = HasZero.zero := rfl

#check zeroPair_fst

/-!
    zeroPair_fst (α : Type) [HasZero α] : (zeroPair α).fst = HasZero.zero

使うときは `α` を指定するだけでよく、`HasZero α` の証明（項）は登録簿から
自動で供給される。
-/

-- 登録済みの型なら、どれにでも同じ定理が適用できる
example : (zeroPair Nat).fst = HasZero.zero := zeroPair_fst Nat
example : (zeroPair Point).fst = HasZero.zero := zeroPair_fst Point

/-! ### 記法もクラスで動いている

`Intro1.lean` 3節の「正確には」で、「`+` の正体は汎用の演算で、どの型の足し算かは
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

表示の `{ x := 1, y := 2 }` は `Point.mk 1 2` の**別表示**である
（フィールド名付きの structure リテラル。書くときにも使える）。
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
（2節の補足で、`(2 : Fin 3)` のようなリテラルが通る理由として再登場する）。

なお、この教材の `HasZero` は練習用の自作クラスで、記法とは独立している
（登録しても `0` と書けるようにはならない）。mathlib にはよく似た `Zero` という
クラスがあり、そちらは `OfNat` への橋渡しを備えているので、
登録すると `0` と書けるようになる。
-/

/-! ### ✏ 練習

1. 本文で `HasZero Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : HasZero Bool where zero := false` を登録し、
   `example : HasZero Bool := inferInstance` と `#check zeroPair Bool` が
   通るようになることを確かめよ。
2. 前問の instance を登録した状態で、
   `example : (zeroPair Bool).fst = HasZero.zero := zeroPair_fst Bool` が
   通ることを確かめよ（登録した瞬間から、一般的な定理も適用できる）。
3. `Add` にならって `instance : Mul Point where mul p q := ⟨p.x * q.x, p.y * q.y⟩`
   を登録し、`#eval (Point.mk 2 3 * Point.mk 4 5).x` の値を予想してから確かめよ。
-/

/-! ## 2. 型の族と Fin

`Intro1.lean` 6節の依存関数型が本領を発揮するのは、**型を返す関数**（型の族）と
組み合わせたときである。標準ライブラリの `Fin` は「`n` 未満の番号の型」を
返す関数である（この型の中身——値と証明の組——は `CH.lean` の6節で見た）。
-/

#check Fin

/-!
    Fin (n : Nat) : Type

binder 形式を読み替えれば `Fin : Nat → Type`——1つ渡すと型が返る。
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

`CH.lean` 6節の `last` と見比べてほしい。`first` の値は常に 0 番なので
証明なしで書けるが、`last` は値 `n` が型の上限すれすれに依存するぶん、
`n < n + 1` の証明を添える必要があった。

集合のアナロジーでは、依存関数型 `(a : α) → P a` は集合族 {P a} の
**直積** ∏ₐ P a に当たる。その項は「各 a に P a の要素を1つずつ選ぶ、選び方」
だからである。`α → β` ＝ B^A（すべての因子が同じ直積、すなわち冪）の、
因子が点ごとに変わってよい一般化になっている。
対になる**族の直和** ∐ₐ P a——「どの a か」の札付きで各 P a の要素を集めたもの——に
当たる**依存和** `(a : α) × P a` もあり、`Pair`（直積）と `MySum`（直和）の
共通の一般化である（`CH.lean` の6節で主役だったもの）。
-/

/-! ### 補足: では `2 : Fin 3` なのか？

「`Fin 3` は 3 未満の番号の型」と聞くと、集合 {0, 1, 2} ⊂ ℕ を思い浮かべて、
「自然数 `2` はそのまま `Fin 3` の項でもあるのか」と考えたくなる。そうではない。
`Intro1.lean` 1節で見たとおり**項はちょうど1つの型を持ち**、型どうしは集合のように重ならない
——集合のアナロジーの限界がここにある。`Fin 3` は `Nat` の部分集合ではなく、
`Nat` とは**別に作られた型**である（作りは `CH.lean` の6節で見た）。

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
（`Fin` 用の読み方が instance として登録されている——1節で見た仕組みである）。
`(2 : Nat)` は自然数の項（それ自体 `Nat.succ (Nat.succ Nat.zero)` の読み替え
——数字はもともと記法である）、`(2 : Fin 3)` は `Fin 3` の「2 番」の項で、
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

発展: リテラルの読みの正体は `OfNat` というクラスで、`(2 : Fin 3)` は
`OfNat.ofNat 2` の略記、`Fin n` 用の instance が「`n` で割った余り」として
実装されている。1節で見た「記法はクラスで動く」がここでも働いている。
-/

/-! ### ✏ 練習

1. `#check first 4` の表示と、`#eval (first 4).val` の値を予想してから確かめよ。
2. `#eval (5 : Fin 4)` の表示を予想してから確かめよ（本文の `(5 : Fin 3)` と
   同じ仕組みである）。
3. `#check first 0` の表示を予想してから確かめよ（`Fin (0 + 1)` は1点の型である）。
4. `#eval (first 5).val + (2 : Fin 3).val` の値を予想してから確かめよ。
-/

/-! ## 3. 記法の自作 — syntax と macro_rules

`Top.lean` は `⋃₀ S` や `{a | p a}` といった数学記法を自作している。仕組みは:

* `syntax` — 「この書き方を受け付けよ」と構文を追加する
* `macro_rules` — 「その書き方はこの項の略記である」と展開を与える

試しに、`Intro1.lean` 5節の `Pair` のための記法を作ってみる。
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
（次節と `Top.lean` で使用）。
-/

/-! ### ✏ 練習

1. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。
2. `infixl:65 " ⊞ " => add` で、`Intro1.lean` の `add`（`MyNat` の足し算）に
   中置記法を与え、`#reduce MyNat.zero.succ ⊞ MyNat.zero.succ` の表示を
   予想してから確かめよ。
-/

/-! ## 4. 集合 — `Set` を自作する

`Top.lean` は、数学でいう「集合」の上に位相を組み立てる。その集合を
ここで作ってしまおう。`CH.lean` で身につけた証明の書き方の、最初の実戦でもある。

`X` の部分集合を1つ指定することは、「各 `a : X` が入っているかどうか」を
決めること——つまり **`X` 上の述語を1つ与えること**と同じである。そこで:
-/

/-- `X` の部分集合の型。実体は述語 `X → Prop` そのもので、新しいデータは何もない。 -/
def Set (X : Type) : Type := X → Prop

#check Set

/-!
    Set (X : Type) : Type

2節の `Fin` と同じ、「型を受け取って型を返す関数」である。

述語 `p` を集合とみなすときの「宣言」も1つ用意する。定義上は恒等関数だが、
「述語を集合と読み替えました」という意思表示をこの名前が担う:
-/

def setOf {X : Type} (p : X → Prop) : Set X := p

#check setOf

/-!
    setOf {X : Type} (p : X → Prop) : Set X

数学の内包記法 `{a | p a}` も、3節の道具でそのまま自作できる:
-/

syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

/-!
所属の記号 `∈`（`\in` と打つ）は、標準ライブラリの記法用クラス `Membership` に
instance 登録すると使えるようになる——1節で見た「記法はクラスで動く」の実戦である。
中身は「集合（＝述語）`s` に点 `a` を適用する」だけ:
-/

instance {X : Type} : Membership X (Set X) := ⟨fun s a => s a⟩

#check (1 : Nat) ∈ ({n | n = 1} : Set Nat)

/-!
    1 ∈ setOf fun n ↦ n = 1 : Prop

型が `Prop` と付いた＝登録に成功している。読むときの注意を2つ。

第一に、**型注釈が2つ要る**理由: 数字 `1` も内包記法 `{n | …}` も
「期待される型に応じて読みが決まる」記法なので、どの型の話かを
先に教えないと読みが決まらないからである。

第二に、表示が `{n | n = 1}` に戻らず `setOf fun n ↦ n = 1` になる理由:
自作した記法は**構文解析（読む方向）専用**で、表示（書く方向）の規則までは
作っていないからである。以後の表示の枠でも、展開先がそのまま見える。

「`a ∈ s` である」ことの証明は、定義を展開すればただの `s a` である。
実際に確かめてみる:
-/

example : (1 : Nat) ∈ ({n | n = 1} : Set Nat) := rfl

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

theorem Set.subset_refl {X : Type} (s : Set X) : s ⊆ s := fun _ ha => ha

#check Set.subset_refl

/-!
    Set.subset_refl {X : Type} (s : Set X) : s ⊆ s

`s ⊆ s` を展開すれば `∀ a, a ∈ s → a ∈ s`——各点で「`p → p`」を示すだけ
（`CH.lean` 1節の世界そのもの）である。名前を `Set.〜` にしたのは
ドット記法（`Intro1.lean` 7節）のためで、この命名の仕組みは次節で説明する。

`Top.lean` はこの `Set` を土台に、`∩`・`∪`・補集合・像・逆像・集合族……と
道具を足していく。
-/

/-! ### ✏ 練習

1. 推移律を項で書け（各点で2つの仮定を順に適用する）:

       theorem Set.subset_trans {X : Type} {s t u : Set X}
           (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u

2. `def evens : Set Nat := {n | IsEven n}` と宣言せよ（`IsEven` は `CH.lean`
   9節の述語）。`example : (4 : Nat) ∈ evens := ⟨2, rfl⟩` が通ることを確かめよ。
3. 全体集合 `def allNat : Set Nat := {_n | True}` を定義し、
   `theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat` を書け
   （各点の証明は `True.intro`。束縛子 `_n` の `_` は「使わない」印である）。
4. `def odds : Set Nat := {n | ¬IsEven n}` を宣言し、
   `#check (3 : Nat) ∈ odds` の表示を予想してから確かめよ。
-/

/-! ## 5. namespace — 名前の接頭辞

`Intro1.lean` 7節のドット記法や、前節の `Set.subset_refl` という名前を
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

外からはフルネームで呼ぶ
-/

/-!
`p.x` が効くのは、`x` が**型名と同じ名前空間** `Point` に置かれているから
である。`Top.lean` では `namespace Set` の中に集合の関数（`Set.ext` など）を
置いていく——`s.ext` のようなドット記法が効くのはそのためである。
逆に、名前空間の**中**の名前を接頭辞なしで使えるようにする `export N (名前)`
という宣言もある（`Top.lean` が `TopologicalSpace.IsOpen` を
`IsOpen` と書くために使っている）。

これで `Top.lean` を読む準備が整った。

なお正確には、Lean の核には依存関数型と帰納型のほかに商型（`Quot`）などもあるが、
この教材では直接は使わない（ただし関数の外延性 `funext` が商型の上に
建っているため、`Top.lean` 末尾の公理の一覧には顔を出す）。
-/

/-! ### ✏ 練習

1. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
-/
