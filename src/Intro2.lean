import Intro1b
import CH2

/-!
# Lean 最小限の導入 II — Top のための道具

型の入門と証明編を2往復し、`CH2.lean` を読み終えた人のためのファイルで、
`Top.lean`（位相空間）を読むのに必要な残りの道具を揃える:
class と instance、記法の自作、集合 `Set` の構築、名前空間。

二つの証明編を経由したので、ここからは**命題と証明も自由に使う**。
読み方は今までどおり——項を見たら型を推測し、表示の枠で答え合わせをする。
-/

/-! ## 1. class と instance {#sec-Intro2.classes}

`class` は structure の変種である。宣言の形は structure と同じで、
[`Intro1b.lean` 2節](#sec-Intro1.structures)の `Pair (α β : Type)` のように
パラメータを取ることもできる。structure との違いは、**class の項は `instance` として
登録簿に載せておける**という1点にある。登録しておけば、必要になったところで
Lean が登録簿から探して使ってくれる。この登録と探索が、この節の主題である。

例として、点付き集合を class で書いてみる。
[`Intro1b.lean` 2節](#sec-Intro1.structures)の `PointedType` は、「型 `carrier` と、
その要素 `point`」を**1つの項に束ねて**持ち歩く structure だった。
今度は型をパラメータにして、「型 `α` の中の点」だけをフィールドにする:
-/

class Pointed (α : Type) : Type where
  point : α

#check Pointed

/-!
    Pointed (α : Type) : Type

`carrier` がフィールドからパラメータ `α` に移り、フィールドは点だけになった。
パラメータにする書き方そのものは structure でもできるので、ここは class の特徴ではない。
class にした意味は、次の `instance` 宣言にある。`Pointed Nat` の項を1つ登録簿に
載せておけば、「`Nat` の点」が必要な場所で、項を引数として手渡さなくても
Lean が見つけてくれる。

登録は `instance` 宣言で行う:
-/

instance : Pointed Nat where
  point := 0

/-!
`Pointed α` の項は「`α` のどの項を**基点**と呼ぶかの指定」で、
`instance` 宣言によって `Nat` の基点として `0` を登録した。

`instance` は**名前を付けない宣言**である（中身は `def` と同じで、
宣言と同時に登録簿へ載る）。使う側は登録簿から探すだけで名前で呼ばないから、
名前を書く必要がない。実際には Lean が `instPointedNat` のような名前を
自動で付けており、`instance myPoint : Pointed Nat where …` と
自分で名前を付けることもできる。

登録簿から探す操作そのものを項として書いたのが `inferInstance` である。
型を見ると、インスタンス引数 `[i : α]` を受け取ってそのまま返すだけの関数で、
「探す」仕事は括弧 `[ ]` の仕組みがやっていることが分かる。

これで括弧が3種類そろった。[`Intro1a.lean` 4節](#sec-Intro1.dependent-functions)の `( )`（明示）・`{ }`（暗黙）に
加えて、`[inst : C α]` が**インスタンス引数**である——他の引数との単一化だけでは
決まらず、エラボレータが `instance` として登録された項の中から探索して埋める。
-/

#check @inferInstance

/-!
    @inferInstance : {α : Sort u_1} → [i : α] → α

頭の `@` は「暗黙引数も省略せずに表示・指定する」
という印で、`@inferInstance` は `inferInstance` の省略なし版である。
`Sort u` は、[`CH1.lean` 1節](#sec-CH.propositions)で見た、`Prop` や `Type`、`Type 1` などを
まとめて扱う宇宙の表記である。つまりこの関数は、命題も通常の型も対象にできる。
-/

/-!
確かめてみる。次の `example` も名前を付けない宣言で、こちらは登録簿にも
載らない。「この型の項が確かに作れる」ことをその場で確かめるためだけに使う。
-/

example : Pointed Nat := inferInstance

/-!
登録してあるので、これは見つかって受理される（`example` は受理されると
Infoview には何も表示しない）。登録していない型では失敗する:

    example : Pointed Bool := inferInstance

    error(lean.synthInstanceFailed): failed to synthesize instance of type class
      Pointed Bool

    Hint: Type class instance resolution failures can be inspected with the
    `set_option trace.Meta.synthInstance true` command.

（`error(…)` の丸括弧はエラーの分類名。`Hint:` は調査のヒントで、
以後の引用ではどちらも省略することがある。）
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
[`Intro1b.lean` 2節](#sec-Intro1.structures)で作った `Point` に基点（原点）を登録してみる。
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

インスタンス引数は `def` だけでなく `theorem` にも書ける。
「基点が登録されたどんな型でも成り立つ」一般的な定理が作れる:
-/

theorem pointPair_fst (α : Type) [Pointed α] : (pointPair α).fst = Pointed.point := rfl

#check pointPair_fst

/-!
    pointPair_fst (α : Type) [Pointed α] : (pointPair α).fst = Pointed.point

使うときは `α` を指定するだけでよく、`Pointed α` の証明（項）は登録簿から
自動で供給される。
-/

-- 登録済みの型なら、どれにでも同じ定理が適用できる
example : (pointPair Nat).fst = Pointed.point := pointPair_fst Nat
example : (pointPair Point).fst = Pointed.point := pointPair_fst Point

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
登録簿から探す——と、機械が自動でつないでいく。`Extra.lean` の発展演習で
「積空間 `X × Y` に位相が自動で載る」のも、これと同じ仕組みである。
-/

/-! ### 記法もクラスで動いている

[`Intro1a.lean` 3節](#sec-Intro1.functions)の先取りで、`+` は `HAdd.hAdd` を使う記法であり、
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

/-! ### 補足（初読は飛ばしてよい）: `+` と数値リテラルの登録簿

正確に言うと、`+` の読み先は、左右の型が違ってもよいクラス `HAdd` の関数
`HAdd.hAdd` である。「`Add α` があれば `HAdd α α α` にもなる」という**橋渡しの
インスタンス**が標準ライブラリに用意されているので、`Add` を登録するだけで
記法まで使えるようになる。登録簿の検索は、このように**連鎖**する。

数字のリテラルにも同じ仕組みがある。数字 `2` は `OfNat.ofNat 2` の略記で、
クラス `OfNat` の instance が、期待される型ごとに読み方を決めている。
[`Intro1a.lean` 3節](#sec-Intro1.functions)で `2` が `Nat` とも `Int` とも読まれたのも、
[`CH2.lean` 6節](#sec-CH.dependent-sums)の補足で `(5 : Fin 3)` が 3 で割った余りの `2` と
読まれたのも、`Nat`・`Int`・`Fin n` それぞれの `OfNat` の instance がそう実装されているから
である。「記法はクラスで動く」という、この節の主題の一例である。

なお、この教材の `Pointed` は練習用の自作クラスである。標準ライブラリにも
同じ形のクラス `Inhabited`（フィールド名は `default`）があり、
「少なくとも1つ項を持つ型」の既定値として広く使われている。
-/

/-! ### ✏ 練習

本文で `Pointed` に対して行った操作を、**二項演算付きの型**（マグマと
呼ばれる）で一通り繰り返す。

1. 本文で `Pointed Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : Pointed Bool where point := false` を登録し、
   `example : Pointed Bool := inferInstance` と
   `example : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool` が
   通るようになることを確かめよ（登録した瞬間から、一般的な定理も適用できる）。
2. `Pointed` と同じ手順でマグマを自作する:
   `class Magma (α : Type) : Type where op : α → α → α` を宣言し、
   `instance : Magma Nat where op := Nat.add` を登録して、
   `example : Magma Nat := inferInstance` が通ることを確かめよ。
3. `pointPair` にならって、汎用関数
   `opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a` を書き、
   `#eval opSelf Nat 3` の値を予想してから確かめよ。
4. 本文の「積に構造を誘導する」にならって、成分ごとに演算する
   `instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β)` を登録し、
   `#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd` の値を
   予想してから確かめよ（探索の連鎖まで含めて、`Pointed` と同じに動く）。
5. `Add` にならって `instance : Mul Point where mul p q := ⟨p.x * q.x, p.y * q.y⟩`
   を登録し、`#eval (Point.mk 2 3 * Point.mk 4 5).x` の値を予想してから確かめよ。
-/

/-! ## 2. 記法の自作 — syntax と macro_rules {#sec-Intro2.notation}

`Top.lean` は `⋃₀ S` や `{a | p a}` といった数学記法を自作している。仕組みは:

* `syntax` — 「この書き方を受け付けよ」と構文を追加する
* `macro_rules` — 「その書き方はこの項の略記である」と展開を与える

試しに、[`Intro1b.lean` 2節](#sec-Intro1.structures)の `Pair` のための記法を作ってみる。
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
2. `infixl:65 " ⊞ " => add` で、`Intro1b.lean` の `add`（`MyNat` の足し算）に
   中置記法を与え、`#reduce MyNat.zero.succ ⊞ MyNat.zero.succ` の表示を
   予想してから確かめよ。
-/

/-! ## 3. 集合 — `Set` を自作する {#sec-Intro2.sets}

`Top.lean` は、数学でいう「集合」の上に位相を組み立てる。その集合を
ここで作ってしまおう。`CH1.lean`・`CH2.lean` で身につけた証明の書き方の、最初の実戦でもある。

`X` の部分集合を1つ指定することは、「各 `a : X` が入っているかどうか」を
決めること——つまり **`X` 上の述語を1つ与えること**と同じである。そこで:
-/

/-- `X` の部分集合の型。実体は述語 `X → Prop` そのもので、新しいデータは何もない。 -/
def Set (X : Type) : Type := X → Prop

#check Set

/-!
    Set (X : Type) : Type

[`Intro1a.lean` 3節](#sec-Intro1.functions)の `Map` と同じく、「型を受け取って型を返す関数」である。

述語 `p` を集合とみなすときの「宣言」も1つ用意する。定義上は恒等関数だが、
「述語を集合と読み替えました」という意思表示をこの名前が担う:
-/

def setOf {X : Type} (p : X → Prop) : Set X := p

#check setOf

/-!
    setOf {X : Type} (p : X → Prop) : Set X

数学の内包記法 `{a | p a}` も、[2節](#sec-Intro2.notation)の道具でそのまま自作できる:
-/

syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

/-!
所属の記号 `∈`（`\in` と打つ）は、標準ライブラリの記法用クラス `Membership` に
instance 登録すると使えるようになる——[1節](#sec-Intro2.classes)で見た「記法はクラスで動く」の実戦である。
中身は「集合（＝述語）`s` に点 `a` を適用する」だけ。
まずクラスそのものを見ておく:
-/

#check Membership

/-!
    Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)

`Membership α γ` は「入れ物 `γ` に要素 `α` が属する」という記法 `∈` のための
クラスである。次の登録は `γ := Set X`・`α := X` の場合に当たる。
-/

/-! ### 補足（初読は飛ばしてよい）: `Membership` の宇宙変数と `outParam`

表示は宇宙変数付きだが、この教材の範囲ではどれも `Type` と読んでよい
（[`Intro1a.lean` 1節](#sec-Intro1.terms-types)）。`outParam` は instance 探索へのヒントで、
「`∈` の右の入れ物の型 `γ` が分かれば、左の要素の型 `α` はそこから自動で
決まる」という指定である。
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
（[`CH1.lean` 2節](#sec-CH.implication)の世界そのもの）である。名前を `Set.〜` にしたのは
ドット記法（[`Intro1b.lean` 2節](#sec-Intro1.structures)で見た関数適用の略記）のためで、
この命名の仕組みは次節で説明する。

`Top.lean` はこの `Set` を土台に、`∩`・`∪`・補集合・像・逆像・集合族……と
道具を足していく。
-/

/-! ### ✏ 練習

1. 推移律を項で書け（各点で2つの仮定を順に適用する）:

       theorem Set.subset_trans {X : Type} {s t u : Set X}
           (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u

2. `def evens : Set Nat := {n | IsEven n}` と宣言せよ（`IsEven` は [`CH2.lean`
   4節](#sec-CH2.existence)の述語）。`example : (4 : Nat) ∈ evens := ⟨2, rfl⟩` が通ることを確かめよ。
3. 全体集合 `def allNat : Set Nat := {_n | True}` を定義し、
   `theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat` を書け
   （各点の証明は `True.intro`。束縛子 `_n` の `_` は「使わない」印である）。
4. `def odds : Set Nat := {n | ¬IsEven n}` を宣言し、
   `#check (3 : Nat) ∈ odds` の表示を予想してから確かめよ。
-/

/-! ## 4. namespace — 名前の接頭辞 {#sec-Intro2.namespaces}

[`Intro1b.lean` 2節](#sec-Intro1.structures)のドット記法や、前節の `Set.subset_refl` という名前を
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
-/

/-! ### 先取り（Top の公理監査）: 商型 `Quot`

Lean の核には依存関数型と帰納型のほかに商型（`Quot`）などもある。
本編では商型を直接は使わないが、関数の外延性 `funext` が商型の上に
建っているため、`Top.lean` 末尾の公理の一覧には顔を出す
（発展演習 `Extra.lean` では商型を直接使う）。
-/

/-! ### ✏ 練習

1. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
-/
