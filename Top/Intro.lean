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
すべての項はちょうど1つの型を持つ。ここで重要なのは、**型もまた項である**こと。
`Nat` 自身も `Type` という型を持つ項であり、`Type` も `Type 1` を持つ項である。
-/

#check Nat       -- Nat : Type
#check Type      -- Type : Type 1
#check Type 1    -- Type 1 : Type 2
#check Prop      -- Prop : Type

/-!
`Type`, `Type 1, Type 2, …` の階層を宇宙（universe）と呼び、
`universe u` と宣言して任意の段 `Type u` を扱える。
`Prop` は命題たちの住む宇宙で、これは `CH.lean` の主題。

型が項と同じ資格を持つ、というこの一様性が Lean の設計の核で、
これがあるから「型を受け取る関数」「型を返す関数」が書ける（3節）。
-/

/-! ## 2. 関数

`def` で項に名前を付ける。関数もまた項であり、`fun x => e` という式で作る。
適用は括弧なしで `f a` と並べる。
-/

def double : Nat → Nat := fun n => n + n

#eval double 21   -- 42（`#eval` は項を計算する）

/-- 引数を左に書く糖衣構文。上の `double` と同じもの。 -/
def double' (n : Nat) : Nat := n + n

/-- 多引数の関数は「関数を返す関数」（カリー化）。
`Nat → Nat → Nat` は `Nat → (Nat → Nat)` と読む。 -/
def addMul (a b c : Nat) : Nat := a + b * c

#check addMul 1      -- addMul 1 : Nat → Nat → Nat（引数を1つだけ渡した残りも項）

/-! ## 3. 依存関数型

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
-- `⟨…⟩` は構成子に引数を渡す記法（4節）。`Fin` の項は「値」と「値 < n の証明」の組。

#check last 2     -- last 2 : Fin (2 + 1)
#check last 9     -- last 9 : Fin (9 + 1)

/-!
ふつうの関数型はこの特殊な場合にすぎない:
`α → β` は、行き先が入力に依存しない `(_ : α) → β` の略記である。

また、行き先が命題（`Prop` の項）のときの依存関数型が全称量化そのもので、
`∀ a, Q a` は `(a : α) → Q a` の別記法である（`CH.lean` の5節）。

`Top.lean` に出てくる「集合の族」 `U : I → Set X` や「型の族」 `P : α → Type` も、
すべてこの「型（や集合）を返す関数」の例である。
-/

/-! ## 4. 帰納型（inductive type）

もう1つの部品が帰納型。**構成子（constructor）のリスト**で型を定義する。
例として、自然数を自分で作ってみる。
-/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-!
この宣言の意味は「`MyNat` の項は、`zero` に `succ` を有限回適用したものが**すべて**であり、
それ以外にはない」ということ。作り方を列挙したら、それで型が決まる。

「それ以外にない」からこそ、場合分け（`match`）と再帰が正当化される。
これが帰納型の項の使い方（除去）である。
-/

def add : MyNat → MyNat → MyNat
  | m, .zero   => m
  | m, .succ n => .succ (add m n)   -- 構造が小さくなる方向への再帰

/-- `rfl` は「両辺が定義から計算して一致する」ことによる等式の証明。
1 + 1 = 2 が計算だけで確かめられる。 -/
example : add (.succ .zero) (.succ .zero) = .succ (.succ .zero) := rfl

/-!
標準ライブラリの型はほとんどすべて帰納型である。
`Nat`（リテラル `3` は `succ (succ (succ zero))` の表示）、`Bool`、`Fin`、
`CH.lean` に出てくる `×` `⊕` `Empty`、命題側の `And` `Or` `False` `Exists` `Eq` も全部そう。
`Eq` の構成子は `rfl` ただ1つで、上で使ったのはこれである。

`Top.lean` では、`Nat` の再帰で集合の有限個の共通部分 `interFin` を定義し、
その性質もまた再帰で証明している。**再帰で書いた証明が数学的帰納法**である。

### structure と class

構成子が1つだけの帰納型には `structure` という書き方が用意されている。
フィールド名がそのまま取り出し関数になる。
-/

structure Point where
  x : Nat
  y : Nat

#check Point.mk           -- 構成子。`⟨1, 2⟩` は `Point.mk 1 2` の略記
#check Point.x            -- 取り出し関数。`p.x` とも書ける

example : (Point.mk 1 2).x = 1 := rfl

/-!
`class` は structure に「登録された項（インスタンス）を Lean が自動で探して渡す」
仕組みを足したもの。`Top.lean` の `[TopologicalSpace X]` という角括弧の引数は
「`X` の位相を探して暗黙に渡してほしい」という意味である。
-/

/-! ## 5. 命題の証明とタクティク

命題は型であり、証明はその項である（詳しくは `CH.lean`）。
`theorem` は `def` と同じ宣言で、名前が違うだけ。

証明の書き方にはもう1つの流儀がある。`by` に続けて、
項を組み立てる**命令**（タクティク）の列を書く方法である。
同じ定理を2通りで書いてみる。
-/

theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩

theorem and_swap' (p q : Prop) : p ∧ q → q ∧ p := by
  intro h            -- `fun h =>` に対応
  exact ⟨h.2, h.1⟩   -- この項をそのまま置く

/-!
`intro` は `fun`、`exact` は項そのものに対応していて、
どちらの流儀でも**最終的に出来上がるのは同じ項**である。
`CH.lean` は対応を見るために項を直接書き、`Top.lean` は証明が長いのでタクティク主体。

`Top.lean` に出てくるタクティクの早見表:

* `intro h` — 仮定を1つ取り込む（`fun h =>`）
* `exact e` — 項 `e` でゴールを閉じる
* `refine ⟨?_, ?_⟩` — 項の穴 `?_` を残して置き、穴を続きのゴールにする
* `apply f` — 結論から逆向きに `f` を適用し、引数をゴールとして残す
* `constructor` — ゴールの型の構成子を適用する
* `cases h with …` — 帰納型の項 `h` を場合分けする（`match` に対応）
* `rw [heq]` — 等式 `heq` でゴールを書き換える
* `show t` — ゴールを定義上等しい形 `t` に読み替える
* `have h : t := e` — 補助的な項に名前を付けて続ける
* `by_cases h : p` — `p` が成り立つ場合と否定の場合に分ける（古典論理）
-/

/-! ## 6. その他、読むのに要る小物

* `variable {α : Type u}` — 以降の宣言に共通する引数をまとめて宣言しておく。
* `universe u` — 宇宙の段の名前を宣言する（1節）。
* `namespace Set … end Set` — 中の名前に接頭辞 `Set.` を付ける。
  `s.ext` のようなドット記法は「`s` の型の名前空間から関数を探す」略記。
* `syntax` / `macro_rules` — 新しい記法の定義。`Top.lean` は
  `⋃₀` や `{a | p a}` などの記法を自分で作っている。

これで `CH.lean` と `Top.lean` を読む準備は足りる。

なお正確には、Lean の核には依存関数型と帰納型のほかに商型（`Quot`）などもあるが、
この教材では使わない。
-/
