import Intro2

/-!
# 位相空間

mathlib を使わず、Lean 4 の標準ライブラリだけで位相空間を組み立てる。

最終目標は「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」。
そのために必要なものだけを、必要になった順に足していく。

数学でいう「集合」には、`Intro2.lean` で作った `Set` を使う
（このファイルはそれを import している）。

## この定理を信じるには何を信じればよいか

末尾の定理 `Homeomorph.ofContinuousBijective` を信じるのに必要なのは、次の3つだけである。

1. Lean の**カーネル**が正しいこと。エラボレータやタクティクがどれだけ複雑でも、
   最後に項を検査するのはカーネルの小さな規則集だけである（`CH.lean` の10節）
2. このファイルに書いた**定義**が、意図した数学的概念を写していること
3. 末尾の `#print axioms` に表示される3つの公理

証明そのものは信じる必要がない。途中の議論がどれだけ長く込み入っていても、
型検査を通った時点で検査は済んでいる。

機械が直接保証してくれるのは、「1 を信頼したうえで、書かれた証明が主張どおりの
型を持つ」ことと、「3 にどの公理が入っているかの列挙」である。
1 と 3 は信頼の**基盤**として明示的に引き受けるものであり、
2 は人間が読んで監査するしかない。定義が間違っていれば、
そこから証明した定理は意図と違うことを言っている。だからこのファイルでは、
すべての定義を1ファイルに収めて目視で監査できる分量に保ち
（mathlib を使わないのはこのためでもある）、主要な定義には
よく知る例・事実がそこから出ることを確かめる「定義の確認」を添えてある。

## 読み方: 主要な宣言のあとの `#check`

主要な名前付きの定義・定理の直後に `#check 名前` を置き、その表示を
`Intro1.lean` と同じ Infoview 風の枠で書き添えてある。
`Intro1.lean` 以来の読み方——表示を見る前に
「いま何がどんな型で手に入るはずか」を**予想**してから確かめる——を、
ここでも続けてほしい。

表示は `名前 (x : A) (y : B) : C` という「引数の列 : 結果の型」の形をとる。
これは関数型 `名前 : A → B → C` と**同じ型の別表示**である。
`def f (n : α) : β := …` と `def f : α → β := fun n => …` が同じ宣言の2通りの
書き方である（`Intro1.lean` 3節）のと対応して、表示もこの2つの形を行き来する。
括弧 `( )` `{ }` の違いは `Intro1.lean` 6節、`[ ]` は `Intro2.lean` 1節。

## 読み方: タクティク証明の記号

証明は `CH.lean` 12節のタクティクで書く。同節の早見表にない記号を挙げておく:

* `·` — 場合分けなどで生じた**サブゴールごと**の証明の区切り
* `t₁; t₂` — `t₁` を実行してから、続けて `t₂` を実行する
* `rw [h] at hmem` — ゴールではなく**仮定** `hmem` の側を書き換える
* `refine ⟨…, ?_, ?_⟩` — 項の形を先に与え、あとで埋める部分を `?_` の穴にする
* `cases i using Fin.cases` — どの場合分けのしかたを使うかを名指しする
* `h ▸ e` — 等式 `h` で `e` の型を書き換える（`rw` の項版）

初出の箇所にも、それぞれ短い説明を添えてある。

また、タクティクで書いた証明にはそれぞれ、**同じ命題の項スタイルの証明**を
対にして並べる（本文の証明の直後の `example`）。どちらの流儀でも
最終的に同じ型の項に行き着くこと（`CH.lean` 12節）の、実地の見比べである。
-/

/-! ## 1. 集合

集合 `Set`（実体は述語 `α → Prop`）と、内包記法 `{a | p a}`・所属 `∈`・
包含 `⊆` は `Intro2.lean` 4節で作った。ここではその上に、残りの道具——
`∩`・`∪`・`∅`・補集合・像・逆像・集合族・有限性・外延性——を積んでいく。
-/

-- ここから `end Set` までの宣言には接頭辞 `Set.` が付く（`Intro2.lean` 5節）
namespace Set

-- 共通の引数の前置き。以後の宣言が `α` を使うと、自動で引数に取り込まれる
variable {α : Type}

/-!
`∩` `∪` `∅` の記法も、`Intro2.lean` 4節の `∈`・`⊆` と同じやり方——
標準ライブラリの記法用クラスへの `instance` 登録——で使えるようにする。
`⟨…⟩` はクラスの構成子にフィールドの中身を渡す書き方である。
-/

/-- 共通部分 `s ∩ t`: 両方に属する点の全体（「かつ」）。 -/
instance : Inter (Set α) := ⟨fun s t => {a | a ∈ s ∧ a ∈ t}⟩

#check ({n | n = 1} : Set Nat) ∩ {n | n = 2}

/-!
    (setOf fun n ↦ n = 1) ∩ setOf fun n ↦ n = 2 : Set Nat

型は Set Nat（命題でなく集合）
-/

/-- 合併 `s ∪ t`: どちらかに属する点の全体（「または」）。 -/
instance : Union (Set α) := ⟨fun s t => {a | a ∈ s ∨ a ∈ t}⟩

#check ({n | n = 1} : Set Nat) ∪ {n | n = 2}

/-!
    (setOf fun n ↦ n = 1) ∪ setOf fun n ↦ n = 2 : Set Nat

型は Set Nat
-/

/-- 空集合 `∅`: どの点も属さない集合。中身は「つねに `False` を返す述語」。 -/
instance : EmptyCollection (Set α) := ⟨{_a | False}⟩

#check (∅ : Set Nat)

/-!
    ∅ : Set Nat
-/

/-!
`instance` は名前のない宣言だが、実際には Lean が自動で命名している。
上の3つは `Set.instInter` のような名前になる
（`set_option pp.explicit true` で項を表示すると中に見える）。
`instance memInst : Membership α (Set α) := …` と自分で名前を付けてもよい。
-/

/-- 全体集合。どの点も属する集合（つねに `True` を返す述語）。
束縛子を `_a` としたのは、述語の中で点を使わないから（`_` は「使わない」印）。 -/
def univ : Set α := {_a | True}

#check univ

/-!
    Set.univ {α : Type} : Set α

namespace の中で宣言したのでフルネームは `Set.univ`。
明示引数はなく、暗黙の `α` は使う場面の期待される型から決まる。
-/

-- 確認: `0 ∈ univ` は定義を展開すると命題 `True` そのもの。
-- `trivial : True` がちょうどその型を持つので、これで閉じる
example : (0 : Nat) ∈ (univ : Set Nat) := trivial

/-- 補集合 `sᶜ`: `s` に属さない点の全体。`∉` は `¬(a ∈ s)` の略記。 -/
def compl (s : Set α) : Set α := {a | a ∉ s}

#check compl

/-!
    Set.compl {α : Type} (s : Set α) : Set α

集合を受け取って集合を返す。`compl : Set α → Set α` と同じこと。
-/

/-- 後置記法 `sᶜ`。`max` は最も強い結合を表す（結合の強さは後でまとめて確認する）。 -/
postfix:max "ᶜ" => Set.compl

/-- 像。`f '' s` は `s` の点を `f` で送った先の全体。
「どこかの `a ∈ s` から来た」を `∃` で言う。 -/
def image {β : Type} (f : α → β) (s : Set α) : Set β := {b | ∃ a, a ∈ s ∧ f a = b}

#check image

/-!
    Set.image {α β : Type} (f : α → β) (s : Set α) : Set β

明示引数が2つ並ぶカリー化された関数。
`image : (α → β) → Set α → Set β` と読み替えられる。
-/

/-- 中置記法 `f '' s`。数字 `80` は結合の強さ。 -/
infixl:80 " '' " => Set.image

/-- 「集合の集まり」`S : Set (Set α)` に属する集合すべての合併。
位相の公理でいう「任意個の合併」を、添字を使わずにこれで表す。 -/
def sUnion (S : Set (Set α)) : Set α := {a | ∃ s, s ∈ S ∧ a ∈ s}

#check sUnion

/-!
    Set.sUnion {α : Type} (S : Set (Set α)) : Set α

引数の型が `Set (Set α)`＝「集合の集合」であることに注意。
-/

/-- 前置記法 `⋃₀ S`。 -/
prefix:110 "⋃₀ " => Set.sUnion

/-- 添字づけられた集合族 `U : I → Set α` の合併。族とは「添字を受け取って
集合を返す関数」である（`Intro2.lean` 2節の型の族の仲間）。`sUnion` が
「集合の集まり」を受け取るのに対し、こちらは添字でパラメータづけた族を受け取る。 -/
def iUnion {I : Type} (U : I → Set α) : Set α := {a | ∃ i, a ∈ U i}

#check iUnion

/-!
    Set.iUnion {α I : Type} (U : I → Set α) : Set α

暗黙引数が `α` と `I` の2つ。どちらも `U` の型から決まるので書かずに済む。
-/

/-- 添字を `J ⊆ I` に制限した合併。「部分族の合併」を表す。 -/
def biUnion {I : Type} (J : Set I) (U : I → Set α) : Set α := {a | ∃ i, i ∈ J ∧ a ∈ U i}

#check biUnion

/-!
    Set.biUnion {α I : Type} (J : Set I) (U : I → Set α) : Set α
-/

/-- 逆像。`f ⁻¹' s` は、`f` で送ると `s` に入る点の全体。 -/
def preimage {β : Type} (f : α → β) (s : Set β) : Set α := {a | f a ∈ s}

#check preimage

/-!
    Set.preimage {α β : Type} (f : α → β) (s : Set β) : Set α

`image` と見比べると `Set β → Set α` で、集合の移動が `f` と**逆向き**。
-/

/-- 中置記法 `f ⁻¹' s`。 -/
infixl:80 " ⁻¹' " => Set.preimage

-- 確認: 逆像も定義どおりに展開される。両辺は計算（関数適用の簡約）で一致するので `rfl`
example : (fun n : Nat => n + 1) ⁻¹' {m | m = 3} = {n | n + 1 = 3} := rfl

/-! ### 記法の結合の強さ

`postfix:max` や `infixl:80` の数字は結合の強さで、大きいほど強く結合する。
ここまでの記法と標準ライブラリの `∩`（70）・`∪`（65）の間には

    ᶜ (max)　>　'' と ⁻¹' (80)　>　∩ (70)　>　∪ (65)

の関係がある。次の等式は「左辺を規則どおりに読むと右辺になる」ことの確認で、
両辺が**同じ項**に構文解析されるからこそ `rfl` で通る。
-/

example (f : Nat → Nat) (s t : Set Nat) : f '' s ∩ t = (f '' s) ∩ t := rfl
example (s t : Set Nat) : s ∩ tᶜ = s ∩ (tᶜ) := rfl
example (s t u : Set Nat) : s ∩ t ∪ u = (s ∩ t) ∪ u := rfl

/-- 有限集合: ある `n` について、`Fin n` からの写像で `s` の点をすべて拾えること。

`Fin n` は `0, 1, …, n-1` のちょうど `n` 個からなる型なので、
「`Fin n` で番号づけられる」がそのまま「点が有限個しかない」を意味する。

`f` は `s` の外の点を拾ってもよい（`Fin n` と `s` の全単射までは要求しない）。
「高々 `n` 個」で十分であり、こうしておくと部分集合の有限性がただちに従う。

書き方を2つ: `∃ (n : Nat) (f : Fin n → α), P` は `∃ n, ∃ f, P` の略記、
`∀ a ∈ s, P a` は `∀ a, a ∈ s → P a` の略記である
（どちらも `#check` の表示では展開された形で見える）。 -/
def Finite (s : Set α) : Prop := ∃ (n : Nat) (f : Fin n → α), ∀ a ∈ s, ∃ i, f i = a

#check Finite

/-!
    Set.Finite {α : Type} (s : Set α) : Prop

結果が `Prop`。つまりこれは集合の**性質**（集合を受け取って命題を返す述語）。
-/

/-- 空集合は有限。`n = 0` とし、拾う関数には `Fin.elim0`（`Fin 0` は空の型なので、
そこからはどこへでも関数が作れる）を渡す。`⟨…, …, …⟩` は `∃` を示す形（`CH.lean` 6節）。 -/
theorem Finite.empty : (∅ : Set α).Finite :=
  ⟨0, Fin.elim0, fun _ ha => False.elim ha⟩

#check Finite.empty

/-!
    Set.Finite.empty {α : Type} : ∅.Finite

仮定なしの定理。`∅.Finite` はドット記法の表示で `Set.Finite ∅` のこと。
定理の #check は「証明済みの命題」を型として見せてくれる。
-/

/-!
### 外延性

属する要素が一致する集合は等しい——関数の外延性 `funext` と命題の外延性
`propext` から従う（集合を関数として定義したことの代金をここで払う）。
この場面に特殊化した型は

    funext  : (∀ a, s a = t a) → s = t
    propext : (a ∈ s ↔ a ∈ t) → (a ∈ s) = (a ∈ t)

で、下の証明項 `funext fun a => propext (h a)` は、この2つを型どおりに
組み合わせただけである。
以後、集合の等式を示すときは `apply Set.ext` で「要素ごとの同値」に還元する。
-/

/-- 外延性: 属する要素が一致する集合は等しい。 -/
theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

#check ext

/-!
    Set.ext {α : Type} {s t : Set α} (h : ∀ (a : α), a ∈ s ↔ a ∈ t) : s = t

定理の型は「仮定 → 結論」の関数型。仮定 `h` を渡すと結論 `s = t` の証明が返る。
`s t` が暗黙なのは、`h` の型に現れるので自動で決まるから。
-/

/-- 二重補集合。ここで初めて古典論理を使う:
`Classical.byContradiction : (¬p → False) → p` は背理法そのものである。 -/
theorem compl_compl (s : Set α) : sᶜᶜ = s :=
  ext fun _ => ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

#check compl_compl

/-!
    Set.compl_compl {α : Type} (s : Set α) : sᶜᶜ = s

どの集合 `s` にも適用できる等式。`∀ s, …` と書くのと `(s : Set α)` を
引数に取るのは同じこと（`CH.lean` 5節: ∀ は依存関数型の記法）。
-/

/-- 2つの合併は「2つだけからなる族」の合併に書き直せる。
`{u | u = s ∨ u = t}` は要素が `s` と `t` の2つ（だけ）の集合族。
位相の公理は族の合併の形で書くので、この橋渡しを補題に切り出しておく
（位相の節の `isOpen_union` で使う）。証明中の `h ▸ hau` は
「等式 `h` で `hau` の型を書き換える」記法。 -/
theorem union_eq_sUnion (s t : Set α) : s ∪ t = ⋃₀ {u | u = s ∨ u = t} := by
  apply ext
  intro a
  constructor
  · intro ha
    cases ha with
    | inl h => exact ⟨s, Or.inl rfl, h⟩
    | inr h => exact ⟨t, Or.inr rfl, h⟩
  · intro ha
    have ⟨u, hu, hau⟩ := ha
    cases hu with
    | inl h => exact Or.inl (h ▸ hau)
    | inr h => exact Or.inr (h ▸ hau)

-- 同じ命題を項で直接書くと、こうなる（タクティクと項の見比べ）:
example (s t : Set α) : s ∪ t = ⋃₀ {u | u = s ∨ u = t} :=
  ext fun _ =>
    ⟨fun ha =>
      match ha with
      | Or.inl h => ⟨s, Or.inl rfl, h⟩
      | Or.inr h => ⟨t, Or.inr rfl, h⟩,
     fun ⟨_, hu, hau⟩ =>
      match hu with
      | Or.inl h => Or.inl (h ▸ hau)
      | Or.inr h => Or.inr (h ▸ hau)⟩

#check union_eq_sUnion

/-!
    Set.union_eq_sUnion {α : Type} (s t : Set α) : s ∪ t = ⋃₀ setOf fun u ↦ u = s ∨ u = t

内包記法は表示では展開先の `setOf` の形で見える（前述）。
-/

/-! ### 有限個の共通部分

`Fin n` で番号づけられた集合たちの共通部分。`n` についての再帰で定義する。
ハウスドルフ側の証明で、有限部分被覆から近傍を1つ作るのに使う。
-/

/-- `n` 個の集合 `W 0, …, W (n-1)` の共通部分。
`Nat` の構造にそったパターンマッチ（`Intro1.lean` 4節）で定義する:
`0` 個なら `univ`、`n + 1` 個なら「先頭 `W 0`」と「残り `n` 個の共通部分」の `∩`。
`fun i => W i.succ` は添字を1つずらして「残りの族」を作っている。 -/
def interFin : (n : Nat) → (Fin n → Set α) → Set α := fun n W =>
  match n with
  | 0 => univ
  | n + 1 => W 0 ∩ interFin n fun i => W i.succ

#check interFin

/-!
    Set.interFin {α : Type} (n : Nat) : (Fin n → Set α) → Set α

表示に binder 形式（`(n : Nat)`）と矢印形式（`→`）が**混ざっている**が、
どちらも同じ関数型の表示にすぎない。全体としては
`interFin : (n : Nat) → (Fin n → Set α) → Set α` という2引数関数である。
-/

/-- すべての `W i` に入る点は共通部分に入る。
定義と同じ再帰の形で証明を書く——**再帰で書いた証明が数学的帰納法**である。
`n = 0` の場合のゴールは `a ∈ univ` すなわち `True` なので `trivial`。 -/
theorem mem_interFin : ∀ (n : Nat) (W : Fin n → Set α) (a : α), (∀ i, a ∈ W i) →
    a ∈ interFin n W := fun n W a h =>
  match n with
  | 0 => trivial
  | n + 1 => ⟨h 0, mem_interFin n (fun i => W i.succ) a fun i => h i.succ⟩

#check mem_interFin

/-!
    Set.mem_interFin {α : Type} (n : Nat) (W : Fin n → Set α) (a : α) : (∀ (i : Fin n), a ∈ W i) → a ∈ interFin n W

引数3つのあと、「仮定 → 結論」。長い表示は適当な位置で折り返されるが
意味は変わらない。
-/

/-- 共通部分に入る点は、すべての `W i` に入る（逆向き）。
`n = 0` では示すべき添字がそもそもない（`Fin 0` は空）ので `Fin.elim0`。
`n + 1` では添字 `i` を `Fin.cases` で「先頭か、後続か」に場合分けする
（`Fin.cases` は、場合分けを項として書くための標準ライブラリの関数）。 -/
theorem interFin_mem : ∀ (n : Nat) (W : Fin n → Set α) (a : α), a ∈ interFin n W →
    ∀ i, a ∈ W i := fun n W a h i =>
  match n with
  | 0 => Fin.elim0 i
  | n + 1 => Fin.cases h.1 (fun j => interFin_mem n (fun k => W k.succ) a h.2 j) i

#check interFin_mem

/-!
    Set.interFin_mem {α : Type} (n : Nat) (W : Fin n → Set α) (a : α) : a ∈ interFin n W → ∀ (i : Fin n), a ∈ W i

`mem_interFin` と仮定・結論が入れ替わっている。2つ合わせて同値。
-/

end Set

/-! ### ✏ 練習

1. `example : (2 : Nat) ∈ ({n | n < 5} : Set Nat)` を証明せよ。
   ヒント: `∈` と `setOf` を展開すればゴールは `2 < 5`、すなわち `3 ≤ 5`——
   `CH.lean` 8節の構成子 `Nat.le.step`・`Nat.le.refl` で書ける。
2. `#print axioms Set.compl_compl` の結果を予想してから確かめよ
   （背理法を使った証明だった）。
-/

/-! ## 2. 全単射

目標の「連続全単射」を述べるために要る。
`Function.Injective`（`∀ ⦃a b⦄, f a = f b → a = b`。括弧 `⦃ ⦄` は
暗黙引数 `{ }` の変種で、この教材では `∀ a b, f a = f b → a = b` と読んでよい）と
`Function.Surjective`（`∀ b, ∃ a, f a = b`）は標準ライブラリにあるので、
全単射だけを定義する。
-/

/-- 全単射: 単射かつ全射。

`Function.Injective f ∧ Function.Surjective f` と `∧` で束ねても内容は同じだが、
ここでは `structure` にする。利点はフィールドに**名前**が付くこと:
取り出しが `hbij.1` ではなく `hbij.injective` と書けて、読み手に意図が伝わる。
ほかにも、フィールドごとに説明（docstring）を付けられる、
フィールドが増えたり順序が変わったりしても使う側の記述が壊れにくい、
という利点がある。中身が命題だけなので `structure … : Prop` にできる。 -/
structure Function.Bijective {α β : Type} (f : α → β) : Prop where
  /-- 単射性: 送り先が同じなら元も同じ。 -/
  injective : Function.Injective f
  /-- 全射性: どの点にも、そこへ送られてくる元がある。 -/
  surjective : Function.Surjective f

#check Function.Bijective

/-!
    Function.Bijective {α β : Type} (f : α → β) : Prop

写像の性質（写像を受け取って命題を返す）。
-/

/-! ### ✏ 練習

1. 恒等写像が全単射であること
   `example : Function.Bijective (fun n : Nat => n)` を証明せよ
   （`injective` は仮定をそのまま返し、`surjective` は証人 `b` と `rfl`）。
-/

/-- `⋃ i, U i` で族全体の合併を表す（`syntax`・`macro_rules` の仕組みは
`Intro2.lean` 3節）。 -/
syntax:110 "⋃ " ident ", " term : term
/-- `⋃ i ∈ J, U i` で添字を `J` に制限した合併を表す。 -/
syntax:110 "⋃ " ident " ∈ " term:110 ", " term : term

macro_rules
  | `(⋃ $i, $U) => `(Set.iUnion fun $i => $U)
  | `(⋃ $i ∈ $J, $U) => `(Set.biUnion $J fun $i => $U)

/-!
注意: この `⋃` も `setOf` と同じく**読む方向だけ**の記法なので、`#check` の
表示では展開先の `Set.iUnion fun i ↦ …`／`J.biUnion fun i ↦ …` が見える。
同様に、`∀ a ∈ s, P` は `∀ (a : X), a ∈ s → P` に、`a ∉ K` は `¬a ∈ K` に
開かれて表示される。以後の表示の枠は、この**展開後の形**で書いてある。
-/

/-! ## 3. 位相空間

開集合が何であるかを指定するデータ `IsOpen` と、それが満たすべき3つの公理。
-/

/-- 位相空間の構造。「どの部分集合を開と呼ぶか」のデータ `IsOpen` と、
それが満たすべき3公理を `class` で束ねる（データ＋性質という構成は
`Intro1.lean` 5節の structure・`Intro2.lean` 1節の class と同じ）。

`class` にしたので、以後 `[TopologicalSpace X]` と角括弧で書くだけで
「`X` に載っている位相」がインスタンス引数として暗黙に渡る。

フィールドは `def` と同じく「引数をコロンの左に書く」形で宣言できる
（`Intro1.lean` 3節の binder 形式）。`∀` と `→` を並べて書いても同じ型である。 -/
class TopologicalSpace (X : Type) where
  /-- その集合が開集合であるという述語。 -/
  IsOpen (s : Set X) : Prop
  /-- 全体集合は開。 -/
  isOpen_univ : IsOpen Set.univ
  /-- 2つの開集合の共通部分は開。 -/
  isOpen_inter (s t : Set X) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t)
  /-- 開集合をいくつ集めて合併しても開。 -/
  isOpen_sUnion (S : Set (Set X)) (h : ∀ s ∈ S, IsOpen s) : IsOpen (⋃₀ S)

#check TopologicalSpace

/-!
    TopologicalSpace (X : Type) : Type

クラスも「型を受け取って型を返す関数」。`TopologicalSpace X` は
「`X` 上の位相全体の型」で、その項1つが位相1つに当たる。

なお、主フィールドの型 `Set X → Prop` は `Set (Set X)` と同じもの——
つまり `IsOpen` は「部分集合の集まり」P(P(X)) の元である。
「開集合系を指定する」という日常の言い方が、そのまま型に写っている。
-/

-- `export` で `TopologicalSpace.IsOpen` などを接頭辞なしの `IsOpen` で書けるようにする
export TopologicalSpace (IsOpen isOpen_univ isOpen_inter isOpen_sUnion)

-- 以後 `X` は位相空間: 位相はインスタンス引数として各宣言に暗黙に付く
variable {X : Type} [TopologicalSpace X]

/-- 空集合が開であることは公理に含めなくてよい。
空な集合族の合併が空集合だから、`isOpen_sUnion` から従う。

証明は `by` のタクティク（`CH.lean` 12節）。まず `⋃₀ ∅ = ∅` を `Set.ext` で示し、
`rw [← h]` で等式 `h` を右辺から左辺の向きに使ってゴールを書き換える。 -/
theorem isOpen_empty : IsOpen (∅ : Set X) := by
  have h : (⋃₀ (∅ : Set (Set X))) = (∅ : Set X) := by
    apply Set.ext
    intro a
    constructor
    · intro ⟨_, hs, _⟩
      exact False.elim hs
    · intro ha
      exact False.elim ha
  rw [← h]
  exact isOpen_sUnion _ fun _ hs => False.elim hs

#check isOpen_empty

/-!
    isOpen_empty {X : Type} [TopologicalSpace X] : IsOpen ∅

`[TopologicalSpace X]` がインスタンス引数として表示に現れる。
結論の `IsOpen ∅` がどの位相の話かは、この引数が決めている。
-/

/-!
同じ証明を項で直接書くと、次のようになる。`have h : … := …;` の並びが
タクティクの `have` に、`h ▸ e` が `rw [← h]; exact e` に対応する
（`▸` は等式 `h` で `e` の型を書き換える演算子。`CH.lean` 9節）。
-/

example : IsOpen (∅ : Set X) :=
  have h : (⋃₀ (∅ : Set (Set X))) = (∅ : Set X) :=
    Set.ext fun _ => ⟨fun ⟨_, hs, _⟩ => False.elim hs, fun ha => False.elim ha⟩
  h ▸ isOpen_sUnion _ fun _ hs => False.elim hs


/-- 2つの開集合の合併も開。公理は「集合族の合併」の形なので、
まず補題 `Set.union_eq_sUnion` で合併を族の合併に書き換えてから公理を適用する。
族の各要素は `s` か `t` のどちらかなので、場合分けしてそれぞれの開性を使う。 -/
theorem isOpen_union {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  rw [Set.union_eq_sUnion]
  refine isOpen_sUnion _ fun u hu => ?_
  cases hu with
  | inl h =>
    rw [h]
    exact hs
  | inr h =>
    rw [h]
    exact ht

#check isOpen_union

/-!
    isOpen_union {X : Type} [TopologicalSpace X] {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t)

明示引数は証明2つだけ。`s t` は `hs ht` の型から決まるので暗黙。
-/

-- こちらも項で。`match` の場合分けが `cases` に当たる
example {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) :=
  (Set.union_eq_sUnion s t) ▸ isOpen_sUnion _ fun _u hu =>
    match hu with
    | Or.inl h => h ▸ hs
    | Or.inr h => h ▸ ht


/-- 有限個の開集合の共通部分は開。`n` についての再帰で、公理の「2つの共通部分」を繰り返す。

無限個の共通部分では成り立たないことに注意（例えば実数直線で
`⋂ n, (-1/n, 1/n) = {0}` は開でない）。有限性がここで効く。 -/
theorem isOpen_interFin : ∀ (n : Nat) (W : Fin n → Set X), (∀ i, IsOpen (W i)) →
    IsOpen (Set.interFin n W) := fun n W h =>
  match n with
  | 0 => isOpen_univ
  | n + 1 => isOpen_inter _ _ (h 0) (isOpen_interFin n (fun i => W i.succ) fun i => h i.succ)

#check isOpen_interFin

/-!
    isOpen_interFin {X : Type} [TopologicalSpace X] (n : Nat) (W : Fin n → Set X) :
      (∀ (i : Fin n), IsOpen (W i)) → IsOpen (Set.interFin n W)
-/

/-- 閉集合: 補集合が開。原始概念は開集合だけなので、閉はこれで定義するほかない。 -/
def IsClosed (s : Set X) : Prop := IsOpen sᶜ

#check IsClosed

/-!
    IsClosed {X : Type} [TopologicalSpace X] (s : Set X) : Prop

`IsOpen` と同じ形の、集合の性質。
-/

/-! ### 定義の確認

型検査が見ているのは「`IsOpen` が3公理を満たす」ことだけで、
`TopologicalSpace` という定義が数学の位相空間の定義を写しているかどうかは
機械では確かめられない（冒頭の 2）。その代わりに、
よく知る例が定義を満たすことを見ておく。
-/

/-- 離散位相: すべての部分集合が開。どんな型にも入る、いちばん簡単な位相。
`where` 構文でクラスの各フィールドを埋めて、`TopologicalSpace X` の項を作る。
公理側はすべて `True` の証明なので `trivial` で済む。
頭の `@[reducible]` は**属性**（宣言に付ける印）で、「この定義は必要に応じて
いつでも展開してよい」という指定。`Extra.lean` の instance 探索で効いてくるだけ
なので、ここでは気にしなくてよい。 -/
@[reducible] def discrete (X : Type) : TopologicalSpace X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ _ _ => trivial
  isOpen_sUnion := fun _ _ => trivial

#check discrete

/-!
    discrete (X : Type) : TopologicalSpace X

型を受け取って**位相そのもの**（`TopologicalSpace X` の項）を返す関数。
-/

/-! ### ✏ 練習

1. `example : (discrete Nat).IsOpen {n | n = 0}` を証明せよ
   （離散位相では、どの部分集合の開性も `True`——証明は `trivial`）。
-/

/-! ## 4. 連続写像

位相空間の間の写像が連続であることを、開集合だけを使って定義する。
写像の向きと逆に、行き先の開集合を引き戻して考えるのがポイント。
-/

variable {Y : Type} [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z]

/-- 連続写像: 開集合の逆像がつねに開。 -/
def Continuous (f : X → Y) : Prop := ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

#check Continuous

/-!
    Continuous {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] (f : X → Y) : Prop

両側の空間それぞれにインスタンス引数が付く。「`f` が連続」という命題は、
実は「どの位相に関してか」を2つ暗黙に抱えている。
-/

/-! ### 定義の確認

連続の定義についても、よく知る事実がここから出ることを見ておく。
どちらも証明は1行で、逆像が定義上ぴったり重なることを使うだけ。
-/

/-- 恒等写像は連続。示すべきは `IsOpen ((fun x => x) ⁻¹' s)` だが、
`(fun x => x) ⁻¹' s` は定義を展開すると `s` そのもの。
だから仮定 `hs : IsOpen s` が、そのまま型の合う項になる。 -/
theorem continuous_id : Continuous (fun x : X => x) :=
  fun _ hs => hs

#check continuous_id

/-!
    continuous_id {X : Type} [TopologicalSpace X] : Continuous fun x ↦ x

仮定なしの定理。結論の中の `fun x ↦ x` が恒等写像。
-/

/-- 連続写像の合成は連続。
`(g ∘ f) ⁻¹' s` が `f ⁻¹' (g ⁻¹' s)` と定義上等しいので、引き戻しを2回続けるだけ。
名前を `Continuous.comp` としたので、`hg.comp hf` とドット記法で使える（`Intro1.lean` 7節）。 -/
theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) :=
  fun s hs => hf _ (hg s hs)

#check Continuous.comp

/-!
    Continuous.comp {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z]
      {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) : Continuous fun x ↦ g (f x)

空間3つぶんのインスタンス引数が並ぶ。明示引数は証明 `hg` `hf` の2つで、
先に適用される `f` の連続性が**後ろ**に来る（合成の記法 `g ∘ f` と同じ順）。
-/

/-! ### ✏ 練習

1. `#check @Continuous` の表示を予想してから確かめよ
   （2つの空間の位相が、どの種類の括弧で並ぶか）。
-/

/-! ## 5. ハウスドルフ空間

「異なる2点は開集合で見分けられる」という条件。
-/

/-- ハウスドルフ空間であるという**性質**。フィールドが命題1つだけの `class : Prop` で、
データは持たない。位相を前提にするので `[TopologicalSpace X]` を引数に取る。

空間ごとに決まる常置的な性質なので `class` にしてある: 以後の定理は
`[Hausdorff Y]` と書くだけで、その証明が登録簿から自動で供給される。 -/
class Hausdorff (X : Type) [TopologicalSpace X] : Prop where
  /-- 異なる2点は、交わらない開集合で分離できる。 -/
  separate : ∀ x y : X, x ≠ y →
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

#check Hausdorff

/-!
    Hausdorff (X : Type) [TopologicalSpace X] : Prop

`TopologicalSpace X : Type`（データ）と違い、こちらは結果が `Prop`（性質）。
-/

/-! ## 6. コンパクト

「どんな開被覆にも有限部分被覆がある」という条件。

被覆は添字づけられた族 `U : I → Set X` で表し、
部分被覆は添字の部分集合 `J ⊆ I` を取ることで表す。
`J` が有限であることは `Set.Finite`（`Fin n` で番号づけられること）で表す。
-/

/-- コンパクト集合。定義を読み下すと:
任意の添字型 `I`（暗黙引数）と開集合族 `U : I → Set X` について、
`U` が `K` を覆うなら、**添字の有限部分集合** `J` に間引いても `K` を覆える。

`Hausdorff` と違って、こちらは `class` にしない。`IsCompact` は個々の
部分集合ごとの述語で、`hK : IsCompact K` というふつうの仮定として渡したり、
補題の**結論**として新しく作ったりする対象だからである
（集合ごとに登録簿へ載せる運用はできない）。
空間全体の性質である `CompactSpace`（下）は `Hausdorff` と同様 `class` にする。 -/
def IsCompact (K : Set X) : Prop :=
  ∀ {I : Type} (U : I → Set X), (∀ i, IsOpen (U i)) → K ⊆ (⋃ i, U i) →
    ∃ J : Set I, J.Finite ∧ K ⊆ (⋃ i ∈ J, U i)

#check IsCompact

/-!
    IsCompact {X : Type} [TopologicalSpace X] (K : Set X) : Prop

表示は短いが、定義の中身は上のとおり `∀` が3つ重なった命題である。
-/

/-- 空間そのものがコンパクトであること: 全体集合 `univ` がコンパクト集合である。
`Hausdorff` と同じく、命題1つだけの `class : Prop`。 -/
class CompactSpace (X : Type) [TopologicalSpace X] : Prop where
  isCompact_univ : IsCompact (Set.univ : Set X)

#check CompactSpace

/-!
    CompactSpace (X : Type) [TopologicalSpace X] : Prop
-/

/-! ## 7. 補題1: コンパクト集合の連続像はコンパクト

方針: 与えられた `f '' K` の開被覆 `U` に対して

1. 被覆を `f` で引き戻して `K` の開被覆 `f ⁻¹' U i` を作る（`Set.subset_preimage_iUnion`）
2. `K` のコンパクト性で、有限部分被覆の添字 `J` を取る
3. 同じ `J` が `f '' K` の有限部分被覆を与える（`Set.image_subset_biUnion`）

1 と 3 は位相と無関係な、像と逆像についての一般的な補題である。
有限性は受け取った `J` をそのまま使い回すだけなので、`Fin n` を開ける必要はない。

なお mathlib では、細かい補題を `theorem` の同義語 `lemma` で宣言する慣例が
あるが、`lemma` は core Lean にはない（mathlib がマクロで定義している）。
この教材では一貫して `theorem` を使う。
-/

/-- 像が族で覆われるなら、元の集合は逆像の族で覆われる（方針の 1）。
位相と無関係な補題なので、節の変数 `X Y`（位相つき）ではなく
新しい型変数 `α β` で述べる。 -/
theorem Set.subset_preimage_iUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i := by
  intro x hx
  have ⟨i, hi⟩ := h (f x) ⟨x, hx, rfl⟩
  exact ⟨i, hi⟩

#check Set.subset_preimage_iUnion

/-!
    Set.subset_preimage_iUnion {α β : Type} {f : α → β} {K : Set α} {I : Type} {U : I → Set β}
      (h : f '' K ⊆ Set.iUnion fun i ↦ U i) : K ⊆ Set.iUnion fun i ↦ f ⁻¹' U i

位相のインスタンス引数が付いていない＝純粋に集合の補題である。
-/

-- 項で書くと1行になる。`x ∈ ⋃ i, f ⁻¹' U i` と `f x ∈ ⋃ i, U i` は定義を
-- 展開すると同じ命題なので、`h` を適用した結果がそのまま答えになる
example {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i :=
  fun x hx => h (f x) ⟨x, hx, rfl⟩

/-- 逆像の部分族で覆われるなら、像は同じ添字の部分族で覆われる（方針の 3）。
証明中の `have ⟨x, hx, hfx⟩ := …` は `∃`（依存和）の分解（`CH.lean` 6節）。 -/
theorem Set.image_subset_biUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i := by
  intro b hb
  have ⟨x, hx, hfx⟩ := hb
  have ⟨i, hiJ, hxi⟩ := h x hx
  exact ⟨i, hiJ, hfx ▸ hxi⟩

#check Set.image_subset_biUnion

/-!
    Set.image_subset_biUnion {α β : Type} {f : α → β} {K : Set α} {I : Type} {J : Set I} {U : I → Set β}
      (h : K ⊆ J.biUnion fun i ↦ f ⁻¹' U i) : f '' K ⊆ J.biUnion fun i ↦ U i
-/

-- 項で。タクティク版の `have ⟨…⟩ :=` による分解が `match` に当たる
example {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i :=
  fun _b hb =>
    match hb with
    | ⟨x, hx, hfx⟩ =>
      match h x hx with
      | ⟨i, hiJ, hxi⟩ => ⟨i, hiJ, hfx ▸ hxi⟩

/-- 補題1: コンパクト集合の連続像はコンパクト。方針の3歩をそのまま並べる。
下の `#check` を見る前に、この主張が「引数の列 : 結果」としてどう並ぶかを
予想してみてほしい。
名前が `IsCompact.image` なので、`hK : IsCompact K` に対し `hK.image hf` と書ける。 -/
theorem IsCompact.image {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) := by
  intro I U hU hcov
  have ⟨J, hJ, hsub⟩ := hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
      (Set.subset_preimage_iUnion hcov)
  exact ⟨J, hJ, Set.image_subset_biUnion hsub⟩

#check IsCompact.image

/-!
    IsCompact.image {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] {K : Set X} (hK : IsCompact K)
      {f : X → Y} (hf : Continuous f) : IsCompact (f '' K)

数学の主張「K コンパクト、f 連続 ⇒ f(K) コンパクト」が、
そのまま「証明を2つ受け取って証明を返す関数」の型になっている。
-/

-- 項で。`intro` が `fun` に、`have` の分解が `match` に、`exact` が組の構成に対応する
example {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) :=
  fun U hU hcov =>
    match hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
        (Set.subset_preimage_iUnion hcov) with
    | ⟨J, hJ, hsub⟩ => ⟨J, hJ, Set.image_subset_biUnion hsub⟩

/-! ### ✏ 練習

1. `#print axioms Set.subset_preimage_iUnion` の結果を予想してから確かめよ
   （包含の付け替えだけの証明に、公理は要るだろうか）。
-/

/-! ## 8. 補題2: ハウスドルフ空間のコンパクト集合は閉

ここが証明の山場で、有限性を実際に使うのもここだけ。方針:

1. 「各点が開近傍ごと入っている集合は開」という一般論を用意する（`isOpen_of_nhds`）
2. `K` の外の点 `y` に、`K` と交わらない開近傍 `W` を作る
   （`IsCompact.exists_disjoint_nhds`）
3. 1 に 2 を渡せば `Kᶜ` が開、すなわち `K` は閉

2 の中身: `K` の各点 `x` は `y` とハウスドルフ性で分離できる。分離する開集合の組を
点ごとに**1つ選ぶ**のではなく、「`y` を分離する開集合の組」の**全体**を添字型にして
`K` を覆う。必要なデータ（`y` 側の開集合と分離性の証明）が添字自身に
抱き合わされているので、選択公理を使わずに済む。この「分離データの束」を
まず名前付きの structure として定義してから、補題に進む。コンパクト性で組を有限個に間引き、
その `V` 側の有限交叉（`interFin`）を `W` とする。
無限個の共通部分では開とは限らないので、有限に減らせたことが本質的に効いている。
-/

/-- 各点が開近傍ごと入っている集合は開（方針の 1）。
`s` は「`s` に含まれる開集合すべて」の合併に等しくなるので、合併の公理が使える。 -/
theorem isOpen_of_nhds {s : Set X} (h : ∀ a ∈ s, ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) :
    IsOpen s := by
  have heq : s = ⋃₀ {W | IsOpen W ∧ W ⊆ s} := by
    apply Set.ext
    intro a
    constructor
    · intro ha
      have ⟨W, hW, haW, hWs⟩ := h a ha
      exact ⟨W, ⟨hW, hWs⟩, haW⟩
    · intro ⟨W, hW, haW⟩
      exact hW.2 a haW
  rw [heq]
  exact isOpen_sUnion _ fun _ hW => hW.1

#check isOpen_of_nhds

/-!
    isOpen_of_nhds {X : Type} [TopologicalSpace X] {s : Set X} (h : ∀ (a : X), a ∈ s → ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) :
      IsOpen s
-/

-- 項で。`rw [heq]` が `heq ▸` に当たる
example {s : Set X} (h : ∀ a ∈ s, ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) :
    IsOpen s :=
  have heq : s = ⋃₀ {W | IsOpen W ∧ W ⊆ s} :=
    Set.ext fun a =>
      ⟨fun ha =>
        match h a ha with
        | ⟨W, hW, haW, hWs⟩ => ⟨W, ⟨hW, hWs⟩, haW⟩,
       fun ⟨_, hW, haW⟩ => hW.2 a haW⟩
  heq ▸ isOpen_sUnion _ fun _ hW => hW.1

/-- 「点 `y` を分離する開集合の組」を名前付きで束ねた structure（`Function.Bijective`
と同じ理由で、`∧` のネストではなくフィールド名を選ぶ）。`left` は `K` を覆う側
として使い、`right` は `y` を含み、2つは交わらない。フィールドの型が前の
フィールドに依存している（`Intro1.lean` 5節）ことにも注意。

`K` はどこにも現れない: この structure は「点 `y` を分離する開集合の組」
だけを束ねたもので、`K` との関係（`left` たちが `K` を覆うこと）は
使う側の補題で述べる。定義は必要最小限の材料だけを持つのがよい。 -/
structure SeparatingPair (y : Y) where
  /-- 分離の `K` 側の開集合。 -/
  left : Set Y
  /-- 分離の `y` 側の開集合。 -/
  right : Set Y
  isOpen_left : IsOpen left
  isOpen_right : IsOpen right
  mem_right : y ∈ right
  disjoint : left ∩ right = ∅

#check SeparatingPair

/-!
    SeparatingPair {Y : Type} [TopologicalSpace Y] (y : Y) : Type

点ごとに「分離データ」の型が決まる。項は6つのフィールド
（開集合2つ＋証明4つ）の束で、`s.left` や `s.disjoint` で取り出す。
-/

/-- コンパクト集合 `K` の外の点は、`K` と交わらない開近傍を持つ（方針の 2）。

被覆の**添字型**として、いま定義した `SeparatingPair y` をそのまま使う。
つまり添字は「開集合の組」と「それが `y` を分離しているという証明」の
抱き合わせであり、被覆の各成分が自分の `right` と分離性を持参してくる。
被覆であること自体は、型注釈つきの `hcov` として先に切り出す——型を書いておけば
そこから読める、という本教材の方法の実演である（`⋃` 記法は束縛子に型注釈を
付けられないので、ここは展開先の `Set.iUnion` を直接書く）。 -/
theorem IsCompact.exists_disjoint_nhds [Hausdorff Y] {K : Set Y} (hK : IsCompact K)
    {y : Y} (hy : y ∉ K) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K := by
  -- `K` のどの点 `x` も `y` と分離できる。分離データ自身を添字と思えば `K` は覆われる
  have hcov : K ⊆ Set.iUnion fun i : SeparatingPair y => i.left := fun x hx => by
    have hne : x ≠ y := fun h => hy (h ▸ hx)
    have ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := Hausdorff.separate x y hne
    exact ⟨⟨U, V, hU, hV, hyV, hUV⟩, hxU⟩
  -- コンパクト性で有限個に間引く（最初のラムダの束縛子に添字型を書いて伝える）
  have ⟨J, hJ, hsub⟩ := hK (fun i : SeparatingPair y => i.left) (fun i => i.isOpen_left) hcov
  -- `J` は有限なので `Fin n` で番号づけ、対応する `right` 側の有限交叉を `W` とする
  have ⟨n, g, hg⟩ := hJ
  refine ⟨Set.interFin n fun k => (g k).right, ?_, ?_, ?_⟩
  · -- 有限個の開集合の共通部分は開
    exact isOpen_interFin n _ fun k => (g k).isOpen_right
  · -- `y` はどの `right` にも入っている
    exact Set.mem_interFin n _ y fun k => (g k).mem_right
  · -- `W` が `K` と交わったとすると、ある組の `left` と `right` の両方に入る点ができて矛盾
    intro a ha haK
    have ⟨i, hiJ, hai⟩ := hsub a haK
    have ⟨k, hk⟩ := hg i hiJ
    have hav : a ∈ (g k).right := Set.interFin_mem n _ a ha k
    have hau : a ∈ (g k).left := by rw [hk]; exact hai
    have hmem : a ∈ (g k).left ∩ (g k).right := ⟨hau, hav⟩
    rw [(g k).disjoint] at hmem
    exact hmem

#check IsCompact.exists_disjoint_nhds

/-!
    IsCompact.exists_disjoint_nhds {Y : Type} [TopologicalSpace Y] [Hausdorff Y] {K : Set Y} (hK : IsCompact K) {y : Y}
      (hy : ¬y ∈ K) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ (a : Y), a ∈ W → ¬a ∈ K
-/

-- 確認: この補題は選択公理どころか `Classical.choice` にも依存していない
-- （`propext` のみ）。データを添字に抱き合わせた効果がここに現れている。
#print axioms IsCompact.exists_disjoint_nhds

/-!
    'IsCompact.exists_disjoint_nhds' depends on axioms: [propext]
-/

-- 山場の補題も項で書ける。`by` の各行がどの項に写るか、対照しながら読んでほしい
-- （`refine ⟨_, ?_, ?_, ?_⟩` は `⟨…, …, …, …⟩` の直接の構成に、
-- 最後の矛盾は `disjoint ▸` による「`a ∈ ∅` すなわち `False`」への書き換えになる）
example [Hausdorff Y] {K : Set Y} (hK : IsCompact K)
    {y : Y} (hy : y ∉ K) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K :=
  have hcov : K ⊆ Set.iUnion fun i : SeparatingPair y => i.left := fun x hx =>
    have hne : x ≠ y := fun h => hy (h ▸ hx)
    match Hausdorff.separate x y hne with
    | ⟨U, V, hU, hV, hxU, hyV, hUV⟩ => ⟨⟨U, V, hU, hV, hyV, hUV⟩, hxU⟩
  match hK (fun i : SeparatingPair y => i.left) (fun i => i.isOpen_left) hcov with
  | ⟨_, hJ, hsub⟩ =>
    match hJ with
    | ⟨n, g, hg⟩ =>
      ⟨Set.interFin n fun k => (g k).right,
       isOpen_interFin n _ fun k => (g k).isOpen_right,
       Set.mem_interFin n _ y fun k => (g k).mem_right,
       fun a ha haK =>
         match hsub a haK with
         | ⟨i, hiJ, hai⟩ =>
           match hg i hiJ with
           | ⟨k, hk⟩ =>
             have hav : a ∈ (g k).right := Set.interFin_mem n _ a ha k
             have hau : a ∈ (g k).left := hk ▸ hai
             have hmem : a ∈ (g k).left ∩ (g k).right := ⟨hau, hav⟩
             ((g k).disjoint ▸ hmem : a ∈ (∅ : Set Y))⟩

/-- 補題2: ハウスドルフ空間のコンパクト集合は閉。上の2つの補題を合わせるだけ。 -/
theorem IsCompact.isClosed [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K := by
  show IsOpen (Kᶜ : Set Y)
  refine isOpen_of_nhds fun y hy => ?_
  have ⟨W, hW, hyW, hWK⟩ := hK.exists_disjoint_nhds hy
  exact ⟨W, hW, hyW, hWK⟩

#check IsCompact.isClosed

/-!
    IsCompact.isClosed {Y : Type} [TopologicalSpace Y] [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K

「空間がハウスドルフ」という仮定は `[Hausdorff Y]` という
インスタンス引数の形で現れる（証明も登録簿から探される）。
-/

-- 項ではここまで縮む。`show` は不要（`IsClosed K` と `IsOpen Kᶜ` は定義上同じ命題）で、
-- 補題が返す ∃ の中身が `isOpen_of_nhds` の要求とそのまま一致している
example [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K :=
  isOpen_of_nhds fun _ hy => hK.exists_disjoint_nhds hy

/-! ## 9. 補題3: コンパクト空間の閉集合はコンパクト

方針: `C` の開被覆 `U` に対して

1. 各成分に開集合 `Cᶜ` を足した族 `U i ∪ Cᶜ` は空間全体を覆う
   （`Set.univ_subset_iUnion_union_compl`）
2. 空間のコンパクト性で、有限部分被覆の添字 `J` を取る
3. `C` の点は `Cᶜ` 側には入らないので、`U` だけの部分被覆に戻せる
   （`Set.subset_biUnion_of_compl`）

1 と 3 は位相と無関係な集合の補題である。
添字集合を増やさずに済ませるため、`I` が空の場合だけ主証明で先に片付ける。
-/

/-- 被覆の各成分に `Cᶜ` を足せば空間全体を覆う（方針の 1）。
`I` が空でないという仮定は、`C` の外の点をどれかの成分に割り当てるために要る。
`Nonempty I` は「`I` の項が少なくとも1つある」という命題で、構成子は `⟨i⟩`、
使うときは `have ⟨i⟩ := hI` と分解する（証明の中でそうしている）。 -/
theorem Set.univ_subset_iUnion_union_compl {α : Type} {C : Set α} {I : Type} {U : I → Set α}
    (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
    (Set.univ : Set α) ⊆ ⋃ i, U i ∪ Cᶜ := by
  intro x _
  by_cases hx : x ∈ C
  · have ⟨i, hi⟩ := hcov x hx
    exact ⟨i, Or.inl hi⟩
  · have ⟨i⟩ := hI
    exact ⟨i, Or.inr hx⟩

#check Set.univ_subset_iUnion_union_compl

/-!
    Set.univ_subset_iUnion_union_compl {α : Type} {C : Set α} {I : Type} {U : I → Set α} (hcov : C ⊆ Set.iUnion fun i ↦ U i)
      (hI : Nonempty I) : Set.univ ⊆ Set.iUnion fun i ↦ U i ∪ Cᶜ
-/

-- 項で。`by_cases` の正体は排中律 `Classical.em` による場合分けである
example {α : Type} {C : Set α} {I : Type} {U : I → Set α}
    (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
    (Set.univ : Set α) ⊆ ⋃ i, U i ∪ Cᶜ :=
  fun x _ =>
    (Classical.em (x ∈ C)).elim
      (fun hx => match hcov x hx with | ⟨i, hi⟩ => ⟨i, Or.inl hi⟩)
      (fun hx => match hI with | ⟨i⟩ => ⟨i, Or.inr hx⟩)

/-- 全体が `U i ∪ Cᶜ` たちで覆われるなら、`C` は `U` だけで覆われる（方針の 3）。 -/
theorem Set.subset_biUnion_of_compl {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i := by
  intro x hx
  have ⟨i, hiJ, hi⟩ := hsub x trivial
  cases hi with
  | inl h => exact ⟨i, hiJ, h⟩
  | inr h => exact (h hx).elim

#check Set.subset_biUnion_of_compl

/-!
    Set.subset_biUnion_of_compl {α : Type} {C : Set α} {I : Type} {J : Set I} {U : I → Set α}
      (hsub : Set.univ ⊆ J.biUnion fun i ↦ U i ∪ Cᶜ) : C ⊆ J.biUnion fun i ↦ U i
-/

-- 項で。`cases hi with` の場合分けは、`match` の入れ子パターンでも書ける
example {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i :=
  fun x hx =>
    match hsub x trivial with
    | ⟨i, hiJ, Or.inl h⟩ => ⟨i, hiJ, h⟩
    | ⟨_, _, Or.inr h⟩ => (h hx).elim

/-- 補題3: コンパクト空間の閉集合はコンパクト。
`by_cases` は「成り立つ場合」と「成り立たない場合」の古典論理による場合分け。 -/
theorem IsClosed.isCompact [CompactSpace X] {C : Set X} (hC : IsClosed C) : IsCompact C := by
  intro I U hU hcov
  by_cases hI : Nonempty I
  · have ⟨J, hJ, hsub⟩ :=
      CompactSpace.isCompact_univ (fun i => U i ∪ Cᶜ)
        (fun i => isOpen_union (hU i) hC)
        (Set.univ_subset_iUnion_union_compl hcov hI)
    exact ⟨J, hJ, Set.subset_biUnion_of_compl hsub⟩
  · -- `I` が空なら `C` も空で、空な部分被覆でよい
    refine ⟨∅, Set.Finite.empty, ?_⟩
    intro x hx
    have ⟨i, _⟩ := hcov x hx
    exact (hI ⟨i⟩).elim

#check IsClosed.isCompact

/-!
    IsClosed.isCompact {X : Type} [TopologicalSpace X] [CompactSpace X] {C : Set X} (hC : IsClosed C) : IsCompact C

補題2と対をなす形。こちらの空間側の仮定は `[CompactSpace X]`。
-/

-- 項で。暗黙引数 `I` を場合分けで使うので、`fun {I} U …` と名前を付けて受ける
example [CompactSpace X] {C : Set X} (hC : IsClosed C) : IsCompact C :=
  fun {I} U hU hcov =>
    (Classical.em (Nonempty I)).elim
      (fun hI =>
        match CompactSpace.isCompact_univ (fun i => U i ∪ Cᶜ)
            (fun i => isOpen_union (hU i) hC)
            (Set.univ_subset_iUnion_union_compl hcov hI) with
        | ⟨J, hJ, hsub⟩ => ⟨J, hJ, Set.subset_biUnion_of_compl hsub⟩)
      (fun hI =>
        ⟨∅, Set.Finite.empty, fun x hx =>
          match hcov x hx with
          | ⟨i, _⟩ => (hI ⟨i⟩).elim⟩)

/-! ## 10. 目標: コンパクトからハウスドルフへの連続全単射は同相

同相写像とは、連続な全単射であって逆写像も連続なもの。
一般には逆写像の連続性は自動ではないが、
定義域がコンパクトで終域がハウスドルフならそれが従う、というのがここでの定理。

方針: 示すべきは「`X` の開集合 `s` について `g ⁻¹' s` が開」。

1. 両側逆写像では「`g` による逆像」＝「`f` による像」（`Set.preimage_eq_image`）。
   これを `sᶜ` に使うと、`g ⁻¹' s` は `f '' sᶜ` の**補集合**だと分かる
2. 開集合の補集合は閉（`isClosed_compl`）
3. 補題3 → 補題1 → 補題2 の連鎖で
   「`sᶜ` は閉 → `sᶜ` はコンパクト → `f '' sᶜ` はコンパクト → `f '' sᶜ` は閉」
4. 閉の定義は「補集合が開」だから、その補集合である `g ⁻¹' s` は開
-/

/-- 同相写像。互いに逆な連続写像の組を `structure` で束ねる:
データ2つ（`toFun`, `invFun`）と、それらが満たすべき性質4つ。
`Homeomorph X Y : Type` は「`X` と `Y` の間の同相写像」**全体の型**であり、
`X ≅ Y` という命題ではなく、同相写像そのものをデータとして持ち歩く。 -/
structure Homeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun

#check Homeomorph

/-!
    Homeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Type

結果が `Prop` でなく `Type`。「同相である」という命題ではなく、
同相写像というデータの型である。
-/

/-- 両側逆写像をもつ写像では、`g` による逆像は `f` による像に等しい（方針の 1）。
位相と無関係な、集合の補題である。全単射のとき「逆像で考えても像で考えても同じ」
という日常的な言い替えの正体がこれ。 -/
theorem Set.preimage_eq_image {α β : Type} {f : α → β} {g : β → α}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (s : Set α) :
    g ⁻¹' s = f '' s := by
  apply Set.ext
  intro y
  constructor
  · -- `g y ∈ s` なら、`y` は `s` の点 `g y` の像（`f (g y) = y`）
    intro hy
    exact ⟨g y, hy, hfg y⟩
  · -- `y = f x`（`x ∈ s`）なら、`g y = g (f x) = x ∈ s`
    intro ⟨x, hx, hfx⟩
    show g y ∈ s
    rw [← hfx, hgf]
    exact hx

#check Set.preimage_eq_image

/-!
    Set.preimage_eq_image {α β : Type} {f : α → β} {g : β → α} (hgf : ∀ (x : α), g (f x) = x) (hfg : ∀ (y : β), f (g y) = y)
      (s : Set α) : g ⁻¹' s = f '' s
-/

-- 項で。`rw [← hfx, hgf]` の2回の書き換えが、`▸` 2回に分かれる
example {α β : Type} {f : α → β} {g : β → α}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (s : Set α) :
    g ⁻¹' s = f '' s :=
  Set.ext fun y =>
    ⟨fun hy => ⟨g y, hy, hfg y⟩,
     fun ⟨x, hx, hfx⟩ =>
      have h1 : g (f x) ∈ s := (hgf x).symm ▸ hx
      (hfx ▸ h1 : g y ∈ s)⟩

/-- 開集合の補集合は閉（方針の 2）。閉の定義は「補集合が開」なので、
二重補集合 `sᶜᶜ = s` に帰着する。 -/
theorem isClosed_compl {s : Set X} (hs : IsOpen s) : IsClosed sᶜ := by
  show IsOpen (sᶜᶜ : Set X)
  rw [Set.compl_compl]
  exact hs

#check isClosed_compl

/-!
    isClosed_compl {X : Type} [TopologicalSpace X] {s : Set X} (hs : IsOpen s) : IsClosed sᶜ
-/

-- 項で。`rw [Set.compl_compl]` が `▸` に、`show` が型注釈に当たる
example {s : Set X} (hs : IsOpen s) : IsClosed sᶜ :=
  ((Set.compl_compl s).symm ▸ hs : IsOpen sᶜᶜ)

/-- 逆写像の連続性。これが定理の中身:
`g` が連続写像 `f` の両側逆写像なら、`g` も連続。
前半の4行が方針の 3（補題3 → 補題1 → 補題2 をドット記法でつなぐ）、
後半が方針の 1・4 による書き換えである。

仮定を「`f` は全単射」ではなく「両側逆写像 `g` がある」という形にしたのは、
結論が `g` の連続性——特定の写像 `g` についての主張——だからである。
全単射から逆写像を**作る**作業（選択公理が要る）は最後の
`Homeomorph.ofContinuousBijective` に分離してあり、
この定理自体は選択公理なしで証明できる。 -/
theorem continuous_invFun [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g := by
  intro s hs
  -- `sᶜ` は閉 → コンパクト → その像はコンパクト → その像は閉
  have hcC : IsClosed (sᶜ : Set X) := isClosed_compl hs
  have hcpt : IsCompact (sᶜ : Set X) := hcC.isCompact
  have himg : IsCompact (f '' (sᶜ : Set X)) := hcpt.image hf
  have hcl : IsClosed (f '' (sᶜ : Set X)) := himg.isClosed
  -- `g ⁻¹' s` は `f '' sᶜ` の補集合（`preimage_eq_image` を `sᶜ` に適用して補集合を取る。
  -- `g ⁻¹' sᶜ` と `(g ⁻¹' s)ᶜ` は定義上同じ集合であることを使っている）
  have heq : g ⁻¹' s = (f '' (sᶜ : Set X))ᶜ := by
    rw [← Set.preimage_eq_image hgf hfg (sᶜ : Set X)]
    exact (Set.compl_compl _).symm
  rw [heq]
  exact hcl

#check continuous_invFun

/-!
    continuous_invFun {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] [CompactSpace X] [Hausdorff Y]
      {f : X → Y} (hf : Continuous f) {g : Y → X} (hgf : ∀ (x : X), g (f x) = x) (hfg : ∀ (y : Y), f (g y) = y) :
      Continuous g

長いが、左から順に「空間の条件（インスタンス引数4つ）→ `f` の連続性 →
`g` が両側逆写像であること2つ → 結論 `g` の連続性」と読み下せる。
-/

-- 定理の中身も項で。`have` の連鎖はそのまま項の `have` になり、
-- `rw` だけが `▸` と `congrArg`（等式の両辺の補集合を取る）に置き換わる
example [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g :=
  fun s hs =>
    have hcC : IsClosed (sᶜ : Set X) := isClosed_compl hs
    have hcpt : IsCompact (sᶜ : Set X) := hcC.isCompact
    have himg : IsCompact (f '' (sᶜ : Set X)) := hcpt.image hf
    have hcl : IsClosed (f '' (sᶜ : Set X)) := himg.isClosed
    have h1 : g ⁻¹' (sᶜ : Set X) = f '' (sᶜ : Set X) :=
      Set.preimage_eq_image hgf hfg _
    have heq : g ⁻¹' s = (f '' (sᶜ : Set X))ᶜ :=
      (Set.compl_compl (g ⁻¹' s)).symm.trans (congrArg (·ᶜ) h1)
    heq ▸ hcl

/-- 目標の定理: コンパクト空間からハウスドルフ空間への連続全単射は同相写像。
（`#check` の表示を見る前に、主定理の型——空間の条件・`f` の条件・結論——が
どんな引数の列になるか、自分で予想してから確かめてほしい。）

`where` 構文で `Homeomorph` の6フィールドを埋める。逆写像は、全射性 `hbij.surjective` の
「存在する」から `Classical.choose` で1つ選んで作る。存在の証明から値を
取り出すこの操作が普通の項の構成では許されないこと（`CH.lean` 11節の
「対応のずれ」）の代金が、公理 `Classical.choice` への依存と
`noncomputable`（この関数は計算はできないが、項としては正当）という印である。

最後のフィールドで使う `_root_.` は「トップレベルの名前」の明示。いま埋めている
フィールド自身が `continuous_invFun` という同名なので、外の定理の方を指すために
付けている。 -/
noncomputable def Homeomorph.ofContinuousBijective [CompactSpace X] [Hausdorff Y]
    (f : X → Y) (hf : Continuous f) (hbij : Function.Bijective f) : Homeomorph X Y where
  toFun := f
  invFun := fun y => Classical.choose (hbij.surjective y)
  left_inv := fun x => hbij.injective (Classical.choose_spec (hbij.surjective (f x)))
  right_inv := fun y => Classical.choose_spec (hbij.surjective y)
  continuous_toFun := hf
  continuous_invFun :=
    _root_.continuous_invFun hf
      (fun x => hbij.injective (Classical.choose_spec (hbij.surjective (f x))))
      (fun y => Classical.choose_spec (hbij.surjective y))

#check Homeomorph.ofContinuousBijective

/-!
    Homeomorph.ofContinuousBijective {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] [CompactSpace X]
      [Hausdorff Y] (f : X → Y) (hf : Continuous f) (hbij : Function.Bijective f) : Homeomorph X Y

この型そのものが主定理の主張である——
「コンパクト空間 X からハウスドルフ空間 Y への写像 f が連続かつ全単射なら、
 X と Y の同相写像（というデータ）が得られる」。
-/

/-! ### 使った公理の確認

冒頭の「信じるもの」の 3 がこれで、`sorry` は使っていない。

ここに形式化の利点がもう1つ現れている:
**どの定理がどの公理に依存するかが、機械的に確かめられる形で明示される**。
実際、この教材の範囲でも `#print axioms` を当てると

* 補題1 `IsCompact.image` は公理に**一切**依存しない
* 補題2の核 `IsCompact.exists_disjoint_nhds` は `propext` のみ
  （途中の `#print axioms` で確認したとおり、選択公理なしで証明できた）
* `Classical.choice` が入る経路は3つだけ:
  1. `Set.compl_compl` の背理法（`Classical.byContradiction`）
  2. 補題3まわりの `by_cases`（`x ∈ C` と `Nonempty I`）。任意の述語への
     排中律であり、Lean の排中律は Diaconescu の定理によって
     choice から導かれた**定理**である
  3. 主定理での逆写像の構成（`Classical.choose`。「存在する」から
     データを取り出す、choice のもっとも直接的な使用）

という勾配が観察できる。紙の証明では「どこで選択公理を使ったか」は
注意深く読まないと分からないが、ここでは検査器が正確に教えてくれる。

なお `propext` は集合を述語として定義したことから、`Quot.sound` は
`Set.ext` の中の `funext`（Lean では定理）から来ている。
-/

#print axioms Homeomorph.ofContinuousBijective

/-!
    'Homeomorph.ofContinuousBijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/-! ### ✏ 練習

1. `#print axioms isOpen_empty` の結果を予想してから確かめよ。
   `Classical.choice` は入るだろうか（合併の公理と `Set.ext` だけで示した証明だった）。
2. `discrete Bool` を使って、`TopologicalSpace Bool` の項を1つ `example` で書け。
3. `IsCompact.isClosed` の型で、「空間がハウスドルフ」という仮定が
   3種類の括弧のどれで現れるか予想してから、本文の表示の枠で確かめよ。
-/

/-! 余力があれば、発展演習 `Extra.lean` へ（解答は `ExtraSol.lean`）。
位相空間の圏と自由忘却随伴を組み立て、このファイルの主定理の
ハウスドルフという仮定が外せないことを反例で確かめるほか、
位相空間の別定義（閉集合系・閉包・近傍系・ネット）の等価性や、
部分空間・積・直和・商をまとめて生む誘導位相とその普遍性を扱う。 -/
