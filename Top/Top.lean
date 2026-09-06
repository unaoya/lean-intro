/-!
# 位相空間

mathlib を使わず、Lean 4 の標準ライブラリだけで位相空間を組み立てる。

最終目標は「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」。
そのために必要なものだけを、必要になった順に足していく。

標準ライブラリには数学でいう「集合」がないので、まずそこから作る。

## この定理を信じるには何を信じればよいか

末尾の定理 `Homeomorph.ofContinuousBijective` を信じるのに必要なのは、次の3つだけである。

1. Lean の型検査器が正しいこと（`CH.lean` の10節で見た「証明の検査＝型検査」）
2. このファイルに書いた**定義**が、意図した数学的概念を写していること
3. 末尾の `#print axioms` に表示される3つの公理

証明そのものは信じる必要がない。途中の議論がどれだけ長く込み入っていても、
型検査を通った時点で検査は済んでいる。

このうち機械が保証**できない**のは 2 だけである。定義が間違っていれば、
そこから証明した定理は意図と違うことを言っている。だからこのファイルでは、
すべての定義を1ファイルに収めて目視で監査できる分量に保ち
（mathlib を使わないのはこのためでもある）、主要な定義には
よく知る例・事実がそこから出ることを確かめる「定義の確認」を添えてある。

## 読み方: 各宣言のあとの `#check`

各宣言の直後に `#check 名前` を置き、その表示を `-- 表示:` に書き添えてある。
「いま何がどんな型で手に入ったか」を宣言ごとに確認しながら読んでほしい。

表示は `名前 (x : A) (y : B) : C` という「引数の列 : 結果の型」の形をとる。
これは関数型 `名前 : A → B → C` と**同じ型の別表示**である。
`def f (n : α) : β := …` と `def f : α → β := fun n => …` が同じ宣言の2通りの
書き方である（`Intro.lean` 3節）のと対応して、表示もこの2つの形を行き来する。
括弧 `( )` `{ }` `[ ]` の違いは `Intro.lean` 5節。
-/

/-! ## 1. 集合

`α` の部分集合を「`α` の要素を受け取って命題を返す関数」として定義する。
`s : Set α` と `a : α` に対し、`s a` が「`a` は `s` に属する」という命題そのものになる。
-/

/-- `α` の部分集合の型。実体は述語 `α → Prop` そのもので、新しいデータは何もない。 -/
def Set (α : Type) : Type := α → Prop

#check Set
-- 表示: `Set (α : Type) : Type`
-- 読み: 型 α を受け取って型を返す。つまり `Set : Type → Type` という
-- 「型を受け取って型を返す関数」である（`Intro.lean` 4節の `Fin` と同じ形）。

-- 確認: `Set α` は `α → Prop` の定義上の言い替えなので、`A : Set α` は
-- キャストなしでそのまま関数として適用できる。型検査が定義を展開して照合する。
example (A : Set Nat) (n : Nat) : Prop := A n

/-- 述語 `p` を集合とみなしたもの。`Set α` は定義上 `α → Prop` なので中身は
恒等関数だが、「述語を集合と読み替える」という宣言をこの名前が担う。 -/
def setOf {α : Type} (p : α → Prop) : Set α := p

#check setOf
-- 表示: `setOf {α : Type} (p : α → Prop) : Set α`
-- 読み: `{α : Type}` は暗黙引数（書かなくても `p` の型から決まる）。
-- 型としては `setOf : (α → Prop) → Set α` と読めばよい。

/-- 内包記法。`{a | p a}` と書いたら `setOf fun a => p a` の略記とする。
`syntax` は「この書き方を受け付けよ」という構文の追加（`Intro.lean` 6節）。 -/
syntax "{" ident " | " term "}" : term

-- `macro_rules` が展開規則を与える。`` `( … ) `` は構文の引用、`$x` `$p` は
-- その中に埋め込まれた変数で、「左の形が来たら右の形に書き換えよ」と読む。
-- 記法は項に展開されてから型検査されるので、検査の対象はあくまで項である。
macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

-- ここから `end Set` までの宣言には接頭辞 `Set.` が付く（`Intro.lean` 6節）
namespace Set

-- 共通の引数の前置き。以後の宣言が `α` を使うと、自動で引数に取り込まれる
variable {α : Type}

/-!
`∈` `⊆` `∩` `∪` `∅` などの記法は、標準ライブラリの記法用クラス
（`Membership` など）にこの `Set` を `instance` 登録すると使えるようになる。
逆に言えば、登録するまでは使えない。実際、この時点で `a ∈ s` と書くと

    error: failed to synthesize instance of type class
      Membership Nat (Set Nat)

と断られる（`Intro.lean` 5節で見た「登録簿にない」エラー）。
以下、クラスごとに `instance` 登録し、直後にその記法が使えるようになったことを
`#check` で確認していく。`⟨…⟩` はクラスの構成子にフィールドの中身を渡す書き方。
-/

/-- 所属 `a ∈ s`。中身は「`s` に `a` を適用する」だけで、定義上そのまま `s a`。 -/
instance : Membership α (Set α) := ⟨fun s a => s a⟩

#check (1 : Nat) ∈ ({n | n = 1} : Set Nat)
-- 表示: `1 ∈ setOf fun n ↦ n = 1 : Prop`
-- 読み: 型が `Prop` と付いた＝ `∈` の登録に成功している。なお表示が
-- `{n | n = 1}` に戻らないのは、自作した記法が構文解析（読む方向）専用で、
-- 表示（書く方向）の規則までは作っていないから。展開先の `setOf …` がそのまま見えている。

-- さらに確認: `1 ∈ {n | n = 1}` は定義上そのまま命題 `1 = 1` なので `rfl` で閉じる
example : (1 : Nat) ∈ ({n | n = 1} : Set Nat) := rfl

/-- 包含 `s ⊆ t`: `s` のどの要素も `t` に属する。全称と含意だけで書ける。 -/
instance : HasSubset (Set α) := ⟨fun s t => ∀ a, a ∈ s → a ∈ t⟩

#check ({n | n = 1} : Set Nat) ⊆ {n | n = 2}   -- 型は Prop

/-- 共通部分 `s ∩ t`: 両方に属する点の全体（「かつ」）。 -/
instance : Inter (Set α) := ⟨fun s t => {a | a ∈ s ∧ a ∈ t}⟩

#check ({n | n = 1} : Set Nat) ∩ {n | n = 2}   -- 型は Set Nat（命題でなく集合）

/-- 合併 `s ∪ t`: どちらかに属する点の全体（「または」）。 -/
instance : Union (Set α) := ⟨fun s t => {a | a ∈ s ∨ a ∈ t}⟩

#check ({n | n = 1} : Set Nat) ∪ {n | n = 2}   -- 型は Set Nat

/-- 空集合 `∅`: どの点も属さない集合。中身は「つねに `False` を返す述語」。 -/
instance : EmptyCollection (Set α) := ⟨{_a | False}⟩

#check (∅ : Set Nat)   -- 表示: `∅ : Set Nat`

/-!
`instance` は名前のない宣言だが、実際には Lean が自動で命名している。
上の5つは `Set.instMembership`, `Set.instInter` のような名前になる
（`set_option pp.explicit true` で項を表示すると中に見える）。
`instance memInst : Membership α (Set α) := …` と自分で名前を付けてもよい。
-/

/-- 全体集合。どの点も属する集合（つねに `True` を返す述語）。 -/
def univ : Set α := {_a | True}

#check univ
-- 表示: `Set.univ {α : Type} : Set α`
-- 読み: namespace の中で宣言したのでフルネームは `Set.univ`。
-- 明示引数はなく、暗黙の `α` は使う場面の期待される型から決まる。

-- 確認: `a ∈ univ` は定義上 `True` なので、その構成子 `trivial` で閉じる
example : (0 : Nat) ∈ (univ : Set Nat) := trivial

/-- 補集合 `sᶜ`: `s` に属さない点の全体。`∉` は `¬(a ∈ s)` の略記。 -/
def compl (s : Set α) : Set α := {a | a ∉ s}

#check compl
-- 表示: `Set.compl {α : Type} (s : Set α) : Set α`
-- 読み: 集合を受け取って集合を返す。`compl : Set α → Set α` と同じこと。

/-- 後置記法 `sᶜ`。`max` は最も強い結合を表す（結合の強さは後でまとめて確認する）。 -/
postfix:max "ᶜ" => Set.compl

/-- 像。`f '' s` は `s` の点を `f` で送った先の全体。
「どこかの `a ∈ s` から来た」を `∃` で言う。 -/
def image {β : Type} (f : α → β) (s : Set α) : Set β := {b | ∃ a, a ∈ s ∧ f a = b}

#check image
-- 表示: `Set.image {α β : Type} (f : α → β) (s : Set α) : Set β`
-- 読み: 明示引数が2つ並ぶカリー化された関数。
-- `image : (α → β) → Set α → Set β` と読み替えられる。

/-- 中置記法 `f '' s`。数字 `80` は結合の強さ。 -/
infixl:80 " '' " => Set.image

/-- 集合族 `S` に属する集合すべての合併。
位相の公理でいう「任意個の合併」を、添字を使わずにこれで表す。 -/
def sUnion (S : Set (Set α)) : Set α := {a | ∃ s, s ∈ S ∧ a ∈ s}

#check sUnion
-- 表示: `Set.sUnion {α : Type} (S : Set (Set α)) : Set α`
-- 読み: 引数の型が `Set (Set α)`＝「集合の集合」であることに注意。

/-- 前置記法 `⋃₀ S`。 -/
prefix:110 "⋃₀ " => Set.sUnion

/-- 添字づけられた集合族 `U : I → Set α` の合併。
族とは「添字を受け取って集合を返す関数」である（`Intro.lean` 4節）。 -/
def iUnion {I : Type} (U : I → Set α) : Set α := {a | ∃ i, a ∈ U i}

#check iUnion
-- 表示: `Set.iUnion {α I : Type} (U : I → Set α) : Set α`
-- 読み: 暗黙引数が `α` と `I` の2つ。どちらも `U` の型から決まるので書かずに済む。

/-- 添字を `J ⊆ I` に制限した合併。「部分族の合併」を表す。 -/
def biUnion {I : Type} (J : Set I) (U : I → Set α) : Set α := {a | ∃ i, i ∈ J ∧ a ∈ U i}

#check biUnion
-- 表示: `Set.biUnion {α I : Type} (J : Set I) (U : I → Set α) : Set α`

/-- 逆像。`f ⁻¹' s` は、`f` で送ると `s` に入る点の全体。 -/
def preimage {β : Type} (f : α → β) (s : Set β) : Set α := {a | f a ∈ s}

#check preimage
-- 表示: `Set.preimage {α β : Type} (f : α → β) (s : Set β) : Set α`
-- 読み: `image` と見比べると `Set β → Set α` で、集合の移動が `f` と**逆向き**。

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
「高々 `n` 個」で十分であり、こうしておくと部分集合の有限性がただちに従う。 -/
def Finite (s : Set α) : Prop := ∃ (n : Nat) (f : Fin n → α), ∀ a ∈ s, ∃ i, f i = a

#check Finite
-- 表示: `Set.Finite {α : Type} (s : Set α) : Prop`
-- 読み: 結果が `Prop`。つまりこれは集合の**性質**（集合を受け取って命題を返す述語）。

/-- 空集合は有限。`n = 0` とし、拾う関数には `Fin.elim0`（`Fin 0` は空の型なので、
そこからはどこへでも関数が作れる）を渡す。`⟨…, …, …⟩` は `∃` の導入（`CH.lean` 6節）。 -/
theorem Finite.empty : (∅ : Set α).Finite :=
  ⟨0, Fin.elim0, fun _ ha => False.elim ha⟩

#check Finite.empty
-- 表示: `Set.Finite.empty {α : Type} : ∅.Finite`
-- 読み: 仮定なしの定理。`∅.Finite` はドット記法の表示で `Set.Finite ∅` のこと。
-- 定理の #check は「証明済みの命題」を型として見せてくれる。

/-- 外延性: 属する要素が一致する集合は等しい。
関数の外延性 `funext` と命題の外延性 `propext` から従う
（集合を関数として定義したことの代金をここで払う）。
以後、集合の等式を示すときは `apply Set.ext` で「要素ごとの同値」に還元する。 -/
theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

#check ext
-- 表示: `Set.ext {α : Type} {s t : Set α} (h : ∀ (a : α), a ∈ s ↔ a ∈ t) : s = t`
-- 読み: 定理の型は「仮定 → 結論」の関数型。仮定 `h` を渡すと結論 `s = t` の証明が返る。
-- `s t` が暗黙なのは、`h` の型に現れるので自動で決まるから。

/-- 二重補集合。ここで初めて古典論理を使う:
`Classical.byContradiction : (¬p → False) → p` は背理法そのものである。 -/
theorem compl_compl (s : Set α) : sᶜᶜ = s :=
  ext fun _ => ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

#check compl_compl
-- 表示: `Set.compl_compl {α : Type} (s : Set α) : sᶜᶜ = s`
-- 読み: どの集合 `s` にも適用できる等式。`∀ s, …` と書くのと `(s : Set α)` を
-- 引数に取るのは同じこと（`Intro.lean` 4節: ∀ は依存関数型）。

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

#check union_eq_sUnion
-- 表示: `Set.union_eq_sUnion {α : Type} (s t : Set α) :
--        s ∪ t = ⋃₀ setOf fun u ↦ u = s ∨ u = t`
-- 読み: 内包記法は表示では展開先の `setOf` の形で見える（前述）。

/-! ### 有限個の共通部分

`Fin n` で番号づけられた集合たちの共通部分。`n` についての再帰で定義する。
ハウスドルフ側の証明で、有限部分被覆から近傍を1つ作るのに使う。
-/

/-- `n` 個の集合 `W 0, …, W (n-1)` の共通部分。
`Nat` の構造にそったパターンマッチ（`Intro.lean` 5節）で定義する:
`0` 個なら `univ`、`n + 1` 個なら「先頭 `W 0`」と「残り `n` 個の共通部分」の `∩`。
`fun i => W i.succ` は添字を1つずらして「残りの族」を作っている。 -/
def interFin : (n : Nat) → (Fin n → Set α) → Set α
  | 0, _ => univ
  | n + 1, W => W 0 ∩ interFin n fun i => W i.succ

#check interFin
-- 表示: `Set.interFin {α : Type} (n : Nat) : (Fin n → Set α) → Set α`
-- 読み: 表示に binder 形式（`(n : Nat)`）と矢印形式（`→`）が**混ざっている**が、
-- どちらも同じ関数型の表示にすぎない。全体としては
-- `interFin : (n : Nat) → (Fin n → Set α) → Set α` という2引数関数である。

/-- すべての `W i` に入る点は共通部分に入る。
定義と同じ再帰の形で証明を書く——**再帰で書いた証明が数学的帰納法**である。
`n = 0` の場合のゴールは `a ∈ univ` すなわち `True` なので `trivial`。 -/
theorem mem_interFin : ∀ (n : Nat) (W : Fin n → Set α) (a : α), (∀ i, a ∈ W i) →
    a ∈ interFin n W
  | 0, _, _, _ => trivial
  | n + 1, _, a, h => ⟨h 0, mem_interFin n _ a fun i => h i.succ⟩

#check mem_interFin
-- 表示: `Set.mem_interFin {α : Type} (n : Nat) (W : Fin n → Set α) (a : α) :
--        (∀ (i : Fin n), a ∈ W i) → a ∈ interFin n W`
-- 読み: 引数3つのあと、「仮定 → 結論」。長い表示は適当な位置で折り返されるが
-- 意味は変わらない。

/-- 共通部分に入る点は、すべての `W i` に入る（逆向き）。
`n = 0` では示すべき添字がそもそもない（`Fin 0` は空）ので `Fin.elim0`。
`n + 1` では途中から `by` でタクティクに切り替え、
添字 `i` を `Fin.cases` で「先頭か、後続か」に場合分けする。 -/
theorem interFin_mem : ∀ (n : Nat) (W : Fin n → Set α) (a : α), a ∈ interFin n W →
    ∀ i, a ∈ W i
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, W, a, h, i => by
      cases i using Fin.cases with
      | zero => exact h.1
      | succ j => exact interFin_mem n _ a h.2 j

#check interFin_mem
-- 表示: `Set.interFin_mem {α : Type} (n : Nat) (W : Fin n → Set α) (a : α) :
--        a ∈ interFin n W → ∀ (i : Fin n), a ∈ W i`
-- 読み: `mem_interFin` と仮定・結論が入れ替わっている。2つ合わせて同値。

end Set

/-! ## 2. 全単射

目標の「連続全単射」を述べるために要る。
`Function.Injective`（`∀ ⦃a b⦄, f a = f b → a = b`）と
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
-- 表示: `Function.Bijective {α β : Type} (f : α → β) : Prop`
-- 読み: 写像の性質（写像を受け取って命題を返す）。

/-- `⋃ i, U i` で族全体の合併を表す。 -/
syntax:110 "⋃ " ident ", " term : term
/-- `⋃ i ∈ J, U i` で添字を `J` に制限した合併を表す。 -/
syntax:110 "⋃ " ident " ∈ " term:110 ", " term : term

macro_rules
  | `(⋃ $i, $U) => `(Set.iUnion fun $i => $U)
  | `(⋃ $i ∈ $J, $U) => `(Set.biUnion $J fun $i => $U)

/-! ## 3. 位相空間

開集合が何であるかを指定するデータ `IsOpen` と、それが満たすべき3つの公理。
-/

/-- 位相空間の構造。「どの部分集合を開と呼ぶか」のデータ `IsOpen` と、
それが満たすべき3公理を `class` で束ねる（データ＋性質という構成は
`Intro.lean` 5節の structure/class と同じ）。

`class` にしたので、以後 `[TopologicalSpace X]` と角括弧で書くだけで
「`X` に載っている位相」がインスタンス引数として暗黙に渡る。

フィールドは `def` と同じく「引数をコロンの左に書く」形で宣言できる
（`Intro.lean` 3節の binder 形式）。`∀` と `→` を並べて書いても同じ型である。 -/
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
-- 表示: `TopologicalSpace (X : Type) : Type`
-- 読み: クラスも「型を受け取って型を返す関数」。`TopologicalSpace X` は
-- 「`X` 上の位相全体の型」で、その項1つが位相1つに当たる。

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
-- 表示: `isOpen_empty {X : Type} [TopologicalSpace X] : IsOpen ∅`
-- 読み: `[TopologicalSpace X]` がインスタンス引数として表示に現れる。
-- 結論の `IsOpen ∅` がどの位相の話かは、この引数が決めている。

/-- 2つの開集合の合併も開。公理は「集合族の合併」の形なので、
まず補題 `Set.union_eq_sUnion` で合併を族の合併に書き換えてから公理を適用する。
族の各要素は `s` か `t` のどちらかなので、場合分けしてそれぞれの開性を使う。 -/
theorem isOpen_union {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  rw [Set.union_eq_sUnion]
  refine isOpen_sUnion _ fun u hu => ?_
  cases hu with
  | inl h => rw [h]; exact hs
  | inr h => rw [h]; exact ht

#check isOpen_union
-- 表示: `isOpen_union {X : Type} [TopologicalSpace X] {s t : Set X}
--        (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t)`
-- 読み: 明示引数は証明2つだけ。`s t` は `hs ht` の型から決まるので暗黙。

/-- 有限個の開集合の共通部分は開。`n` についての再帰で、公理の「2つの共通部分」を繰り返す。

無限個の共通部分では成り立たないことに注意（例えば実数直線で
`⋂ n, (-1/n, 1/n) = {0}` は開でない）。有限性がここで効く。 -/
theorem isOpen_interFin : ∀ (n : Nat) (W : Fin n → Set X), (∀ i, IsOpen (W i)) →
    IsOpen (Set.interFin n W)
  | 0, _, _ => isOpen_univ
  | n + 1, _, h => isOpen_inter _ _ (h 0) (isOpen_interFin n _ fun i => h i.succ)

#check isOpen_interFin
-- 表示: `isOpen_interFin {X : Type} [TopologicalSpace X] (n : Nat) (W : Fin n → Set X) :
--        (∀ (i : Fin n), IsOpen (W i)) → IsOpen (Set.interFin n W)`

/-- 閉集合: 補集合が開。原始概念は開集合だけなので、閉はこれで定義するほかない。 -/
def IsClosed (s : Set X) : Prop := IsOpen sᶜ

#check IsClosed
-- 表示: `IsClosed {X : Type} [TopologicalSpace X] (s : Set X) : Prop`
-- 読み: `IsOpen` と同じ形の、集合の性質。

/-! ### 定義の確認

型検査が見ているのは「`IsOpen` が3公理を満たす」ことだけで、
`TopologicalSpace` という定義が数学の位相空間の定義を写しているかどうかは
機械では確かめられない（冒頭の 2）。その代わりに、
よく知る例が定義を満たすことを見ておく。
-/

/-- 離散位相: すべての部分集合が開。どんな型にも入る、いちばん簡単な位相。
`where` 構文でクラスの各フィールドを埋めて、`TopologicalSpace X` の項を作る。
公理側はすべて `True` の証明なので `trivial` で済む。 -/
@[reducible] def discrete (X : Type) : TopologicalSpace X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ _ _ => trivial
  isOpen_sUnion := fun _ _ => trivial

#check discrete
-- 表示: `discrete (X : Type) : TopologicalSpace X`
-- 読み: 型を受け取って**位相そのもの**（`TopologicalSpace X` の項）を返す関数。

/-! ## 4. 連続写像

「近くの点を近くに送る」を開集合だけで言い換えたのが次の定義。
写像の向きと逆に、行き先の開集合を引き戻して考えるのがポイント。
-/

variable {Y : Type} [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z]

/-- 連続写像: 開集合の逆像がつねに開。 -/
def Continuous (f : X → Y) : Prop := ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

#check Continuous
-- 表示: `Continuous {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
--        (f : X → Y) : Prop`
-- 読み: 両側の空間それぞれにインスタンス引数が付く。「`f` が連続」という命題は、
-- 実は「どの位相に関してか」を2つ暗黙に抱えている。

/-! ### 定義の確認

連続の定義についても、よく知る事実がここから出ることを見ておく。
どちらも証明は1行で、逆像が定義上ぴったり重なることを使うだけ。
-/

/-- 恒等写像は連続。`(fun x => x) ⁻¹' s` は `s` そのものなので、仮定をそのまま返せばよい。 -/
theorem continuous_id : Continuous (fun x : X => x) :=
  fun _ hs => hs

#check continuous_id
-- 表示: `continuous_id {X : Type} [TopologicalSpace X] : Continuous fun x => x`
-- 読み: 仮定なしの定理。結論の中の `fun x => x` が恒等写像。

/-- 連続写像の合成は連続。
`(g ∘ f) ⁻¹' s` が `f ⁻¹' (g ⁻¹' s)` と定義上等しいので、引き戻しを2回続けるだけ。
名前を `Continuous.comp` としたので、`hg.comp hf` とドット記法で使える（`Intro.lean` 5節）。 -/
theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) :=
  fun s hs => hf _ (hg s hs)

#check Continuous.comp
-- 表示: `Continuous.comp {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
--        {Z : Type} [TopologicalSpace Z] {g : Y → Z} {f : X → Y}
--        (hg : Continuous g) (hf : Continuous f) : Continuous fun x => g (f x)`
-- 読み: 空間3つぶんのインスタンス引数が並ぶ。明示引数は証明 `hg` `hf` の2つで、
-- 先に適用される `f` の連続性が**後ろ**に来る（合成の記法 `g ∘ f` と同じ順）。

/-! ## 5. ハウスドルフ空間

「異なる2点は開集合で見分けられる」という条件。
点が多すぎず貼りついていない、という感じの性質。
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
-- 表示: `Hausdorff (X : Type) [TopologicalSpace X] : Prop`
-- 読み: `TopologicalSpace X : Type`（データ）と違い、こちらは結果が `Prop`（性質）。

/-! ## 6. コンパクト

「どんな開被覆にも有限部分被覆がある」という条件。
無限にある開集合のうち有限個で済ませられる、という有限性の性質。

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
-- 表示: `IsCompact {X : Type} [TopologicalSpace X] (K : Set X) : Prop`
-- 読み: 表示は短いが、定義の中身は上のとおり `∀` が3つ重なった命題である。

/-- 空間そのものがコンパクトであること: 全体集合 `univ` がコンパクト集合である。
`Hausdorff` と同じく、命題1つだけの `class : Prop`。 -/
class CompactSpace (X : Type) [TopologicalSpace X] : Prop where
  isCompact_univ : IsCompact (Set.univ : Set X)

#check CompactSpace
-- 表示: `CompactSpace (X : Type) [TopologicalSpace X] : Prop`

/-! ## 7. 補題1: コンパクト集合の連続像はコンパクト

方針: 与えられた `f '' K` の開被覆 `U` に対して

1. 被覆を `f` で引き戻して `K` の開被覆 `f ⁻¹' U i` を作る（`Set.subset_preimage_iUnion`）
2. `K` のコンパクト性で、有限部分被覆の添字 `J` を取る
3. 同じ `J` が `f '' K` の有限部分被覆を与える（`Set.image_subset_biUnion`）

1 と 3 は位相と無関係な、像と逆像についての一般的な補題である。
有限性は受け取った `J` をそのまま使い回すだけなので、`Fin n` を開ける必要はない。

なお、細かい補題には `theorem` のかわりに `lemma` と書きたいところだが、
`lemma` という宣言は core Lean にはない（mathlib がマクロとして定義している）。
中身は `theorem` の別名にすぎないので、自分でも作れる。以下の補題で使う。
-/

/-- `lemma` 宣言を `theorem` の別名として自作する。
`declModifiers` は docstring などの修飾部、`declId`・`declSig`・`declVal` は
名前・シグネチャ・本体に対応する構文カテゴリ。 -/
macro mods:declModifiers "lemma" d:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $d $sig $val)

/-- 像が族で覆われるなら、元の集合は逆像の族で覆われる（方針の 1）。
位相と無関係な補題なので、節の変数 `X Y`（位相つき）ではなく
新しい型変数 `α β` で述べる。 -/
lemma Set.subset_preimage_iUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i := by
  intro x hx
  have ⟨i, hi⟩ := h (f x) ⟨x, hx, rfl⟩
  exact ⟨i, hi⟩

#check Set.subset_preimage_iUnion
-- 表示: `Set.subset_preimage_iUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
--        {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i`
-- 読み: 位相のインスタンス引数が付いていない＝純粋に集合の補題である。

/-- 逆像の部分族で覆われるなら、像は同じ添字の部分族で覆われる（方針の 3）。
証明中の `have ⟨x, hx, hfx⟩ := …` は `∃`（依存和）の分解（`CH.lean` 6節）。 -/
lemma Set.image_subset_biUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i := by
  intro b hb
  have ⟨x, hx, hfx⟩ := hb
  have ⟨i, hiJ, hxi⟩ := h x hx
  exact ⟨i, hiJ, hfx ▸ hxi⟩

#check Set.image_subset_biUnion
-- 表示: `Set.image_subset_biUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
--        {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i`

/-- 補題1: コンパクト集合の連続像はコンパクト。方針の3歩をそのまま並べる。
名前が `IsCompact.image` なので、`hK : IsCompact K` に対し `hK.image hf` と書ける。 -/
theorem IsCompact.image {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) := by
  intro I U hU hcov
  have ⟨J, hJ, hsub⟩ := hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
      (Set.subset_preimage_iUnion hcov)
  exact ⟨J, hJ, Set.image_subset_biUnion hsub⟩

#check IsCompact.image
-- 表示: `IsCompact.image {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
--        {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) : IsCompact (f '' K)`
-- 読み: 数学の主張「K コンパクト、f 連続 ⇒ f(K) コンパクト」が、
-- そのまま「証明を2つ受け取って証明を返す関数」の型になっている。

/-! ## 8. 補題2: ハウスドルフ空間のコンパクト集合は閉

ここが証明の山場で、有限性を実際に使うのもここだけ。方針:

1. 「各点が開近傍ごと入っている集合は開」という一般論を用意する（`isOpen_of_nhds`）
2. `K` の外の点 `y` に、`K` と交わらない開近傍 `W` を作る
   （`IsCompact.exists_disjoint_nhds`）
3. 1 に 2 を渡せば `Kᶜ` が開、すなわち `K` は閉

2 の中身: `K` の各点 `x` は `y` とハウスドルフ性で分離できる。分離する開集合の組を
点ごとに**1つ選ぶ**のではなく、「`y` を分離する開集合の組」の**全体**を添字型にして
`K` を覆う。必要なデータ（`V` 側と分離性の証明）が添字自身に抱き合わされているので、
選択公理を使わずに済む。コンパクト性で組を有限個に間引き、
その `V` 側の有限交叉（`interFin`）を `W` とする。
無限個の共通部分では開とは限らないので、有限に減らせたことが本質的に効いている。
-/

/-- 各点が開近傍ごと入っている集合は開（方針の 1）。
`s` は「`s` に含まれる開集合すべて」の合併に等しくなるので、合併の公理が使える。 -/
lemma isOpen_of_nhds {s : Set X} (h : ∀ a ∈ s, ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) :
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
-- 表示: `isOpen_of_nhds {X : Type} [TopologicalSpace X] {s : Set X}
--        (h : ∀ a ∈ s, ∃ W, IsOpen W ∧ a ∈ W ∧ W ⊆ s) : IsOpen s`

/-- コンパクト集合 `K` の外の点は、`K` と交わらない開近傍を持つ（方針の 2）。

被覆の添字型には部分型（`CH.lean` 6節の依存和）

    {p : Set Y × Set Y // IsOpen p.1 ∧ IsOpen p.2 ∧ y ∈ p.2 ∧ p.1 ∩ p.2 = ∅}

を使う。つまり添字は「開集合の組」と「それが `y` を分離しているという証明」の
抱き合わせであり、被覆の各成分が自分の `V` と分離性を持参してくる。
`hK` へは `(I := …)` という名前付き引数で添字型を明示して渡す。 -/
lemma IsCompact.exists_disjoint_nhds [Hausdorff Y] {K : Set Y} (hK : IsCompact K)
    {y : Y} (hy : y ∉ K) : ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K := by
  -- `K` を「`y` を分離する組の `U` 側」たちで覆い、コンパクト性で有限個に間引く
  have ⟨J, hJ, hsub⟩ := hK
      (I := {p : Set Y × Set Y // IsOpen p.1 ∧ IsOpen p.2 ∧ y ∈ p.2 ∧ p.1 ∩ p.2 = ∅})
      (fun i => i.val.1) (fun i => i.property.1)
      (fun x hx => by
        have hne : x ≠ y := fun h => hy (h ▸ hx)
        have ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := Hausdorff.separate x y hne
        exact ⟨⟨(U, V), hU, hV, hyV, hUV⟩, hxU⟩)
  -- `J` は有限なので `Fin n` で番号づけ、対応する `V` 側の有限交叉を `W` とする
  have ⟨n, g, hg⟩ := hJ
  refine ⟨Set.interFin n fun k => (g k).val.2, ?_, ?_, ?_⟩
  · -- 有限個の開集合の共通部分は開
    exact isOpen_interFin n _ fun k => (g k).property.2.1
  · -- `y` はどの `V` にも入っている
    exact Set.mem_interFin n _ y fun k => (g k).property.2.2.1
  · -- `W` が `K` と交わったとすると、ある組の `U` と `V` の両方に入る点ができて矛盾
    intro a ha haK
    have ⟨i, hiJ, hai⟩ := hsub a haK
    have ⟨k, hk⟩ := hg i hiJ
    have hav : a ∈ (g k).val.2 := Set.interFin_mem n _ a ha k
    have hau : a ∈ (g k).val.1 := by rw [hk]; exact hai
    have hmem : a ∈ (g k).val.1 ∩ (g k).val.2 := ⟨hau, hav⟩
    rw [(g k).property.2.2.2] at hmem
    exact hmem

#check IsCompact.exists_disjoint_nhds
-- 表示: `IsCompact.exists_disjoint_nhds {Y : Type} [TopologicalSpace Y] [Hausdorff Y]
--        {K : Set Y} (hK : IsCompact K) {y : Y} (hy : y ∉ K) :
--        ∃ W, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K`

-- 確認: この補題は選択公理どころか `Classical.choice` にも依存していない
-- （`propext` のみ）。データを添字に抱き合わせた効果がここに現れている。
#print axioms IsCompact.exists_disjoint_nhds

/-- 補題2: ハウスドルフ空間のコンパクト集合は閉。上の2つの補題を合わせるだけ。 -/
theorem IsCompact.isClosed [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K := by
  show IsOpen (Kᶜ : Set Y)
  refine isOpen_of_nhds fun y hy => ?_
  have ⟨W, hW, hyW, hWK⟩ := hK.exists_disjoint_nhds hy
  exact ⟨W, hW, hyW, hWK⟩

#check IsCompact.isClosed
-- 表示: `IsCompact.isClosed {Y : Type} [TopologicalSpace Y] [Hausdorff Y]
--        {K : Set Y} (hK : IsCompact K) : IsClosed K`
-- 読み: 「空間がハウスドルフ」という仮定は `[Hausdorff Y]` という
-- インスタンス引数の形で現れる（証明も登録簿から探される）。

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
`I` が空でないという仮定は、`C` の外の点をどれかの成分に割り当てるために要る。 -/
lemma Set.univ_subset_iUnion_union_compl {α : Type} {C : Set α} {I : Type} {U : I → Set α}
    (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
    (Set.univ : Set α) ⊆ ⋃ i, U i ∪ Cᶜ := by
  intro x _
  by_cases hx : x ∈ C
  · have ⟨i, hi⟩ := hcov x hx
    exact ⟨i, Or.inl hi⟩
  · have ⟨i⟩ := hI
    exact ⟨i, Or.inr hx⟩

#check Set.univ_subset_iUnion_union_compl
-- 表示: `Set.univ_subset_iUnion_union_compl {α : Type} {C : Set α} {I : Type}
--        {U : I → Set α} (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
--        Set.univ ⊆ ⋃ i, U i ∪ Cᶜ`

/-- 全体が `U i ∪ Cᶜ` たちで覆われるなら、`C` は `U` だけで覆われる（方針の 3）。 -/
lemma Set.subset_biUnion_of_compl {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i := by
  intro x hx
  have ⟨i, hiJ, hi⟩ := hsub x trivial
  cases hi with
  | inl h => exact ⟨i, hiJ, h⟩
  | inr h => exact absurd hx h

#check Set.subset_biUnion_of_compl
-- 表示: `Set.subset_biUnion_of_compl {α : Type} {C : Set α} {I : Type} {J : Set I}
--        {U : I → Set α} (hsub : Set.univ ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i`

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
    exact absurd ⟨i⟩ hI

#check IsClosed.isCompact
-- 表示: `IsClosed.isCompact {X : Type} [TopologicalSpace X] [CompactSpace X]
--        {C : Set X} (hC : IsClosed C) : IsCompact C`
-- 読み: 補題2と対をなす形。こちらの空間側の仮定は `[CompactSpace X]`。

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
-- 表示: `Homeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Type`
-- 読み: 結果が `Prop` でなく `Type`。「同相である」という命題ではなく、
-- 同相写像というデータの型である。

/-- 両側逆写像をもつ写像では、`g` による逆像は `f` による像に等しい（方針の 1）。
位相と無関係な、集合の補題である。全単射のとき「逆像で考えても像で考えても同じ」
という日常的な言い替えの正体がこれ。 -/
lemma Set.preimage_eq_image {α β : Type} {f : α → β} {g : β → α}
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
-- 表示: `Set.preimage_eq_image {α β : Type} {f : α → β} {g : β → α}
--        (hgf : ∀ (x : α), g (f x) = x) (hfg : ∀ (y : β), f (g y) = y) (s : Set α) :
--        g ⁻¹' s = f '' s`

/-- 開集合の補集合は閉（方針の 2）。閉の定義は「補集合が開」なので、
二重補集合 `sᶜᶜ = s` に帰着する。 -/
lemma isClosed_compl {s : Set X} (hs : IsOpen s) : IsClosed sᶜ := by
  show IsOpen (sᶜᶜ : Set X)
  rw [Set.compl_compl]
  exact hs

#check isClosed_compl
-- 表示: `isClosed_compl {X : Type} [TopologicalSpace X] {s : Set X} (hs : IsOpen s) :
--        IsClosed sᶜ`

/-- 逆写像の連続性。これが定理の中身:
`g` が連続写像 `f` の両側逆写像なら、`g` も連続。
前半の4行が方針の 3（補題3 → 補題1 → 補題2 をドット記法でつなぐ）、
後半が方針の 1・4 による書き換えである。 -/
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
-- 表示: `continuous_invFun {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
--        [CompactSpace X] [Hausdorff Y] {f : X → Y} (hf : Continuous f) {g : Y → X}
--        (hgf : ∀ (x : X), g (f x) = x) (hfg : ∀ (y : Y), f (g y) = y) : Continuous g`
-- 読み: 長いが、左から順に「空間の条件（インスタンス引数4つ）→ `f` の連続性 →
-- `g` が両側逆写像であること2つ → 結論 `g` の連続性」と読み下せる。

/-- 目標の定理: コンパクト空間からハウスドルフ空間への連続全単射は同相写像。

`where` 構文で `Homeomorph` の6フィールドを埋める。逆写像は、全射性 `hbij.surjective` の
「存在する」から `Classical.choose` で1つ選んで作る。選択を使う構成なので
`noncomputable`（この関数は計算はできないが、項としては正当）という印が要る。 -/
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
-- 表示: `Homeomorph.ofContinuousBijective {X : Type} [TopologicalSpace X] {Y : Type}
--        [TopologicalSpace Y] [CompactSpace X] [Hausdorff Y] (f : X → Y)
--        (hf : Continuous f) (hbij : Function.Bijective f) : Homeomorph X Y`
-- 読み: この型そのものが主定理の主張である——
-- 「コンパクト空間 X からハウスドルフ空間 Y への写像 f が連続かつ全単射なら、
--  X と Y の同相写像（というデータ）が得られる」。

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

/-! 余力があれば、発展演習 `Extra.lean` へ（解答は `ExtraSol.lean`）。
位相空間の圏と自由忘却随伴を組み立て、最後にこのファイルの主定理の
ハウスドルフという仮定が外せないことを反例で確かめる。 -/
