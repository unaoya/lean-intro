import Top

/-! # 発展演習: 位相空間の圏と自由忘却随伴

`Top.lean` まで読み終えた人のための演習問題。題材は次の4つ。

* 密着位相・離散位相と、その普遍性
* 位相空間の圏と、離散・密着・忘却の3つの関手
* 自由忘却随伴 「離散 ⊣ 忘却 ⊣ 密着」
* 位相空間の別定義（閉集合系・閉包作用素・近傍系・ネット）と等価性（Part 5）

最後に、これらを使って **`Top.lean` の主定理のハウスドルフという仮定が
外せないこと**を反例で確かめる。

## 進め方

* `sorry` と書かれた場所を自分の証明・構成で置き換える。
  `sorry` が残っているとビルド時に警告が出るので、消えたら完成。
* 「主張も自分で書く」問題は、コメントの指示に従って宣言ごと自分で書く。
* 構造の定義（`Category` など）は与えてある。ただし `Functor` のように
  「まず自分で設計してから見比べよ」とある定義は、先に紙に書いてみることを勧める。
* 解答は `ExtraSol.lean` にある。
* 各宣言の直後の `#check` には、`Top.lean` と同じ流儀で「表示」と「読み」を添えてある。

## 記法の補足

`Top.lean` の `Continuous` は位相をインスタンス引数で受け取るので、
1つの型に別の位相を載せて論じるには `@` で位相を明示する。例えば
`@Continuous X (discrete X) Y tY f` は「`X` に離散位相を入れたとき `f` は連続」。
-/

/-! ## Part 1: 密着位相

離散位相（`Top.lean` の `discrete`、すべての部分集合が開）の対極として、
開集合が `∅` と `univ` しかない位相を**密着位相**という。
-/

/-- 問題1: 密着位相が位相の3公理を満たすことを示せ。

ヒント: `isOpen_sUnion` では「`S` のどれかが `univ` か、全部 `∅` か」で
場合分けする（`by_cases`）。 -/
@[reducible] def indiscrete (X : Type) : TopologicalSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

#check indiscrete
-- 表示: `indiscrete (X : Type) : TopologicalSpace X`
-- 読み: `discrete` と同じ形——型を受け取って位相そのものを返す関数。

/-- 問題2: 離散位相からの写像はすべて連続であることを示せ。

離散位相では何もかも開なので、逆像の開性はただで手に入る。 -/
theorem continuous_from_discrete {X Y : Type} [tY : TopologicalSpace Y] (f : X → Y) :
    @Continuous X (discrete X) Y tY f :=
  sorry

#check continuous_from_discrete
-- 表示: `continuous_from_discrete {X Y : Type} [tY : TopologicalSpace Y] (f : X → Y) :
--        Continuous f`
-- 読み: 表示では暗黙・インスタンス引数が省かれるので、結論がただの `Continuous f` に
-- 見える。実際の主張は `@Continuous X (discrete X) Y tY f` で、`X` 側が離散位相で
-- あることは表示からは読めない。`@` 付きの主張は `#check` の表示だけでは
-- 区別できないことに注意。

/-- 問題3: 密着位相への写像はすべて連続であることを示せ。

ヒント: 逆像を取る前に開集合は `∅` か `univ` しかない。
`f ⁻¹' ∅` と `f ⁻¹' Set.univ` は定義上それぞれ `∅` と `univ` に等しい。 -/
theorem continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
    @Continuous X tX Y (indiscrete Y) f :=
  sorry

#check continuous_to_indiscrete
-- 表示: `continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
--        Continuous f`
-- 読み: 同様に、実際の主張は `@Continuous X tX Y (indiscrete Y) f`（`Y` 側が密着位相）。

-- 問題4（主張も自分で書く）:
-- 「密着位相を入れた `Bool` はハウスドルフでない」を形式化し、証明せよ。
-- ヒント: 否定 `¬p` は `p → False`（`CH.lean` 4節）。
-- `true` と `false` を分離する開集合の組が取れたとして、矛盾を導く。
-- （ここに theorem を書く）

/-! ## Part 2: 圏と関手

「対象」と「射」、恒等射と合成、そして3つの法則。圏の定義は次のとおり与える。
`Obj` と `Hom` が**データ**、`id_comp` 以下が**性質**という構成は、
`TopologicalSpace` の定義（`IsOpen` がデータ、3公理が性質）と同じ形をしている。

なお `Functor` という名前は標準ライブラリと衝突するので、
この部の定義は名前空間 `Cat` に入れる。
-/

namespace Cat

structure Category where
  /-- 対象の集まり。`Type 1` なのは、対象として `Type` の全体を入れたいから。 -/
  Obj : Type 1
  /-- 対象 `A` から `B` への射の型。 -/
  Hom : Obj → Obj → Type
  /-- 恒等射。 -/
  id : (A : Obj) → Hom A A
  /-- 合成は図式順: `comp f g` は「`f` してから `g`」。 -/
  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
  /-- 恒等射は合成の左単位。 -/
  id_comp : ∀ {A B : Obj} (f : Hom A B), comp (id A) f = f
  /-- 恒等射は合成の右単位。 -/
  comp_id : ∀ {A B : Obj} (f : Hom A B), comp f (id B) = f
  /-- 合成の結合律。 -/
  assoc : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp (comp f g) h = comp f (comp g h)

#check Category
-- 表示: `Cat.Category : Type 2`
-- 読み: フィールド `Obj` が `Type 1` の項なので、`Category` 自身は `Type 2` の項。
-- `Intro.lean` 1節の宇宙の階段（`Type : Type 1 : Type 2`）が実際に必要になる場面である。

/-- 問題5: 型の圏を作れ。対象は型、射は関数。

法則の証明はすべて `rfl` で済むはず。なぜ済むのかも考えてみること
（関数の合成は定義上結合的である）。 -/
@[reducible] def TypeCat : Category :=
  sorry

#check TypeCat
-- 表示: `Cat.TypeCat : Category`
-- 読み: 「圏」という型の項が1つ手に入った。

/-- 位相空間の圏の対象: 台の型と、その上の位相を束ねたもの。

`attribute [instance] TopSpace.str` としておくと、`A : TopSpace` に対して
`A.carrier` 上の位相が自動で見つかるようになり、`Continuous f` とだけ書ける。 -/
structure TopSpace : Type 1 where
  /-- 台の型。 -/
  carrier : Type
  /-- 台の上の位相。 -/
  str : TopologicalSpace carrier

#check TopSpace
-- 表示: `Cat.TopSpace : Type 1`
-- 読み: 台の型（`Type` の項）をフィールドに含むので、`Type` でなく `Type 1` に住む。

attribute [instance] TopSpace.str

/-- 問題6: 位相空間の圏を作れ。対象は `TopSpace`、
射は「関数と、その連続性の証明の組」`{ f : A.carrier → B.carrier // Continuous f }`。

これは `CH.lean` 6節の依存和そのもの（`Subtype`）である。
ヒント: 恒等射は `continuous_id`、合成は `Continuous.comp`。
射の等しさは `Subtype.ext`（第一成分が等しければ等しい）で示す。 -/
@[reducible] def TopCat : Category :=
  sorry

#check TopCat
-- 表示: `Cat.TopCat : Category`

/-! ### 関手

圏から圏への「構造を保つ対応」。対象の対応 `obj` と射の対応 `map` からなり、
恒等射と合成を保つ。まず自分でこの structure を設計してから、下と見比べよ。
-/

structure Functor (C D : Category) where
  /-- 対象の対応。 -/
  obj : C.Obj → D.Obj
  /-- 射の対応。行き先の型が `obj` に依存していることに注意（依存関数型）。 -/
  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)
  /-- 恒等射を恒等射に写す。 -/
  map_id : ∀ A : C.Obj, map (C.id A) = D.id (obj A)
  /-- 合成を合成に写す。 -/
  map_comp : ∀ {A B E : C.Obj} (f : C.Hom A B) (g : C.Hom B E),
    map (C.comp f g) = D.comp (map f) (map g)

#check Functor
-- 表示: `Cat.Functor (C D : Category) : Type 1`
-- 読み: 2つの圏を受け取って「その間の関手全体の型」を返す。

/-- 問題7: 忘却関手 `U : Top → Type` を作れ。位相を忘れて台の型だけを残す。 -/
@[reducible] def forgetful : Functor TopCat TypeCat :=
  sorry

#check forgetful
-- 表示: `Cat.forgetful : Functor TopCat TypeCat`

/-- 問題8: 離散関手 `D : Type → Top` を作れ。型に離散位相を載せる。
射の行き先（任意の写像が連続になること）は問題2で作った。

ヒント: 行き先の位相はインスタンス探索では見つからないので、
`continuous_from_discrete (tY := discrete _) f` のように名前付き引数で明示する。 -/
@[reducible] def discreteFunctor : Functor TypeCat TopCat :=
  sorry

#check discreteFunctor
-- 表示: `Cat.discreteFunctor : Functor TypeCat TopCat`

/-- 問題9: 密着関手 `I : Type → Top` を作れ。型に密着位相を載せる。
射の行き先は問題3で作った。 -/
@[reducible] def indiscreteFunctor : Functor TypeCat TopCat :=
  sorry

#check indiscreteFunctor
-- 表示: `Cat.indiscreteFunctor : Functor TypeCat TopCat`

/-! ## Part 3: 随伴

関手 `F : C → D` と `G : D → C` が随伴 `F ⊣ G` であるとは、
hom 集合の間に自然な全単射

    Hom_D(F A, B) ≃ Hom_C(A, G B)

があること。全単射は `Top.lean` の `Homeomorph` と同じ形の structure で表す。
「自然」の意味は `Adjunction` の2つの等式（`f` を前に合成してから対応させても、
対応させてから合成しても同じ、およびその `h` 版）。
-/

structure Equiv (α β : Type) where
  /-- 順方向の写像。 -/
  toFun : α → β
  /-- 逆方向の写像。 -/
  invFun : β → α
  /-- 往復すると戻る（`α` 側）。 -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- 往復すると戻る（`β` 側）。 -/
  right_inv : ∀ b, toFun (invFun b) = b

#check Equiv
-- 表示: `Cat.Equiv (α β : Type) : Type`

structure Adjunction {C D : Category} (F : Functor C D) (G : Functor D C) where
  /-- hom 集合の全単射 `Hom_D(F A, B) ≃ Hom_C(A, G B)`。 -/
  homEquiv : (A : C.Obj) → (B : D.Obj) → Equiv (D.Hom (F.obj A) B) (C.Hom A (G.obj B))
  /-- 自然性（`A` 側）: 射 `f` を先に合成してから対応させても、
  対応させてから合成しても同じ。 -/
  naturality_left :
    ∀ {A' A : C.Obj} {B : D.Obj} (f : C.Hom A' A) (g : D.Hom (F.obj A) B),
      (homEquiv A' B).toFun (D.comp (F.map f) g) = C.comp f ((homEquiv A B).toFun g)
  /-- 自然性（`B` 側）。 -/
  naturality_right :
    ∀ {A : C.Obj} {B B' : D.Obj} (g : D.Hom (F.obj A) B) (h : D.Hom B B'),
      (homEquiv A B').toFun (D.comp g h) = C.comp ((homEquiv A B).toFun g) (G.map h)

#check Adjunction
-- 表示: `Cat.Adjunction {C D : Category} (F : Functor C D) (G : Functor D C) : Type 1`
-- 読み: 圏 `C` `D` は関手 `F` `G` の型から決まるので暗黙引数。

/-- 問題10: 随伴「離散 ⊣ 忘却」を作れ。

`Hom_Top(D X, A) ≃ Hom_Type(X, U A)`: 左辺の射は「連続な写像」、
右辺の射は「ただの写像」だが、離散位相からはどんな写像も連続（問題2）なので、
この対応の実体は「同じ関数を右へ左へ読み替えるだけ」である。
自然性も含め、ほとんどの証明が `rfl` か `Subtype.ext rfl` で済むはず。 -/
def discreteAdj : Adjunction discreteFunctor forgetful :=
  sorry

#check discreteAdj
-- 表示: `Cat.discreteAdj : Adjunction discreteFunctor forgetful`
-- 読み: 型がそのまま「離散 ⊣ 忘却」と読める。

/-- 問題11: 随伴「忘却 ⊣ 密着」を作れ。問題10と対称的。

これで 離散 ⊣ 忘却 ⊣ 密着 という3連随伴ができたことになる。
離散位相が「もっとも細かい位相」、密着位相が「もっとも粗い位相」であることの
圏論的な言い換えである。 -/
def indiscreteAdj : Adjunction forgetful indiscreteFunctor :=
  sorry

#check indiscreteAdj
-- 表示: `Cat.indiscreteAdj : Adjunction forgetful indiscreteFunctor`
-- 読み: こちらは「忘却 ⊣ 密着」。合わせて 離散 ⊣ 忘却 ⊣ 密着。

end Cat

/-! ## Part 4（発展）: 反例 — 主定理の仮定は外せない

`Top.lean` の主定理は「コンパクト空間から**ハウスドルフ空間**への連続全単射は同相」。
ハウスドルフという仮定を外すと成り立たないことを、ここまでの道具で確かめる。

反例は恒等写像 `id : (Bool, 離散) → (Bool, 密着)`。これは
連続（問題3）かつ全単射で、定義域はコンパクト（問題12）だが、
逆写像（これも `id`）は連続でない（問題13）。つまり同相ではない。
主定理と見比べると、足りないのは終域のハウスドルフ性だけである（問題4）。
-/

-- 問題12（主張も自分で書く）:
-- 「離散位相を入れた `Bool` はコンパクト」を形式化し、証明せよ。
-- ヒント: 開被覆から `true` を覆う番号と `false` を覆う番号を1つずつ取り、
-- その2つからなる添字集合を使う。有限性の証人は `Fin 2` からの関数で作る。
-- `CompactSpace.mk` のインスタンス引数も `@` で明示する必要がある。
-- （ここに theorem を書く）

-- 問題13（主張も自分で書く）:
-- 「恒等写像 `(Bool, 密着) → (Bool, 離散)` は連続でない」を形式化し、証明せよ。
-- ヒント: 離散側で開集合 `{b | b = true}` を考える。その逆像は自分自身だが、
-- 密着位相の開集合は `∅` と `univ` だけなので、どちらの場合も矛盾する。
-- （ここに theorem を書く）

/-! ## Part 5（さらに発展）: 位相空間の別定義と等価性

`TopologicalSpace`（開集合系）は位相の唯一の定義ではない。この Part では

* A: **閉集合系**（`ClosedTopology`）
* B: **Kuratowski の閉包作用素**（`KuratowskiClosure`）
* C: **近傍系**（`NeighborhoodSystem`）
* D: **ネット**による閉集合の特徴づけ（こちらは公理化ではなく特徴づけ）

を形式化し、A〜C が開集合系と**等価**であることを、Part 3 で作った `Cat.Equiv` を
「構造どうしの全単射」として使って示す。

等価性の証明には「同じ `IsOpen` を持つ2つの `TopologicalSpace` は等しい」という
外延性補題が要る。証明フィールドは proof irrelevance により等しさに影響しないので、
述語フィールドの一致だけから構造全体の等しさが出る（下の `ext'`。この形の補題は
各構造に対して与えておく）。

この Part の `#check` は表示の注記を省く（読み方はこれまでと同じ）。
-/

/-- 集合族の共通部分。`sUnion` の双対。 -/
def Set.sInter {α : Type} (S : Set (Set α)) : Set α := {a | ∀ s ∈ S, a ∈ s}

/-- 前置記法 `⋂₀ S`。 -/
prefix:110 "⋂₀ " => Set.sInter

/-- 包含の反対称性。集合の等式を示す基本手段（以下で多用する）。 -/
lemma Set.subset_antisymm {α : Type} {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  Set.ext fun a => ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩

/-- 同じ `IsOpen` を持つ位相は等しい。`cases` で両者を分解すると、
述語の一致を代入した残りは証明フィールドだけになり、
proof irrelevance により `rfl` で閉じる。 -/
theorem TopologicalSpace.ext' {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : t₁.IsOpen = t₂.IsOpen) : t₁ = t₂ := by
  cases t₁; cases t₂; cases h; rfl

/-- 問題14: 補集合の基本法則を示せ（ド・モルガンを含む6本）。
`compl_inter` と `compl_sInter` には古典論理（`by_cases` か
`Classical.byContradiction`）が要る。どこで要るのか意識しながら書くこと。 -/
lemma Set.compl_univ {α : Type} : (Set.univ : Set α)ᶜ = ∅ := sorry

lemma Set.compl_empty {α : Type} : (∅ : Set α)ᶜ = Set.univ := sorry

lemma Set.compl_union {α : Type} (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := sorry

lemma Set.compl_inter {α : Type} (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := sorry

lemma Set.compl_sUnion {α : Type} (S : Set (Set α)) :
    (⋃₀ S)ᶜ = ⋂₀ (Set.compl '' S) := sorry

lemma Set.compl_sInter {α : Type} (S : Set (Set α)) :
    (⋂₀ S)ᶜ = ⋃₀ (Set.compl '' S) := sorry

/-! ### A: 閉集合系 -/

/-- 閉集合系による位相の公理化。開集合系の公理の双対になっている。 -/
structure ClosedTopology (X : Type) where
  /-- その集合が閉集合であるという述語。 -/
  IsClosed (s : Set X) : Prop
  /-- 空集合は閉。 -/
  isClosed_empty : IsClosed ∅
  /-- 2つの閉集合の合併は閉。 -/
  isClosed_union (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t)
  /-- 閉集合をいくつ集めて共通部分を取っても閉。 -/
  isClosed_sInter (S : Set (Set X)) (h : ∀ s ∈ S, IsClosed s) : IsClosed (⋂₀ S)

theorem ClosedTopology.ext' {X : Type} {c₁ c₂ : ClosedTopology X}
    (h : c₁.IsClosed = c₂.IsClosed) : c₁ = c₂ := by
  cases c₁; cases c₂; cases h; rfl

/-- 問題15: 閉集合系から開集合系を作れ（開 = 補集合が閉）。問題14を使う。 -/
@[reducible] def ClosedTopology.toTop {X : Type} (c : ClosedTopology X) : TopologicalSpace X where
  IsOpen s := c.IsClosed sᶜ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 問題16: 開集合系から閉集合系を作れ（閉 = 補集合が開）。 -/
def TopologicalSpace.toClosed {X : Type} (t : TopologicalSpace X) : ClosedTopology X where
  IsClosed s := t.IsOpen sᶜ
  isClosed_empty := sorry
  isClosed_union := sorry
  isClosed_sInter := sorry

/-- 問題17: 往復が恒等であることを示し、`Cat.Equiv` にまとめよ。
ヒント: `ext'` → `funext` → `show` で二重補集合の形に読み替えて `compl_compl`。 -/
theorem toTop_toClosed {X : Type} (t : TopologicalSpace X) : t.toClosed.toTop = t := sorry

theorem toClosed_toTop {X : Type} (c : ClosedTopology X) : c.toTop.toClosed = c := sorry

def topEquivClosed (X : Type) : Cat.Equiv (TopologicalSpace X) (ClosedTopology X) := sorry

/-! ### B: Kuratowski の閉包作用素 -/

/-- Kuratowski の閉包公理。「閉包」の振る舞いだけで位相を決める。 -/
structure KuratowskiClosure (X : Type) where
  /-- 閉包作用素。 -/
  cl (s : Set X) : Set X
  /-- 空集合の閉包は空。 -/
  cl_empty : cl ∅ = ∅
  /-- 拡大性: もとの集合を含む。 -/
  subset_cl (s : Set X) : s ⊆ cl s
  /-- 有限合併の保存。 -/
  cl_union (s t : Set X) : cl (s ∪ t) = cl s ∪ cl t
  /-- 冪等性: 2回閉包しても変わらない。 -/
  cl_cl (s : Set X) : cl (cl s) = cl s

theorem KuratowskiClosure.ext' {X : Type} {k₁ k₂ : KuratowskiClosure X}
    (h : k₁.cl = k₂.cl) : k₁ = k₂ := by
  cases k₁; cases k₂; cases h; rfl

/-- 位相から定める閉包: `s` を含む閉集合すべての共通部分。 -/
def TopologicalSpace.closure {X : Type} (t : TopologicalSpace X) (s : Set X) : Set X :=
  ⋂₀ {u | t.IsOpen uᶜ ∧ s ⊆ u}

/-- 問題18: 閉包の基本性質4本を示せ。
`closure_isClosed` には問題14の `compl_sInter` が要る。 -/
lemma TopologicalSpace.subset_closure {X : Type} (t : TopologicalSpace X) (s : Set X) :
    s ⊆ t.closure s := sorry

lemma TopologicalSpace.closure_min {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (hu : t.IsOpen uᶜ) (hsu : s ⊆ u) : t.closure s ⊆ u := sorry

lemma TopologicalSpace.closure_isClosed {X : Type} (t : TopologicalSpace X) (s : Set X) :
    t.IsOpen (t.closure s)ᶜ := sorry

lemma TopologicalSpace.closure_mono {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (h : s ⊆ u) : t.closure s ⊆ t.closure u := sorry

/-- 問題19: 閉包公理から単調性を導け。使ってよいのは `cl_union` だけ。
ヒント: `s ⊆ t` なら `s ∪ t = t`。 -/
lemma KuratowskiClosure.mono {X : Type} (k : KuratowskiClosure X) {s t : Set X}
    (h : s ⊆ t) : k.cl s ⊆ k.cl t := sorry

/-- 問題20: 閉包作用素から開集合系を作れ（開 = 補集合が `cl` の不動点）。
`isOpen_sUnion` が山場: `subset_antisymm` と `mono` を使う。 -/
@[reducible] def KuratowskiClosure.toTop {X : Type} (k : KuratowskiClosure X) : TopologicalSpace X where
  IsOpen s := k.cl sᶜ = sᶜ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 問題21: 位相から閉包作用素を作れ。問題18の4本を使う。 -/
def TopologicalSpace.toKur {X : Type} (t : TopologicalSpace X) : KuratowskiClosure X where
  cl := t.closure
  cl_empty := sorry
  subset_cl := sorry
  cl_union := sorry
  cl_cl := sorry

/-- 問題22: 往復が恒等であることを示し、`Cat.Equiv` にまとめよ。 -/
theorem toKur_toTop {X : Type} (t : TopologicalSpace X) : t.toKur.toTop = t := sorry

theorem toTop_toKur {X : Type} (k : KuratowskiClosure X) : k.toTop.toKur = k := sorry

def topEquivKur (X : Type) : Cat.Equiv (TopologicalSpace X) (KuratowskiClosure X) := sorry

/-! ### C: 近傍系 -/

/-- 近傍系による位相の公理化（ハウスドルフ流）。 -/
structure NeighborhoodSystem (X : Type) where
  /-- 各点に、その「近傍」の族を割り当てる。 -/
  N (x : X) : Set (Set X)
  /-- 全体集合はどの点の近傍でもある。 -/
  univ_mem (x : X) : Set.univ ∈ N x
  /-- 近傍はその点を含む。 -/
  mem_of (x : X) (U : Set X) (h : U ∈ N x) : x ∈ U
  /-- 近傍を含む集合は近傍。 -/
  superset (x : X) (U V : Set X) (hU : U ∈ N x) (hUV : U ⊆ V) : V ∈ N x
  /-- 2つの近傍の共通部分は近傍。 -/
  inter (x : X) (U V : Set X) (hU : U ∈ N x) (hV : V ∈ N x) : U ∩ V ∈ N x
  /-- 近傍 `U` の中には「その各点にとっても `U` が近傍」となる近傍 `V` がある。 -/
  interior (x : X) (U : Set X) (h : U ∈ N x) : ∃ V ∈ N x, ∀ y ∈ V, U ∈ N y

theorem NeighborhoodSystem.ext' {X : Type} {n₁ n₂ : NeighborhoodSystem X}
    (h : n₁.N = n₂.N) : n₁ = n₂ := by
  cases n₁; cases n₂; cases h; rfl

/-- 問題23: 近傍系から開集合系を作れ（開 = 自分の各点の近傍である集合）。 -/
@[reducible] def NeighborhoodSystem.toTop {X : Type} (n : NeighborhoodSystem X) : TopologicalSpace X where
  IsOpen s := ∀ x ∈ s, s ∈ n.N x
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 問題24: 開集合系から近傍系を作れ（近傍 = 開集合を間に挟んで点を含む集合）。 -/
def TopologicalSpace.toNbhd {X : Type} (t : TopologicalSpace X) : NeighborhoodSystem X where
  N x := {U | ∃ V, t.IsOpen V ∧ x ∈ V ∧ V ⊆ U}
  univ_mem := sorry
  mem_of := sorry
  superset := sorry
  inter := sorry
  interior := sorry

/-- 問題25: 往復が恒等であることを示し、`Cat.Equiv` にまとめよ。
片方は `Top.lean` の `isOpen_of_nhds` がそのまま効く。
もう片方の鍵は `W := {y | U ∈ N y}` が開になること（`interior` 公理を使う）。 -/
theorem toNbhd_toTop {X : Type} (t : TopologicalSpace X) : t.toNbhd.toTop = t := sorry

theorem toTop_toNbhd {X : Type} (n : NeighborhoodSystem X) : n.toTop.toNbhd = n := sorry

def topEquivNbhd (X : Type) : Cat.Equiv (TopologicalSpace X) (NeighborhoodSystem X) := sorry

/-! ### D: ネットによる閉集合の特徴づけ -/

/-- 有向な添字: 空でなく、どの2元にも上界がある。 -/
structure DirectedIndex : Type 1 where
  /-- 添字の型。 -/
  ι : Type
  /-- 「後」の関係。 -/
  le : ι → ι → Prop
  /-- 空でない。 -/
  inhabited : Nonempty ι
  /-- どの2元にも共通の「後」がある。 -/
  upper (i j : ι) : ∃ k, le i k ∧ le j k

/-- ネット `net : D.ι → X` が点 `a` に収束する:
`a` のどの開近傍にも、ある添字から先はすべて入る。 -/
def Converges {X : Type} (t : TopologicalSpace X) (D : DirectedIndex)
    (net : D.ι → X) (a : X) : Prop :=
  ∀ U, t.IsOpen U → a ∈ U → ∃ d, ∀ e, D.le d e → net e ∈ U

/-- 問題26: 閉集合の中のネットの極限は、その閉集合に入ることを示せ。
ヒント: `upper d d` で「d 以後」の添字を1つ取る。 -/
theorem nets_of_isClosed {X : Type} (t : TopologicalSpace X) {s : Set X}
    (hs : t.IsOpen sᶜ) (D : DirectedIndex) (net : D.ι → X)
    (hnet : ∀ e, net e ∈ s) {a : X} (hconv : Converges t D net a) : a ∈ s := sorry

/-- 問題27: 逆——中のネットの極限で閉じている集合は閉であることを示せ。

方針: `isOpen_of_nhds` に持ち込む。`a ∈ sᶜ` の開近傍が取れないと仮定すると、
`a` の**どの**開近傍も `s` と交わる。そこで添字型を
「`a` の開近傍の全体」（部分型）とし、包含の逆向きで有向にして、
各近傍から `s` の点を `Classical.choose` で**選んで**ネットを作ると、
それは `a` に収束し、仮定から `a ∈ s` となって矛盾する。
`Top.lean` の補題2（選択を避けた）と対照的に、ここでは選択が本質的に要る。
できたら `#print axioms` で確認せよ。 -/
theorem isClosed_of_nets {X : Type} (t : TopologicalSpace X) {s : Set X}
    (h : ∀ (D : DirectedIndex) (net : D.ι → X), (∀ e, net e ∈ s) →
         ∀ a, Converges t D net a → a ∈ s) :
    t.IsOpen sᶜ := sorry
