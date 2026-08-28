import Top

/-! # 発展演習: 位相空間の圏と自由忘却随伴

`Top.lean` まで読み終えた人のための演習問題。題材は次の3つ。

* 密着位相・離散位相と、その普遍性
* 位相空間の圏と、離散・密着・忘却の3つの関手
* 自由忘却随伴 「離散 ⊣ 忘却 ⊣ 密着」

最後に、これらを使って **`Top.lean` の主定理のハウスドルフという仮定が
外せないこと**を反例で確かめる。

## 進め方

* `sorry` と書かれた場所を自分の証明・構成で置き換える。
  `sorry` が残っているとビルド時に警告が出るので、消えたら完成。
* 「主張も自分で書く」問題は、コメントの指示に従って宣言ごと自分で書く。
* 構造の定義（`Category` など）は与えてある。ただし `Functor` のように
  「まず自分で設計してから見比べよ」とある定義は、先に紙に書いてみることを勧める。
* 解答は `ExtraSol.lean` にある。

## 記法の補足

`Top.lean` の `Continuous` は位相をインスタンス引数で受け取るので、
1つの型に別の位相を載せて論じるには `@` で位相を明示する。例えば
`@Continuous X (discrete X) Y tY f` は「`X` に離散位相を入れたとき `f` は連続」。
-/

universe u

/-! ## Part 1: 密着位相

離散位相（`Top.lean` の `discrete`、すべての部分集合が開）の対極として、
開集合が `∅` と `univ` しかない位相を**密着位相**という。
-/

/-- 問題1: 密着位相が位相の3公理を満たすことを示せ。

ヒント: `isOpen_sUnion` では「`S` のどれかが `univ` か、全部 `∅` か」で
場合分けする（`by_cases`）。 -/
@[reducible] def indiscrete (X : Type u) : TopologicalSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 問題2: 離散位相からの写像はすべて連続であることを示せ。

離散位相では何もかも開なので、逆像の開性はただで手に入る。 -/
theorem continuous_from_discrete {X Y : Type u} [tY : TopologicalSpace Y] (f : X → Y) :
    @Continuous X (discrete X) Y tY f :=
  sorry

/-- 問題3: 密着位相への写像はすべて連続であることを示せ。

ヒント: 逆像を取る前に開集合は `∅` か `univ` しかない。
`f ⁻¹' ∅` と `f ⁻¹' Set.univ` は定義上それぞれ `∅` と `univ` に等しい。 -/
theorem continuous_to_indiscrete {X Y : Type u} [tX : TopologicalSpace X] (f : X → Y) :
    @Continuous X tX Y (indiscrete Y) f :=
  sorry

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
  Obj : Type (u + 1)
  Hom : Obj → Obj → Type u
  id : (A : Obj) → Hom A A
  /-- 合成は図式順: `comp f g` は「`f` してから `g`」。 -/
  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
  id_comp : ∀ {A B : Obj} (f : Hom A B), comp (id A) f = f
  comp_id : ∀ {A B : Obj} (f : Hom A B), comp f (id B) = f
  assoc : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp (comp f g) h = comp f (comp g h)

/-- 問題5: 型の圏を作れ。対象は型、射は関数。

法則の証明はすべて `rfl` で済むはず。なぜ済むのかも考えてみること
（関数の合成は定義上結合的である）。 -/
@[reducible] def TypeCat : Category.{u} :=
  sorry

/-- 位相空間の圏の対象: 台の型と、その上の位相を束ねたもの。

`attribute [instance] TopSpace.str` としておくと、`A : TopSpace` に対して
`A.carrier` 上の位相が自動で見つかるようになり、`Continuous f` とだけ書ける。 -/
structure TopSpace : Type (u + 1) where
  carrier : Type u
  str : TopologicalSpace carrier

attribute [instance] TopSpace.str

/-- 問題6: 位相空間の圏を作れ。対象は `TopSpace`、
射は「関数と、その連続性の証明の組」`{ f : A.carrier → B.carrier // Continuous f }`。

これは `CH.lean` 6節の依存和そのもの（`Subtype`）である。
ヒント: 恒等射は `continuous_id`、合成は `Continuous.comp`。
射の等しさは `Subtype.ext`（第一成分が等しければ等しい）で示す。 -/
@[reducible] def TopCat : Category.{u} :=
  sorry

/-! ### 関手

圏から圏への「構造を保つ対応」。対象の対応 `obj` と射の対応 `map` からなり、
恒等射と合成を保つ。まず自分でこの structure を設計してから、下と見比べよ。
-/

structure Functor (C D : Category.{u}) where
  obj : C.Obj → D.Obj
  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)
  map_id : ∀ A : C.Obj, map (C.id A) = D.id (obj A)
  map_comp : ∀ {A B E : C.Obj} (f : C.Hom A B) (g : C.Hom B E),
    map (C.comp f g) = D.comp (map f) (map g)

/-- 問題7: 忘却関手 `U : Top → Type` を作れ。位相を忘れて台の型だけを残す。 -/
@[reducible] def forgetful : Functor TopCat.{u} TypeCat.{u} :=
  sorry

/-- 問題8: 離散関手 `D : Type → Top` を作れ。型に離散位相を載せる。
射の行き先（任意の写像が連続になること）は問題2で作った。

ヒント: 行き先の位相はインスタンス探索では見つからないので、
`continuous_from_discrete (tY := discrete _) f` のように名前付き引数で明示する。 -/
@[reducible] def discreteFunctor : Functor TypeCat.{u} TopCat.{u} :=
  sorry

/-- 問題9: 密着関手 `I : Type → Top` を作れ。型に密着位相を載せる。
射の行き先は問題3で作った。 -/
@[reducible] def indiscreteFunctor : Functor TypeCat.{u} TopCat.{u} :=
  sorry

/-! ## Part 3: 随伴

関手 `F : C → D` と `G : D → C` が随伴 `F ⊣ G` であるとは、
hom 集合の間に自然な全単射

    Hom_D(F A, B) ≃ Hom_C(A, G B)

があること。全単射は `Top.lean` の `Homeomorph` と同じ形の structure で表す。
「自然」の意味は `Adjunction` の2つの等式（`f` を前に合成してから対応させても、
対応させてから合成しても同じ、およびその `h` 版）。
-/

structure Equiv (α β : Type u) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

structure Adjunction {C D : Category.{u}} (F : Functor C D) (G : Functor D C) where
  homEquiv : (A : C.Obj) → (B : D.Obj) → Equiv (D.Hom (F.obj A) B) (C.Hom A (G.obj B))
  naturality_left :
    ∀ {A' A : C.Obj} {B : D.Obj} (f : C.Hom A' A) (g : D.Hom (F.obj A) B),
      (homEquiv A' B).toFun (D.comp (F.map f) g) = C.comp f ((homEquiv A B).toFun g)
  naturality_right :
    ∀ {A : C.Obj} {B B' : D.Obj} (g : D.Hom (F.obj A) B) (h : D.Hom B B'),
      (homEquiv A B').toFun (D.comp g h) = C.comp ((homEquiv A B).toFun g) (G.map h)

/-- 問題10: 随伴「離散 ⊣ 忘却」を作れ。

`Hom_Top(D X, A) ≃ Hom_Type(X, U A)`: 左辺の射は「連続な写像」、
右辺の射は「ただの写像」だが、離散位相からはどんな写像も連続（問題2）なので、
この対応の実体は「同じ関数を右へ左へ読み替えるだけ」である。
自然性も含め、ほとんどの証明が `rfl` か `Subtype.ext rfl` で済むはず。 -/
def discreteAdj : Adjunction discreteFunctor.{u} forgetful.{u} :=
  sorry

/-- 問題11: 随伴「忘却 ⊣ 密着」を作れ。問題10と対称的。

これで 離散 ⊣ 忘却 ⊣ 密着 という3連随伴ができたことになる。
離散位相が「もっとも細かい位相」、密着位相が「もっとも粗い位相」であることの
圏論的な言い換えである。 -/
def indiscreteAdj : Adjunction forgetful.{u} indiscreteFunctor.{u} :=
  sorry

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
