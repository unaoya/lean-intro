-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import Top

-- # 発展演習: 位相空間の圏と自由忘却随伴

-- ## Part 1: 密着位相

@[reducible] def indiscrete (X : Type) : TopologicalSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

#check indiscrete
-- 表示: `indiscrete (X : Type) : TopologicalSpace X`
-- 読み: `discrete` と同じ形——型を受け取って位相そのものを返す関数。

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

theorem continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
    @Continuous X tX Y (indiscrete Y) f :=
  sorry

#check continuous_to_indiscrete
-- 表示: `continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
--        Continuous f`
-- 読み: 同様に、実際の主張は `@Continuous X tX Y (indiscrete Y) f`（`Y` 側が密着位相）。

-- 問題4（主張も自分で書く）:
-- 「密着位相を入れた `Bool` はハウスドルフでない」を形式化し、証明せよ。
-- ヒント: 否定 `¬p` は `p → False`（[`CH2.lean` 3節](#sec-CH.empty-types)）。
-- `true` と `false` を分離する開集合の組が取れたとして、矛盾を導く。
-- （ここに theorem を書く）

-- ## Part 2: 圏と関手

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
-- [`Intro1a.lean` 1節](#sec-Intro1.terms-types)の宇宙の階段（`Type : Type 1 : Type 2`）が実際に必要になる場面である。

@[reducible] def TypeCat : Category :=
  sorry

#check TypeCat
-- 表示: `Cat.TypeCat : Category`
-- 読み: 「圏」という型の項が1つ手に入った。

structure TopSpace : Type 1 where
  /-- 台の型。 -/
  carrier : Type
  /-- 台の上の位相。 -/
  str : TopologicalSpace carrier

#check TopSpace
-- 表示: `Cat.TopSpace : Type 1`
-- 読み: 台の型（`Type` の項）をフィールドに含むので、`Type` でなく `Type 1` に住む。

attribute [instance] TopSpace.str

@[reducible] def TopCat : Category :=
  sorry

#check TopCat
-- 表示: `Cat.TopCat : Category`

-- ### 関手

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

@[reducible] def forgetful : Functor TopCat TypeCat :=
  sorry

#check forgetful
-- 表示: `Cat.forgetful : Functor TopCat TypeCat`

@[reducible] def discreteFunctor : Functor TypeCat TopCat :=
  sorry

#check discreteFunctor
-- 表示: `Cat.discreteFunctor : Functor TypeCat TopCat`

@[reducible] def indiscreteFunctor : Functor TypeCat TopCat :=
  sorry

#check indiscreteFunctor
-- 表示: `Cat.indiscreteFunctor : Functor TypeCat TopCat`

-- ## Part 3: 随伴

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

def discreteAdj : Adjunction discreteFunctor forgetful :=
  sorry

#check discreteAdj
-- 表示: `Cat.discreteAdj : Adjunction discreteFunctor forgetful`
-- 読み: 型がそのまま「離散 ⊣ 忘却」と読める。

def indiscreteAdj : Adjunction forgetful indiscreteFunctor :=
  sorry

#check indiscreteAdj
-- 表示: `Cat.indiscreteAdj : Adjunction forgetful indiscreteFunctor`
-- 読み: こちらは「忘却 ⊣ 密着」。合わせて 離散 ⊣ 忘却 ⊣ 密着。

end Cat

-- ## Part 4（発展）: 反例 — 主定理の仮定は外せない

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

-- ## Part 5（さらに発展）: 位相空間の別定義と等価性

def Set.sInter {α : Type} (S : Set (Set α)) : Set α := {a | ∀ s ∈ S, a ∈ s}

prefix:110 "⋂₀ " => Set.sInter

theorem Set.subset_antisymm {α : Type} {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  Set.ext fun a => ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩

theorem TopologicalSpace.ext' {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : t₁.IsOpen = t₂.IsOpen) : t₁ = t₂ := by
  cases t₁; cases t₂; cases h; rfl

theorem Set.compl_univ {α : Type} : (Set.univ : Set α)ᶜ = ∅ := sorry

theorem Set.compl_empty {α : Type} : (∅ : Set α)ᶜ = Set.univ := sorry

theorem Set.compl_union {α : Type} (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := sorry

theorem Set.compl_inter {α : Type} (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := sorry

theorem Set.compl_sUnion {α : Type} (S : Set (Set α)) :
    (⋃₀ S)ᶜ = ⋂₀ (Set.compl '' S) := sorry

theorem Set.compl_sInter {α : Type} (S : Set (Set α)) :
    (⋂₀ S)ᶜ = ⋃₀ (Set.compl '' S) := sorry

-- ### A: 閉集合系

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

@[reducible] def ClosedTopology.toTop {X : Type} (c : ClosedTopology X) : TopologicalSpace X where
  IsOpen s := c.IsClosed sᶜ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

def TopologicalSpace.toClosed {X : Type} (t : TopologicalSpace X) : ClosedTopology X where
  IsClosed s := t.IsOpen sᶜ
  isClosed_empty := sorry
  isClosed_union := sorry
  isClosed_sInter := sorry

theorem toTop_toClosed {X : Type} (t : TopologicalSpace X) : t.toClosed.toTop = t := sorry

theorem toClosed_toTop {X : Type} (c : ClosedTopology X) : c.toTop.toClosed = c := sorry

def topEquivClosed (X : Type) : Cat.Equiv (TopologicalSpace X) (ClosedTopology X) := sorry

-- ### B: Kuratowski の閉包作用素

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

def TopologicalSpace.closure {X : Type} (t : TopologicalSpace X) (s : Set X) : Set X :=
  ⋂₀ {u | t.IsOpen uᶜ ∧ s ⊆ u}

theorem TopologicalSpace.subset_closure {X : Type} (t : TopologicalSpace X) (s : Set X) :
    s ⊆ t.closure s := sorry

theorem TopologicalSpace.closure_min {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (hu : t.IsOpen uᶜ) (hsu : s ⊆ u) : t.closure s ⊆ u := sorry

theorem TopologicalSpace.closure_isClosed {X : Type} (t : TopologicalSpace X) (s : Set X) :
    t.IsOpen (t.closure s)ᶜ := sorry

theorem TopologicalSpace.closure_mono {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (h : s ⊆ u) : t.closure s ⊆ t.closure u := sorry

theorem KuratowskiClosure.mono {X : Type} (k : KuratowskiClosure X) {s t : Set X}
    (h : s ⊆ t) : k.cl s ⊆ k.cl t := sorry

@[reducible] def KuratowskiClosure.toTop {X : Type} (k : KuratowskiClosure X) : TopologicalSpace X where
  IsOpen s := k.cl sᶜ = sᶜ
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

def TopologicalSpace.toKur {X : Type} (t : TopologicalSpace X) : KuratowskiClosure X where
  cl := t.closure
  cl_empty := sorry
  subset_cl := sorry
  cl_union := sorry
  cl_cl := sorry

theorem toKur_toTop {X : Type} (t : TopologicalSpace X) : t.toKur.toTop = t := sorry

theorem toTop_toKur {X : Type} (k : KuratowskiClosure X) : k.toTop.toKur = k := sorry

def topEquivKur (X : Type) : Cat.Equiv (TopologicalSpace X) (KuratowskiClosure X) := sorry

-- ### C: 近傍系

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

@[reducible] def NeighborhoodSystem.toTop {X : Type} (n : NeighborhoodSystem X) : TopologicalSpace X where
  IsOpen s := ∀ x ∈ s, s ∈ n.N x
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

def TopologicalSpace.toNbhd {X : Type} (t : TopologicalSpace X) : NeighborhoodSystem X where
  N x := {U | ∃ V, t.IsOpen V ∧ x ∈ V ∧ V ⊆ U}
  univ_mem := sorry
  mem_of := sorry
  superset := sorry
  inter := sorry
  interior := sorry

theorem toNbhd_toTop {X : Type} (t : TopologicalSpace X) : t.toNbhd.toTop = t := sorry

theorem toTop_toNbhd {X : Type} (n : NeighborhoodSystem X) : n.toTop.toNbhd = n := sorry

def topEquivNbhd (X : Type) : Cat.Equiv (TopologicalSpace X) (NeighborhoodSystem X) := sorry

-- ### D: ネットによる閉集合の特徴づけ

structure DirectedIndex : Type 1 where
  /-- 添字の型。 -/
  ι : Type
  /-- 「後」の関係。 -/
  le : ι → ι → Prop
  /-- 空でない。 -/
  inhabited : Nonempty ι
  /-- どの2元にも共通の「後」がある。 -/
  upper (i j : ι) : ∃ k, le i k ∧ le j k

def Converges {X : Type} (t : TopologicalSpace X) (D : DirectedIndex)
    (net : D.ι → X) (a : X) : Prop :=
  ∀ U, t.IsOpen U → a ∈ U → ∃ d, ∀ e, D.le d e → net e ∈ U

theorem nets_of_isClosed {X : Type} (t : TopologicalSpace X) {s : Set X}
    (hs : t.IsOpen sᶜ) (D : DirectedIndex) (net : D.ι → X)
    (hnet : ∀ e, net e ∈ s) {a : X} (hconv : Converges t D net a) : a ∈ s := sorry

theorem isClosed_of_nets {X : Type} (t : TopologicalSpace X) {s : Set X}
    (h : ∀ (D : DirectedIndex) (net : D.ι → X), (∀ e, net e ∈ s) →
         ∀ a, Converges t D net a → a ∈ s) :
    t.IsOpen sᶜ := sorry

-- ## Part 6: 誘導位相 — 位相を写像に沿って移す

example {α β : Type} (f : α → β) : f ⁻¹' (Set.univ : Set β) = Set.univ := rfl

example {α β : Type} (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := rfl

theorem Set.preimage_sUnion {α β : Type} (f : α → β) (S : Set (Set β)) :
    f ⁻¹' (⋃₀ S) = ⋃₀ (Set.preimage f '' S) := sorry

@[reducible] def TopologicalSpace.coinduced {X Y : Type} (tX : TopologicalSpace X)
    (f : X → Y) : TopologicalSpace Y where
  IsOpen s := tX.IsOpen (f ⁻¹' s)
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

#check TopologicalSpace.coinduced
-- 表示: `TopologicalSpace.coinduced {X Y : Type} (tX : TopologicalSpace X) (f : X → Y) :
--        TopologicalSpace Y`
-- 読み: 位相と写像を受け取り、行き先の上の位相を返す。`tX.coinduced f` と
-- ドット記法で使う。

@[reducible] def finalTopology {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X) :
    TopologicalSpace X where
  IsOpen s := ∀ i, (tY i).IsOpen (f i ⁻¹' s)
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

#check finalTopology
-- 表示: `finalTopology {I : Type} {Y : I → Type} {X : Type}
--        (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X) :
--        TopologicalSpace X`

-- ### 引き戻しの困難と、上からの定義

@[reducible] def initialTopology {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i) :
    TopologicalSpace X where
  IsOpen s := ∀ t' : TopologicalSpace X,
    (∀ i u, (tY i).IsOpen u → t'.IsOpen (f i ⁻¹' u)) → t'.IsOpen s
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

#check initialTopology
-- 表示: `initialTopology {I : Type} {Y : I → Type} {X : Type}
--        (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i) :
--        TopologicalSpace X`
-- 読み: `finalTopology` と見比べると、族の向きが `Y i → X` から `X → Y i` に
-- 反転している。それだけで定義の中身はこれほど変わる。

-- ### 定義の確認: 連続性と極値性

theorem continuous_toFinal {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X) (i : I) :
    @Continuous (Y i) (tY i) X (finalTopology tY f) (f i) := sorry

theorem final_finest {I : Type} {Y : I → Type} {X : Type}
    {tY : (i : I) → TopologicalSpace (Y i)} {f : (i : I) → Y i → X}
    {t' : TopologicalSpace X} (h : ∀ i, @Continuous (Y i) (tY i) X t' (f i)) :
    ∀ s, t'.IsOpen s → (finalTopology tY f).IsOpen s := sorry

theorem continuous_fromInitial {I : Type} {Y : I → Type} {X : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i) (i : I) :
    @Continuous X (initialTopology tY f) (Y i) (tY i) (f i) := sorry

theorem initial_coarsest {I : Type} {Y : I → Type} {X : Type}
    {tY : (i : I) → TopologicalSpace (Y i)} {f : (i : I) → X → Y i}
    {t' : TopologicalSpace X} (h : ∀ i, @Continuous X t' (Y i) (tY i) (f i)) :
    ∀ s, (initialTopology tY f).IsOpen s → t'.IsOpen s := sorry

-- ### 普遍性

theorem continuous_fromCoinduced_iff {X Y Z : Type} (tX : TopologicalSpace X)
    (tZ : TopologicalSpace Z) (f : X → Y) (g : Y → Z) :
    @Continuous Y (tX.coinduced f) Z tZ g ↔ @Continuous X tX Z tZ (fun x => g (f x)) :=
  sorry

theorem continuous_fromFinal_iff {I : Type} {Y : I → Type} {X Z : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → Y i → X)
    (tZ : TopologicalSpace Z) (g : X → Z) :
    @Continuous X (finalTopology tY f) Z tZ g ↔
      ∀ i, @Continuous (Y i) (tY i) Z tZ (fun y => g (f i y)) := sorry

theorem continuous_toInitial_iff {I : Type} {Y : I → Type} {X Z : Type}
    (tY : (i : I) → TopologicalSpace (Y i)) (f : (i : I) → X → Y i)
    (tZ : TopologicalSpace Z) (g : Z → X) :
    @Continuous Z tZ X (initialTopology tY f) g ↔
      ∀ i, @Continuous Z tZ (Y i) (tY i) (fun z => f i (g z)) := sorry

-- ### 部分空間・積・直和・商

@[reducible] def TopologicalSpace.induced {X Y : Type} (f : X → Y)
    (t : TopologicalSpace Y) : TopologicalSpace X :=
  initialTopology (Y := fun _ : Unit => Y) (fun _ => t) (fun _ => f)

instance instTopSubtype {X : Type} [tX : TopologicalSpace X] (p : X → Prop) :
    TopologicalSpace (Subtype p) :=
  tX.induced Subtype.val

instance instTopPi {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : I) → Y i) :=
  initialTopology tY fun i g => g i

instance instTopProd {X Y : Type} [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  initialTopology (Y := fun b => cond b X Y)
    (fun b => match b with | true => t₁ | false => t₂)
    (fun b => match b with | true => Prod.fst | false => Prod.snd)

instance instTopSigma {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : I) × Y i) :=
  finalTopology tY fun i => Sigma.mk i

instance instTopQuot {X : Type} [tX : TopologicalSpace X] {r : X → X → Prop} :
    TopologicalSpace (Quot r) :=
  tX.coinduced (Quot.mk r)

-- 定義の確認: 直和への包含は連続（問題32(1)の特殊化がそのまま通る）
example {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)] (i : I) :
    Continuous (Sigma.mk i : Y i → (j : I) × Y j) :=
  continuous_toFinal tY (fun i => Sigma.mk i) i

-- 定義の確認: 二項積の第一射影は連続（問題33(1)を `i := true` で使う。
-- 族を明示して渡すと、`match` が `true` の枝に簡約されて `Prod.fst` になる）
example {X Y : Type} [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    Continuous (@Prod.fst X Y) :=
  continuous_fromInitial (Y := fun b => cond b X Y)
    (fun b => match b with | true => t₁ | false => t₂)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) true

theorem isOpen_subtype_iff {X : Type} [tX : TopologicalSpace X] {p : X → Prop}
    {s : Set (Subtype p)} :
    IsOpen s ↔ ∃ u, IsOpen u ∧ s = Subtype.val ⁻¹' u := sorry

theorem continuous_apply {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)]
    (i : I) : Continuous fun g : (j : I) → Y j => g i := sorry

theorem continuous_pi_iff {I : Type} {Y : I → Type} [tY : (i : I) → TopologicalSpace (Y i)]
    {Z : Type} [tZ : TopologicalSpace Z] (g : Z → (i : I) → Y i) :
    Continuous g ↔ ∀ i, Continuous fun z => g z i := sorry

theorem continuous_quotMk {X : Type} [tX : TopologicalSpace X] (r : X → X → Prop) :
    Continuous (Quot.mk r) := sorry

theorem continuous_quotLift {X Z : Type} [tX : TopologicalSpace X] [tZ : TopologicalSpace Z]
    {r : X → X → Prop} {g : X → Z} (hg : ∀ a b, r a b → g a = g b) :
    Continuous (Quot.lift g hg) ↔ Continuous g := sorry

theorem initialTopology_empty {X : Type} {Y : Empty → Type}
    (tY : (i : Empty) → TopologicalSpace (Y i)) (f : (i : Empty) → X → Y i) :
    initialTopology tY f = indiscrete X := sorry

theorem finalTopology_empty {X : Type} {Y : Empty → Type}
    (tY : (i : Empty) → TopologicalSpace (Y i)) (f : (i : Empty) → Y i → X) :
    finalTopology tY f = discrete X := sorry

-- ### 商写像 — 主定理の再訪

theorem Set.image_preimage_of_surjective {α β : Type} {f : α → β}
    (hf : Function.Surjective f) (u : Set β) : f '' (f ⁻¹' u) = u := sorry

theorem coinduced_eq_of_surjective {X Y : Type}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    tX.coinduced f = tY := sorry

example {X Y : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [CompactSpace X] [Hausdorff Y] {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g := sorry

-- できたら確認: 問題41は Classical.choice に依存する（補題2・3の by_cases 経由）が、
-- 主定理と違って Classical.choose による「構成」はない
-- #print axioms coinduced_eq_of_surjective
