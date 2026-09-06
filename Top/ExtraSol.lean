import Top

/-! # 発展演習の解答

`Extra.lean` の全問題の解答。問題文と説明はそちらを参照。
各宣言の直後の `#check` の注記は `Top.lean` と同じ流儀。
-/

/-! ## Part 1: 密着位相 -/

/-- 問題1: 密着位相。開集合は `∅` と `univ` だけ。 -/
@[reducible] def indiscrete (X : Type) : TopologicalSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := by
    intro s t hs ht
    cases hs with
    | inl h =>
      left
      rw [h]
      apply Set.ext
      intro a
      exact ⟨fun h' => h'.1, False.elim⟩
    | inr h =>
      cases ht with
      | inl h' =>
        left
        rw [h, h']
        apply Set.ext
        intro a
        exact ⟨fun h'' => h''.2, False.elim⟩
      | inr h' =>
        right
        rw [h, h']
        apply Set.ext
        intro a
        exact ⟨fun h'' => h''.1, fun h'' => ⟨h'', h''⟩⟩
  isOpen_sUnion := by
    intro S hS
    by_cases h : ∃ s ∈ S, s = Set.univ
    · right
      have ⟨s, hsS, hs⟩ := h
      apply Set.ext
      intro a
      constructor
      · intro _
        trivial
      · intro _
        refine ⟨s, hsS, ?_⟩
        rw [hs]
        trivial
    · left
      apply Set.ext
      intro a
      constructor
      · intro ⟨s, hsS, has⟩
        cases hS s hsS with
        | inl he => rw [he] at has; exact has
        | inr hu => exact absurd ⟨s, hsS, hu⟩ h
      · exact False.elim

#check indiscrete
-- 表示: `indiscrete (X : Type) : TopologicalSpace X`
-- 読み: `discrete` と同じ形——型を受け取って位相そのものを返す関数。

/-- 問題2: 離散位相からの写像はすべて連続。 -/
theorem continuous_from_discrete {X Y : Type} [tY : TopologicalSpace Y] (f : X → Y) :
    @Continuous X (discrete X) Y tY f :=
  fun _ _ => trivial

#check continuous_from_discrete
-- 表示: `continuous_from_discrete {X Y : Type} [tY : TopologicalSpace Y] (f : X → Y) :
--        Continuous f`
-- 読み: 表示では暗黙・インスタンス引数が省かれるので、結論がただの `Continuous f` に
-- 見える。実際の主張は `@Continuous X (discrete X) Y tY f` で、`X` 側が離散位相で
-- あることは表示からは読めない。`@` 付きの主張は `#check` の表示だけでは
-- 区別できないことに注意。

/-- 問題3: 密着位相への写像はすべて連続。 -/
theorem continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
    @Continuous X tX Y (indiscrete Y) f := by
  intro s hs
  cases hs with
  | inl h => rw [h]; exact isOpen_empty
  | inr h => rw [h]; exact isOpen_univ

#check continuous_to_indiscrete
-- 表示: `continuous_to_indiscrete {X Y : Type} [tX : TopologicalSpace X] (f : X → Y) :
--        Continuous f`
-- 読み: 同様に、実際の主張は `@Continuous X tX Y (indiscrete Y) f`（`Y` 側が密着位相）。

/-- 問題4: 2点以上の型に密着位相を入れるとハウスドルフでない。`Bool` で示す。 -/
theorem indiscrete_bool_not_hausdorff : ¬ @Hausdorff Bool (indiscrete Bool) := by
  intro h
  have ⟨U, V, _hU, hV, htU, hfV, hUV⟩ := h.separate true false (by decide)
  -- V は空でない開集合なので univ しかありえない
  have hVuniv : V = Set.univ := by
    cases hV with
    | inl he => rw [he] at hfV; exact False.elim hfV
    | inr hu => exact hu
  -- すると true も V に入ってしまい、U ∩ V = ∅ に反する
  have htV : (true : Bool) ∈ V := by rw [hVuniv]; trivial
  have hmem : (true : Bool) ∈ U ∩ V := ⟨htU, htV⟩
  rw [hUV] at hmem
  exact hmem

#check indiscrete_bool_not_hausdorff
-- 表示: `indiscrete_bool_not_hausdorff : ¬Hausdorff Bool`
-- 読み: どの位相の話か（`indiscrete Bool`）はインスタンス引数として表示から省かれている。

/-! ## Part 2: 圏と関手 -/

namespace Cat

/-- 圏。（この定義は問題ファイルで与えられている） -/
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

/-- 問題5: 型の圏。対象は型、射は関数。法則はすべて `rfl`。 -/
@[reducible] def TypeCat : Category where
  Obj := Type
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

#check TypeCat
-- 表示: `Cat.TypeCat : Category`
-- 読み: 「圏」という型の項が1つ手に入った。

/-- 台の型と位相を束ねたもの。（問題ファイルで与えられている） -/
structure TopSpace : Type 1 where
  /-- 台の型。 -/
  carrier : Type
  /-- 台の上の位相。 -/
  str : TopologicalSpace carrier

#check TopSpace
-- 表示: `Cat.TopSpace : Type 1`
-- 読み: 台の型（`Type` の項）をフィールドに含むので、`Type` でなく `Type 1` に住む。

attribute [instance] TopSpace.str

/-- 問題6: 位相空間の圏。射は連続写像、すなわち「関数と連続性の証明の組」。 -/
@[reducible] def TopCat : Category where
  Obj := TopSpace
  Hom A B := { f : A.carrier → B.carrier // Continuous f }
  id _ := ⟨fun a => a, continuous_id⟩
  comp f g := ⟨fun a => g.val (f.val a), g.property.comp f.property⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

#check TopCat
-- 表示: `Cat.TopCat : Category`

/-- 関手。（問題ファイルで与えられている） -/
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

/-- 問題7: 忘却関手。位相を忘れて台の型だけ残す。 -/
@[reducible] def forgetful : Functor TopCat TypeCat where
  obj A := A.carrier
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

#check forgetful
-- 表示: `Cat.forgetful : Functor TopCat TypeCat`

/-- 問題8: 離散関手。型に離散位相を載せる。射の行き先は問題2で作った。 -/
@[reducible] def discreteFunctor : Functor TypeCat TopCat where
  obj X := ⟨X, discrete X⟩
  -- 行き先の位相はインスタンス探索では見つからないので、名前付き引数で明示する
  map f := ⟨f, continuous_from_discrete (tY := discrete _) f⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

#check discreteFunctor
-- 表示: `Cat.discreteFunctor : Functor TypeCat TopCat`

/-- 問題9: 密着関手。型に密着位相を載せる。射の行き先は問題3で作った。 -/
@[reducible] def indiscreteFunctor : Functor TypeCat TopCat where
  obj X := ⟨X, indiscrete X⟩
  map f := ⟨f, continuous_to_indiscrete (tX := indiscrete _) f⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

#check indiscreteFunctor
-- 表示: `Cat.indiscreteFunctor : Functor TypeCat TopCat`

/-! ## Part 3: 随伴 -/

/-- 全単射。（問題ファイルで与えられている） -/
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

/-- 随伴 `F ⊣ G`。hom 集合の自然な全単射。（問題ファイルで与えられている） -/
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

/-- 問題10: 離散 ⊣ 忘却。
`Hom_Top(D X, A) ≃ Hom_Type(X, U A)` で、対応の実体は「同じ関数」。 -/
def discreteAdj : Adjunction discreteFunctor forgetful where
  homEquiv _ _ :=
    { toFun := fun f => f.val
      invFun := fun f => ⟨f, continuous_from_discrete f⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  naturality_left _ _ := rfl
  naturality_right _ _ := rfl

#check discreteAdj
-- 表示: `Cat.discreteAdj : Adjunction discreteFunctor forgetful`
-- 読み: 型がそのまま「離散 ⊣ 忘却」と読める。

/-- 問題11: 忘却 ⊣ 密着。合わせて 離散 ⊣ 忘却 ⊣ 密着 の3連随伴になる。 -/
def indiscreteAdj : Adjunction forgetful indiscreteFunctor where
  homEquiv _ _ :=
    { toFun := fun f => ⟨f, continuous_to_indiscrete f⟩
      invFun := fun f => f.val
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  naturality_left _ _ := Subtype.ext rfl
  naturality_right _ _ := Subtype.ext rfl

#check indiscreteAdj
-- 表示: `Cat.indiscreteAdj : Adjunction forgetful indiscreteFunctor`
-- 読み: こちらは「忘却 ⊣ 密着」。合わせて 離散 ⊣ 忘却 ⊣ 密着。

end Cat

/-! ## Part 4: 反例 — 主定理の仮定は外せない -/

/-- 問題12: 離散位相を入れた `Bool` はコンパクト。
点が2つしかないので、被覆から `true` 用と `false` 用の番号を1つずつ取ればよい。 -/
theorem compactSpace_discrete_bool : @CompactSpace Bool (discrete Bool) := by
  refine @CompactSpace.mk Bool (discrete Bool) ?_
  intro I U _ hcov
  have ⟨i₁, h₁⟩ := hcov true trivial
  have ⟨i₂, h₂⟩ := hcov false trivial
  refine ⟨{j | j = i₁ ∨ j = i₂}, ⟨2, fun k => if k.val = 0 then i₁ else i₂, ?_⟩, ?_⟩
  · intro a ha
    cases ha with
    | inl h => exact ⟨⟨0, by omega⟩, by simp [h]⟩
    | inr h => exact ⟨⟨1, by omega⟩, by simp [h]⟩
  · intro b _
    cases b with
    | true => exact ⟨i₁, Or.inl rfl, h₁⟩
    | false => exact ⟨i₂, Or.inr rfl, h₂⟩

#check compactSpace_discrete_bool
-- 表示: `compactSpace_discrete_bool : CompactSpace Bool`
-- 読み: こちらも `discrete Bool` が表示から省かれている。

/-- 問題13: 恒等写像 `id : (Bool, 密着) → (Bool, 離散)` は連続でない。
離散側で開の `{b | b = true}` の逆像は自分自身だが、密着側では `∅` でも `univ` でもない。 -/
theorem not_continuous_id_indiscrete_to_discrete :
    ¬ @Continuous Bool (indiscrete Bool) Bool (discrete Bool) (fun b => b) := by
  intro h
  have hopen := h {b | b = true} trivial
  cases hopen with
  | inl he =>
    have hmem : (true : Bool) ∈ ((fun b : Bool => b) ⁻¹' {b | b = true}) := rfl
    rw [he] at hmem
    exact hmem
  | inr hu =>
    have hmem : (false : Bool) ∈ ((fun b : Bool => b) ⁻¹' {b | b = true}) := by
      rw [hu]
      trivial
    have : false = true := hmem
    exact Bool.noConfusion this

#check not_continuous_id_indiscrete_to_discrete
-- 表示: `not_continuous_id_indiscrete_to_discrete : ¬Continuous fun b ↦ b`
-- 読み: 両側の位相（密着 → 離散）が省かれ、「恒等写像が不連続」という一見奇妙な
-- 表示になる。同じ型に2つの位相を載せているので、`@` を思い出して読むこと。

/-!
まとめ: `id : (Bool, 離散) → (Bool, 密着)` は

* 連続（問題3）で全単射、
* 定義域はコンパクト（問題12）、
* しかし逆写像（これも `id`）は連続でない（問題13）。

つまり同相ではない。`Top.lean` の主定理と見比べると、
足りないのは終域のハウスドルフ性だけであり（問題4）、
主定理のハウスドルフという仮定が外せないことが分かる。
-/

/-! ## Part 5: 位相空間の別定義と等価性（解答） -/

/-- 集合族の共通部分。`sUnion` の双対。 -/
def Set.sInter {α : Type} (S : Set (Set α)) : Set α := {a | ∀ s ∈ S, a ∈ s}

/-- 前置記法 `⋂₀ S`。 -/
prefix:110 "⋂₀ " => Set.sInter

/-- 包含の反対称性。集合の等式を示す基本手段。 -/
lemma Set.subset_antisymm {α : Type} {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  Set.ext fun a => ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩

/-- 同じ `IsOpen` を持つ位相は等しい。証明フィールドは proof irrelevance により
等しさに影響しないので、`cases` で分解して述語の一致を代入すれば `rfl` で閉じる。 -/
theorem TopologicalSpace.ext' {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : t₁.IsOpen = t₂.IsOpen) : t₁ = t₂ := by
  cases t₁; cases t₂; cases h; rfl

/-- 問題14: 補集合の基本法則（ド・モルガンを含む6本）。 -/
lemma Set.compl_univ {α : Type} : (Set.univ : Set α)ᶜ = ∅ :=
  Set.ext fun _ => ⟨fun h => h trivial, fun h => False.elim h⟩

lemma Set.compl_empty {α : Type} : (∅ : Set α)ᶜ = Set.univ :=
  Set.ext fun _ => ⟨fun _ => trivial, fun _ h => h⟩

lemma Set.compl_union {α : Type} (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  Set.ext fun _ => ⟨fun h => ⟨fun hs => h (Or.inl hs), fun ht => h (Or.inr ht)⟩,
    fun h hu => match hu with | Or.inl hs => h.1 hs | Or.inr ht => h.2 ht⟩

lemma Set.compl_inter {α : Type} (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  apply Set.ext
  intro a
  constructor
  · intro h
    by_cases hs : a ∈ s
    · exact Or.inr fun ht => h ⟨hs, ht⟩
    · exact Or.inl hs
  · intro h hc
    cases h with
    | inl h => exact h hc.1
    | inr h => exact h hc.2

lemma Set.compl_sUnion {α : Type} (S : Set (Set α)) :
    (⋃₀ S)ᶜ = ⋂₀ (Set.compl '' S) := by
  apply Set.ext
  intro a
  constructor
  · intro h u hu
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    intro has
    exact h ⟨s, hsS, has⟩
  · intro h ⟨s, hsS, has⟩
    exact h sᶜ ⟨s, hsS, rfl⟩ has

lemma Set.compl_sInter {α : Type} (S : Set (Set α)) :
    (⋂₀ S)ᶜ = ⋃₀ (Set.compl '' S) := by
  apply Set.ext
  intro a
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro s hsS
    apply Classical.byContradiction
    intro hns
    exact hne ⟨sᶜ, ⟨s, hsS, rfl⟩, hns⟩
  · intro ⟨u, hu, hau⟩ hmem
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu] at hau
    exact hau (hmem s hsS)

/-! ### A: 閉集合系 -/

/-- 閉集合系による位相の公理化。開集合系の公理の双対。 -/
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

/-- 問題15: 閉集合系から開集合系を作る（開 = 補集合が閉）。 -/
@[reducible] def ClosedTopology.toTop {X : Type} (c : ClosedTopology X) : TopologicalSpace X where
  IsOpen s := c.IsClosed sᶜ
  isOpen_univ := by rw [Set.compl_univ]; exact c.isClosed_empty
  isOpen_inter s t hs ht := by
    rw [Set.compl_inter]; exact c.isClosed_union _ _ hs ht
  isOpen_sUnion S h := by
    rw [Set.compl_sUnion]
    refine c.isClosed_sInter _ fun u hu => ?_
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    exact h s hsS

/-- 問題16: 開集合系から閉集合系を作る（閉 = 補集合が開）。 -/
def TopologicalSpace.toClosed {X : Type} (t : TopologicalSpace X) : ClosedTopology X where
  IsClosed s := t.IsOpen sᶜ
  isClosed_empty := by rw [Set.compl_empty]; exact t.isOpen_univ
  isClosed_union s u hs hu := by
    rw [Set.compl_union]; exact t.isOpen_inter _ _ hs hu
  isClosed_sInter S h := by
    rw [Set.compl_sInter]
    refine t.isOpen_sUnion _ fun u hu => ?_
    have ⟨s, hsS, hsu⟩ := hu
    rw [← hsu]
    exact h s hsS

/-- 問題17: 往復は恒等（開→閉→開）。鍵は二重補集合。 -/
theorem toTop_toClosed {X : Type} (t : TopologicalSpace X) : t.toClosed.toTop = t := by
  apply TopologicalSpace.ext'
  funext s
  show t.IsOpen sᶜᶜ = t.IsOpen s
  rw [Set.compl_compl]

theorem toClosed_toTop {X : Type} (c : ClosedTopology X) : c.toTop.toClosed = c := by
  apply ClosedTopology.ext'
  funext s
  show c.IsClosed sᶜᶜ = c.IsClosed s
  rw [Set.compl_compl]

/-- 問題17: 開集合系と閉集合系は「構造として」全単射で対応する。 -/
def topEquivClosed (X : Type) : Cat.Equiv (TopologicalSpace X) (ClosedTopology X) where
  toFun := TopologicalSpace.toClosed
  invFun := ClosedTopology.toTop
  left_inv := toTop_toClosed
  right_inv := toClosed_toTop

/-! ### B: Kuratowski の閉包作用素 -/

/-- Kuratowski の閉包公理。閉包の振る舞いだけで位相を決める。 -/
structure KuratowskiClosure (X : Type) where
  /-- 閉包作用素。 -/
  cl (s : Set X) : Set X
  /-- 空集合の閉包は空。 -/
  cl_empty : cl ∅ = ∅
  /-- 拡大性。 -/
  subset_cl (s : Set X) : s ⊆ cl s
  /-- 有限合併の保存。 -/
  cl_union (s t : Set X) : cl (s ∪ t) = cl s ∪ cl t
  /-- 冪等性。 -/
  cl_cl (s : Set X) : cl (cl s) = cl s

theorem KuratowskiClosure.ext' {X : Type} {k₁ k₂ : KuratowskiClosure X}
    (h : k₁.cl = k₂.cl) : k₁ = k₂ := by
  cases k₁; cases k₂; cases h; rfl

/-- 位相から定める閉包: `s` を含む閉集合すべての共通部分。 -/
def TopologicalSpace.closure {X : Type} (t : TopologicalSpace X) (s : Set X) : Set X :=
  ⋂₀ {u | t.IsOpen uᶜ ∧ s ⊆ u}

/-- 問題18の準備（解答側）: 位相から定めた閉包の基本性質4本。 -/
lemma TopologicalSpace.subset_closure {X : Type} (t : TopologicalSpace X) (s : Set X) :
    s ⊆ t.closure s :=
  fun a ha _ hu => hu.2 a ha

lemma TopologicalSpace.closure_min {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (hu : t.IsOpen uᶜ) (hsu : s ⊆ u) : t.closure s ⊆ u :=
  fun _ ha => ha u ⟨hu, hsu⟩

lemma TopologicalSpace.closure_isClosed {X : Type} (t : TopologicalSpace X) (s : Set X) :
    t.IsOpen (t.closure s)ᶜ := by
  show t.IsOpen (⋂₀ {u | t.IsOpen uᶜ ∧ s ⊆ u})ᶜ
  rw [Set.compl_sInter]
  refine t.isOpen_sUnion _ fun v hv => ?_
  have ⟨u, hu, huv⟩ := hv
  rw [← huv]
  exact hu.1

lemma TopologicalSpace.closure_mono {X : Type} (t : TopologicalSpace X) {s u : Set X}
    (h : s ⊆ u) : t.closure s ⊆ t.closure u :=
  t.closure_min (t.closure_isClosed u) fun a ha => t.subset_closure u a (h a ha)

/-- 問題19: 閉包公理から単調性が出る（合併の保存だけから）。 -/
lemma KuratowskiClosure.mono {X : Type} (k : KuratowskiClosure X) {s t : Set X}
    (h : s ⊆ t) : k.cl s ⊆ k.cl t := by
  have hst : s ∪ t = t :=
    Set.subset_antisymm
      (fun a ha => match ha with | Or.inl h' => h a h' | Or.inr h' => h')
      (fun a ha => Or.inr ha)
  have hu := k.cl_union s t
  rw [hst] at hu
  intro a ha
  rw [hu]
  exact Or.inl ha

/-- 問題20: 閉包作用素から開集合系を作る（開 = 補集合が閉包の不動点）。 -/
@[reducible] def KuratowskiClosure.toTop {X : Type} (k : KuratowskiClosure X) : TopologicalSpace X where
  IsOpen s := k.cl sᶜ = sᶜ
  isOpen_univ := by rw [Set.compl_univ]; exact k.cl_empty
  isOpen_inter s t hs ht := by rw [Set.compl_inter, k.cl_union, hs, ht]
  isOpen_sUnion S h := by
    apply Set.subset_antisymm
    · intro a ha ⟨s, hsS, has⟩
      have hTs : (⋃₀ S)ᶜ ⊆ sᶜ := fun b hb hbs => hb ⟨s, hsS, hbs⟩
      have hcl := k.mono hTs a ha
      rw [h s hsS] at hcl
      exact hcl has
    · exact k.subset_cl _

/-- 問題21: 位相から閉包作用素を作る（閉包 = 含む閉集合すべての共通部分）。 -/
def TopologicalSpace.toKur {X : Type} (t : TopologicalSpace X) : KuratowskiClosure X where
  cl := t.closure
  cl_empty := by
    apply Set.subset_antisymm
    · exact t.closure_min (by rw [Set.compl_empty]; exact t.isOpen_univ) fun a ha => ha
    · exact t.subset_closure ∅
  subset_cl := t.subset_closure
  cl_union s u := by
    apply Set.subset_antisymm
    · refine t.closure_min ?_ ?_
      · rw [Set.compl_union]
        exact t.isOpen_inter _ _ (t.closure_isClosed s) (t.closure_isClosed u)
      · intro a ha
        cases ha with
        | inl h => exact Or.inl (t.subset_closure s a h)
        | inr h => exact Or.inr (t.subset_closure u a h)
    · intro a ha
      cases ha with
      | inl h => exact t.closure_mono (fun b hb => Or.inl hb) a h
      | inr h => exact t.closure_mono (fun b hb => Or.inr hb) a h
  cl_cl s := by
    apply Set.subset_antisymm
    · exact t.closure_min (t.closure_isClosed s) fun a ha => ha
    · exact t.subset_closure _

/-- 問題22: 往復（位相→閉包→位相）。 -/
theorem toKur_toTop {X : Type} (t : TopologicalSpace X) : t.toKur.toTop = t := by
  apply TopologicalSpace.ext'
  funext s
  show (t.closure sᶜ = sᶜ) = t.IsOpen s
  apply propext
  constructor
  · intro h
    have hc := t.closure_isClosed sᶜ
    rw [h, Set.compl_compl] at hc
    exact hc
  · intro h
    exact Set.subset_antisymm
      (t.closure_min (by rw [Set.compl_compl]; exact h) fun a ha => ha)
      (t.subset_closure _)

/-- 問題22: 往復（閉包→位相→閉包）。 -/
theorem toTop_toKur {X : Type} (k : KuratowskiClosure X) : k.toTop.toKur = k := by
  apply KuratowskiClosure.ext'
  funext s
  apply Set.subset_antisymm
  · intro a ha
    refine ha (k.cl s) ⟨?_, k.subset_cl s⟩
    show k.cl (k.cl s)ᶜᶜ = (k.cl s)ᶜᶜ
    rw [Set.compl_compl, k.cl_cl]
  · intro a ha u hu
    have h1 : k.cl uᶜᶜ = uᶜᶜ := hu.1
    rw [Set.compl_compl] at h1
    have hmem := k.mono hu.2 a ha
    rw [h1] at hmem
    exact hmem

/-- 問題22: 開集合系と閉包作用素の等価性。 -/
def topEquivKur (X : Type) : Cat.Equiv (TopologicalSpace X) (KuratowskiClosure X) where
  toFun := TopologicalSpace.toKur
  invFun := KuratowskiClosure.toTop
  left_inv := toKur_toTop
  right_inv := toTop_toKur

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
  /-- 近傍 U の中には、「その各点にとっても U が近傍」となる近傍 V がある。 -/
  interior (x : X) (U : Set X) (h : U ∈ N x) : ∃ V ∈ N x, ∀ y ∈ V, U ∈ N y

theorem NeighborhoodSystem.ext' {X : Type} {n₁ n₂ : NeighborhoodSystem X}
    (h : n₁.N = n₂.N) : n₁ = n₂ := by
  cases n₁; cases n₂; cases h; rfl

/-- 問題23: 近傍系から開集合系を作る（開 = 各点の近傍であるような集合）。 -/
@[reducible] def NeighborhoodSystem.toTop {X : Type} (n : NeighborhoodSystem X) : TopologicalSpace X where
  IsOpen s := ∀ x ∈ s, s ∈ n.N x
  isOpen_univ := fun x _ => n.univ_mem x
  isOpen_inter s t hs ht := fun x hx =>
    n.inter x s t (hs x hx.1) (ht x hx.2)
  isOpen_sUnion S h := fun x hx => by
    have ⟨s, hsS, hxs⟩ := hx
    exact n.superset x s _ (h s hsS x hxs) fun b hb => ⟨s, hsS, hb⟩

/-- 問題24: 開集合系から近傍系を作る（近傍 = 開集合を間に挟んで点を含む集合）。 -/
def TopologicalSpace.toNbhd {X : Type} (t : TopologicalSpace X) : NeighborhoodSystem X where
  N x := {U | ∃ V, t.IsOpen V ∧ x ∈ V ∧ V ⊆ U}
  univ_mem _x := ⟨Set.univ, t.isOpen_univ, trivial, fun _ _ => trivial⟩
  mem_of x _U h :=
    have ⟨_, _, hxV, hVU⟩ := h
    hVU x hxV
  superset _x _U _W hU hUW :=
    have ⟨V, hV, hxV, hVU⟩ := hU
    ⟨V, hV, hxV, fun b hb => hUW b (hVU b hb)⟩
  inter _x _U _W hU hW :=
    have ⟨V₁, h₁, hx₁, hs₁⟩ := hU
    have ⟨V₂, h₂, hx₂, hs₂⟩ := hW
    ⟨V₁ ∩ V₂, t.isOpen_inter _ _ h₁ h₂, ⟨hx₁, hx₂⟩, fun b hb => ⟨hs₁ b hb.1, hs₂ b hb.2⟩⟩
  interior _x _U hU :=
    have ⟨V, hV, hxV, hVU⟩ := hU
    ⟨V, ⟨V, hV, hxV, fun _ hb => hb⟩, fun _ hy => ⟨V, hV, hy, hVU⟩⟩

/-- 問題25: 往復（位相→近傍→位相）。`isOpen_of_nhds` がそのまま効く。 -/
theorem toNbhd_toTop {X : Type} (t : TopologicalSpace X) : t.toNbhd.toTop = t := by
  apply TopologicalSpace.ext'
  funext s
  show (∀ x ∈ s, ∃ V, t.IsOpen V ∧ x ∈ V ∧ V ⊆ s) = t.IsOpen s
  apply propext
  constructor
  · intro h
    exact @isOpen_of_nhds X t s h
  · intro h x hx
    exact ⟨s, h, hx, fun _ hb => hb⟩

/-- 問題25: 往復（近傍→位相→近傍）。鍵は `W := {y | U ∈ N y}` が開になること。 -/
theorem toTop_toNbhd {X : Type} (n : NeighborhoodSystem X) : n.toTop.toNbhd = n := by
  apply NeighborhoodSystem.ext'
  funext x
  apply Set.subset_antisymm
  · intro U hU
    have ⟨V, hVopen, hxV, hVU⟩ := hU
    exact n.superset x V U (hVopen x hxV) hVU
  · intro U hU
    refine ⟨{y | U ∈ n.N y}, ?_, hU, ?_⟩
    · intro y hy
      have ⟨V, hVN, hall⟩ := n.interior y U hy
      exact n.superset y V _ hVN hall
    · exact fun y hy => n.mem_of y U hy

/-- 問題25: 開集合系と近傍系の等価性。 -/
def topEquivNbhd (X : Type) : Cat.Equiv (TopologicalSpace X) (NeighborhoodSystem X) where
  toFun := TopologicalSpace.toNbhd
  invFun := NeighborhoodSystem.toTop
  left_inv := toNbhd_toTop
  right_inv := toTop_toNbhd

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

/-- 問題26: 閉集合の中のネットの極限は、その閉集合に入る。 -/
theorem nets_of_isClosed {X : Type} (t : TopologicalSpace X) {s : Set X}
    (hs : t.IsOpen sᶜ) (D : DirectedIndex) (net : D.ι → X)
    (hnet : ∀ e, net e ∈ s) {a : X} (hconv : Converges t D net a) : a ∈ s := by
  by_cases ha : a ∈ s
  · exact ha
  · have ⟨d, hd⟩ := hconv sᶜ hs ha
    have ⟨e, hde, _⟩ := D.upper d d
    exact absurd (hnet e) (hd e hde)

/-- 問題27: 逆——中のネットの極限で閉じている集合は閉。

添字型を「`a` の開近傍の全体」とし、包含の逆向きで有向にする。
各近傍から `s` の点を**選ぶ**ところで `Classical.choose` が要る。 -/
theorem isClosed_of_nets {X : Type} (t : TopologicalSpace X) {s : Set X}
    (h : ∀ (D : DirectedIndex) (net : D.ι → X), (∀ e, net e ∈ s) →
         ∀ a, Converges t D net a → a ∈ s) :
    t.IsOpen sᶜ := by
  refine @isOpen_of_nhds X t sᶜ fun a ha => ?_
  by_cases hex : ∃ W, t.IsOpen W ∧ a ∈ W ∧ W ⊆ sᶜ
  · exact hex
  · exfalso
    -- `a` のどの開近傍も `s` と交わる
    have hmeet : ∀ W : {W : Set X // t.IsOpen W ∧ a ∈ W}, ∃ b, b ∈ W.val ∩ s := by
      intro ⟨W, hW, haW⟩
      by_cases hb : ∃ b, b ∈ W ∩ s
      · exact hb
      · exact absurd ⟨W, hW, haW, fun b hbW hbs => hb ⟨b, hbW, hbs⟩⟩ hex
    -- 添字 = a の開近傍の全体、包含の逆向きで有向
    let D : DirectedIndex := ⟨{W : Set X // t.IsOpen W ∧ a ∈ W},
      fun V W => W.val ⊆ V.val,
      ⟨⟨Set.univ, t.isOpen_univ, trivial⟩⟩,
      fun V W => ⟨⟨V.val ∩ W.val,
        t.isOpen_inter _ _ V.property.1 W.property.1,
        ⟨V.property.2, W.property.2⟩⟩,
        fun b hb => hb.1, fun b hb => hb.2⟩⟩
    -- 各近傍から s の点を選んでネットを作る（ここが選択）
    let net : D.ι → X := fun W => Classical.choose (hmeet W)
    have hnet_s : ∀ W, net W ∈ s := fun W => (Classical.choose_spec (hmeet W)).2
    have hconv : Converges t D net a := by
      intro U hU haU
      refine ⟨⟨U, hU, haU⟩, ?_⟩
      intro E hE
      exact hE _ (Classical.choose_spec (hmeet E)).1
    exact ha (h D net hnet_s a hconv)

-- 確認: 両方向とも古典論理に依存する（結論 a ∈ s には二重否定の除去が要る）。
-- 特に問題27は各近傍からの点の選択を Classical.choose で行っており、
-- ネットによる特徴づけには選択公理が深く関わる
#print axioms nets_of_isClosed
#print axioms isClosed_of_nets
