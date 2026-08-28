import Top

/-! # 発展演習の解答

`Extra.lean` の全問題の解答。問題文と説明はそちらを参照。
-/

universe u

/-! ## Part 1: 密着位相 -/

/-- 問題1: 密着位相。開集合は `∅` と `univ` だけ。 -/
@[reducible] def indiscrete (X : Type u) : TopologicalSpace X where
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

/-- 問題2: 離散位相からの写像はすべて連続。 -/
theorem continuous_from_discrete {X Y : Type u} [tY : TopologicalSpace Y] (f : X → Y) :
    @Continuous X (discrete X) Y tY f :=
  fun _ _ => trivial

/-- 問題3: 密着位相への写像はすべて連続。 -/
theorem continuous_to_indiscrete {X Y : Type u} [tX : TopologicalSpace X] (f : X → Y) :
    @Continuous X tX Y (indiscrete Y) f := by
  intro s hs
  cases hs with
  | inl h => rw [h]; exact isOpen_empty
  | inr h => rw [h]; exact isOpen_univ

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

/-! ## Part 2: 圏と関手 -/

namespace Cat

/-- 圏。（この定義は問題ファイルで与えられている） -/
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

/-- 問題5: 型の圏。対象は型、射は関数。法則はすべて `rfl`。 -/
@[reducible] def TypeCat : Category.{u} where
  Obj := Type u
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- 台の型と位相を束ねたもの。（問題ファイルで与えられている） -/
structure TopSpace : Type (u + 1) where
  carrier : Type u
  str : TopologicalSpace carrier

attribute [instance] TopSpace.str

/-- 問題6: 位相空間の圏。射は連続写像、すなわち「関数と連続性の証明の組」。 -/
@[reducible] def TopCat : Category.{u} where
  Obj := TopSpace.{u}
  Hom A B := { f : A.carrier → B.carrier // Continuous f }
  id _ := ⟨fun a => a, continuous_id⟩
  comp f g := ⟨fun a => g.val (f.val a), g.property.comp f.property⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

/-- 関手。（問題ファイルで与えられている） -/
structure Functor (C D : Category.{u}) where
  obj : C.Obj → D.Obj
  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)
  map_id : ∀ A : C.Obj, map (C.id A) = D.id (obj A)
  map_comp : ∀ {A B E : C.Obj} (f : C.Hom A B) (g : C.Hom B E),
    map (C.comp f g) = D.comp (map f) (map g)

/-- 問題7: 忘却関手。位相を忘れて台の型だけ残す。 -/
@[reducible] def forgetful : Functor TopCat.{u} TypeCat.{u} where
  obj A := A.carrier
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 問題8: 離散関手。型に離散位相を載せる。射の行き先は問題2で作った。 -/
@[reducible] def discreteFunctor : Functor TypeCat.{u} TopCat.{u} where
  obj X := ⟨X, discrete X⟩
  -- 行き先の位相はインスタンス探索では見つからないので、名前付き引数で明示する
  map f := ⟨f, continuous_from_discrete (tY := discrete _) f⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- 問題9: 密着関手。型に密着位相を載せる。射の行き先は問題3で作った。 -/
@[reducible] def indiscreteFunctor : Functor TypeCat.{u} TopCat.{u} where
  obj X := ⟨X, indiscrete X⟩
  map f := ⟨f, continuous_to_indiscrete (tX := indiscrete _) f⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-! ## Part 3: 随伴 -/

/-- 全単射。（問題ファイルで与えられている） -/
structure Equiv (α β : Type u) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- 随伴 `F ⊣ G`。hom 集合の自然な全単射。（問題ファイルで与えられている） -/
structure Adjunction {C D : Category.{u}} (F : Functor C D) (G : Functor D C) where
  homEquiv : (A : C.Obj) → (B : D.Obj) → Equiv (D.Hom (F.obj A) B) (C.Hom A (G.obj B))
  naturality_left :
    ∀ {A' A : C.Obj} {B : D.Obj} (f : C.Hom A' A) (g : D.Hom (F.obj A) B),
      (homEquiv A' B).toFun (D.comp (F.map f) g) = C.comp f ((homEquiv A B).toFun g)
  naturality_right :
    ∀ {A : C.Obj} {B B' : D.Obj} (g : D.Hom (F.obj A) B) (h : D.Hom B B'),
      (homEquiv A B').toFun (D.comp g h) = C.comp ((homEquiv A B).toFun g) (G.map h)

/-- 問題10: 離散 ⊣ 忘却。
`Hom_Top(D X, A) ≃ Hom_Type(X, U A)` で、対応の実体は「同じ関数」。 -/
def discreteAdj : Adjunction discreteFunctor.{u} forgetful.{u} where
  homEquiv _ _ :=
    { toFun := fun f => f.val
      invFun := fun f => ⟨f, continuous_from_discrete f⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  naturality_left _ _ := rfl
  naturality_right _ _ := rfl

/-- 問題11: 忘却 ⊣ 密着。合わせて 離散 ⊣ 忘却 ⊣ 密着 の3連随伴になる。 -/
def indiscreteAdj : Adjunction forgetful.{u} indiscreteFunctor.{u} where
  homEquiv _ _ :=
    { toFun := fun f => ⟨f, continuous_to_indiscrete f⟩
      invFun := fun f => f.val
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  naturality_left _ _ := Subtype.ext rfl
  naturality_right _ _ := Subtype.ext rfl

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

/-!
まとめ: `id : (Bool, 離散) → (Bool, 密着)` は

* 連続（問題3）で全単射、
* 定義域はコンパクト（問題12）、
* しかし逆写像（これも `id`）は連続でない（問題13）。

つまり同相ではない。`Top.lean` の主定理と見比べると、
足りないのは終域のハウスドルフ性だけであり（問題4）、
主定理のハウスドルフという仮定が外せないことが分かる。
-/
