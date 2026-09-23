-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import Intro2

-- # 位相空間

-- ## 1. タクティク — 証明のもう1つの書き方

theorem swapAnd' {p q : Prop} : p ∧ q → q ∧ p := by
  intro h            -- `fun h =>` に対応
  exact ⟨h.2, h.1⟩   -- この項をそのまま置く

#check swapAnd'

#print swapAnd'

/- ✏ 練習
1. `CH2.lean` 2節の `swapOr` をタクティク（`intro`・`cases`・`exact`）で
   書き直し、`#print` で生成された項を元の `swapOr` と見比べよ。字面は一致しない——
   `cases` は `match` ではなく `Or.casesOn` を直接置くからである。
   **それでも型は同じ**であり、検査されるのはその型だけである、
   というのが本節の要点である。
2. `theorem idTac {p : Prop} : p → p` を `intro`・`exact` で書き、`#print idTac` の
   表示を予想してから確かめよ（こちらは手書きと同じ字面に戻る）。
-/

-- ## 2. 集合

-- ここから `end Set` までの宣言には接頭辞 `Set.` が付く（[`Intro2.lean` 4節](#sec-Intro2.namespaces)）
namespace Set

-- 共通の引数の前置き。以後の宣言が `α` を使うと、自動で引数に取り込まれる
variable {α : Type}

instance : Inter (Set α) := ⟨fun s t => {a | a ∈ s ∧ a ∈ t}⟩

#check ({n | n = 1} : Set Nat) ∩ {n | n = 2}

instance : Union (Set α) := ⟨fun s t => {a | a ∈ s ∨ a ∈ t}⟩

#check ({n | n = 1} : Set Nat) ∪ {n | n = 2}

instance : EmptyCollection (Set α) := ⟨{_a | False}⟩

#check (∅ : Set Nat)

def univ : Set α := {_a | True}

#check univ

-- 確認: `0 ∈ univ` は定義を展開すると命題 `True` そのもの。
-- `trivial : True` がちょうどその型を持つので、これで閉じる
example : (0 : Nat) ∈ (univ : Set Nat) := trivial

def compl (s : Set α) : Set α := {a | a ∉ s}

#check compl

postfix:max "ᶜ" => Set.compl

def image {β : Type} (f : α → β) (s : Set α) : Set β := {b | ∃ a, a ∈ s ∧ f a = b}

#check image

infixl:80 " '' " => Set.image

def sUnion (S : Set (Set α)) : Set α := {a | ∃ s, s ∈ S ∧ a ∈ s}

#check sUnion

prefix:110 "⋃₀ " => Set.sUnion

def iUnion {I : Type} (U : I → Set α) : Set α := {a | ∃ i, a ∈ U i}

#check iUnion

def biUnion {I : Type} (J : Set I) (U : I → Set α) : Set α := {a | ∃ i, i ∈ J ∧ a ∈ U i}

#check biUnion

def preimage {β : Type} (f : α → β) (s : Set β) : Set α := {a | f a ∈ s}

#check preimage

infixl:80 " ⁻¹' " => Set.preimage

-- 確認: 逆像も定義どおりに展開される。両辺は計算（関数適用の簡約）で一致するので `rfl`
example : (fun n : Nat => n + 1) ⁻¹' {m | m = 3} = {n | n + 1 = 3} := rfl

-- ### 補足（初読は飛ばしてよい）: 記法の結合の強さ

example (f : Nat → Nat) (s t : Set Nat) : f '' s ∩ t = (f '' s) ∩ t := rfl
example (s t : Set Nat) : s ∩ tᶜ = s ∩ (tᶜ) := rfl
example (s t u : Set Nat) : s ∩ t ∪ u = (s ∩ t) ∪ u := rfl

-- （補足・先取りここまで）

def Finite (s : Set α) : Prop := ∃ (n : Nat) (f : Fin n → α), ∀ a ∈ s, ∃ i, f i = a

#check Finite

theorem Finite.empty : (∅ : Set α).Finite :=
  ⟨0, Fin.elim0, fun _ ha => False.elim ha⟩

#check Finite.empty

-- ### 外延性

theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

#check ext

theorem compl_compl (s : Set α) : sᶜᶜ = s :=
  ext fun _ => ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

#check compl_compl

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

-- ### 有限個の共通部分

def interFin : (n : Nat) → (Fin n → Set α) → Set α := fun n W =>
  match n with
  | 0 => univ
  | n + 1 => W 0 ∩ interFin n fun i => W i.succ

#check interFin

theorem mem_interFin : ∀ (n : Nat) (W : Fin n → Set α) (a : α), (∀ i, a ∈ W i) →
    a ∈ interFin n W := fun n W a h =>
  match n with
  | 0 => trivial
  | n + 1 => ⟨h 0, mem_interFin n (fun i => W i.succ) a fun i => h i.succ⟩

#check mem_interFin

theorem interFin_mem : ∀ (n : Nat) (W : Fin n → Set α) (a : α), a ∈ interFin n W →
    ∀ i, a ∈ W i := fun n W a h i =>
  match n with
  | 0 => Fin.elim0 i
  | n + 1 => Fin.cases h.1 (fun j => interFin_mem n (fun k => W k.succ) a h.2 j) i

#check interFin_mem

end Set

/- ✏ 練習
1. `example : (2 : Nat) ∈ ({n | n < 5} : Set Nat)` を証明せよ。
   ヒント: `∈` と `setOf` を展開すればゴールは `2 < 5`、すなわち `3 ≤ 5`——
   `CH2.lean` 8節の構成子 `Nat.le.step`・`Nat.le.refl` で書ける。
2. `#print axioms Set.compl_compl` の結果を予想してから確かめよ
   （背理法を使った証明だった）。
-/

-- ## 3. 全単射

structure Function.Bijective {α β : Type} (f : α → β) : Prop where
  /-- 単射性: 送り先が同じなら元も同じ。 -/
  injective : Function.Injective f
  /-- 全射性: どの点にも、そこへ送られてくる元がある。 -/
  surjective : Function.Surjective f

#check Function.Bijective

/- ✏ 練習
1. 恒等写像が全単射であること
   `example : Function.Bijective (fun n : Nat => n)` を証明せよ
   （`injective` は仮定をそのまま返し、`surjective` は証人 `b` と `rfl`）。
-/

syntax:110 "⋃ " ident ", " term : term

syntax:110 "⋃ " ident " ∈ " term:110 ", " term : term

macro_rules
  | `(⋃ $i, $U) => `(Set.iUnion fun $i => $U)
  | `(⋃ $i ∈ $J, $U) => `(Set.biUnion $J fun $i => $U)

-- ## 4. 位相空間

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

-- `export` で `TopologicalSpace.IsOpen` などを接頭辞なしの `IsOpen` で書けるようにする
export TopologicalSpace (IsOpen isOpen_univ isOpen_inter isOpen_sUnion)

-- 以後 `X` は位相空間: 位相はインスタンス引数として各宣言に暗黙に付く
variable {X : Type} [TopologicalSpace X]

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

example : IsOpen (∅ : Set X) :=
  have h : (⋃₀ (∅ : Set (Set X))) = (∅ : Set X) :=
    Set.ext fun _ => ⟨fun ⟨_, hs, _⟩ => False.elim hs, fun ha => False.elim ha⟩
  h ▸ isOpen_sUnion _ fun _ hs => False.elim hs

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

-- こちらも項で。`match` の場合分けが `cases` に当たる
example {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) :=
  (Set.union_eq_sUnion s t) ▸ isOpen_sUnion _ fun _u hu =>
    match hu with
    | Or.inl h => h ▸ hs
    | Or.inr h => h ▸ ht

theorem isOpen_interFin : ∀ (n : Nat) (W : Fin n → Set X), (∀ i, IsOpen (W i)) →
    IsOpen (Set.interFin n W) := fun n W h =>
  match n with
  | 0 => isOpen_univ
  | n + 1 => isOpen_inter _ _ (h 0) (isOpen_interFin n (fun i => W i.succ) fun i => h i.succ)

#check isOpen_interFin

def IsClosed (s : Set X) : Prop := IsOpen sᶜ

#check IsClosed

-- ### 定義の確認

@[reducible] def discrete (X : Type) : TopologicalSpace X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ _ _ => trivial
  isOpen_sUnion := fun _ _ => trivial

#check discrete

/- ✏ 練習
1. `example : (discrete Nat).IsOpen {n | n = 0}` を証明せよ
   （離散位相では、どの部分集合の開性も `True`——証明は `trivial`）。
-/

-- ## 5. 連続写像

variable {Y : Type} [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z]

def Continuous (f : X → Y) : Prop := ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

#check Continuous

-- ### 定義の確認

theorem continuous_id : Continuous (fun x : X => x) :=
  fun _ hs => hs

#check continuous_id

theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) :=
  fun s hs => hf _ (hg s hs)

#check Continuous.comp

/- ✏ 練習
1. `#check @Continuous` の表示を予想してから確かめよ
   （2つの空間の位相が、どの種類の括弧で並ぶか）。
-/

-- ## 6. ハウスドルフ空間

class Hausdorff (X : Type) [TopologicalSpace X] : Prop where
  /-- 異なる2点は、交わらない開集合で分離できる。 -/
  separate : ∀ x y : X, x ≠ y →
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

#check Hausdorff

-- ## 7. コンパクト

def IsCompact (K : Set X) : Prop :=
  ∀ {I : Type} (U : I → Set X), (∀ i, IsOpen (U i)) → K ⊆ (⋃ i, U i) →
    ∃ J : Set I, J.Finite ∧ K ⊆ (⋃ i ∈ J, U i)

#check IsCompact

class CompactSpace (X : Type) [TopologicalSpace X] : Prop where
  isCompact_univ : IsCompact (Set.univ : Set X)

#check CompactSpace

-- ## 8. 補題1: コンパクト集合の連続像はコンパクト

theorem Set.subset_preimage_iUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i := by
  intro x hx
  have ⟨i, hi⟩ := h (f x) ⟨x, hx, rfl⟩
  exact ⟨i, hi⟩

#check Set.subset_preimage_iUnion

-- 項で書くと1行になる。`x ∈ ⋃ i, f ⁻¹' U i` と `f x ∈ ⋃ i, U i` は定義を
-- 展開すると同じ命題なので、`h` を適用した結果がそのまま答えになる
example {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {U : I → Set β} (h : f '' K ⊆ ⋃ i, U i) : K ⊆ ⋃ i, f ⁻¹' U i :=
  fun x hx => h (f x) ⟨x, hx, rfl⟩

theorem Set.image_subset_biUnion {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i := by
  intro b hb
  have ⟨x, hx, hfx⟩ := hb
  have ⟨i, hiJ, hxi⟩ := h x hx
  exact ⟨i, hiJ, hfx ▸ hxi⟩

#check Set.image_subset_biUnion

-- 項で。タクティク版の `have ⟨…⟩ :=` による分解が `match` に当たる
example {α β : Type} {f : α → β} {K : Set α} {I : Type}
    {J : Set I} {U : I → Set β} (h : K ⊆ ⋃ i ∈ J, f ⁻¹' U i) : f '' K ⊆ ⋃ i ∈ J, U i :=
  fun _b hb =>
    match hb with
    | ⟨x, hx, hfx⟩ =>
      match h x hx with
      | ⟨i, hiJ, hxi⟩ => ⟨i, hiJ, hfx ▸ hxi⟩

theorem IsCompact.image {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) := by
  intro I U hU hcov
  have ⟨J, hJ, hsub⟩ := hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
      (Set.subset_preimage_iUnion hcov)
  exact ⟨J, hJ, Set.image_subset_biUnion hsub⟩

#check IsCompact.image

-- 項で。`intro` が `fun` に、`have` の分解が `match` に、`exact` が組の構成に対応する
example {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) :=
  fun U hU hcov =>
    match hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i))
        (Set.subset_preimage_iUnion hcov) with
    | ⟨J, hJ, hsub⟩ => ⟨J, hJ, Set.image_subset_biUnion hsub⟩

/- ✏ 練習
1. `#print axioms Set.subset_preimage_iUnion` の結果を予想してから確かめよ
   （包含の付け替えだけの証明に、公理は要るだろうか）。
-/

-- ## 9. 補題2: ハウスドルフ空間のコンパクト集合は閉

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

-- 確認: この補題は選択公理どころか `Classical.choice` にも依存していない
-- （`propext` のみ）。データを添字に抱き合わせた効果がここに現れている。
#print axioms IsCompact.exists_disjoint_nhds

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

theorem IsCompact.isClosed [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K := by
  show IsOpen (Kᶜ : Set Y)
  refine isOpen_of_nhds fun y hy => ?_
  have ⟨W, hW, hyW, hWK⟩ := hK.exists_disjoint_nhds hy
  exact ⟨W, hW, hyW, hWK⟩

#check IsCompact.isClosed

-- 項ではここまで縮む。`show` は不要（`IsClosed K` と `IsOpen Kᶜ` は定義上同じ命題）で、
-- 補題が返す ∃ の中身が `isOpen_of_nhds` の要求とそのまま一致している
example [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K :=
  isOpen_of_nhds fun _ hy => hK.exists_disjoint_nhds hy

-- ## 10. 補題3: コンパクト空間の閉集合はコンパクト

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

-- 項で。`by_cases` の正体は排中律 `Classical.em` による場合分けである
example {α : Type} {C : Set α} {I : Type} {U : I → Set α}
    (hcov : C ⊆ ⋃ i, U i) (hI : Nonempty I) :
    (Set.univ : Set α) ⊆ ⋃ i, U i ∪ Cᶜ :=
  fun x _ =>
    (Classical.em (x ∈ C)).elim
      (fun hx => match hcov x hx with | ⟨i, hi⟩ => ⟨i, Or.inl hi⟩)
      (fun hx => match hI with | ⟨i⟩ => ⟨i, Or.inr hx⟩)

theorem Set.subset_biUnion_of_compl {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i := by
  intro x hx
  have ⟨i, hiJ, hi⟩ := hsub x trivial
  cases hi with
  | inl h => exact ⟨i, hiJ, h⟩
  | inr h => exact (h hx).elim

#check Set.subset_biUnion_of_compl

-- 項で。`cases hi with` の場合分けは、`match` の入れ子パターンでも書ける
example {α : Type} {C : Set α} {I : Type} {J : Set I}
    {U : I → Set α} (hsub : (Set.univ : Set α) ⊆ ⋃ i ∈ J, U i ∪ Cᶜ) : C ⊆ ⋃ i ∈ J, U i :=
  fun x hx =>
    match hsub x trivial with
    | ⟨i, hiJ, Or.inl h⟩ => ⟨i, hiJ, h⟩
    | ⟨_, _, Or.inr h⟩ => (h hx).elim

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

-- ## 11. 目標: コンパクトからハウスドルフへの連続全単射は同相

structure Homeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun

#check Homeomorph

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

-- 項で。`rw [← hfx, hgf]` の2回の書き換えが、`▸` 2回に分かれる
example {α β : Type} {f : α → β} {g : β → α}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (s : Set α) :
    g ⁻¹' s = f '' s :=
  Set.ext fun y =>
    ⟨fun hy => ⟨g y, hy, hfg y⟩,
     fun ⟨x, hx, hfx⟩ =>
      have h1 : g (f x) ∈ s := (hgf x).symm ▸ hx
      (hfx ▸ h1 : g y ∈ s)⟩

theorem isClosed_compl {s : Set X} (hs : IsOpen s) : IsClosed sᶜ := by
  show IsOpen (sᶜᶜ : Set X)
  rw [Set.compl_compl]
  exact hs

#check isClosed_compl

-- 項で。`rw [Set.compl_compl]` が `▸` に、`show` が型注釈に当たる
example {s : Set X} (hs : IsOpen s) : IsClosed sᶜ :=
  ((Set.compl_compl s).symm ▸ hs : IsOpen sᶜᶜ)

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

-- ### 使った公理の確認

#print axioms Homeomorph.ofContinuousBijective

/- ✏ 練習
1. `#print axioms isOpen_empty` の結果を予想してから確かめよ。
   `Classical.choice` は入るだろうか（合併の公理と `Set.ext` だけで示した証明だった）。
2. `discrete Bool` を使って、`TopologicalSpace Bool` の項を1つ `example` で書け。
3. `IsCompact.isClosed` の型で、「空間がハウスドルフ」という仮定が
   3種類の括弧のどれで現れるか予想してから、本文の表示の枠で確かめよ。
-/
