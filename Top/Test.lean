/-!
# 位相空間

mathlib を使わず、Lean 4 の標準ライブラリだけで位相空間を組み立てる。

最終目標は「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」。
そのために必要なものだけを、必要になった順に足していく。

標準ライブラリには数学でいう「集合」がないので、まずそこから作る。
-/

universe u v

/-! ## 1. 集合

`α` の部分集合を「`α` の要素を受け取って命題を返す関数」として定義する。
`s : Set α` と `a : α` に対し、`s a` が「`a` は `s` に属する」という命題そのものになる。
-/

def Set (α : Type u) : Type u := α → Prop

/-- `{a | p a}` で「`p` を満たす `a` 全体」を表す。 -/
def setOf {α : Type u} (p : α → Prop) : Set α := p

syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

namespace Set

variable {α : Type u}

/-- 所属。`a ∈ s` は定義上そのまま `s a`。 -/
instance : Membership α (Set α) := ⟨fun s a => s a⟩

instance : HasSubset (Set α) := ⟨fun s t => ∀ a, a ∈ s → a ∈ t⟩

instance : Inter (Set α) := ⟨fun s t => {a | a ∈ s ∧ a ∈ t}⟩

instance : Union (Set α) := ⟨fun s t => {a | a ∈ s ∨ a ∈ t}⟩

instance : EmptyCollection (Set α) := ⟨{_a | False}⟩

/-- 全体集合。 -/
def univ : Set α := {_a | True}

/-- 補集合。 -/
def compl (s : Set α) : Set α := {a | a ∉ s}

postfix:max "ᶜ" => Set.compl

/-- 像。`f '' s` は `s` の点を `f` で送った先の全体。 -/
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {b | ∃ a, a ∈ s ∧ f a = b}

infixl:80 " '' " => Set.image

/-- 集合族 `S` に属する集合すべての合併。
位相の公理でいう「任意個の合併」を、添字を使わずにこれで表す。 -/
def sUnion (S : Set (Set α)) : Set α := {a | ∃ s, s ∈ S ∧ a ∈ s}

prefix:110 "⋃₀ " => Set.sUnion

/-- 添字づけられた集合族 `U : I → Set α` の合併。 -/
def iUnion {I : Type v} (U : I → Set α) : Set α := {a | ∃ i, a ∈ U i}

/-- 添字を `J ⊆ I` に制限した合併。「部分族の合併」を表す。 -/
def biUnion {I : Type v} (J : Set I) (U : I → Set α) : Set α := {a | ∃ i, i ∈ J ∧ a ∈ U i}

/-- 逆像。`f ⁻¹' s` は、`f` で送ると `s` に入る点の全体。 -/
def preimage {β : Type v} (f : α → β) (s : Set β) : Set α := {a | f a ∈ s}

infixl:80 " ⁻¹' " => Set.preimage

/-- 有限集合: ある `n` について、`Fin n` からの写像で `s` の点をすべて拾えること。

`Fin n` は `0, 1, …, n-1` のちょうど `n` 個からなる型なので、
「`Fin n` で番号づけられる」がそのまま「点が有限個しかない」を意味する。

`f` は `s` の外の点を拾ってもよい（`Fin n` と `s` の全単射までは要求しない）。
「高々 `n` 個」で十分であり、こうしておくと部分集合の有限性がただちに従う。 -/
def Finite (s : Set α) : Prop := ∃ (n : Nat) (f : Fin n → α), ∀ a ∈ s, ∃ i, f i = a

theorem Finite.empty : (∅ : Set α).Finite :=
  ⟨0, Fin.elim0, fun _ ha => False.elim ha⟩

/-- 外延性: 属する要素が一致する集合は等しい。
関数の外延性 `funext` と命題の外延性 `propext` から従う。 -/
theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

/-- 二重補集合。ここで初めて古典論理（背理法）を使う。 -/
theorem compl_compl (s : Set α) : sᶜᶜ = s :=
  ext fun _ => ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

/-! ### 有限個の共通部分

`Fin n` で番号づけられた集合たちの共通部分。`n` についての再帰で定義する。
ハウスドルフ側の証明で、有限部分被覆から近傍を1つ作るのに使う。
-/

def interFin : (n : Nat) → (Fin n → Set α) → Set α
  | 0, _ => univ
  | n + 1, W => W 0 ∩ interFin n fun i => W i.succ

/-- すべての `W i` に入る点は共通部分に入る。 -/
theorem mem_interFin : ∀ (n : Nat) (W : Fin n → Set α) (a : α), (∀ i, a ∈ W i) →
    a ∈ interFin n W
  | 0, _, _, _ => trivial
  | n + 1, _, a, h => ⟨h 0, mem_interFin n _ a fun i => h i.succ⟩

/-- 共通部分に入る点は、すべての `W i` に入る。 -/
theorem interFin_mem : ∀ (n : Nat) (W : Fin n → Set α) (a : α), a ∈ interFin n W →
    ∀ i, a ∈ W i
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, W, a, h, i => by
      cases i using Fin.cases with
      | zero => exact h.1
      | succ j => exact interFin_mem n _ a h.2 j

end Set

/-! ## 2. 全単射

目標の「連続全単射」を述べるために要る。
`Function.Injective`（`∀ ⦃a b⦄, f a = f b → a = b`）と
`Function.Surjective`（`∀ b, ∃ a, f a = b`）は標準ライブラリにあるので、
全単射だけを定義する。
-/

def Function.Bijective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f

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

class TopologicalSpace (X : Type u) where
  /-- その集合が開集合であるという述語。 -/
  IsOpen : Set X → Prop
  /-- 全体集合は開。 -/
  isOpen_univ : IsOpen Set.univ
  /-- 2つの開集合の共通部分は開。 -/
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- 開集合をいくつ集めて合併しても開。 -/
  isOpen_sUnion : ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S)

export TopologicalSpace (IsOpen isOpen_univ isOpen_inter isOpen_sUnion)

variable {X : Type u} [TopologicalSpace X]

/-- 空集合が開であることは公理に含めなくてよい。
空な集合族の合併が空集合だから、`isOpen_sUnion` から従う。 -/
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

/-- 2つの開集合の合併も開。`s` と `t` だけからなる集合族に公理を適用する。 -/
theorem isOpen_union {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  have heq : s ∪ t = ⋃₀ {u | u = s ∨ u = t} := by
    apply Set.ext
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
  rw [heq]
  refine isOpen_sUnion _ fun u hu => ?_
  cases hu with
  | inl h => rw [h]; exact hs
  | inr h => rw [h]; exact ht

/-- 有限個の開集合の共通部分は開。`n` についての再帰で、公理の「2つの共通部分」を繰り返す。

無限個の共通部分では成り立たないことに注意（例えば実数直線で
`⋂ n, (-1/n, 1/n) = {0}` は開でない）。有限性がここで効く。 -/
theorem isOpen_interFin : ∀ (n : Nat) (W : Fin n → Set X), (∀ i, IsOpen (W i)) →
    IsOpen (Set.interFin n W)
  | 0, _, _ => isOpen_univ
  | n + 1, _, h => isOpen_inter _ _ (h 0) (isOpen_interFin n _ fun i => h i.succ)

/-- 閉集合: 補集合が開。 -/
def IsClosed (s : Set X) : Prop := IsOpen sᶜ

/-! ## 4. 連続写像

「近くの点を近くに送る」を開集合だけで言い換えたのが次の定義。
写像の向きと逆に、行き先の開集合を引き戻して考えるのがポイント。
-/

-- 空間はすべて同じ universe `u` に揃えておく。
-- コンパクト性の定義で添字の型 `I` を `Type u` に取るため、ここを揃えないと
-- 「`X` がコンパクト」と「`f '' X` がコンパクト」で universe がずれて型が合わなくなる。
variable {Y : Type u} [TopologicalSpace Y]

/-- 連続写像: 開集合の逆像がつねに開。 -/
def Continuous (f : X → Y) : Prop := ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

/-! ## 5. ハウスドルフ空間

「異なる2点は開集合で見分けられる」という条件。
点が多すぎず貼りついていない、という感じの性質。
-/

class Hausdorff (X : Type u) [TopologicalSpace X] : Prop where
  /-- 異なる2点は、交わらない開集合で分離できる。 -/
  separate : ∀ x y : X, x ≠ y →
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

/-! ## 6. コンパクト

「どんな開被覆にも有限部分被覆がある」という条件。
無限にある開集合のうち有限個で済ませられる、という有限性の性質。

被覆は添字づけられた族 `U : I → Set X` で表し、
部分被覆は添字の部分集合 `J ⊆ I` を取ることで表す。
`J` が有限であることは `Set.Finite`（`Fin n` で番号づけられること）で表す。
-/

def IsCompact (K : Set X) : Prop :=
  ∀ {I : Type u} (U : I → Set X), (∀ i, IsOpen (U i)) → K ⊆ (⋃ i, U i) →
    ∃ J : Set I, J.Finite ∧ K ⊆ (⋃ i ∈ J, U i)

/-- 空間そのものがコンパクトであること。 -/
class CompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  isCompact_univ : IsCompact (Set.univ : Set X)

/-! ## 7. 補題1: コンパクト集合の連続像はコンパクト

`f '' K` の開被覆を `f` で引き戻すと `K` の開被覆になる。
`K` のコンパクト性で有限部分被覆の添字 `J` を取れば、
同じ `J` がそのまま `f '' K` の有限部分被覆を与える。
有限性は受け取った `J` をそのまま使い回すだけなので、`Fin n` を開ける必要はない。
-/

theorem IsCompact.image {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' K) := by
  intro I U hU hcov
  -- 引き戻した族が `K` を覆う
  have hcov' : K ⊆ ⋃ i, f ⁻¹' U i := by
    intro x hx
    have hfx : f x ∈ f '' K := ⟨x, hx, rfl⟩
    have ⟨i, hi⟩ := hcov _ hfx
    exact ⟨i, hi⟩
  have ⟨J, hJ, hsub⟩ := hK (fun i => f ⁻¹' U i) (fun i => hf _ (hU i)) hcov'
  refine ⟨J, hJ, ?_⟩
  intro y hy
  have ⟨x, hx, hfx⟩ := hy
  have ⟨i, hiJ, hxi⟩ := hsub _ hx
  exact ⟨i, hiJ, hfx ▸ hxi⟩

/-! ## 8. 補題2: ハウスドルフ空間のコンパクト集合は閉

ここが証明の山場で、有限性を実際に使うのもここだけ。

`K` の外の点 `y` を1つ取る。`K` の各点 `x` は `y` と分離できるので、
交わらない開集合の組 `U x ∋ x`, `V x ∋ y` が取れる。
`U` たちは `K` を覆うから、コンパクト性で有限個 `U (g 0), …, U (g (n-1))` に減らせる。
対応する `V (g 0), …, V (g (n-1))` の共通部分を取れば、
これは有限個の共通部分なので開であり、`y` を含み、`K` と交わらない。
無限個の共通部分では開とは限らないので、有限に減らせたことが本質的に効いている。
-/

theorem IsCompact.isClosed [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K := by
  -- `K` の外の各点は、`K` と交わらない開近傍を持つ
  have key : ∀ y : Y, y ∉ K → ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ ∀ a ∈ W, a ∉ K := by
    intro y hy
    -- 各点 `x` について分離する開集合の組を選ぶ。
    -- `x ∉ K` のときは使わないので、`(∅, univ)` で埋めておく。
    have hsep : ∀ x : Y, ∃ p : Set Y × Set Y,
        IsOpen p.1 ∧ IsOpen p.2 ∧ (x ∈ K → x ∈ p.1) ∧ y ∈ p.2 ∧ p.1 ∩ p.2 = ∅ := by
      intro x
      by_cases hx : x ∈ K
      · have hne : x ≠ y := fun h => hy (h ▸ hx)
        have ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := Hausdorff.separate x y hne
        exact ⟨(U, V), hU, hV, fun _ => hxU, hyV, hUV⟩
      · refine ⟨(∅, Set.univ), isOpen_empty, isOpen_univ, fun h => absurd h hx, trivial, ?_⟩
        apply Set.ext
        intro a
        exact ⟨fun h => h.1, fun h => False.elim h⟩
    -- 選択公理で、点ごとの選択を1つの関数にまとめる
    have ⟨p, hp⟩ := Classical.axiomOfChoice hsep
    have hcov : K ⊆ ⋃ x, (p x).1 := fun a ha => ⟨a, (hp a).2.2.1 ha⟩
    have ⟨J, hJ, hsub⟩ := hK (fun x => (p x).1) (fun x => (hp x).1) hcov
    -- `J` は有限なので `Fin n` で番号づけられる
    have ⟨n, g, hg⟩ := hJ
    refine ⟨Set.interFin n fun i => (p (g i)).2, ?_, ?_, ?_⟩
    · -- 有限個の開集合の共通部分は開
      exact isOpen_interFin n _ fun i => (hp (g i)).2.1
    · -- `y` はすべての `V` に入る
      exact Set.mem_interFin n _ y fun i => (hp (g i)).2.2.2.1
    · -- 共通部分は `K` と交わらない
      intro a ha haK
      have ⟨x, hxJ, hax⟩ := hsub _ haK
      have ⟨i, hi⟩ := hg x hxJ
      have hav : a ∈ (p (g i)).2 := Set.interFin_mem n _ a ha i
      have hau : a ∈ (p (g i)).1 := by rw [hi]; exact hax
      have : a ∈ (p (g i)).1 ∩ (p (g i)).2 := ⟨hau, hav⟩
      rw [(hp (g i)).2.2.2.2] at this
      exact False.elim this
  -- `Kᶜ` は「`K` と交わらない開集合」全体の合併なので開
  show IsOpen (Kᶜ : Set Y)
  have heq : (Kᶜ : Set Y) = ⋃₀ {W | IsOpen W ∧ ∀ a ∈ W, a ∉ K} := by
    apply Set.ext
    intro a
    constructor
    · intro ha
      have ⟨W, hW, haW, hWK⟩ := key a ha
      exact ⟨W, ⟨hW, hWK⟩, haW⟩
    · intro ha
      have ⟨W, hW, haW⟩ := ha
      exact hW.2 a haW
  rw [heq]
  exact isOpen_sUnion _ fun _ hW => hW.1

/-! ## 9. 補題3: コンパクト空間の閉集合はコンパクト

`C` の被覆 `U` に、開集合 `Cᶜ` を各成分に足した族 `U i ∪ Cᶜ` を考えると、
これは空間全体を覆う。空間のコンパクト性で有限部分被覆を取り、
`C` の点は `Cᶜ` の側には入らないことを使って `U` だけの部分被覆に戻す。

添字集合を増やさずに済ませるため、`I` が空の場合だけ先に片付けておく。
-/

theorem IsClosed.isCompact [CompactSpace X] {C : Set X} (hC : IsClosed C) : IsCompact C := by
  intro I U hU hcov
  by_cases hI : Nonempty I
  · have hU' : ∀ i, IsOpen (U i ∪ Cᶜ) := fun i => isOpen_union (hU i) hC
    have hcov' : (Set.univ : Set X) ⊆ ⋃ i, U i ∪ Cᶜ := by
      intro x _
      by_cases hx : x ∈ C
      · have ⟨i, hi⟩ := hcov x hx
        exact ⟨i, Or.inl hi⟩
      · have ⟨i⟩ := hI
        exact ⟨i, Or.inr hx⟩
    have ⟨J, hJ, hsub⟩ :=
      CompactSpace.isCompact_univ (fun i => U i ∪ Cᶜ) hU' hcov'
    refine ⟨J, hJ, ?_⟩
    intro x hx
    have ⟨i, hiJ, hi⟩ := hsub x trivial
    cases hi with
    | inl h => exact ⟨i, hiJ, h⟩
    | inr h => exact absurd hx h
  · -- `I` が空なら `C` も空
    refine ⟨∅, Set.Finite.empty, ?_⟩
    intro x hx
    have ⟨i, _⟩ := hcov x hx
    exact absurd ⟨i⟩ hI

/-! ## 10. 目標: コンパクトからハウスドルフへの連続全単射は同相

同相写像とは、連続な全単射であって逆写像も連続なもの。
一般には逆写像の連続性は自動ではないが、
定義域がコンパクトで終域がハウスドルフならそれが従う、というのがここでの定理。

逆写像 `g` の連続性は「`X` の開集合 `s` について `g ⁻¹' s` が開」だが、
全単射なので `g ⁻¹' s = f '' s` であり、補集合を取ると
「`f '' sᶜ` が閉」を示せばよい。そこで補題3・1・2をこの順に使う:

  `sᶜ` は閉 → `sᶜ` はコンパクト → `f '' sᶜ` はコンパクト → `f '' sᶜ` は閉
-/

structure Homeomorph (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun

/-- 逆写像の連続性。これが定理の中身。 -/
theorem continuous_invFun [CompactSpace X] [Hausdorff Y]
    {f : X → Y} (hf : Continuous f) {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Continuous g := by
  intro s hs
  -- `sᶜ` は閉、よってコンパクト、よってその像もコンパクト、よって像は閉
  have hcC : IsClosed (sᶜ : Set X) := by
    show IsOpen (sᶜᶜ : Set X)
    rw [Set.compl_compl]
    exact hs
  have hcpt : IsCompact (f '' (sᶜ : Set X)) := IsCompact.image (IsClosed.isCompact hcC) hf
  have hclosed : IsClosed (f '' (sᶜ : Set X)) := IsCompact.isClosed hcpt
  -- `g ⁻¹' s` が `f '' sᶜ` の補集合であること
  have heq : g ⁻¹' s = (f '' (sᶜ : Set X))ᶜ := by
    apply Set.ext
    intro y
    constructor
    · intro hy hmem
      have ⟨x, hx, hfx⟩ := hmem
      -- `x ∉ s` なのに、`g y = g (f x) = x` が `s` に入ってしまう
      refine hx ?_
      show x ∈ s
      rw [← hgf x, hfx]
      exact hy
    · intro hy
      show g y ∈ s
      by_cases hgs : g y ∈ s
      · exact hgs
      · exact absurd ⟨g y, hgs, hfg y⟩ hy
  rw [heq]
  exact hclosed

/-- コンパクト空間からハウスドルフ空間への連続全単射は同相写像。 -/
noncomputable def Homeomorph.ofContinuousBijective [CompactSpace X] [Hausdorff Y]
    (f : X → Y) (hf : Continuous f) (hbij : Function.Bijective f) : Homeomorph X Y where
  toFun := f
  -- 全射性から逆写像を選ぶ。選択を使うので `noncomputable`。
  invFun := fun y => Classical.choose (hbij.2 y)
  left_inv := fun x => hbij.1 (Classical.choose_spec (hbij.2 (f x)))
  right_inv := fun y => Classical.choose_spec (hbij.2 y)
  continuous_toFun := hf
  continuous_invFun :=
    _root_.continuous_invFun hf
      (fun x => hbij.1 (Classical.choose_spec (hbij.2 (f x))))
      (fun y => Classical.choose_spec (hbij.2 y))

-- 使った公理の確認。`sorry` は使っていない。
-- 集合を関数として定義したので命題の外延性 `propext` を、
-- 点ごとの選択・背理法・逆写像の構成に `Classical.choice` を使っている。
-- （`funext` は Lean では `Quot.sound` から導かれる定理なので、公理として現れない。）
#print axioms Homeomorph.ofContinuousBijective
