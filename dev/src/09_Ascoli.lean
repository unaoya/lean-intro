import «06_Topology»

/-! # 発展演習: Ascoli の定理（ブルバキ流）

`06_Topology.lean` まで読み終えた人のための、もう1つの演習問題集
（`07_Exercises.lean` とは独立に読める）。題材は関数空間のコンパクト性の定理
**Ascoli の定理**である。

## 古典版とブルバキ版

古典的な Arzelà–Ascoli の定理は「`C([a, b])` の部分集合が相対コンパクトであるための
必要十分条件は、一様有界かつ同程度連続（等連続）であること」と述べられ、
証明には点列と対角線論法を使う。

ブルバキ（『位相』第X章 §2）はこれを次の2段に分解した。

1. **Théorème 1**: 等連続な関数族の上では、各点収束と一様収束が（コンパクト集合上で）一致する
2. **Théorème 2 (Ascoli)**: 等連続で、各点での値の集合が全有界（précompact）な族は、
   一様収束について全有界である。コンパクト性はその系として出る

点列も対角線論法も使わない。本質は 1——「等連続なら、有限個の点での値を見れば
全体が一様に制御できる」——であり、2 はそこから有限被覆を掛け合わせるだけで出る。
この演習ではこの分解に沿って進む。

## この演習での取捨

ブルバキは一様構造をフィルターで定義し、`𝔖`-収束（部分集合族 `𝔖` 上での一様収束）の
一般論の中で定理を述べる。mathlib の `Mathlib.Topology.UniformSpace.Ascoli` も
ほぼそのまま形式化している。この演習では次のように絞る。

* 一様構造は**近縁（entourage）の集合族**として直接公理化する（標準形の5公理）
* 関数空間は「コンパクト空間 `X` から一様空間 `Y` への写像全体」に
  **全体での一様収束**の一様構造を入れたものだけを扱う
* Théorème 1 は「一様構造の一致」という抽象的な形ではなく、
  **有限点制御補題**（Part C）という具体的な形で証明する
* 有限性は `List` で扱う（`06_Topology.lean` の `Set.Finite` との橋渡しは与える）

## 構成

* Part A: 一様構造と、そこから定まる位相
* Part B: 一様収束の一様構造と等連続性
* Part C: 核心補題（Théorème 1 の有限版）
* Part D: 全有界性と主定理（全有界版）
* Part E: 反例——等連続性の仮定は外せない
* Part F: 逆向き——全有界なら等連続
* Part G: フィルターと Zorn の補題（コンパクト版の準備）
* Part H: 主定理のコンパクト版

Part A〜D が本体で、ここまでに選択公理による「選択」は有限点制御補題の
近傍の選択（`Classical.choose`）しか使わない。Part G・H は重い。
一般の一様空間で「全有界 ⇒（完備なら）コンパクト」を示すには
**超フィルター補題**が要り、これは選択公理より真に弱いが、選択公理なしの集合論
（ZF）では証明できない。core Lean には Zorn の補題がないので、Part G で自作する。

## 進め方

`07_Exercises.lean` と同じく、`sorry` を自分の証明で置き換える。解答は `09_AscoliSol.lean` にある。
与えてある宣言（`sorry` のないもの）も、問題を解くときに使ってよい。
-/

/-! ## Part A: 一様構造

まず集合の道具を少し足す。`compRel V W` は関係の合成
（`a` から `V` で `z` へ、`z` から `W` で `b` へ行ける）、`swapRel V` は逆関係である。
リストと有限性の橋渡し2つも与える。
-/

namespace Set

variable {α : Type}

/-- 2つの集合が互いに含み合えば等しい。 -/
theorem subset_antisymm {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  ext fun a => ⟨h₁ a, h₂ a⟩

/-- 関係の合成 `V ○ W`。 -/
def compRel (V W : Set (α × α)) : Set (α × α) := {p | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W}

/-- 逆関係 `V⁻¹`。 -/
def swapRel (V : Set (α × α)) : Set (α × α) := {p | (p.2, p.1) ∈ V}

/-- リストに載っている元の全体は有限集合。 -/
theorem finite_of_list (L : List α) : Set.Finite {a | a ∈ L} :=
  ⟨L.length, L.get, fun _ ha => List.get_of_mem ha⟩

/-- 有限集合の元はすべて、あるリストに載せられる。 -/
theorem Finite.exists_list {s : Set α} (hs : s.Finite) : ∃ L : List α, ∀ a ∈ s, a ∈ L :=
  have ⟨_, f, hf⟩ := hs
  ⟨List.ofFn f, fun a ha => List.mem_ofFn.mpr (hf a ha)⟩

end Set

/-! 一様構造は「2点が `V`-近い」という関係 `V ⊆ α × α` たち（**近縁**）を指定する。
距離空間なら `V_ε = {(a, b) | d(a, b) < ε}` を含む関係が近縁である。
5つの公理はそれぞれ、距離の性質の抽象化になっている。

* `univ_mem`・`mono`・`inter_mem`: 近縁の全体はフィルターをなす（`ε` の取り方の自由度）
* `refl`: 近縁は対角線を含む（`d(a, a) = 0`）
* `symm`: 近縁の逆も近縁（`d(a, b) = d(b, a)`）
* `comp`: どの近縁 `V` にも、`W ○ W ⊆ V` となる近縁 `W` がある（三角不等式、`ε/2`）
-/

/-- 一様構造（標準形）。 -/
class UniformSpace (α : Type) where
  /-- 近縁の全体。 -/
  Entourage : Set (Set (α × α))
  /-- 全体の関係は近縁。 -/
  univ_mem : Set.univ ∈ Entourage
  /-- 近縁より大きい関係は近縁。 -/
  mono : ∀ {V W : Set (α × α)}, V ∈ Entourage → V ⊆ W → W ∈ Entourage
  /-- 2つの近縁の共通部分は近縁。 -/
  inter_mem : ∀ {V W : Set (α × α)}, V ∈ Entourage → W ∈ Entourage → V ∩ W ∈ Entourage
  /-- 近縁は対角線を含む。 -/
  refl : ∀ {V : Set (α × α)}, V ∈ Entourage → ∀ a, (a, a) ∈ V
  /-- 近縁の逆関係は近縁。 -/
  symm : ∀ {V : Set (α × α)}, V ∈ Entourage → Set.swapRel V ∈ Entourage
  /-- 「半分」の近縁がある。 -/
  comp : ∀ {V : Set (α × α)}, V ∈ Entourage → ∃ W, W ∈ Entourage ∧ Set.compRel W W ⊆ V

/-- `𝓤 α` で `α` の近縁の全体を表す（mathlib と同じ記号）。 -/
notation "𝓤 " α:max => @UniformSpace.Entourage α _

namespace UniformSpace

variable {α : Type} [UniformSpace α]

/-- 問題1: 対称な「半分」の近縁を作れ。古典的な議論の「`ε/2` を取る」に当たる。

ヒント: `comp` で `W ○ W ⊆ V` となる `W` を取り、`W ∩ swapRel W` を使う。 -/
theorem exists_half {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c, (a, b) ∈ W → (b, c) ∈ W → (a, c) ∈ V :=
  sorry

/-- 問題2: 対称な「3分の1」の近縁を作れ。これが Part C・F の「`ε/3` 論法」の道具になる。

ヒント: 問題1を2回使う（`V` の半分 `W₁`、`W₁` の半分 `W₂`）。
`(c, d) ∈ W₂` から `(c, d) ∈ W₁` を出すには、`(d, d) ∈ W₂`（`refl`）をつなげばよい。 -/
theorem exists_third {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c d, (a, b) ∈ W → (b, c) ∈ W → (c, d) ∈ W → (a, d) ∈ V :=
  sorry

/-- 問題3: 一様構造から位相が定まることを示せ。
`s` が開 ⟺ `s` のどの点 `a` にも、`a` の「`V`-球」`{b | (a, b) ∈ V}` が `s` に収まる近縁 `V` がある。

距離空間で「どの点にも、その点を中心とする `ε`-球が収まる」とするのと同じ定義である。
`instance` にしたので、以後一様空間には自動でこの位相が載る。 -/
instance toTopologicalSpace : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, ∃ V ∈ 𝓤 α, ∀ b, (a, b) ∈ V → b ∈ s
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 問題4: `V`-球そのものは開とは限らないが、中心を含む開集合を内側に含むことを示せ。

ヒント: `O = {y | ∃ W ∈ 𝓤 α, ∀ z, (y, z) ∈ W → (a, z) ∈ V}`（`y` の周りに
`V`-球に収まる近縁がある点の全体）が求めるもの。開であることは、
`W` の半分 `W'`（`comp`）を `y` の近くの点の証人に使えば示せる。 -/
theorem exists_open_ball {V : Set (α × α)} (hV : V ∈ 𝓤 α) (a : α) :
    ∃ O : Set α, IsOpen O ∧ a ∈ O ∧ ∀ b ∈ O, (a, b) ∈ V :=
  sorry

end UniformSpace

open UniformSpace

/-! ## Part B: 一様収束の一様構造と等連続性

写像 `f, g : X → Y` が「一様に `V`-近い」とは、すべての `x` で `(f x, g x) ∈ V` となること。
この関係 `unifRel V` を含む関係を近縁とするのが、**一様収束の一様構造**である。
Part A の位相と組み合わせると、`X → Y` には一様収束の位相が自動で載る。
-/

section FunctionSpace

variable {X Y : Type} [UniformSpace Y]

/-- 近縁 `V` から作る「一様に `V`-近い」写像の組の全体。 -/
def unifRel (V : Set (Y × Y)) : Set ((X → Y) × (X → Y)) := {p | ∀ x, (p.1 x, p.2 x) ∈ V}

/-- 問題5: 一様収束の一様構造が公理を満たすことを示せ。

`Entourage` を展開すると `∃ V ∈ 𝓤 Y, unifRel V ⊆ 𝒱` なので、各公理は
`Y` 側の同じ公理から出る。`comp` では `Y` 側の半分 `W` に対する `unifRel W` を使う。 -/
instance uniformFun : UniformSpace (X → Y) where
  Entourage := {𝒱 | ∃ V ∈ 𝓤 Y, unifRel V ⊆ 𝒱}
  univ_mem := sorry
  mono := sorry
  inter_mem := sorry
  refl := sorry
  symm := sorry
  comp := sorry

variable [TopologicalSpace X]

/-! **等連続性**は、族 `H` のすべての写像について、連続性の `U` が `f` によらず
共通に取れることをいう。定義域 `X` は位相空間でよい（一様構造は要らない）。 -/

/-- 点 `x` での等連続性: どの近縁 `V` にも `x` の開近傍 `U` があって、
`H` のどの `f` についても `U` の点での値が `f x` と `V`-近い。 -/
def EquicontinuousAt (H : Set (X → Y)) (x : X) : Prop :=
  ∀ V ∈ 𝓤 Y, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ V

/-- 等連続性: すべての点で等連続。 -/
def Equicontinuous (H : Set (X → Y)) : Prop := ∀ x, EquicontinuousAt H x

/-- 問題6: 等連続な族の部分族は等連続であることを示せ。 -/
theorem Equicontinuous.mono {H H' : Set (X → Y)} (hH : Equicontinuous H) (h : H' ⊆ H) :
    Equicontinuous H' :=
  sorry

/-- 問題7: 連続写像1つだけからなる族は等連続であることを示せ。
等連続性が連続性の「族版」であることの確認である。

ヒント: 問題4で `f x` の周りの開集合 `O` を取り、その逆像 `f ⁻¹' O` を `U` にする。 -/
theorem equicontinuous_singleton {f : X → Y} (hf : Continuous f) :
    Equicontinuous {g | g = f} :=
  sorry

/-! ## Part C: 核心補題（Théorème 1 の有限版）

ブルバキの Théorème 1 は「等連続集合の上では、各点収束の一様構造と
コンパクト収束の一様構造が一致する」と述べる。`X` がコンパクトなときに
これを具体的に言い直したのが次の補題である:

> 等連続族 `H` と近縁 `V` に対して、有限個の点 `P` と近縁 `W` があって、
> `H` の2つの写像が `P` の各点で `W`-近いなら、**すべての点で** `V`-近い。

「一様に近い」かどうかが、有限個の点での値だけで判定できる。
これが Ascoli の定理の心臓部で、証明は古典的な `ε/3` 論法そのものである。
-/

/-- 問題8: 有限点制御補題を示せ。

方針:
1. 問題2で `V` の対称な3分の1 `W` を取る
2. 各点 `x` で等連続性を `W` に使い、開近傍 `U x` を `Classical.choose` で選ぶ
3. `U` は `X` を覆うので、コンパクト性（`CompactSpace.isCompact_univ`）で
   有限個の添字の集合 `J` に間引き、`Set.Finite.exists_list` でリスト `P` にする
4. 任意の `x` は、ある `y ∈ J` について `x ∈ U y`。すると
   `(f x, f y)`・`(f y, g y)`・`(g y, g x)` がどれも `W` に入り、3つつなげて `(f x, g x) ∈ V` -/
theorem Equicontinuous.finite_control [CompactSpace X] {H : Set (X → Y)}
    (hH : Equicontinuous H) {V : Set (Y × Y)} (hV : V ∈ 𝓤 Y) :
    ∃ W ∈ 𝓤 Y, ∃ P : List X, ∀ f ∈ H, ∀ g ∈ H,
      (∀ p ∈ P, (f p, g p) ∈ W) → ∀ x, (f x, g x) ∈ V :=
  sorry

end FunctionSpace

/-! ## Part D: 全有界性と主定理

集合 `A` が **`V`-小さい**とは、`A` のどの2点も `V`-近いこと。
集合 `s` が**全有界**（ブルバキの précompact）とは、どの近縁 `V` についても
有限個の `V`-小さい集合で覆えること。距離空間なら「どの `ε` についても
直径 `ε` 以下の有限個の集合で覆える」である。
-/

section TotallyBounded

variable {α : Type}

/-- `A` は `V`-小さい。 -/
def Small (V : Set (α × α)) (A : Set α) : Prop := ∀ a ∈ A, ∀ b ∈ A, (a, b) ∈ V

/-- 全有界: どの近縁 `V` についても、`V`-小さい集合の有限リストで覆える。 -/
def TotallyBounded [UniformSpace α] (s : Set α) : Prop :=
  ∀ V ∈ 𝓤 α, ∃ L : List (Set α), (∀ A ∈ L, Small V A) ∧ ∀ a ∈ s, ∃ A ∈ L, a ∈ A

/-! 2つの有限被覆 `L`・`M` の**共通細分**——`A ∩ B`（`A ∈ L`、`B ∈ M`）の全体——も
有限被覆である。個数で言えば `|L| × |M|` 個だが、`Fin` の積の番号づけを避けて
`List.flatMap` で作る。この組合せ論の部分は与える。 -/

/-- 2つの有限被覆の共通細分。 -/
def List.interCover (L M : List (Set α)) : List (Set α) :=
  L.flatMap fun A => M.map fun B => A ∩ B

/-- 共通細分の各片は `A ∩ B` の形。 -/
theorem List.mem_interCover {L M : List (Set α)} {C : Set α} (h : C ∈ List.interCover L M) :
    ∃ A ∈ L, ∃ B ∈ M, C = A ∩ B := by
  have ⟨A, hA, hC⟩ := List.mem_flatMap.mp h
  have ⟨B, hB, hAB⟩ := List.mem_map.mp hC
  exact ⟨A, hA, B, hB, hAB.symm⟩

/-- `L` と `M` がともに `s` を覆うなら、共通細分も `s` を覆う。 -/
theorem List.interCover_covers {s : Set α} {L M : List (Set α)}
    (hL : ∀ a ∈ s, ∃ A ∈ L, a ∈ A) (hM : ∀ a ∈ s, ∃ B ∈ M, a ∈ B) :
    ∀ a ∈ s, ∃ C ∈ List.interCover L M, a ∈ C := by
  intro a ha
  have ⟨A, hA, haA⟩ := hL a ha
  have ⟨B, hB, haB⟩ := hM a ha
  exact ⟨A ∩ B, List.mem_flatMap.mpr ⟨A, hA, List.mem_map_of_mem hB⟩, haA, haB⟩

/-- 問題9: 全有界な集合の部分集合は全有界であることを示せ。 -/
theorem TotallyBounded.subset [UniformSpace α] {s t : Set α} (hs : TotallyBounded s)
    (h : t ⊆ s) : TotallyBounded t :=
  sorry

variable {X Y : Type} [UniformSpace Y]

/-- 問題10: 各点で値の集合が全有界なら、有限個の点 `P` を固定するごとに、
`H` を「`P` の各点で `W`-近い」写像の集まり有限個で覆えることを示せ。

`P` についての帰納法（再帰）で示す。
* `P = []`: 条件は空なので、`[Set.univ]` 1つで覆える
* `P = x :: P'`: `P'` についての被覆 `C` と、`x` での値の `W`-小さい被覆 `L` を取り、
  `L` の各片の逆像 `(fun f => f x) ⁻¹' A` のリストと `C` の共通細分を取る

ブルバキの証明では、ここが「有限個の全有界集合の積は全有界」に当たる。 -/
theorem finite_points_cover {H : Set (X → Y)}
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) {W : Set (Y × Y)} (hW : W ∈ 𝓤 Y) :
    ∀ P : List X, ∃ C : List (Set (X → Y)),
      (∀ S ∈ C, ∀ f ∈ S, ∀ g ∈ S, ∀ p ∈ P, (f p, g p) ∈ W) ∧ ∀ f ∈ H, ∃ S ∈ C, f ∈ S :=
  sorry

variable [TopologicalSpace X]

/-- 問題11（主定理・Ascoli の定理、全有界版）:
コンパクト空間 `X` から一様空間 `Y` への写像の族 `H` が等連続で、
各点での値の集合が全有界なら、`H` は一様収束について全有界であることを示せ。

方針: 近縁 `𝒱 ⊇ unifRel V` を取る。問題8で `V` に対する `W` と有限個の点 `P` を取り、
問題10で `P` についての被覆 `C` を作る。各片を `S ∩ H` に取り替えれば、
問題8により `𝒱`-小さくなる（問題8は `H` の写像にしか使えないので `∩ H` が要る）。 -/
theorem ascoli [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) : TotallyBounded H :=
  sorry

end TotallyBounded

/-! ## Part E: 反例——等連続性の仮定は外せない

`X` を「自然数に無限遠点を1つ付け加えた空間」（1点コンパクト化）、`Y` を `Bool` とし、
`H` を「点 `n` だけで `true` になる関数 `δ n`」の全体とする。
値は `Bool` にしかならないので各点での全有界性はただで成り立つが、
`H` は無限遠点で等連続でなく、実際に一様収束について全有界でない。

`Option Nat` の `none` を無限遠点とする。`none` を含む開集合は、
ある番号から先の自然数をすべて含むもの（補集合が有限であることに相当する）とする。
-/

namespace Counterexample

/-- 1点コンパクト化 `Option Nat` の位相（与える）。 -/
instance : TopologicalSpace (Option Nat) where
  IsOpen s := none ∈ s → ∃ N, ∀ n, N ≤ n → some n ∈ s
  isOpen_univ := fun _ => ⟨0, fun _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht ⟨h₁, h₂⟩
    have ⟨N₁, hN₁⟩ := hs h₁
    have ⟨N₂, hN₂⟩ := ht h₂
    exact ⟨N₁ + N₂, fun n hn =>
      ⟨hN₁ n (Nat.le_trans (Nat.le_add_right N₁ N₂) hn),
       hN₂ n (Nat.le_trans (Nat.le_add_left N₂ N₁) hn)⟩⟩
  isOpen_sUnion := by
    intro S hS ⟨s, hsS, hs⟩
    have ⟨N, hN⟩ := hS s hsS hs
    exact ⟨N, fun n hn => ⟨s, hsS, hN n hn⟩⟩

/-- 問題12: `Option Nat` はコンパクトであることを示せ。

ヒント: `none` を覆う `U i₀` は、ある `N` 以上の `some n` をすべて含む。
残りの `some 0, …, some (N-1)` を覆う添字を1つずつ `Classical.choose` で選び、
`i₀` と合わせて `Fin (N + 1) → I` で番号づける（`match` で `0` と `k + 1` に分ける）。 -/
instance : CompactSpace (Option Nat) where
  isCompact_univ := sorry

/-- 対角線。 -/
def diagonal (α : Type) : Set (α × α) := {p | p.1 = p.2}

/-- 離散一様構造: 対角線を含む関係がすべて近縁（与える）。 -/
@[reducible] def discreteUniformity (α : Type) : UniformSpace α where
  Entourage := {V | ∀ a, (a, a) ∈ V}
  univ_mem := fun _ => trivial
  mono := fun hV h a => h _ (hV a)
  inter_mem := fun hV hW a => ⟨hV a, hW a⟩
  refl := fun hV => hV
  symm := fun hV a => hV a
  comp := fun hV =>
    ⟨diagonal α, fun _ => rfl, fun ⟨a, b⟩ ⟨z, (h₁ : a = z), (h₂ : z = b)⟩ => by
      rw [← h₂, ← h₁]
      exact hV a⟩

instance : UniformSpace Bool := discreteUniformity Bool

/-- 点 `n` だけで `true` になる関数。無限遠点では `false`。 -/
def δ (n : Nat) : Option Nat → Bool
  | none => false
  | some m => decide (m = n)

/-- 反例の族。 -/
def H : Set (Option Nat → Bool) := {f | ∃ n, f = δ n}

/-- 問題13: `Bool` の部分集合はすべて全有界であることを示せ。

ヒント: `[{b | b = true}, {b | b = false}]` で覆う。各片は1点なので、どの近縁についても小さい。 -/
theorem totallyBounded_bool (s : Set Bool) : TotallyBounded s :=
  sorry

/-- 問題14: `H` は無限遠点で等連続でないことを示せ。

ヒント: 近縁として対角線 `diagonal Bool` を使う。`none` の開近傍は十分大きい `some N` を含むが、
`δ N none = false` と `δ N (some N) = true` は近くない。 -/
theorem not_equicontinuousAt : ¬ EquicontinuousAt H none :=
  sorry

/-- 問題15: `unifRel (diagonal Bool)` について小さい集合は `δ` を高々1つしか含まない。
そこで、そのような集合の有限リストに対し、どこまで先に行っても
どの片にも入らない `δ n` があることを示せ（鳩の巣原理の代わり）。

ヒント: リストについての帰納法。`A :: L` では、`L` を避ける `δ n`（`N ≤ n`）と、
さらに `L` を避ける `δ m`（`n + 1 ≤ m`）を取る。`A` が両方を含むことはない
（点 `some n` での値が `true` と `false` で異なる）。 -/
theorem exists_avoid (L : List (Set (Option Nat → Bool)))
    (hL : ∀ A ∈ L, Small (unifRel (diagonal Bool)) A) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ A ∈ L, δ n ∉ A :=
  sorry

/-- 問題16: `H` は一様収束について全有界でないことを示せ。
問題12〜14と合わせると、主定理の「等連続」を外すと結論が成り立たないことがわかる。 -/
theorem not_totallyBounded : ¬ TotallyBounded H :=
  sorry

end Counterexample

/-! ## Part F: 逆向き——全有界なら等連続

ブルバキの Théorème 2 は必要十分条件である。逆向き（Arzelà が示した向き）は
`X` のコンパクト性も要らない。ただし `H` の各写像が連続であることは仮定する。
-/

section Converse

variable {X Y : Type} [UniformSpace Y]

/-- 問題17: 一様収束について全有界な族は、各点での値の集合も全有界であることを示せ。

ヒント: `unifRel V` についての被覆の各片の、`x` での値の像を並べる。 -/
theorem TotallyBounded.eval {H : Set (X → Y)} (hH : TotallyBounded H) (x : X) :
    TotallyBounded ((fun f => f x) '' H) :=
  sorry

variable [TopologicalSpace X]

/-- 問題18: 連続写像からなる、一様収束について全有界な族は等連続であることを示せ。

方針: 3分の1の近縁 `W` を取り、`unifRel W` について `H` を有限個の小さい片で覆う。
被覆のリストについての帰納法で、「どの片 `S` についても、`S ∩ H` の写像がすべて
`U` 上で `V`-振れに収まる」開近傍 `U` を作る。片 `S` が `H` の元 `g` を含むなら、
`g` の連続性で近傍を縮め、`(f x, g x)`・`(g x, g x')`・`(g x', f x')` の3つをつなぐ
（含まないなら縮めなくてよい）。 -/
theorem TotallyBounded.equicontinuous {H : Set (X → Y)} (hc : ∀ f ∈ H, Continuous f)
    (hH : TotallyBounded H) : Equicontinuous H :=
  sorry

end Converse

/-! ## Part G: フィルターと Zorn の補題

コンパクト版の証明には、コンパクト性をフィルターで言い換える必要がある。
**フィルター**は「十分大きい集合」の集まりで、一様構造の近縁の全体
（Part A の `univ_mem`・`mono`・`inter_mem`）がまさにその例になっている。
-/

/-- フィルター。 -/
structure Filter (α : Type) where
  /-- 属する集合の全体。 -/
  sets : Set (Set α)
  /-- 全体集合は属する。 -/
  univ_mem : Set.univ ∈ sets
  /-- 属する集合より大きい集合は属する。 -/
  mono : ∀ {s t : Set α}, s ∈ sets → s ⊆ t → t ∈ sets
  /-- 2つの共通部分も属する。 -/
  inter_mem : ∀ {s t : Set α}, s ∈ sets → t ∈ sets → s ∩ t ∈ sets

namespace Filter

variable {α β : Type}

/-- `s ∈ F` で `s ∈ F.sets` を表す。 -/
instance : Membership (Set α) (Filter α) := ⟨fun F s => s ∈ F.sets⟩

/-- 超フィルター: 空集合を含まず、どの集合もそれ自身か補集合のどちらかが属する。 -/
structure IsUltra (F : Filter α) : Prop where
  /-- 空集合は属さない。 -/
  empty_not_mem : (∅ : Set α) ∉ F
  /-- どの集合も、それ自身か補集合が属する。 -/
  mem_or_compl_mem : ∀ s : Set α, s ∈ F ∨ sᶜ ∈ F

/-- 超フィルターに属さない集合の補集合は属する。 -/
theorem IsUltra.compl_mem {F : Filter α} (hF : F.IsUltra) {s : Set α} (hs : s ∉ F) : sᶜ ∈ F :=
  (hF.mem_or_compl_mem s).resolve_left hs

/-- 空集合を含まないフィルターの元は空でない。 -/
theorem nonempty_of_mem {F : Filter α} (hF : (∅ : Set α) ∉ F) {s : Set α} (hs : s ∈ F) :
    ∃ a, a ∈ s :=
  Classical.byContradiction fun h => hF (F.mono hs fun a ha => h ⟨a, ha⟩)

/-- 像フィルター: `f` による逆像が `F` に属する集合の全体。 -/
def map (f : α → β) (F : Filter α) : Filter β where
  sets := {s | f ⁻¹' s ∈ F}
  univ_mem := F.univ_mem
  mono := fun hs h => F.mono hs fun a ha => h (f a) ha
  inter_mem := fun hs ht => F.inter_mem hs ht

/-- 問題19: 超フィルターの像は超フィルターであることを示せ。

ヒント: `f ⁻¹' ∅` と `∅`、`f ⁻¹' sᶜ` と `(f ⁻¹' s)ᶜ` は定義上等しい。 -/
theorem IsUltra.map {F : Filter α} (hF : F.IsUltra) (f : α → β) : (F.map f).IsUltra :=
  sorry

/-- 問題20: 有限個（リスト `L` で添字づけた）の元の共通部分もフィルターに属することを示せ。
リストについての再帰で示す。 -/
theorem mem_list_inter (F : Filter α) {I : Type} (s : I → Set α) :
    ∀ L : List I, (∀ i ∈ L, s i ∈ F) → {a | ∀ i ∈ L, a ∈ s i} ∈ F :=
  sorry

end Filter

/-! ### Zorn の補題（包含順序の集合族版）

示したいのは次の形である（`β` は任意の型、`𝔉` はその部分集合の族）:

> `𝔉` の空でない鎖の合併がつねに `𝔉` に属するなら、`𝔉` のどの元 `A` についても、
> `A` を含む `𝔉` の極大元 `M` がある。

証明は Bourbaki–Witt の不動点定理の方法による。選択公理で「真に大きい元があれば
それを1つ選ぶ」写像 `next` を作り、`A` から `next` と鎖の合併で到達できる集合の全体
（**塔**）を帰納的に定義する。塔が鎖であることを示せば、塔全体の合併 `M` が
`next M = M` を満たし、それが極大であることを意味する。
-/

namespace Zorn

variable {β : Type}

/-- 鎖: どの2つも包含で比較できる集合族。 -/
def IsChain (c : Set (Set β)) : Prop := ∀ s ∈ c, ∀ t ∈ c, s ⊆ t ∨ t ⊆ s

open Classical in
/-- `S` より真に大きい `𝔉` の元があればそれを1つ選び、なければ `S` 自身を返す。 -/
noncomputable def next (𝔉 : Set (Set β)) (S : Set β) : Set β :=
  if h : ∃ T, T ∈ 𝔉 ∧ S ⊆ T ∧ T ≠ S then Classical.choose h else S

/-- 塔: `A` から出発して、`next` と「空でない鎖の合併」で到達できる集合。
塔に属することを帰納的な述語として定義する（`Tower 𝔉 A` の構成子が塔の閉包規則）。 -/
inductive Tower (𝔉 : Set (Set β)) (A : Set β) : Set β → Prop
  | base : Tower 𝔉 A A
  | next {S : Set β} : Tower 𝔉 A S → Tower 𝔉 A (next 𝔉 S)
  | sup (c : Set (Set β)) : (∀ S ∈ c, Tower 𝔉 A S) → IsChain c → (∃ S, S ∈ c) →
      Tower 𝔉 A (⋃₀ c)

variable {𝔉 : Set (Set β)} {A : Set β}

/-- `next` は大きくする（与える）。 -/
theorem subset_next (S : Set β) : S ⊆ next 𝔉 S := by
  unfold next
  split
  · next h => exact (Classical.choose_spec h).2.1
  · exact Set.subset_refl S

/-- `next` は `𝔉` から出ない（与える）。 -/
theorem next_mem {S : Set β} (hS : S ∈ 𝔉) : next 𝔉 S ∈ 𝔉 := by
  unfold next
  split
  · next h => exact (Classical.choose_spec h).1
  · exact hS

/-- 問題21: 塔の元は `𝔉` に属し、`A` を含むことを示せ。
塔についての帰納法（`induction hS with`）で、構成子 `base`・`next`・`sup` ごとに示す。 -/
theorem Tower.mem (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {S : Set β} (hS : Tower 𝔉 A S) : S ∈ 𝔉 ∧ A ⊆ S :=
  sorry

/-- 極点: 自分より真に小さい塔の元 `T` について、`next T` も自分に収まる。 -/
def Extreme (𝔉 : Set (Set β)) (A C : Set β) : Prop :=
  ∀ T, Tower 𝔉 A T → T ⊆ C → T ≠ C → next 𝔉 T ⊆ C

/-- 問題22: 塔の元 `C` が極点なら、どの塔の元 `T` も `T ⊆ C` か `next C ⊆ T` であることを示せ。

ヒント: `T` についての帰納法。
* `base`: 問題21で `A ⊆ C`
* `next T`: 帰納法の仮定で場合分けし、`T ⊆ C` の場合はさらに `T = C` かどうかで分ける
  （`T ≠ C` なら極点の定義が使える）
* `sup c`: 「`c` のすべてが `C` に含まれる」かどうかで分ける -/
theorem Extreme.dichotomy (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hCT : Tower 𝔉 A C) (hC : Extreme 𝔉 A C) {T : Set β}
    (hT : Tower 𝔉 A T) : T ⊆ C ∨ next 𝔉 C ⊆ T :=
  sorry

/-- 問題23: 塔の元はすべて極点であることを示せ。

ヒント: `C` についての帰納法。
* `base`: `A` より真に小さい塔の元はない
* `next C`: 問題22を `C` に使う
* `sup c`: `T ≠ ⋃₀ c` から、`T` に含まれない `S ∈ c` が取れる。
  問題22を `S` に使うと `T ⊆ S`（かつ `T ≠ S`）となり、`S` の極点性が使える -/
theorem Tower.extreme (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hC : Tower 𝔉 A C) : Extreme 𝔉 A C :=
  sorry

/-- 問題24: 塔は鎖であることを示せ（問題22・23から直ちに出る）。 -/
theorem Tower.isChain (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : IsChain {S | Tower 𝔉 A S} :=
  sorry

/-- 問題25（Zorn の補題）: 極大元の存在を示せ。

方針: 塔全体の合併 `M` は（問題24により）それ自身塔の元なので、`next M` も塔の元で
`next M ⊆ M`。`M` より真に大きい `N ∈ 𝔉` があったとすると、`next` の定義により
`next M` は `M` より真に大きい元になり、矛盾する（`dif_pos` で `next` の `if` を開く）。 -/
theorem exists_maximal (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : ∃ M, M ∈ 𝔉 ∧ A ⊆ M ∧ ∀ N, N ∈ 𝔉 → M ⊆ N → N = M :=
  sorry

end Zorn

namespace Filter

variable {α : Type}

/-- 問題26（超フィルター補題）: 空集合を含まないフィルターは超フィルターに延長できることを示せ。

方針: 「空集合を含まないフィルターの `sets`」の全体 `P : Set (Set (Set α))` に Zorn の補題を使う
（鎖の合併もフィルターの3条件を満たし、空集合を含まない）。極大元 `M` が超フィルターでないとして、
`s ∉ M`・`sᶜ ∉ M` となる `s` を取ると、`{t | ∃ m ∈ M, m ∩ s ⊆ t}` が
`M` より真に大きい `P` の元になり、極大性に反する。 -/
theorem exists_ultra (F : Filter α) (hF : (∅ : Set α) ∉ F) :
    ∃ G : Filter α, G.IsUltra ∧ F.sets ⊆ G.sets :=
  sorry

end Filter

/-! ## Part H: 主定理のコンパクト版

フィルター `F` が点 `a` に**収束する**とは、`a` のどの開近傍も `F` に属すること。
コンパクト性は超フィルターの収束で特徴づけられる（問題27・28）。
一様空間では、全有界な集合を含む超フィルターは**コーシー**になる（問題31）。
あとは、コーシーで各点収束するフィルターが一様収束すること（問題32）を示せば、
主定理（全有界版）からコンパクト版が出る。
-/

section Compact

/-- フィルターの収束。 -/
def Filter.ConvergesTo {X : Type} [TopologicalSpace X] (F : Filter X) (a : X) : Prop :=
  ∀ U, IsOpen U → a ∈ U → U ∈ F

variable {X : Type} [TopologicalSpace X]

/-- 問題27: `K` を含む超フィルターがすべて `K` の点に収束するなら、`K` はコンパクトであることを示せ。

方針: 開被覆 `U` が有限部分被覆を持たないと仮定する。
`{s | ∃ L : List I, {a | a ∈ K ∧ ∀ i ∈ L, a ∉ U i} ⊆ s}` は空集合を含まないフィルターになる
（空集合を含むなら `L` が有限部分被覆を与える。`Set.finite_of_list` を使う）。
これを超フィルターに延長して極限 `a ∈ K` を取ると、`a ∈ U i` なる `i` について
`U i` とその補集合の両方が属してしまう。 -/
theorem isCompact_of_ultra {K : Set X}
    (h : ∀ F : Filter X, F.IsUltra → K ∈ F → ∃ a, a ∈ K ∧ F.ConvergesTo a) : IsCompact K :=
  sorry

/-- 問題28: コンパクト集合を含む超フィルターは、その集合の点に収束することを示せ。

方針: 収束先がないと仮定すると、`K` の各点 `a` に `F` に属さない開近傍が取れる
（添字型は部分型 `{a // a ∈ K}`）。有限部分被覆を取ると、各片の補集合は `F` に属し
（超フィルター）、問題20でその共通部分と `K` の共通部分も属するが、それは空である。 -/
theorem IsCompact.ultra_converges {K : Set X} (hK : IsCompact K) {F : Filter X}
    (hF : F.IsUltra) (hKF : K ∈ F) : ∃ a, a ∈ K ∧ F.ConvergesTo a :=
  sorry

/-- 問題29: 超フィルターに属する集合が有限個の集合で覆われるなら、そのどれかが属することを示せ。

ヒント: リストについての再帰。先頭 `A` が属さなければ `Aᶜ` が属するので、
`s ∩ Aᶜ` を残りのリストで覆う。 -/
theorem Filter.IsUltra.mem_of_cover {α : Type} {F : Filter α} (hF : F.IsUltra) :
    ∀ (L : List (Set α)) (s : Set α), s ∈ F → (∀ a ∈ s, ∃ A ∈ L, a ∈ A) → ∃ A ∈ L, A ∈ F :=
  sorry

variable {α : Type} [UniformSpace α]

/-- 問題30: 一様空間のコンパクト集合は全有界であることを示せ。

ヒント: 対称な半分 `W`（問題1）を取り、各点 `a` の周りに `W`-球に収まる開集合（問題4）を選んで
`K` を覆う。有限部分被覆の各片は `V`-小さい。 -/
theorem IsCompact.totallyBounded {K : Set α} (hK : IsCompact K) : TotallyBounded K :=
  sorry

/-- コーシーフィルター: どの近縁 `V` についても、`V`-小さい集合が属する。 -/
def Filter.Cauchy (F : Filter α) : Prop := ∀ V ∈ 𝓤 α, ∃ A, A ∈ F ∧ Small V A

/-- 問題31: 全有界な集合を含む超フィルターはコーシーであることを示せ（問題29を使う）。 -/
theorem Filter.IsUltra.cauchy {F : Filter α} (hF : F.IsUltra) {s : Set α}
    (hs : TotallyBounded s) (hsF : s ∈ F) : F.Cauchy :=
  sorry

end Compact

section AscoliCompact

variable {X Y : Type} [UniformSpace Y]

/-- 問題32: コーシーフィルターが各点で `φ` に収束するなら、一様収束の位相で `φ` に収束することを示せ。

方針: 開集合 `𝒪 ∋ φ` は `unifRel V`-球を含む。`V` の半分 `W` を取り、
`unifRel W`-小さい `A ∈ F` を取れば `A ⊆ 𝒪` となる。実際 `f ∈ A` と点 `x` について、
`φ x` の近くに値をとる `g ∈ A` が（`F` が空集合を含まないので）取れ、
`(φ x, g x) ∈ W` と `(g x, f x) ∈ W` をつなげばよい。 -/
theorem Filter.Cauchy.convergesTo_of_pointwise {F : Filter (X → Y)} (hF : F.Cauchy)
    (hne : (∅ : Set (X → Y)) ∉ F) (φ : X → Y)
    (hφ : ∀ x, (F.map fun f => f x).ConvergesTo (φ x)) : F.ConvergesTo φ :=
  sorry

variable [TopologicalSpace X]

/-- 問題33（主定理・Ascoli の定理、コンパクト版）:
コンパクト空間 `X` から一様空間 `Y` への写像の族 `H` が等連続で、各点での値の集合が
コンパクト集合に含まれ（相対コンパクト）、`H` が一様収束の位相で閉なら、
`H` は一様収束の位相でコンパクトであることを示せ。

方針: 問題27に持ち込む。`H` を含む超フィルター `F` は、主定理（問題11）と問題30・31によりコーシー。
各点 `x` での像フィルターは超フィルター（問題19）で、コンパクト集合を含むので
収束する（問題28）。その極限を並べた `φ` に `F` は一様収束し（問題32）、
`H` が閉なので `φ ∈ H`。 -/
theorem ascoli_compact [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, ∃ K : Set Y, IsCompact K ∧ (fun f => f x) '' H ⊆ K) (hcl : IsClosed H) :
    IsCompact H :=
  sorry

end AscoliCompact

-- できたら確認: 主定理（全有界版・コンパクト版）が使う公理
-- #print axioms ascoli
-- #print axioms ascoli_compact
