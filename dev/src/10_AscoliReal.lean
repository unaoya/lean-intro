import «08_RealSol»
import «09_AscoliSol»

/-! # 発展演習: 実数版 Arzelà–Ascoli の定理

`08_Real.lean`（実数）と `09_Ascoli.lean`（ブルバキ流 Ascoli の定理）の続き。
抽象的な Ascoli の定理から、解析の講義でおなじみの形を導く:

> **Arzelà–Ascoli の定理**: 閉区間 `[a, b]` 上の実数値関数の族が
> 一様有界かつ一様等連続なら、その族のどの関数列も、一様収束する部分列を持つ。

## 何が新しく要るか

`09_Ascoli.lean` の主定理（コンパクト版 `ascoli_compact`）を実数に使うには、
仮定を1つずつ実数の言葉で確かめればよい。Ascoli の議論そのものはやり直さない。

* 実数に一様構造を入れる（Part A）。`|a - b| < ε` で近縁を作る
* 各点での値の集合がコンパクト集合に入る——一様有界なら `[-M, M]` に入り、
  それがコンパクトであることは `08_Real.lean` の **Heine–Borel**（`isCompact_Icc`）である
* 等連続性を `ε`-論法の形で言い直す（Part C）

これで「閉集合版」（Part D）がすぐに出る。そこから、閉包を取って「相対コンパクト版」（Part F）、
さらに集積点と部分列を作って「点列版」（Part G）へ進み、最後に定義域を閉区間にする（Part H）。
逆向き（Part E）も `09_Ascoli.lean` の結果から出る。

## 構成

* Part A: 実数の一様構造
* Part B: 2つの位相の一致
* Part C: 用語の対応（等連続性・一様有界性）
* Part D: 実数版 Ascoli（閉集合版）
* Part E: 逆向き——コンパクトなら一様有界かつ等連続
* Part F: 相対コンパクト版（閉包）
* Part G: 点列版（一様収束する部分列）
* Part H: 閉区間上の関数（古典的な Arzelà–Ascoli の定理）

## 進め方

これまでと同じく、`sorry` を自分の証明で置き換える。解答は `10_AscoliRealSol.lean` にある。
このファイルは `08_Real.lean`・`09_Ascoli.lean` の**解答**を import しているので、
それらを解き終えていなくても、そこで示した定理をすべて使える。
-/

open CompleteOrderedField UniformSpace

variable {R : Type} [CompleteOrderedField R]

/-! ## Part A: 実数の一様構造

2点 `a`・`b` が「`ε` より近い」という関係 `{(a, b) | |a - b| < ε}` を含む関係を、近縁とする。
一様構造の5公理は、`08_Real.lean` の計算規則から出る。とくに `comp`（「半分」の近縁）は
三角不等式 `abs_sub_le` と `add_halves` による `ε/2` 論法である。
-/

/-- 問題1: 実数の一様構造が公理を満たすことを示せ。

ヒント: `inter_mem` では2つの `ε` の小さいほう（`CompleteOrderedField.min`・`lt_min`）を取る。
`comp` では `{p | abs (p.1 - p.2) < ε / 2}` を「半分」にする。 -/
instance realUniformSpace : UniformSpace R where
  Entourage := {V | ∃ ε, 0 < ε ∧ ∀ a b : R, abs (a - b) < ε → (a, b) ∈ V}
  univ_mem := sorry
  mono := sorry
  inter_mem := sorry
  refl := sorry
  symm := sorry
  comp := sorry

/-- 近縁 `{(a, b) | |a - b| < ε}`。 -/
def distLt (ε : R) : Set (R × R) := {p | abs (p.1 - p.2) < ε}

theorem distLt_mem {ε : R} (hε : 0 < ε) : distLt ε ∈ 𝓤 R := ⟨ε, hε, fun _ _ h => h⟩

/-! ## Part B: 2つの位相の一致

この時点で、実数には位相が**2つ**載っている。

* `08_Real.lean` で入れた `ε`-位相 `CompleteOrderedField.instTopologicalSpace`
* `09_Ascoli.lean` の instance `UniformSpace.toTopologicalSpace` が、Part A の一様構造から作る位相

どちらも「どの点のまわりにも `ε`-近傍が収まる集合が開」という同じ定義に見えるが、
定義の字面が違う（片方は近縁を経由する）ので、Lean にとっては別の項である。
`IsCompact (Icc a b)` と書くとインスタンス探索は後者を選び、`08_Real.lean` の
`isCompact_Icc a b`（前者についての定理）はそのままでは型が合わない。

そこで、2つの位相が**等しい**ことを示し（問題2）、その等式で定理を運ぶ（問題3）。
-/

/-! ### 補足（初読は飛ばしてよい）: インスタンスの菱形

同じ型に同じクラスのインスタンスが2通りの経路で作られる状況を、**菱形**（diamond）と呼ぶ。
mathlib では、一様構造のクラスが位相そのものをフィールドとして持ち、実数の一様構造を作るときに
「その位相は既存の位相と等しい」ことの証明を添える、という設計で菱形を避けている。
ここでは `09_Ascoli.lean` の定義を変えずに、等式を1本示して済ませる。
-/

/-- 開集合が一致する位相は等しい。フィールド `IsOpen` 以外は命題なので、
`IsOpen` が関数として等しければ構造全体が等しい。 -/
theorem TopologicalSpace.ext_iff_isOpen {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : ∀ s, t₁.IsOpen s ↔ t₂.IsOpen s) : t₁ = t₂ := by
  cases t₁
  cases t₂
  congr
  funext s
  exact propext (h s)

/-- 問題2: 一様構造から定まる位相は、`08_Real.lean` の `ε`-位相と等しいことを示せ。

ヒント: `TopologicalSpace.ext_iff_isOpen` で開集合の同値に還元する。
`|y - x|` と `|x - y|` の入れ替えに `abs_sub_comm` を使う。 -/
theorem uniform_topology_eq :
    (UniformSpace.toTopologicalSpace : TopologicalSpace R) =
      CompleteOrderedField.instTopologicalSpace :=
  sorry

/-- 問題3: Heine–Borel を、一様構造の位相についての主張に運べ。

ヒント: `rw [uniform_topology_eq]` でゴールの中の位相を書き換えてから、`isCompact_Icc`。 -/
theorem isCompact_Icc' (a b : R) : IsCompact (Icc a b) :=
  sorry

/-! ## Part C: 用語の対応

解析でふつうに使う `ε`-論法の形の定義を用意し、`09_Ascoli.lean` の定義と対応させる。
定義域 `X` はここでは一般の位相空間である。
-/

section Dictionary

variable {X : Type} [TopologicalSpace X]

/-- `ε`-論法での等連続性: どの点 `x` とどの `ε > 0` にも `x` の開近傍 `U` があって、
族のどの関数も `U` の上で `f x` から `ε` 以上ずれない。 -/
def EquicontinuousR (H : Set (X → R)) : Prop :=
  ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ y ∈ U, abs (f y - f x) < ε

/-- 一様有界: 族のすべての関数の値が、共通の `M` で抑えられる。 -/
def UniformlyBounded (H : Set (X → R)) : Prop := ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M

/-- 問題4: `ε`-論法の等連続性と、近縁による等連続性（`09_Ascoli.lean`）は同値であることを示せ。

ヒント: `⟹` では近縁 `V` に含まれる `ε`-関係を使い、`⟸` では近縁 `distLt ε` を使う。 -/
theorem equicontinuousR_iff {H : Set (X → R)} : EquicontinuousR H ↔ Equicontinuous H :=
  sorry

/-- 問題5: `|a| ≤ M` なら `a ∈ [-M, M]` であることを示せ（`neg_abs_le`・`le_abs_self`）。 -/
theorem mem_Icc_of_abs_le {a M : R} (h : abs a ≤ M) : a ∈ Icc (-M) M :=
  sorry

omit [TopologicalSpace X] in
/-- 問題6: 一様有界なら、各点での値の集合はコンパクト集合（`[-M, M]`）に含まれることを示せ。 -/
theorem UniformlyBounded.pointwise {H : Set (X → R)} (h : UniformlyBounded H) (x : X) :
    ∃ K : Set R, IsCompact K ∧ (fun f => f x) '' H ⊆ K :=
  sorry

/-! ## Part D: 実数版 Ascoli（閉集合版） -/

/-- 問題7（実数版 Ascoli の定理、閉集合版）: コンパクト空間上の実数値関数の族が
等連続・一様有界で、一様収束の位相で閉なら、コンパクトであることを示せ。
`09_Ascoli.lean` の `ascoli_compact` に、問題4・6を渡すだけである。 -/
theorem arzela_ascoli_closed [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) (hcl : IsClosed H) : IsCompact H :=
  sorry

/-! ## Part E: 逆向き——コンパクトなら一様有界かつ等連続

等連続性は `09_Ascoli.lean` の問題30（コンパクト ⇒ 全有界）と問題18（全有界 ⇒ 等連続）から出る。
一様有界性のために、「有限個の有界な集合の合併は有界」を用意する。
上界の最大値を取る代わりに、上界の絶対値の和を取ると、場合分けが減る。
-/

/-- 問題8: 有限個の有界な集合で覆われる集合は有界であることを示せ。
「`y` は `M` で抑えられる」を一般の述語 `B y M`（`M` について単調）として述べておき、
実数（問題9）と関数（問題11）の両方に使う。

ヒント: リストについての再帰。`A :: L` では、`s` のうち `A` に入らない点の集合に再帰し、
2つの上界 `M₁`・`M₂` から `abs M₁ + abs M₂` を作る。 -/
theorem bounded_of_cover {β : Type} (B : β → R → Prop)
    (hB : ∀ y M M', B y M → M ≤ M' → B y M') {s : Set β} :
    ∀ L : List (Set β), (∀ A ∈ L, ∃ M, ∀ y ∈ A, y ∈ s → B y M) →
      (∀ y ∈ s, ∃ A ∈ L, y ∈ A) → ∃ M, ∀ y ∈ s, B y M :=
  sorry

/-- 問題9: 実数の全有界集合は有界であることを示せ。

ヒント: `distLt 1` について小さい集合で覆い、問題8を使う。`s` の点 `a` を含む片は
`|a| + 1` で抑えられる（`abs_le_abs_add_abs_sub`）。 -/
theorem TotallyBounded.bounded {s : Set R} (hs : TotallyBounded s) :
    ∃ M, ∀ y ∈ s, abs y ≤ M :=
  sorry

/-- 問題10: コンパクト空間上の連続関数は有界であることを示せ。

ヒント: 値の集合 `f '' univ` はコンパクト（`IsCompact.image`）なので全有界（`IsCompact.totallyBounded`）。 -/
theorem bounded_of_continuous [CompactSpace X] {f : X → R} (hf : Continuous f) :
    ∃ M, ∀ x, abs (f x) ≤ M :=
  sorry

/-- 問題11（逆向き）: 連続関数からなる、一様収束の位相でコンパクトな族は、
一様有界かつ等連続であることを示せ。

ヒント: 一様有界性は、`unifRel (distLt 1)` について小さい片で族を覆い、問題8を使う。
族の関数 `g` を含む片は、`g` の上界（問題10）に `1` を足した数で抑えられる。 -/
theorem arzela_ascoli_converse [CompactSpace X] {H : Set (X → R)}
    (hc : ∀ f ∈ H, Continuous f) (hH : IsCompact H) :
    UniformlyBounded H ∧ EquicontinuousR H :=
  sorry

/-! ## Part F: 相対コンパクト版（閉包）

Part D の「閉」の仮定を外すため、族の**閉包**を取る。閉包も一様有界・等連続であることを示せば、
Part D から閉包がコンパクト、つまり族が相対コンパクトであることがわかる。
-/

/-- 閉包: どの開近傍も `s` と交わる点の全体。 -/
def closure {α : Type} [TopologicalSpace α] (s : Set α) : Set α :=
  {a | ∀ U, IsOpen U → a ∈ U → ∃ b, b ∈ U ∧ b ∈ s}

/-- 問題12: 集合は閉包に含まれることを示せ。 -/
theorem subset_closure {α : Type} [TopologicalSpace α] (s : Set α) : s ⊆ closure s :=
  sorry

/-- 問題13: 閉包は閉集合であることを示せ。

ヒント: `isOpen_of_nhds`（`06_Topology.lean`）。閉包の外の点 `a` には `s` と交わらない
開近傍 `U` があり、`U` の点はどれも閉包の外にある。 -/
theorem isClosed_closure {α : Type} [TopologicalSpace α] (s : Set α) : IsClosed (closure s) :=
  sorry

/-- 閉包の点の近くには、元の集合の点がある（一様収束の意味で）。 -/
theorem exists_near_of_mem_closure {X : Type} {H : Set (X → R)} {f : X → R}
    (hf : f ∈ closure H) {ε : R} (hε : 0 < ε) : ∃ g, g ∈ H ∧ ∀ x, abs (f x - g x) < ε := by
  have hV : unifRel (distLt ε) ∈ 𝓤 (X → R) := ⟨_, distLt_mem hε, fun _ h => h⟩
  have ⟨O, hO, hfO, hOV⟩ := exists_open_ball hV f
  have ⟨g, hgO, hgH⟩ := hf O hO hfO
  exact ⟨g, hgH, hOV g hgO⟩

omit [TopologicalSpace X] in
/-- 問題14: 一様有界な族の閉包は一様有界であることを示せ（上界は `M + 1` にしてよい）。 -/
theorem UniformlyBounded.closure {H : Set (X → R)} (h : UniformlyBounded H) :
    UniformlyBounded (closure H) :=
  sorry

/-- `a < ε/4`・`b < ε/2`・`c < ε/4` なら `a + b + c < ε`。 -/
theorem add_three_lt {a b c ε : R} (ha : a < ε / 2 / 2) (hb : b < ε / 2) (hc : c < ε / 2 / 2) :
    a + b + c < ε := by
  have h₁ := add_lt_add ha hc
  rw [add_halves] at h₁
  have h₂ := add_lt_add h₁ hb
  rw [add_halves] at h₂
  have e : a + b + c = a + c + b := by ac_rfl
  rw [e]
  exact h₂

/-- 問題15: 等連続な族の閉包は等連続であることを示せ。

ヒント: `ε/4`・`ε/2`・`ε/4` の3分割（`add_three_lt`）。閉包の関数 `f` に一様に `ε/4` 近い
族の関数 `g` を取り、`|f y - f x| ≤ |f y - g y| + |g y - g x| + |g x - f x|` とする。 -/
theorem EquicontinuousR.closure {H : Set (X → R)} (h : EquicontinuousR H) :
    EquicontinuousR (closure H) :=
  sorry

/-- 問題16（実数版 Ascoli の定理、相対コンパクト版）: コンパクト空間上の実数値関数の族が
等連続・一様有界なら、その閉包はコンパクトであることを示せ。 -/
theorem arzela_ascoli_closure [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) : IsCompact (closure H) :=
  sorry

/-! ## Part G: 点列版（一様収束する部分列）

コンパクト性から点列版へ進む。2段に分ける。

1. コンパクト集合の中の点列は**集積点** `g` を持つ: `g` のどの開近傍にも、
   どこまで先に行っても点列の項が入る（問題17）
2. 近傍を `1/(k+1)`-球と小さくしながら、その中に入る項を順に選ぶと、
   `g` に一様収束する部分列ができる（問題19）

2 で `1/(k+1) → 0` を使うところで、`08_Real.lean` の**アルキメデス性**（`exists_nat_gt`）が効く。
逆数の計算を避けるため、`1/(k+1)`-球を `{(a, b) | |a - b| * (k + 1) < 1}` の形で表す。
部分列の添字 `φ` は「`φ k < φ (k + 1)`」を満たす関数として表す。
-/

/-- 問題17: コンパクト集合の中の点列は集積点を持つことを示せ。

方針: 背理法。`K` のどの点 `g` にも、ある番号 `N g` から先の項が入らない開近傍 `U g` がある
（添字型は部分型 `{g // g ∈ K}`）。有限部分被覆の番号の和 `N` を取ると、
項 `u N` はどの `U g` にも入らないはずだが、`K` は覆われているので矛盾する。
番号の和は `(P.map N).sum`、和が各項以上であることはリストについての帰納法で示す。 -/
theorem IsCompact.exists_clusterPt {α : Type} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) {u : Nat → α} (hu : ∀ n, u n ∈ K) :
    ∃ g, g ∈ K ∧ ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U :=
  sorry

/-- 問題18: `ε⁻¹ < n` かつ `|d| * n < 1` なら `|d| < ε` であることを示せ。

ヒント: 背理法。`ε ≤ |d|` なら `1 = ε * ε⁻¹ < ε * n ≤ |d| * n < 1` となる。 -/
theorem lt_of_mul_natCast_lt_one {d ε n : R} (hε : 0 < ε) (hn : ε⁻¹ < n)
    (h : abs d * n < 1) : abs d < ε :=
  sorry

theorem natCast_succ_pos (k : Nat) : (0 : R) < natCast (k + 1) := by
  rw [natCast_succ]
  exact lt_of_le_of_lt (natCast_nonneg k) (lt_add_of_pos_right _ zero_lt_one)

theorem natCast_le_natCast {m n : Nat} (h : m ≤ n) : (natCast m : R) ≤ natCast n := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, natCast_add]
  have := add_le_add_left _ _ (natCast_nonneg k) (natCast m : R)
  rw [add_zero] at this
  exact this

/-- 近縁 `{(a, b) | |a - b| * (k + 1) < 1}`。 -/
def distInv (k : Nat) : Set (R × R) := {p | abs (p.1 - p.2) * natCast (k + 1) < 1}

theorem distInv_mem (k : Nat) : distInv (R := R) k ∈ 𝓤 R := by
  have hk := natCast_succ_pos (R := R) k
  refine ⟨(natCast (k + 1))⁻¹, inv_pos hk, fun a b h => ?_⟩
  have := mul_lt_mul_of_pos_left h hk
  rw [mul_comm (natCast (k + 1)) (natCast (k + 1))⁻¹, inv_mul_cancel (ne_of_lt hk).symm,
    mul_comm] at this
  exact this

/-- 問題19: 点列の集積点 `g` に一様収束する部分列を作れ。

方針:
1. 各 `k` と `N` について、`N` 以後の項で、`g` から一様に `distInv k`-近いものがある
   （`unifRel (distInv k)` について `exists_open_ball` で開近傍を取り、集積点の性質を使う）
2. その項の番号を `c k N` と `Classical.choose` で選び、`Nat.rec` で
   `φ 0 = c 0 0`、`φ (k + 1) = c (k + 1) (φ k + 1)` と再帰的に定める
3. `ε > 0` にはアルキメデス性で `ε⁻¹ < natCast N` となる `N` を取り、問題18を使う -/
theorem exists_subseq_tendsto {X : Type} {u : Nat → X → R} {g : X → R}
    (hg : ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

/-- 問題20（実数版 Ascoli の定理、点列版）: コンパクト空間上の等連続・一様有界な関数族の
どの関数列も、一様収束する部分列を持ち、その極限は連続であることを示せ。

ヒント: 閉包（問題16）の中で集積点を取り（問題17）、問題19。
極限の連続性は、閉包の等連続性（問題15）から出る。 -/
theorem arzela_ascoli_seq [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) {u : Nat → X → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : X → R,
      (∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (g y - g x) < ε) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

end Dictionary

/-! ## Part H: 閉区間上の関数（古典的な Arzelà–Ascoli の定理）

最後に、定義域を閉区間 `[a, b]` にする。閉区間は `R` の部分集合 `Icc a b` だが、
関数の定義域には型が要るので、部分型 `{x // x ∈ Icc a b}` を使い、部分空間位相を入れる。
-/

/-- 部分空間位相: 全体の開集合で切り取った集合を開とする。 -/
instance subspaceTopology {α : Type} [TopologicalSpace α] (p : α → Prop) :
    TopologicalSpace (Subtype p) where
  IsOpen s := ∃ U : Set α, IsOpen U ∧ ∀ x : Subtype p, x ∈ s ↔ x.1 ∈ U
  isOpen_univ := ⟨Set.univ, isOpen_univ, fun _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  isOpen_inter := fun _ _ ⟨U, hU, hsU⟩ ⟨V, hV, htV⟩ =>
    ⟨U ∩ V, isOpen_inter _ _ hU hV, fun x =>
      ⟨fun ⟨h₁, h₂⟩ => ⟨(hsU x).mp h₁, (htV x).mp h₂⟩,
       fun ⟨h₁, h₂⟩ => ⟨(hsU x).mpr h₁, (htV x).mpr h₂⟩⟩⟩
  isOpen_sUnion := fun S hS =>
    ⟨⋃₀ {U | IsOpen U ∧ ∀ x : Subtype p, x.1 ∈ U → x ∈ ⋃₀ S},
     isOpen_sUnion _ fun _ hU => hU.1, fun x =>
      ⟨fun ⟨s, hsS, hxs⟩ =>
        have ⟨U, hU, hsU⟩ := hS s hsS
        ⟨U, ⟨hU, fun y hy => ⟨s, hsS, (hsU y).mpr hy⟩⟩, (hsU x).mp hxs⟩,
       fun ⟨_, ⟨_, hU⟩, hxU⟩ => hU x hxU⟩⟩

/-- 問題21: 閉区間（部分空間）はコンパクト空間であることを示せ。

ヒント: 部分空間の開被覆 `W i` の各片を切り取る全体の開集合 `U i` を `Classical.choose` で選び、
`U` が `Icc a b` を覆うことから問題3で有限個に減らす。 -/
instance (a b : R) : CompactSpace {x // x ∈ Icc a b} where
  isCompact_univ := sorry

/-- 問題22: 古典的な**一様等連続性**（`δ` が点によらない）から、等連続性が出ることを示せ。

ヒント: 点 `x` の開近傍として `{y | |y - x| < δ}` を取る。これは `ball x δ` を切り取った集合で、
`ball x δ` の開性は `08_Real.lean` の `isOpen_ball`（問題2で位相を書き換えてから使う）。 -/
theorem equicontinuousR_of_uniform {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε) :
    EquicontinuousR H :=
  sorry

/-- 問題23（古典的な Arzelà–Ascoli の定理）: 閉区間上の実数値関数の族が一様有界かつ一様等連続なら、
そのどの関数列も一様収束する部分列を持つことを示せ（問題20・21・22）。 -/
theorem arzela_ascoli {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (hb : ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M)
    (heq : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε)
    {u : Nat → {x // x ∈ Icc a b} → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : {x // x ∈ Icc a b} → R,
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

/-! 解答（`10_AscoliRealSol.lean`）では、古典的な Arzelà–Ascoli の定理が依存する公理は
`propext`・`Classical.choice`・`Quot.sound` の3つだけである。実数の公理は `class` の引数なので
現れない。`09_Ascoli.lean` で自作した Zorn の補題（超フィルター補題）を経由していることは、
公理の一覧からは見えない——それは公理ではなく、証明された定理だからである。
問題を解き終えたら、次の出力に `sorryAx` が残っていないことを確かめよ。
-/

#print axioms arzela_ascoli
