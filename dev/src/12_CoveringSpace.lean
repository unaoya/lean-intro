import «07_ExercisesSol»
import «08_RealSol»

/-! # 発展演習: 位相空間の被覆

`08_Real.lean` と `11_Covering.lean` のあとに読む演習問題集。
`11_Covering.lean` でグラフの上に組み立てた被覆の理論を、位相空間の上で組み立て直す。
この章の目標は**ホモトピーの持ち上げ定理**（問題19）で、続く `13_FundamentalGroupoid.lean` で
これを使って円周の基本群が整数の群と同型であることを示す。

## グラフ版との違い

グラフ版では、道の持ち上げがリストの長さの帰納法一発で済んだ。位相空間では、道は区間 $[0, 1]$ からの
連続写像なので、ここに解析が要る。この章の仕事は、ほぼすべてこの一点に集まっている。

1. 区間を細かく切って、各小片の像が均等被覆近傍に収まるようにする
   （区間のコンパクト性とルベーグ数の補題。`08_Real.lean` Part G）
2. 小片ごとに持ち上げて、つなぐ（貼り合わせ補題）
3. つないだものが連続であることを示す

この章では、区間を 2 等分していく帰納法をとる。長さ $2^{-n}$ の区間ごとに像が小さければ、
区間の前半と後半を別々に持ち上げ、$t = 1/2$ で貼り合わせればよい（問題15）。

## 前提

* 実数は `08_Real.lean` の完備順序体 `R`、単位区間 $[0, 1]$ はその部分空間である
* 部分空間・積の位相は `07_Exercises.lean` Part 6 のものを使う。そこではどれも
  「射影をすべて連続にする最も粗い位相」として上から定義されていた。
  この章は、その上で具体的な議論ができる形の補題（Part A）から始める
* 前の章は解答ファイル（`07_ExercisesSol.lean`・`08_RealSol.lean`）を import する。
  前の章の問題が解けていなくても、この章は使える

## 構成

* Part A: 部分空間と積
* Part B: 閉集合と貼り合わせ
* Part C: 単位区間
* Part D: 被覆と局所的な持ち上げ
* Part E: 持ち上げ定理

山場は Part D の局所的な持ち上げ（問題15）と、Part E のホモトピーの持ち上げ（問題19）である。

## 進め方

`sorry` を自分の証明で置き換える。解答は `12_CoveringSpaceSol.lean` にある。
与えてある宣言（`sorry` のないもの）も、問題を解くときに使ってよい。
-/

namespace CovSpace
/-! ## Part A: 部分空間と積

`07_Exercises.lean` Part 6 の部分空間・積の位相は、始位相——「射影をすべて連続にする最も粗い位相」——
として上から定義されていた。この定義は、連続写像の判定（普遍性）には便利だが、
開集合が具体的にどんな形をしているかは定義から読めない。この Part では、以後の議論に要る
具体的な事実を取り出す。

* 部分空間への写像・部分空間からの写像の連続性（07 の問題33・35 の特殊化として与える）
* **連続性の局所性**（問題2）: 各点に、そこへの制限が連続になる開近傍があれば連続
* **積の開集合は、各点のまわりに開集合の直積 `U × V` を含む**（問題4）

問題4 は `07_Exercises.lean` の問題36 と同じ発想で示す。「各点のまわりに開集合の直積を含む集合」の
全体が位相をなすこと（問題3）を示し、それを「始位相は最も粗い」（07 の問題33(2)）に使う。
-/

section


variable {X Y Z : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

/-! ### 部分空間 -/

theorem continuous_subtype_val {p : X → Prop} : Continuous (Subtype.val : Subtype p → X) :=
  continuous_fromInitial (Y := fun _ : Unit => X) (fun _ => tX)
    (fun _ => Subtype.val) ()

theorem continuous_subtype_mk {p : X → Prop} {f : Z → X} (hf : Continuous f)
    (h : ∀ z, p (f z)) : Continuous (fun z => (⟨f z, h z⟩ : Subtype p)) :=
  (continuous_toInitial_iff (Y := fun _ : Unit => X) (fun _ => tX)
    (fun _ => Subtype.val) tZ _).mpr fun _ => hf

theorem continuous_restrict {p : X → Prop} {f : X → Y} (hf : Continuous f) :
    Continuous (fun a : Subtype p => f a.1) :=
  Continuous.comp hf continuous_subtype_val

/-- 問題1: 開集合への制限で開な集合は、全体でも開であることを示せ。

ヒント: `07_Exercises.lean` の問題36（`isOpen_subtype_iff`）で `s = Subtype.val ⁻¹' u` と書き、
問題の集合が `W ∩ u` に等しいことを示す。 -/
theorem isOpen_of_subtype_open {W : Set X} (hW : IsOpen W) {s : Set (Subtype W)}
    (hs : IsOpen s) : IsOpen {x | ∃ h : x ∈ W, (⟨x, h⟩ : Subtype W) ∈ s} :=
  sorry

/-- 問題2: **連続性は局所的**: 各点に、そこへの制限が連続になる開近傍があれば連続であることを示せ。

ヒント: `06_Topology.lean` の `isOpen_of_nhds` を使う。点 `x` の開近傍 `W` について、
制限の逆像を問題1で全体の開集合に持ち上げる。 -/
theorem continuous_of_locally {f : X → Y}
    (h : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ Continuous (fun a : Subtype W => f a.1)) :
    Continuous f :=
  sorry

/-! ### 積 -/

section Prod

variable {A B C : Type} [tA : TopologicalSpace A] [tB : TopologicalSpace B] [tC : TopologicalSpace C]

theorem continuous_fst : Continuous (@Prod.fst A B) :=
  continuous_fromInitial (Y := fun b => cond b A B)
    (fun b => match b with | true => tA | false => tB)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) true

theorem continuous_snd : Continuous (@Prod.snd A B) :=
  continuous_fromInitial (Y := fun b => cond b A B)
    (fun b => match b with | true => tA | false => tB)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) false

theorem continuous_prod_mk {f : C → A} {g : C → B} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => (f z, g z)) :=
  (continuous_toInitial_iff (Y := fun b => cond b A B)
    (fun b => match b with | true => tA | false => tB)
    (fun b => match b with | true => Prod.fst | false => Prod.snd) tC _).mpr fun b =>
    match b with
    | true => hf
    | false => hg

end Prod

/-- 問題3: 開集合の直積を含む集合の全体は位相をなすことを示せ。

ヒント: 共通部分では直積 `U₁ ∩ U₂`・`V₁ ∩ V₂` を取る。合併では、点が属する 1 つの集合の直積をそのまま使う。 -/
@[reducible] def rectTop : TopologicalSpace (X × Y) where
  IsOpen W := ∀ p ∈ W, ∃ U V, IsOpen U ∧ IsOpen V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧
    ∀ q : X × Y, q.1 ∈ U → q.2 ∈ V → q ∈ W
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- 問題4: （発展）**積の開集合は、各点のまわりに開集合の直積を含む**ことを示せ。

ヒント: 2 つの射影が問題3の位相に関して連続であることを示し、`07_Exercises.lean` の
`initial_coarsest`（問題33(2)）に渡す。型推論の都合で、位相は `(t' := @rectTop X Y tX tY)` と明示する。 -/
theorem exists_rect {W : Set (X × Y)} (hW : IsOpen W) {p : X × Y} (hp : p ∈ W) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ q : X × Y, q.1 ∈ U → q.2 ∈ V → q ∈ W :=
  sorry

end


/-! ## Part B: 閉集合と貼り合わせ

区間を半分ずつ使ってつないだ写像の連続性は、**貼り合わせ補題**（問題8）で示す。
空間が 2 つの閉集合 `A`・`B` で覆われていれば、写像の連続性は、`A` と `B` への制限の連続性に
帰着する。証明は閉集合の言葉で書く: 閉集合の逆像を `A` 側と `B` 側に分け、それぞれが閉であることを示す。
-/

section

open CompleteOrderedField

variable {X Y Z : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

theorem isClosed_inter {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ t) := by
  have e : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
    apply Set.ext; intro x
    constructor
    · intro h
      by_cases hs' : x ∈ s
      · exact .inr fun ht' => h ⟨hs', ht'⟩
      · exact .inl hs'
    · intro h ⟨h1, h2⟩
      rcases h with h | h
      · exact h h1
      · exact h h2
  show IsOpen (s ∩ t)ᶜ
  rw [e]; exact isOpen_union hs ht

/-- 問題5: 2 つの閉集合の合併は閉であることを示せ。

ヒント: 合併の補集合は補集合の共通部分。 -/
theorem isClosed_union {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) :=
  sorry

/-- 問題6: 閉集合の逆像が閉なら連続であることを示せ。

ヒント: 開集合 `s` について `sᶜ` は閉（`Set.compl_compl`）。`f ⁻¹' s = (f ⁻¹' sᶜ)ᶜ`。 -/
theorem continuous_of_closed {f : X → Y} (h : ∀ s, IsClosed s → IsClosed (f ⁻¹' s)) :
    Continuous f :=
  sorry

theorem isClosed_preimage {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) := hf _ hs

/-- 問題7: 閉集合の部分空間で閉な集合は、全体でも閉であることを示せ。

ヒント: `isOpen_subtype_iff` を補集合に使い、問題の集合を `A ∩ uᶜ` と書き直す。 -/
theorem isClosed_of_subtype_closed {A : Set X} (hA : IsClosed A) {s : Set (Subtype A)}
    (hs : IsClosed s) : IsClosed {x | ∃ h : x ∈ A, (⟨x, h⟩ : Subtype A) ∈ s} :=
  sorry

/-- 問題8: **貼り合わせ補題**: 2 つの閉集合で覆われた空間上の写像は、それぞれへの制限が連続なら連続であることを示せ。

ヒント: 問題6を使う。閉集合の逆像を `A` 側と `B` 側の合併に分け、問題7と問題5。 -/
theorem continuous_of_closed_cover {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) {f : X → Y}
    (hfA : Continuous (fun a : Subtype A => f a.1)) (hfB : Continuous (fun a : Subtype B => f a.1)) :
    Continuous f :=
  sorry

/-! ### 実数の閉集合

貼り合わせでは、区間を `t ≤ 1/2` と `1/2 ≤ t` の 2 つの閉集合に分ける。
-/

variable {R : Type} [CompleteOrderedField R]

/-- 問題9: 半直線 `{x | x ≤ c}` は閉であることを示せ。

ヒント: 補集合の点 `x`（`c < x`）のまわりには、半径 `x - c` の近傍が収まる。`abs_lt` を使う。 -/
theorem isClosed_le_const (c : R) : IsClosed ({x | x ≤ c} : Set R) :=
  sorry

theorem isClosed_ge_const (c : R) : IsClosed ({x | c ≤ x} : Set R) := by
  intro x hx
  have hx' : x < c := not_le.mp hx
  refine ⟨c - x, sub_pos.mpr hx', fun y hy hyc => ?_⟩
  have h1 := add_lt_add_right (abs_lt.mp hy).2 x
  rw [sub_add_cancel, sub_add_cancel] at h1
  exact not_le.mpr h1 hyc

end


/-! ## Part C: 単位区間

単位区間 `UI R` は、`R` の部分集合 `[0, 1]` を部分型にしたもの（位相は部分空間位相）である。
2 等分の帰納法のために、前半・後半への縮小 `halfL t = t / 2`・`halfR t = (t + 1) / 2` と、
$2^{-n}$ を表す `halfPow n` を用意する。問題12 は、`08_Real.lean` のアルキメデス性から出る。
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

/-- 単位区間 `[0, 1]`（実数の部分空間）。 -/
abbrev UI (R : Type) [CompleteOrderedField R] : Type := Subtype (fun t : R => t ∈ Icc (0 : R) 1)

theorem zero_le_one' : (0 : R) ≤ 1 := le_of_lt zero_lt_one

theorem le_of_eq' {a b : R} (h : a = b) : a ≤ b := h ▸ le_refl a

def ui0 : UI R := ⟨0, le_refl 0, zero_le_one'⟩
def ui1 : UI R := ⟨1, zero_le_one', le_refl 1⟩

theorem UI.ext {s t : UI R} (h : s.1 = t.1) : s = t := by
  cases s; cases t; cases h; rfl

/-! ### 半分と 2 倍の計算 -/

theorem div_two_le_div_two {a b : R} (h : a ≤ b) : a / 2 ≤ b / 2 :=
  mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos zero_lt_two))

theorem zero_div_two : (0 : R) / 2 = 0 := zero_mul _

theorem two_div_two : (2 : R) / 2 = 1 := mul_inv_cancel 2 two_ne_zero

theorem two_mul_div_two (t : R) : 2 * t / 2 = t := by
  rw [mul_comm]; exact mul_div_cancel two_ne_zero

theorem two_mul_half : (2 : R) * (1 / 2) = 1 := mul_div_cancel_left 1 two_ne_zero

theorem half_nonneg' : (0 : R) ≤ 1 / 2 := le_of_lt (half_pos zero_lt_one)

theorem half_le_one : (1 : R) / 2 ≤ 1 := le_of_lt (half_lt_self zero_lt_one)

theorem add_div_two (a b : R) : (a + b) / 2 = a / 2 + b / 2 := add_mul a b _

theorem sub_div_two (a b : R) : (a - b) / 2 = a / 2 - b / 2 := sub_mul a b _

theorem abs_div_two (a : R) : abs (a / 2) = abs a / 2 := by
  rw [div_def, abs_mul, abs_of_nonneg (le_of_lt (inv_pos zero_lt_two))]; rfl

theorem two_mul_le_two_mul {a b : R} (h : a ≤ b) : 2 * a ≤ 2 * b :=
  mul_le_mul_of_nonneg_left h (le_of_lt zero_lt_two)

theorem two_mul_one : (2 : R) * 1 = 2 := mul_one 2

/-- `t / 2 ∈ [0, 1]`。 -/
def halfL (t : UI R) : UI R :=
  ⟨t.1 / 2, le_trans _ _ _ (le_of_eq' zero_div_two.symm) (div_two_le_div_two t.2.1),
    le_trans _ _ _ (div_two_le_div_two t.2.2) half_le_one⟩

/-- `(t + 1) / 2 ∈ [0, 1]`。 -/
def halfR (t : UI R) : UI R :=
  ⟨(t.1 + 1) / 2,
    le_trans _ _ _ half_nonneg' (by
      have := div_two_le_div_two (add_le_add_right t.2.1 1)
      rwa [zero_add] at this),
    by
      have := div_two_le_div_two (add_le_add_right t.2.2 1)
      rwa [← two_def, two_div_two] at this⟩

theorem halfL_one : halfL (ui1 : UI R) = halfR ui0 := UI.ext (by show (1 : R) / 2 = (0 + 1) / 2; rw [zero_add])

theorem halfL_zero : halfL (ui0 : UI R) = ui0 := UI.ext zero_div_two

/-- 問題10: `t ↦ t / 2` は連続であることを示せ。

ヒント: `continuous_subtype_mk` と、`08_Real.lean` の `continuous_mul`。 -/
theorem continuous_halfL : Continuous (halfL : UI R → UI R) :=
  sorry

theorem continuous_halfR : Continuous (halfR : UI R → UI R) :=
  continuous_subtype_mk (continuous_mul (continuous_add continuous_subtype_val (continuous_const _))
    (continuous_const _)) _

theorem two_mul_mem {t : R} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 2 * t ∈ Icc (0 : R) 1 :=
  ⟨by have := two_mul_le_two_mul h0; rwa [mul_zero] at this,
   by have := two_mul_le_two_mul h1; rwa [two_mul_half] at this⟩

theorem two_mul_sub_one_mem {t : R} (h0 : 1 / 2 ≤ t) (h1 : t ≤ 1) : 2 * t - 1 ∈ Icc (0 : R) 1 := by
  refine ⟨sub_nonneg.mpr ?_, ?_⟩
  · have := two_mul_le_two_mul h0; rwa [two_mul_half] at this
  · have := add_le_add_right (two_mul_le_two_mul h1) (-1)
    rw [two_mul_one, two_def, add_assoc, add_neg_cancel, add_zero] at this
    exact this

/-! ### 2 のべき -/

/-- `2⁻ⁿ`。 -/
noncomputable def halfPow : Nat → R
  | 0 => 1
  | n + 1 => halfPow n / 2

theorem halfPow_pos : ∀ n : Nat, (0 : R) < halfPow n
  | 0 => zero_lt_one
  | n + 1 => half_pos (halfPow_pos n)

theorem halfPow_le_one : ∀ n : Nat, (halfPow n : R) ≤ 1
  | 0 => le_refl 1
  | n + 1 => le_trans _ _ _ (le_of_lt (half_lt_self (halfPow_pos n))) (halfPow_le_one n)

/-- 問題11: `n · 2⁻ⁿ ≤ 1` を示せ。

ヒント: `n` の帰納法。`(n + 1) · 2⁻⁽ⁿ⁺¹⁾ = (n · 2⁻ⁿ + 2⁻ⁿ) / 2 ≤ (1 + 1) / 2`（`halfPow_le_one`）。 -/
theorem natCast_mul_halfPow_le : ∀ n : Nat, natCast n * (halfPow n : R) ≤ 1 :=
  sorry

/-- 問題12: 十分大きい `n` で `2⁻ⁿ < δ` となることを示せ。

ヒント: `08_Real.lean` のアルキメデス性で `δ⁻¹ < n` となる `n` を取ると `1 < n · δ`。問題11と比べる。 -/
theorem exists_halfPow_lt {δ : R} (hδ : 0 < δ) : ∃ n : Nat, (halfPow n : R) < δ :=
  sorry

end


/-! ## Part D: 被覆と局所的な持ち上げ

開集合 `U` が `p : E → X` で**均等に被覆される**（`EvenlyCovered`）とは、`p⁻¹ U` が互いに交わらない
開集合（シート）`V i` に分かれ、各シートが `p` で `U` と同相に写ることである。同相であることは、
逆写像 `s i` を与え、`U` の上で連続であることで表す。**被覆**（`CoveringMap`）は、連続写像であって、
底のどの点にも均等に被覆される開近傍があるもの。`11_Covering.lean` の `Covering` や
`06_Topology.lean` の `Homeomorph` と同じく、写像と性質を束ねた structure にする。

この Part の中心は**局所的な持ち上げ**（問題15）である。`F : Y × [0,1] → X` と、`F(·, 0)` の持ち上げ
`F0` が与えられ、`y₀` の近傍 `N` の上で「長さ $2^{-n}$ の区間ごとに像が均等被覆近傍に収まる」とする。
このとき `y₀` のより小さい近傍の上に、`F` の連続な持ち上げがある。証明は `n` の帰納法で、
`n = 0`（像が 1 つの均等被覆近傍に収まる場合）は問題14、`n + 1` は区間の前半と後半に分けて
帰納法の仮定を 2 回使い、`t = 1/2` で貼り合わせる。
-/

/-! ### 補足: 逆写像を `X` 全体の関数として持つ理由

シートの逆写像 `s i` は、本来は `U` から `V i` への写像である。ここでは `s i : X → E` と
`X` 全体の関数として持ち、`U` の外での値は使わない（連続性も `U` への制限で述べる）。
こうすると、`s i (F q)` のような合成を書くたびに「`F q ∈ U` の証明」を添えずに済む。
部分型を使うのは、連続性を述べるところだけになる。
-/

section

open CompleteOrderedField

/-- 問題13: 定数写像は連続であることを示せ。

ヒント: 逆像は、値が `s` に入るかどうかで `univ` か `∅`。 -/
theorem continuous_const_map {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (b : B) :
    Continuous (fun _ : A => b) :=
  sorry

variable {R : Type} [CompleteOrderedField R]
variable {E X : Type} [tE : TopologicalSpace E] [tX : TopologicalSpace X]

/-- 開集合 `U` が `p` で**均等に被覆される**: `p ⁻¹' U` は互いに交わらない開集合（シート）`V i` に
分かれ、各シートは `p` で `U` と同相に写る。`s i` はその逆写像（`U` の上だけで意味を持つ）。 -/
def EvenlyCovered (p : E → X) (U : Set X) : Prop :=
  ∃ (ι : Type) (V : ι → Set E) (s : ι → X → E),
    (∀ i, IsOpen (V i)) ∧
    (∀ e, p e ∈ U → ∃ i, e ∈ V i) ∧
    (∀ i j e, e ∈ V i → e ∈ V j → i = j) ∧
    (∀ i x, x ∈ U → s i x ∈ V i ∧ p (s i x) = x) ∧
    (∀ i e, e ∈ V i → s i (p e) = e) ∧
    (∀ i, Continuous (fun x : Subtype U => s i x.1))

/-- **被覆**: 連続写像であって、底のどの点にも均等に被覆される開近傍があるもの。 -/
structure CoveringMap (E X : Type) [TopologicalSpace E] [TopologicalSpace X] where
  toFun : E → X
  continuous_toFun : Continuous toFun
  evenly : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ EvenlyCovered toFun U

theorem sub_halfR (a b : R) : (a + 1) / 2 - (b + 1) / 2 = (a - b) / 2 := by
  rw [← sub_div_two, add_sub_add_right]

/-- 問題14: 局所的な持ち上げの基底: 像が 1 つの均等被覆近傍に収まるなら、シートの逆写像を合成すればよいことを示せ。

ヒント: `hsmall` を `τ = 0` に使うと、`N × [0,1]` 全体の像が 1 つの `U` に収まる。
`F0 y₀` を含むシート `V i` を取り、`N'` を「`N` の点で `F0` の値が `V i` に入るもの」（問題1で開）、
`G := s i ∘ F` とする。 -/
theorem lift_local_zero (p : CoveringMap E X) (Y : Type) [TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (N : Set Y) (hN : IsOpen N)
    (F0 : Y → E) (hF0 : Continuous (fun y : Subtype N => F0 y.1))
    (h0 : ∀ y ∈ N, p.toFun (F0 y) = F (y, ui0))
    (hsmall : ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ 1 → F (y, t) ∈ U)
    (y0 : Y) (hy0 : y0 ∈ N) : ∃ N' : Set Y, IsOpen N' ∧ y0 ∈ N' ∧ N' ⊆ N ∧ ∃ G : Y × UI R → E,
      (∀ y ∈ N', ∀ t, p.toFun (G (y, t)) = F (y, t)) ∧ (∀ y ∈ N', G (y, ui0) = F0 y) ∧
      Continuous (fun q : Subtype (fun q : Y × UI R => q.1 ∈ N') => G q.1) :=
  sorry

/-- 問題15: （発展）**局所的な持ち上げ**（2 等分の帰納法）。`y₀` の近傍 `N` の上で、長さ `2⁻ⁿ` の区間ごとに
`F` の像が均等被覆近傍に収まるなら、`y₀` のより小さい近傍の上に連続な持ち上げがあることを示せ。

ヒント: `n` についての再帰。`0` は問題14。`n + 1` では `F₁(y, t) = F(y, t/2)`・`F₂(y, t) = F(y, (t+1)/2)` とし、
`F₁` を `F0` から、`F₂` を `F₁` の持ち上げの終点 `G₁(·, 1)` から持ち上げる（長さの条件は縮小で半分になる）。
最後に `t ≤ 1/2` と `1/2 ≤ t` の 2 つの閉集合で貼り合わせる（問題8・問題9）。`t = 1/2` で両者が一致することに注意。
`if` による場合分けのために、証明の冒頭で `classical` とする。 -/
theorem lift_local (p : CoveringMap E X) : ∀ (n : Nat) (Y : Type) [TopologicalSpace Y]
    (F : Y × UI R → X), Continuous F → ∀ (N : Set Y), IsOpen N →
    ∀ (F0 : Y → E), Continuous (fun y : Subtype N => F0 y.1) →
    (∀ y ∈ N, p.toFun (F0 y) = F (y, ui0)) →
    (∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, t) ∈ U) →
    ∀ y0 ∈ N, ∃ N' : Set Y, IsOpen N' ∧ y0 ∈ N' ∧ N' ⊆ N ∧ ∃ G : Y × UI R → E,
      (∀ y ∈ N', ∀ t, p.toFun (G (y, t)) = F (y, t)) ∧ (∀ y ∈ N', G (y, ui0) = F0 y) ∧
      Continuous (fun q : Subtype (fun q : Y × UI R => q.1 ∈ N') => G q.1) :=
  sorry

end


/-! ## Part E: 持ち上げ定理

Part D の局所的な持ち上げから、3 つの定理を出す。

* **小ささの条件**（問題16）: 各点 `y₀` のある近傍と `n` について、Part D の仮定が成り立つ。
  区間のコンパクト性とルベーグ数から出る
* **道の持ち上げの一意性**（問題17）: 区間の連結性（`08_Real.lean` の `Icc_connected`）から出る
* **ホモトピーの持ち上げ**（問題19）と、その特別な場合（`Y` が 1 点）の**道の持ち上げ**（問題18）

問題19 では、持ち上げ `G` を点ごとに定義する: 各 `y` について、道 `t ↦ F(y, t)` を `F0 y` から
持ち上げた道の値を `G(y, t)` とする。連続性は局所的に示す（問題2）。各点のまわりでは、Part D の局所的な
持ち上げが連続で、一意性（問題17）によって `G` と一致するからである。
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {E X : Type} [tE : TopologicalSpace E] [tX : TopologicalSpace X]

/-- 問題16: （発展）小ささの条件: `y₀` のある近傍と `n` について、長さ `2⁻ⁿ` の区間ごとに像が均等被覆近傍に収まることを示せ。

ヒント: 各 `t` で `F(y₀, t)` の均等被覆近傍 `U` の逆像に問題4を使い、`N_t × J_t` を取る
（`J_t` は区間の開集合なので、`isOpen_subtype_iff` で `R` の開集合 `O_t` に直す）。区間のコンパクト性
（`isCompact_Icc`）で有限個の `t` に減らし、`N` をそれらの `N_t` の共通部分（`Set.interFin`）とする。
`δ` はルベーグ数（`lebesgue`）、`n` は問題12で取る。 -/
theorem exists_small (p : CoveringMap E X) {Y : Type} [tY : TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (y0 : Y) :
    ∃ N : Set Y, IsOpen N ∧ y0 ∈ N ∧ ∃ n : Nat, ∀ τ : UI R, ∃ U, EvenlyCovered p.toFun U ∧
      ∀ y ∈ N, ∀ t : UI R, abs (t.1 - τ.1) ≤ halfPow n → F (y, t) ∈ U :=
  sorry

/-- 問題17: **道の持ち上げの一意性**: 同じ道の 2 つの持ち上げは、始点が一致すれば一致することを示せ。

ヒント: `{t | f t = g t}` と `{t | f t ≠ g t}` がともに開であることを示し、`Icc_connected` を使う。
前者では、`f t` を含むシート `V i` を取ると、`f` と `g` がともに `V i` に入る近傍で `f = s i ∘ p ∘ f = s i ∘ p ∘ g = g`。 -/
theorem lift_unique (p : CoveringMap E X) {f g : UI R → E} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, p.toFun (f t) = p.toFun (g t)) (h0 : f ui0 = g ui0) : f = g :=
  sorry

/-- 1 点の空間の位相（開集合はすべて）。 -/
instance instTopUnit : TopologicalSpace Unit where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

/-- 問題18: **道の持ち上げの存在**: 始点の持ち上げを決めれば、道は持ち上がることを示せ。

ヒント: `Y` を 1 点の空間 `Unit` として、問題16・15。 -/
theorem exists_lift_path (p : CoveringMap E X) (γ : UI R → X) (hγ : Continuous γ) (e0 : E)
    (he : p.toFun e0 = γ ui0) :
    ∃ γ' : UI R → E, Continuous γ' ∧ (∀ t, p.toFun (γ' t) = γ t) ∧ γ' ui0 = e0 :=
  sorry

/-- 問題19: **ホモトピーの持ち上げ**: `F : Y × [0,1] → X` と `F(·, 0)` の連続な持ち上げから、`F` 全体の連続な持ち上げが得られることを示せ。

ヒント: 各 `y` で道 `t ↦ F(y, t)` の持ち上げ（問題18）を選び、`G(y, t)` をその値とする。連続性は問題2で局所的に示す:
点 `(y₀, t₀)` で問題16・15から `N' × [0,1]` 上の連続な持ち上げ `G'` を取ると、`y ∈ N'` では問題17により `G(y, ·) = G'(y, ·)`。 -/
theorem exists_lift_homotopy (p : CoveringMap E X) {Y : Type} [tY : TopologicalSpace Y]
    (F : Y × UI R → X) (hF : Continuous F) (F0 : Y → E) (hF0 : Continuous F0)
    (h0 : ∀ y, p.toFun (F0 y) = F (y, ui0)) :
    ∃ G : Y × UI R → E, Continuous G ∧ (∀ q, p.toFun (G q) = F q) ∧ ∀ y, G (y, ui0) = F0 y :=
  sorry

end

end CovSpace

/-! 解答（`12_CoveringSpaceSol.lean`）では、ホモトピーの持ち上げが依存する公理は
`propext`・`Classical.choice`・`Quot.sound` の 3 つだけである。
問題を解き終えたら、次の出力に `sorryAx` が残っていないことを確かめよ。
-/

#print axioms CovSpace.exists_lift_homotopy
