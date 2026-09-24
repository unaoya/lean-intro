import «11_CoveringSol»
import «12_CoveringSpaceSol»

/-! # 発展演習: 基本亜群と円周

`12_CoveringSpace.lean` の持ち上げ定理を使って、位相空間の基本亜群とモノドロミーを組み立て、
**円周の基本群は整数の群と同型**（問題26）であることを示す。`11_Covering.lean`（グラフ版）の
Part C〜F と同じ道筋を位相空間でたどり直し、途中（Part D）で、グラフ版と位相版に共通する部分を
一度だけ書く枠組みを取り出す。

## グラフ版との対応

| `11_Covering.lean`（グラフ） | この章（位相空間） |
|---|---|
| 道 = 隣接条件つきの辺のリスト | 道 = $[0, 1]$ からの連続写像 |
| 連接 = リストの連結 | 連接 = 区間を半分ずつ使って貼り合わせる |
| 亜群の法則は、リストの等式から | 亜群の法則は、再パラメータ化の補題から |
| ホモトピー不変性は、正規形定理から | ホモトピー不変性は、ホモトピーの持ち上げから |
| 直線グラフ → 花束 | $\mathbb{R} \to S^1 = \mathbb{R}/\mathbb{Z}$ |
| 直線グラフは単連結（既約な閉道がない） | $\mathbb{R}$ は単連結（直線ホモトピー） |

## 構成

* Part A: 道
* Part B: ホモトピーと亜群の法則
* Part C: モノドロミー
* Part D: 共通の枠組み
* Part E: 円周
* Part F: π₁(S¹) ≃ ℤ

## 進め方

`sorry` を自分の証明で置き換える。解答は `13_FundamentalGroupoidSol.lean` にある。
前の章は解答ファイル（`11_CoveringSol.lean`・`12_CoveringSpaceSol.lean`）を import するので、
前の章の問題が解けていなくても、この章は使える。
-/

namespace CovSpace

/-! ## Part A: 道

道は、単位区間から連続な写像で、始点と終点を指定したもの（`Path x y`）である。2 本の道の**連接**は、
区間の前半で 1 本目を、後半で 2 本目を 2 倍の速さでたどる。この「半分ずつの貼り合わせ」を `glue` として
定義しておく（`12_CoveringSpace.lean` の局所的な持ち上げで使ったものと同じ形）。

道の**ホモトピー**は、端点を止めた連続な変形 `H : [0,1] × [0,1] → X` である。`H (s, t)` の `s` が道の
パラメータ、`t` が変形のパラメータ。

この Part の中心は**再パラメータ化の補題**（問題3）である。端点で一致する `φ, ψ : [0,1] → [0,1]` について、
`γ ∘ φ` と `γ ∘ ψ` はホモトピックになる。証明は直線ホモトピー `(1 - t) φ(s) + t ψ(s)` で、
単位区間が凸であることしか使わない。Part B の亜群の法則は、すべてこの補題に帰着する。
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

/-- 単位区間どうしの半分の貼り合わせ: `s ≤ 1/2` なら `f (2s)`、そうでなければ `g (2s - 1)`。 -/
noncomputable def glue {A : Type} (f g : UI R → A) (s : UI R) : A :=
  open Classical in
  if h : s.1 ≤ 1 / 2 then f ⟨2 * s.1, two_mul_mem s.2.1 h⟩
  else g ⟨2 * s.1 - 1, two_mul_sub_one_mem (le_of_lt (not_le.mp h)) s.2.2⟩

theorem glue_of_le {A : Type} (f g : UI R → A) {s : UI R} (h : s.1 ≤ 1 / 2) :
    glue f g s = f ⟨2 * s.1, two_mul_mem s.2.1 h⟩ := by
  unfold glue; rw [dif_pos h]

/-- 問題1: `1/2 ≤ s` なら貼り合わせは後半の値であることを示せ。境目 `s = 1/2` で両者が一致することを使う。

ヒント: `unfold glue` して `s.1 ≤ 1/2` かどうかで場合分けする。等号の場合は `s = 1/2` なので、
`⟨2 s⟩ = 1`・`⟨2 s - 1⟩ = 0` を `UI.ext` で示して書き換え、仮定 `f 1 = g 0` を使う。 -/
theorem glue_of_ge {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) {s : UI R} (h : 1 / 2 ≤ s.1) :
    glue f g s = g ⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ :=
  sorry

/-- 問題2: 貼り合わせは連続であることを示せ（パラメータつき版）。

ヒント: `12_CoveringSpace.lean` の貼り合わせ補題（`continuous_of_closed_cover`）を、第 2 成分が `1/2` 以下・以上の
2 つの閉集合に使う。それぞれの側では `glue_of_le`・問題1で関数を書き直し（`funext`）、連続性を示す。 -/
theorem continuous_glue_param {Z A : Type} [TopologicalSpace Z] [TopologicalSpace A]
    (f g : Z × UI R → A) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, f (z, ui1) = g (z, ui0)) :
    Continuous (fun q : Z × UI R => glue (fun s => f (q.1, s)) (fun s => g (q.1, s)) q.2) :=
  sorry

theorem continuous_glue {A : Type} [TopologicalSpace A] {f g : UI R → A}
    (hf : Continuous f) (hg : Continuous g) (hfg : f ui1 = g ui0) : Continuous (glue f g) := by
  have := continuous_glue_param (Z := Unit) (fun q => f q.2) (fun q => g q.2)
    (hf.comp continuous_snd) (hg.comp continuous_snd) (fun _ => hfg)
  exact this.comp (continuous_prod_mk (continuous_const_map ()) continuous_id)

/-- `x` から `y` への道。 -/
structure Path (x y : X) where
  toFun : UI R → X
  continuous_toFun : Continuous toFun
  source : toFun ui0 = x
  target : toFun ui1 = y

variable {x y z w : X}

theorem Path.ext {γ δ : Path (R := R) x y} (h : ∀ s, γ.toFun s = δ.toFun s) : γ = δ := by
  cases γ; cases δ
  have : _ := funext h
  subst this
  rfl

/-- 定数道。 -/
def Path.refl (x : X) : Path (R := R) x x :=
  ⟨fun _ => x, continuous_const_map x, rfl, rfl⟩

/-- 連接。 -/
noncomputable def Path.trans (γ : Path (R := R) x y) (δ : Path (R := R) y z) : Path (R := R) x z :=
  ⟨glue γ.toFun δ.toFun, continuous_glue γ.continuous_toFun δ.continuous_toFun
      (by rw [γ.target, δ.source]),
    by rw [glue_of_le (s := ui0) _ _ half_nonneg']
       exact (congrArg γ.toFun (UI.ext (mul_zero 2))).trans γ.source,
    by rw [glue_of_ge (s := ui1) _ _ (by rw [γ.target, δ.source]) half_le_one]
       exact (congrArg δ.toFun (UI.ext (show 2 * 1 - 1 = (1 : R) by
         rw [two_mul_one, two_def, add_sub_cancel]))).trans δ.target⟩

/-- 区間の反転 `s ↦ 1 - s`。 -/
def uiRev (s : UI R) : UI R :=
  ⟨1 - s.1, sub_nonneg.mpr s.2.2, by
    have := add_le_add_left _ _ (neg_le_neg s.2.1) 1
    rwa [neg_zero, add_zero] at this⟩

theorem continuous_uiRev : Continuous (uiRev : UI R → UI R) :=
  continuous_subtype_mk (continuous_sub (continuous_const _) continuous_subtype_val) _

theorem uiRev_zero : uiRev (ui0 : UI R) = ui1 := UI.ext (sub_zero 1)
theorem uiRev_one : uiRev (ui1 : UI R) = ui0 := UI.ext (sub_self 1)

/-- 逆道。 -/
def Path.symm (γ : Path (R := R) x y) : Path (R := R) y x :=
  ⟨fun s => γ.toFun (uiRev s), γ.continuous_toFun.comp continuous_uiRev,
    by show γ.toFun (uiRev ui0) = y; rw [uiRev_zero, γ.target],
    by show γ.toFun (uiRev ui1) = x; rw [uiRev_one, γ.source]⟩

/-- 道のホモトピー（端点を止める）。`H (s, t)` の `s` が道のパラメータ、`t` が変形のパラメータ。 -/
def Path.Homotopic (γ δ : Path (R := R) x y) : Prop :=
  ∃ H : UI R × UI R → X, Continuous H ∧ (∀ s, H (s, ui0) = γ.toFun s) ∧
    (∀ s, H (s, ui1) = δ.toFun s) ∧ (∀ t, H (ui0, t) = x) ∧ (∀ t, H (ui1, t) = y)

/-! ### 再パラメータ化の補題 -/

/-- 凸結合 `(1 - t) a + t b` は区間に入る。 -/
def uiMix (a b t : UI R) : UI R :=
  ⟨(1 - t.1) * a.1 + t.1 * b.1,
    add_nonneg (mul_nonneg _ _ (sub_nonneg.mpr t.2.2) a.2.1) (mul_nonneg _ _ t.2.1 b.2.1),
    by
      have h1 := mul_le_mul_of_nonneg_left a.2.2 (sub_nonneg.mpr t.2.2)
      have h2 := mul_le_mul_of_nonneg_left b.2.2 t.2.1
      have := add_le_add h1 h2
      rwa [mul_one, mul_one, sub_add_cancel] at this⟩

theorem uiMix_zero (a b : UI R) : uiMix a b ui0 = a :=
  UI.ext (show (1 - 0) * a.1 + 0 * b.1 = a.1 by rw [sub_zero, one_mul, zero_mul, add_zero])

theorem uiMix_one (a b : UI R) : uiMix a b ui1 = b :=
  UI.ext (show (1 - 1) * a.1 + 1 * b.1 = b.1 by rw [sub_self, zero_mul, one_mul, zero_add])

theorem uiMix_self (a t : UI R) : uiMix a a t = a :=
  UI.ext (show (1 - t.1) * a.1 + t.1 * a.1 = a.1 by rw [← add_mul, sub_add_cancel, one_mul])

theorem continuous_uiMix {Z : Type} [TopologicalSpace Z] {a b t : Z → UI R}
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun z => uiMix (a z) (b z) (t z)) :=
  continuous_subtype_mk (continuous_add
    (continuous_mul (continuous_sub (continuous_const _) (continuous_subtype_val.comp ht))
      (continuous_subtype_val.comp ha))
    (continuous_mul (continuous_subtype_val.comp ht) (continuous_subtype_val.comp hb))) _

/-- 問題3: **再パラメータ化の補題**: 端点で一致する `φ, ψ : [0,1] → [0,1]` について、`γ ∘ φ` と `γ ∘ ψ` はホモトピックであることを示せ。

ヒント: `H(s, t) := γ (uiMix (φ s) (ψ s) t)`（直線ホモトピー）。端点では `φ` と `ψ` の値が一致するので `uiMix_self`。 -/
theorem homotopic_reparam (γ : UI R → X) (hγ : Continuous γ) {φ ψ : UI R → UI R}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h0 : φ ui0 = ψ ui0) (h1 : φ ui1 = ψ ui1)
    (P Q : Path (R := R) x y) (hP : ∀ s, P.toFun s = γ (φ s)) (hQ : ∀ s, Q.toFun s = γ (ψ s)) :
    P.Homotopic Q :=
  sorry

end


/-! ## Part B: ホモトピーと亜群の法則

ホモトピックであることは同値関係で（問題6・7）、連接・逆道と両立する（問題8）。
亜群の法則（単位律・結合律・逆元律）は、両辺を**同じ道の再パラメータ化**として書き直し、
問題3を使って示す。たとえば定数道との連接 `refl · γ` は、`γ ∘ glue (定数 0) id` に等しい。

書き直しの計算は、貼り合わせと写像の合成が可換であること（問題4）に帰着する。
結合律（問題10）も、`1/4`・`3/4` のような数値計算をせず、貼り合わせどうしの等式だけで示せる。
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]
variable {x y z w : X}

/-! ### 貼り合わせの計算規則 -/

/-- 問題4: 写像を合成してから貼り合わせても、貼り合わせてから合成しても同じであることを示せ。

ヒント: `unfold glue` して `s.1 ≤ 1/2` で場合分けし、両辺の `dif_pos`・`dif_neg` を外す。 -/
theorem glue_comp {A B : Type} (h : A → B) (f g : UI R → A) (s : UI R) :
    h (glue f g s) = glue (fun u => h (f u)) (fun u => h (g u)) s :=
  sorry

theorem glue_congr {A : Type} {f f' g g' : UI R → A} (hf : ∀ u, f u = f' u) (hg : ∀ u, g u = g' u)
    (s : UI R) : glue f g s = glue f' g' s := by
  rw [funext hf, funext hg]

theorem glue_const {A : Type} {f g : UI R → A} {c : A} (hf : ∀ u, f u = c) (hg : ∀ u, g u = c)
    (s : UI R) : glue f g s = c := by
  unfold glue
  by_cases hs : s.1 ≤ 1 / 2
  · rw [dif_pos hs, hf]
  · rw [dif_neg hs, hg]

theorem glue_zero {A : Type} (f g : UI R → A) : glue f g ui0 = f ui0 := by
  rw [glue_of_le (s := ui0) _ _ half_nonneg']
  exact congrArg f (UI.ext (mul_zero 2))

theorem glue_one {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) : glue f g ui1 = g ui1 := by
  rw [glue_of_ge (s := ui1) _ _ hfg half_le_one]
  exact congrArg g (UI.ext (show 2 * 1 - 1 = (1 : R) by rw [two_mul_one, two_def, add_sub_cancel]))

/-- 問題5: 前半への縮小 `halfL` で貼り合わせを読むと、前半の写像になることを示せ。

ヒント: `glue_of_le` を `halfL u` に使い（`u / 2 ≤ 1/2`）、`2 * (u / 2) = u`（`mul_div_cancel_left`）。 -/
theorem glue_halfL {A : Type} (f g : UI R → A) (u : UI R) : glue f g (halfL u) = f u :=
  sorry

theorem glue_halfR {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) (u : UI R) :
    glue f g (halfR u) = g u := by
  have h : (1 : R) / 2 ≤ (u.1 + 1) / 2 := by
    have := div_two_le_div_two (add_le_add_right u.2.1 1)
    rwa [zero_add] at this
  rw [glue_of_ge (s := halfR u) _ _ hfg h]
  exact congrArg g (UI.ext (show 2 * ((u.1 + 1) / 2) - 1 = u.1 by
    rw [mul_div_cancel_left _ two_ne_zero, add_sub_cancel]))

theorem Path.trans_halfL (γ : Path (R := R) x y) (δ : Path (R := R) y z) (u : UI R) :
    (γ.trans δ).toFun (halfL u) = γ.toFun u := glue_halfL _ _ u

theorem Path.trans_halfR (γ : Path (R := R) x y) (δ : Path (R := R) y z) (u : UI R) :
    (γ.trans δ).toFun (halfR u) = δ.toFun u :=
  glue_halfR _ _ (by rw [γ.target, δ.source]) u

/-! ### 同値関係 -/

theorem Path.Homotopic.refl' (γ : Path (R := R) x y) : γ.Homotopic γ :=
  ⟨fun q => γ.toFun q.1, γ.continuous_toFun.comp continuous_fst, fun _ => rfl, fun _ => rfl,
    fun _ => γ.source, fun _ => γ.target⟩

/-- 問題6: ホモトピーは対称であることを示せ。

ヒント: `H(s, 1 - t)`（`uiRev`）。 -/
theorem Path.Homotopic.symm' {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : δ.Homotopic γ :=
  sorry

/-- 問題7: ホモトピーは推移的であることを示せ。

ヒント: 変形のパラメータ `t` の側で、2 つのホモトピーを問題2で貼り合わせる。 -/
theorem Path.Homotopic.trans' {γ δ ε : Path (R := R) x y} (h : γ.Homotopic δ) (k : δ.Homotopic ε) :
    γ.Homotopic ε :=
  sorry

/-! ### 連接・逆道との両立 -/

theorem continuous_swap {A B : Type} [TopologicalSpace A] [TopologicalSpace B] :
    Continuous (fun q : A × B => (q.2, q.1)) := continuous_prod_mk continuous_snd continuous_fst

/-- 問題8: 連接はホモトピーと両立することを示せ。

ヒント: 今度は道のパラメータ `s` の側で貼り合わせる。問題2は第 2 成分での貼り合わせなので、
成分を入れ替えて（`continuous_swap`）使う。 -/
theorem Path.Homotopic.trans_congr {γ γ' : Path (R := R) x y} {δ δ' : Path (R := R) y z}
    (h : γ.Homotopic γ') (k : δ.Homotopic δ') : (γ.trans δ).Homotopic (γ'.trans δ') :=
  sorry

theorem Path.Homotopic.symm_congr {γ γ' : Path (R := R) x y} (h : γ.Homotopic γ') :
    γ.symm.Homotopic γ'.symm := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  refine ⟨fun q => H (uiRev q.1, q.2), hH.comp (continuous_prod_mk
    (continuous_uiRev.comp continuous_fst) continuous_snd), fun s => h0 _, fun s => h1 _,
    fun t => ?_, fun t => ?_⟩
  · show H (uiRev ui0, t) = y; rw [uiRev_zero, hy]
  · show H (uiRev ui1, t) = x; rw [uiRev_one, hx]

/-! ### 亜群の法則（再パラメータ化の補題から） -/

theorem continuous_id' {A : Type} [TopologicalSpace A] : Continuous (fun a : A => a) :=
  continuous_id

/-- 問題9: 左単位律を示せ。

ヒント: 問題3を `φ = glue (fun _ => ui0) id`、`ψ = id` に使う。`refl · γ` の値が `γ (φ s)` であることは問題4。 -/
theorem Path.refl_trans (γ : Path (R := R) x y) : ((Path.refl x).trans γ).Homotopic γ :=
  sorry

theorem Path.trans_refl (γ : Path (R := R) x y) : (γ.trans (Path.refl y)).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) (fun _ => ui1))
    (ψ := fun u => u) (continuous_glue continuous_id' (continuous_const_map _) rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue γ.toFun (fun _ => y) s = γ.toFun (glue (fun u => u) (fun _ => ui1) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => rfl) (fun _ => γ.target.symm) s

/-- 問題10: （発展）結合律を示せ。

ヒント: `Γ := γ.trans (δ.trans ε)` とし、左辺を `Γ ∘ glue α β` と書く。ここで
`α = glue halfL (halfR ∘ halfL)`、`β = halfR ∘ halfR`。`Γ ∘ halfL = γ`、`Γ ∘ halfR = δ.trans ε`（`trans_halfL`・`trans_halfR`）。 -/
theorem Path.trans_assoc (γ : Path (R := R) x y) (δ : Path (R := R) y z) (ε : Path (R := R) z w) :
    ((γ.trans δ).trans ε).Homotopic (γ.trans (δ.trans ε)) :=
  sorry

/-- 問題11: 逆道を先にたどると定数道にホモトピックであることを示せ。

ヒント: 問題3を `φ = glue uiRev id`、`ψ = 定数 1` に使う。 -/
theorem Path.symm_trans (γ : Path (R := R) x y) : (γ.symm.trans γ).Homotopic (Path.refl y) :=
  sorry

theorem Path.trans_symm (γ : Path (R := R) x y) : (γ.trans γ.symm).Homotopic (Path.refl x) := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) uiRev)
    (ψ := fun _ => ui0) (continuous_glue continuous_id' continuous_uiRev uiRev_zero.symm)
    (continuous_const_map _) (glue_zero _ _) (by rw [glue_one _ _ uiRev_zero.symm, uiRev_one]) _ _
    (fun s => ?_) (fun s => γ.source.symm)
  show glue γ.toFun (fun u => γ.toFun (uiRev u)) s = γ.toFun (glue (fun u => u) uiRev s)
  rw [glue_comp γ.toFun]

end


/-! ## Part C: モノドロミー

道のホモトピー類を商型 `Quot` で作り（`PathClass`）、連接と逆道を入れる。亜群の法則は Part B から出る。

被覆 `p` について、点 `x` の上のファイバーの点 `a` と、`x` から `y` への道 `γ` が与えられたとき、
`γ` を `a` から持ち上げた道の終点を `liftEnd γ a` とする。これがホモトピー類だけで決まること
（問題13）は、`12_CoveringSpace.lean` のホモトピーの持ち上げから出る。グラフ版では正規形定理から
出したところである。こうして得られる写像 `transport` がモノドロミーである。

モノドロミーがファイバーの間の全単射であることは、この Part では示さず、次の Part で
グラフ版と一緒に一度だけ示す。
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

/-- 道のホモトピー類。 -/
def PathClass (R : Type) [CompleteOrderedField R] (x y : X) : Type :=
  Quot (fun γ δ : Path (R := R) x y => γ.Homotopic δ)

namespace PathClass

variable {x y z w : X}

def mk (γ : Path (R := R) x y) : PathClass R x y := Quot.mk _ γ

theorem sound {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : mk γ = mk δ := Quot.sound h

def refl (x : X) : PathClass R x x := mk (Path.refl x)

noncomputable def comp (φ : PathClass R x y) (ψ : PathClass R y z) : PathClass R x z :=
  Quot.lift (fun γ => Quot.lift (fun δ => mk (γ.trans δ))
      (fun _ _ h => sound (Path.Homotopic.trans_congr (Path.Homotopic.refl' γ) h)) ψ)
    (fun _ _ h => by
      induction ψ using Quot.ind with
      | mk δ => exact sound (Path.Homotopic.trans_congr h (Path.Homotopic.refl' δ)))
    φ

def inv (φ : PathClass R x y) : PathClass R y x :=
  Quot.lift (fun γ => mk γ.symm) (fun _ _ h => sound (Path.Homotopic.symm_congr h)) φ

theorem refl_comp (φ : PathClass R x y) : (refl x).comp φ = φ := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.refl_trans γ)

theorem comp_refl (φ : PathClass R x y) : φ.comp (refl y) = φ := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.trans_refl γ)

theorem comp_assoc (φ : PathClass R x y) (ψ : PathClass R y z) (χ : PathClass R z w) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  induction φ using Quot.ind with
  | mk γ =>
    induction ψ using Quot.ind with
    | mk δ =>
      induction χ using Quot.ind with
      | mk ε => exact sound (Path.trans_assoc γ δ ε)

theorem inv_comp (φ : PathClass R x y) : φ.inv.comp φ = refl y := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.symm_trans γ)

theorem comp_inv (φ : PathClass R x y) : φ.comp φ.inv = refl x := by
  induction φ using Quot.ind with
  | mk γ => exact sound (Path.trans_symm γ)

end PathClass

/-! ### モノドロミー -/

variable {E : Type} [tE : TopologicalSpace E]

namespace CoveringMap

variable (p : CoveringMap E X)

/-- 点 `x` の上のファイバー。 -/
abbrev Fiber (x : X) : Type := {e : E // p.toFun e = x}

theorem fiberExt {x : X} {a b : p.Fiber x} (h : a.1 = b.1) : a = b := by
  cases a; cases b; cases h; rfl

variable {x y z : X}

theorem fiber_start (γ : Path (R := R) x y) (a : p.Fiber x) : p.toFun a.1 = γ.toFun ui0 := by
  rw [a.2, γ.source]

/-- 道の持ち上げの終点。 -/
noncomputable def liftEnd (γ : Path (R := R) x y) (a : p.Fiber x) : p.Fiber y :=
  ⟨Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1 (p.fiber_start γ a)) ui1,
   by rw [(Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
      (p.fiber_start γ a))).2.1, γ.target]⟩

/-- 問題12: 持ち上げの終点は、持ち上げを 1 つ示せば決まることを示せ。

ヒント: 選んだ持ち上げと与えられた持ち上げに、`12_CoveringSpace.lean` の `lift_unique` を使う。 -/
theorem liftEnd_eq (γ : Path (R := R) x y) (a : p.Fiber x) {f : UI R → E} (hf : Continuous f)
    (hfp : ∀ t, p.toFun (f t) = γ.toFun t) (hf0 : f ui0 = a.1) : (p.liftEnd γ a).1 = f ui1 :=
  sorry

/-- 問題13: **ホモトピックな道の持ち上げは同じ点に着く**ことを示せ。

ヒント: `exists_lift_homotopy` を `H` に使い、`γ` の持ち上げから始まる持ち上げ `G` を得る。`G(0, ·)` と `G(1, ·)` は
定数道の持ち上げなので定数（`lift_unique`）。すると `G(·, 1)` は `δ` の持ち上げで、始点は `a`、終点は `γ` の持ち上げの終点。 -/
theorem liftEnd_homotopic {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) (a : p.Fiber x) :
    p.liftEnd γ a = p.liftEnd δ a :=
  sorry

/-- ホモトピー類に沿った輸送（モノドロミー）。 -/
noncomputable def transport (φ : PathClass R x y) (a : p.Fiber x) : p.Fiber y :=
  Quot.lift (fun γ => p.liftEnd γ a) (fun _ _ h => p.liftEnd_homotopic h a) φ

theorem transport_refl (a : p.Fiber x) : p.transport (PathClass.refl (R := R) x) a = a :=
  p.fiberExt (p.liftEnd_eq (Path.refl x) a (continuous_const_map a.1) (fun _ => a.2) rfl)

/-- 問題14: 連接に沿った輸送は、輸送の合成であることを示せ。

ヒント: `γ` の持ち上げ `γ'` と、その終点からの `δ` の持ち上げ `δ'` を貼り合わせる（`continuous_glue`）と、
`γ.trans δ` の持ち上げになる（問題4で `p` と貼り合わせを入れ替える）。 -/
theorem transport_trans (φ : PathClass R x y) (ψ : PathClass R y z) (a : p.Fiber x) :
    p.transport (φ.comp ψ) a = p.transport ψ (p.transport φ a) :=
  sorry

end CoveringMap

end


/-! ## Part D: 共通の枠組み

`11_Covering.lean` の Part E の補足で、「モノドロミーの 3 つの問題（24〜26）はグラフであることを
一度も使っていない」と述べた。使ったのは、持ち上げが一意に定まることと、道のホモトピー類の亜群の法則
だけである。この Part では、それを定理の形にする。

* `PathSystem`: 道のホモトピー類の亜群（連接・定数道・逆道と、その法則）
* `LiftSystem`: ファイバーの族と、道のホモトピー類に沿った輸送（定数道・連接との関係）

「モノドロミーはファイバーの間の全単射」（問題15）を、この抽象的な形で一度だけ証明する。
グラフの被覆（`11_Covering.lean`）と位相空間の被覆（Part C）は、どちらもこの枠組みの**実例**になる。
2 つの被覆理論の類似は、ここで「同じ定理の 2 つの実例」という形式化された事実になる。
-/

section

/-- 道のホモトピー類の連接構造（亜群）の抽象化。 -/
structure PathSystem (V : Type) where
  Hom : V → V → Type
  refl : (x : V) → Hom x x
  trans : {x y z : V} → Hom x y → Hom y z → Hom x z
  symm : {x y : V} → Hom x y → Hom y x
  refl_trans : ∀ {x y : V} (γ : Hom x y), trans (refl x) γ = γ
  trans_refl : ∀ {x y : V} (γ : Hom x y), trans γ (refl y) = γ
  trans_assoc : ∀ {x y z w : V} (γ : Hom x y) (δ : Hom y z) (ε : Hom z w),
    trans (trans γ δ) ε = trans γ (trans δ ε)
  symm_trans : ∀ {x y : V} (γ : Hom x y), trans (symm γ) γ = refl y
  trans_symm : ∀ {x y : V} (γ : Hom x y), trans γ (symm γ) = refl x

/-- 被覆の抽象化: ファイバーの族と、道のホモトピー類に沿った輸送。 -/
structure LiftSystem {V : Type} (P : PathSystem V) (F : V → Type) where
  transport : {x y : V} → P.Hom x y → F x → F y
  transport_refl : ∀ (x : V) (a : F x), transport (P.refl x) a = a
  transport_trans : ∀ {x y z : V} (γ : P.Hom x y) (δ : P.Hom y z) (a : F x),
    transport (P.trans γ δ) a = transport δ (transport γ a)

namespace LiftSystem

variable {V : Type} {P : PathSystem V} {F : V → Type} (L : LiftSystem P F)

/-- 問題15: **共通の定理**: モノドロミーはファイバーの間の全単射であることを示せ。

ヒント: 逆道 `P.symm γ` に沿った輸送が逆写像になる。`transport_trans`・`transport_refl` と、
`PathSystem` の法則 `trans_symm`・`symm_trans`。`11_Covering.lean` の問題26と同じ証明である。 -/
theorem transport_bijective {x y : V} (γ : P.Hom x y) : Function.Bijective (L.transport γ) where
  injective := sorry
  surjective := sorry

end LiftSystem

/-! ### 実例 1: グラフの被覆（`11_Covering.lean`） -/

def graphPathSystem (G : SGraph) : PathSystem G.V where
  Hom := SGraph.PathClass G
  refl := SGraph.PathClass.refl
  trans φ ψ := φ.comp ψ
  symm φ := φ.inv
  refl_trans := SGraph.PathClass.refl_comp
  trans_refl := SGraph.PathClass.comp_refl
  trans_assoc := SGraph.PathClass.comp_assoc
  symm_trans := SGraph.PathClass.inv_comp
  trans_symm := SGraph.PathClass.comp_inv

noncomputable def graphLiftSystem {Y X : SGraph} (p : SGraph.Covering Y X) :
    LiftSystem (graphPathSystem X) p.Fiber where
  transport := p.transport
  transport_refl _ a := p.transport_refl a
  transport_trans := p.transport_trans

/-! ### 実例 2: 位相空間の被覆 -/

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

noncomputable def topPathSystem (R : Type) [CompleteOrderedField R] (X : Type)
    [TopologicalSpace X] : PathSystem X where
  Hom := PathClass R
  refl := PathClass.refl
  trans φ ψ := φ.comp ψ
  symm φ := φ.inv
  refl_trans := PathClass.refl_comp
  trans_refl := PathClass.comp_refl
  trans_assoc := PathClass.comp_assoc
  symm_trans := PathClass.inv_comp
  trans_symm := PathClass.comp_inv

noncomputable def topLiftSystem {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : CoveringMap E X) : LiftSystem (topPathSystem R X) p.Fiber where
  transport := p.transport
  transport_refl _ a := p.transport_refl a
  transport_trans := p.transport_trans

/-- 同じ定理の 2 つの実例。 -/
example {Y X : SGraph} (p : SGraph.Covering Y X) {v w : X.V} (γ : SGraph.PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  (graphLiftSystem p).transport_bijective γ

example {E X : Type} [TopologicalSpace E] [TopologicalSpace X] (p : CoveringMap E X) {x y : X}
    (γ : PathClass R x y) : Function.Bijective (p.transport γ) :=
  (topLiftSystem p).transport_bijective γ

end


/-! ## Part E: 円周

円周を $S^1 = \mathbb{R} / \mathbb{Z}$（整数だけずれた 2 数を同一視した商）として作り、
`07_Exercises.lean` Part 6 の商位相を入れる。射影 `proj : R → R/ℤ` が被覆であることを示す。

点 `[a]` の均等被覆近傍は、`a` のまわりの半径 `1/2` の開区間の像で、シートは整数 `n` だけずらした開区間
`V n = (a + n - 1/2, a + n + 1/2)`、シートへの逆写像は `circleSec a n` である。逆写像の連続性は、
`proj` が開写像であること（問題18）から出る。
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

/-! ### 整数の計算 -/

theorem natCast_succ_ge_one (k : Nat) : (1 : R) ≤ natCast (k + 1) := by
  rw [natCast_succ]
  have := add_le_add_right (natCast_nonneg (R := R) k) 1
  rwa [zero_add] at this

/-- 問題16: 絶対値が 1 未満の整数は 0 であることを示せ。

ヒント: `Int.ofNat` と `Int.negSucc` で場合分けする。`natCast (k + 1) ≥ 1`（`natCast_succ_ge_one`）。 -/
theorem int_eq_zero_of_abs_lt_one : ∀ {k : Int}, abs (intCast k : R) < 1 → k = 0 :=
  sorry

theorem intCast_sub (m n : Int) : (intCast (m - n) : R) = intCast m - intCast n := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg]; rfl

theorem intCast_injective {m n : Int} (h : (intCast m : R) = intCast n) : m = n := by
  have : m - n = 0 := int_eq_zero_of_abs_lt_one (R := R)
    (by rw [intCast_sub, h, sub_self, abs_zero]; exact zero_lt_one)
  omega

/-- 問題17: 差が整数で、どちらも `a` から `1/2` 未満の距離にある 2 数は等しいことを示せ。

ヒント: `intCast m = (w - a) + (a - r)` の絶対値は `1` 未満なので、問題16で `m = 0`。 -/
theorem eq_of_close {a r w : R} {m : Int} (hr : abs (r - a) < 1 / 2) (hw : abs (w - a) < 1 / 2)
    (hm : w = r + intCast m) : w = r :=
  sorry

/-! ### 円周 `R / ℤ` -/

/-- 整数だけずれた 2 数を同一視する。 -/
def circleSetoid (R : Type) [CompleteOrderedField R] : Setoid R where
  r a b := ∃ n : Int, b = a + intCast n
  iseqv := {
    refl := fun a => ⟨0, (add_zero a).symm⟩
    symm := fun {a b} ⟨n, h⟩ => ⟨-n, by rw [h, intCast_neg, add_assoc, add_neg_cancel, add_zero]⟩
    trans := fun {a b c} ⟨m, h₁⟩ ⟨n, h₂⟩ => ⟨m + n, by rw [h₂, h₁, intCast_add, add_assoc]⟩ }

/-- 円周。 -/
def Circle (R : Type) [CompleteOrderedField R] : Type := Quotient (circleSetoid R)

instance : TopologicalSpace (Circle R) :=
  inferInstanceAs (TopologicalSpace (Quot (circleSetoid R).r))

/-- 射影 `R → R/ℤ`。 -/
def proj (r : R) : Circle R := Quotient.mk _ r

theorem proj_eq_iff {a b : R} : proj a = proj b ↔ ∃ n : Int, b = a + intCast n :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem proj_add_int (a : R) (n : Int) : proj (a + intCast n) = proj a :=
  (proj_eq_iff.mpr ⟨n, rfl⟩).symm

theorem continuous_proj : Continuous (proj : R → Circle R) :=
  continuous_quotMk (circleSetoid R).r

theorem isOpen_circle_iff {s : Set (Circle R)} : IsOpen s ↔ IsOpen (proj ⁻¹' s) := Iff.rfl

/-- 問題18: 射影 `proj : R → R/ℤ` は開写像であることを示せ。

ヒント: 商位相での開集合は、`R` への逆像が開いたもの（`isOpen_circle_iff`）。
`w ∈ W` と `r = w + n` なら、`r` のまわりの近傍を `n` だけずらすと `W` の中に入る。 -/
theorem isOpen_image_proj {W : Set R} (hW : IsOpen W) :
    IsOpen ({z | ∃ w, w ∈ W ∧ proj w = z} : Set (Circle R)) :=
  sorry

/-! ### `R → R/ℤ` は被覆 -/

/-- 点 `a` のまわりの均等被覆近傍の、シート `n` の逆写像。 -/
noncomputable def circleSec (a : R) (n : Int) (z : Circle R) : R :=
  open Classical in
  if h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z then Classical.choose h + intCast n else 0

theorem circleSec_spec {a : R} {z : Circle R} (h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z) (n : Int) :
    ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z ∧ circleSec a n z = r + intCast n := by
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  unfold circleSec; rw [dif_pos h]

/-- `a` から `1/2` 未満の点 `r` の類については、逆写像の値は `r + n`。 -/
theorem circleSec_proj {a r : R} (hr : abs (r - a) < 1 / 2) (n : Int) :
    circleSec a n (proj r) = r + intCast n := by
  obtain ⟨r', hr', hpr', hs⟩ := circleSec_spec ⟨r, hr, rfl⟩ n
  obtain ⟨m, hm⟩ := proj_eq_iff.mp hpr'
  rw [hs, ← eq_of_close hr' hr hm]

theorem abs_shift (r a : R) (n : Int) : abs (r + intCast n - (a + intCast n)) = abs (r - a) := by
  rw [add_sub_add_right]

/-- 問題19: （発展）`a` のまわりの `1/2`-近傍の像は均等に被覆されることを示せ。

ヒント: シートは `ball (a + n) (1/2)`、逆写像は `circleSec a n`。合併は `proj_eq_iff`、交わらないことは問題17、
シートの点での逆写像は `circleSec_proj`。逆写像の連続性は、`O` の逆像が `proj` による開集合
`{r | |r - a| < 1/2 ∧ r + n ∈ O}` の像になることと問題18。 -/
theorem evenlyCovered_circle (a : R) :
    EvenlyCovered (proj : R → Circle R) {z | ∃ r, r ∈ ball a (1 / 2) ∧ proj r = z} :=
  sorry

/-- **`R → R/ℤ` は被覆**。 -/
def circleCovering : CoveringMap R (Circle R) where
  toFun := proj
  continuous_toFun := continuous_proj
  evenly := by
    intro x
    induction x using Quotient.ind with
    | _ a =>
      exact ⟨_, isOpen_image_proj (isOpen_ball a (1 / 2)), ⟨a, mem_ball_self (half_pos zero_lt_one),
        rfl⟩, evenlyCovered_circle a⟩

end


/-! ## Part F: π₁(S¹) ≃ ℤ

基点 `[0]` のループの類 `φ` に、`0` から持ち上げた終点の整数を対応させる。これが**モノドロミー次数**
`deg` である。主定理（問題26）は、`deg` が連接を和に写す全単射であること。証明は `11_Covering.lean` の
Part F と同じ 3 つの部品からなる。

* **準同型性**（問題22）: 整数 `m` だけの平行移動（**デッキ変換**）は持ち上げと可換（問題21）
* **単射性**（問題23・24）: $\mathbb{R}$ は単連結。持ち上げた閉じた道は、直線ホモトピーで定数に縮み、
  それを `proj` で押し出すと、もとのループが定数ループにホモトピックとわかる
* **全射性**（問題25）: `n` 周するループ `t ↦ [n t]` の持ち上げは `t ↦ n t` で、終点は `n`
-/

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

/-- 円周の基点 `[0]`。 -/
def base : Circle R := proj 0

theorem proj_intCast (m : Int) : proj (intCast m : R) = base := by
  have := proj_add_int (0 : R) m
  rw [zero_add] at this
  exact this

/-- 基点の上のファイバーの点 `m`（整数）。 -/
def fibInt (m : Int) : circleCovering.Fiber (base : Circle R) := ⟨intCast m, proj_intCast m⟩

/-- 問題20: 基点の上のファイバーの点は整数であることを示せ。

ヒント: `proj a = proj 0` から、ある `n` で `0 = a + n`（`proj_eq_iff`）。 -/
theorem fiber_int (a : circleCovering.Fiber (base : Circle R)) : ∃ n : Int, a.1 = intCast n :=
  sorry

/-- 問題21: **デッキ変換**: 整数 `m` から持ち上げると、`0` から持ち上げた終点を `m` だけずらした点に着くことを示せ。

ヒント: `0` からの持ち上げ `γ'` を `m` だけずらした `γ' + m` は、`m` からの持ち上げ（`proj_add_int`）。問題12。 -/
theorem transport_fibInt (φ : PathClass R (base : Circle R) base) (m : Int) :
    (circleCovering.transport φ (fibInt m)).1 = (circleCovering.transport φ (fibInt 0)).1 + intCast m :=
  sorry

/-- **モノドロミー次数**: ループを `0` から持ち上げた終点の整数。 -/
noncomputable def deg (φ : PathClass R (base : Circle R) base) : Int :=
  Classical.choose (fiber_int (circleCovering.transport φ (fibInt 0)))

theorem deg_spec (φ : PathClass R (base : Circle R) base) :
    circleCovering.transport φ (fibInt 0) = fibInt (deg φ) :=
  circleCovering.fiberExt (Classical.choose_spec (fiber_int (circleCovering.transport φ (fibInt 0))))

/-- 問題22: モノドロミー次数は連接を和に写すことを示せ。

ヒント: `transport_trans` で分解し、`deg_spec` と問題21。整数の等式に戻すのは `intCast_injective`。 -/
theorem deg_comp (φ ψ : PathClass R (base : Circle R) base) :
    deg (φ.comp ψ) = deg φ + deg ψ :=
  sorry

theorem deg_refl : deg (PathClass.refl (R := R) (base : Circle R)) = 0 := by
  apply intCast_injective (R := R)
  have h := congrArg Subtype.val (deg_spec (PathClass.refl (R := R) (base : Circle R)))
  rw [circleCovering.transport_refl] at h
  exact h.symm

theorem deg_inv (φ : PathClass R (base : Circle R) base) : deg φ.inv = -deg φ := by
  have h := deg_comp φ.inv φ
  rw [PathClass.inv_comp, deg_refl] at h
  omega

/-- 問題23: 次数 0 のループは定数ループにホモトピックであることを示せ。

ヒント: `γ` の持ち上げ `γ'` は `0` から `0` への閉じた道。直線ホモトピー `(1 - t) γ'(s)` を `proj` で押し出すと、
`γ` から定数ループへのホモトピーになる。 -/
theorem deg_eq_zero {φ : PathClass R (base : Circle R) base} (h : deg φ = 0) :
    φ = PathClass.refl base :=
  sorry

/-- 問題24: モノドロミー次数は単射であることを示せ。

ヒント: `deg (φ.comp ψ.inv) = 0` を示して問題23を使い、亜群の法則で `φ = ψ` に直す。`11_Covering.lean` の問題34と同じ。 -/
theorem deg_injective : Function.Injective (deg (R := R)) :=
  sorry

/-- `n` 周するループ `t ↦ [n t]`。 -/
def loopN (n : Int) : Path (R := R) (base : Circle R) base where
  toFun t := proj (intCast n * t.1)
  continuous_toFun := continuous_proj.comp (continuous_mul (continuous_const _) continuous_subtype_val)
  source := by show proj (intCast n * 0) = base; rw [mul_zero]; rfl
  target := by show proj (intCast n * 1) = base; rw [mul_one]; exact proj_intCast n

/-- 問題25: モノドロミー次数は全射であることを示せ。

ヒント: `n` 周するループ `loopN n` の持ち上げは `t ↦ n t`（問題12）。 -/
theorem deg_surjective : Function.Surjective (deg (R := R)) :=
  sorry

/-- 問題26: **主定理 π₁(S¹) ≃ ℤ**: モノドロミー次数は、連接を和に写す全単射であることを示せ。

ヒント: 問題22・24・25。 -/
theorem pi1_circle :
    (∀ φ ψ : PathClass R (base : Circle R) base, deg (φ.comp ψ) = deg φ + deg ψ) ∧
      Function.Bijective (deg (R := R)) :=
  sorry

end

end CovSpace

/-! 解答（`13_FundamentalGroupoidSol.lean`）では、主定理が依存する公理は
`propext`・`Classical.choice`・`Quot.sound` の 3 つだけである（`11_Covering.lean` の主定理と同じ）。
問題を解き終えたら、次の出力に `sorryAx` が残っていないことを確かめよ。
-/

#print axioms CovSpace.pi1_circle
