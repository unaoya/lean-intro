-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。
-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。

import LeanIntro.Solutions.«11_Covering»
import LeanIntro.Solutions.«12_CoveringSpace»

-- # 発展演習: 基本亜群と円周

namespace CovSpace

-- ## Part A: 道

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

noncomputable def glue {A : Type} (f g : UI R → A) (s : UI R) : A :=
  open Classical in
  if h : s.1 ≤ 1 / 2 then f ⟨2 * s.1, two_mul_mem s.2.1 h⟩
  else g ⟨2 * s.1 - 1, two_mul_sub_one_mem (le_of_lt (not_le.mp h)) s.2.2⟩

theorem glue_of_le {A : Type} (f g : UI R → A) {s : UI R} (h : s.1 ≤ 1 / 2) :
    glue f g s = f ⟨2 * s.1, two_mul_mem s.2.1 h⟩ := by
  unfold glue; rw [dif_pos h]

theorem glue_of_ge {A : Type} (f g : UI R → A) (hfg : f ui1 = g ui0) {s : UI R} (h : 1 / 2 ≤ s.1) :
    glue f g s = g ⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ :=
  sorry

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

def Path.refl (x : X) : Path (R := R) x x :=
  ⟨fun _ => x, continuous_const_map x, rfl, rfl⟩

noncomputable def Path.trans (γ : Path (R := R) x y) (δ : Path (R := R) y z) : Path (R := R) x z :=
  ⟨glue γ.toFun δ.toFun, continuous_glue γ.continuous_toFun δ.continuous_toFun
      (by rw [γ.target, δ.source]),
    by rw [glue_of_le (s := ui0) _ _ half_nonneg']
       exact (congrArg γ.toFun (UI.ext (mul_zero 2))).trans γ.source,
    by rw [glue_of_ge (s := ui1) _ _ (by rw [γ.target, δ.source]) half_le_one]
       exact (congrArg δ.toFun (UI.ext (show 2 * 1 - 1 = (1 : R) by
         rw [two_mul_one, two_def, add_sub_cancel]))).trans δ.target⟩

def uiRev (s : UI R) : UI R :=
  ⟨1 - s.1, sub_nonneg.mpr s.2.2, by
    have := add_le_add_left _ _ (neg_le_neg s.2.1) 1
    rwa [neg_zero, add_zero] at this⟩

theorem continuous_uiRev : Continuous (uiRev : UI R → UI R) :=
  continuous_subtype_mk (continuous_sub (continuous_const _) continuous_subtype_val) _

theorem uiRev_zero : uiRev (ui0 : UI R) = ui1 := UI.ext (sub_zero 1)
theorem uiRev_one : uiRev (ui1 : UI R) = ui0 := UI.ext (sub_self 1)

def Path.symm (γ : Path (R := R) x y) : Path (R := R) y x :=
  ⟨fun s => γ.toFun (uiRev s), γ.continuous_toFun.comp continuous_uiRev,
    by show γ.toFun (uiRev ui0) = y; rw [uiRev_zero, γ.target],
    by show γ.toFun (uiRev ui1) = x; rw [uiRev_one, γ.source]⟩

def Path.Homotopic (γ δ : Path (R := R) x y) : Prop :=
  ∃ H : UI R × UI R → X, Continuous H ∧ (∀ s, H (s, ui0) = γ.toFun s) ∧
    (∀ s, H (s, ui1) = δ.toFun s) ∧ (∀ t, H (ui0, t) = x) ∧ (∀ t, H (ui1, t) = y)

-- ### 再パラメータ化の補題

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

theorem homotopic_reparam (γ : UI R → X) (hγ : Continuous γ) {φ ψ : UI R → UI R}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h0 : φ ui0 = ψ ui0) (h1 : φ ui1 = ψ ui1)
    (P Q : Path (R := R) x y) (hP : ∀ s, P.toFun s = γ (φ s)) (hQ : ∀ s, Q.toFun s = γ (ψ s)) :
    P.Homotopic Q :=
  sorry

end

-- ## Part B: ホモトピーと亜群の法則

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]
variable {x y z w : X}

-- ### 貼り合わせの計算規則

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

-- ### 同値関係

theorem Path.Homotopic.refl' (γ : Path (R := R) x y) : γ.Homotopic γ :=
  ⟨fun q => γ.toFun q.1, γ.continuous_toFun.comp continuous_fst, fun _ => rfl, fun _ => rfl,
    fun _ => γ.source, fun _ => γ.target⟩

theorem Path.Homotopic.symm' {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : δ.Homotopic γ :=
  sorry

theorem Path.Homotopic.trans' {γ δ ε : Path (R := R) x y} (h : γ.Homotopic δ) (k : δ.Homotopic ε) :
    γ.Homotopic ε :=
  sorry

-- ### 連接・逆道との両立

theorem continuous_swap {A B : Type} [TopologicalSpace A] [TopologicalSpace B] :
    Continuous (fun q : A × B => (q.2, q.1)) := continuous_prod_mk continuous_snd continuous_fst

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

-- ### 亜群の法則（再パラメータ化の補題から）

theorem continuous_id' {A : Type} [TopologicalSpace A] : Continuous (fun a : A => a) :=
  continuous_id

theorem Path.refl_trans (γ : Path (R := R) x y) : ((Path.refl x).trans γ).Homotopic γ :=
  sorry

theorem Path.trans_refl (γ : Path (R := R) x y) : (γ.trans (Path.refl y)).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) (fun _ => ui1))
    (ψ := fun u => u) (continuous_glue continuous_id' (continuous_const_map _) rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue γ.toFun (fun _ => y) s = γ.toFun (glue (fun u => u) (fun _ => ui1) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => rfl) (fun _ => γ.target.symm) s

theorem Path.trans_assoc (γ : Path (R := R) x y) (δ : Path (R := R) y z) (ε : Path (R := R) z w) :
    ((γ.trans δ).trans ε).Homotopic (γ.trans (δ.trans ε)) :=
  sorry

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

-- ## Part C: モノドロミー

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]

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

-- ### モノドロミー

variable {E : Type} [tE : TopologicalSpace E]

namespace CoveringMap

variable (p : CoveringMap E X)

abbrev Fiber (x : X) : Type := {e : E // p.toFun e = x}

theorem fiberExt {x : X} {a b : p.Fiber x} (h : a.1 = b.1) : a = b := by
  cases a; cases b; cases h; rfl

variable {x y z : X}

theorem fiber_start (γ : Path (R := R) x y) (a : p.Fiber x) : p.toFun a.1 = γ.toFun ui0 := by
  rw [a.2, γ.source]

noncomputable def liftEnd (γ : Path (R := R) x y) (a : p.Fiber x) : p.Fiber y :=
  ⟨Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1 (p.fiber_start γ a)) ui1,
   by rw [(Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
      (p.fiber_start γ a))).2.1, γ.target]⟩

theorem liftEnd_eq (γ : Path (R := R) x y) (a : p.Fiber x) {f : UI R → E} (hf : Continuous f)
    (hfp : ∀ t, p.toFun (f t) = γ.toFun t) (hf0 : f ui0 = a.1) : (p.liftEnd γ a).1 = f ui1 :=
  sorry

theorem liftEnd_homotopic {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) (a : p.Fiber x) :
    p.liftEnd γ a = p.liftEnd δ a :=
  sorry

noncomputable def transport (φ : PathClass R x y) (a : p.Fiber x) : p.Fiber y :=
  Quot.lift (fun γ => p.liftEnd γ a) (fun _ _ h => p.liftEnd_homotopic h a) φ

theorem transport_refl (a : p.Fiber x) : p.transport (PathClass.refl (R := R) x) a = a :=
  p.fiberExt (p.liftEnd_eq (Path.refl x) a (continuous_const_map a.1) (fun _ => a.2) rfl)

theorem transport_trans (φ : PathClass R x y) (ψ : PathClass R y z) (a : p.Fiber x) :
    p.transport (φ.comp ψ) a = p.transport ψ (p.transport φ a) :=
  sorry

end CoveringMap

end

-- ## Part D: 共通の枠組み

section

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

structure LiftSystem {V : Type} (P : PathSystem V) (F : V → Type) where
  transport : {x y : V} → P.Hom x y → F x → F y
  transport_refl : ∀ (x : V) (a : F x), transport (P.refl x) a = a
  transport_trans : ∀ {x y z : V} (γ : P.Hom x y) (δ : P.Hom y z) (a : F x),
    transport (P.trans γ δ) a = transport δ (transport γ a)

namespace LiftSystem

variable {V : Type} {P : PathSystem V} {F : V → Type} (L : LiftSystem P F)

theorem transport_bijective {x y : V} (γ : P.Hom x y) : Function.Bijective (L.transport γ) where
  injective := sorry
  surjective := sorry

end LiftSystem

-- ### 実例 1: グラフの被覆（`11_Covering.lean`）

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

-- ### 実例 2: 位相空間の被覆

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

example {Y X : SGraph} (p : SGraph.Covering Y X) {v w : X.V} (γ : SGraph.PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  (graphLiftSystem p).transport_bijective γ

example {E X : Type} [TopologicalSpace E] [TopologicalSpace X] (p : CoveringMap E X) {x y : X}
    (γ : PathClass R x y) : Function.Bijective (p.transport γ) :=
  (topLiftSystem p).transport_bijective γ

end

-- ## Part E: 円周

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

-- ### 整数の計算

theorem natCast_succ_ge_one (k : Nat) : (1 : R) ≤ natCast (k + 1) := by
  rw [natCast_succ]
  have := add_le_add_right (natCast_nonneg (R := R) k) 1
  rwa [zero_add] at this

theorem int_eq_zero_of_abs_lt_one : ∀ {k : Int}, abs (intCast k : R) < 1 → k = 0 :=
  sorry

theorem intCast_sub (m n : Int) : (intCast (m - n) : R) = intCast m - intCast n := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg]; rfl

theorem intCast_injective {m n : Int} (h : (intCast m : R) = intCast n) : m = n := by
  have : m - n = 0 := int_eq_zero_of_abs_lt_one (R := R)
    (by rw [intCast_sub, h, sub_self, abs_zero]; exact zero_lt_one)
  omega

theorem eq_of_close {a r w : R} {m : Int} (hr : abs (r - a) < 1 / 2) (hw : abs (w - a) < 1 / 2)
    (hm : w = r + intCast m) : w = r :=
  sorry

-- ### 円周 `R / ℤ`

def circleSetoid (R : Type) [CompleteOrderedField R] : Setoid R where
  r a b := ∃ n : Int, b = a + intCast n
  iseqv := {
    refl := fun a => ⟨0, (add_zero a).symm⟩
    symm := fun {a b} ⟨n, h⟩ => ⟨-n, by rw [h, intCast_neg, add_assoc, add_neg_cancel, add_zero]⟩
    trans := fun {a b c} ⟨m, h₁⟩ ⟨n, h₂⟩ => ⟨m + n, by rw [h₂, h₁, intCast_add, add_assoc]⟩ }

def Circle (R : Type) [CompleteOrderedField R] : Type := Quotient (circleSetoid R)

instance : TopologicalSpace (Circle R) :=
  inferInstanceAs (TopologicalSpace (Quot (circleSetoid R).r))

def proj (r : R) : Circle R := Quotient.mk _ r

theorem proj_eq_iff {a b : R} : proj a = proj b ↔ ∃ n : Int, b = a + intCast n :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem proj_add_int (a : R) (n : Int) : proj (a + intCast n) = proj a :=
  (proj_eq_iff.mpr ⟨n, rfl⟩).symm

theorem continuous_proj : Continuous (proj : R → Circle R) :=
  continuous_quotMk (circleSetoid R).r

theorem isOpen_circle_iff {s : Set (Circle R)} : IsOpen s ↔ IsOpen (proj ⁻¹' s) := Iff.rfl

theorem isOpen_image_proj {W : Set R} (hW : IsOpen W) :
    IsOpen ({z | ∃ w, w ∈ W ∧ proj w = z} : Set (Circle R)) :=
  sorry

-- ### `R → R/ℤ` は被覆

noncomputable def circleSec (a : R) (n : Int) (z : Circle R) : R :=
  open Classical in
  if h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z then Classical.choose h + intCast n else 0

theorem circleSec_spec {a : R} {z : Circle R} (h : ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z) (n : Int) :
    ∃ r, abs (r - a) < 1 / 2 ∧ proj r = z ∧ circleSec a n z = r + intCast n := by
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  unfold circleSec; rw [dif_pos h]

theorem circleSec_proj {a r : R} (hr : abs (r - a) < 1 / 2) (n : Int) :
    circleSec a n (proj r) = r + intCast n := by
  obtain ⟨r', hr', hpr', hs⟩ := circleSec_spec ⟨r, hr, rfl⟩ n
  obtain ⟨m, hm⟩ := proj_eq_iff.mp hpr'
  rw [hs, ← eq_of_close hr' hr hm]

theorem abs_shift (r a : R) (n : Int) : abs (r + intCast n - (a + intCast n)) = abs (r - a) := by
  rw [add_sub_add_right]

theorem evenlyCovered_circle (a : R) :
    EvenlyCovered (proj : R → Circle R) {z | ∃ r, r ∈ ball a (1 / 2) ∧ proj r = z} :=
  sorry

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

-- ## Part F: π₁(S¹) ≃ ℤ

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

def base : Circle R := proj 0

theorem proj_intCast (m : Int) : proj (intCast m : R) = base := by
  have := proj_add_int (0 : R) m
  rw [zero_add] at this
  exact this

def fibInt (m : Int) : circleCovering.Fiber (base : Circle R) := ⟨intCast m, proj_intCast m⟩

theorem fiber_int (a : circleCovering.Fiber (base : Circle R)) : ∃ n : Int, a.1 = intCast n :=
  sorry

theorem transport_fibInt (φ : PathClass R (base : Circle R) base) (m : Int) :
    (circleCovering.transport φ (fibInt m)).1 = (circleCovering.transport φ (fibInt 0)).1 + intCast m :=
  sorry

noncomputable def deg (φ : PathClass R (base : Circle R) base) : Int :=
  Classical.choose (fiber_int (circleCovering.transport φ (fibInt 0)))

theorem deg_spec (φ : PathClass R (base : Circle R) base) :
    circleCovering.transport φ (fibInt 0) = fibInt (deg φ) :=
  circleCovering.fiberExt (Classical.choose_spec (fiber_int (circleCovering.transport φ (fibInt 0))))

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

theorem deg_eq_zero {φ : PathClass R (base : Circle R) base} (h : deg φ = 0) :
    φ = PathClass.refl base :=
  sorry

theorem deg_injective : Function.Injective (deg (R := R)) :=
  sorry

def loopN (n : Int) : Path (R := R) (base : Circle R) base where
  toFun t := proj (intCast n * t.1)
  continuous_toFun := continuous_proj.comp (continuous_mul (continuous_const _) continuous_subtype_val)
  source := by show proj (intCast n * 0) = base; rw [mul_zero]; rfl
  target := by show proj (intCast n * 1) = base; rw [mul_one]; exact proj_intCast n

theorem deg_surjective : Function.Surjective (deg (R := R)) :=
  sorry

theorem pi1_circle :
    (∀ φ ψ : PathClass R (base : Circle R) base, deg (φ.comp ψ) = deg φ + deg ψ) ∧
      Function.Bijective (deg (R := R)) :=
  sorry

end

end CovSpace

#print axioms CovSpace.pi1_circle
