-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Solutions.«11_Covering»
import LeanIntro.Solutions.«12_CoveringSpace»

-- # 発展演習: 基本亜群と円周（解答）

namespace CovSpace

-- ## 道とホモトピー

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
    glue f g s = g ⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ := by
  unfold glue
  by_cases h' : s.1 ≤ 1 / 2
  · rw [dif_pos h']
    have ht : s.1 = 1 / 2 := le_antisymm _ _ h' h
    have e1 : (⟨2 * s.1, two_mul_mem s.2.1 h'⟩ : UI R) = ui1 :=
      UI.ext (by show 2 * s.1 = 1; rw [ht, two_mul_half])
    have e2 : (⟨2 * s.1 - 1, two_mul_sub_one_mem h s.2.2⟩ : UI R) = ui0 :=
      UI.ext (by show 2 * s.1 - 1 = 0; rw [ht, two_mul_half, sub_self])
    rw [e1, e2, hfg]
  · rw [dif_neg h']

theorem continuous_glue_param {Z A : Type} [TopologicalSpace Z] [TopologicalSpace A]
    (f g : Z × UI R → A) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, f (z, ui1) = g (z, ui0)) :
    Continuous (fun q : Z × UI R => glue (fun s => f (q.1, s)) (fun s => g (q.1, s)) q.2) := by
  have hval : Continuous (fun q : Z × UI R => q.2.1) := continuous_subtype_val.comp continuous_snd
  refine continuous_of_closed_cover (isClosed_preimage hval (isClosed_le_const (1 / 2 : R)))
    (isClosed_preimage hval (isClosed_ge_const (1 / 2 : R))) (fun q => le_total _ _) ?_ ?_
  · have e : (fun a : Subtype ({q | q.2.1 ≤ 1 / 2} : Set (Z × UI R)) =>
        glue (fun s => f (a.1.1, s)) (fun s => g (a.1.1, s)) a.1.2) =
        fun a => f (a.1.1, ⟨2 * a.1.2.1, two_mul_mem a.1.2.2.1 a.2⟩) := by
      funext a; exact glue_of_le _ _ a.2
    have hc := hf.comp (continuous_prod_mk (continuous_fst.comp continuous_subtype_val)
      (continuous_subtype_mk (continuous_mul (continuous_const _) (hval.comp continuous_subtype_val))
        (fun a : Subtype ({q | q.2.1 ≤ 1 / 2} : Set (Z × UI R)) => two_mul_mem a.1.2.2.1 a.2)))
    rw [← e] at hc
    exact hc
  · have e : (fun a : Subtype ({q | 1 / 2 ≤ q.2.1} : Set (Z × UI R)) =>
        glue (fun s => f (a.1.1, s)) (fun s => g (a.1.1, s)) a.1.2) =
        fun a => g (a.1.1, ⟨2 * a.1.2.1 - 1, two_mul_sub_one_mem a.2 a.1.2.2.2⟩) := by
      funext a; exact glue_of_ge _ _ (hfg a.1.1) a.2
    have hc := hg.comp (continuous_prod_mk (continuous_fst.comp continuous_subtype_val)
      (continuous_subtype_mk (continuous_sub (continuous_mul (continuous_const _)
        (hval.comp continuous_subtype_val)) (continuous_const _))
        (fun a : Subtype ({q | 1 / 2 ≤ q.2.1} : Set (Z × UI R)) =>
          two_mul_sub_one_mem a.2 a.1.2.2.2)))
    rw [← e] at hc
    exact hc

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
    P.Homotopic Q := by
  refine ⟨fun q => γ (uiMix (φ q.1) (ψ q.1) q.2), ?_, fun s => ?_, fun s => ?_, fun t => ?_,
    fun t => ?_⟩
  · exact hγ.comp (continuous_uiMix (hφ.comp continuous_fst) (hψ.comp continuous_fst) continuous_snd)
  · show γ (uiMix _ _ ui0) = _; rw [uiMix_zero, hP]
  · show γ (uiMix _ _ ui1) = _; rw [uiMix_one, hQ]
  · show γ (uiMix (φ ui0) (ψ ui0) t) = x
    rw [h0, uiMix_self, ← hQ, Q.source]
  · show γ (uiMix (φ ui1) (ψ ui1) t) = y
    rw [h1, uiMix_self, ← hQ, Q.target]

end

-- ## ホモトピーの同値性と亜群の法則

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]
variable {X : Type} [tX : TopologicalSpace X]
variable {x y z w : X}

-- ### 貼り合わせの計算規則

theorem glue_comp {A B : Type} (h : A → B) (f g : UI R → A) (s : UI R) :
    h (glue f g s) = glue (fun u => h (f u)) (fun u => h (g u)) s := by
  unfold glue
  by_cases hs : s.1 ≤ 1 / 2
  · rw [dif_pos hs, dif_pos hs]
  · rw [dif_neg hs, dif_neg hs]

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

theorem glue_halfL {A : Type} (f g : UI R → A) (u : UI R) : glue f g (halfL u) = f u := by
  rw [glue_of_le (s := halfL u) _ _ (le_trans _ _ _ (div_two_le_div_two u.2.2) (le_refl _))]
  exact congrArg f (UI.ext (show 2 * (u.1 / 2) = u.1 from mul_div_cancel_left _ two_ne_zero))

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

theorem Path.Homotopic.symm' {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) : δ.Homotopic γ := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  refine ⟨fun q => H (q.1, uiRev q.2), hH.comp (continuous_prod_mk continuous_fst
    (continuous_uiRev.comp continuous_snd)), fun s => ?_, fun s => ?_, fun t => hx _, fun t => hy _⟩
  · show H (s, uiRev ui0) = _; rw [uiRev_zero, h1]
  · show H (s, uiRev ui1) = _; rw [uiRev_one, h0]

theorem Path.Homotopic.trans' {γ δ ε : Path (R := R) x y} (h : γ.Homotopic δ) (k : δ.Homotopic ε) :
    γ.Homotopic ε := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  obtain ⟨K, hK, k0, k1, kx, ky⟩ := k
  have hHK : ∀ s, H (s, ui1) = K (s, ui0) := fun s => by rw [h1, k0]
  refine ⟨fun q => glue (fun t => H (q.1, t)) (fun t => K (q.1, t)) q.2,
    continuous_glue_param H K hH hK hHK, fun s => ?_, fun s => ?_, fun t => ?_, fun t => ?_⟩
  · show glue _ _ ui0 = _; rw [glue_zero, h0]
  · show glue _ _ ui1 = _; rw [glue_one _ _ (hHK s), k1]
  · exact glue_const (fun _ => hx _) (fun _ => kx _) t
  · exact glue_const (fun _ => hy _) (fun _ => ky _) t

-- ### 連接・逆道との両立

theorem continuous_swap {A B : Type} [TopologicalSpace A] [TopologicalSpace B] :
    Continuous (fun q : A × B => (q.2, q.1)) := continuous_prod_mk continuous_snd continuous_fst

theorem Path.Homotopic.trans_congr {γ γ' : Path (R := R) x y} {δ δ' : Path (R := R) y z}
    (h : γ.Homotopic γ') (k : δ.Homotopic δ') : (γ.trans δ).Homotopic (γ'.trans δ') := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  obtain ⟨K, hK, k0, k1, kx, ky⟩ := k
  have hHK : ∀ t, H (ui1, t) = K (ui0, t) := fun t => by rw [hy, kx]
  have hc := continuous_glue_param (fun q : UI R × UI R => H (q.2, q.1))
    (fun q => K (q.2, q.1)) (hH.comp continuous_swap) (hK.comp continuous_swap) hHK
  refine ⟨fun q => glue (fun s => H (s, q.2)) (fun s => K (s, q.2)) q.1,
    hc.comp continuous_swap, fun s => ?_, fun s => ?_, fun t => ?_, fun t => ?_⟩
  · exact glue_congr (fun u => h0 u) (fun u => k0 u) s
  · exact glue_congr (fun u => h1 u) (fun u => k1 u) s
  · show glue _ _ ui0 = x; rw [glue_zero, hx]
  · show glue _ _ ui1 = z; rw [glue_one _ _ (hHK t), ky]

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

theorem Path.refl_trans (γ : Path (R := R) x y) : ((Path.refl x).trans γ).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun _ => ui0) (fun u => u))
    (ψ := fun u => u) (continuous_glue (continuous_const_map _) continuous_id' rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue (fun _ => x) γ.toFun s = γ.toFun (glue (fun _ => ui0) (fun u => u) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => γ.source.symm) (fun _ => rfl) s

theorem Path.trans_refl (γ : Path (R := R) x y) : (γ.trans (Path.refl y)).Homotopic γ := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) (fun _ => ui1))
    (ψ := fun u => u) (continuous_glue continuous_id' (continuous_const_map _) rfl) continuous_id'
    (glue_zero _ _) (glue_one _ _ rfl) _ _ (fun s => ?_) (fun s => rfl)
  show glue γ.toFun (fun _ => y) s = γ.toFun (glue (fun u => u) (fun _ => ui1) s)
  rw [glue_comp γ.toFun]
  exact glue_congr (fun _ => rfl) (fun _ => γ.target.symm) s

theorem Path.trans_assoc (γ : Path (R := R) x y) (δ : Path (R := R) y z) (ε : Path (R := R) z w) :
    ((γ.trans δ).trans ε).Homotopic (γ.trans (δ.trans ε)) := by
  let Γ := γ.trans (δ.trans ε)
  let α : UI R → UI R := glue halfL (fun u => halfR (halfL u))
  let β : UI R → UI R := fun u => halfR (halfR u)
  have hα1 : halfL (ui1 : UI R) = halfR (halfL ui0) := by rw [halfL_zero, halfL_one]
  have hαc : Continuous α := continuous_glue continuous_halfL
    (continuous_halfR.comp continuous_halfL) hα1
  have hαβ : α ui1 = β ui0 := by
    show glue _ _ ui1 = halfR (halfR ui0)
    rw [glue_one _ _ hα1, halfL_one]
  refine homotopic_reparam Γ.toFun Γ.continuous_toFun (φ := glue α β) (ψ := fun u => u)
    (continuous_glue hαc (continuous_halfR.comp continuous_halfR) hαβ) continuous_id' ?_ ?_ _ _
    (fun s => ?_) (fun s => rfl)
  · show glue α β ui0 = ui0
    rw [glue_zero]
    show glue _ _ ui0 = ui0
    rw [glue_zero, halfL_zero]
  · show glue α β ui1 = ui1
    rw [glue_one _ _ hαβ]
    show halfR (halfR ui1) = ui1
    exact UI.ext (show ((((1 : R) + 1) / 2) + 1) / 2 = 1 by rw [← two_def, two_div_two, ← two_def,
      two_div_two])
  · show glue (glue γ.toFun δ.toFun) ε.toFun s = Γ.toFun (glue α β s)
    rw [glue_comp Γ.toFun]
    refine glue_congr (fun u => ?_) (fun u => ?_) s
    · show glue γ.toFun δ.toFun u = Γ.toFun (glue halfL (fun u => halfR (halfL u)) u)
      rw [glue_comp Γ.toFun]
      exact glue_congr (fun v => (Path.trans_halfL _ _ v).symm)
        (fun v => by
          show δ.toFun v = Γ.toFun (halfR (halfL v))
          rw [Path.trans_halfR, Path.trans_halfL]) u
    · show ε.toFun u = Γ.toFun (halfR (halfR u))
      rw [Path.trans_halfR, Path.trans_halfR]

theorem Path.symm_trans (γ : Path (R := R) x y) : (γ.symm.trans γ).Homotopic (Path.refl y) := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue uiRev (fun u => u))
    (ψ := fun _ => ui1) (continuous_glue continuous_uiRev continuous_id' uiRev_one)
    (continuous_const_map _) (by rw [glue_zero, uiRev_zero]) (glue_one _ _ uiRev_one) _ _
    (fun s => ?_) (fun s => γ.target.symm)
  show glue (fun u => γ.toFun (uiRev u)) γ.toFun s = γ.toFun (glue uiRev (fun u => u) s)
  rw [glue_comp γ.toFun]

theorem Path.trans_symm (γ : Path (R := R) x y) : (γ.trans γ.symm).Homotopic (Path.refl x) := by
  refine homotopic_reparam γ.toFun γ.continuous_toFun (φ := glue (fun u => u) uiRev)
    (ψ := fun _ => ui0) (continuous_glue continuous_id' continuous_uiRev uiRev_zero.symm)
    (continuous_const_map _) (glue_zero _ _) (by rw [glue_one _ _ uiRev_zero.symm, uiRev_one]) _ _
    (fun s => ?_) (fun s => γ.source.symm)
  show glue γ.toFun (fun u => γ.toFun (uiRev u)) s = γ.toFun (glue (fun u => u) uiRev s)
  rw [glue_comp γ.toFun]

end

-- ## 基本亜群とモノドロミー

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
    (hfp : ∀ t, p.toFun (f t) = γ.toFun t) (hf0 : f ui0 = a.1) : (p.liftEnd γ a).1 = f ui1 := by
  have spec := Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
    (p.fiber_start γ a))
  have := lift_unique p spec.1 hf (fun t => by rw [spec.2.1, hfp]) (by rw [spec.2.2, hf0])
  exact congrFun this ui1

theorem liftEnd_homotopic {γ δ : Path (R := R) x y} (h : γ.Homotopic δ) (a : p.Fiber x) :
    p.liftEnd γ a = p.liftEnd δ a := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  have spec := Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
    (p.fiber_start γ a))
  let γ' := Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1 (p.fiber_start γ a))
  obtain ⟨G, hG, hGp, hG0⟩ := exists_lift_homotopy p H hH γ' spec.1 (fun s => by
    show p.toFun (γ' s) = H (s, ui0); rw [spec.2.1, h0])
  -- `G (0, ·)` は定数道 `x` の持ち上げなので定数
  have hleft : (fun t => G (ui0, t)) = fun _ => a.1 := by
    refine lift_unique p (hG.comp (continuous_prod_mk (continuous_const_map _) continuous_id'))
      (continuous_const_map _) (fun t => by
        show p.toFun (G (ui0, t)) = p.toFun a.1; rw [hGp, hx, a.2]) ?_
    show G (ui0, ui0) = a.1; rw [hG0]; exact spec.2.2
  have hright : (fun t => G (ui1, t)) = fun _ => γ' ui1 := by
    refine lift_unique p (hG.comp (continuous_prod_mk (continuous_const_map _) continuous_id'))
      (continuous_const_map _) (fun t => by
        show p.toFun (G (ui1, t)) = p.toFun (γ' ui1); rw [hGp, hy, spec.2.1, γ.target]) ?_
    show G (ui1, ui0) = γ' ui1; rw [hG0]
  apply p.fiberExt
  have e1 : (p.liftEnd δ a).1 = G (ui1, ui1) :=
    p.liftEnd_eq δ a (hG.comp (continuous_prod_mk continuous_id' (continuous_const_map _)))
      (fun t => by show p.toFun (G (t, ui1)) = _; rw [hGp, h1])
      (congrFun hleft ui1)
  rw [e1, congrFun hright ui1]
  rfl

noncomputable def transport (φ : PathClass R x y) (a : p.Fiber x) : p.Fiber y :=
  Quot.lift (fun γ => p.liftEnd γ a) (fun _ _ h => p.liftEnd_homotopic h a) φ

theorem transport_refl (a : p.Fiber x) : p.transport (PathClass.refl (R := R) x) a = a :=
  p.fiberExt (p.liftEnd_eq (Path.refl x) a (continuous_const_map a.1) (fun _ => a.2) rfl)

theorem transport_trans (φ : PathClass R x y) (ψ : PathClass R y z) (a : p.Fiber x) :
    p.transport (φ.comp ψ) a = p.transport ψ (p.transport φ a) := by
  induction φ using Quot.ind with
  | mk γ =>
    induction ψ using Quot.ind with
    | mk δ =>
      show p.liftEnd (γ.trans δ) a = p.liftEnd δ (p.liftEnd γ a)
      have sγ := Classical.choose_spec (exists_lift_path p γ.toFun γ.continuous_toFun a.1
        (p.fiber_start γ a))
      let γ' := Classical.choose (exists_lift_path p γ.toFun γ.continuous_toFun a.1
        (p.fiber_start γ a))
      let b := p.liftEnd γ a
      have sδ := Classical.choose_spec (exists_lift_path p δ.toFun δ.continuous_toFun b.1
        (p.fiber_start δ b))
      let δ' := Classical.choose (exists_lift_path p δ.toFun δ.continuous_toFun b.1
        (p.fiber_start δ b))
      have hjoin : γ' ui1 = δ' ui0 := sδ.2.2.symm
      apply p.fiberExt
      rw [p.liftEnd_eq (γ.trans δ) a (continuous_glue sγ.1 sδ.1 hjoin)
        (fun t => by
          show p.toFun (glue γ' δ' t) = glue γ.toFun δ.toFun t
          rw [glue_comp p.toFun]
          exact glue_congr sγ.2.1 sδ.2.1 t)
        (by rw [glue_zero]; exact sγ.2.2), glue_one _ _ hjoin]
      rfl

end CoveringMap

end

-- ## 共通の枠組み: グラフの被覆と位相空間の被覆

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
  injective := by
    intro a b h
    have h' := congrArg (L.transport (P.symm γ)) h
    rw [← L.transport_trans, ← L.transport_trans, P.trans_symm, L.transport_refl,
      L.transport_refl] at h'
    exact h'
  surjective := by
    intro b
    refine ⟨L.transport (P.symm γ) b, ?_⟩
    rw [← L.transport_trans, P.symm_trans, L.transport_refl]

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

-- ## 円周

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

-- ### 整数の計算

theorem natCast_succ_ge_one (k : Nat) : (1 : R) ≤ natCast (k + 1) := by
  rw [natCast_succ]
  have := add_le_add_right (natCast_nonneg (R := R) k) 1
  rwa [zero_add] at this

theorem int_eq_zero_of_abs_lt_one : ∀ {k : Int}, abs (intCast k : R) < 1 → k = 0
  | Int.ofNat 0, _ => rfl
  | Int.ofNat (k + 1), h => by
      exfalso
      have h' : abs (natCast (k + 1) : R) < 1 := h
      rw [abs_of_nonneg (natCast_nonneg _)] at h'
      exact not_le.mpr h' (natCast_succ_ge_one k)
  | Int.negSucc k, h => by
      exfalso
      have h' : abs (-natCast (k + 1) : R) < 1 := h
      rw [abs_neg, abs_of_nonneg (natCast_nonneg _)] at h'
      exact not_le.mpr h' (natCast_succ_ge_one k)

theorem intCast_sub (m n : Int) : (intCast (m - n) : R) = intCast m - intCast n := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg]; rfl

theorem intCast_injective {m n : Int} (h : (intCast m : R) = intCast n) : m = n := by
  have : m - n = 0 := int_eq_zero_of_abs_lt_one (R := R)
    (by rw [intCast_sub, h, sub_self, abs_zero]; exact zero_lt_one)
  omega

theorem eq_of_close {a r w : R} {m : Int} (hr : abs (r - a) < 1 / 2) (hw : abs (w - a) < 1 / 2)
    (hm : w = r + intCast m) : w = r := by
  have hm0 : m = 0 := by
    apply int_eq_zero_of_abs_lt_one (R := R)
    have e : (intCast m : R) = (w - a) + (a - r) := by
      rw [hm, sub_add_sub_cancel]
      rw [sub_def, add_comm r, add_assoc, add_neg_cancel, add_zero]
    rw [e]
    refine lt_of_le_of_lt (abs_add _ _) ?_
    have hr' : abs (a - r) < 1 / 2 := by rw [abs_sub_comm]; exact hr
    have := add_lt_add hw hr'
    rwa [add_halves] at this
  rw [hm, hm0]; exact add_zero r

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
    IsOpen ({z | ∃ w, w ∈ W ∧ proj w = z} : Set (Circle R)) := by
  rw [isOpen_circle_iff]
  intro r ⟨w, hwW, hwr⟩
  obtain ⟨n, hn⟩ := proj_eq_iff.mp hwr
  obtain ⟨ε, hε, hball⟩ := hW w hwW
  refine ⟨ε, hε, fun r' hr' => ⟨r' - intCast n, hball _ ?_, ?_⟩⟩
  · have e : r' - intCast n - w = r' - r := by
      rw [hn, sub_def, sub_def, sub_def, neg_add]; ac_rfl
    rw [e]; exact hr'
  · show proj (r' - intCast n) = proj r'
    rw [← proj_add_int (r' - intCast n) n, sub_add_cancel]

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
    EvenlyCovered (proj : R → Circle R) {z | ∃ r, r ∈ ball a (1 / 2) ∧ proj r = z} := by
  refine ⟨Int, fun n => ball (a + intCast n) (1 / 2), circleSec a, fun n => isOpen_ball _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- `p⁻¹ U` はシートの合併
    intro e ⟨r, hr, hre⟩
    obtain ⟨n, hn⟩ := proj_eq_iff.mp hre
    refine ⟨n, ?_⟩
    show abs (e - (a + intCast n)) < 1 / 2
    rw [hn, abs_shift]; exact hr
  · -- シートは互いに交わらない
    intro m n e hm hn
    apply intCast_injective (R := R)
    have h1 : abs (e - (a + intCast m)) < 1 / 2 := hm
    have h2 : abs (e - (a + intCast n)) < 1 / 2 := hn
    have e1 : (intCast m : R) = a + intCast m - a := by rw [add_comm a, add_sub_cancel]
    have e2 : (intCast n : R) = a + intCast n - a := by rw [add_comm a, add_sub_cancel]
    refine Classical.byContradiction fun hne => ?_
    have := eq_of_close (a := e) (r := a + intCast m) (w := a + intCast n) (m := n - m)
      (by rw [abs_sub_comm]; exact h1) (by rw [abs_sub_comm]; exact h2)
      (by rw [intCast_sub, add_assoc, sub_def, add_comm (intCast n), ← add_assoc (intCast m),
            add_neg_cancel, zero_add])
    exact hne (by
      have h3 := congrArg (fun t => t - a) this
      simp only at h3
      rw [← e1, ← e2] at h3
      exact h3.symm)
  · -- 逆写像はシートに入り、`p` で戻る
    intro n z ⟨r, hr, hrz⟩
    rw [← hrz, circleSec_proj hr n]
    refine ⟨?_, proj_add_int r n⟩
    show abs (r + intCast n - (a + intCast n)) < 1 / 2
    rw [abs_shift]; exact hr
  · -- シートの点 `e` については `s (p e) = e`
    intro n e he
    have he' : abs (e - (a + intCast n)) < 1 / 2 := he
    have hr : abs (e - intCast n - a) < 1 / 2 := by
      have : e - intCast n - a = e - (a + intCast n) := by
        rw [sub_def, sub_def, sub_def, neg_add]; ac_rfl
      rw [this]; exact he'
    have hpe : proj e = proj (e - intCast n) := by
      rw [← proj_add_int (e - intCast n) n, sub_add_cancel]
    rw [hpe, circleSec_proj hr n, sub_add_cancel]
  · -- 逆写像は連続（`proj` が開写像であることから）
    intro n
    intro O hO
    let W : Set R := {r | abs (r - a) < 1 / 2 ∧ r + intCast n ∈ O}
    have hWo : IsOpen W :=
      isOpen_inter _ _ (isOpen_ball a (1 / 2))
        (continuous_add continuous_id' (continuous_const _) O hO)
    refine isOpen_subtype_iff.mpr ⟨_, isOpen_image_proj hWo, ?_⟩
    apply Set.ext
    intro z
    constructor
    · intro hz
      obtain ⟨r, hr, hrz⟩ := z.2
      refine ⟨r, ⟨hr, ?_⟩, hrz⟩
      have hz' : circleSec a n z.1 ∈ O := hz
      rw [← hrz, circleSec_proj hr n] at hz'
      exact hz'
    · intro ⟨w, ⟨hw, hwO⟩, hwz⟩
      show circleSec a n z.1 ∈ O
      rw [← hwz, circleSec_proj hw n]; exact hwO

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

-- ## π₁(S¹) ≃ ℤ

section

open CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

def base : Circle R := proj 0

theorem proj_intCast (m : Int) : proj (intCast m : R) = base := by
  have := proj_add_int (0 : R) m
  rw [zero_add] at this
  exact this

def fibInt (m : Int) : circleCovering.Fiber (base : Circle R) := ⟨intCast m, proj_intCast m⟩

theorem fiber_int (a : circleCovering.Fiber (base : Circle R)) : ∃ n : Int, a.1 = intCast n := by
  obtain ⟨n, hn⟩ := proj_eq_iff.mp a.2
  refine ⟨-n, ?_⟩
  rw [intCast_neg]
  have h : a.1 + intCast n = 0 := hn.symm
  have := neg_eq_of_add_eq_zero h
  rw [← this, neg_neg]

theorem transport_fibInt (φ : PathClass R (base : Circle R) base) (m : Int) :
    (circleCovering.transport φ (fibInt m)).1 = (circleCovering.transport φ (fibInt 0)).1 + intCast m := by
  induction φ using Quot.ind with
  | mk γ =>
    show (circleCovering.liftEnd γ (fibInt m)).1 = (circleCovering.liftEnd γ (fibInt 0)).1 + intCast m
    have spec := Classical.choose_spec (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
      (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0)))
    rw [circleCovering.liftEnd_eq γ (fibInt m)
      (f := fun t => Classical.choose (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
        (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0))) t + intCast m)
      (continuous_add spec.1 (continuous_const _))
      (fun t => by
        show proj (_ + intCast m) = γ.toFun t
        rw [proj_add_int]; exact spec.2.1 t)
      (by show _ + intCast m = intCast m; rw [spec.2.2]; exact zero_add _)]
    rfl

noncomputable def deg (φ : PathClass R (base : Circle R) base) : Int :=
  Classical.choose (fiber_int (circleCovering.transport φ (fibInt 0)))

theorem deg_spec (φ : PathClass R (base : Circle R) base) :
    circleCovering.transport φ (fibInt 0) = fibInt (deg φ) :=
  circleCovering.fiberExt (Classical.choose_spec (fiber_int (circleCovering.transport φ (fibInt 0))))

theorem deg_comp (φ ψ : PathClass R (base : Circle R) base) :
    deg (φ.comp ψ) = deg φ + deg ψ := by
  apply intCast_injective (R := R)
  have h := congrArg Subtype.val (deg_spec (φ.comp ψ))
  rw [circleCovering.transport_trans, deg_spec φ, transport_fibInt, deg_spec ψ] at h
  have h' : (intCast (deg (φ.comp ψ)) : R) = intCast (deg ψ) + intCast (deg φ) := h.symm
  rw [h', intCast_add, add_comm]

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
    φ = PathClass.refl base := by
  induction φ using Quot.ind with
  | mk γ =>
    have spec := Classical.choose_spec (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
      (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0)))
    let γ' := Classical.choose (exists_lift_path circleCovering γ.toFun γ.continuous_toFun
      (fibInt 0).1 (circleCovering.fiber_start γ (fibInt 0)))
    have h0 : γ' ui0 = 0 := spec.2.2
    have h1 : γ' ui1 = 0 := by
      have := congrArg Subtype.val (deg_spec (PathClass.mk γ))
      rw [show deg (PathClass.mk γ) = 0 from h] at this
      exact this
    refine PathClass.sound ⟨fun q => proj ((1 - q.2.1) * γ' q.1), ?_, fun s => ?_, fun s => ?_,
      fun t => ?_, fun t => ?_⟩
    · exact continuous_proj.comp (continuous_mul
        (continuous_sub (continuous_const _) (continuous_subtype_val.comp continuous_snd))
        (spec.1.comp continuous_fst))
    · show proj ((1 - 0) * γ' s) = γ.toFun s
      rw [sub_zero, one_mul]; exact spec.2.1 s
    · show proj ((1 - 1) * γ' s) = base
      rw [sub_self, zero_mul]; rfl
    · show proj ((1 - t.1) * γ' ui0) = base
      rw [h0, mul_zero]; rfl
    · show proj ((1 - t.1) * γ' ui1) = base
      rw [h1, mul_zero]; rfl

theorem deg_injective : Function.Injective (deg (R := R)) := by
  intro φ ψ h
  have hz : deg (φ.comp ψ.inv) = 0 := by
    rw [deg_comp, deg_inv]; omega
  have hk := deg_eq_zero hz
  calc φ = φ.comp (PathClass.refl base) := (PathClass.comp_refl φ).symm
    _ = φ.comp (ψ.inv.comp ψ) := congrArg φ.comp (PathClass.inv_comp ψ).symm
    _ = (φ.comp ψ.inv).comp ψ := (PathClass.comp_assoc φ ψ.inv ψ).symm
    _ = (PathClass.refl base).comp ψ := by rw [hk]
    _ = ψ := PathClass.refl_comp ψ

def loopN (n : Int) : Path (R := R) (base : Circle R) base where
  toFun t := proj (intCast n * t.1)
  continuous_toFun := continuous_proj.comp (continuous_mul (continuous_const _) continuous_subtype_val)
  source := by show proj (intCast n * 0) = base; rw [mul_zero]; rfl
  target := by show proj (intCast n * 1) = base; rw [mul_one]; exact proj_intCast n

theorem deg_surjective : Function.Surjective (deg (R := R)) := by
  intro n
  refine ⟨PathClass.mk (loopN n), intCast_injective (R := R) ?_⟩
  have h := congrArg Subtype.val (deg_spec (PathClass.mk (loopN (R := R) n)))
  refine (show (intCast (deg (PathClass.mk (loopN (R := R) n))) : R) = _ from h.symm).trans ?_
  show (circleCovering.liftEnd (loopN n) (fibInt 0)).1 = intCast n
  rw [circleCovering.liftEnd_eq (loopN n) (fibInt 0) (f := fun t => intCast n * t.1)
    (continuous_mul (continuous_const _) continuous_subtype_val) (fun _ => rfl)
    (show intCast n * 0 = intCast 0 by rw [mul_zero]; rfl)]
  show intCast n * 1 = intCast n
  rw [mul_one]

theorem pi1_circle :
    (∀ φ ψ : PathClass R (base : Circle R) base, deg (φ.comp ψ) = deg φ + deg ψ) ∧
      Function.Bijective (deg (R := R)) :=
  ⟨deg_comp, ⟨deg_injective, deg_surjective⟩⟩

end

end CovSpace

#print axioms CovSpace.pi1_circle
