import CoverProbeC

/-!
# 試作D: π₁(花束) ≃ ℤ — 被覆機構による証明

ℝ → S¹ から π₁(S¹) ≃ ℤ を出す議論の離散版を、試作Cの機構で完遂する。

同型 `deg : π₁(花束) → ℤ` は**モノドロミー**で定義する:
ループ γ の持ち上げを基点 0 から走らせ、終点の整数を読む。

- **準同型性** — デッキ変換(ℤ の平行移動)が持ち上げと可換なことから
  (`shift_wf` + `transport_apply`)
- **単射性** — 全空間 zcover(直線グラフ = 木)が**単連結**なことから
  (`zc_drift`: 既約な道は単調に進む → 既約な閉道は空)
- **全射性** — ループの冪がすべての整数を実現することから

これは位相空間版で「ℝ が単連結」「ℝ が弧状連結」「デッキ変換群 ≃ ℤ」が
果たす役割の、そのままの離散類似である。
-/

namespace CoverProbe

open SGraph

/-! ## PathClass の群法則(基点つきで使う形) -/

namespace SGraph.PathClass

variable {X : SGraph} {v w : X.V}

theorem comp_refl (γ : PathClass X v w) :
    γ.comp (PathClass.mk (Wf.nil w)) = γ := by
  induction γ using Quot.ind with
  | mk a => exact mk_eq_of_eq (List.append_nil a.1) (Wf.append a.2 (.nil w)) a.2

theorem refl_comp (γ : PathClass X v w) :
    (PathClass.mk (Wf.nil v)).comp γ = γ := by
  induction γ using Quot.ind with
  | mk a => exact mk_eq_of_eq (List.nil_append a.1) (Wf.append (.nil v) a.2) a.2

theorem comp_assoc {u z : X.V} (γ : PathClass X v u) (δ : PathClass X u w)
    (ε : PathClass X w z) :
    (γ.comp δ).comp ε = γ.comp (δ.comp ε) := by
  induction γ using Quot.ind with
  | mk a =>
    induction δ using Quot.ind with
    | mk b =>
      induction ε using Quot.ind with
      | mk c =>
        exact mk_eq_of_eq (List.append_assoc a.1 b.1 c.1)
          (Wf.append (Wf.append a.2 b.2) c.2) (Wf.append a.2 (Wf.append b.2 c.2))

theorem inv_comp (γ : PathClass X v w) :
    γ.inv.comp γ = PathClass.mk (Wf.nil w) := by
  induction γ using Quot.ind with
  | mk a =>
    exact PathClass.sound (Wf.append a.2.revWord a.2) (.nil w)
      (homotopic_revWord_append a.1)

end SGraph.PathClass

/-! ## 簡約の射による押し出し(全空間の簡約を底空間に写す) -/

theorem mapWord_reduces {Y X : SGraph} (p : GraphHom Y X) {m m' : List Y.E}
    (h : Reduces Y m m') : Reduces X (mapWord p m) (mapWord p m') := by
  induction h with
  | cancel m₁ m₂ e =>
      rw [mapWord_append, mapWord_cons, mapWord_cons, ← p.bar_toE, mapWord_append]
      exact .cancel _ _ _
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-! ## zcover の計算補題 -/

theorem zc_init_true (i : Int) : zcover.init (i, true) = i := rfl
theorem zc_init_false (i : Int) : zcover.init (i, false) = i + 1 := rfl
theorem zc_term_true (i : Int) : zcover.term (i, true) = i + 1 := rfl
theorem zc_term_false (i : Int) : zcover.term (i, false) = i := rfl

/-! ## zcover は単連結(木である)

既約な道は単調に進む(`zc_drift`)。核心は「向きが反転する隣接2辺は
自動的に backtrack」という直線グラフの性質で、これが「木には既約な閉道が
ない」の中身である。 -/

theorem zc_drift : ∀ {m : List zcover.E} {e : zcover.E} {v w : Int},
    Wf zcover v (e :: m) w → IsReduced (e :: m) →
    (e.2 = true ∧ v < w) ∨ (e.2 = false ∧ w < v)
  | [], e, v, w, h, _ => by
      have hi := Wf.cons_inv h
      have hw := Wf.nil_inv hi.2
      cases e with
      | mk i b =>
        cases b with
        | true =>
            refine .inl ⟨rfl, ?_⟩
            have h1 : v = i := hi.1
            have h2 : (i + 1 : Int) = w := hw
            omega
        | false =>
            refine .inr ⟨rfl, ?_⟩
            have h1 : v = i + 1 := hi.1
            have h2 : (i : Int) = w := hw
            omega
  | f :: m, e, v, w, h, hr => by
      have hi := Wf.cons_inv h
      have hrf : f ≠ zcover.bar e := hr.1
      have hstep := zc_drift hi.2 hr.2
      cases e with
      | mk i b =>
        cases f with
        | mk j c =>
          cases b with
          | true =>
              refine .inl ⟨rfl, ?_⟩
              have h1 : v = i := hi.1
              cases hstep with
              | inl hrec =>
                  have h2 : (i + 1 : Int) < w := hrec.2
                  omega
              | inr hrec =>
                  exfalso
                  apply hrf
                  have hc : c = false := hrec.1
                  subst hc
                  have hadj := (Wf.cons_inv hi.2).1
                  have hj : (i + 1 : Int) = j + 1 := hadj
                  have hji : j = i := by omega
                  subst hji
                  rfl
          | false =>
              refine .inr ⟨rfl, ?_⟩
              have h1 : v = i + 1 := hi.1
              cases hstep with
              | inr hrec =>
                  have h2 : w < (i : Int) := hrec.2
                  omega
              | inl hrec =>
                  exfalso
                  apply hrf
                  have hc : c = true := hrec.1
                  subst hc
                  have hadj := (Wf.cons_inv hi.2).1
                  have hj : (i : Int) = j := hadj
                  have hji : j = i := by omega
                  subst hji
                  rfl

/-- **zcover の単連結性**: 既約な閉道は空。 -/
theorem zc_reduced_closed : ∀ {m : List zcover.E} {v : Int},
    Wf zcover v m v → IsReduced m → m = []
  | [], _, _, _ => rfl
  | e :: m, v, h, hr => by
      exfalso
      cases zc_drift h hr with
      | inl h' =>
          have hlt : v < v := h'.2
          omega
      | inr h' =>
          have hlt : v < v := h'.2
          omega

/-! ## デッキ変換: ℤ の平行移動は持ち上げと可換 -/

/-- 語を `k` だけ平行移動する(デッキ変換の辺への作用)。 -/
def shiftWord (k : Int) (m : List zcover.E) : List zcover.E :=
  m.map (fun e => (e.1 + k, e.2))

theorem mapWord_shift (k : Int) : ∀ (m : List zcover.E),
    mapWord zcoverHom (shiftWord k m) = mapWord zcoverHom m
  | [] => rfl
  | e :: m => congrArg (fun t => e.2 :: t) (mapWord_shift k m)

theorem shift_wf (k : Int) : ∀ (m : List zcover.E) {v w : Int},
    Wf zcover v m w → Wf zcover (v + k) (shiftWord k m) (w + k)
  | [], v, w, h => by
      have hv : v = w := Wf.nil_inv h
      subst hv
      exact Wf.nil (G := zcover) (v + k)
  | e :: m, v, w, h => by
      have hi := Wf.cons_inv h
      have ih := shift_wf k m hi.2
      cases e with
      | mk i b =>
        cases b with
        | true =>
            have h1 : v = i := hi.1
            subst h1
            have ih' : Wf zcover ((v + 1 : Int) + k) (shiftWord k m) (w + k) := ih
            rw [show ((v + 1 : Int) + k) = v + k + 1 from by omega] at ih'
            exact Wf.cons (G := zcover) ((v + k, true) : Int × Bool) ih'
        | false =>
            have h1 : v = i + 1 := hi.1
            subst h1
            rw [show ((i + 1 : Int) + k) = i + k + 1 from by omega]
            have ih' : Wf zcover ((i : Int) + k) (shiftWord k m) (w + k) := ih
            exact Wf.cons (G := zcover) ((i + k, false) : Int × Bool) ih'

/-! ## モノドロミー次数 deg -/

/-- ファイバーの基点(0 の持ち上げ)。 -/
def basePt : {y : zcover.V // zcoverHom.toV y = ()} := ⟨(0 : Int), rfl⟩

/-- **モノドロミー次数**: ループを 0 から持ち上げ、終点の整数を読む。 -/
noncomputable def deg (γ : PathClass bouquet () ()) : Int :=
  (zcover_isCovering.transport γ basePt).1

/-- 平行移動との可換性: `i` からの持ち上げの終点は `deg γ + i`。 -/
theorem transport_apply (γ : PathClass bouquet () ()) (i : Int) :
    (zcover_isCovering.transport γ ⟨i, rfl⟩).1 = deg γ + i := by
  induction γ using Quot.ind with
  | mk ld =>
    match zcover_isCovering.liftEnd_spec basePt ld.2 with
    | ⟨m, hm, hmap⟩ =>
      have hm' : Wf zcover ((0 : Int) + i) (shiftWord i m)
          (deg (Quot.mk _ ld) + i) := shift_wf i m hm
      rw [show ((0 : Int) + i) = i from by omega] at hm'
      exact zcover_isCovering.liftEnd_eq ⟨i, rfl⟩ ld.2 hm'
        ((mapWord_shift i m).trans hmap)

theorem deg_comp (γ δ : PathClass bouquet () ()) :
    deg (γ.comp δ) = deg γ + deg δ := by
  have hfix : zcover_isCovering.transport γ basePt = ⟨deg γ, rfl⟩ :=
    IsCovering.fiberExt rfl
  have h : deg (γ.comp δ) = deg δ + deg γ := by
    show (zcover_isCovering.transport (γ.comp δ) basePt).1 = _
    rw [zcover_isCovering.transport_trans γ δ basePt, hfix, transport_apply]
  omega

theorem deg_refl : deg (PathClass.mk (Wf.nil (G := bouquet) ())) = 0 :=
  congrArg Subtype.val (zcover_isCovering.transport_refl basePt)

/-- 花束のループの類。 -/
def loop : PathClass bouquet () () := PathClass.mk loopWf

theorem deg_loop : deg loop = 1 := by
  have h : deg loop = (0 : Int) + 1 :=
    zcover_isCovering.liftEnd_eq basePt loopWf
      (Wf.cons (G := zcover) ((0, true) : Int × Bool) (Wf.nil (zcover.term (0, true)))) rfl
  omega

theorem deg_inv (γ : PathClass bouquet () ()) : deg γ.inv = - deg γ := by
  have h := deg_comp γ.inv γ
  rw [PathClass.inv_comp, deg_refl] at h
  omega

/-! ## 全射性: ループの冪 -/

def loopPow : Nat → PathClass bouquet () ()
  | 0 => PathClass.mk (Wf.nil (G := bouquet) ())
  | k + 1 => (loopPow k).comp loop

theorem deg_loopPow : ∀ k : Nat, deg (loopPow k) = Int.ofNat k
  | 0 => deg_refl
  | k + 1 => by
      have h := deg_comp (loopPow k) loop
      rw [deg_loopPow k, deg_loop] at h
      exact h

theorem deg_surjective : ∀ n : Int, ∃ γ : PathClass bouquet () (), deg γ = n := by
  intro n
  match n with
  | Int.ofNat k => exact ⟨loopPow k, deg_loopPow k⟩
  | Int.negSucc k =>
      refine ⟨(loopPow (k + 1)).inv, ?_⟩
      rw [deg_inv, deg_loopPow]
      rfl

/-! ## 単射性: 全空間の単連結性から -/

/-- 核が自明: 持ち上げが 0 に戻るループは自明。全空間の既約閉道が空である
    こと(単連結性)を、簡約の押し出しで底空間へ運ぶ。 -/
theorem deg_eq_zero {γ : PathClass bouquet () ()} (h : deg γ = 0) :
    γ = PathClass.mk (Wf.nil (G := bouquet) ()) := by
  induction γ using Quot.ind with
  | mk ld =>
    match zcover_isCovering.liftEnd_spec basePt ld.2 with
    | ⟨m, hm, hmap⟩ =>
      have h0 : (zcover_isCovering.liftEnd basePt ld.1 ld.2).1 = (0 : Int) := h
      rw [h0] at hm
      have hm0 : Wf zcover (0 : Int) m (0 : Int) := hm
      letI : DecidableEq zcover.E := fun a b => Classical.propDecidable _
      have hred : Wf zcover (0 : Int) (SGraph.reduce m) (0 : Int) := Wf.reduce hm0
      have hnil : SGraph.reduce m = [] :=
        zc_reduced_closed hred (reduce_isReduced m)
      have hR : Reduces zcover m [] := hnil ▸ reduces_reduce m
      have hdown := (mapWord_reduces zcoverHom hR).toHomotopic
      rw [hmap, mapWord_nil] at hdown
      exact PathClass.sound ld.2 (Wf.nil (G := bouquet) ()) hdown

theorem deg_injective {γ δ : PathClass bouquet () ()} (h : deg γ = deg δ) :
    γ = δ := by
  have hz : deg (γ.comp δ.inv) = 0 := by
    rw [deg_comp, deg_inv]
    omega
  have hker := deg_eq_zero hz
  calc γ = γ.comp (PathClass.mk (Wf.nil (G := bouquet) ())) := (PathClass.comp_refl γ).symm
    _ = γ.comp (δ.inv.comp δ) := by rw [PathClass.inv_comp]
    _ = (γ.comp δ.inv).comp δ := (PathClass.comp_assoc γ δ.inv δ).symm
    _ = (PathClass.mk (Wf.nil (G := bouquet) ())).comp δ := by rw [hker]
    _ = δ := PathClass.refl_comp δ

/-! ## 主定理 -/

/-- **π₁(花束) ≃ ℤ**: モノドロミー次数 `deg` は積を和に写す全単射。
    位相空間版の π₁(S¹) ≃ ℤ の離散類似が、被覆(zcover)・単連結性・
    デッキ変換という同じ部品立てで完結した。 -/
theorem pi1_bouquet_equiv_int :
    ∃ φ : PathClass bouquet () () → Int,
      (∀ γ δ, φ (γ.comp δ) = φ γ + φ δ) ∧
      (∀ γ δ, φ γ = φ δ → γ = δ) ∧
      (∀ n : Int, ∃ γ, φ γ = n) :=
  ⟨deg, deg_comp, fun _ _ => deg_injective, deg_surjective⟩

#print axioms pi1_bouquet_equiv_int

end CoverProbe
