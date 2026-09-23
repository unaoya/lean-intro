-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import «06_Topology»

-- # 発展演習: グラフの被覆

-- ## Part A: Serre グラフと道

structure SGraph where
  V : Type
  E : Type
  init : E → V
  bar : E → E
  bar_bar : ∀ e, bar (bar e) = e
  bar_ne : ∀ e, bar e ≠ e

namespace SGraph

variable {G : SGraph}

def term (G : SGraph) (e : G.E) : G.V := G.init (G.bar e)

theorem term_bar (e : G.E) : G.term (G.bar e) = G.init e :=
  sorry

inductive Wf (G : SGraph) : G.V → List G.E → G.V → Prop
  | nil (v : G.V) : Wf G v [] v
  | cons (e : G.E) {l : List G.E} {w : G.V} :
      Wf G (G.term e) l w → Wf G (G.init e) (e :: l) w

theorem Wf.nil_inv {v w : G.V} (h : Wf G v [] w) : v = w := by
  cases h with
  | nil => rfl

theorem Wf.cons_inv {v w : G.V} {e : G.E} {l : List G.E} (h : Wf G v (e :: l) w) :
    v = G.init e ∧ Wf G (G.term e) l w := by
  cases h with
  | cons _ h' => exact ⟨rfl, h'⟩

theorem Wf.append {v u w : G.V} : ∀ {l₁ l₂ : List G.E},
    Wf G v l₁ u → Wf G u l₂ w → Wf G v (l₁ ++ l₂) w :=
  sorry

theorem Wf.end_unique : ∀ {y w₁ w₂ : G.V} {m : List G.E},
    Wf G y m w₁ → Wf G y m w₂ → w₁ = w₂ :=
  sorry

theorem Wf.append_split : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E},
    Wf G v (l₁ ++ l₂) w → ∃ u, Wf G v l₁ u ∧ Wf G u l₂ w :=
  sorry

def revWord (G : SGraph) (l : List G.E) : List G.E := (l.map G.bar).reverse

theorem revWord_cons (e : G.E) (l : List G.E) :
    revWord G (e :: l) = revWord G l ++ [G.bar e] := by
  simp [revWord]

theorem revWord_append (l l' : List G.E) :
    revWord G (l ++ l') = revWord G l' ++ revWord G l := by
  simp [revWord]

theorem Wf.revWord : ∀ {v w : G.V} {l : List G.E},
    Wf G v l w → Wf G w (SGraph.revWord G l) v :=
  sorry

end SGraph

def bouquet : SGraph where
  V := Unit
  E := Bool
  init _ := ()
  bar := Bool.not
  bar_bar := by decide
  bar_ne := by decide

instance : DecidableEq bouquet.E := inferInstanceAs (DecidableEq Bool)

def zcover : SGraph where
  V := Int
  E := Int × Bool
  init e := cond e.2 e.1 (e.1 + 1)
  bar e := (e.1, !e.2)
  bar_bar e := by cases e with | mk i b => simp
  bar_ne := by
    intro e h
    cases e with
    | mk i b => cases b <;> simp at h

-- ## Part B: ホモトピーと正規形定理

namespace SGraph

variable {G : SGraph}

def IsReduced : List G.E → Prop
  | [] => True
  | [_] => True
  | e :: f :: l => f ≠ G.bar e ∧ IsReduced (f :: l)

theorem IsReduced.tail : ∀ {l : List G.E} {e : G.E}, IsReduced (e :: l) → IsReduced l
  | [], _, _ => trivial
  | _ :: _, _, h => h.2

inductive Homotopic (G : SGraph) : List G.E → List G.E → Prop
  | cancel (l₁ l₂ : List G.E) (e : G.E) :
      Homotopic G (l₁ ++ e :: G.bar e :: l₂) (l₁ ++ l₂)
  | refl (l : List G.E) : Homotopic G l l
  | symm {l l' : List G.E} : Homotopic G l l' → Homotopic G l' l
  | trans {l l' l'' : List G.E} :
      Homotopic G l l' → Homotopic G l' l'' → Homotopic G l l''

inductive Reduces (G : SGraph) : List G.E → List G.E → Prop
  | cancel (l₁ l₂ : List G.E) (e : G.E) :
      Reduces G (l₁ ++ e :: G.bar e :: l₂) (l₁ ++ l₂)
  | refl (l : List G.E) : Reduces G l l
  | trans {l l' l'' : List G.E} :
      Reduces G l l' → Reduces G l' l'' → Reduces G l l''

theorem Reduces.toHomotopic {l l' : List G.E} (h : Reduces G l l') :
    Homotopic G l l' := by
  induction h with
  | cancel l₁ l₂ e => exact .cancel l₁ l₂ e
  | refl l => exact .refl l
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Reduces.cons {l l' : List G.E} (e : G.E) (h : Reduces G l l') :
    Reduces G (e :: l) (e :: l') := by
  induction h with
  | cancel l₁ l₂ f => exact .cancel (e :: l₁) l₂ f
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

section Reduce

variable [DecidableEq G.E]

def rcons (e : G.E) : List G.E → List G.E
  | [] => [e]
  | f :: r => if f = G.bar e then r else e :: f :: r

theorem rcons_nil (e : G.E) : rcons e ([] : List G.E) = [e] := rfl

theorem rcons_cons (e f : G.E) (r : List G.E) :
    rcons e (f :: r) = if f = G.bar e then r else e :: f :: r := rfl

def reduce : List G.E → List G.E
  | [] => []
  | e :: l => rcons e (reduce l)

theorem reduce_cons (e : G.E) (l : List G.E) : reduce (e :: l) = rcons e (reduce l) := rfl

theorem isReduced_rcons {e : G.E} : ∀ {m : List G.E}, IsReduced m → IsReduced (rcons e m) :=
  sorry

theorem reduce_isReduced : ∀ l : List G.E, IsReduced (reduce l) :=
  sorry

theorem rcons_rcons_bar (e : G.E) : ∀ (m : List G.E), IsReduced m →
    rcons e (rcons (G.bar e) m) = m :=
  sorry

theorem reduce_append_cancel (e : G.E) : ∀ (l₁ l₂ : List G.E),
    reduce (l₁ ++ e :: G.bar e :: l₂) = reduce (l₁ ++ l₂) :=
  sorry

theorem reduces_cons_rcons (e : G.E) (m : List G.E) :
    Reduces G (e :: m) (rcons e m) := by
  match m with
  | [] => exact .refl _
  | f :: r =>
    by_cases h : f = G.bar e
    · subst h
      rw [rcons_cons, if_pos rfl]
      exact Reduces.cancel [] r e
    · rw [rcons_cons, if_neg h]
      exact .refl _

theorem reduces_reduce : ∀ l : List G.E, Reduces G l (reduce l) :=
  sorry

theorem homotopic_iff_reduce_eq {l l' : List G.E} :
    Homotopic G l l' ↔ reduce l = reduce l' :=
  sorry

theorem reduce_eq_self_of_isReduced : ∀ {l : List G.E}, IsReduced l → reduce l = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by
      rw [reduce_cons, reduce_eq_self_of_isReduced h.2, rcons_cons, if_neg h.1]

theorem eq_of_homotopic_of_isReduced {l l' : List G.E}
    (hl : IsReduced l) (hl' : IsReduced l') (h : Homotopic G l l') : l = l' :=
  sorry

end Reduce

theorem Wf.of_append_cancel : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E} {e : G.E},
    Wf G v (l₁ ++ e :: G.bar e :: l₂) w → Wf G v (l₁ ++ l₂) w :=
  sorry

theorem Wf.of_reduces {v w : G.V} {l l' : List G.E} (h : Reduces G l l') :
    Wf G v l w → Wf G v l' w := by
  induction h with
  | cancel l₁ l₂ e => exact fun hw => Wf.of_append_cancel l₁ hw
  | refl l => exact id
  | trans _ _ ih₁ ih₂ => exact fun hw => ih₂ (ih₁ hw)

theorem Wf.reduce [DecidableEq G.E] {v w : G.V} {l : List G.E} (hw : Wf G v l w) :
    Wf G v (SGraph.reduce l) w :=
  sorry

end SGraph

example : SGraph.reduce (G := bouquet) [true, false, true] = [true] := rfl
example : SGraph.reduce (G := bouquet) [true, true, false, false] = [] := rfl

-- ## Part C: π₁ 亜群

namespace SGraph

variable {G : SGraph}

theorem Homotopic.appendRight {l l' : List G.E} (r : List G.E)
    (h : Homotopic G l l') : Homotopic G (l ++ r) (l' ++ r) := by
  induction h with
  | cancel l₁ l₂ e =>
      rw [List.append_assoc, List.append_assoc]
      exact .cancel l₁ (l₂ ++ r) e
  | refl l => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Homotopic.appendLeft (r : List G.E) {l l' : List G.E}
    (h : Homotopic G l l') : Homotopic G (r ++ l) (r ++ l') := by
  induction h with
  | cancel l₁ l₂ e =>
      rw [← List.append_assoc, ← List.append_assoc]
      exact .cancel (r ++ l₁) l₂ e
  | refl l => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Homotopic.revWordCong {l l' : List G.E} (h : Homotopic G l l') :
    Homotopic G (revWord G l) (revWord G l') :=
  sorry

theorem homotopic_revWord_append : ∀ l : List G.E, Homotopic G (revWord G l ++ l) [] :=
  sorry

theorem homotopic_append_revWord : ∀ l : List G.E, Homotopic G (l ++ revWord G l) [] :=
  sorry

def PathClass (G : SGraph) (v w : G.V) : Type :=
  Quot (fun a b : {l : List G.E // Wf G v l w} => Homotopic G a.1 b.1)

namespace PathClass

def mk {v w : G.V} {l : List G.E} (hl : Wf G v l w) : PathClass G v w :=
  Quot.mk _ ⟨l, hl⟩

theorem mk_eq_of_eq {v w : G.V} {l l' : List G.E}
    (h : l = l') (hl : Wf G v l w) (hl' : Wf G v l' w) : mk hl = mk hl' := by
  subst h; rfl

theorem sound {v w : G.V} {l l' : List G.E}
    (hl : Wf G v l w) (hl' : Wf G v l' w) (h : Homotopic G l l') : mk hl = mk hl' :=
  Quot.sound h

def refl (v : G.V) : PathClass G v v := mk (Wf.nil v)

def comp {v u w : G.V} (φ : PathClass G v u) (ψ : PathClass G u w) : PathClass G v w :=
  Quot.lift
    (fun a => Quot.lift (fun b => mk (Wf.append a.2 b.2))
      (fun _ _ hb => Quot.sound (Homotopic.appendLeft a.1 hb)) ψ)
    (fun _ _ ha => by
      induction ψ using Quot.ind with
      | mk b =>
        apply Quot.sound
        exact Homotopic.appendRight b.1 ha)
    φ

def inv {v w : G.V} (φ : PathClass G v w) : PathClass G w v :=
  Quot.lift (fun a => mk a.2.revWord)
    (fun _ _ h => Quot.sound (Homotopic.revWordCong h)) φ

variable {v w : G.V}

theorem refl_comp (γ : PathClass G v w) : (refl v).comp γ = γ :=
  sorry

theorem comp_refl (γ : PathClass G v w) : γ.comp (refl w) = γ :=
  sorry

theorem comp_assoc {u z : G.V} (γ : PathClass G v u) (δ : PathClass G u w)
    (ε : PathClass G w z) : (γ.comp δ).comp ε = γ.comp (δ.comp ε) :=
  sorry

theorem inv_comp (γ : PathClass G v w) : γ.inv.comp γ = refl w :=
  sorry

theorem comp_inv (γ : PathClass G v w) : γ.comp γ.inv = refl v :=
  sorry

end PathClass

end SGraph

-- ## Part D: 被覆と持ち上げ

namespace SGraph

structure GraphHom (Y X : SGraph) where
  toV : Y.V → X.V
  toE : Y.E → X.E
  init_toE : ∀ e, X.init (toE e) = toV (Y.init e)
  bar_toE : ∀ e, X.bar (toE e) = toE (Y.bar e)

variable {Y X : SGraph}

theorem GraphHom.term_toE (p : GraphHom Y X) (e : Y.E) :
    X.term (p.toE e) = p.toV (Y.term e) := by
  rw [term, p.bar_toE, p.init_toE]
  rfl

structure Covering (Y X : SGraph) extends GraphHom Y X where
  star_surj : ∀ (y : Y.V) (f : X.E), X.init f = toV y →
    ∃ e : Y.E, Y.init e = y ∧ toE e = f
  star_inj : ∀ e e' : Y.E, Y.init e = Y.init e' → toE e = toE e' → e = e'

def mapWord {A B : Type} (f : A → B) (m : List A) : List B := m.map f

theorem mapWord_nil {A B : Type} (f : A → B) : mapWord f [] = [] := rfl

theorem mapWord_cons {A B : Type} (f : A → B) (a : A) (m : List A) :
    mapWord f (a :: m) = f a :: mapWord f m := rfl

theorem mapWord_append {A B : Type} (f : A → B) (m m' : List A) :
    mapWord f (m ++ m') = mapWord f m ++ mapWord f m' := by
  simp [mapWord]

theorem mapWord_split {A B : Type} (f : A → B) : ∀ (l₁ : List B) {l₂ : List B}
    {m : List A}, mapWord f m = l₁ ++ l₂ →
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ mapWord f m₁ = l₁ ∧ mapWord f m₂ = l₂
  | [], _, m, h => ⟨[], m, rfl, rfl, h⟩
  | _ :: _, _, [], h => by simp [mapWord] at h
  | _ :: l₁, _, a :: _, h => by
      rw [mapWord_cons] at h
      injection h with h1 h2
      match mapWord_split f l₁ h2 with
      | ⟨m₁, m₂, hm, hmap₁, hmap₂⟩ =>
        refine ⟨a :: m₁, m₂, by rw [hm]; rfl, ?_, hmap₂⟩
        rw [mapWord_cons, h1, hmap₁]

end SGraph

open SGraph in

def zcoverCovering : Covering zcover bouquet where
  toV _ := ()
  toE e := e.2
  init_toE _ := rfl
  bar_toE _ := rfl
  star_surj := sorry
  star_inj := sorry

namespace SGraph.Covering

variable {Y X : SGraph} (p : Covering Y X)

theorem exists_lift_word :
    ∀ (l : List X.E) (y : Y.V) {w : X.V}, Wf X (p.toV y) l w →
      ∃ w' : Y.V, ∃ m : List Y.E, Wf Y y m w' ∧ mapWord p.toE m = l ∧ p.toV w' = w :=
  sorry

theorem lift_word_unique :
    ∀ {m m' : List Y.E} {y w₁ w₂ : Y.V},
      Wf Y y m w₁ → Wf Y y m' w₂ → mapWord p.toE m = mapWord p.toE m' → m = m' :=
  sorry

theorem endpoint_of_reduces :
    ∀ {l l' : List X.E}, Reduces X l l' →
      ∀ {y b : Y.V} {m : List Y.E}, Wf Y y m b → mapWord p.toE m = l →
        ∃ m' : List Y.E, Wf Y y m' b ∧ mapWord p.toE m' = l' :=
  sorry

theorem endpoint_eq {l l' : List X.E}
    (hh : Homotopic X l l') {y b b' : Y.V} {m m' : List Y.E}
    (hm : Wf Y y m b) (hmapm : mapWord p.toE m = l)
    (hm' : Wf Y y m' b') (hmapm' : mapWord p.toE m' = l') : b = b' :=
  sorry

-- ## Part E: モノドロミー

abbrev Fiber (v : X.V) : Type := {y : Y.V // p.toV y = v}

theorem fiberExt {v : X.V} {a b : p.Fiber v} (h : a.1 = b.1) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem fiber_wf {v w : X.V} (a : p.Fiber v) {l : List X.E}
    (hl : Wf X v l w) : Wf X (p.toV a.1) l w := by
  rw [a.2]; exact hl

noncomputable def liftEnd {v w : X.V} (a : p.Fiber v) (l : List X.E)
    (hl : Wf X v l w) : p.Fiber w :=
  ⟨Classical.choose (p.exists_lift_word l a.1 (p.fiber_wf a hl)),
   (Classical.choose_spec (Classical.choose_spec
     (p.exists_lift_word l a.1 (p.fiber_wf a hl)))).2.2⟩

theorem liftEnd_spec {v w : X.V} (a : p.Fiber v) {l : List X.E} (hl : Wf X v l w) :
    ∃ m, Wf Y a.1 m (p.liftEnd a l hl).1 ∧ mapWord p.toE m = l :=
  ⟨Classical.choose (Classical.choose_spec (p.exists_lift_word l a.1 (p.fiber_wf a hl))),
   (Classical.choose_spec (Classical.choose_spec
     (p.exists_lift_word l a.1 (p.fiber_wf a hl)))).1,
   (Classical.choose_spec (Classical.choose_spec
     (p.exists_lift_word l a.1 (p.fiber_wf a hl)))).2.1⟩

theorem liftEnd_eq {v w : X.V} (a : p.Fiber v) {l : List X.E} (hl : Wf X v l w)
    {b : Y.V} {m : List Y.E} (hm : Wf Y a.1 m b) (hmap : mapWord p.toE m = l) :
    (p.liftEnd a l hl).1 = b := by
  match p.liftEnd_spec a hl with
  | ⟨M, hM, hMmap⟩ =>
    have heq : M = m := p.lift_word_unique hM hm (by rw [hMmap, hmap])
    subst heq
    exact Wf.end_unique hM hm

noncomputable def transport {v w : X.V} (γ : PathClass X v w) (a : p.Fiber v) :
    p.Fiber w :=
  Quot.lift (fun l => p.liftEnd a l.1 l.2)
    (fun l l' hll' => by
      apply p.fiberExt
      match p.liftEnd_spec a l.2, p.liftEnd_spec a l'.2 with
      | ⟨_, hM, hMmap⟩, ⟨_, hM', hM'map⟩ =>
        exact p.endpoint_eq hll' hM hMmap hM' hM'map)
    γ

theorem transport_refl {v : X.V} (a : p.Fiber v) :
    p.transport (PathClass.refl v) a = a :=
  sorry

theorem transport_trans {v u w : X.V}
    (γ : PathClass X v u) (δ : PathClass X u w) (a : p.Fiber v) :
    p.transport (γ.comp δ) a = p.transport δ (p.transport γ a) :=
  sorry

theorem transport_bijective {v w : X.V} (γ : PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  sorry

end SGraph.Covering

open SGraph

def loopWf : Wf bouquet () [true] () :=
  Wf.cons (G := bouquet) true (Wf.nil (bouquet.term true))

example (i : Int) :
    (zcoverCovering.transport (PathClass.mk loopWf) ⟨i, rfl⟩).1 = i + 1 :=
  zcoverCovering.liftEnd_eq ⟨i, rfl⟩ loopWf
    (Wf.cons (G := zcover) ((i, true) : Int × Bool) (Wf.nil (zcover.term (i, true)))) rfl

-- ## Part F: π₁(花束) ≃ ℤ

theorem mapWord_reduces {Y X : SGraph} (p : GraphHom Y X) {m m' : List Y.E}
    (h : Reduces Y m m') : Reduces X (mapWord p.toE m) (mapWord p.toE m') := by
  induction h with
  | cancel m₁ m₂ e =>
      rw [mapWord_append, mapWord_cons, mapWord_cons, ← p.bar_toE, mapWord_append]
      exact .cancel _ _ _
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem zc_drift : ∀ {m : List zcover.E} {e : zcover.E} {v w : Int},
    Wf zcover v (e :: m) w → IsReduced (e :: m) →
    (e.2 = true ∧ v < w) ∨ (e.2 = false ∧ w < v) :=
  sorry

theorem zc_reduced_closed : ∀ {m : List zcover.E} {v : Int},
    Wf zcover v m v → IsReduced m → m = [] :=
  sorry

def shiftWord (k : Int) (m : List zcover.E) : List zcover.E :=
  m.map (fun e => (e.1 + k, e.2))

theorem mapWord_shift (k : Int) : ∀ (m : List zcover.E),
    mapWord zcoverCovering.toE (shiftWord k m) = mapWord zcoverCovering.toE m
  | [] => rfl
  | e :: m => congrArg (fun t => e.2 :: t) (mapWord_shift k m)

theorem shift_wf (k : Int) : ∀ (m : List zcover.E) {v w : Int},
    Wf zcover v m w → Wf zcover (v + k) (shiftWord k m) (w + k) :=
  sorry

abbrev triv : PathClass bouquet () () := PathClass.refl (G := bouquet) ()

def basePt : zcoverCovering.Fiber () := ⟨(0 : Int), rfl⟩

noncomputable def deg (γ : PathClass bouquet () ()) : Int :=
  (zcoverCovering.transport γ basePt).1

theorem transport_apply (γ : PathClass bouquet () ()) (i : Int) :
    (zcoverCovering.transport γ ⟨i, rfl⟩).1 = deg γ + i :=
  sorry

theorem deg_comp (γ δ : PathClass bouquet () ()) :
    deg (γ.comp δ) = deg γ + deg δ :=
  sorry

theorem deg_refl : deg triv = 0 :=
  congrArg Subtype.val (zcoverCovering.transport_refl basePt)

theorem deg_inv (γ : PathClass bouquet () ()) : deg γ.inv = - deg γ :=
  sorry

def loop : PathClass bouquet () () := PathClass.mk loopWf

theorem deg_loop : deg loop = 1 := by
  have h : deg loop = (0 : Int) + 1 :=
    zcoverCovering.liftEnd_eq basePt loopWf
      (Wf.cons (G := zcover) ((0, true) : Int × Bool) (Wf.nil (zcover.term (0, true)))) rfl
  omega

def loopPow : Nat → PathClass bouquet () ()
  | 0 => triv
  | k + 1 => (loopPow k).comp loop

theorem deg_eq_zero {γ : PathClass bouquet () ()} (h : deg γ = 0) :
    γ = triv :=
  sorry

theorem deg_injective : Function.Injective deg :=
  sorry

theorem deg_loopPow : ∀ k : Nat, deg (loopPow k) = Int.ofNat k
  | 0 => deg_refl
  | k + 1 => by
      have h := deg_comp (loopPow k) loop
      rw [deg_loopPow k, deg_loop] at h
      exact h

theorem deg_surjective : Function.Surjective deg :=
  sorry

theorem pi1_bouquet :
    (∀ γ δ : PathClass bouquet () (), deg (γ.comp δ) = deg γ + deg δ) ∧
      Function.Bijective deg :=
  sorry

#print axioms pi1_bouquet
