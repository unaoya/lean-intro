import CoverProbeA
import CoverProbeB

/-!
# 試作C: グラフの被覆と一意持ち上げ — A と B の接続

内容:
1. π₁ 亜群の構成(試作Aの正規形定理を使い、道のホモトピー類を `Quot` で作る)
   → 試作Bの `PathSystem` の実例になる
2. グラフの被覆(star の全単射)と**持ち上げ定理**(リストの帰納法一発)
3. ホモトピックな道の持ち上げは同じ点に着く(離散版ホモトピー持ち上げ。
   任意の挿入は `Wf` を壊すので、`Reduces`(削除のみ)と正規形定理に帰着させる)
4. 以上から `LiftSystem` の実例を作る → 試作Bのモノドロミー・ファイバー全単射が
   グラフの被覆に対して一斉に成立する
5. 例: 花束グラフの ℤ 被覆と、ループのモノドロミーが +1 で作用すること
-/

namespace CoverProbe

namespace SGraph

variable {G : SGraph}

/-! ## 道の基本補題の追加 -/

/-- 空の語の道は動かない。 -/
theorem Wf.nil_inv {v w : G.V} (h : Wf G v [] w) : v = w := by
  cases h with
  | nil => rfl

/-- 道の終点は始点と語で決まる。 -/
theorem Wf.end_unique : ∀ {y w₁ w₂ : G.V} {m : List G.E},
    Wf G y m w₁ → Wf G y m w₂ → w₁ = w₂
  | _, _, _, _, .nil _, h₂ => by cases h₂ with | nil => rfl
  | _, _, _, _, .cons e h₁, h₂ => Wf.end_unique h₁ (Wf.cons_inv h₂).2

/-- 連接の分解。 -/
theorem Wf.append_split : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E},
    Wf G v (l₁ ++ l₂) w → ∃ u, Wf G v l₁ u ∧ Wf G u l₂ w
  | _, _, [], _, h => ⟨_, .nil _, h⟩
  | v, w, e :: l₁, l₂, h => by
      have hi := Wf.cons_inv h
      match Wf.append_split l₁ hi.2 with
      | ⟨u, h₁, h₂⟩ =>
        refine ⟨u, ?_, h₂⟩
        have hc := Wf.cons e h₁
        rw [← hi.1] at hc
        exact hc

/-! ## ホモトピーの合同性と語の反転 -/

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

/-- 語の反転: 各辺を反転して並べ替える。道の逆向きに対応する。 -/
def revWord (G : SGraph) (l : List G.E) : List G.E := (l.map G.bar).reverse

theorem revWord_cons (e : G.E) (l : List G.E) :
    revWord G (e :: l) = revWord G l ++ [G.bar e] := by
  simp [revWord]

theorem revWord_append (l l' : List G.E) :
    revWord G (l ++ l') = revWord G l' ++ revWord G l := by
  simp [revWord]

theorem Wf.revWord : ∀ {v w : G.V} {l : List G.E},
    Wf G v l w → Wf G w (SGraph.revWord G l) v
  | _, _, _, .nil v => .nil v
  | _, _, _, .cons e h => by
      rw [revWord_cons]
      have s : Wf G (G.term e) [G.bar e] (G.term (G.bar e)) := Wf.cons (G.bar e) (.nil _)
      rw [term_bar] at s
      exact (Wf.revWord h).append s

theorem Homotopic.revWordCong {l l' : List G.E} (h : Homotopic G l l') :
    Homotopic G (revWord G l) (revWord G l') := by
  induction h with
  | cancel l₁ l₂ e =>
      have lhs : revWord G (l₁ ++ e :: G.bar e :: l₂) =
          revWord G l₂ ++ e :: G.bar e :: revWord G l₁ := by
        simp [revWord_append, revWord_cons, G.bar_bar, List.append_assoc]
      rw [lhs, revWord_append]
      exact .cancel (revWord G l₂) (revWord G l₁) e
  | refl l => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- 逆向きに歩いてから歩き直すと、ホモトピーで消える。 -/
theorem homotopic_revWord_append : ∀ l : List G.E, Homotopic G (revWord G l ++ l) []
  | [] => .refl _
  | e :: l => by
      rw [revWord_cons, List.append_assoc]
      have step : Homotopic G (revWord G l ++ (G.bar e :: e :: l)) (revWord G l ++ l) := by
        have h := Homotopic.cancel (G := G) (revWord G l) l (G.bar e)
        rw [G.bar_bar] at h
        exact h
      exact .trans step (homotopic_revWord_append l)

theorem homotopic_append_revWord : ∀ l : List G.E, Homotopic G (l ++ revWord G l) []
  | [] => .refl _
  | e :: l => by
      rw [revWord_cons, ← List.append_assoc]
      have h1 : Homotopic G ((l ++ revWord G l) ++ [G.bar e]) ([] ++ [G.bar e]) :=
        Homotopic.appendRight _ (homotopic_append_revWord l)
      have h2 := Homotopic.appendLeft [e] h1
      exact .trans h2 (Homotopic.cancel [] [] e)

/-! ## π₁ 亜群: 道のホモトピー類 -/

/-- `v` から `w` への道のホモトピー類。 -/
def PathClass (X : SGraph) (v w : X.V) : Type :=
  Quot (fun a b : {l : List X.E // Wf X v l w} => Homotopic X a.1 b.1)

def PathClass.mk {X : SGraph} {v w : X.V} {l : List X.E} (hl : Wf X v l w) :
    PathClass X v w :=
  Quot.mk _ ⟨l, hl⟩

theorem PathClass.mk_eq_of_eq {X : SGraph} {v w : X.V} {l l' : List X.E}
    (h : l = l') (hl : Wf X v l w) (hl' : Wf X v l' w) :
    PathClass.mk hl = PathClass.mk hl' := by
  subst h; rfl

/-- ホモトピーの `Quot.sound`(代表の水準)。 -/
theorem PathClass.sound {X : SGraph} {v w : X.V} {l l' : List X.E}
    (hl : Wf X v l w) (hl' : Wf X v l' w) (h : Homotopic X l l') :
    PathClass.mk hl = PathClass.mk hl' :=
  Quot.sound h

/-- 連接。 -/
def PathClass.comp {X : SGraph} {v u w : X.V}
    (φ : PathClass X v u) (ψ : PathClass X u w) : PathClass X v w :=
  Quot.lift
    (fun a => Quot.lift (fun b => PathClass.mk (Wf.append a.2 b.2))
      (fun _ _ hb => Quot.sound (Homotopic.appendLeft a.1 hb)) ψ)
    (fun _ _ ha => by
      induction ψ using Quot.ind with
      | mk b =>
        apply Quot.sound
        exact Homotopic.appendRight b.1 ha)
    φ

/-- 逆道。 -/
def PathClass.inv {X : SGraph} {v w : X.V} (φ : PathClass X v w) : PathClass X w v :=
  Quot.lift (fun a => PathClass.mk a.2.revWord)
    (fun _ _ h => Quot.sound (Homotopic.revWordCong h)) φ

/-- グラフの π₁ 亜群は `PathSystem` の実例(離散版)。 -/
def pathSystem (X : SGraph) : PathSystem X.V where
  Hom := PathClass X
  refl v := PathClass.mk (.nil v)
  trans φ ψ := φ.comp ψ
  symm φ := φ.inv
  refl_trans := by
    intro x y γ
    induction γ using Quot.ind with
    | mk a => exact PathClass.mk_eq_of_eq (List.nil_append a.1) (Wf.append (.nil x) a.2) a.2
  trans_refl := by
    intro x y γ
    induction γ using Quot.ind with
    | mk a => exact PathClass.mk_eq_of_eq (List.append_nil a.1) (Wf.append a.2 (.nil y)) a.2
  trans_assoc := by
    intro x y z w γ δ ε
    induction γ using Quot.ind with
    | mk a =>
      induction δ using Quot.ind with
      | mk b =>
        induction ε using Quot.ind with
        | mk c =>
          exact PathClass.mk_eq_of_eq (List.append_assoc a.1 b.1 c.1)
            (Wf.append (Wf.append a.2 b.2) c.2) (Wf.append a.2 (Wf.append b.2 c.2))
  symm_trans := by
    intro x y γ
    induction γ using Quot.ind with
    | mk a =>
      exact PathClass.sound (Wf.append a.2.revWord a.2) (.nil y)
        (homotopic_revWord_append a.1)
  trans_symm := by
    intro x y γ
    induction γ using Quot.ind with
    | mk a =>
      exact PathClass.sound (Wf.append a.2 a.2.revWord) (.nil x)
        (homotopic_append_revWord a.1)

end SGraph

open SGraph

/-! ## グラフの射と被覆 -/

/-- グラフの射: 頂点と辺を写し、始点と反転を保つ。 -/
structure GraphHom (Y X : SGraph) where
  toV : Y.V → X.V
  toE : Y.E → X.E
  init_toE : ∀ e, X.init (toE e) = toV (Y.init e)
  bar_toE : ∀ e, X.bar (toE e) = toE (Y.bar e)

variable {Y X : SGraph}

theorem GraphHom.term_toE (p : GraphHom Y X) (e : Y.E) :
    X.term (p.toE e) = p.toV (Y.term e) := by
  simp only [SGraph.term]
  rw [p.bar_toE, p.init_toE]

/-- 語を射で写す。 -/
def mapWord (p : GraphHom Y X) (m : List Y.E) : List X.E := m.map p.toE

theorem mapWord_nil (p : GraphHom Y X) : mapWord p [] = [] := rfl

theorem mapWord_cons (p : GraphHom Y X) (e : Y.E) (m : List Y.E) :
    mapWord p (e :: m) = p.toE e :: mapWord p m := rfl

theorem mapWord_append (p : GraphHom Y X) (m m' : List Y.E) :
    mapWord p (m ++ m') = mapWord p m ++ mapWord p m' := by
  simp [mapWord]

theorem mapWord_split (p : GraphHom Y X) : ∀ (l₁ : List X.E) {l₂ : List X.E}
    {m : List Y.E}, mapWord p m = l₁ ++ l₂ →
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ mapWord p m₁ = l₁ ∧ mapWord p m₂ = l₂
  | [], l₂, m, h => ⟨[], m, rfl, rfl, h⟩
  | _ :: _, _, [], h => by simp [mapWord] at h
  | f :: l₁, l₂, e :: m, h => by
      rw [mapWord_cons] at h
      injection h with h1 h2
      match mapWord_split p l₁ h2 with
      | ⟨m₁, m₂, hm, hmap₁, hmap₂⟩ =>
        refine ⟨e :: m₁, m₂, by rw [hm]; rfl, ?_, hmap₂⟩
        show p.toE e :: mapWord p m₁ = f :: l₁
        rw [h1, hmap₁]

/-- **被覆**: 各頂点の star(そこから出る辺)の上で全単射。
    位相空間の被覆の「局所自明性」の離散版がこの2条件に縮む。 -/
structure IsCovering (p : GraphHom Y X) : Prop where
  star_surj : ∀ (y : Y.V) (f : X.E), X.init f = p.toV y →
    ∃ e : Y.E, Y.init e = y ∧ p.toE e = f
  star_inj : ∀ e e' : Y.E, Y.init e = Y.init e' → p.toE e = p.toE e' → e = e'

namespace IsCovering

variable {p : GraphHom Y X}

/-! ## 持ち上げ定理 — 位相の議論(区間のコンパクト性)がリストの帰納法に置き換わる -/

/-- **道の持ち上げの存在**: 始点の持ち上げを決めれば、道は持ち上がる。
    証明は語の長さに関する帰納法一発。 -/
theorem exists_lift_word (hp : IsCovering p) :
    ∀ (l : List X.E) (y : Y.V) {w : X.V}, Wf X (p.toV y) l w →
      ∃ w' : Y.V, ∃ m : List Y.E, Wf Y y m w' ∧ mapWord p m = l ∧ p.toV w' = w
  | [], y, w, h => ⟨y, [], .nil y, rfl, Wf.nil_inv h⟩
  | f :: l, y, w, h => by
      have hi := Wf.cons_inv h
      match hp.star_surj y f hi.1.symm with
      | ⟨e, he_init, he_map⟩ =>
        have hterm : p.toV (Y.term e) = X.term f := by
          rw [← p.term_toE, he_map]
        have h2 : Wf X (p.toV (Y.term e)) l w := by rw [hterm]; exact hi.2
        match exists_lift_word hp l (Y.term e) h2 with
        | ⟨w', m, hm, hmap, hw⟩ =>
          refine ⟨w', e :: m, ?_, ?_, hw⟩
          · have hc := Wf.cons e hm
            rw [he_init] at hc
            exact hc
          · show p.toE e :: mapWord p m = f :: l
            rw [he_map, hmap]

/-- **持ち上げの一意性**: 同じ点から始まり同じ語に写る持ち上げは一致する。 -/
theorem lift_word_unique (hp : IsCovering p) :
    ∀ {m m' : List Y.E} {y w₁ w₂ : Y.V},
      Wf Y y m w₁ → Wf Y y m' w₂ → mapWord p m = mapWord p m' → m = m'
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, hmap => by simp [mapWord] at hmap
  | _ :: _, [], _, _, _, _, _, hmap => by simp [mapWord] at hmap
  | e :: m, e' :: m', y, w₁, w₂, h₁, h₂, hmap => by
      have hi₁ := Wf.cons_inv h₁
      have hi₂ := Wf.cons_inv h₂
      rw [mapWord_cons, mapWord_cons] at hmap
      injection hmap with hh ht
      have he : e = e' := hp.star_inj e e' (hi₁.1.symm.trans hi₂.1) hh
      subst he
      rw [lift_word_unique hp hi₁.2 hi₂.2 ht]

/-- backtrack の削除は、持ち上げの**終点を変えずに**持ち上げの語を縮める。
    位相空間版の「ホモトピー持ち上げ」に対応する核。 -/
theorem endpoint_of_reduces (hp : IsCovering p) :
    ∀ {l l' : List X.E}, Reduces X l l' →
      ∀ {y b : Y.V} {m : List Y.E}, Wf Y y m b → mapWord p m = l →
        ∃ m' : List Y.E, Wf Y y m' b ∧ mapWord p m' = l'
  | _, _, .refl _, _, _, m, hm, hmap => ⟨m, hm, hmap⟩
  | _, _, .trans h₁ h₂, _, _, m, hm, hmap => by
      match endpoint_of_reduces hp h₁ hm hmap with
      | ⟨m₁, hm₁, hmap₁⟩ => exact endpoint_of_reduces hp h₂ hm₁ hmap₁
  | _, _, .cancel l₁ l₂ f, y, b, m, hm, hmap => by
      match mapWord_split p l₁ hmap with
      | ⟨m₁, m₂, hmeq, hmap₁, hmap₂⟩ =>
        subst hmeq
        match m₂, hm, hmap₂ with
        | [], _, hmap₂ => simp [mapWord] at hmap₂
        | [_], _, hmap₂ => simp [mapWord] at hmap₂
        | ê :: g :: m₃, hm, hmap₂ =>
            rw [mapWord_cons, mapWord_cons] at hmap₂
            injection hmap₂ with h1 h2'
            injection h2' with h2 h3
            match Wf.append_split m₁ hm with
            | ⟨u, hu₁, hu₂⟩ =>
              have hi₁ := Wf.cons_inv hu₂
              have hi₂ := Wf.cons_inv hi₁.2
              have hg : g = Y.bar ê := by
                refine hp.star_inj g (Y.bar ê) ?_ ?_
                · exact hi₂.1.symm
                · rw [h2, ← p.bar_toE, h1]
              subst hg
              have hdel : Wf Y u m₃ b := Wf.of_append_cancel [] hu₂
              exact ⟨m₁ ++ m₃, Wf.append hu₁ hdel,
                by rw [mapWord_append, hmap₁, h3]⟩

/-- **ホモトピックな道の持ち上げは同じ点に着く**。証明は正規形定理に帰着:
    どちらの持ち上げも正規形への削除列を持ち、正規形の持ち上げは一意。 -/
theorem endpoint_eq (hp : IsCovering p) {l l' : List X.E}
    (hh : Homotopic X l l') {y b b' : Y.V} {m m' : List Y.E}
    (hm : Wf Y y m b) (hmapm : mapWord p m = l)
    (hm' : Wf Y y m' b') (hmapm' : mapWord p m' = l') : b = b' := by
  letI : DecidableEq X.E := fun a b => Classical.propDecidable _
  have hred : SGraph.reduce l = SGraph.reduce l' := homotopic_iff_reduce_eq.mp hh
  match hp.endpoint_of_reduces (reduces_reduce l) hm hmapm,
        hp.endpoint_of_reduces (reduces_reduce l') hm' hmapm' with
  | ⟨mr, hmr, hmapr⟩, ⟨mr', hmr', hmapr'⟩ =>
    have heq : mr = mr' := hp.lift_word_unique hmr hmr' (by rw [hmapr, hmapr', hred])
    subst heq
    exact Wf.end_unique hmr hmr'

/-! ## ファイバーと輸送 — `LiftSystem` の実例へ -/

theorem fiberExt {v : X.V} {a b : {y : Y.V // p.toV y = v}} (h : a.1 = b.1) : a = b := by
  cases a with
  | mk a1 ha =>
    cases b with
    | mk b1 hb =>
      cases h
      rfl

theorem fiber_wf {v w : X.V} (a : {y : Y.V // p.toV y = v}) {l : List X.E}
    (hl : Wf X v l w) : Wf X (p.toV a.1) l w := by
  rw [a.2]; exact hl

/-- 道の持ち上げの終点。存在は `exists_lift_word`、抽出は選択公理。 -/
noncomputable def liftEnd (hp : IsCovering p) {v w : X.V}
    (a : {y : Y.V // p.toV y = v}) (l : List X.E) (hl : Wf X v l w) :
    {y : Y.V // p.toV y = w} :=
  ⟨Classical.choose (hp.exists_lift_word l a.1 (fiber_wf a hl)),
   (Classical.choose_spec (Classical.choose_spec
     (hp.exists_lift_word l a.1 (fiber_wf a hl)))).2.2⟩

theorem liftEnd_spec (hp : IsCovering p) {v w : X.V}
    (a : {y : Y.V // p.toV y = v}) {l : List X.E} (hl : Wf X v l w) :
    ∃ m, Wf Y a.1 m (hp.liftEnd a l hl).1 ∧ mapWord p m = l :=
  ⟨Classical.choose (Classical.choose_spec (hp.exists_lift_word l a.1 (fiber_wf a hl))),
   (Classical.choose_spec (Classical.choose_spec
     (hp.exists_lift_word l a.1 (fiber_wf a hl)))).1,
   (Classical.choose_spec (Classical.choose_spec
     (hp.exists_lift_word l a.1 (fiber_wf a hl)))).2.1⟩

/-- `liftEnd` の特徴づけ: 持ち上げの語を1つ示せば終点が決まる。 -/
theorem liftEnd_eq (hp : IsCovering p) {v w : X.V}
    (a : {y : Y.V // p.toV y = v}) {l : List X.E} (hl : Wf X v l w)
    {b : Y.V} {m : List Y.E} (hm : Wf Y a.1 m b) (hmap : mapWord p m = l) :
    (hp.liftEnd a l hl).1 = b := by
  match hp.liftEnd_spec a hl with
  | ⟨M, hM, hMmap⟩ =>
    have heq : M = m := hp.lift_word_unique hM hm (by rw [hMmap, hmap])
    subst heq
    exact Wf.end_unique hM hm

/-- ホモトピー類に沿った輸送。`endpoint_eq` により代表の取り方によらない。 -/
noncomputable def transport (hp : IsCovering p) {v w : X.V}
    (γ : PathClass X v w) (a : {y : Y.V // p.toV y = v}) :
    {y : Y.V // p.toV y = w} :=
  Quot.lift (fun l => hp.liftEnd a l.1 l.2)
    (fun l l' hll' => by
      apply fiberExt
      match hp.liftEnd_spec a l.2, hp.liftEnd_spec a l'.2 with
      | ⟨M, hM, hMmap⟩, ⟨M', hM', hM'map⟩ =>
        exact hp.endpoint_eq hll' hM hMmap hM' hM'map)
    γ

theorem transport_refl (hp : IsCovering p) {v : X.V}
    (a : {y : Y.V // p.toV y = v}) :
    hp.transport (PathClass.mk (.nil v)) a = a := by
  apply fiberExt
  exact hp.liftEnd_eq a (.nil v) (.nil a.1) rfl

theorem transport_trans (hp : IsCovering p) {v u w : X.V}
    (γ : PathClass X v u) (δ : PathClass X u w) (a : {y : Y.V // p.toV y = v}) :
    hp.transport (γ.comp δ) a = hp.transport δ (hp.transport γ a) := by
  induction γ using Quot.ind with
  | mk lg =>
    induction δ using Quot.ind with
    | mk ld =>
      apply fiberExt
      match hp.liftEnd_spec a lg.2 with
      | ⟨m₁, hm₁, hmap₁⟩ =>
        match hp.liftEnd_spec (hp.liftEnd a lg.1 lg.2) ld.2 with
        | ⟨m₂, hm₂, hmap₂⟩ =>
          exact hp.liftEnd_eq a (Wf.append lg.2 ld.2) (Wf.append hm₁ hm₂)
            (by rw [mapWord_append, hmap₁, hmap₂])

/-- **主結果**: グラフの被覆は `LiftSystem` の実例。これで試作Bの
    モノドロミー・ファイバー全単射の全定理がグラフの被覆に対して成立する。 -/
noncomputable def toLiftSystem (hp : IsCovering p) :
    LiftSystem (pathSystem X) (fun v => {y : Y.V // p.toV y = v}) where
  transport := hp.transport
  transport_refl := fun _ a => hp.transport_refl a
  transport_trans := fun γ δ a => hp.transport_trans γ δ a

end IsCovering

/-! ## 例: 花束グラフの ℤ 被覆(普遍被覆の離散版)

ℝ → S¹ の離散類似。頂点 ℤ、各 `i` から `i+1` へ辺が1本。 -/

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

def zcoverHom : GraphHom zcover bouquet where
  toV _ := ()
  toE e := e.2
  init_toE _ := rfl
  bar_toE _ := rfl

theorem zcover_isCovering : IsCovering zcoverHom where
  star_surj := by
    intro y f _
    cases f with
    | true => exact ⟨(y, true), rfl, rfl⟩
    | false =>
        have key : ∀ j : Int, ∃ i : Int, i + 1 = j := fun j => ⟨j - 1, by omega⟩
        match key y with
        | ⟨i, hi⟩ => exact ⟨(i, false), hi, rfl⟩
  star_inj := by
    intro e e' hinit hmap
    cases e with
    | mk i b =>
      cases e' with
      | mk i' b' =>
        have hb : b = b' := hmap
        subst hb
        cases b with
        | true =>
            have h : i = i' := hinit
            rw [h]
        | false =>
            have h : i + 1 = i' + 1 := hinit
            have h' : i = i' := by omega
            rw [h']

/-- 花束のループ(円周を1周する道の離散版)。 -/
def loopWf : Wf bouquet () [true] () :=
  Wf.cons (G := bouquet) true (Wf.nil (bouquet.term true))

/-- **モノドロミーの計算**: ループの類はファイバー ℤ に +1 で作用する。
    π₁(花束) ≃ ℤ の「≃ の中身」がここに見えている。 -/
example (i : Int) :
    (zcover_isCovering.transport (PathClass.mk loopWf) ⟨i, rfl⟩).1 = i + 1 :=
  zcover_isCovering.liftEnd_eq ⟨i, rfl⟩ loopWf
    (Wf.cons (G := zcover) ((i, true) : Int × Bool) (Wf.nil (zcover.term (i, true)))) rfl

end CoverProbe
