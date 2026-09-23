import «06_Topology»

/-! # 発展演習: グラフの被覆（解答）

`09_Covering.lean` の全問題の解答。主張は問題ファイルと一字一句同じにしてある。
-/

/-! ## Part A: Serre グラフと道 -/

/-- Serre 流のグラフ。辺は向きつきで、反転 `bar` は不動点のない対合。
無向の辺 1 本を、互いに反転しあう向きつきの辺 2 本 `e`・`ē` で表す。 -/
structure SGraph where
  V : Type
  E : Type
  init : E → V
  bar : E → E
  bar_bar : ∀ e, bar (bar e) = e
  bar_ne : ∀ e, bar e ≠ e

namespace SGraph

variable {G : SGraph}

/-- 辺の終点 = 反転した辺の始点。 -/
def term (G : SGraph) (e : G.E) : G.V := G.init (G.bar e)

/-- 問題1: 反転した辺の終点は、元の辺の始点である。 -/
theorem term_bar (e : G.E) : G.term (G.bar e) = G.init e := by
  rw [term, G.bar_bar]

/-- 語（辺のリスト）が `v` から `w` への**道**であること: 隣接条件。 -/
inductive Wf (G : SGraph) : G.V → List G.E → G.V → Prop
  | nil (v : G.V) : Wf G v [] v
  | cons (e : G.E) {l : List G.E} {w : G.V} :
      Wf G (G.term e) l w → Wf G (G.init e) (e :: l) w

/-- 逆転補題: 空の語の道は動かない。 -/
theorem Wf.nil_inv {v w : G.V} (h : Wf G v [] w) : v = w := by
  cases h with
  | nil => rfl

/-- 逆転補題: `e :: l` が道なら、始点は `e` の始点で、残りも道。 -/
theorem Wf.cons_inv {v w : G.V} {e : G.E} {l : List G.E} (h : Wf G v (e :: l) w) :
    v = G.init e ∧ Wf G (G.term e) l w := by
  cases h with
  | cons _ h' => exact ⟨rfl, h'⟩

/-- 問題2: 道の連接は道。 -/
theorem Wf.append {v u w : G.V} : ∀ {l₁ l₂ : List G.E},
    Wf G v l₁ u → Wf G u l₂ w → Wf G v (l₁ ++ l₂) w
  | _, _, .nil _, h₂ => h₂
  | _, _, .cons e h₁, h₂ => .cons e (Wf.append h₁ h₂)

/-- 問題3: 道の終点は始点と語で決まる。 -/
theorem Wf.end_unique : ∀ {y w₁ w₂ : G.V} {m : List G.E},
    Wf G y m w₁ → Wf G y m w₂ → w₁ = w₂
  | _, _, _, _, .nil _, h₂ => Wf.nil_inv h₂
  | _, _, _, _, .cons _ h₁, h₂ => Wf.end_unique h₁ (Wf.cons_inv h₂).2

/-- 問題4: 連接の形の語が道なら、途中の点で2つの道に分かれる。 -/
theorem Wf.append_split : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E},
    Wf G v (l₁ ++ l₂) w → ∃ u, Wf G v l₁ u ∧ Wf G u l₂ w
  | _, _, [], _, h => ⟨_, .nil _, h⟩
  | _, _, e :: l₁, _, h => by
      have hi := Wf.cons_inv h
      match Wf.append_split l₁ hi.2 with
      | ⟨u, h₁, h₂⟩ =>
        refine ⟨u, ?_, h₂⟩
        rw [hi.1]
        exact Wf.cons e h₁

/-- 語の反転: 各辺を反転して逆順に並べる。道を逆向きにたどることに当たる。 -/
def revWord (G : SGraph) (l : List G.E) : List G.E := (l.map G.bar).reverse

theorem revWord_cons (e : G.E) (l : List G.E) :
    revWord G (e :: l) = revWord G l ++ [G.bar e] := by
  simp [revWord]

theorem revWord_append (l l' : List G.E) :
    revWord G (l ++ l') = revWord G l' ++ revWord G l := by
  simp [revWord]

/-- 問題5: 道を逆向きにたどった語も道。 -/
theorem Wf.revWord : ∀ {v w : G.V} {l : List G.E},
    Wf G v l w → Wf G w (SGraph.revWord G l) v
  | _, _, _, .nil v => .nil v
  | _, _, _, .cons e h => by
      rw [revWord_cons]
      have s : Wf G (G.term e) [G.bar e] (G.term (G.bar e)) := Wf.cons (G.bar e) (.nil _)
      rw [term_bar] at s
      exact (Wf.revWord h).append s

end SGraph

/-- 花束（頂点1つ・ループ1本）。円周の離散版。
向きつきの辺は `true`（正の向き）と `false`（逆向き）の2本。 -/
def bouquet : SGraph where
  V := Unit
  E := Bool
  init _ := ()
  bar := Bool.not
  bar_bar := by decide
  bar_ne := by decide

instance : DecidableEq bouquet.E := inferInstanceAs (DecidableEq Bool)

/-- 直線グラフ。実数直線の離散版。頂点は整数、辺 `(i, true)` は `i` から `i + 1` へ、
その反転 `(i, false)` は `i + 1` から `i` へ向かう。 -/
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

/-! ## Part B: ホモトピーと正規形定理 -/

namespace SGraph

variable {G : SGraph}

/-- 語が**既約**であること: backtrack（`e` の直後の `ē`）を含まない。 -/
def IsReduced : List G.E → Prop
  | [] => True
  | [_] => True
  | e :: f :: l => f ≠ G.bar e ∧ IsReduced (f :: l)

theorem IsReduced.tail : ∀ {l : List G.E} {e : G.E}, IsReduced (e :: l) → IsReduced l
  | [], _, _ => trivial
  | _ :: _, _, h => h.2

/-- 語のホモトピー: backtrack の削除（と、その逆の挿入）で生成される同値関係。 -/
inductive Homotopic (G : SGraph) : List G.E → List G.E → Prop
  | cancel (l₁ l₂ : List G.E) (e : G.E) :
      Homotopic G (l₁ ++ e :: G.bar e :: l₂) (l₁ ++ l₂)
  | refl (l : List G.E) : Homotopic G l l
  | symm {l l' : List G.E} : Homotopic G l l' → Homotopic G l' l
  | trans {l l' l'' : List G.E} :
      Homotopic G l l' → Homotopic G l' l'' → Homotopic G l l''

/-- 削除だけの一方向の関係。 -/
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

/-- 既約な語の先頭に辺を1本足す。先頭と打ち消し合うなら消す。 -/
def rcons (e : G.E) : List G.E → List G.E
  | [] => [e]
  | f :: r => if f = G.bar e then r else e :: f :: r

theorem rcons_nil (e : G.E) : rcons e ([] : List G.E) = [e] := rfl

theorem rcons_cons (e f : G.E) (r : List G.E) :
    rcons e (f :: r) = if f = G.bar e then r else e :: f :: r := rfl

/-- 語の簡約（正規形の計算）。 -/
def reduce : List G.E → List G.E
  | [] => []
  | e :: l => rcons e (reduce l)

theorem reduce_cons (e : G.E) (l : List G.E) : reduce (e :: l) = rcons e (reduce l) := rfl

/-- 問題6: 既約な語に `rcons` しても既約。 -/
theorem isReduced_rcons {e : G.E} : ∀ {m : List G.E}, IsReduced m → IsReduced (rcons e m)
  | [], _ => trivial
  | f :: r, hm => by
      rw [rcons_cons]
      by_cases h : f = G.bar e
      · rw [if_pos h]; exact hm.tail
      · rw [if_neg h]; exact ⟨h, hm⟩

/-- 問題7: 簡約の結果は既約。 -/
theorem reduce_isReduced : ∀ l : List G.E, IsReduced (reduce l)
  | [] => trivial
  | _ :: l => isReduced_rcons (reduce_isReduced l)

/-- 問題8: 既約な語に `ē` と `e` を順に足すと元に戻る。 -/
theorem rcons_rcons_bar (e : G.E) : ∀ (m : List G.E), IsReduced m →
    rcons e (rcons (G.bar e) m) = m
  | [], _ => by rw [rcons_nil, rcons_cons, if_pos rfl]
  | f :: r, hm => by
      rw [rcons_cons]
      by_cases h : f = G.bar (G.bar e)
      · rw [if_pos h]
        rw [G.bar_bar] at h
        subst h
        match r, hm with
        | [], _ => rw [rcons_nil]
        | g :: r', hm => rw [rcons_cons, if_neg hm.1]
      · rw [if_neg h, rcons_cons, if_pos rfl]

/-- 問題9: `reduce` は backtrack の削除で変わらない。 -/
theorem reduce_append_cancel (e : G.E) : ∀ (l₁ l₂ : List G.E),
    reduce (l₁ ++ e :: G.bar e :: l₂) = reduce (l₁ ++ l₂)
  | [], l₂ => by
      rw [List.nil_append, List.nil_append, reduce_cons, reduce_cons]
      exact rcons_rcons_bar e (reduce l₂) (reduce_isReduced l₂)
  | x :: l₁, l₂ => by
      rw [List.cons_append, List.cons_append, reduce_cons, reduce_cons,
        reduce_append_cancel e l₁ l₂]

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

/-- 問題10: どの語も自分の正規形へ**削除だけで**到達する。 -/
theorem reduces_reduce : ∀ l : List G.E, Reduces G l (reduce l)
  | [] => .refl _
  | e :: l => by
      rw [reduce_cons]
      exact .trans (Reduces.cons e (reduces_reduce l)) (reduces_cons_rcons e (reduce l))

/-- 問題11（正規形定理）: ホモトピックであることと、正規形が一致することは同値。 -/
theorem homotopic_iff_reduce_eq {l l' : List G.E} :
    Homotopic G l l' ↔ reduce l = reduce l' := by
  constructor
  · intro h
    induction h with
    | cancel l₁ l₂ e => exact reduce_append_cancel e l₁ l₂
    | refl l => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    have h₁ := (reduces_reduce l).toHomotopic
    have h₂ := (reduces_reduce l').toHomotopic
    rw [h] at h₁
    exact h₁.trans h₂.symm

theorem reduce_eq_self_of_isReduced : ∀ {l : List G.E}, IsReduced l → reduce l = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by
      rw [reduce_cons, reduce_eq_self_of_isReduced h.2, rcons_cons, if_neg h.1]

/-- 問題12: ホモトピックな既約語は等しい（既約代表の一意性）。 -/
theorem eq_of_homotopic_of_isReduced {l l' : List G.E}
    (hl : IsReduced l) (hl' : IsReduced l') (h : Homotopic G l l') : l = l' := by
  rw [← reduce_eq_self_of_isReduced hl, ← reduce_eq_self_of_isReduced hl']
  exact homotopic_iff_reduce_eq.mp h

end Reduce

/-- 問題13: backtrack の**削除**は、道であることを保つ。 -/
theorem Wf.of_append_cancel : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E} {e : G.E},
    Wf G v (l₁ ++ e :: G.bar e :: l₂) w → Wf G v (l₁ ++ l₂) w
  | _, _, [], _, _, h => by
      have h₁ := Wf.cons_inv h
      have h₂ := Wf.cons_inv h₁.2
      have h₃ := h₂.2
      rw [term_bar] at h₃
      rw [h₁.1]
      exact h₃
  | _, _, _ :: l₁, _, _, h => by
      have hi := Wf.cons_inv h
      rw [hi.1]
      exact .cons _ (Wf.of_append_cancel l₁ hi.2)

theorem Wf.of_reduces {v w : G.V} {l l' : List G.E} (h : Reduces G l l') :
    Wf G v l w → Wf G v l' w := by
  induction h with
  | cancel l₁ l₂ e => exact fun hw => Wf.of_append_cancel l₁ hw
  | refl l => exact id
  | trans _ _ ih₁ ih₂ => exact fun hw => ih₂ (ih₁ hw)

/-- 問題14: 道の正規形は、同じ始点・終点の道。 -/
theorem Wf.reduce [DecidableEq G.E] {v w : G.V} {l : List G.E} (hw : Wf G v l w) :
    Wf G v (SGraph.reduce l) w :=
  Wf.of_reduces (reduces_reduce l) hw

end SGraph

/-- 花束では、正規形が計算で求まる。 -/
example : SGraph.reduce (G := bouquet) [true, false, true] = [true] := rfl
example : SGraph.reduce (G := bouquet) [true, true, false, false] = [] := rfl

/-! ## Part C: π₁ 亜群 -/

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

/-- 問題15: ホモトピックな語を反転しても、ホモトピック。 -/
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

/-- 問題16: 逆向きにたどってから元の向きにたどると、ホモトピーで消える。 -/
theorem homotopic_revWord_append : ∀ l : List G.E, Homotopic G (revWord G l ++ l) []
  | [] => .refl _
  | e :: l => by
      rw [revWord_cons, List.append_assoc]
      have step : Homotopic G (revWord G l ++ (G.bar e :: e :: l)) (revWord G l ++ l) := by
        have h := Homotopic.cancel (G := G) (revWord G l) l (G.bar e)
        rw [G.bar_bar] at h
        exact h
      exact .trans step (homotopic_revWord_append l)

/-- 問題17: 元の向きにたどってから逆向きにたどっても、ホモトピーで消える。 -/
theorem homotopic_append_revWord : ∀ l : List G.E, Homotopic G (l ++ revWord G l) []
  | [] => .refl _
  | e :: l => by
      rw [revWord_cons, ← List.append_assoc]
      have h1 : Homotopic G ((l ++ revWord G l) ++ [G.bar e]) ([] ++ [G.bar e]) :=
        Homotopic.appendRight _ (homotopic_append_revWord l)
      have h2 := Homotopic.appendLeft [e] h1
      exact .trans h2 (Homotopic.cancel [] [] e)

/-- `v` から `w` への道のホモトピー類。 -/
def PathClass (G : SGraph) (v w : G.V) : Type :=
  Quot (fun a b : {l : List G.E // Wf G v l w} => Homotopic G a.1 b.1)

namespace PathClass

def mk {v w : G.V} {l : List G.E} (hl : Wf G v l w) : PathClass G v w :=
  Quot.mk _ ⟨l, hl⟩

/-- 同じ語の類は等しい。 -/
theorem mk_eq_of_eq {v w : G.V} {l l' : List G.E}
    (h : l = l') (hl : Wf G v l w) (hl' : Wf G v l' w) : mk hl = mk hl' := by
  subst h; rfl

/-- ホモトピックな語の類は等しい。 -/
theorem sound {v w : G.V} {l l' : List G.E}
    (hl : Wf G v l w) (hl' : Wf G v l' w) (h : Homotopic G l l') : mk hl = mk hl' :=
  Quot.sound h

/-- 定数道の類。 -/
def refl (v : G.V) : PathClass G v v := mk (Wf.nil v)

/-- 連接。 -/
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

/-- 逆道。 -/
def inv {v w : G.V} (φ : PathClass G v w) : PathClass G w v :=
  Quot.lift (fun a => mk a.2.revWord)
    (fun _ _ h => Quot.sound (Homotopic.revWordCong h)) φ

variable {v w : G.V}

/-- 問題18a: 左単位律。 -/
theorem refl_comp (γ : PathClass G v w) : (refl v).comp γ = γ := by
  induction γ using Quot.ind with
  | mk a => exact mk_eq_of_eq (List.nil_append a.1) (Wf.append (.nil v) a.2) a.2

/-- 問題18b: 右単位律。 -/
theorem comp_refl (γ : PathClass G v w) : γ.comp (refl w) = γ := by
  induction γ using Quot.ind with
  | mk a => exact mk_eq_of_eq (List.append_nil a.1) (Wf.append a.2 (.nil w)) a.2

/-- 問題18c: 結合律。 -/
theorem comp_assoc {u z : G.V} (γ : PathClass G v u) (δ : PathClass G u w)
    (ε : PathClass G w z) : (γ.comp δ).comp ε = γ.comp (δ.comp ε) := by
  induction γ using Quot.ind with
  | mk a =>
    induction δ using Quot.ind with
    | mk b =>
      induction ε using Quot.ind with
      | mk c =>
        exact mk_eq_of_eq (List.append_assoc a.1 b.1 c.1)
          (Wf.append (Wf.append a.2 b.2) c.2) (Wf.append a.2 (Wf.append b.2 c.2))

/-- 問題18d: 逆道を先にたどると定数道。 -/
theorem inv_comp (γ : PathClass G v w) : γ.inv.comp γ = refl w := by
  induction γ using Quot.ind with
  | mk a =>
    exact sound (Wf.append a.2.revWord a.2) (.nil w) (homotopic_revWord_append a.1)

/-- 問題18e: 逆道をあとでたどっても定数道。 -/
theorem comp_inv (γ : PathClass G v w) : γ.comp γ.inv = refl v := by
  induction γ using Quot.ind with
  | mk a =>
    exact sound (Wf.append a.2 a.2.revWord) (.nil v) (homotopic_append_revWord a.1)

end PathClass

end SGraph

/-! ## Part D: 被覆と持ち上げ -/

namespace SGraph

/-- グラフの射: 頂点と辺を写し、始点と反転を保つ。 -/
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

/-- **被覆**: グラフの射であって、各頂点の star（そこから出る辺の集合）の上で
全単射になるもの。写像（データ）と性質（命題）を束ねた structure で、
06_Topology の `Homeomorph` と同じ作り。 -/
structure Covering (Y X : SGraph) extends GraphHom Y X where
  star_surj : ∀ (y : Y.V) (f : X.E), X.init f = toV y →
    ∃ e : Y.E, Y.init e = y ∧ toE e = f
  star_inj : ∀ e e' : Y.E, Y.init e = Y.init e' → toE e = toE e' → e = e'

/-- 語を辺の写像で写す。 -/
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
/-- 問題19: 直線グラフ → 花束（辺の向きだけを見る射）は被覆である。 -/
def zcoverCovering : Covering zcover bouquet where
  toV _ := ()
  toE e := e.2
  init_toE _ := rfl
  bar_toE _ := rfl
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

namespace SGraph.Covering

variable {Y X : SGraph} (p : Covering Y X)

/-- 問題20: **道の持ち上げの存在**。始点の持ち上げを決めれば、道は持ち上がる。 -/
theorem exists_lift_word :
    ∀ (l : List X.E) (y : Y.V) {w : X.V}, Wf X (p.toV y) l w →
      ∃ w' : Y.V, ∃ m : List Y.E, Wf Y y m w' ∧ mapWord p.toE m = l ∧ p.toV w' = w
  | [], y, _, h => ⟨y, [], .nil y, rfl, Wf.nil_inv h⟩
  | f :: l, y, w, h => by
      have hi := Wf.cons_inv h
      match p.star_surj y f hi.1.symm with
      | ⟨e, he_init, he_map⟩ =>
        have hterm : p.toV (Y.term e) = X.term f := by
          rw [← p.term_toE, he_map]
        have h2 : Wf X (p.toV (Y.term e)) l w := by rw [hterm]; exact hi.2
        match exists_lift_word l (Y.term e) h2 with
        | ⟨w', m, hm, hmap, hw⟩ =>
          refine ⟨w', e :: m, ?_, ?_, hw⟩
          · rw [← he_init]
            exact Wf.cons e hm
          · rw [mapWord_cons, he_map, hmap]

/-- 問題21: **持ち上げの一意性**。同じ点から始まり同じ語に写る持ち上げは一致する。 -/
theorem lift_word_unique :
    ∀ {m m' : List Y.E} {y w₁ w₂ : Y.V},
      Wf Y y m w₁ → Wf Y y m' w₂ → mapWord p.toE m = mapWord p.toE m' → m = m'
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, hmap => by simp [mapWord] at hmap
  | _ :: _, [], _, _, _, _, _, hmap => by simp [mapWord] at hmap
  | e :: _, e' :: _, _, _, _, h₁, h₂, hmap => by
      have hi₁ := Wf.cons_inv h₁
      have hi₂ := Wf.cons_inv h₂
      rw [mapWord_cons, mapWord_cons] at hmap
      injection hmap with hh ht
      have he : e = e' := p.star_inj e e' (hi₁.1.symm.trans hi₂.1) hh
      subst he
      rw [lift_word_unique hi₁.2 hi₂.2 ht]

/-- 問題22（発展）: backtrack の削除は、持ち上げの**終点を変えずに**持ち上げの語を縮める。 -/
theorem endpoint_of_reduces :
    ∀ {l l' : List X.E}, Reduces X l l' →
      ∀ {y b : Y.V} {m : List Y.E}, Wf Y y m b → mapWord p.toE m = l →
        ∃ m' : List Y.E, Wf Y y m' b ∧ mapWord p.toE m' = l'
  | _, _, .refl _, _, _, m, hm, hmap => ⟨m, hm, hmap⟩
  | _, _, .trans h₁ h₂, _, _, _, hm, hmap => by
      match endpoint_of_reduces h₁ hm hmap with
      | ⟨_, hm₁, hmap₁⟩ => exact endpoint_of_reduces h₂ hm₁ hmap₁
  | _, _, .cancel l₁ _ _, _, _, _, hm, hmap => by
      match mapWord_split p.toE l₁ hmap with
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
            | ⟨_, hu₁, hu₂⟩ =>
              have hi₁ := Wf.cons_inv hu₂
              have hi₂ := Wf.cons_inv hi₁.2
              have hg : g = Y.bar ê := by
                refine p.star_inj g (Y.bar ê) ?_ ?_
                · exact hi₂.1.symm
                · rw [h2, ← p.bar_toE, h1]
              subst hg
              have hdel := Wf.of_append_cancel [] hu₂
              exact ⟨m₁ ++ m₃, Wf.append hu₁ hdel,
                by rw [mapWord_append, hmap₁, h3]⟩

/-- 問題23: **ホモトピックな道の持ち上げは同じ点に着く**。 -/
theorem endpoint_eq {l l' : List X.E}
    (hh : Homotopic X l l') {y b b' : Y.V} {m m' : List Y.E}
    (hm : Wf Y y m b) (hmapm : mapWord p.toE m = l)
    (hm' : Wf Y y m' b') (hmapm' : mapWord p.toE m' = l') : b = b' := by
  letI : DecidableEq X.E := fun _ _ => Classical.propDecidable _
  have hred : SGraph.reduce l = SGraph.reduce l' := homotopic_iff_reduce_eq.mp hh
  match p.endpoint_of_reduces (reduces_reduce l) hm hmapm,
        p.endpoint_of_reduces (reduces_reduce l') hm' hmapm' with
  | ⟨mr, hmr, hmapr⟩, ⟨mr', hmr', hmapr'⟩ =>
    have heq : mr = mr' := p.lift_word_unique hmr hmr' (by rw [hmapr, hmapr', hred])
    subst heq
    exact Wf.end_unique hmr hmr'

/-! ## Part E: モノドロミー -/

/-- 頂点 `v` の上のファイバー。 -/
abbrev Fiber (v : X.V) : Type := {y : Y.V // p.toV y = v}

theorem fiberExt {v : X.V} {a b : p.Fiber v} (h : a.1 = b.1) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem fiber_wf {v w : X.V} (a : p.Fiber v) {l : List X.E}
    (hl : Wf X v l w) : Wf X (p.toV a.1) l w := by
  rw [a.2]; exact hl

/-- 道の持ち上げの終点。存在は問題20、取り出しは選択公理。 -/
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

/-- `liftEnd` の特徴づけ: 持ち上げの語を1つ示せば、終点が決まる。 -/
theorem liftEnd_eq {v w : X.V} (a : p.Fiber v) {l : List X.E} (hl : Wf X v l w)
    {b : Y.V} {m : List Y.E} (hm : Wf Y a.1 m b) (hmap : mapWord p.toE m = l) :
    (p.liftEnd a l hl).1 = b := by
  match p.liftEnd_spec a hl with
  | ⟨M, hM, hMmap⟩ =>
    have heq : M = m := p.lift_word_unique hM hm (by rw [hMmap, hmap])
    subst heq
    exact Wf.end_unique hM hm

/-- ホモトピー類に沿った輸送（モノドロミー）。問題23により代表の取り方によらない。 -/
noncomputable def transport {v w : X.V} (γ : PathClass X v w) (a : p.Fiber v) :
    p.Fiber w :=
  Quot.lift (fun l => p.liftEnd a l.1 l.2)
    (fun l l' hll' => by
      apply p.fiberExt
      match p.liftEnd_spec a l.2, p.liftEnd_spec a l'.2 with
      | ⟨_, hM, hMmap⟩, ⟨_, hM', hM'map⟩ =>
        exact p.endpoint_eq hll' hM hMmap hM' hM'map)
    γ

/-- 問題24: 定数道に沿った輸送は恒等。 -/
theorem transport_refl {v : X.V} (a : p.Fiber v) :
    p.transport (PathClass.refl v) a = a := by
  apply p.fiberExt
  exact p.liftEnd_eq a (.nil v) (.nil a.1) rfl

/-- 問題25: 連接に沿った輸送は、輸送の合成。 -/
theorem transport_trans {v u w : X.V}
    (γ : PathClass X v u) (δ : PathClass X u w) (a : p.Fiber v) :
    p.transport (γ.comp δ) a = p.transport δ (p.transport γ a) := by
  induction γ using Quot.ind with
  | mk lg =>
    induction δ using Quot.ind with
    | mk ld =>
      apply p.fiberExt
      match p.liftEnd_spec a lg.2 with
      | ⟨m₁, hm₁, hmap₁⟩ =>
        match p.liftEnd_spec (p.liftEnd a lg.1 lg.2) ld.2 with
        | ⟨m₂, hm₂, hmap₂⟩ =>
          exact p.liftEnd_eq a (Wf.append lg.2 ld.2) (Wf.append hm₁ hm₂)
            (by rw [mapWord_append, hmap₁, hmap₂])

/-- 問題26: モノドロミーは、ファイバーの間の全単射。 -/
theorem transport_bijective {v w : X.V} (γ : PathClass X v w) :
    Function.Bijective (p.transport γ) where
  injective := by
    intro a b h
    have h' := congrArg (p.transport γ.inv) h
    rw [← p.transport_trans, ← p.transport_trans, PathClass.comp_inv,
      p.transport_refl, p.transport_refl] at h'
    exact h'
  surjective := by
    intro b
    refine ⟨p.transport γ.inv b, ?_⟩
    rw [← p.transport_trans, PathClass.inv_comp, p.transport_refl]

end SGraph.Covering

open SGraph

/-- 花束のループ（円周を1周する道の離散版）。 -/
def loopWf : Wf bouquet () [true] () :=
  Wf.cons (G := bouquet) true (Wf.nil (bouquet.term true))

/-- ループの類は、ファイバー ℤ に +1 で作用する。 -/
example (i : Int) :
    (zcoverCovering.transport (PathClass.mk loopWf) ⟨i, rfl⟩).1 = i + 1 :=
  zcoverCovering.liftEnd_eq ⟨i, rfl⟩ loopWf
    (Wf.cons (G := zcover) ((i, true) : Int × Bool) (Wf.nil (zcover.term (i, true)))) rfl

/-! ## Part F: π₁(花束) ≃ ℤ -/

/-- 被覆でなくても、グラフの射は削除の列を底へ押し出す。 -/
theorem mapWord_reduces {Y X : SGraph} (p : GraphHom Y X) {m m' : List Y.E}
    (h : Reduces Y m m') : Reduces X (mapWord p.toE m) (mapWord p.toE m') := by
  induction h with
  | cancel m₁ m₂ e =>
      rw [mapWord_append, mapWord_cons, mapWord_cons, ← p.bar_toE, mapWord_append]
      exact .cancel _ _ _
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- 問題27: 直線グラフの既約な道は、最初の辺の向きに単調に進む。 -/
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

/-- 問題28: **直線グラフは単連結**: 既約な閉道は空。 -/
theorem zc_reduced_closed : ∀ {m : List zcover.E} {v : Int},
    Wf zcover v m v → IsReduced m → m = []
  | [], _, _, _ => rfl
  | _ :: _, v, h, hr => by
      exfalso
      cases zc_drift h hr with
      | inl h' =>
          have hlt : v < v := h'.2
          omega
      | inr h' =>
          have hlt : v < v := h'.2
          omega

/-- 語を `k` だけ平行移動する（デッキ変換の辺への作用）。 -/
def shiftWord (k : Int) (m : List zcover.E) : List zcover.E :=
  m.map (fun e => (e.1 + k, e.2))

theorem mapWord_shift (k : Int) : ∀ (m : List zcover.E),
    mapWord zcoverCovering.toE (shiftWord k m) = mapWord zcoverCovering.toE m
  | [] => rfl
  | e :: m => congrArg (fun t => e.2 :: t) (mapWord_shift k m)

/-- 問題29: 平行移動した語も道（平行移動はデッキ変換）。 -/
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

/-- 花束の定数ループの類（基本群の単位元）。 -/
abbrev triv : PathClass bouquet () () := PathClass.refl (G := bouquet) ()

/-- ファイバーの基点（0 の持ち上げ）。 -/
def basePt : zcoverCovering.Fiber () := ⟨(0 : Int), rfl⟩

/-- **モノドロミー次数**: ループを 0 から持ち上げ、終点の整数を読む。 -/
noncomputable def deg (γ : PathClass bouquet () ()) : Int :=
  (zcoverCovering.transport γ basePt).1

/-- 問題30: `i` から持ち上げると、終点は `deg γ + i`。 -/
theorem transport_apply (γ : PathClass bouquet () ()) (i : Int) :
    (zcoverCovering.transport γ ⟨i, rfl⟩).1 = deg γ + i := by
  induction γ using Quot.ind with
  | mk ld =>
    match zcoverCovering.liftEnd_spec basePt ld.2 with
    | ⟨m, hm, hmap⟩ =>
      have hm' : Wf zcover ((0 : Int) + i) (shiftWord i m)
          (deg (Quot.mk _ ld) + i) := shift_wf i m hm
      rw [show ((0 : Int) + i) = i from by omega] at hm'
      exact zcoverCovering.liftEnd_eq ⟨i, rfl⟩ ld.2 hm'
        ((mapWord_shift i m).trans hmap)

/-- 問題31: `deg` は連接を和に写す。 -/
theorem deg_comp (γ δ : PathClass bouquet () ()) :
    deg (γ.comp δ) = deg γ + deg δ := by
  have hfix : zcoverCovering.transport γ basePt = ⟨deg γ, rfl⟩ :=
    zcoverCovering.fiberExt rfl
  have h : deg (γ.comp δ) = deg δ + deg γ := by
    show (zcoverCovering.transport (γ.comp δ) basePt).1 = _
    rw [zcoverCovering.transport_trans γ δ basePt, hfix, transport_apply]
  omega

theorem deg_refl : deg triv = 0 :=
  congrArg Subtype.val (zcoverCovering.transport_refl basePt)

/-- 問題32: `deg` は逆道を符号反転に写す。 -/
theorem deg_inv (γ : PathClass bouquet () ()) : deg γ.inv = - deg γ := by
  have h := deg_comp γ.inv γ
  rw [PathClass.inv_comp, deg_refl] at h
  omega

/-- 花束のループの類。 -/
def loop : PathClass bouquet () () := PathClass.mk loopWf

theorem deg_loop : deg loop = 1 := by
  have h : deg loop = (0 : Int) + 1 :=
    zcoverCovering.liftEnd_eq basePt loopWf
      (Wf.cons (G := zcover) ((0, true) : Int × Bool) (Wf.nil (zcover.term (0, true)))) rfl
  omega

/-- ループの `k` 乗。 -/
def loopPow : Nat → PathClass bouquet () ()
  | 0 => triv
  | k + 1 => (loopPow k).comp loop

/-- 問題33: 持ち上げが 0 に戻るループは自明。 -/
theorem deg_eq_zero {γ : PathClass bouquet () ()} (h : deg γ = 0) :
    γ = triv := by
  induction γ using Quot.ind with
  | mk ld =>
    match zcoverCovering.liftEnd_spec basePt ld.2 with
    | ⟨m, hm, hmap⟩ =>
      have h0 : (zcoverCovering.liftEnd basePt ld.1 ld.2).1 = (0 : Int) := h
      rw [h0] at hm
      have hm0 : Wf zcover (0 : Int) m (0 : Int) := hm
      letI : DecidableEq zcover.E := fun _ _ => Classical.propDecidable _
      have hred : Wf zcover (0 : Int) (SGraph.reduce m) (0 : Int) := Wf.reduce hm0
      have hnil : SGraph.reduce m = [] :=
        zc_reduced_closed hred (reduce_isReduced m)
      have hR : Reduces zcover m [] := hnil ▸ reduces_reduce m
      have hdown := (mapWord_reduces zcoverCovering.toGraphHom hR).toHomotopic
      rw [hmap, mapWord_nil] at hdown
      exact PathClass.sound ld.2 (Wf.nil (G := bouquet) ()) hdown

/-- 問題34: `deg` は単射。 -/
theorem deg_injective : Function.Injective deg := by
  intro γ δ h
  have hz : deg (γ.comp δ.inv) = 0 := by
    rw [deg_comp, deg_inv]
    omega
  have hker := deg_eq_zero hz
  calc γ = γ.comp triv := (PathClass.comp_refl γ).symm
    _ = γ.comp (δ.inv.comp δ) := congrArg γ.comp (PathClass.inv_comp δ).symm
    _ = (γ.comp δ.inv).comp δ := (PathClass.comp_assoc γ δ.inv δ).symm
    _ = triv.comp δ := by rw [hker]
    _ = δ := PathClass.refl_comp δ

theorem deg_loopPow : ∀ k : Nat, deg (loopPow k) = Int.ofNat k
  | 0 => deg_refl
  | k + 1 => by
      have h := deg_comp (loopPow k) loop
      rw [deg_loopPow k, deg_loop] at h
      exact h

/-- 問題35: `deg` は全射。 -/
theorem deg_surjective : Function.Surjective deg := by
  intro n
  match n with
  | Int.ofNat k => exact ⟨loopPow k, deg_loopPow k⟩
  | Int.negSucc k =>
      refine ⟨(loopPow (k + 1)).inv, ?_⟩
      rw [deg_inv, deg_loopPow]
      rfl

/-- 問題36（主定理）: **π₁(花束) ≃ ℤ**。モノドロミー次数 `deg` は、
連接を和に写す全単射である。 -/
theorem pi1_bouquet :
    (∀ γ δ : PathClass bouquet () (), deg (γ.comp δ) = deg γ + deg δ) ∧
      Function.Bijective deg :=
  ⟨deg_comp, ⟨deg_injective, deg_surjective⟩⟩

#print axioms pi1_bouquet
