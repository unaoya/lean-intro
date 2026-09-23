/-!
# 試作A: グラフの道の正規形定理

被覆章の最難所と見込む「各ホモトピー類は既約な代表をちょうど1つ持つ」を
Lean 4 コアのみ(import なし)で証明し、重さを測る。

方針: 語(辺のリスト)の水準で簡約関数 `reduce` を先に定義し、
「ホモトピック ↔ reduce が等しい」を示す。diamond 補題は使わず、
`reduce` が生成関係の各ステップで不変であることに帰着させる。

設計上の発見(本文の囲みに使える):
* backtrack の**挿入**は任意の辺で許すと道の適合条件 `Wf` を壊す
  (挿入する辺の始点が合っている必要がある)。しかし削除だけの一方向関係
  `Reduces` は `Wf` を保ち、`l` から `reduce l` へは削除だけで到達できるので、
  道の水準のホモトピーと語の水準のホモトピーは `Wf` な語の上では一致する。
-/

namespace CoverProbe

/-- Serre 流のグラフ。辺は向きつきで、反転 `bar` は不動点のない対合。 -/
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

theorem term_bar (e : G.E) : G.term (G.bar e) = G.init e := by
  rw [term, G.bar_bar]

/-- 語(辺のリスト)が `v` から `w` への**道**であること: 隣接条件。 -/
inductive Wf (G : SGraph) : G.V → List G.E → G.V → Prop
  | nil (v : G.V) : Wf G v [] v
  | cons (e : G.E) {l : List G.E} {w : G.V} :
      Wf G (G.term e) l w → Wf G (G.init e) (e :: l) w

/-- 語が**既約**であること: backtrack `e, ē` を含まない。 -/
def IsReduced : List G.E → Prop
  | [] => True
  | [_] => True
  | e :: f :: l => f ≠ G.bar e ∧ IsReduced (f :: l)

theorem IsReduced.tail : ∀ {l : List G.E} {e : G.E}, IsReduced (e :: l) → IsReduced l
  | [], _, _ => trivial
  | _ :: _, _, h => h.2

/-- 逆転補題: `e :: l` が道なら、始点は `e` の始点で、残りも道。 -/
theorem Wf.cons_inv {v w : G.V} {e : G.E} {l : List G.E} (h : Wf G v (e :: l) w) :
    v = G.init e ∧ Wf G (G.term e) l w := by
  cases h with
  | cons _ h' => exact ⟨rfl, h'⟩

/-- 語のホモトピー: backtrack の削除と挿入で生成される同値関係。 -/
inductive Homotopic (G : SGraph) : List G.E → List G.E → Prop
  | cancel (l₁ l₂ : List G.E) (e : G.E) :
      Homotopic G (l₁ ++ e :: G.bar e :: l₂) (l₁ ++ l₂)
  | refl (l : List G.E) : Homotopic G l l
  | symm {l l' : List G.E} : Homotopic G l l' → Homotopic G l' l
  | trans {l l' l'' : List G.E} :
      Homotopic G l l' → Homotopic G l' l'' → Homotopic G l l''

/-- 削除だけの一方向関係。`Wf` を保つ(挿入は保たない)ので別に立てる。 -/
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

/-- 語の簡約(正規形の計算)。 -/
def reduce : List G.E → List G.E
  | [] => []
  | e :: l => rcons e (reduce l)

theorem reduce_cons (e : G.E) (l : List G.E) : reduce (e :: l) = rcons e (reduce l) := rfl

theorem isReduced_rcons {e : G.E} : ∀ {m : List G.E}, IsReduced m → IsReduced (rcons e m)
  | [], _ => trivial
  | f :: r, hm => by
      rw [rcons_cons]
      by_cases h : f = G.bar e
      · rw [if_pos h]; exact hm.tail
      · rw [if_neg h]; exact ⟨h, hm⟩

theorem reduce_isReduced : ∀ l : List G.E, IsReduced (reduce l)
  | [] => trivial
  | _ :: l => isReduced_rcons (reduce_isReduced l)

/-- 鍵になる計算補題: 既約な語に `ē` と `e` を順に足すと元に戻る。 -/
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

theorem reduce_cancel (e : G.E) (l : List G.E) :
    reduce (e :: G.bar e :: l) = reduce l := by
  rw [reduce_cons, reduce_cons]
  exact rcons_rcons_bar e (reduce l) (reduce_isReduced l)

theorem reduce_append_cancel (e : G.E) : ∀ (l₁ l₂ : List G.E),
    reduce (l₁ ++ e :: G.bar e :: l₂) = reduce (l₁ ++ l₂)
  | [], l₂ => reduce_cancel e l₂
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

/-- どの語も自分の正規形へ**削除だけで**到達する。 -/
theorem reduces_reduce : ∀ l : List G.E, Reduces G l (reduce l)
  | [] => .refl _
  | e :: l => by
      rw [reduce_cons]
      exact .trans (Reduces.cons e (reduces_reduce l)) (reduces_cons_rcons e (reduce l))

/-- **正規形定理**: 2つの語がホモトピックであることと正規形が一致することは同値。 -/
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
  | e :: f :: r, h => by
      rw [reduce_cons, reduce_eq_self_of_isReduced h.2, rcons_cons, if_neg h.1]

/-- **既約代表の一意性**: ホモトピックな既約語は等しい。 -/
theorem eq_of_homotopic_of_isReduced {l l' : List G.E}
    (hl : IsReduced l) (hl' : IsReduced l') (h : Homotopic G l l') : l = l' := by
  rw [← reduce_eq_self_of_isReduced hl, ← reduce_eq_self_of_isReduced hl']
  exact homotopic_iff_reduce_eq.mp h

end Reduce

/-! ## 簡約は道であることを保つ -/

theorem Wf.append {v u w : G.V} : ∀ {l₁ l₂ : List G.E},
    Wf G v l₁ u → Wf G u l₂ w → Wf G v (l₁ ++ l₂) w
  | _, _, .nil _, h₂ => h₂
  | _, _, .cons e h₁, h₂ => .cons e (Wf.append h₁ h₂)

/-- backtrack の**削除**は道であることを保つ。
    (挿入は保たない: 挿入する辺の始点が合っている必要がある。) -/
theorem Wf.of_append_cancel : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E} {e : G.E},
    Wf G v (l₁ ++ e :: G.bar e :: l₂) w → Wf G v (l₁ ++ l₂) w
  | _, _, [], _, e, h => by
      have h₁ := Wf.cons_inv h
      have h₂ := Wf.cons_inv h₁.2
      have h'' := h₂.2
      rw [term_bar] at h''
      rw [h₁.1]
      exact h''
  | _, _, x :: l₁, _, _, h => by
      cases h with
      | cons _ h' => exact .cons _ (Wf.of_append_cancel l₁ h')

theorem Wf.of_reduces {v w : G.V} {l l' : List G.E} (h : Reduces G l l') :
    Wf G v l w → Wf G v l' w := by
  induction h with
  | cancel l₁ l₂ e => exact fun hw => Wf.of_append_cancel l₁ hw
  | refl l => exact id
  | trans _ _ ih₁ ih₂ => exact fun hw => ih₂ (ih₁ hw)

/-- 道の正規形はやはり道で、始点・終点を保つ。 -/
theorem Wf.reduce [DecidableEq G.E] {v w : G.V} {l : List G.E} (hw : Wf G v l w) :
    Wf G v (SGraph.reduce l) w :=
  Wf.of_reduces (reduces_reduce l) hw

end SGraph

/-! ## 例: 花束グラフ(円周の離散版) -/

/-- 頂点1つ、ループ1本(向きつき辺2本)。π₁ ≃ ℤ となるべき最小の例。 -/
def bouquet : SGraph where
  V := Unit
  E := Bool
  init _ := ()
  bar := Bool.not
  bar_bar := by decide
  bar_ne := by decide

instance : DecidableEq bouquet.E := inferInstanceAs (DecidableEq Bool)

/-- 正規形は計算できる(語の問題が決定可能)。 -/
example : SGraph.reduce (G := bouquet) [true, false, true] = [true] := rfl
example : SGraph.reduce (G := bouquet) [true, true, false, false] = [] := rfl

end CoverProbe
