import «06_Topology»

/-! # 発展演習: グラフの被覆

`06_Topology.lean` まで読み終えた人のための演習問題集
（`07_Exercises.lean`・`08_Ascoli.lean` とは独立に読める）。題材は**被覆と基本群**で、
ゴールは「円周の基本群は整数の群 $\mathbb{Z}$ と同型」の離散版である。

## 位相空間の被覆の証明の骨組み

被覆 $p : \mathbb{R} \to S^1$ を使って $\pi_1(S^1) \cong \mathbb{Z}$ を示す古典的な議論は、
次の段を踏む。

1. **局所自明性**: 被覆とは、底空間の各点のまわりで、上の空間が
   底の開集合のコピーの直和になっている写像である
2. **道の持ち上げ**: 底の道は、始点の持ち上げを決めれば上へ一意に持ち上がる。
   区間 $[0, 1]$ のコンパクト性（ルベーグ数）で道を局所自明な小片に切って示す
3. **ホモトピーの持ち上げ**: ホモトピックな道の持ち上げは、同じ点に着く
4. **モノドロミー**: 2・3 から、ループのホモトピー類がファイバー（1点の逆像）に作用する
5. **計算**: 上の空間 $\mathbb{R}$ が単連結なので、この作用によってループの類が整数と対応する

## グラフ版: 解析を抜いた骨組み

この演習では、同じ骨組みを**グラフ**の上で組み立てる。位相は一切出てこない。

| 位相空間 | グラフ |
|---|---|
| 道 $[0, 1] \to X$ | 辺のリスト（隣接条件つき） |
| ホモトピー | 行って戻る辺の対 $e\,\bar e$ の挿入・削除 |
| 局所自明性 | 各頂点から出る辺（star）の上の全単射 |
| 区間のコンパクト性とルベーグ数 | リストの長さに関する帰納法 |
| $\mathbb{R}$ | 直線グラフ（頂点は整数） |
| $S^1$ | 花束（頂点1つ・ループ1本） |
| $\mathbb{R}$ は単連結 | 直線グラフには、行って戻る以外の閉じた道がない |

段 2 の解析（区間のコンパクト性）は、グラフではリストの帰納法に置き換わる。
一方で段 4・5 の議論は、位相空間版とほぼ同じ形のまま残る。グラフ版を組み立てると、
被覆の理論のどこが解析で、どこが解析によらない部分かが分かれて見える。

## 構成

* Part A: Serre グラフと道
* Part B: ホモトピーと正規形定理
* Part C: π₁ 亜群
* Part D: 被覆と持ち上げ
* Part E: モノドロミー
* Part F: π₁(花束) ≃ ℤ

山場は Part B の正規形定理（問題11）と Part D の持ち上げ（問題20〜23）である。
Part F はそれまでの結果をすべて使う。

## 進め方

`07_Exercises.lean`・`08_Ascoli.lean` と同じく、`sorry` を自分の証明で置き換える。
解答は `09_CoveringSol.lean` にある。与えてある宣言（`sorry` のないもの）も、
問題を解くときに使ってよい。`06_Topology.lean` からは、全単射 `Function.Bijective` だけを使う。
-/

/-! ## Part A: Serre グラフと道

Serre 流のグラフは、頂点の型 `V`、**向きつき**の辺の型 `E`、各辺の始点 `init`、
辺の向きを反対にする**反転** `bar` からなる。無向の辺 1 本を、互いに反転しあう
向きつきの辺 2 本 `e`・`ē` で表す。こうしておくと、道を「向きつきの辺の列」として
一様に扱え、辺の終点も「反転した辺の始点」として定義できる。

辺のリストを**語**と呼ぶ。語が `v` から `w` への**道**であることを、
添字つき帰納型 `Wf G v l w` で表す。`nil v` は `v` にとどまる長さ 0 の道、
`cons e h` は `e` の終点から出る道 `h` の前に `e` をつないだ道である。
-/

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

/-- 問題1: 反転した辺の終点は、元の辺の始点であることを示せ。

ヒント: `term` を展開して `bar_bar` で書き換える。 -/
theorem term_bar (e : G.E) : G.term (G.bar e) = G.init e :=
  sorry

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

/-! ### 補足: 逆転補題を与えておく理由

道 `h : Wf G v (e :: l) w` を `cases h` で分解すると、Lean は添字の等式
`v = G.init e` を解いて変数 `v` を消そうとする。添字の片方が変数ならこれは解けるが、
両辺がどちらも関数の適用になると解けない。たとえば `e :: ē :: l` の形の道を
2 段続けて `cases` で分解すると、2 段目で `G.init (G.bar e)`（`e` の終点）と
`G.init e'`（次の辺 `e'` の始点）を等しいとおく必要が生じ、
依存消去の失敗（Dependent elimination failed）というエラーになる。

逆転補題 `Wf.cons_inv` は、添字を変数 `v` のままにして分解し、解けない等式を
**結論の一部** `v = G.init e` として返す。こうすると等式は証明の中で `rw` に使える
ただの仮定になる。以下の問題では、道の分解には `cases` ではなくこの 2 つの補題を使うとよい。
-/

/-- 問題2: 道の連接は道であることを示せ。

ヒント: 1 つ目の道についての場合分けで再帰する。`nil` なら 2 つ目の道そのもの、
`cons e h₁` なら `.cons e (Wf.append h₁ h₂)`。 -/
theorem Wf.append {v u w : G.V} : ∀ {l₁ l₂ : List G.E},
    Wf G v l₁ u → Wf G u l₂ w → Wf G v (l₁ ++ l₂) w :=
  sorry

/-- 問題3: 道の終点は、始点と語で決まることを示せ。

ヒント: 1 つ目の道で場合分けし、2 つ目の道は逆転補題で分解して再帰する。 -/
theorem Wf.end_unique : ∀ {y w₁ w₂ : G.V} {m : List G.E},
    Wf G y m w₁ → Wf G y m w₂ → w₁ = w₂ :=
  sorry

/-- 問題4: 連接の形の語が道なら、途中の点で 2 つの道に分かれることを示せ。

ヒント: `l₁` についての再帰。`e :: l₁` の場合は `Wf.cons_inv` で分解して再帰し、
始点を `rw` で合わせてから `Wf.cons e` をつける。 -/
theorem Wf.append_split : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E},
    Wf G v (l₁ ++ l₂) w → ∃ u, Wf G v l₁ u ∧ Wf G u l₂ w :=
  sorry

/-- 語の反転: 各辺を反転して逆順に並べる。道を逆向きにたどることに当たる。 -/
def revWord (G : SGraph) (l : List G.E) : List G.E := (l.map G.bar).reverse

theorem revWord_cons (e : G.E) (l : List G.E) :
    revWord G (e :: l) = revWord G l ++ [G.bar e] := by
  simp [revWord]

theorem revWord_append (l l' : List G.E) :
    revWord G (l ++ l') = revWord G l' ++ revWord G l := by
  simp [revWord]

/-- 問題5: 道を逆向きにたどった語も道であることを示せ。

ヒント: 道についての再帰。`cons e h` の場合は `revWord_cons` で書き換え、
`[G.bar e]` が `G.term e` から `G.init e` への道であること（問題1）と問題2を使う。 -/
theorem Wf.revWord : ∀ {v w : G.V} {l : List G.E},
    Wf G v l w → Wf G w (SGraph.revWord G l) v :=
  sorry

end SGraph

/-! 例を 2 つ用意しておく。**花束**は頂点 1 つ・ループ 1 本のグラフで、円周の離散版に当たる。
**直線グラフ**は頂点が整数で、`i` と `i + 1` を辺でつないだグラフで、実数直線の離散版に当たる。
Part D で、直線グラフから花束への「向きだけを見る」射が被覆になることを示す。
-/

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

/-! ## Part B: ホモトピーと正規形定理

グラフの道のホモトピーは、**行って戻る**辺の対 `e, ē`（backtrack）の削除と、
その逆の挿入で生成される同値関係 `Homotopic` として定義する。連続的な変形は出てこない。
backtrack を含まない語を**既約**と呼ぶ。

この Part の目標は**正規形定理**（問題11）である。**2 つの語がホモトピックであるのは、
それぞれを簡約した既約語が一致するときに限る。**とくに、各ホモトピー類には既約な代表がちょうど 1 つある（問題12）。

証明の方針を先に述べておく。「簡約の順序によらず結果が一致する」という
合流性を直接示すのではなく、簡約を**関数** `reduce` として先に定義する。
`reduce` は語を後ろから読み、既約な語の先頭に辺を 1 本ずつ足していく（`rcons`）。
足す辺が先頭と打ち消し合えば消す。あとは、`reduce` の値が backtrack の削除で
変わらないこと（問題9）と、どの語も `reduce` の値まで削除だけで縮められること
（問題10）を示せば、正規形定理が出る。関数として定義しておけば、
正規形は計算で求まる（Part B の末尾の例）。

`reduce` の定義には、辺が等しいかどうかの判定（`DecidableEq G.E`）が要る。
-/

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

/-! ### 補足: 削除だけの関係 `Reduces` を別に立てる理由

語のホモトピー `Homotopic` は語についての関係で、道であること（隣接条件）は見ていない。
道の水準で考えると、backtrack の**削除**は道を道に写す（問題13）が、
**挿入**はそうとは限らない。挿入する辺 `e` の始点が、挿入する位置の頂点と
一致している必要があるからである。

そこで、道についての議論はすべて削除だけの関係 `Reduces` で行い、
挿入は正規形定理の中に閉じ込める。どの語も削除だけで正規形に到達する（問題10）ので、
2 つのホモトピックな道は、どちらも削除だけで同じ正規形に縮められる。
紙の上では「ホモトピーで変形する」と一言で済ませるところだが、
形式化すると、この区別が避けられない形で表に出てくる。
-/

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

/-- 問題6: 既約な語に `rcons` で辺を足しても既約であることを示せ。

ヒント: `m` で場合分けし、`f :: r` の場合は `rcons_cons` で展開して
`by_cases h : f = G.bar e` で分ける。`if` は `if_pos h`・`if_neg h` で外せる。 -/
theorem isReduced_rcons {e : G.E} : ∀ {m : List G.E}, IsReduced m → IsReduced (rcons e m) :=
  sorry

/-- 問題7: 簡約の結果は既約であることを示せ。 -/
theorem reduce_isReduced : ∀ l : List G.E, IsReduced (reduce l) :=
  sorry

/-- 問題8: 既約な語に `ē` と `e` を順に足すと、元に戻ることを示せ。

ヒント: `m` の場合分け。`f :: r` の場合は `f = G.bar (G.bar e)` かどうかで分ける。
等しければ `bar_bar` により `f = e` で、`r` をさらに場合分けする
（`r = g :: r'` なら、`m` が既約なので `g ≠ G.bar e`）。 -/
theorem rcons_rcons_bar (e : G.E) : ∀ (m : List G.E), IsReduced m →
    rcons e (rcons (G.bar e) m) = m :=
  sorry

/-- 問題9: `reduce` の値は、backtrack の削除で変わらないことを示せ。

ヒント: `l₁` についての再帰。`[]` の場合は `reduce_cons` を 2 回展開して問題7・8。 -/
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

/-- 問題10: どの語も、自分の正規形へ**削除だけで**到達することを示せ。

ヒント: 再帰。`Reduces.cons` と、与えてある `reduces_cons_rcons` を `Reduces.trans` でつなぐ。 -/
theorem reduces_reduce : ∀ l : List G.E, Reduces G l (reduce l) :=
  sorry

/-- 問題11（正規形定理）: ホモトピックであることと、正規形が一致することは同値であることを示せ。

ヒント: →は `Homotopic` についての帰納法（`induction h`）で、`cancel` の場合が問題9。
←は、問題10により `l` も `l'` も正規形まで削除で縮められることを使う（`Reduces.toHomotopic`）。 -/
theorem homotopic_iff_reduce_eq {l l' : List G.E} :
    Homotopic G l l' ↔ reduce l = reduce l' :=
  sorry

theorem reduce_eq_self_of_isReduced : ∀ {l : List G.E}, IsReduced l → reduce l = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by
      rw [reduce_cons, reduce_eq_self_of_isReduced h.2, rcons_cons, if_neg h.1]

/-- 問題12: ホモトピックな既約語は等しいことを示せ（既約な代表の一意性）。

ヒント: 与えてある `reduce_eq_self_of_isReduced` で両辺を正規形に書き換え、問題11。 -/
theorem eq_of_homotopic_of_isReduced {l l' : List G.E}
    (hl : IsReduced l) (hl' : IsReduced l') (h : Homotopic G l l') : l = l' :=
  sorry

end Reduce

/-- 問題13: backtrack の**削除**は、道であることを保つことを示せ。

ヒント: `l₁` についての再帰。`[]` の場合は逆転補題を 2 回使い、
問題1で `G.term (G.bar e) = G.init e` と書き換える。 -/
theorem Wf.of_append_cancel : ∀ {v w : G.V} (l₁ : List G.E) {l₂ : List G.E} {e : G.E},
    Wf G v (l₁ ++ e :: G.bar e :: l₂) w → Wf G v (l₁ ++ l₂) w :=
  sorry

theorem Wf.of_reduces {v w : G.V} {l l' : List G.E} (h : Reduces G l l') :
    Wf G v l w → Wf G v l' w := by
  induction h with
  | cancel l₁ l₂ e => exact fun hw => Wf.of_append_cancel l₁ hw
  | refl l => exact id
  | trans _ _ ih₁ ih₂ => exact fun hw => ih₂ (ih₁ hw)

/-- 問題14: 道の正規形は、同じ始点・終点の道であることを示せ。

ヒント: 与えてある `Wf.of_reduces` と問題10。 -/
theorem Wf.reduce [DecidableEq G.E] {v w : G.V} {l : List G.E} (hw : Wf G v l w) :
    Wf G v (SGraph.reduce l) w :=
  sorry

end SGraph

/-! 花束では、正規形が計算で求まる。どちらも `rfl`（定義の展開による計算）で確かめられる。
2 つ目は「正の向きに 2 周してから逆向きに 2 周するループは、ホモトピーで消える」ことに当たる。
-/

/-- 花束では、正規形が計算で求まる。 -/
example : SGraph.reduce (G := bouquet) [true, false, true] = [true] := rfl
example : SGraph.reduce (G := bouquet) [true, true, false, false] = [] := rfl

/-! ## Part C: π₁ 亜群

道のホモトピー類全体に、連接と逆道を入れる。類は商型 `Quot` で作り、
連接 `comp`・逆道 `inv` は `Quot.lift` で代表の取り方によらずに定義する。
そのためにホモトピーが連接と反転と両立すること（`appendLeft`・`appendRight`・問題15）を使う。

基点を固定しないので、得られるのは群ではなく**亜群**（すべての射が可逆な圏）である。
基点 `v` から `v` へのループの類だけを見れば群になり、それが基本群である。
Part F では花束の基点 `()` のループの類 `PathClass bouquet () ()` を扱う。
-/

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

/-- 問題15: ホモトピックな語を反転しても、ホモトピックであることを示せ。

ヒント: `induction h`。`cancel` の場合、反転した語がまた `… ++ e :: G.bar e :: …` の形に
なることを `simp [revWord_append, revWord_cons, G.bar_bar, List.append_assoc]` で示す。 -/
theorem Homotopic.revWordCong {l l' : List G.E} (h : Homotopic G l l') :
    Homotopic G (revWord G l) (revWord G l') :=
  sorry

/-- 問題16: 逆向きにたどってから元の向きにたどると、ホモトピーで消えることを示せ。

ヒント: 再帰。`e :: l` の場合、`revWord_cons` と `List.append_assoc` で書き換えると
真ん中に backtrack `ē e` が現れる（`Homotopic.cancel` を `G.bar e` に使い、`bar_bar`）。 -/
theorem homotopic_revWord_append : ∀ l : List G.E, Homotopic G (revWord G l ++ l) [] :=
  sorry

/-- 問題17: 元の向きにたどってから逆向きにたどっても、ホモトピーで消えることを示せ。

ヒント: 再帰。`appendRight`・`appendLeft` で内側の `l ++ revWord G l` を消し、
最後に残る `[e, ē]` を消す。 -/
theorem homotopic_append_revWord : ∀ l : List G.E, Homotopic G (l ++ revWord G l) [] :=
  sorry

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

/-! 問題18a〜e は亜群の法則である。どれも `induction γ using Quot.ind` で代表に下ろしてから示す。
単位律と結合律は、代表の語の等式（`List.nil_append`・`List.append_nil`・`List.append_assoc`）
なので `mk_eq_of_eq` で、逆元の法則は問題16・17と `sound` で示せる。
道の証明を明示する必要があるときは `Wf.append` などで組み立てる。
-/

/-- 問題18a: 左単位律を示せ。 -/
theorem refl_comp (γ : PathClass G v w) : (refl v).comp γ = γ :=
  sorry

/-- 問題18b: 右単位律を示せ。 -/
theorem comp_refl (γ : PathClass G v w) : γ.comp (refl w) = γ :=
  sorry

/-- 問題18c: 結合律を示せ。 -/
theorem comp_assoc {u z : G.V} (γ : PathClass G v u) (δ : PathClass G u w)
    (ε : PathClass G w z) : (γ.comp δ).comp ε = γ.comp (δ.comp ε) :=
  sorry

/-- 問題18d: 逆道を先にたどると定数道であることを示せ。 -/
theorem inv_comp (γ : PathClass G v w) : γ.inv.comp γ = refl w :=
  sorry

/-- 問題18e: 逆道をあとでたどっても定数道であることを示せ。 -/
theorem comp_inv (γ : PathClass G v w) : γ.comp γ.inv = refl v :=
  sorry

end PathClass

end SGraph

/-! ## Part D: 被覆と持ち上げ

グラフの射は、頂点と辺を写し、始点と反転を保つ写像である。**被覆**は、グラフの射であって、
各頂点 `y` から出る辺の集合（`y` の star）を、`y` の像から出る辺の集合へ
**全単射**に写すものとする。位相空間の被覆の局所自明性が、グラフではこの条件になる。

被覆 `Covering` は、写像（データ）と、それが star の上で全単射であるという性質（命題）を
1 つに束ねた structure として定義する。`06_Topology.lean` の同相写像 `Homeomorph`
（写像と連続性を束ねた structure）と同じ作りである。`extends GraphHom Y X` により、
被覆 `p` から射としての成分 `p.toV`・`p.toE`・`p.bar_toE` などがそのまま取り出せる。

この Part の中心は問題20（**道の持ち上げ**）で、証明は語の長さについての帰納法である。
位相空間版で区間のコンパクト性とルベーグ数が担う仕事を、ここではリストの再帰が担う。
問題22・23は、ホモトピックな道の持ち上げが同じ点に着くこと（ホモトピーの持ち上げ）で、
Part B の正規形定理に帰着させる。
-/

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
/-- 問題19: 直線グラフ → 花束（辺の向きだけを見る射）は被覆であることを示せ。
写像の成分は与えてあるので、star の上の全射性と単射性を示す。

ヒント: 全射性は花束の辺 `f` で場合分けする。`false` の場合、`y` から出る逆向きの辺は
`(y - 1, false)` である。ただし `y : zcover.V` のままでは引き算の記法が見つからないので、
`∀ j : Int, ∃ i : Int, i + 1 = j` を先に `Int` の上で示して `y` に使うとよい。
単射性は 2 本の辺を分解し、向きが等しいことを使って場合分けし、`omega` で。 -/
def zcoverCovering : Covering zcover bouquet where
  toV _ := ()
  toE e := e.2
  init_toE _ := rfl
  bar_toE _ := rfl
  star_surj := sorry
  star_inj := sorry

namespace SGraph.Covering

variable {Y X : SGraph} (p : Covering Y X)

/-- 問題20: **道の持ち上げの存在**。始点の持ち上げを決めれば、道は持ち上がることを示せ。

ヒント: `l` についての再帰。`f :: l` の場合、star の全射性 `p.star_surj` で
`f` の持ち上げ `e` を取り、`e` の終点から残りを再帰で持ち上げる。
`e` の終点の像が `f` の終点であることは `GraphHom.term_toE` から出る。 -/
theorem exists_lift_word :
    ∀ (l : List X.E) (y : Y.V) {w : X.V}, Wf X (p.toV y) l w →
      ∃ w' : Y.V, ∃ m : List Y.E, Wf Y y m w' ∧ mapWord p.toE m = l ∧ p.toV w' = w :=
  sorry

/-- 問題21: **持ち上げの一意性**。同じ点から始まり同じ語に写る持ち上げは、一致することを示せ。

ヒント: 両方の語で場合分けする。先頭の辺どうしは始点も像も同じなので、
star の単射性 `p.star_inj` で等しい。 -/
theorem lift_word_unique :
    ∀ {m m' : List Y.E} {y w₁ w₂ : Y.V},
      Wf Y y m w₁ → Wf Y y m' w₂ → mapWord p.toE m = mapWord p.toE m' → m = m' :=
  sorry

/-- 問題22（発展）: backtrack の削除は、持ち上げの**終点を変えずに**持ち上げの語を縮めることを示せ。

ヒント: `Reduces` の構成子についての再帰。本体は `cancel l₁ l₂ f` の場合で、
`mapWord_split` で `m` を `m₁ ++ m₂` に切り、`m₂` から `ê :: g :: m₃` の形を取り出す。
`g` と `Y.bar ê` は始点も像も同じなので、star の単射性で等しい。
つまり上の語にも backtrack があり、あとは問題13で消せる。 -/
theorem endpoint_of_reduces :
    ∀ {l l' : List X.E}, Reduces X l l' →
      ∀ {y b : Y.V} {m : List Y.E}, Wf Y y m b → mapWord p.toE m = l →
        ∃ m' : List Y.E, Wf Y y m' b ∧ mapWord p.toE m' = l' :=
  sorry

/-- 問題23: **ホモトピックな道の持ち上げは同じ点に着く**ことを示せ。

ヒント: `reduce` を使うために `letI : DecidableEq X.E := fun _ _ => Classical.propDecidable _`
と置く。両方の持ち上げを正規形まで縮める（問題10・22）。正規形は等しい（問題11）ので、
縮めた持ち上げの語も等しく（問題21）、終点も等しい（問題3）。 -/
theorem endpoint_eq {l l' : List X.E}
    (hh : Homotopic X l l') {y b b' : Y.V} {m m' : List Y.E}
    (hm : Wf Y y m b) (hmapm : mapWord p.toE m = l)
    (hm' : Wf Y y m' b') (hmapm' : mapWord p.toE m' = l') : b = b' :=
  sorry

/-! ## Part E: モノドロミー

頂点 `v` の上の**ファイバー** `p.Fiber v` は、`v` に写る頂点の全体である。
ファイバーの点 `a` と、`v` から `w` への道の類 `γ` が与えられたとき、
`γ` の代表を `a` から持ち上げた終点は `w` の上のファイバーに入る。
問題23により、これは代表の取り方によらない。こうして得られる写像
`p.transport γ : p.Fiber v → p.Fiber w` を**モノドロミー**（輸送）と呼ぶ。

持ち上げの存在（問題20）は「存在する」という命題なので、終点を取り出すには
選択公理（`Classical.choose`）を使う（`liftEnd`）。取り出した終点は、
持ち上げの語を 1 つ示せば決まる（`liftEnd_eq`）ので、以下の問題では
`liftEnd` の中身を開かずに `liftEnd_eq` を使えばよい。
-/

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

/-- 問題24: 定数道に沿った輸送は恒等であることを示せ。

ヒント: `p.fiberExt` で点の等式に落とし、`liftEnd_eq` に長さ 0 の持ち上げ `.nil a.1` を渡す。 -/
theorem transport_refl {v : X.V} (a : p.Fiber v) :
    p.transport (PathClass.refl v) a = a :=
  sorry

/-- 問題25: 連接に沿った輸送は、輸送の合成であることを示せ。

ヒント: `γ`・`δ` を代表に下ろす。`liftEnd_spec` で 2 つの持ち上げの語を取り出し、
それらを連接した語（問題2）を `liftEnd_eq` に渡す。 -/
theorem transport_trans {v u w : X.V}
    (γ : PathClass X v u) (δ : PathClass X u w) (a : p.Fiber v) :
    p.transport (γ.comp δ) a = p.transport δ (p.transport γ a) :=
  sorry

/-- 問題26: モノドロミーは、ファイバーの間の全単射であることを示せ。

ヒント: 逆道 `γ.inv` に沿った輸送が逆写像になる。問題24・25と問題18d・18e。 -/
theorem transport_bijective {v w : X.V} (γ : PathClass X v w) :
    Function.Bijective (p.transport γ) :=
  sorry

end SGraph.Covering

/-! ### 補足: 問題24〜26はグラフを使っていない

問題24〜26の証明を振り返ると、グラフであることを直接には一度も使っていない。
使ったのは、持ち上げが一意に定まること（`liftEnd_eq`）と、道の類の亜群の法則（問題18）だけである。
したがって、位相空間の被覆についても、道とホモトピーの持ち上げさえ示せば、
モノドロミーについての同じ定理が同じ証明で得られる。
被覆の理論のうち解析が要るのは持ち上げの部分だけで、そこから先は持ち上げの一意性から出る。
-/

open SGraph

/-! 花束のループ（正の向きの辺 1 本からなる道）を、直線グラフの点 `i` から持ち上げると、
`i` から `i + 1` への辺になる。つまりループの類はファイバー（整数全体）に `+1` で作用する。
Part F で示す $\pi_1 \cong \mathbb{Z}$ の対応の中身は、この作用である。
-/

/-- 花束のループ（円周を1周する道の離散版）。 -/
def loopWf : Wf bouquet () [true] () :=
  Wf.cons (G := bouquet) true (Wf.nil (bouquet.term true))

/-- ループの類は、ファイバー ℤ に +1 で作用する。 -/
example (i : Int) :
    (zcoverCovering.transport (PathClass.mk loopWf) ⟨i, rfl⟩).1 = i + 1 :=
  zcoverCovering.liftEnd_eq ⟨i, rfl⟩ loopWf
    (Wf.cons (G := zcover) ((i, true) : Int × Bool) (Wf.nil (zcover.term (i, true)))) rfl

/-! ## Part F: π₁(花束) ≃ ℤ

花束の基本群から整数への写像 `deg`（**モノドロミー次数**）を、
「ループを直線グラフの 0 から持ち上げ、終点の整数を読む」ことで定義する。
主定理は、`deg` が連接を和に写す全単射であることである。証明は 3 つの部品からなり、
それぞれ位相空間版の議論の部品に対応する。

* **準同型性**（問題31）: 直線グラフの平行移動 `i ↦ i + k` は、持ち上げと可換な変換
  （**デッキ変換**）である（問題29・30）。`i` から持ち上げた終点は `deg γ + i` になる
* **単射性**（問題33・34）: 直線グラフは**単連結**である。既約な道は一方向に単調に進むので、
  既約な閉じた道は空しかない（問題27・28）。持ち上げが 0 に戻るループは、
  上で削除だけで空にでき、それを底へ写せばループ自身が自明とわかる
* **全射性**（問題35）: ループの `k` 乗と、その逆道で、すべての整数が得られる

整数の等式・不等式は `omega` で閉じられる。ただし `omega` は `Int.ofNat k` を
ひとかたまりの未知数として扱うので、`Int.ofNat (k + 1) = Int.ofNat k + 1` のような
等式は、定義の展開（`rfl`・`exact`）で閉じる。
-/

/-- 被覆でなくても、グラフの射は削除の列を底へ押し出す。 -/
theorem mapWord_reduces {Y X : SGraph} (p : GraphHom Y X) {m m' : List Y.E}
    (h : Reduces Y m m') : Reduces X (mapWord p.toE m) (mapWord p.toE m') := by
  induction h with
  | cancel m₁ m₂ e =>
      rw [mapWord_append, mapWord_cons, mapWord_cons, ← p.bar_toE, mapWord_append]
      exact .cancel _ _ _
  | refl l => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- 問題27: 直線グラフの既約な道は、最初の辺の向きに単調に進むことを示せ。

ヒント: 語についての再帰で、2 辺目以降の道に再帰した結果と、1 辺目の向きを比べる。
向きが食い違うと、隣接条件から 2 辺目が 1 辺目の反転になり、既約性に反する。
辺は `cases e with | mk i b` で整数と向きに分解できる。 -/
theorem zc_drift : ∀ {m : List zcover.E} {e : zcover.E} {v w : Int},
    Wf zcover v (e :: m) w → IsReduced (e :: m) →
    (e.2 = true ∧ v < w) ∨ (e.2 = false ∧ w < v) :=
  sorry

/-- 問題28: **直線グラフは単連結**: 既約な閉じた道は空であることを示せ。

ヒント: 空でなければ、問題27から `v < v` が出る。 -/
theorem zc_reduced_closed : ∀ {m : List zcover.E} {v : Int},
    Wf zcover v m v → IsReduced m → m = [] :=
  sorry

/-- 語を `k` だけ平行移動する（デッキ変換の辺への作用）。 -/
def shiftWord (k : Int) (m : List zcover.E) : List zcover.E :=
  m.map (fun e => (e.1 + k, e.2))

theorem mapWord_shift (k : Int) : ∀ (m : List zcover.E),
    mapWord zcoverCovering.toE (shiftWord k m) = mapWord zcoverCovering.toE m
  | [] => rfl
  | e :: m => congrArg (fun t => e.2 :: t) (mapWord_shift k m)

/-- 問題29: 平行移動した語も道であることを示せ（平行移動はデッキ変換）。

ヒント: `m` についての再帰。辺の向きで場合分けし、始点を `subst` で揃える。
`(i + 1) + k = (i + k) + 1` のような書き換えは `show … from by omega` で作る。 -/
theorem shift_wf (k : Int) : ∀ (m : List zcover.E) {v w : Int},
    Wf zcover v m w → Wf zcover (v + k) (shiftWord k m) (w + k) :=
  sorry

/-- 花束の定数ループの類（基本群の単位元）。 -/
abbrev triv : PathClass bouquet () () := PathClass.refl (G := bouquet) ()

/-- ファイバーの基点（0 の持ち上げ）。 -/
def basePt : zcoverCovering.Fiber () := ⟨(0 : Int), rfl⟩

/-- **モノドロミー次数**: ループを 0 から持ち上げ、終点の整数を読む。 -/
noncomputable def deg (γ : PathClass bouquet () ()) : Int :=
  (zcoverCovering.transport γ basePt).1

/-- 問題30: `i` から持ち上げると、終点は `deg γ + i` であることを示せ。

ヒント: `γ` を代表に下ろし、0 からの持ち上げ（`liftEnd_spec`）を `i` だけ平行移動したもの
（問題29・`mapWord_shift`）を `liftEnd_eq` に渡す。 -/
theorem transport_apply (γ : PathClass bouquet () ()) (i : Int) :
    (zcoverCovering.transport γ ⟨i, rfl⟩).1 = deg γ + i :=
  sorry

/-- 問題31: `deg` は連接を和に写すことを示せ。

ヒント: 問題25で `γ.comp δ` に沿った輸送を分解し、`δ` に沿った輸送の始点が
`deg γ` であることから問題30を使う。 -/
theorem deg_comp (γ δ : PathClass bouquet () ()) :
    deg (γ.comp δ) = deg γ + deg δ :=
  sorry

theorem deg_refl : deg triv = 0 :=
  congrArg Subtype.val (zcoverCovering.transport_refl basePt)

/-- 問題32: `deg` は逆道を符号反転に写すことを示せ。

ヒント: 問題31を `γ.inv` と `γ` に使い、問題18d と `deg_refl`。 -/
theorem deg_inv (γ : PathClass bouquet () ()) : deg γ.inv = - deg γ :=
  sorry

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

/-- 問題33: 持ち上げが 0 に戻るループは自明であることを示せ。

ヒント: `γ` を代表に下ろし、0 から 0 への持ち上げの語 `m` を取る。
`m` の正規形は 0 から 0 への道（問題14）で既約（問題7）なので、問題28により空である。
つまり `m` は削除だけで空にできる（問題10）。それを底へ写し（`mapWord_reduces`）、
`PathClass.sound` を使う。`reduce` を使うには `DecidableEq zcover.E` を
`Classical.propDecidable` で置く。 -/
theorem deg_eq_zero {γ : PathClass bouquet () ()} (h : deg γ = 0) :
    γ = triv :=
  sorry

/-- 問題34: `deg` は単射であることを示せ。

ヒント: `deg (γ.comp δ.inv) = 0` を示して問題33を使い、亜群の法則（問題18）で
`γ = δ` に直す。`calc` で等式をつなぐと見通しがよい。 -/
theorem deg_injective : Function.Injective deg :=
  sorry

theorem deg_loopPow : ∀ k : Nat, deg (loopPow k) = Int.ofNat k
  | 0 => deg_refl
  | k + 1 => by
      have h := deg_comp (loopPow k) loop
      rw [deg_loopPow k, deg_loop] at h
      exact h

/-- 問題35: `deg` は全射であることを示せ。

ヒント: `n` で場合分けする。`Int.ofNat k` には `loopPow k`、
`Int.negSucc k`（$-(k+1)$）には `(loopPow (k + 1)).inv` を使う（`deg_loopPow`・問題32）。 -/
theorem deg_surjective : Function.Surjective deg :=
  sorry

/-- 問題36（主定理）: **π₁(花束) ≃ ℤ**。モノドロミー次数 `deg` は、
連接を和に写す全単射であることを示せ。 -/
theorem pi1_bouquet :
    (∀ γ δ : PathClass bouquet () (), deg (γ.comp δ) = deg γ + deg δ) ∧
      Function.Bijective deg :=
  sorry

/-! 解答（`09_CoveringSol.lean`）では、主定理が依存する公理は
`propext`・`Classical.choice`・`Quot.sound` の 3 つだけである。
`06_Topology.lean` の最終定理・`08_Ascoli.lean` の主定理と同じである。
問題を解き終えたら、次の出力に `sorryAx` が残っていないことを確かめよ。
-/

#print axioms pi1_bouquet
