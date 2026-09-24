import «06_Topology»

/-! # 発展演習: 実数

`06_Topology.lean` まで読み終えた人のための演習問題集
（`07_Exercises.lean` とは独立に読める）。題材は**実数**で、
「実数の公理」から出発して、四則演算と順序の計算規則、絶対値、
アルキメデス性、実数の位相と連続関数、そして閉区間のコンパクト性（Heine–Borel）・
連結性・ルベーグ数の補題までを証明する。

## 実数を構成せずに仮定する

実数を有理数から構成する（デデキント切断やコーシー列）ことはしない。
代わりに、実数が満たすべき性質——**完備順序体**の公理——を `class` として書き、
「この公理を満たす型 `R`」を変数として受け取る。以下の定理はすべて
「任意の完備順序体 `R` について」の形をしている。

公理を `axiom` で宣言するのではなく `class` の引数として受け取るので、
`#print axioms` に新しい公理は現れない（末尾で確かめる）。何を仮定したかは、
定理の型の引数 `[CompleteOrderedField R]` として見える。

## 構成

* Part A: 実数の公理
* Part B: 足し算と掛け算
* Part C: 順序
* Part D: 絶対値と最小値
* Part E: 完備性
* Part F: 位相と連続性
* Part G: 閉区間

Part B〜D は公理から計算規則を導く部分で、1 問 1 問は短い。
Part E で初めて完備性（上限の存在）を使う。山場は Part G の 3 つの定理である。

## 進め方

`07_Exercises.lean` と同じく、`sorry` を自分の証明で置き換える。
解答は `08_RealSol.lean` にある。与えてある宣言（`sorry` のないもの）も、
問題を解くときに使ってよい。
-/

/-! ## Part A: 実数の公理

完備順序体の公理を並べる。4 つのグループからなる。

* **可換体**: 足し算と掛け算の結合律・可換律、`0` と `1`、符号反転 `-a`、
  分配法則、`0 ≠ 1`、`0` でない数の逆数 `a⁻¹`
* **全順序**: `≤` の反射律・推移律・反対称律と、どの 2 数も比べられること。
  `<` は `≤` から `a ≤ b ∧ ¬ b ≤ a` として定まる
* **演算と順序の両立**: 両辺に同じ数を足しても `≤` は保たれる。0 以上の数の積は 0 以上
* **完備性**: 空でなく上に有界な集合には、最小の上界（上限）がある

`Add R`・`Mul R` などを `extends` しているのは、`a + b`・`a * b`・`a⁻¹`・`a ≤ b` といった
記法を使うためである（記法が class で動く仕組みは [`05_MathematicalTools.lean` 1節](#sec-Intro2.classes)）。
引き算 `a - b` と割り算 `a / b` は公理に含めず、`a + -b`・`a * b⁻¹` として定義する。
数 `2` は `1 + 1` と定義する。
-/

/-- 完備順序体の公理。 -/
class CompleteOrderedField (R : Type) extends Add R, Mul R, Neg R, Inv R, Zero R, One R,
    LE R, LT R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  zero_ne_one : (0 : R) ≠ 1
  mul_inv_cancel : ∀ a : R, a ≠ 0 → a * a⁻¹ = 1
  le_refl : ∀ a : R, a ≤ a
  le_trans : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : R, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : R, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : R, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c, c + a ≤ c + b
  mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  exists_lub : ∀ S : Set R, (∃ x, x ∈ S) → (∃ M, ∀ x ∈ S, x ≤ M) →
    ∃ s, (∀ x ∈ S, x ≤ s) ∧ ∀ M, (∀ x ∈ S, x ≤ M) → s ≤ M

namespace CompleteOrderedField

variable {R : Type} [CompleteOrderedField R]

instance : Sub R := ⟨fun a b => a + -b⟩
instance : Div R := ⟨fun a b => a * b⁻¹⟩
instance : OfNat R 2 := ⟨1 + 1⟩

instance : Std.Associative (α := R) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := R) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := R) (· * ·) := ⟨mul_assoc⟩
instance : Std.Commutative (α := R) (· * ·) := ⟨mul_comm⟩

theorem sub_def (a b : R) : a - b = a + -b := rfl

theorem div_def (a b : R) : a / b = a * b⁻¹ := rfl

theorem two_def : (2 : R) = 1 + 1 := rfl

/-! ## Part B: 足し算と掛け算

`a * 0 = 0` や `-(-a) = a` のような「当たり前」の規則も、公理には入っていないので
証明が要る。ここでは、以後の計算で使う規則を公理から導く。

証明はほとんどが `rw`（書き換え）の連鎖である。足し算の項の順序や括弧の付け方を
入れ替えるだけの等式は、`ac_rfl` で閉じられる（下の補足）。
-/

/-! ### 補足: `ac_rfl` が閉じる等式

`ac_rfl` は、結合律と可換律だけで移り合う 2 つの式が等しいことを示すタクティクである。
たとえば `a + (b + c) + d = d + c + (a + b)` を閉じる。
使うには、演算が結合的・可換であることを `Std.Associative`・`Std.Commutative` の
instance として登録しておく（Part A の末尾でしている）。
`ac_rfl` が扱うのは項の並べ替えだけで、`a + -a = 0` のような打ち消しや、
分配法則は扱わない。それらは `rw` で公理や補題を使って書き換える。
-/

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

/-- 問題1: 足し算は左から簡約できることを示せ。

ヒント: `congrArg (fun x => -a + x) h` で両辺の左に `-a` を足し、
`add_assoc`・`neg_add_cancel`・`zero_add` で書き換える。 -/
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
  sorry

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  rw [add_comm a, add_comm b] at h
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

/-- 問題2: `-(-a) = a` を示せ。

ヒント: 与えてある `neg_eq_of_add_eq_zero` に、公理 `neg_add_cancel a` を渡す。 -/
theorem neg_neg (a : R) : -(-a) = a :=
  sorry

theorem neg_zero : -(0 : R) = 0 := neg_eq_of_add_eq_zero (add_zero 0)

/-- 問題3: `-(a + b) = -a + -b` を示せ。

ヒント: `neg_eq_of_add_eq_zero` を使い、`a + b + (-a + -b) = 0` を示す。
`(a + -a) + (b + -b)` への並べ替えは `ac_rfl` で。 -/
theorem neg_add (a b : R) : -(a + b) = -a + -b :=
  sorry

theorem sub_self (a : R) : a - a = 0 := add_neg_cancel a

theorem sub_zero (a : R) : a - 0 = a := by rw [sub_def, neg_zero, add_zero]

theorem zero_sub (a : R) : 0 - a = -a := by rw [sub_def, zero_add]

theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_def, add_assoc, neg_add_cancel, add_zero]

theorem add_sub_cancel (a b : R) : a + b - b = a := by
  rw [sub_def, add_assoc, add_neg_cancel, add_zero]

theorem sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg (· + b) h
    simp only at h'
    rw [sub_add_cancel, zero_add] at h'
    exact h'
  · intro h; rw [h, sub_self]

theorem neg_sub (a b : R) : -(a - b) = b - a := by
  rw [sub_def, neg_add, neg_neg, sub_def, add_comm]

theorem sub_add_sub_cancel (a b c : R) : a - b + (b - c) = a - c := by
  rw [sub_def, sub_def, sub_def, add_assoc, ← add_assoc (-b), neg_add_cancel, zero_add]

theorem add_sub_add_right (a b c : R) : a + c - (b + c) = a - b := by
  rw [sub_def, sub_def, neg_add]
  calc a + c + (-b + -c) = a + -b + (c + -c) := by ac_rfl
    _ = a + -b := by rw [add_neg_cancel, add_zero]

theorem mul_one (a : R) : a * 1 = a := by rw [mul_comm, one_mul]

theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

/-- 問題4: `a * 0 = 0` を示せ。

ヒント: `a * 0 + a * 0 = a * (0 + 0) = a * 0 + 0` なので、問題1で `a * 0` を簡約する。 -/
theorem mul_zero (a : R) : a * 0 = 0 :=
  sorry

theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]

/-- 問題5: `a * -b = -(a * b)` を示せ。

ヒント: `neg_eq_of_add_eq_zero` を使う。`a * b + a * -b = a * (b + -b)`（分配法則）`= a * 0`。 -/
theorem mul_neg (a b : R) : a * -b = -(a * b) :=
  sorry

theorem neg_mul (a b : R) : -a * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_def, sub_def, mul_add, mul_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [mul_comm, mul_sub, mul_comm c, mul_comm c]

theorem two_mul (a : R) : 2 * a = a + a := by rw [two_def, add_mul, one_mul]

/-- 問題6: 積が 0 なら、どちらかが 0 であることを示せ。

ヒント: `by_cases ha : a = 0` で分ける。`a ≠ 0` なら
`b = a⁻¹ * a * b = a⁻¹ * (a * b) = 0`。 -/
theorem mul_eq_zero {a b : R} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  sorry

theorem inv_mul_cancel {a : R} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_cancel a h]

theorem div_mul_cancel {a b : R} (h : b ≠ 0) : a / b * b = a := by
  rw [div_def, mul_assoc, inv_mul_cancel h, mul_one]

theorem mul_div_cancel {a b : R} (h : b ≠ 0) : a * b / b = a := by
  rw [div_def, mul_assoc, mul_inv_cancel b h, mul_one]

theorem mul_div_cancel_left {c : R} (e : R) (h : c ≠ 0) : c * (e / c) = e := by
  rw [mul_comm, div_mul_cancel h]

theorem inv_ne_zero {a : R} (h : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h'
  have := mul_inv_cancel a h
  rw [h', mul_zero] at this
  exact zero_ne_one this

/-! ## Part C: 順序

順序の公理は `≤` について述べてあるので、`<` についての規則はそこから導く。
`0 < 1` も公理ではなく定理である（問題12）。

不等式をいくつもつなぐ議論は `calc` で書くと読みやすい。`≤` と `<` を混ぜてつなぐには、
推移律を `Trans` の instance として登録しておく必要がある（この Part で与えている）。
-/

theorem lt_irrefl (a : R) : ¬ a < a := fun h => ((lt_iff_le_not_le a a).mp h).2 (le_refl a)

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b := ((lt_iff_le_not_le a b).mp h).1

/-- 問題7: `a ≤ b` でないことと `b < a` は同値であることを示せ。

ヒント: →は `le_total a b` で場合分けし、公理 `lt_iff_le_not_le` で `<` を組み立てる。 -/
theorem not_le {a b : R} : ¬ a ≤ b ↔ b < a :=
  sorry

theorem not_lt {a b : R} : ¬ a < b ↔ b ≤ a := by
  constructor
  · intro h
    rcases le_total b a with h' | h'
    · exact h'
    · exact Classical.byContradiction fun h'' => h (not_le.mp h'')
  · intro h h'
    exact not_le.mpr h' h

theorem lt_of_le_of_lt {a b c : R} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  not_le.mp fun h => not_le.mpr h₂ (le_trans c a b h h₁)

theorem lt_of_lt_of_le {a b c : R} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  not_le.mp fun h => not_le.mpr h₁ (le_trans b c a h₂ h)

theorem lt_trans {a b c : R} (h₁ : a < b) (h₂ : b < c) : a < c :=
  lt_of_le_of_lt (le_of_lt h₁) h₂

instance : Trans (α := R) (β := R) (γ := R) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans _ _ _⟩
instance : Trans (α := R) (β := R) (γ := R) (· ≤ ·) (· < ·) (· < ·) := ⟨lt_of_le_of_lt⟩
instance : Trans (α := R) (β := R) (γ := R) (· < ·) (· ≤ ·) (· < ·) := ⟨lt_of_lt_of_le⟩
instance : Trans (α := R) (β := R) (γ := R) (· < ·) (· < ·) (· < ·) := ⟨lt_trans⟩

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := fun e => lt_irrefl b (e ▸ h)

theorem lt_of_le_of_ne {a b : R} (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b :=
  not_le.mp fun h => h₂ (le_antisymm a b h₁ h)

theorem lt_or_le (a b : R) : a < b ∨ b ≤ a := by
  by_cases h : b ≤ a
  · exact .inr h
  · exact .inl (not_le.mp h)

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a, add_comm b]; exact add_le_add_left a b h c

theorem le_of_add_le_add_left {a b c : R} (h : c + a ≤ c + b) : a ≤ b := by
  have := add_le_add_left _ _ h (-c)
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at this
  exact this

/-- 問題8: 両辺に同じ数を足しても `<` は保たれることを示せ。

ヒント: 問題7で `<` を「`≤` でない」に言い換える。`c + b ≤ c + a` なら、与えてある
`le_of_add_le_add_left` で `b ≤ a` となり矛盾する。 -/
theorem add_lt_add_left {a b : R} (h : a < b) (c : R) : c + a < c + b :=
  sorry

theorem add_lt_add_right {a b : R} (h : a < b) (c : R) : a + c < b + c := by
  rw [add_comm a, add_comm b]; exact add_lt_add_left h c

theorem add_le_add {a b c d : R} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans _ _ _ (add_le_add_right h₁ c) (add_le_add_left _ _ h₂ b)

theorem add_lt_add {a b c d : R} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  lt_trans (add_lt_add_right h₁ c) (add_lt_add_left h₂ b)

theorem add_lt_add_of_lt_of_le {a b c d : R} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left _ _ h₂ b)

/-- 問題9: `0 ≤ b - a` と `a ≤ b` は同値であることを示せ。

ヒント: 両向きとも `add_le_add_right` で両辺に `a`（または `-a`）を足し、
`sub_add_cancel`・`add_neg_cancel` で整理する。 -/
theorem sub_nonneg {a b : R} : 0 ≤ b - a ↔ a ≤ b :=
  sorry

theorem sub_pos {a b : R} : 0 < b - a ↔ a < b := by
  constructor
  · intro h; exact not_le.mp fun h' => not_le.mpr h (by
      have := add_le_add_right h' (-a); rwa [add_neg_cancel] at this)
  · intro h; exact not_le.mp fun h' => not_le.mpr h (by
      have := add_le_add_right h' a; rwa [zero_add, sub_add_cancel] at this)

/-- 問題10: 符号を反転すると `≤` の向きが逆になることを示せ。

ヒント: `a ≤ b` の両辺に `-a` を足し、さらに `-b` を足す（`add_le_add_right` を 2 回）。 -/
theorem neg_le_neg {a b : R} (h : a ≤ b) : -b ≤ -a :=
  sorry

theorem neg_lt_neg {a b : R} (h : a < b) : -b < -a :=
  not_le.mp fun h' => not_le.mpr h (by have := neg_le_neg h'; rwa [neg_neg, neg_neg] at this)

theorem neg_nonneg {a : R} : 0 ≤ -a ↔ a ≤ 0 := by
  constructor
  · intro h; have := neg_le_neg h; rwa [neg_neg, neg_zero] at this
  · intro h; have := neg_le_neg h; rwa [neg_zero] at this

theorem neg_pos {a : R} : 0 < -a ↔ a < 0 := by
  constructor
  · intro h; have := neg_lt_neg h; rwa [neg_neg, neg_zero] at this
  · intro h; have := neg_lt_neg h; rwa [neg_zero] at this

theorem add_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have := add_lt_add ha hb; rwa [add_zero] at this

theorem add_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have := add_le_add ha hb; rwa [add_zero] at this

theorem lt_add_of_pos_right (a : R) {b : R} (h : 0 < b) : a < a + b := by
  have := add_lt_add_left h a; rwa [add_zero] at this

theorem sub_lt_self (a : R) {b : R} (h : 0 < b) : a - b < a := by
  have := add_lt_add_left (neg_lt_neg h) a
  rwa [neg_zero, add_zero] at this

/-- 問題11: 正の数どうしの積は正であることを示せ。

ヒント: `mul_nonneg` で `0 ≤ a * b`。`0 ≠ a * b` は問題6から。`lt_of_le_of_ne` でまとめる。 -/
theorem mul_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  sorry

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  have := mul_nonneg c (b - a) hc (sub_nonneg.mpr h)
  rw [mul_sub] at this
  exact sub_nonneg.mp this

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm a, mul_comm b]; exact mul_le_mul_of_nonneg_left h hc

theorem mul_lt_mul_of_pos_left {a b c : R} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  have := mul_pos hc (sub_pos.mpr h)
  rw [mul_sub] at this
  exact sub_pos.mp this

theorem mul_self_nonneg (a : R) : 0 ≤ a * a := by
  rcases le_total 0 a with h | h
  · exact mul_nonneg a a h h
  · have := mul_nonneg (-a) (-a) (neg_nonneg.mpr h) (neg_nonneg.mpr h)
    rwa [neg_mul_neg] at this

/-- 問題12: `0 < 1` を示せ。

ヒント: 与えてある `mul_self_nonneg 1` で `0 ≤ 1 * 1 = 1`。等しくないことは公理 `zero_ne_one`。 -/
theorem zero_lt_one : (0 : R) < 1 :=
  sorry

theorem zero_lt_two : (0 : R) < 2 := add_pos zero_lt_one zero_lt_one

/-- 問題13: 正の数の逆数は正であることを示せ。

ヒント: 問題7で背理法の形にする。`a⁻¹ ≤ 0` なら、`a` を掛けて
（`mul_le_mul_of_nonneg_left`）`1 ≤ 0` となり、問題12に反する。 -/
theorem inv_pos {a : R} (h : 0 < a) : 0 < a⁻¹ :=
  sorry

theorem div_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := mul_pos ha (inv_pos hb)

theorem two_ne_zero : (2 : R) ≠ 0 := (ne_of_lt zero_lt_two).symm

theorem add_halves (a : R) : a / 2 + a / 2 = a := by
  rw [← two_mul, mul_comm, div_mul_cancel two_ne_zero]

theorem half_pos {a : R} (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

/-- 問題14: 正の数の半分は、もとの数より小さいことを示せ。

ヒント: `a / 2 < a / 2 + a / 2 = a`（`lt_add_of_pos_right`・`half_pos`・`add_halves`）。 -/
theorem half_lt_self {a : R} (h : 0 < a) : a / 2 < a :=
  sorry

theorem half_add_lt {c ε : R} (h : 0 < ε) : c + ε / 2 < c + ε :=
  add_lt_add_left (half_lt_self h) c

/-! ## Part D: 絶対値と最小値

絶対値 `abs a` は、`0 ≤ a` なら `a`、そうでなければ `-a` と定義する。
「`0 ≤ a` かどうか」で場合分けする `if` を書くには、その命題が決定可能である必要があり、
ここでは排中律（`open Classical`）でそれを与える。そのため `abs` は `noncomputable` になる。
最小値 `min a b` も同様である。

この Part の中心は三角不等式（問題16）で、以後 `ε`-論法のたびに使う。
-/

open Classical in
/-- 絶対値。 -/
noncomputable def abs (a : R) : R := if 0 ≤ a then a else -a

theorem abs_of_nonneg {a : R} (h : 0 ≤ a) : abs a = a := by
  rw [abs, if_pos h]

theorem abs_of_neg {a : R} (h : a < 0) : abs a = -a := by
  rw [abs, if_neg (not_le.mpr h)]

theorem abs_zero : abs (0 : R) = 0 := abs_of_nonneg (le_refl 0)

theorem abs_of_nonpos {a : R} (h : a ≤ 0) : abs a = -a := by
  rcases lt_or_le a 0 with h' | h'
  · exact abs_of_neg h'
  · have : a = 0 := le_antisymm _ _ h h'
    rw [this, abs_zero, neg_zero]

theorem abs_nonneg (a : R) : 0 ≤ abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h]; exact le_of_lt (neg_pos.mpr h)
  · rw [abs_of_nonneg h]; exact h

theorem le_abs_self (a : R) : a ≤ abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h]; exact le_trans _ _ _ (le_of_lt h) (le_of_lt (neg_pos.mpr h))
  · rw [abs_of_nonneg h]; exact le_refl a

theorem abs_neg (a : R) : abs (-a) = abs a := by
  rcases lt_or_le a 0 with h | h
  · rw [abs_of_neg h, abs_of_nonneg (le_of_lt (neg_pos.mpr h))]
  · rcases lt_or_le 0 a with h' | h'
    · rw [abs_of_nonneg h, abs_of_neg (neg_pos.mp (by rwa [neg_neg]))]
      exact neg_neg a
    · have : a = 0 := le_antisymm _ _ h' h
      rw [this, neg_zero]

theorem neg_abs_le (a : R) : -abs a ≤ a := by
  have := le_abs_self (-a)
  rw [abs_neg] at this
  have := neg_le_neg this
  rwa [neg_neg] at this

theorem abs_sub_comm (a b : R) : abs (a - b) = abs (b - a) := by
  rw [← neg_sub, abs_neg]

/-- 問題15: `|a| < b` と `-b < a < b` は同値であることを示せ。

ヒント: →は `le_abs_self`・`neg_abs_le`。←は `lt_or_le a 0` で `a` の符号により場合分けする。 -/
theorem abs_lt {a b : R} : abs a < b ↔ -b < a ∧ a < b :=
  sorry

/-- 問題16: **三角不等式** `|a + b| ≤ |a| + |b|` を示せ。

ヒント: `a + b` の符号で場合分けする。負なら `|a + b| = -a + -b` で、
`-a ≤ |a|` は `neg_abs_le` から出る。 -/
theorem abs_add (a b : R) : abs (a + b) ≤ abs a + abs b :=
  sorry

theorem abs_sub_le (a b c : R) : abs (a - c) ≤ abs (a - b) + abs (b - c) := by
  rw [← sub_add_sub_cancel a b c]
  exact abs_add _ _

theorem abs_sub_self (a : R) : abs (a - a) = 0 := by rw [sub_self, abs_zero]

theorem abs_le_abs_add_abs_sub (a b : R) : abs a ≤ abs b + abs (a - b) := by
  have := abs_add b (a - b)
  rwa [sub_def, ← add_assoc, add_comm b a, add_assoc, add_neg_cancel, add_zero] at this

theorem abs_sub_lt_of {c y ε : R} (h₁ : c - ε < y) (h₂ : y < c + ε) : abs (y - c) < ε := by
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have := add_lt_add_right h₁ (-c)
    rw [sub_def, add_comm c, add_assoc, add_neg_cancel, add_zero] at this
    exact this
  · have := add_lt_add_right h₂ (-c)
    rw [add_comm c, add_assoc, add_neg_cancel, add_zero] at this
    exact this

theorem mul_nonpos_of_nonneg_of_nonpos {a b : R} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have := mul_nonneg a (-b) ha (neg_nonneg.mpr hb)
  rw [mul_neg] at this
  exact neg_nonneg.mp this

/-- 問題17: `|a * b| = |a| * |b|` を示せ。

ヒント: `le_total 0 a` と `le_total 0 b` で 4 通りに分ける。
`abs_of_nonneg`・`abs_of_nonpos`・`mul_nonpos_of_nonneg_of_nonpos`・`neg_mul_neg` を使う。 -/
theorem abs_mul (a b : R) : abs (a * b) = abs a * abs b :=
  sorry

open Classical in
noncomputable def min (a b : R) : R := if a ≤ b then a else b

theorem min_le_left (a b : R) : min a b ≤ a := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact le_refl a
  · rw [if_neg h]; exact le_of_lt (not_le.mp h)

theorem min_le_right (a b : R) : min a b ≤ b := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact le_refl b

theorem lt_min {a b c : R} (hb : a < b) (hc : a < c) : a < min b c := by
  unfold min
  by_cases h : b ≤ c
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact hc

/-! ## Part E: 完備性

Part B〜D で使った公理は、有理数でも成り立つ。実数を有理数から区別するのは
完備性（上限の存在）だけである。この Part では、完備性から
**アルキメデス性**（どの実数よりも大きい自然数がある）と、
**整数部分**（どの実数も、ある整数 `n` について `n ≤ x < n + 1` を満たす）を導く。

そのために、自然数と整数を実数に埋め込む関数 `natCast`・`intCast` を定義する。
`intCast` が足し算を保つこと（`intCast_add`）などの計算は与えてある。
-/

/-- 問題18: 上限より少しでも小さい値の上には、集合の元があることを示せ。

ヒント: 背理法（`Classical.byContradiction`）。どの元も `s - ε` 以下なら、`s - ε` は上界なので
`s ≤ s - ε` となり、`sub_lt_self` に反する。 -/
theorem exists_mem_gt_of_lub {S : Set R} {s : R}
    (hlub : ∀ M, (∀ x ∈ S, x ≤ M) → s ≤ M) {ε : R} (hε : 0 < ε) :
    ∃ x, x ∈ S ∧ s - ε < x :=
  sorry

/-- 自然数の埋め込み。 -/
def natCast : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1

theorem natCast_zero : (natCast 0 : R) = 0 := rfl

theorem natCast_succ (n : Nat) : (natCast (n + 1) : R) = natCast n + 1 := rfl

theorem natCast_nonneg : ∀ n : Nat, (0 : R) ≤ natCast n
  | 0 => le_refl 0
  | n + 1 => add_nonneg (natCast_nonneg n) (le_of_lt zero_lt_one)

theorem natCast_add (m : Nat) : ∀ n : Nat, (natCast (m + n) : R) = natCast m + natCast n
  | 0 => (add_zero _).symm
  | n + 1 => by
      rw [← Nat.add_assoc, natCast_succ, natCast_succ, natCast_add m n, add_assoc]

/-- 問題19: **アルキメデス性**: どの実数よりも大きい自然数があることを示せ。

ヒント: 背理法。自然数の像 `{y | ∃ n, y = natCast n}` が `x` で押さえられるなら上限 `s` がある。
問題18で `s - 1 < natCast n` となる `n` を取ると、`natCast (n + 1)` が `s` を超える。 -/
theorem exists_nat_gt (x : R) : ∃ n : Nat, x < natCast n :=
  sorry

/-- 整数の埋め込み。 -/
def intCast : Int → R
  | Int.ofNat n => natCast n
  | Int.negSucc n => -natCast (n + 1)

theorem intCast_natCast (n : Nat) : (intCast (n : Int) : R) = natCast n := rfl

theorem intCast_zero : (intCast 0 : R) = 0 := rfl

theorem intCast_sub_one : ∀ k : Int, (intCast (k - 1) : R) = intCast k - 1
  | Int.ofNat 0 => by
      rw [show Int.ofNat 0 - 1 = Int.negSucc 0 from rfl]
      show -(natCast 1 : R) = natCast 0 - 1
      rw [natCast_succ, natCast_zero, zero_add, zero_sub]
  | Int.ofNat (n + 1) => by
      rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp only [Int.ofNat_eq_natCast]; omega]
      show (natCast n : R) = natCast (n + 1) - 1
      rw [natCast_succ, add_sub_cancel]
  | Int.negSucc n => by
      rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) by simp only [Int.negSucc_eq]; omega]
      show -(natCast (n + 1 + 1) : R) = -natCast (n + 1) - 1
      rw [natCast_succ (n + 1), neg_add]; rfl

theorem intCast_add_one (k : Int) : (intCast (k + 1) : R) = intCast k + 1 := by
  have h := intCast_sub_one (R := R) (k + 1)
  rw [Int.add_sub_cancel] at h
  rw [h, sub_add_cancel]

theorem intCast_add_natCast (k : Int) : ∀ n : Nat,
    (intCast (k + n) : R) = intCast k + natCast n
  | 0 => by rw [Int.natCast_zero, Int.add_zero]; exact (add_zero _).symm
  | n + 1 => by
      rw [Int.natCast_add, Int.natCast_one, ← Int.add_assoc, intCast_add_one,
        intCast_add_natCast k n, natCast_succ, add_assoc]

theorem intCast_neg_natCast_add (N : Nat) : (intCast (-(N : Int)) : R) + natCast N = 0 := by
  rw [← intCast_add_natCast, Int.add_left_neg]; rfl

theorem intCast_sub_natCast (k : Int) : ∀ n : Nat,
    (intCast (k - n) : R) = intCast k - natCast n
  | 0 => by rw [Int.natCast_zero, Int.sub_zero, natCast_zero, sub_zero]
  | n + 1 => by
      rw [show k - ((n + 1 : Nat) : Int) = k - (n : Int) - 1 by omega, intCast_sub_one,
        intCast_sub_natCast k n, natCast_succ, sub_def, sub_def, sub_def, neg_add, add_assoc]

/-- 整数の足し算は実数の足し算に写る。 -/
theorem intCast_add (m : Int) : ∀ n : Int, (intCast (m + n) : R) = intCast m + intCast n
  | Int.ofNat k => intCast_add_natCast m k
  | Int.negSucc k => by
      rw [show m + Int.negSucc k = m - ((k + 1 : Nat) : Int) by simp only [Int.negSucc_eq]; omega,
        intCast_sub_natCast]
      rfl

theorem intCast_neg (m : Int) : (intCast (-m) : R) = -intCast m := by
  apply Eq.symm
  apply neg_eq_of_add_eq_zero
  rw [← intCast_add, Int.add_right_neg]; rfl

/-- 問題20: （発展）**整数部分**: どの実数 `x` にも、`n ≤ x < n + 1` となる整数 `n` があることを示せ。

ヒント: 問題19を `x` と `-x` に使い、自然数 `N`・`M` で `-N ≤ x < M` とする。
「`a ≤ x < a + m` なら `a + k ≤ x < a + k + 1` となる自然数 `k` がある」を `m` の帰納法で示し、
`a = -N`、`m = N + M` に使う。`intCast_add_natCast`・`intCast_neg_natCast_add` が使える。 -/
theorem exists_int_floor (x : R) : ∃ n : Int, intCast n ≤ x ∧ x < intCast n + 1 :=
  sorry

/-! ## Part F: 位相と連続性

「どの点のまわりにも `ε`-近傍が収まる」集合を開集合として、`R` に位相を入れる
（`06_Topology.lean` の `TopologicalSpace` の instance）。
以後、`R` を値に取る関数の連続性は、`06_Topology.lean` の定義
（開集合の逆像が開）の意味である。

その定義のままでは扱いにくいので、`ε`-論法の形の判定法（問題23）を用意する。
これを使って、連続関数の和・積が連続であることを示す。位相空間 `X` は一般のもので、
`R` 自身に限らない。
-/

/-- 問題21: 実数の位相: どの点のまわりにも `ε`-近傍が収まる集合を開集合とする。
位相の公理を満たすことを示せ。

ヒント: 共通部分では、2 つの `ε` の小さいほう（`min`・`lt_min`・`min_le_left`）を取る。
合併では、点が属する 1 つの集合の `ε` をそのまま使う。 -/
instance : TopologicalSpace R where
  IsOpen s := ∀ x ∈ s, ∃ ε, 0 < ε ∧ ∀ y, abs (y - x) < ε → y ∈ s
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

theorem isOpen_iff {s : Set R} :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε, 0 < ε ∧ ∀ y, abs (y - x) < ε → y ∈ s := Iff.rfl

/-- `ε`-近傍（開区間）。 -/
def ball (x ε : R) : Set R := {y | abs (y - x) < ε}

/-- 問題22: `ε`-近傍は開集合であることを示せ。

ヒント: 点 `y` のまわりには、半径 `ε - |y - x|` の近傍が収まる。三角不等式 `abs_sub_le` を使う。 -/
theorem isOpen_ball (x ε : R) : IsOpen (ball x ε) :=
  sorry

theorem mem_ball_self {x ε : R} (h : 0 < ε) : x ∈ ball x ε := by
  show abs (x - x) < ε
  rw [abs_sub_self]; exact h

section Continuity

variable {X : Type} [TopologicalSpace X]

/-- 問題23: 実数値関数の連続性は、各点で「値が `ε` 以内に収まる開近傍がある」で判定できることを示せ。

ヒント: `f ⁻¹' s` を「`f ⁻¹' s` に含まれる開集合全体の合併」と書き直し（`Set.ext`）、
`isOpen_sUnion` を使う。 -/
theorem continuous_of_forall {f : X → R}
    (h : ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (f y - f x) < ε) :
    Continuous f :=
  sorry

theorem forall_of_continuous {f : X → R} (hf : Continuous f) (x : X) {ε : R} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (f y - f x) < ε :=
  ⟨f ⁻¹' ball (f x) ε, hf _ (isOpen_ball _ _), mem_ball_self hε, fun _ hy => hy⟩

theorem continuous_id' : Continuous (fun x : R => x) :=
  continuous_of_forall fun x ε hε => ⟨ball x ε, isOpen_ball x ε, mem_ball_self hε, fun _ hy => hy⟩

theorem continuous_const (c : R) : Continuous (fun _ : X => c) :=
  continuous_of_forall fun _ _ hε =>
    ⟨Set.univ, isOpen_univ, trivial, fun _ _ => by rw [abs_sub_self]; exact hε⟩

/-- 問題24: 連続関数の和は連続であることを示せ。

ヒント: 問題23を使う。`f` と `g` に `ε / 2` で `forall_of_continuous` を使い、2 つの開近傍の共通部分を取る。
差を `(f y - f x) + (g y - g x)` に並べ替え（`ac_rfl`）、三角不等式と `add_halves`。 -/
theorem continuous_add {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) :=
  sorry

theorem continuous_neg {f : X → R} (hf : Continuous f) : Continuous (fun x => -f x) := by
  apply continuous_of_forall
  intro x ε hε
  obtain ⟨U, hU, hxU, hfU⟩ := forall_of_continuous hf x hε
  refine ⟨U, hU, hxU, fun y hy => ?_⟩
  have e : -f y - -f x = -(f y - f x) := by rw [sub_def, sub_def, neg_add]
  rw [e, abs_neg]; exact hfU y hy

theorem continuous_sub {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) := continuous_add hf (continuous_neg hg)

/-- 問題25: （発展）連続関数の積は連続であることを示せ。

ヒント: `f y * g y - f x * g x = f y * (g y - g x) + g x * (f y - f x)` と分ける。
`f` の近傍では値の差を 1 未満にも抑えて `|f y| ≤ |f x| + 1` とし、
各項が `ε / 2` 未満になるよう、`g` の差を `ε / 2 / (|f x| + 1)` 未満、`f` の差を `ε / 2 / (|g x| + 1)` 未満に取る。 -/
theorem continuous_mul {f g : X → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) :=
  sorry

end Continuity

/-! ## Part G: 閉区間

閉区間 `[a, b]` について、3 つの定理を示す。どれも Part E の上限の議論で証明する。

* **Heine–Borel**（問題27）: 閉区間はコンパクト。`06_Topology.lean` の `IsCompact` が、
  ここで初めて具体的な空間の具体的な集合に対して成り立つ
* **連結性**（問題28）: 閉区間は、交わらない 2 つの開集合に分けられない
* **ルベーグ数の補題**（問題30）: 閉区間を開集合で覆うと、ある `δ > 0` について、
  区間のどの点のまわりの `δ`-近傍も、覆う開集合のどれか 1 つに収まる

3 つの証明は同じ型をしている。「`a` から `x` まで性質が成り立つ」ような `x` の集合の
上限 `c` を取り、`c` の近くの様子を見て、`c` が区間の右端 `b` まで届くことを示す。
-/

/-- 閉区間 `[a, b]`。 -/
def Icc (a b : R) : Set R := {x | a ≤ x ∧ x ≤ b}

/-- 問題26: 有限集合に 1 点を足しても有限であることを示せ。

ヒント: `J` を拾う `f : Fin n → I` に、最後の番号 `n` で `i` を拾うよう 1 つ足す:
`fun k => if h : k.val < n then f ⟨k.val, h⟩ else i`。 -/
theorem finite_insert {I : Type} {J : Set I} (hJ : J.Finite) (i : I) :
    ({j | j ∈ J ∨ j = i} : Set I).Finite :=
  sorry

theorem finite_singleton {I : Type} (i : I) : ({j | j = i} : Set I).Finite :=
  ⟨1, fun _ => i, fun _ hj => ⟨⟨0, Nat.zero_lt_one⟩, hj.symm⟩⟩

/-- 問題27: **Heine–Borel**: 閉区間はコンパクトであることを示せ。

ヒント: `[a, x]` が有限個で覆える `x ∈ [a, b]` の集合の上限を `c` とする。`c` を含む開集合 `U i₁` の
`ε`-近傍と、`c - ε` より大きいその集合の元 `x`（問題18）を取ると、`[a, c + ε/2]` までが
`i₁` を足して覆える（問題26）。`b ≤ c + ε/2` なら終わり、そうでなければ `c + ε/2` が上限を超えて矛盾する。 -/
theorem isCompact_Icc (a b : R) : IsCompact (Icc a b) :=
  sorry

/-- 問題28: **閉区間の連結性**: 閉区間を、互いに交わらない 2 つの開集合で分けることはできないことを示せ。
`a` を含む側が区間全体を含む。

ヒント: 問題27と同じ形。`[a, x] ⊆ U` となる `x` の集合の上限 `c` を取る。まず `c ∈ U` を示す
（`c ∈ V` なら、`c` に近いその集合の元が `U` と `V` の両方に入る）。あとは問題27と同じく `c + ε/2` を見る。 -/
theorem Icc_connected {a b : R} {U V : Set R} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : ∀ x ∈ Icc a b, x ∈ U ∨ x ∈ V) (hdisj : ∀ x ∈ Icc a b, x ∈ U → x ∈ V → False)
    (hab : a ≤ b) (ha : a ∈ U) : ∀ x ∈ Icc a b, x ∈ U :=
  sorry

/-- 有限個の実数の最小値（0 個なら 1）。 -/
noncomputable def finMin : (n : Nat) → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, g => min (g 0) (finMin n fun k => g k.succ)

theorem finMin_pos : ∀ (n : Nat) (g : Fin n → R), (∀ k, 0 < g k) → 0 < finMin n g
  | 0, _, _ => zero_lt_one
  | n + 1, _, h => lt_min (h 0) (finMin_pos n _ fun k => h k.succ)

/-- 問題29: 有限個の数の最小値は、そのどれ以下でもあることを示せ。

ヒント: `n` についての再帰。`k` は `cases k using Fin.cases` で `0` と `succ` に分ける。 -/
theorem finMin_le : ∀ (n : Nat) (g : Fin n → R) (k : Fin n), finMin n g ≤ g k :=
  sorry

/-- 問題30: **ルベーグ数の補題**: 閉区間を覆う開集合族には、ある `δ > 0` があって、区間のどの点のまわりの
`δ`-近傍も、族のどれか 1 つに収まることを示せ。

ヒント: 区間の各点 `p` に、ある `U i` に収まる近傍の半径 `r p` を選び（`Classical.choose`）、
半径 `r p / 2` の近傍で区間を覆う。問題27で有限個に減らし、それらの半径の最小値（`finMin`）を `δ` とする。
最後は三角不等式で `|y - p| < r p` を示す。 -/
theorem lebesgue {a b : R} {I : Type} (U : I → Set R) (hU : ∀ i, IsOpen (U i))
    (hcov : Icc a b ⊆ (⋃ i, U i)) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ Icc a b, ∃ i, ∀ y, abs (y - x) < δ → y ∈ U i :=
  sorry

end CompleteOrderedField

/-! 解答（`08_RealSol.lean`）では、ルベーグ数の補題が依存する公理は
`propext`・`Classical.choice`・`Quot.sound` の 3 つだけである。
実数の公理は `axiom` ではなく `class` の引数なので、ここには現れない。
問題を解き終えたら、次の出力に `sorryAx` が残っていないことを確かめよ。
-/

#print axioms CompleteOrderedField.lebesgue
