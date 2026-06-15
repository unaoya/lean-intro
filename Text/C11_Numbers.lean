-- Text/C11_Numbers.lean — Ch11 数の体系（リテラル・除法・cast）
-- リテラルの一般機構（Ch3 のエラーの回収）・除法 Div・cast 補題（構成的な部分のみ・
-- cast は射）。これが y=x 計算（Ch12）の土台。sup を使う archimedean 系は第 II 部へ。
import Text.C10_Induction

noncomputable section

open Range

-- ============================================================
-- §1 リテラルの一般機構と除法
-- ============================================================

-- 自然数の埋め込み（構造的再帰）
-- ANCHOR: of_nat
noncomputable def Real.ofNat : Nat → Real
  | 0 => 0
  | n + 1 => Real.ofNat n + 1
-- ANCHOR_END: of_nat

-- リテラル 2 以上（Ch3 の failed to synthesize がここで消える）
noncomputable instance (n : Nat) : OfNat Real (n + 2) := ⟨Real.ofNat (n + 2)⟩

-- 変数の埋め込み ↑n（リテラル用 OfNat との対比）
noncomputable instance : NatCast Real := ⟨Real.ofNat⟩

-- 除法の記法（等分割の分点式のため）
noncomputable instance : Div Real := ⟨fun a b => a * Field.inv b⟩

-- defeq の観察: 「数の 2 つの建て方」の分かれ目。
-- cast は代数の 0 と 1 から建てた（代数一次）。重なる点の等式の「強さ」が違う:
-- cast 0 = 0 は構成により rfl（defeq）、cast 1 = 1 は命題的（証明が要る）。
-- もし全リテラルを cast で配線したら (1 : Real) の中身は 0 + 1 になり、
-- 公理には計算が無いので 1 と defeq にならない——rfl 証明が死ぬ（Ch7 の 2 種の等しさ）。
-- これが mathlib の Nat.AtLeastTwo（リテラル 0/1/2 以上の担当の排他分割）の理由
-- ANCHOR: cast_defeq
example : Real.ofNat 0 = 0 := rfl        -- defeq（構成どおり）
example : Real.ofNat 1 = 0 + 1 := rfl    -- 中身は 0 + 1
#check_failure (rfl : Real.ofNat 1 = 1)  -- 0 + 1 と 1 は defeq でない（公理に計算は無い）
theorem cast_one : ((1 : Nat) : Real) = 1 := zero_add' 1  -- 命題的にはもちろん等しい
-- ANCHOR_END: cast_defeq

-- ============================================================
-- ダイヤモンド事件: 「2 つ目の値を正準にすると事故」（class 深い機構の悪い例）
--   リテラルの担当を 0/1/2 以上で排他分割する理由——同じ型に 2 つインスタンスを
--   登録すると機構は黙って 1 つを選び、事故は静かに起きる。Ch2 の「class＝自動で
--   見つかる構造」の影の側面。本物の NatCast ダイヤモンドの語りは原稿側。
-- ============================================================

-- ANCHOR: diamond
namespace DiamondIncident

class Price (α : Type) where
  value : α → Nat

structure Coin where
  v : Nat

instance viaFace : Price Coin := ⟨fun c => c.v⟩
instance viaDouble : Price Coin := ⟨fun c => c.v + c.v⟩

-- どちらが選ばれているか？ 機構は後者（viaDouble）を黙って選ぶ
example : Price.value (⟨3⟩ : Coin) = 6 := rfl

end DiamondIncident
-- ANCHOR_END: diamond

-- ============================================================
-- §2 除法の補題（中点・半分・等分の計算部品）
-- ============================================================

theorem zero_div (a : Real) : 0 / a = 0 := by
  show (0 : Real) * Field.inv a = 0; exact zero_mul' _

theorem mul_div_cancel' (a b : Real) (ha : a ≠ (0 : Real)) : a * b / a = b := by
  show a * b * Field.inv a = b
  calc a * b * Field.inv a = b * a * Field.inv a := by rw [mul_comm a b]
    _ = b * (a * Field.inv a) := mul_assoc b a (Field.inv a)
    _ = b * 1 := by rw [show a * Field.inv a = (1 : Real) from Field.mul_inv a ha]
    _ = b := mul_one_b b

theorem div_mul_cancel (a c : Real) (hc : c ≠ (0 : Real)) : a / c * c = a := by
  show a * Field.inv c * c = a
  rw [mul_assoc, show Field.inv c * c = (1 : Real) from Field.inv_mul c hc, mul_one_b]

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by my_ring

theorem div_add_div (a b c : Real) : a / c + b / c = (a + b) / c := by my_ring

-- ============================================================
-- 自作タクティク my_field: 分数を結合し div_eq_iff で分母を払い my_ring で閉じる
--   （inv 相殺＝q·inv q=1 を要する除法恒等式を自動化。非ゼロは仮定/one_one_ne_zero から）
-- ============================================================

theorem mul_div_cancel_right (b c : Real) (hc : c ≠ 0) : b * c / c = b := by
  rw [mul_comm b c]; exact mul_div_cancel' c b hc

theorem div_eq_iff (a b c : Real) (hc : c ≠ 0) : a / c = b ↔ a = b * c := by
  constructor
  · intro h
    have h2 : a / c * c = b * c := by rw [h]
    rwa [div_mul_cancel a c hc] at h2
  · intro h; rw [h]; exact mul_div_cancel_right b c hc

theorem div_mul_eq_mul_div (a b c : Real) : a / c * b = a * b / c := by my_ring

open Lean Lean.Meta in
def findNonzero (oneOne : Expr) (c : Expr) : MetaM (Option Expr) := do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    match (← instantiateMVars decl.type).getAppFnArgs with
    | (``Ne, #[_, x, _]) => if ← isDefEq x c then return some decl.toExpr
    | _ => pure ()
  if ← isDefEq c oneOne then return some (mkConst ``one_one_ne_zero)
  return none

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic in
elab "my_field" : tactic => do
  evalTactic (← `(tactic| try simp only [div_add_div, div_sub_div, div_mul_eq_mul_div]))
  let oneOne ← elabTerm (← `((1 + 1 : Real))) (some (mkConst ``Real))
  let goal ← getMainGoal
  goal.withContext do
    let ty ← goal.getType
    let some (_, lhs, rhs) := ty.eq? | throwError "my_field: 等式でない"
    let clear (g : MVarId) (num den other : Expr) : TacticM Unit := do
      let some hden ← findNonzero oneOne den | throwError "my_field: 分母の非ゼロが不明"
      let iffPf ← mkAppM ``div_eq_iff #[num, other, den, hden]
      let eqProof ← mkAppM ``propext #[iffPf]
      let newTgt ← mkEq num (← mkAppM ``HMul.hMul #[other, den])
      let g2 ← g.replaceTargetEq newTgt eqProof
      replaceMainGoal [g2]
      evalTactic (← `(tactic| my_ring))
    match lhs.getAppFnArgs with
    | (``HDiv.hDiv, #[_,_,_,_, num, den]) => clear goal num den rhs
    | _ => match rhs.getAppFnArgs with
      | (``HDiv.hDiv, #[_,_,_,_, num, den]) =>
          evalTactic (← `(tactic| symm))
          let g ← getMainGoal
          clear g num den lhs
      | _ => evalTactic (← `(tactic| my_ring))


theorem half_add (a : Real) : a / (1 + 1) + a / (1 + 1) = a := by my_field

-- x は (x + x) の半分
theorem double_half (x : Real) : (x + x) / (1 + 1) = x := by my_field

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / (1 + 1) :=
  pos_mul_pos a (Field.inv (1 + 1)) h (pos_inv (1 + 1) zero_lt_one_one)

theorem half_lt {ε : Real} (hε : 0 < ε) : ε / (1 + 1) < ε := by
  have h := add_left_lt (ε / (1 + 1)) 0 (ε / (1 + 1)) (pos_half ε hε)
  rw [add_zero'] at h
  rw [half_add ε] at h
  exact h

theorem pos_div_pos (a b : Real) : 0 < a → 0 < b → 0 < a / b :=
  fun ha hb => pos_mul_pos a (Field.inv b) ha (pos_inv b hb)

theorem nonneg_div_nonneg (a b : Real) : 0 ≤ a → 0 < b → 0 ≤ a / b :=
  fun ha hb => mul_nonneg a (Field.inv b) ha (pos_inv b hb).1

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c :=
  fun hc hab => mul_right_lt a b (Field.inv c) (pos_inv c hc) hab

theorem div_right_le (a b c : Real) : 0 < c → a ≤ b → a / c ≤ b / c :=
  fun hc hab => nonneg_mul_nonneg a b (Field.inv c) (pos_inv c hc).1 hab

-- ============================================================
-- §3 cast 補題（構成的な部分のみ）
-- ============================================================

-- ofNat の定義（| 0 | n+1）により再帰方程式は rfl
theorem succ_ofNat (n : Nat) : Real.ofNat (n + 1) = Real.ofNat n + (1 : Real) := rfl

/-- **順序写像**（順序を保つ写像＝弱単調）。順序集合間の「順序の射」を抽象的に述べる述語。 -/
def Monotone {α β : Type} [LE α] [LE β] (φ : α → β) : Prop := ∀ a b, a ≤ b → φ a ≤ φ b

/-- **cast は順序写像**（順序系の基盤）。`b = a + k` の k について帰納し、各ステップ
`cast m ≤ cast m + 1`（`0 ≤ 1` のみ）で積む。**cast_nonneg を使わず**証明する。 -/
theorem cast_le : Monotone (fun (n : Nat) => (n : Real)) := by
  intro a b h
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  clear h
  show (a : Real) ≤ Real.ofNat (a + k)
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from (Nat.add_assoc a k 1).symm, succ_ofNat]
    exact le_trans ih (le_add_nonneg _ 1 (le_of_lt zero_lt_one))

theorem cast_add (n m : Nat) : (n : Real) + (m : Real) = ((n + m : Nat) : Real) := by
  show Real.ofNat n + Real.ofNat m = Real.ofNat (n + m)
  induction m with
  | zero => rw [Nat.add_zero]; exact add_zero' _
  | succ m ih =>
    have eq2 : n + (m + 1) = (n + m) + 1 := Nat.add_succ n m
    rw [succ_ofNat, eq2, succ_ofNat]
    calc Real.ofNat n + (Real.ofNat m + 1)
      = (Real.ofNat n + Real.ofNat m) + 1 := (add_assoc _ _ _).symm
      _ = Real.ofNat (n + m) + 1 := by rw [ih]

/-- cast は乗法を保つ: `((n*m : Nat) : Real) = (n:Real)*(m:Real)`。 -/
theorem cast_mul (n m : Nat) : ((n * m : Nat) : Real) = (n : Real) * (m : Real) := by
  induction m with
  | zero =>
    rw [Nat.mul_zero, show ((0 : Nat) : Real) = 0 from rfl, mul_zero']
  | succ m ih =>
    rw [Nat.mul_succ, ← cast_add (n * m) n, ih,
        show ((m + 1 : Nat) : Real) = (m : Real) + 1 from by rw [← cast_add m 1, cast_one],
        CommRing.left_distrib, mul_one_b]

-- ============================================================
-- cast は「順序半環の射」: 0・1・+・×・≤ を保つ。
--   nonneg・狭義単調・単射は **射の一般論**から出る——cast 固有は cast_le と +/× だけ。
-- ============================================================

-- ANCHOR: cast_hom
/-- **順序半環の射**: Nat → Real が 0・1・+・×・≤ を保つこと
（≤ の保存＝順序写像 `Monotone`）。Nat と Real を順序半環とみなしたときの準同型。 -/
structure IsOrderedSemiringHom (φ : Nat → Real) : Prop where
  map_zero : φ 0 = 0
  map_one : φ 1 = 1
  map_add : ∀ a b, φ (a + b) = φ a + φ b
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  monotone : Monotone φ

namespace IsOrderedSemiringHom
variable {φ : Nat → Real}

/-- 射は非負: `0 ≤ φ n`（順序写像＋0 を保つ・`0 ≤ n` だから）。 -/
theorem nonneg (h : IsOrderedSemiringHom φ) (n : Nat) : 0 ≤ φ n := by
  rw [← h.map_zero]; exact h.monotone 0 n (Nat.zero_le n)

/-- 射は後者で狭義増加: `φ n < φ (n+1)`（`φ(n+1)=φ n+φ 1=φ n+1 > φ n`・**0<1 のみ**）。 -/
theorem succ_step (h : IsOrderedSemiringHom φ) (n : Nat) : φ n < φ (n + 1) := by
  rw [h.map_add n 1, h.map_one]
  exact lt_add_pos (φ n) 1 zero_lt_one

/-- 射は狭義単調: `a < b → φ a < φ b`（順序写像＋後者増加の離散版）。 -/
theorem strictMono (h : IsOrderedSemiringHom φ) {a b : Nat} (hab : a < b) : φ a < φ b :=
  lt_le_trans (φ a) (φ (a + 1)) (φ b) (h.succ_step a) (h.monotone (a + 1) b hab)

/-- 射は単射（狭義単調の帰結）: `φ a = φ b → a = b`。三分法で a<b・b<a を ≠ で排除。 -/
theorem injective (h : IsOrderedSemiringHom φ) {a b : Nat} (hab : φ a = φ b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hab ((ne_of_gt (h.strictMono hlt)).symm)
  · exact heq
  · exact absurd hab (ne_of_gt (h.strictMono hgt))

/-- **加法を保つ射は有限和と可換**: `φ (Σ f) = Σ (φ ∘ f)`（`map_zero`＋`map_add` だけの帰結・
順序や乗法は不要）。Σ は Nat・Real の両方で `[Add][Zero]` で定義されているので、
**加法準同型が Σ を運ぶ**。「構造の射は構造的演算（有限和）と交換する」という一般論。 -/
theorem map_summation (h : IsOrderedSemiringHom φ) :
    ∀ (n : Nat) (f : Range n → Nat), φ (Summation n f) = Summation n (fun i => φ (f i)) := by
  intro n
  induction n with
  | zero => intro f; exact h.map_zero
  | succ m ih =>
    intro f
    show φ (Summation m (fun k => f (Range.incl k)) + f ⟨m, Nat.lt_succ_self m⟩)
        = Summation m (fun k => φ (f (Range.incl k))) + φ (f ⟨m, Nat.lt_succ_self m⟩)
    rw [h.map_add, ih (fun k => f (Range.incl k))]

end IsOrderedSemiringHom

/-- cast `(· : Real)` は順序半環の射（0/1/+/×/≤ を保つ）。 -/
theorem cast_isHom : IsOrderedSemiringHom (fun (n : Nat) => (n : Real)) :=
  ⟨rfl, cast_one, fun a b => (cast_add a b).symm, fun a b => cast_mul a b, cast_le⟩

-- cast の順序系は「射の一般論」を cast に適用するだけ（cast 固有の証明は不要）
/-- `0 ≤ cast n`（射の非負）。 -/
theorem cast_nonneg (n : Nat) : (0 : Real) ≤ (n : Real) := cast_isHom.nonneg n
/-- `cast n ≤ cast (n+1)`（順序写像に `n ≤ n+1`）。 -/
theorem cast_le_succ (n : Nat) : (n : Real) ≤ ((n + 1 : Nat) : Real) :=
  cast_le n (n + 1) (Nat.le_succ n)
/-- cast は狭義単調: `a < b → cast a < cast b`（射の狭義単調）。 -/
theorem cast_lt (a b : Nat) (h : a < b) : (a : Real) < (b : Real) := cast_isHom.strictMono h
/-- cast は単射（射の単射）。 -/
theorem cast_inj (a b : Nat) (h : (a : Real) = (b : Real)) : a = b := cast_isHom.injective h
/-- `0 < cast (n+1)`（`cast_lt 0 (n+1)`）。 -/
theorem cast_pos_succ (n : Nat) : (0 : Real) < ((n + 1 : Nat) : Real) := by
  have h := cast_lt 0 (n + 1) (Nat.succ_pos n)
  rwa [show ((0 : Nat) : Real) = 0 from rfl] at h
/-- `m ≠ 0 → 0 < cast m`（`cast_lt 0 m`）。 -/
theorem cast_pos_of_ne (m : Nat) (hm : m ≠ 0) : (0 : Real) < (m : Real) := by
  have h := cast_lt 0 m (Nat.pos_of_ne_zero hm)
  rwa [show ((0 : Nat) : Real) = 0 from rfl] at h

/-- cast は Σ と可換: `((Σ f : Nat) : Real) = Σ (cast ∘ f)`——**射が和と交換する一般論**
（`map_summation`）の cast への適用。Σ を Nat で計算してから cast しても、各項を cast して
から Σ しても同じ。 -/
theorem cast_summation (n : Nat) (f : Range n → Nat) :
    ((Summation n f : Nat) : Real) = Summation n (fun i => ((f i : Nat) : Real)) :=
  cast_isHom.map_summation n f
-- ANCHOR_END: cast_hom

-- 章末監査: 古典論理ゼロ（[Real, Real.instLOF] のみ・cast の射性も構成的）
#print axioms cast_mul
