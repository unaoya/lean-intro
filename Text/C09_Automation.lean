-- Text/C09_Automation.lean — Ch9 自動化と自作タクティク（simp・omega・my_ring）
-- まずバニラ（simp/omega/ac_rfl）を押さえ、その上で自分の公理から「proof by
-- reflection」で自作タクティクを作る: my_abel（加法可換群）→ my_ring（可換環）。
-- mathlib の ring/abel/linarith は無い（unknown tactic）ので、すべて自作する。
-- 反射の健全性は **任意の AddCommGroup/CommRing 上**で証明する（Real 固定でない）。
-- ゆえに my_abel/my_ring は Real に限らずどの可換群/可換環の等式でも閉じる。
import Lean
import Text.C08_Rewrite

-- ============================================================
-- §1 simp — hand-proved 補題を渡して派生恒等式を畳む（既定セットは汚さない）
-- ============================================================

-- ANCHOR: simp_demo
example (a b : Real) : (a + b) + -b = a := by
  simp only [add_assoc, add_neg', add_zero']
example (a : Real) : -(-a) + 0 = a := by simp only [neg_neg, add_zero']
-- ANCHOR_END: simp_demo

-- ============================================================
-- §2 omega — Nat の線形算術（添字計算）の決定手続き
-- ============================================================

-- ANCHOR: omega_demo
example (n : Nat) : n + 1 - 1 = n := by omega
example (a b : Nat) : a + b + 0 = b + a := by omega
-- ANCHOR_END: omega_demo

-- ============================================================
-- §3 ac_rfl — 結合・可換を Std インスタンスとして「道具に教える」
--    純 AC（逆元なし）の並べ替えを吸収する。相殺は扱えない（→ §5 の反射へ）。
-- ============================================================

instance : Std.Associative (· + · : Real → Real → Real) := ⟨add_assoc⟩
instance : Std.Commutative (· + · : Real → Real → Real) := ⟨add_comm⟩

-- ANCHOR: ac_demo
example (a b c d : Real) : (a + b) + (c + d) = (a + c) + (b + d) := by ac_rfl
-- ANCHOR_END: ac_demo

-- ============================================================
-- §3.5 抽象代数補題（反射の健全性が依存する公理の帰結）
--    Real ではなく **任意の AddCommGroup/CommRing** 上で一度だけ証明しておく。
--    これにより反射の健全性も my_abel/my_ring も型多相になる。
--    （Ch7/7 の Real 版補題はそのまま・ここは抽象版を別名で並置する。）
-- ============================================================

namespace AbstractAlg

variable {α : Type}

section Group
variable [AddCommGroup α]

-- 左簡約（C06 の add_left_cancel' の抽象版）
theorem add_left_cancel (a : α) {b c : α} (h : a + b = a + c) : b = c :=
  calc b = AddCommMonoid.zero + b := (AddCommMonoid.zero_add b).symm
    _ = (-a + a) + b := by rw [AddCommGroup.neg_add]
    _ = -a + (a + b) := AddCommMonoid.add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (AddCommMonoid.add_assoc _ _ _).symm
    _ = AddCommMonoid.zero + c := by rw [AddCommGroup.neg_add]
    _ = c := AddCommMonoid.zero_add c

-- 加える相手が同じ零和なら逆元（一意性）
theorem neg_eq_of_add_eq_zero {a b : α} (h : a + b = AddCommMonoid.zero) : -a = b :=
  add_left_cancel a (by rw [AddCommGroup.add_neg, h])

theorem neg_neg (a : α) : - -a = a :=
  neg_eq_of_add_eq_zero (by rw [AddCommGroup.neg_add])

theorem neg_zero : -(AddCommMonoid.zero : α) = AddCommMonoid.zero :=
  neg_eq_of_add_eq_zero (AddCommMonoid.add_zero _)

theorem neg_add_distrib (a b : α) : -(a + b) = -a + -b :=
  neg_eq_of_add_eq_zero
    (calc (a + b) + (-a + -b)
        = a + (b + (-a + -b)) := AddCommMonoid.add_assoc a b _
      _ = a + (b + (-b + -a)) := by rw [AddCommMonoid.add_comm (-a) (-b)]
      _ = a + ((b + -b) + -a) := by rw [AddCommMonoid.add_assoc b (-b) (-a)]
      _ = a + (AddCommMonoid.zero + -a) := by rw [AddCommGroup.add_neg]
      _ = a + -a := by rw [AddCommMonoid.zero_add]
      _ = AddCommMonoid.zero := AddCommGroup.add_neg a)

end Group

section Ring
variable [CommRing α]

theorem mul_zero (a : α) : a * AddCommMonoid.zero = AddCommMonoid.zero :=
  add_left_cancel (a * AddCommMonoid.zero)
    (by rw [← CommRing.left_distrib, AddCommMonoid.add_zero, AddCommMonoid.add_zero])

theorem zero_mul (a : α) : AddCommMonoid.zero * a = AddCommMonoid.zero :=
  add_left_cancel (AddCommMonoid.zero * a)
    (by rw [← CommRing.right_distrib, AddCommMonoid.add_zero, AddCommMonoid.add_zero])

theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  (neg_eq_of_add_eq_zero
    (by rw [← CommRing.right_distrib, AddCommGroup.add_neg, zero_mul])).symm

theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  (neg_eq_of_add_eq_zero
    (by rw [← CommRing.left_distrib, AddCommGroup.add_neg, mul_zero])).symm

end Ring

end AbstractAlg

-- ============================================================
-- §4 反射の発想（proof by reflection）
--    simp/ac_rfl は「並べ替え＋相殺」（a + b - a = b 型）を閉じられない。
--    そこで式を構文（Expr）として写し取り、決定可能な正規形に潰して比較する。
--    まず加法群（§5 my_abel）、次に環（§6 my_ring）へ拡張する。
-- ============================================================

namespace MyAbel

-- 構文（原子は Nat で番号付け）・型に依存しない純データ
inductive Expr where
  | atom : Nat → Expr
  | zero : Expr
  | add  : Expr → Expr → Expr
  | neg  : Expr → Expr
  | sub  : Expr → Expr → Expr

variable {α : Type} [AddCommGroup α]

-- 評価（原子割当 ρ のもとで α へ）
noncomputable def Expr.eval (ρ : Nat → α) : Expr → α
  | .atom i => ρ i
  | .zero   => AddCommMonoid.zero
  | .add a b => a.eval ρ + b.eval ρ
  | .neg a   => -(a.eval ρ)
  | .sub a b => a.eval ρ + -(b.eval ρ)

-- 符号付き原子（true=正・false=負）の評価
noncomputable def sval (ρ : Nat → α) (p : Nat × Bool) : α :=
  if p.2 then ρ p.1 else -(ρ p.1)

-- 正規形リストの評価
noncomputable def nfEval (ρ : Nat → α) : List (Nat × Bool) → α
  | [] => AddCommMonoid.zero
  | p :: t => sval ρ p + nfEval ρ t

-- 整列挿入（同原子・逆符号なら相殺）— 計算可能（List(Nat×Bool) のみ）
def ins (p : Nat × Bool) : List (Nat × Bool) → List (Nat × Bool)
  | [] => [p]
  | q :: t =>
    if p.1 < q.1 then p :: q :: t
    else if p.1 = q.1 ∧ p.2 ≠ q.2 then t
    else q :: ins p t

def canon (l : List (Nat × Bool)) : List (Nat × Bool) := l.foldr ins []

def flat : Expr → List (Nat × Bool)
  | .atom i => [(i, true)]
  | .zero   => []
  | .add a b => flat a ++ flat b
  | .neg a   => (flat a).map (fun p => (p.1, !p.2))
  | .sub a b => flat a ++ (flat b).map (fun p => (p.1, !p.2))

def normalize (e : Expr) : List (Nat × Bool) := canon (flat e)

-- ===== 健全性（任意の AddCommGroup 上）=====

theorem nfEval_append (ρ : Nat → α) (l1 l2 : List (Nat × Bool)) :
    nfEval ρ (l1 ++ l2) = nfEval ρ l1 + nfEval ρ l2 := by
  induction l1 with
  | nil => exact (AddCommMonoid.zero_add _).symm
  | cons p t ih =>
    show sval ρ p + nfEval ρ (t ++ l2) = (sval ρ p + nfEval ρ t) + nfEval ρ l2
    rw [ih, AddCommMonoid.add_assoc]

theorem sval_flip (ρ : Nat → α) (p : Nat × Bool) :
    sval ρ (p.1, !p.2) = -(sval ρ p) := by
  obtain ⟨i, b⟩ := p
  cases b with
  | true  => rfl
  | false => exact (AbstractAlg.neg_neg (ρ i)).symm

theorem nfEval_map_flip (ρ : Nat → α) (l : List (Nat × Bool)) :
    nfEval ρ (l.map (fun p => (p.1, !p.2))) = -(nfEval ρ l) := by
  induction l with
  | nil => exact AbstractAlg.neg_zero.symm
  | cons p t ih =>
    show sval ρ (p.1, !p.2) + nfEval ρ (t.map _) = -(sval ρ p + nfEval ρ t)
    rw [ih, AbstractAlg.neg_add_distrib, sval_flip]

theorem nfEval_ins (ρ : Nat → α) (p : Nat × Bool) (l : List (Nat × Bool)) :
    nfEval ρ (ins p l) = sval ρ p + nfEval ρ l := by
  induction l with
  | nil => rfl
  | cons q t ih =>
    unfold ins
    by_cases h1 : p.1 < q.1
    · simp only [if_pos h1]; rfl
    · by_cases h2 : p.1 = q.1 ∧ p.2 ≠ q.2
      · simp only [if_neg h1, if_pos h2]
        show nfEval ρ t = sval ρ p + (sval ρ q + nfEval ρ t)
        have hpq : sval ρ p + sval ρ q = AddCommMonoid.zero := by
          have hb : p.2 ≠ q.2 := h2.2
          unfold sval
          rw [h2.1]
          revert hb
          cases p.2 <;> cases q.2 <;> intro hb <;>
            first
            | exact absurd rfl hb
            | exact AddCommGroup.neg_add _
            | exact AddCommGroup.add_neg _
        rw [← AddCommMonoid.add_assoc, hpq, AddCommMonoid.zero_add]
      · simp only [if_neg h1, if_neg h2]
        show sval ρ q + nfEval ρ (ins p t) = sval ρ p + (sval ρ q + nfEval ρ t)
        rw [ih, ← AddCommMonoid.add_assoc, ← AddCommMonoid.add_assoc,
          AddCommMonoid.add_comm (sval ρ q) (sval ρ p)]

theorem nfEval_canon (ρ : Nat → α) (l : List (Nat × Bool)) :
    nfEval ρ (canon l) = nfEval ρ l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    show nfEval ρ (ins p (canon t)) = sval ρ p + nfEval ρ t
    rw [nfEval_ins, ih]

theorem eval_normalize (ρ : Nat → α) (e : Expr) :
    e.eval ρ = nfEval ρ (normalize e) := by
  unfold normalize
  rw [nfEval_canon]
  induction e with
  | atom i => exact (AddCommMonoid.add_zero (ρ i)).symm
  | zero => rfl
  | add a b iha ihb =>
    show a.eval ρ + b.eval ρ = nfEval ρ (flat a ++ flat b)
    rw [nfEval_append, iha, ihb]
  | neg a iha =>
    show -(a.eval ρ) = nfEval ρ ((flat a).map (fun p => (p.1, !p.2)))
    rw [nfEval_map_flip, iha]
  | sub a b iha ihb =>
    show a.eval ρ + -(b.eval ρ) = nfEval ρ (flat a ++ (flat b).map (fun p => (p.1, !p.2)))
    rw [nfEval_append, nfEval_map_flip, iha, ihb]

theorem of_normalize_eq (ρ : Nat → α) (a b : Expr)
    (h : normalize a = normalize b) : a.eval ρ = b.eval ρ := by
  rw [eval_normalize ρ a, eval_normalize ρ b, h]

end MyAbel

-- ===== メタ: 目標 L = R を Expr に反射して my_abel が閉じる =====
open Lean Lean.Meta in
partial def reifyAbel (zeroExpr : Expr) (atomsRef : IO.Ref (Array Expr)) :
    Expr → MetaM Expr := fun e => do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``MyAbel.Expr.add)
        (← reifyAbel zeroExpr atomsRef a) (← reifyAbel zeroExpr atomsRef b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``MyAbel.Expr.sub)
        (← reifyAbel zeroExpr atomsRef a) (← reifyAbel zeroExpr atomsRef b)
  | (``Neg.neg, #[_, _, a]) =>
      return mkApp (mkConst ``MyAbel.Expr.neg) (← reifyAbel zeroExpr atomsRef a)
  | _ =>
      if ← isDefEq e zeroExpr then
        return mkConst ``MyAbel.Expr.zero
      else
        let atoms ← atomsRef.get
        let mut idx : Option Nat := none
        for i in [0:atoms.size] do
          if ← isDefEq atoms[i]! e then
            idx := some i
            break
        match idx with
        | some i => return mkApp (mkConst ``MyAbel.Expr.atom) (mkNatLit i)
        | none =>
            atomsRef.modify (·.push e)
            return mkApp (mkConst ``MyAbel.Expr.atom) (mkNatLit atoms.size)

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic in
elab "my_abel" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← goal.getType
    let some (α, lhs, rhs) := ty.eq? | throwError "my_abel: 目標が等式でない"
    -- 目標の型 α から AddCommGroup α インスタンスを取り、零を構成する
    let inst ← synthInstance (← mkAppM ``AddCommMonoid #[α])
    let zeroExpr ← mkAppOptM ``AddCommMonoid.zero #[some α, some inst]
    let atomsRef ← IO.mkRef (#[] : Array Expr)
    let eL ← reifyAbel zeroExpr atomsRef lhs
    let eR ← reifyAbel zeroExpr atomsRef rhs
    let atoms ← atomsRef.get
    let listExpr ← mkListLit α atoms.toList
    let rho := mkLambda `i BinderInfo.default (mkConst ``Nat)
      (mkAppN (mkConst ``List.getD [Level.zero]) #[α, listExpr, mkBVar 0, zeroExpr])
    let nL ← mkAppM ``MyAbel.normalize #[eL]
    let nR ← mkAppM ``MyAbel.normalize #[eR]
    let normPf ← mkDecideProof (← mkEq nL nR)
    let pf ← mkAppM ``MyAbel.of_normalize_eq #[rho, eL, eR, normPf]
    goal.assign pf

-- ANCHOR: my_abel_demo
-- simp/ac_rfl が閉じられなかった「並べ替え＋相殺」が一行で閉じる
example (a b : Real) : a + b - a = b := by my_abel
example (a b c : Real) : b + -a = (c + -a) + (b + -c) := by my_abel
-- ANCHOR_END: my_abel_demo

-- ============================================================
-- §6 環への拡張: 原子 → 単項式（積）。正規形＝符号付き単項式のリスト。
--    crossMul（分配律）で積を展開する。my_abel を包含する。
-- ============================================================

namespace MyRing

inductive Expr where
  | atom : Nat → Expr
  | zero : Expr
  | one  : Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | neg  : Expr → Expr
  | sub  : Expr → Expr → Expr

variable {α : Type} [CommRing α]

noncomputable def Expr.eval (ρ : Nat → α) : Expr → α
  | .atom i => ρ i
  | .zero   => AddCommMonoid.zero
  | .one    => MulCommMonoid.one
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .neg a   => -(a.eval ρ)
  | .sub a b => a.eval ρ + -(b.eval ρ)

-- 符号の付与（match なので defeq で簡約される）
noncomputable def applySign : Bool → α → α
  | true,  x => x
  | false, x => -x

-- 符号の積（XNOR: 一致なら +）
def xnorB : Bool → Bool → Bool
  | true,  b => b
  | false, b => !b

-- 単項式（原子の積）の評価
noncomputable def monEval (ρ : Nat → α) : List Nat → α
  | [] => MulCommMonoid.one
  | i :: t => ρ i * monEval ρ t

noncomputable def entEval (ρ : Nat → α) (e : List Nat × Bool) : α :=
  applySign e.2 (monEval ρ e.1)

noncomputable def nfEval (ρ : Nat → α) : List (List Nat × Bool) → α
  | [] => AddCommMonoid.zero
  | e :: t => entEval ρ e + nfEval ρ t

-- 原子の整列挿入（単項式内）
def insAtom (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: t => if i ≤ j then i :: j :: t else j :: insAtom i t

def mulMon (m1 m2 : List Nat) : List Nat := m1.foldr insAtom m2

def monLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else monLt as bs

def entMul (e1 e2 : List Nat × Bool) : List Nat × Bool :=
  (mulMon e1.1 e2.1, xnorB e1.2 e2.2)

def insEntry (p : List Nat × Bool) : List (List Nat × Bool) → List (List Nat × Bool)
  | [] => [p]
  | q :: t =>
    if p.1 = q.1 ∧ p.2 ≠ q.2 then t
    else if monLt p.1 q.1 then p :: q :: t
    else q :: insEntry p t

def canon (l : List (List Nat × Bool)) : List (List Nat × Bool) := l.foldr insEntry []

def crossMul (l1 l2 : List (List Nat × Bool)) : List (List Nat × Bool) :=
  l1.flatMap (fun e1 => l2.map (fun e2 => entMul e1 e2))

def flat : Expr → List (List Nat × Bool)
  | .atom i => [([i], true)]
  | .zero   => []
  | .one    => [([], true)]
  | .add a b => flat a ++ flat b
  | .mul a b => crossMul (flat a) (flat b)
  | .neg a   => (flat a).map (fun e => (e.1, !e.2))
  | .sub a b => flat a ++ (flat b).map (fun e => (e.1, !e.2))

def normalize (e : Expr) : List (List Nat × Bool) := canon (flat e)

-- ===== 健全性（任意の CommRing 上）=====

theorem applySign_mul (s1 s2 : Bool) (x y : α) :
    applySign (xnorB s1 s2) (x * y) = applySign s1 x * applySign s2 y := by
  cases s1 <;> cases s2
  · exact (show (-x) * (-y) = x * y by
      rw [AbstractAlg.neg_mul, AbstractAlg.mul_neg, AbstractAlg.neg_neg]).symm
  · exact (AbstractAlg.neg_mul x y).symm
  · exact (AbstractAlg.mul_neg x y).symm
  · rfl

theorem monEval_insAtom (ρ : Nat → α) (i : Nat) (m : List Nat) :
    monEval ρ (insAtom i m) = ρ i * monEval ρ m := by
  induction m with
  | nil => rfl
  | cons j t ih =>
    unfold insAtom
    by_cases h : i ≤ j
    · simp only [if_pos h]; rfl
    · simp only [if_neg h]
      show ρ j * monEval ρ (insAtom i t) = ρ i * (ρ j * monEval ρ t)
      rw [ih, ← MulCommMonoid.mul_assoc, ← MulCommMonoid.mul_assoc,
        MulCommMonoid.mul_comm (ρ j) (ρ i)]

theorem monEval_mulMon (ρ : Nat → α) (m1 m2 : List Nat) :
    monEval ρ (mulMon m1 m2) = monEval ρ m1 * monEval ρ m2 := by
  induction m1 with
  | nil => exact (MulCommMonoid.one_mul _).symm
  | cons i t ih =>
    show monEval ρ (insAtom i (mulMon t m2)) = (ρ i * monEval ρ t) * monEval ρ m2
    rw [monEval_insAtom, ih, MulCommMonoid.mul_assoc]

theorem entEval_entMul (ρ : Nat → α) (e1 e2 : List Nat × Bool) :
    entEval ρ (entMul e1 e2) = entEval ρ e1 * entEval ρ e2 := by
  show applySign (xnorB e1.2 e2.2) (monEval ρ (mulMon e1.1 e2.1))
     = applySign e1.2 (monEval ρ e1.1) * applySign e2.2 (monEval ρ e2.1)
  rw [monEval_mulMon, applySign_mul]

theorem nfEval_append (ρ : Nat → α) (l1 l2 : List (List Nat × Bool)) :
    nfEval ρ (l1 ++ l2) = nfEval ρ l1 + nfEval ρ l2 := by
  induction l1 with
  | nil => exact (AddCommMonoid.zero_add _).symm
  | cons e t ih =>
    show entEval ρ e + nfEval ρ (t ++ l2) = (entEval ρ e + nfEval ρ t) + nfEval ρ l2
    rw [ih, AddCommMonoid.add_assoc]

theorem entEval_flip (ρ : Nat → α) (e : List Nat × Bool) :
    entEval ρ (e.1, !e.2) = -(entEval ρ e) := by
  show applySign (!e.2) (monEval ρ e.1) = -(applySign e.2 (monEval ρ e.1))
  cases e.2
  · exact (AbstractAlg.neg_neg _).symm
  · rfl

theorem nfEval_map_flip (ρ : Nat → α) (l : List (List Nat × Bool)) :
    nfEval ρ (l.map (fun e => (e.1, !e.2))) = -(nfEval ρ l) := by
  induction l with
  | nil => exact AbstractAlg.neg_zero.symm
  | cons e t ih =>
    show entEval ρ (e.1, !e.2) + nfEval ρ (t.map _) = -(entEval ρ e + nfEval ρ t)
    rw [ih, AbstractAlg.neg_add_distrib, entEval_flip]

theorem nfEval_distrib (ρ : Nat → α) (e1 : List Nat × Bool) (l : List (List Nat × Bool)) :
    nfEval ρ (l.map (fun e2 => entMul e1 e2)) = entEval ρ e1 * nfEval ρ l := by
  induction l with
  | nil => exact (AbstractAlg.mul_zero _).symm
  | cons e t ih =>
    show entEval ρ (entMul e1 e) + nfEval ρ (t.map _) = entEval ρ e1 * (entEval ρ e + nfEval ρ t)
    rw [ih, entEval_entMul, CommRing.left_distrib]

theorem nfEval_crossMul (ρ : Nat → α) (l1 l2 : List (List Nat × Bool)) :
    nfEval ρ (crossMul l1 l2) = nfEval ρ l1 * nfEval ρ l2 := by
  induction l1 with
  | nil => exact (AbstractAlg.zero_mul _).symm
  | cons e t ih =>
    show nfEval ρ (l2.map (fun e2 => entMul e e2) ++ crossMul t l2)
        = (entEval ρ e + nfEval ρ t) * nfEval ρ l2
    rw [nfEval_append, nfEval_distrib, ih, CommRing.right_distrib]

theorem nfEval_insEntry (ρ : Nat → α) (p : List Nat × Bool) (l : List (List Nat × Bool)) :
    nfEval ρ (insEntry p l) = entEval ρ p + nfEval ρ l := by
  induction l with
  | nil => rfl
  | cons q t ih =>
    unfold insEntry
    by_cases hc : p.1 = q.1 ∧ p.2 ≠ q.2
    · simp only [if_pos hc]
      show nfEval ρ t = entEval ρ p + (entEval ρ q + nfEval ρ t)
      have hpq : entEval ρ p + entEval ρ q = AddCommMonoid.zero := by
        have hb : p.2 ≠ q.2 := hc.2
        show applySign p.2 (monEval ρ p.1) + applySign q.2 (monEval ρ q.1) = AddCommMonoid.zero
        rw [hc.1]
        revert hb
        cases p.2 <;> cases q.2 <;> intro hb <;>
          first
          | exact absurd rfl hb
          | exact AddCommGroup.neg_add _
          | exact AddCommGroup.add_neg _
      rw [← AddCommMonoid.add_assoc, hpq, AddCommMonoid.zero_add]
    · simp only [if_neg hc]
      by_cases ho : monLt p.1 q.1 = true
      · simp only [ho, if_true]; rfl
      · simp only [ho]
        show entEval ρ q + nfEval ρ (insEntry p t) = entEval ρ p + (entEval ρ q + nfEval ρ t)
        rw [ih, ← AddCommMonoid.add_assoc, ← AddCommMonoid.add_assoc,
          AddCommMonoid.add_comm (entEval ρ q) (entEval ρ p)]

theorem nfEval_canon (ρ : Nat → α) (l : List (List Nat × Bool)) :
    nfEval ρ (canon l) = nfEval ρ l := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    show nfEval ρ (insEntry e (canon t)) = entEval ρ e + nfEval ρ t
    rw [nfEval_insEntry, ih]

theorem eval_flat (ρ : Nat → α) (e : Expr) : e.eval ρ = nfEval ρ (flat e) := by
  induction e with
  | atom i =>
    show ρ i = ρ i * MulCommMonoid.one + AddCommMonoid.zero
    rw [MulCommMonoid.mul_one, AddCommMonoid.add_zero]
  | zero => rfl
  | one =>
    show MulCommMonoid.one = MulCommMonoid.one + AddCommMonoid.zero
    rw [AddCommMonoid.add_zero]
  | add a b iha ihb =>
    show a.eval ρ + b.eval ρ = nfEval ρ (flat a ++ flat b)
    rw [nfEval_append, iha, ihb]
  | mul a b iha ihb =>
    show a.eval ρ * b.eval ρ = nfEval ρ (crossMul (flat a) (flat b))
    rw [nfEval_crossMul, iha, ihb]
  | neg a iha =>
    show -(a.eval ρ) = nfEval ρ ((flat a).map (fun e => (e.1, !e.2)))
    rw [nfEval_map_flip, iha]
  | sub a b iha ihb =>
    show a.eval ρ + -(b.eval ρ) = nfEval ρ (flat a ++ (flat b).map (fun e => (e.1, !e.2)))
    rw [nfEval_append, nfEval_map_flip, iha, ihb]

theorem eval_normalize (ρ : Nat → α) (e : Expr) :
    e.eval ρ = nfEval ρ (normalize e) := by
  unfold normalize; rw [nfEval_canon, eval_flat]

theorem of_normalize_eq (ρ : Nat → α) (a b : Expr)
    (h : normalize a = normalize b) : a.eval ρ = b.eval ρ := by
  rw [eval_normalize ρ a, eval_normalize ρ b, h]

end MyRing

-- ===== メタ: my_ring =====
open Lean Lean.Meta in
partial def reifyRing (oneExpr zeroExpr : Expr) (atomsRef : IO.Ref (Array Expr)) :
    Expr → MetaM Expr := fun e => do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``MyRing.Expr.add)
        (← reifyRing oneExpr zeroExpr atomsRef a) (← reifyRing oneExpr zeroExpr atomsRef b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``MyRing.Expr.mul)
        (← reifyRing oneExpr zeroExpr atomsRef a) (← reifyRing oneExpr zeroExpr atomsRef b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``MyRing.Expr.sub)
        (← reifyRing oneExpr zeroExpr atomsRef a) (← reifyRing oneExpr zeroExpr atomsRef b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      -- a / b = a * (b⁻¹)。b⁻¹ は積の原子として扱う（純 ring の除法を my_ring が閉じる）
      let invB ← mkAppM ``Field.inv #[b]
      return mkApp2 (mkConst ``MyRing.Expr.mul)
        (← reifyRing oneExpr zeroExpr atomsRef a) (← reifyRing oneExpr zeroExpr atomsRef invB)
  | (``Neg.neg, #[_, _, a]) =>
      return mkApp (mkConst ``MyRing.Expr.neg) (← reifyRing oneExpr zeroExpr atomsRef a)
  | _ =>
      if ← isDefEq e zeroExpr then return mkConst ``MyRing.Expr.zero
      else if ← isDefEq e oneExpr then return mkConst ``MyRing.Expr.one
      else
        let atoms ← atomsRef.get
        let mut idx : Option Nat := none
        for i in [0:atoms.size] do
          if ← isDefEq atoms[i]! e then idx := some i; break
        match idx with
        | some i => return mkApp (mkConst ``MyRing.Expr.atom) (mkNatLit i)
        | none =>
            atomsRef.modify (·.push e)
            return mkApp (mkConst ``MyRing.Expr.atom) (mkNatLit atoms.size)

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic in
elab "my_ring" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← goal.getType
    let some (α, lhs, rhs) := ty.eq? | throwError "my_ring: 目標が等式でない"
    -- 目標の型 α から零・単位元を構成する（CommRing α が要る）
    let acmInst ← synthInstance (← mkAppM ``AddCommMonoid #[α])
    let mcmInst ← synthInstance (← mkAppM ``MulCommMonoid #[α])
    let zeroExpr ← mkAppOptM ``AddCommMonoid.zero #[some α, some acmInst]
    let oneExpr  ← mkAppOptM ``MulCommMonoid.one #[some α, some mcmInst]
    let atomsRef ← IO.mkRef (#[] : Array Expr)
    let eL ← reifyRing oneExpr zeroExpr atomsRef lhs
    let eR ← reifyRing oneExpr zeroExpr atomsRef rhs
    let atoms ← atomsRef.get
    let listExpr ← mkListLit α atoms.toList
    let rho := mkLambda `i BinderInfo.default (mkConst ``Nat)
      (mkAppN (mkConst ``List.getD [Level.zero]) #[α, listExpr, mkBVar 0, zeroExpr])
    let nL ← mkAppM ``MyRing.normalize #[eL]
    let nR ← mkAppM ``MyRing.normalize #[eR]
    let normPf ← mkDecideProof (← mkEq nL nR)
    let pf ← mkAppM ``MyRing.of_normalize_eq #[rho, eL, eR, normPf]
    goal.assign pf

-- ANCHOR: my_ring_demo
example (a b c : Real) : a * (b + c) = a * b + a * c := by my_ring
example (a b c d : Real) : (a + b) * (c + d) = a*c + a*d + b*c + b*d := by my_ring
example (a b : Real) : a * b - b * a = 0 := by my_ring
example (a b c : Real) : a * (b + c) + -(a * b) = a * c := by my_ring
-- ANCHOR_END: my_ring_demo
