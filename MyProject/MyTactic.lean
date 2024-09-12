import Lean

open Lean Meta Elab Tactic

#check Nat.le_step

example : 2 ≤ 6 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

example : 2 ≤ 6 := by
  repeat (first | apply Nat.le_refl | apply Nat.le_step)

macro "nat_le" : tactic =>
  `(tactic | repeat (first | apply Nat.le_refl | apply Nat.le_step))

example : 10 ≤ 20 := by
  nat_le

macro "repeat_apply" t₁:term "then" t₂:term : tactic =>
do
  `(tactic| repeat (first | apply $t₂ | apply $t₁))

example : 1 ≤ 14 := by
  repeat_apply Nat.le_step then Nat.le_refl

example : 12 ≤ 26 := by
  repeat_apply Nat.succ_le_succ then Nat.zero_le

#check Expr.eq?
#check Expr.app2?
#check Nat.le

#print Syntax

#print Expr

def matchLe (e : Expr) :
  MetaM <| Option (Expr × Expr) := do
  let nat := mkConst ``Nat
  let a ← mkFreshExprMVar nat
  let b ← mkFreshExprMVar nat
  let ineq ← mkAppM ``Nat.le #[a, b]
  if ← isDefEq ineq e then
    return some (a, b)
  else
    return none

elab "match_le" : tactic => do
  match ← matchLe (← getMainTarget) with
  | some (a, b) => logInfo m!"Matched inequality; a = {a}, b = {b}"
  | none => logWarning m!"Main target not of the correct form"

example (x y : Nat) (h : x ≤ y) : x ≤ y := by
  match_le
  assumption

elab "match_le_hyp" t:term : tactic => do
  let h ← elabTerm t none
  match ← matchLe (← inferType h) with
  | some (a, b) => logInfo m!"Matched inequality; a = {a}, b = {b}"
  | none => logWarning m!"Main target not of the correct form"

example (x y : Nat) (h : x ≤ y) : x ≤ y := by
  match_le_hyp h
  assumption

elab "rw_le" t:term : tactic =>
  withMainContext do
    let h ← elabTerm t none
    let hType ← inferType h
    let target ← getMainTarget
    match ← matchLe hType, ← matchLe target with
    | some (a, b), some (c, d) =>
      let firstEq ← isDefEq a c
      let secondEq ← isDefEq b d
      if firstEq && secondEq then
        closeMainGoal `rw_le h
      else
      if firstEq then
        let newTarget ← mkAppM ``Nat.le #[b, d]
        let newGoal ← mkFreshExprMVar newTarget
        let proof ← mkAppM ``Nat.le_trans #[h, newGoal]
        let goal ← getMainGoal
        goal.assign proof
        replaceMainGoal [newGoal.mvarId!]
      else
      if secondEq then
        let newTarget ← mkAppM ``Nat.le #[c, a]
        let newGoal ← mkFreshExprMVar newTarget
        let proof ← mkAppM ``Nat.le_trans #[newGoal, h]
        let goal ← getMainGoal
        goal.assign proof
        replaceMainGoal [newGoal.mvarId!]
      else
        throwError "Neither ends matched"
    | _, _ =>
      throwError "Did not get inequalities"

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw_le h₁
  exact h₂

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw_le h₂
  exact h₁
