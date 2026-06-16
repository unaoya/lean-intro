-- Text/C09_Order.lean — Ch9 順序と calc（≤/< のスカラー代数）
-- 順序の補題を **Real に固定せず、成り立つ最小の順序クラス**で述べる:
--   ・加法と順序だけ要る補題 → OrderedAddCommMonoid
--   ・符号（neg）も要る補題   → OrderedAddCommGroup
--   ・乗法の非負性が要る補題   → OrderedField
--   ・線形性（le_total）が要る  → LinearOrderedField
-- 自作タクティク（my_abel/my_ring=Ch8・lin=本章）はどれも型多相なので、補題証明を畳む。
-- 注意: `<` は Real の `LT`（≤∧≠）に、`-` は Real の `Sub` に依存するため、それらを使う
-- 補題は Real 専用に置く（順序クラスに lt/sub を積む一般化は将来の課題）。
-- 本章まで古典論理ゼロ（not_lt_imp_le 等の古典補題は第 II 部）。
import Text.C08_Automation

-- ============================================================
-- §1 順序の基本（最小クラス OrderedAddCommMonoid のフィールドを使いやすく包む）
--    冒頭で Real に取り出すのはやめ、最初から型多相の補題として置く。
-- ============================================================

theorem le_refl {α : Type} [OrderedAddCommMonoid α] (a : α) : a ≤ a :=
  OrderedAddCommMonoid.le_refl a
theorem le_trans {α : Type} [OrderedAddCommMonoid α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    a ≤ c := OrderedAddCommMonoid.le_trans a b c h₁ h₂
theorem le_antisymm {α : Type} [OrderedAddCommMonoid α] (a b : α) (h₁ : a ≤ b) (h₂ : b ≤ a) :
    a = b := OrderedAddCommMonoid.le_antisymm a b h₁ h₂
theorem le_total {α : Type} [LinearOrderedField α] (a b : α) : a ≤ b ∨ b ≤ a :=
  LinearOrderedField.le_total a b

-- ============================================================
-- §2 加法と順序（OrderedAddCommMonoid — neg は不要）
-- ============================================================

theorem add_le_add_right {α : Type} [OrderedAddCommMonoid α] (a b c : α) (h : a ≤ b) :
    a + c ≤ b + c := OrderedAddCommMonoid.add_le_add_right a b c h

theorem add_left_le {α : Type} [OrderedAddCommMonoid α] (a b c : α) (h : b ≤ c) :
    a + b ≤ a + c := by
  have h1 := add_le_add_right b c a h
  rw [AddCommMonoid.add_comm b a, AddCommMonoid.add_comm c a] at h1; exact h1

theorem add_le_add' {α : Type} [OrderedAddCommMonoid α] {a b c d : α}
    (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right a b c h₁) (add_left_le b c d h₂)

theorem add_nonneg' {α : Type} [OrderedAddCommMonoid α] {x y : α}
    (hx : AddCommMonoid.zero ≤ x) (hy : AddCommMonoid.zero ≤ y) :
    AddCommMonoid.zero ≤ x + y := by
  have h := add_le_add' hx hy
  rwa [AddCommMonoid.add_zero] at h

-- ============================================================
-- §3 符号と非負（OrderedAddCommGroup — neg が要る）。差は a + -b で表す（Sub 非依存）。
-- ============================================================

theorem nonneg_iff_le {α : Type} [OrderedAddCommGroup α] (a b : α) :
    a ≤ b ↔ AddCommMonoid.zero ≤ b + -a := by
  constructor
  · intro h
    have h1 := add_le_add_right a b (-a) h
    rw [AddCommGroup.add_neg] at h1; exact h1
  · intro h
    have h1 := add_le_add_right AddCommMonoid.zero (b + -a) a h
    rw [AddCommMonoid.zero_add, show b + -a + a = b from by my_abel] at h1
    exact h1

theorem neg_neg_nonneg {α : Type} [OrderedAddCommGroup α] (a : α) :
    a ≤ AddCommMonoid.zero → AddCommMonoid.zero ≤ -a := by
  intro h
  have h1 := add_le_add_right a AddCommMonoid.zero (-a) h
  rw [AddCommGroup.add_neg, AddCommMonoid.zero_add] at h1; exact h1

theorem neg_le_neg' {α : Type} [OrderedAddCommGroup α] {a b : α} (h : a ≤ b) : -b ≤ -a := by
  have h1 := add_le_add_right a b (-a + -b) h
  rw [show a + (-a + -b) = -b from by my_abel,
    show b + (-a + -b) = -a from by my_abel] at h1
  exact h1

-- ============================================================
-- §4 乗法と非負（OrderedField — mul_nonneg が要る）。my_ring で分配を畳む。
-- ============================================================

theorem mul_nonneg {α : Type} [OrderedField α] (a b : α)
    (h : AddCommMonoid.zero ≤ a) (h' : AddCommMonoid.zero ≤ b) :
    AddCommMonoid.zero ≤ a * b := OrderedField.mul_nonneg a b h h'

theorem nonmul_neg_le {α : Type} [OrderedField α] (a b c : α)
    (hc : AddCommMonoid.zero ≤ c) (hab : AddCommMonoid.zero ≤ b + -a) :
    AddCommMonoid.zero ≤ b * c + -(a * c) := by
  rw [show b * c + -(a * c) = (b + -a) * c from by my_ring]
  exact mul_nonneg (b + -a) c hab hc

theorem nonneg_mul_nonneg {α : Type} [OrderedField α] (a b c : α)
    (h : AddCommMonoid.zero ≤ c) : a ≤ b → a * c ≤ b * c := by
  intro hab; rw [nonneg_iff_le] at hab ⊢
  exact nonmul_neg_le a b c h hab

-- ============================================================
-- §5 順序の自作タクティク（mono = 単調性合同・lin = 差の和で非負）
--    どちらも型多相。lin はゴールの型 α を取り出し、my_ring（Ch8・一般化済）で
--    正規化する。「tactic を先に作って派生補題を畳む」設計の要。
-- ============================================================

-- lin: 仮説 xᵢ ≤ yᵢ の差 yᵢ + -xᵢ（非負）を足し合わせ、目標 a ≤ b の b + -a に my_ring で
--      一致させる。OrderedAddCommGroup（差の非負）＋ CommRing（my_ring）を要する＝OrderedField。
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic in
elab "lin" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← goal.getType
    let (α, a, b) ← match ty.getAppFnArgs with
      | (``LE.le, #[α, _, a, b]) => pure (α, a, b)
      | _ => throwError "lin: 目標が a ≤ b でない"
    let acmInst ← synthInstance (← mkAppM ``AddCommMonoid #[α])
    let mcmInst ← synthInstance (← mkAppM ``MulCommMonoid #[α])
    let zeroExpr ← mkAppOptM ``AddCommMonoid.zero #[some α, some acmInst]
    let oneExpr  ← mkAppOptM ``MulCommMonoid.one #[some α, some mcmInst]
    let mut diffNn : Array (Expr × Expr) := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      match (← instantiateMVars decl.type).getAppFnArgs with
      | (``LE.le, #[_, _, x, y]) =>
          let iff ← mkAppM ``nonneg_iff_le #[x, y]
          let nn ← mkAppM ``Iff.mp #[iff, decl.toExpr]
          let diff ← mkAppM ``HAdd.hAdd #[y, ← mkAppM ``Neg.neg #[x]]
          diffNn := diffNn.push (diff, nn)
      | _ => pure ()
    let mut S := zeroExpr
    let mut nnPf ← mkAppM ``le_refl #[zeroExpr]
    for (diff, nn) in diffNn do
      nnPf ← mkAppM ``add_nonneg' #[nnPf, nn]
      S ← mkAppM ``HAdd.hAdd #[S, diff]
    let subBA ← mkAppM ``HAdd.hAdd #[b, ← mkAppM ``Neg.neg #[a]]
    let atomsRef ← IO.mkRef (#[] : Array Expr)
    let eL ← reifyRing oneExpr zeroExpr atomsRef subBA
    let eR ← reifyRing oneExpr zeroExpr atomsRef S
    let atoms ← atomsRef.get
    let listExpr ← mkListLit α atoms.toList
    let rho := mkLambda `i BinderInfo.default (mkConst ``Nat)
      (mkAppN (mkConst ``List.getD [Level.zero]) #[α, listExpr, mkBVar 0, zeroExpr])
    let normPf ← mkDecideProof (← mkEq (← mkAppM ``MyRing.normalize #[eL])
                                       (← mkAppM ``MyRing.normalize #[eR]))
    let hEq ← mkAppM ``MyRing.of_normalize_eq #[rho, eL, eR, normPf]
    let motive ← withLocalDeclD `z α fun z => do
      mkLambdaFVars #[z] (← mkAppM ``LE.le #[zeroExpr, z])
    let congrEq ← mkCongrArg motive hEq
    let hNonneg ← mkEqMPR congrEq nnPf
    let final ← mkAppM ``Iff.mpr #[← mkAppM ``nonneg_iff_le #[a, b], hNonneg]
    goal.assign final

-- ============================================================
-- §6 差と移項の補題（Real 専用: `-` は Real の Sub に依存）。多くは lin で畳める。
-- ============================================================

theorem sub_le_sub_right {a b : Real} (h : a ≤ b) (c : Real) : a - c ≤ b - c := by lin
theorem sub_le_sub_left {a b : Real} (h : a ≤ b) (c : Real) : c - b ≤ c - a := by lin
theorem le_add_nonneg (a b : Real) (hb : (0 : Real) ≤ b) : a ≤ a + b := by lin
theorem le_of_add_nonneg_eq {a b c : Real} (h : a + b = c) (hb : (0 : Real) ≤ b) : a ≤ c := by
  rw [← h]; exact le_add_nonneg a b hb
theorem le_of_nonneg_add_eq {a b c : Real} (h : a + b = c) (ha : (0 : Real) ≤ a) : b ≤ c := by
  rw [← h]; have : b ≤ a + b := by lin
  exact this

-- ============================================================
-- §7 calc 用 Trans インスタンス（≤/< 混在の calc はこの機構で動く——種明かしの素材）
--    < は Real の LT（≤∧≠）なので Real 専用。
-- ============================================================

theorem lt_trans (a b c : Real) : a < b → b < c → a < c := by
  intro ⟨hab, _⟩ ⟨hbc, hne_bc⟩
  exact ⟨le_trans hab hbc, fun heq => hne_bc (le_antisymm b c hbc (heq ▸ hab))⟩

theorem lt_le_trans (a b c : Real) : a < b → b ≤ c → a < c := by
  intro ⟨hab, hne⟩ hbc
  exact ⟨le_trans hab hbc, fun heq => hne (le_antisymm a b hab (heq ▸ hbc))⟩

theorem le_lt_trans {a b c : Real} : a ≤ b → b < c → a < c := by
  intro hab ⟨hbc, hne⟩
  exact ⟨le_trans hab hbc, fun heq => hne (le_antisymm b c hbc (heq ▸ hab))⟩

instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le := ⟨fun h₁ h₂ => le_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt :=
  ⟨fun h₁ h₂ => lt_le_trans _ _ _ h₁ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt := ⟨fun h₁ h₂ => le_lt_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LT.lt LT.lt := ⟨fun h₁ h₂ => lt_trans _ _ _ h₁ h₂⟩
instance : Trans (Eq : Real → Real → Prop) LE.le LE.le := ⟨fun h₁ h₂ => h₁ ▸ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) Eq LE.le := ⟨fun h₁ h₂ => h₂ ▸ h₁⟩

-- ============================================================
-- §8 厳密不等式（Real 専用: LT = ≤∧≠）
-- ============================================================

theorem add_left_lt (a b c : Real) : b < c → a + b < a + c := by
  intro ⟨hle, hne⟩
  exact ⟨add_left_le a b c hle, fun h => hne (AbstractAlg.add_left_cancel a h)⟩

theorem add_lt_add_right (a b c : Real) : a < b → a + c < b + c := by
  intro h
  rw [AddCommMonoid.add_comm a c, AddCommMonoid.add_comm b c]
  exact add_left_lt c a b h

theorem neg_lt_neg {a b : Real} (h : a < b) : -b < -a :=
  ⟨neg_le_neg' h.1, fun e => h.2 (by
    have e2 := congrArg (fun z => -z) e
    simp only [] at e2
    rw [show -(-b) = b from AbstractAlg.neg_neg b, show -(-a) = a from AbstractAlg.neg_neg a] at e2
    exact e2.symm)⟩

theorem sub_lt_sub_left {a b : Real} (h : a < b) (c : Real) : c - b < c - a :=
  add_left_lt c (-b) (-a) (neg_lt_neg h)

theorem lt_add_of_sub_lt {a b c : Real} (h : a - b < c) : a < c + b := by
  have h1 := add_lt_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

theorem sub_lt_swap {a b c : Real} (h : a - b < c) : a - c < b := by
  have h1 := lt_add_of_sub_lt h
  have h2 := add_lt_add_right a (c + b) (-c) h1
  rwa [show c + b + -c = b from by my_abel] at h2

theorem sub_lt_of_lt_add {a b c : Real} (h : a < b + c) : a - b < c := by
  have h1 := add_lt_add_right a (b + c) (-b) h
  rwa [show (b + c) + -b = c from by my_abel] at h1

theorem sub_lt_self (z : Real) {h : Real} (hh : (0 : Real) < h) : z - h < z := by
  have hneg : -h < (0 : Real) := by have := neg_lt_neg hh; rwa [neg_zero] at this
  have := add_left_lt z (-h) 0 hneg
  rwa [add_zero'] at this

theorem lt_add_pos (a b : Real) (hb : (0 : Real) < b) : a < a + b := by
  have h := add_left_lt a 0 b hb
  rwa [add_zero'] at h

theorem le_add_of_sub_le {a b c : Real} (h : a - b ≤ c) : a ≤ c + b := by
  have h1 := add_le_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

theorem sub_pos_of_lt {a b : Real} (h : a < b) : (0 : Real) < b - a := by
  refine ⟨(nonneg_iff_le a b).mp h.1, fun heq => h.2 ?_⟩
  have h' : a + (b - a) = a + 0 := by rw [← heq]
  rw [add_sub_cancel', add_zero'] at h'
  exact h'.symm

-- ============================================================
-- §9 乗法の順序と 0 < 1（Real 専用: LT・le_total）
-- ============================================================

theorem mul_right_lt (a b c : Real) : (0 : Real) < c → a < b → a * c < b * c := by
  intro ⟨hc, hnc⟩ ⟨hab, hne⟩
  refine ⟨nonneg_mul_nonneg a b c hc hab, fun heq => hne ?_⟩
  have hcne : c ≠ (0 : Real) := hnc.symm
  calc a = a * c * Field.inv c := by
        rw [mul_assoc, show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]
    _ = b * c * Field.inv c := by rw [heq]
    _ = b := by rw [mul_assoc, show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]

theorem zero_lt_one : (0 : Real) < 1 := by
  cases le_total (0 : Real) 1 with
  | inl h => exact ⟨h, fun heq => Field.nontrivial heq⟩
  | inr h =>
    have h0 : (0 : Real) ≤ -1 := neg_neg_nonneg 1 h
    have h1 : (0 : Real) ≤ (-1) * (-1) := mul_nonneg (-1) (-1) h0 h0
    have h2 : (-1 : Real) * (-1) = 1 := by my_ring
    rw [h2] at h1
    exact absurd (le_antisymm (0 : Real) (1 : Real) h1 h) Field.nontrivial

-- リテラル 2 はまだ無い: 1 + 1 で書く（リテラル機構は Ch11）
theorem zero_lt_one_one : (0 : Real) < 1 + 1 := by
  have h1 := add_left_lt 1 0 1 zero_lt_one
  rw [add_zero'] at h1
  exact lt_trans 0 1 (1 + 1) zero_lt_one h1

theorem one_one_ne_zero : ((1 : Real) + 1) ≠ 0 := ne_of_gt zero_lt_one_one

theorem pos_inv (b : Real) (hb : (0 : Real) < b) : (0 : Real) < Field.inv b := by
  have hbne : b ≠ (0 : Real) := hb.2.symm
  refine ⟨?_, fun h => Field.nontrivial (show (0 : Real) = 1 from by
    calc (0 : Real) = b * 0 := by my_ring
      _ = b * Field.inv b := by rw [h]
      _ = 1 := Field.mul_inv b hbne)⟩
  cases le_total (0 : Real) (Field.inv b) with
  | inl h => exact h
  | inr h =>
    exfalso
    have h0 : (0 : Real) ≤ -(Field.inv b) := neg_neg_nonneg _ h
    have h1 : (0 : Real) ≤ b * -(Field.inv b) := mul_nonneg b (-(Field.inv b)) hb.1 h0
    rw [mul_neg, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne] at h1
    have h2 : (1 : Real) ≤ 0 := by
      have := add_le_add_right (0 : Real) (-(1 : Real)) (1 : Real) h1
      rw [zero_add', neg_add'] at this; exact this
    exact zero_lt_one.2 (le_antisymm (0 : Real) (1 : Real) zero_lt_one.1 h2)

theorem pos_mul_pos (a b : Real) : (0 : Real) < a → (0 : Real) < b → (0 : Real) < a * b := by
  intro ha hb
  exact ⟨mul_nonneg a b ha.1 hb.1, fun h =>
    ha.2 (by
      calc (0 : Real) = 0 * Field.inv b := by my_ring
        _ = (a * b) * Field.inv b := by rw [h]
        _ = a * (b * Field.inv b) := mul_assoc _ _ _
        _ = a * 1 := by rw [show b * Field.inv b = (1 : Real) from Field.mul_inv b hb.2.symm]
        _ = a := mul_one_b a)⟩

-- ============================================================
-- §10 mono（単調性合同・型多相）。≤ の一般補題と Real の < 補題を逆向きに当てる。
-- ============================================================

syntax "mono" : tactic
macro_rules
  | `(tactic| mono) => `(tactic|
      first
      | exact le_refl _
      | assumption
      | (apply add_le_add' <;> mono)
      | (apply sub_le_sub_right <;> mono)
      | (apply sub_le_sub_left <;> mono)
      | (apply sub_lt_sub_left <;> mono)
      | (apply add_lt_add_right <;> mono)
      | (apply add_left_lt <;> mono))

-- ANCHOR: order_tac_demo
-- 単調性は両方で
example (a b c d : Real) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by mono
example (a b c d : Real) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by lin
-- 線形結合（推移）は lin のみ
example (a b c : Real) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by lin
-- 補題は最小クラスで型多相: 任意の OrderedField で成り立つ
example {α : Type} [OrderedField α] (a b : α) (h : AddCommMonoid.zero ≤ a)
    (h' : AddCommMonoid.zero ≤ b) : AddCommMonoid.zero ≤ a * b := mul_nonneg a b h h'
-- ANCHOR_END: order_tac_demo
