def Range (n : Nat) := { i : Nat // i < n }

namespace Range

@[simp]
theorem mk_val {n m : Nat} (h : m < n) : (⟨m, h⟩ : Range n).val = m := rfl

theorem ext (n : Nat) (k m : Range n) : k = m ↔ k.val = m.val :=
  Subtype.ext_iff

def incl {n : Nat} : Range n → Range n.succ :=
  fun k => ⟨k.val, Nat.lt_succ_of_lt k.property⟩

@[simp]
theorem incl_val {n : Nat} (k : Range n) : (incl k).val = k.val := rfl

def addone {n : Nat} : Range n → Range n.succ :=
  fun k => ⟨k.val + 1, Nat.succ_lt_succ k.property⟩

@[simp]
theorem addone_val {n : Nat} (k : Range n) : (addone k).val = k.val + 1 := rfl

theorem addone_incl_comm (n : Nat) (i : Range n) :
    addone (incl i) = incl (addone i) := rfl

-- Rangeに順序構造を導入し、整列なことを示し、帰納法を定義する
-- wellorderdかwellfoundedか、整礎帰納法

def le {n : Nat} : Range n → Range n → Prop :=
  InvImage ( · ≤ · ) (fun k => k.val)

instance {n : Nat} : LE (Range n) := ⟨le⟩

def lt {n : Nat} : Range n → Range n → Prop :=
  InvImage ( · < · ) (fun k => k.val)

instance {n : Nat} : LT (Range n) := ⟨lt⟩

-- @[simp]
-- theorem lt_def {n : Nat} (i j : Range n) : i.val < j.val ↔ i < j := Iff.rfl

instance {n : Nat} : WellFoundedRelation (Range n) where
  rel := lt
  wf := InvImage.wf _ Nat.lt_wfRel.wf

theorem induction (n : Nat) (P : Range n → Prop)
    (IH : ∀ x, (∀ y, y < x → P y) → P x) : ∀ a, P a := by
  intro a
  apply WellFounded.induction
  · apply Range.instWellFoundedRelation.wf
  · exact IH

def gt {n : Nat} : Range n → Range n → Prop :=
  fun i j => j < i

-- Range n 上の命題に対し、それを満たすものが非空なら最大および最小があること


end Range

open Range

variable {α : Type} [Add α] [OfNat α 0]

-- resの特別な場合とかける、fの行き先を一般化？0の行き先が0なのはなぜ？
def fpred (n : Nat) (f : Range n → Nat) : Range (n - 1) → Nat :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ n => fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩

-- 合成で書きたい
-- 単体的集合のrelを全部書く？
def res (n m : Nat) (h : n ≤ m) (f : Range m → α) : Range n → α := by
  exact fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property h⟩

def fmax (n : Nat) (f : Range n → Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => max (f ⟨n, Nat.lt_succ_self n⟩) (fmax n (fpred n.succ f))

def Summation : (n : Nat) → (Range n → α) → α
  | 0 => fun _ => 0
  | Nat.succ n =>
      fun f =>
        Summation n
          (fun k =>
            f ⟨k.val, Nat.lt_trans k.property (Nat.lt_add_one n)⟩)
            + f ⟨n, (Nat.lt_add_one n)⟩

theorem sumation_zero (f : Range 0 → α) : Summation 0 f = 0 := rfl

theorem sumation_succ (n : Nat) (f : Range n.succ → α) :
  Summation n.succ f = Summation n (res n n.succ (Nat.le_succ n) f) + f ⟨n, Nat.lt_add_one n⟩ := rfl

def natMul : Nat → α → α
  | 0, _ => 0
  | Nat.succ n, a => natMul n a + a

instance : HMul Nat α α := ⟨natMul⟩

theorem zero_mul (a : α) : (0 : Nat) * a = (0 : α) := rfl

theorem succ_mul (n : Nat) (a : α) : n.succ * a = n * a + a := rfl

theorem sum_const (n : Nat) (a : α) : Summation n (fun _ => a) = n * a :=
  match n with
  | 0 => (sumation_zero _).trans (zero_mul a).symm
  | Nat.succ n => (congrArg (fun x => x + a) (sum_const n a)).trans (succ_mul n a).symm

-- theorem sum_id (n : Nat) : Summation n (fun k => k.val) = n * (n - 1) / 2 :=
--   match n with
--   | 0 => rfl
--   | Nat.succ n => by sorry

theorem has_min (p : Nat → Prop) (hp : ∃ n, p n) :
    ∃ a, p a ∧ ∀ x, p x → ¬(x < a) := by
  rcases hp with ⟨a, ha⟩
  let motive (y : Nat) := p y → ∃ b, p b ∧ ∀ x, p x → ¬(x < b)
  let (ind : ∀ n, (∀ m, m < n → motive m) → motive n) :=
    fun n IH => (fun h => ?h)
  have h := @Nat.strongRecOn motive a ind
  exact h ha
  by_cases h' : ∃ m, m < n ∧ p m
  · rcases h' with ⟨m, hm⟩
    have := IH m hm.1 hm.2
    exact this
  · have : ∀ m, m < n → ¬p m := by
      intro m hm hpm
      apply h'
      exact ⟨m, hm, hpm⟩
    apply Exists.intro n
    constructor
    · exact h
    · intro x hpx hxn
      apply this x hxn hpx

noncomputable def min (p : Nat → Prop) (hp : ∃ n, p n) : Nat :=
  Classical.choose (has_min p hp)
