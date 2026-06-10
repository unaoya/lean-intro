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

-- Range の順序と整礎帰納法（points_mono 等の項レベル帰納に使用）
def lt {n : Nat} : Range n → Range n → Prop :=
  InvImage ( · < · ) (fun k => k.val)

instance {n : Nat} : LT (Range n) := ⟨lt⟩

instance {n : Nat} : WellFoundedRelation (Range n) where
  rel := lt
  wf := InvImage.wf _ Nat.lt_wfRel.wf

theorem induction (n : Nat) (P : Range n → Prop)
    (IH : ∀ x, (∀ y, y < x → P y) → P x) : ∀ a, P a := by
  intro a
  apply WellFounded.induction
  · apply Range.instWellFoundedRelation.wf
  · exact IH

end Range

open Range

variable {α : Type} [Add α] [OfNat α 0]

def Summation : (n : Nat) → (Range n → α) → α
  | 0 => fun _ => 0
  | Nat.succ n =>
      fun f =>
        Summation n
          (fun k =>
            f ⟨k.val, Nat.lt_trans k.property (Nat.lt_add_one n)⟩)
            + f ⟨n, (Nat.lt_add_one n)⟩

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
