variable {α : Type} [Add α] [OfNat α 0]

-- 任意の自然数に対して0以上である
theorem zero_le (n : Nat) : 0 ≤ n :=
  Nat.zero_le n

#print Nat.zero_le
#print Nat.le

#print Nat.brecOn

-- inductiveの説明
-- これで全てでありかつ全て異なる

inductive MyType : Type where
  | foo : MyType
  | bar : MyType

theorem foo_neq_bar : MyType.foo ≠ MyType.bar := MyType.noConfusion

theorem foo_or_bar (x : MyType) : x = MyType.foo ∨ x = MyType.bar :=
  match x with
  | MyType.foo => Or.inl rfl
  | MyType.bar => Or.inr rfl

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

theorem zero_ne_succ (n : MyNat) : MyNat.zero ≠ MyNat.succ n := MyNat.noConfusion

theorem zero_or_succ (n : MyNat) : n = MyNat.zero ∨ ∃ m, n = MyNat.succ m :=
  match n with
  | MyNat.zero => Or.inl rfl
  | MyNat.succ m => Or.inr ⟨m, rfl⟩

theorem succ_inj {n m : MyNat} (h : MyNat.succ n = MyNat.succ m) : n = m :=
  MyNat.noConfusion h id

inductive MyNat.le : MyNat → MyNat → Prop where
  | refl (n : MyNat) : MyNat.le n n
  | succ (n m : MyNat) : MyNat.le n m → MyNat.le n (MyNat.succ m)

theorem MyNat.le_refl (n : MyNat) : MyNat.le n n := MyNat.le.refl n

-- 任意の自然数に対してそれより大きな自然数が存在することを示す（何を仮定する？）
theorem exists_gt (n : Nat) : ∃ m, n < m :=
  ⟨n.succ, Nat.lt_succ_self n⟩

theorem exists_gt' : ∀ (n : Nat), ∃ m, n < m :=
  fun n => ⟨n.succ, Nat.lt_succ_self n⟩

-- 任意は直積、関数、存在は直和
-- andがかつ、orがまたは

-- 偶数の和が偶数であることを示す（何を仮定する？）

def Even (n : Nat) := ∃ (m : Nat), n = 2 * m

def Even' (n : Nat) := Exists (fun m => n = 2 * m)

#check Even
#check Even'

#print Even
#print Even'

theorem two_is_even : Even 2 := ⟨1, rfl⟩

#print two_is_even

def two_is_two_mul_n (n : Nat) : Prop := 2 = 2 * n

theorem two_is_even' : Even 2 := @Exists.intro Nat two_is_two_mul_n 1 rfl

#check Exists

-- SortとType

#print Exists

#check Exists.intro

theorem even_add_even_even (m n : Nat) (h1 : Even m) (h2 : Even n) : Even (m + n) :=
  match h1, h2 with
  | ⟨m', h3⟩, ⟨n', h4⟩ => ⟨m' + n', by rw [h3, h4, Nat.mul_add]⟩

def Range (n : Nat) := { i : Nat // i < n }

#check max
#check (inferInstance : Max Nat)
#check max 1 2

def incl {n : Nat} : Range n → Range n.succ := fun k => ⟨k.val, Nat.lt_succ_of_lt k.property⟩

def addone {n : Nat} : Range n → Range n.succ := fun k => ⟨k.val + 1, sorry⟩

def fpred (n : Nat) (f : Range n → Nat) : Range (n - 1) → Nat :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ n => fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n)⟩

def fmax (n : Nat) (f : Range n → Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => max (f ⟨n, Nat.lt_succ_self n⟩) (fmax n (fpred n.succ f))

#check Nat.lt_trans

#check Nat.recOn
  -- let F : ℕ → X × ℝ := fun n ↦
  --   Nat.recOn n (Prod.mk x (min ε (B 0)))
  --     fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)

inductive test where
  | a
  | b

#check test.rec

def testfun (x : test) : Nat :=
  match x with
  | test.a => 1
  | test.b => 2

-- set_option pp.all true
#print testfun
#print test.casesOn

def Sumation : (n : Nat) → (Range n → α) → α
  | 0 => fun _ => 0
  | Nat.succ n =>
      fun f =>
        Sumation n
          (fun k =>
            f ⟨k.val, Nat.lt_trans k.property (Nat.lt_add_one n)⟩)
            + f ⟨n, (Nat.lt_add_one n)⟩

-- 積分の性質の離散ばん
-- 区間の分割、線形性、単調性、三角不等式


example (k n m : Nat) (h : k < n) (h' : n ≤ m) : k < m := Nat.lt_of_lt_of_le h h'

def res (n m : Nat) (h : n ≤ m) (f : Range m → α) : Range n → α := by
  exact fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property h⟩

variable [HMul Nat α α]

theorem zero_mul (a : Nat) : 0 * a = 0 := by sorry

theorem sumation_zero (f : Range 0 → Nat) : Sumation 0 f = 0 := rfl

theorem sumation_succ (n : Nat) (f : Range n.succ → Nat) :
  Sumation n.succ f = Sumation n (res n n.succ (Nat.le_succ n) f) + f ⟨n, Nat.lt_add_one n⟩ := rfl

theorem suc_add (n : Nat) : n.succ * a = n * a + a := sorry

theorem sum_const (n : Nat) (a : Nat) : Sumation n (fun _ => a) = n * a :=
  match n with
  | 0 => (sumation_zero _).trans (zero_mul a).symm
  | Nat.succ n => (congrArg (fun x => x + a) (sum_const n a)).trans (suc_add n).symm

theorem sum_id (n : Nat) : Sumation n (fun k => k.val) = n * (n - 1) / 2 :=
  match n with
  | 0 => rfl
  | Nat.succ n => by sorry

-- 証明項を直接書く
-- tacticを使う
-- ライブラリの定理を使う
-- tacticもライブラリがある

-- #check Iff.intro

-- theorem sq_one (n : Nat) : n = 1 ↔ n * n = 1 :=
--   Iff.intro
--     (fun h => by rw [h, Nat.mul_one])
--     (fun h => by rw [← h, Nat.mul_one])
