-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«04_Exists»

-- ✏ 練習 98 の解答

theorem and_left {p q : Prop} : p ∧ q → p := fun h => h.left

def fst' {α β : Type} : α × β → α := fun x => x.fst

-- ✏ 練習 99 の解答

theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩

-- ✏ 練習 100 の解答

example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩

-- ✏ 練習 101 の解答

theorem all_and {α : Type} {Q R : α → Prop} :
    (∀ a, Q a) → (∀ a, R a) → ∀ a, Q a ∧ R a :=
  fun hq hr a => ⟨hq a, hr a⟩

-- ✏ 練習 103 の解答

theorem or_idem {p : Prop} : p ∨ p → p := fun h =>
  match h with
  | .inl hp => hp
  | .inr hp => hp

-- ✏ 練習 104 の解答

theorem or_map {p q r : Prop} : (p → q) → p ∨ r → q ∨ r := fun f h =>
  match h with
  | .inl hp => .inl (f hp)
  | .inr hr => .inr hr

-- ✏ 練習 105 の解答

example : (1 = 2) ∨ (2 = 2) := .inr rfl

-- ✏ 練習 106 の解答

theorem noContra {p q : Prop} : p → ¬p → q :=
  fun hp hnp => (hnp hp).elim

-- ✏ 練習 107 の解答

theorem dni {p : Prop} : p → ¬¬p := fun hp hnp => hnp hp

-- ✏ 練習 108 の解答

example : ¬False := fun h => h

-- ✏ 練習 109 の解答

theorem isEven_two_mul : ∀ n : Nat, IsEven (2 * n) :=
  fun n => ⟨n, rfl⟩

-- ✏ 練習 110 の解答

theorem isEven_add_two : ∀ n : Nat, IsEven n → IsEven (n + 2) :=
  fun _ hn =>
    match hn with
    | ⟨k, hk⟩ => ⟨k + 1, (congrArg (· + 2) hk).trans (Nat.mul_succ 2 k).symm⟩

-- ✏ 練習 111 の解答

example : IsEven 10 := ⟨5, rfl⟩

-- ✏ 練習 102 の解答

theorem exists_left {α : Type} {Q R : α → Prop} :
    (∃ a, Q a ∧ R a) → ∃ a, Q a :=
  fun h =>
    match h with
    | ⟨a, hqr⟩ => ⟨a, hqr.left⟩

-- ✏ 練習 96 の解答

example : ∃ n : Nat, IsZero n := ⟨0, rfl⟩

-- ✏ 練習 112 の解答

example : IsZero (0 * 5) := rfl

example : IsZero (5 * 0) := rfl

example : IsZero (5 * 0) := all_mul_zero 5

-- ✏ 練習 113 の解答

example : 1 ≤ 3 := Nat.le.step (Nat.le.step Nat.le.refl)

-- ✏ 練習 114 の解答

theorem MyEq.trans {α : Type} {a b c : α} (h₁ : MyEq a b) (h₂ : MyEq b c) :
    MyEq a c :=
  match h₂ with
  | .refl => h₁

-- ✏ 練習 115 の解答

theorem MyEq.ofEq {α : Type} {a b : α} (h : a = b) : MyEq a b :=
  match h with
  | rfl => MyEq.refl

-- ✏ 練習 116 の解答

theorem andToOr {p q : Prop} : p ∧ q → p ∨ q := fun h => .inl h.left

-- ✏ 練習 117 の解答

#check @Nat.add_sub_cancel

example : ∀ n : Nat, n + 1 - 1 = n := fun n => Nat.add_sub_cancel n 1

-- ✏ 練習 118 の解答

#eval (3 : Nat) - 5

-- ✏ 練習 119 の解答

-- ✏ 練習 97 の解答

theorem triple_multiple : ∀ n : Nat, ∃ k, n + n + n = 3 * k :=
  fun n => ⟨n, Eq.symm (Eq.trans (Nat.succ_mul 2 n)
    (congrArg (fun x => x + n) (Nat.two_mul n)))⟩
