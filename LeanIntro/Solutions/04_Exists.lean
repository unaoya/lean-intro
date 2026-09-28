-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«04_Exists»

-- ✏ 練習 50 の解答

def surjectiveOfRightInverse (A B : Type) (f : A → B) (g : B → A)
    (hfg : ∀ b : B, f (g b) = b) :
    ∀ b : B, ∃ a : A, f a = b :=
  fun b => Exists.intro (g b) (hfg b)

-- ✏ 練習 55 の解答

def threeCompSurjective (A B C D : Type)
    (f : A → B) (g : B → C) (k : C → D)
    (hf : ∀ b, ∃ a, f a = b) (hg : ∀ c, ∃ b, g b = c)
    (hk : ∀ d, ∃ c, k c = d) :
    ∀ d, ∃ a, k (g (f a)) = d :=
  comp_surjective A C D (fun a => g (f a)) k
    (comp_surjective A B C f g hf hg) hk

-- ✏ 練習 52 の解答

def existsFirst (A B C : Type) (f : A → B) (g : A → C) (b : B) (c : C)
    (h : ∃ a : A, f a = b ∧ g a = c) : ∃ a : A, f a = b :=
  match h with
  | Exists.intro a habc =>
    match habc with
    | And.intro hab _ => Exists.intro a hab

-- ✏ 練習 53 の解答

def preimageTwoPoints (A B : Type) (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y) (x a b : A)
    (h : f x = f a ∨ f x = f b) : x = a ∨ x = b :=
  match h with
  | Or.inl hxa => Or.inl (hf x a hxa)
  | Or.inr hxb => Or.inr (hf x b hxb)

-- ✏ 練習 54 の解答

def neOfImageNe (A B : Type) (f : A → B) (x y : A)
    (hne : f x ≠ f y) : x ≠ y :=
  fun h => hne (congrArg f h)

-- ✏ 練習 51 の解答

def isEven_add_two : ∀ n : Nat, IsEven n → IsEven (n + 2) :=
  fun _ hn => isEven_add hn (Exists.intro 1 rfl)
