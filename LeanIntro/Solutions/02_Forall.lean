-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«02_Forall»

-- ✏ 練習 29 の解答

def comp_monotone (f g : Nat → Nat)
    (hf : ∀ x y : Nat, x ≤ y → f x ≤ f y)
    (hg : ∀ u v : Nat, u ≤ v → g u ≤ g v) :
    ∀ x y : Nat, x ≤ y → g (f x) ≤ g (f y) :=
  fun x y h => hg (f x) (f y) (hf x y h)

-- ✏ 練習 28 の解答

#check 3 = 5

#check 5 = 5

-- ✏ 練習 31 の解答

def two_add_three : 2 + 3 = 5 := rfl

-- ✏ 練習 32 の解答

-- ✏ 練習 33 の解答

#check all_refl 12

#check fun n : Nat => all_refl (n + 1)

-- ✏ 練習 35 の解答

def three_comp_injective (A B C D : Type)
    (f : A → B) (g : B → C) (k : C → D)
    (hf : ∀ x y, f x = f y → x = y)
    (hg : ∀ x y, g x = g y → x = y)
    (hk : ∀ x y, k x = k y → x = y) :
    ∀ x y, k (g (f x)) = k (g (f y)) → x = y :=
  fun x y h => hf x y (hg (f x) (f y) (hk (g (f x)) (g (f y)) h))

-- ✏ 練習 30 の解答

def cancel_pointwise_again (X A B : Type)
    (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y)
    (u v : X → A) (h : ∀ t : X, f (u t) = f (v t)) :
    ∀ t : X, u t = v t :=
  fun t => hf (u t) (v t) (h t)

-- ✏ 練習 36 の解答

def leftCompose (X A B : Type) (f : A → B) :
    (X → A) → (X → B) :=
  fun u => fun t => f (u t)

def leftCompose_injective (X A B : Type) (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y) :
    ∀ u v : X → A,
      leftCompose X A B f u = leftCompose X A B f v →
      u = v :=
  fun u v h =>
    funext (fun t =>
      hf (u t) (v t) (congrArg (fun w : X → B => w t) h))

-- ✏ 練習 37 の解答

def injective_of_pointwise_cancel (f : Nat → Nat)
    (hcancel : ∀ u v : Nat → Nat,
      (∀ t : Nat, f (u t) = f (v t)) → ∀ t : Nat, u t = v t) :
    ∀ x y : Nat, f x = f y → x = y :=
  fun x y h => hcancel (fun _ => x) (fun _ => y) (fun _ => h) 0

-- ✏ 練習 38 の解答

def three_comp_monotone (f g k : Nat → Nat)
    (hf : ∀ x y, x ≤ y → f x ≤ f y)
    (hg : ∀ x y, x ≤ y → g x ≤ g y)
    (hk : ∀ x y, x ≤ y → k x ≤ k y) :
    ∀ x y, x ≤ y → k (g (f x)) ≤ k (g (f y)) :=
  fun x y h => hk (g (f x)) (g (f y)) (hg (f x) (f y) (hf x y h))

-- ✏ 練習 34 の解答

-- ✏ 練習 39 の解答

def left_inverse_of_right_inverse (A B : Type) (f : A → B) (g : B → A)
    (hf : ∀ x y : A, f x = f y → x = y)
    (hfg : ∀ y : B, f (g y) = y) :
    ∀ x : A, g (f x) = x :=
  fun x => hf (g (f x)) x (hfg (f x))
