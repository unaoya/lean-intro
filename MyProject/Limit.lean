import MyProject.Real

open Real

-- 解析入門の実数の公理が全て成立することを確認し、名前をつける

-- 極限の定義

-- 関数の極限
def IsLimAt (f : Real → Real) (l : Real) (a : Real) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) < ε

def Continuous (f : Real → Real) : Prop :=
  ∀ a, ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

-- 微分係数の定義
def HasDerivAt (f : Real → Real) (f' : Real) (a : Real) : Prop :=
  IsLimAt (fun x ↦ (f x - f a) / (x - a)) f' a

instance : Decidable (∃ f', HasDerivAt f f' a) := by sorry

noncomputable
def deriv (f : Real → Real) (a : Real) : Real :=
  if h : ∃ f', HasDerivAt f f' a then Classical.choose h else 0

-- 微分係数の具体例

-- 導関数の定義？

def Range (n : Nat) := { i : Nat // i < n }

def Sumation : (n : Nat) → (Range n → Real) → Real
  | 0 => fun i => 0
  | Nat.succ n => fun f => Sumation n (fun k => f ⟨k.val, sorry⟩) + f ⟨n, sorry⟩

-- 分割を定義

structure Partition (n : Nat) (a b : Real) where
  points : Range n.succ → Real
  left : points ⟨0, by simp⟩ = a
  right : points ⟨n, by simp⟩ = b

-- 代表点を定義
def IsRepr (a b : Real) (n : Nat) (Δ : Partition n a b)
  (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points ⟨i.val, by sorry⟩ ≤ ξ i ∧ ξ i ≤ Δ.points ⟨i.val.succ, sorry⟩

def Partition.length (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) : Real :=
  Δ.points ⟨i.val.succ, sorry⟩ - Δ.points ⟨i.val, sorry⟩

def Partition.diam (n : Nat) (a b : Real) (Δ : Partition n a b) : Real :=
  sorry
  -- max Partition.length n a b Δ i

-- リーマン和の定義
def HasRiemannSum (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (S : Real) (ξ : Range n → Real) : Prop :=
  Sumation n (fun i ↦ f (ξ i) * Δ.length i) = S

instance : Decidable (∃ S, HasRiemannSum f a b n Δ S ξ) := by sorry

noncomputable
def RiemannSum (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real): Real :=
  if h : ∃ S, HasRiemannSum f a b n Δ S ξ then Classical.choose h else 0

-- 積分の定義
def HasIntegral (f : Real → Real) (a b : Real) (i : Real) : Prop :=
  ∀ (ε : Real), 0 < ε → ∃ (δ : Real), 0 < δ ∧ ∀ n : Nat, ∀ Δ : Partition n a b, ∀ ξ : Range n → Real,
    IsRepr a b n Δ ξ → (Partition.diam n a b Δ) < δ →
    abs (RiemannSum f a b n Δ ξ - i) < ε

instance : Decidable (∃ i, HasIntegral f a b i) := by sorry

noncomputable
def Integral (f : Real → Real) (a b : Real) : Real :=
  if h : ∃ i, HasIntegral f a b i then Classical.choose h else 0

-- 不定積分の定義

-- 定数関数の積分
theorem const_integral (c a b : Real) : Integral (fun x ↦ c) a b = c * (b - a) := by
  sorry

-- 積分の線形性
theorem linear_integral (f g : Real → Real) (a b : Real) :
  Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by
  sorry

-- 積分の区間についての加法性

theorem add_integral (f : Real → Real) (a b c : Real) (h : a < b) :
  Integral f a b + Integral f b c = Integral f a c := by
  sorry

-- 積分の単調性
theorem integral_monotone (f g : Real → Real) (a b : Real) (h : a < b) (h' : ∀ x, f x ≤ g x) :
  Integral f a b ≤ Integral g a b := by
  sorry

-- 三角不等式

theorem int_triangle_ineq (f : Real → Real) (a b : Real) :
  abs (Integral f a b) ≤ Integral (fun x ↦ abs (f x)) a b := by
  sorry

-- 微積分学の基本定理

theorem main (f : Real → Real) (a x : Real) (h : Continuous f) :
  HasDerivAt (fun x ↦ Integral f a x) (f x) x := by
  intro ε hε
  rcases h x ε hε with ⟨δ, hδ⟩
  simp
  exact ⟨δ, ⟨hδ.1, by
    intro y h₀ h₁
    have : Integral f a y - Integral f a x = Integral f x y := by sorry
    rw [this]
    have : f x = Integral (fun t ↦ f x) x y / (y - x) := by sorry
    rw [this]
    have : Integral f x y / (y - x) - Integral (fun t => f x) x y / (y - x) = (Integral f x y - Integral (fun t => f x) x y) / (y - x) := by sorry
    rw [this]
    rw [← linear_integral]
    sorry
  ⟩⟩
