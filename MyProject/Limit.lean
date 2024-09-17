import MyProject.Real
import MyProject.NatNum

-- 古典論理、選択公理（無限直積が空でない、とは違う、型理論的な何か？）を使う
-- Decidableも消したい
-- 全ての命題に真偽が決まるか？排中律？
noncomputable section

open Real

-- 実数の計算とかsummationの計算とか。抽象化して準備しておく。

theorem summation_smul (n : Nat) (f : Range n → Real) (c : Real) :
  Sumation n (fun i ↦ c * f i) = c * Sumation n f := by
  sorry

theorem sub_self (a : Real) : a - a = 0 := by
  sorry

theorem add_sub_cancel (a b : Real) : a + b - a = b := by
  sorry

theorem add_sub_add (a b c d : Real) : a + b - (c + d) = (a - c) + (b - d) := by
  sorry

theorem add_mul (a b c : Real) : (a + b) * c = a * c + b * c := by
  sorry

theorem neg_mul (a b : Real) : -a * b = -(a * b) := by
  sorry

theorem add_neg_sub (a b : Real) : a + -b = a - b := by
  sorry

theorem mul_div_cancel (a b : Real) : a * b / b = a := by
  sorry

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by
  sorry

theorem zero_lt_one : (0 : Real) < 1 := by
  sorry

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / 2 := by
  sorry

theorem min_pos (a b : Real) (h : 0 < a) (h' : 0 < b) : 0 < min a b := by
  sorry

theorem mul_nonneg (a b : Real) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b := by
  sorry

theorem Real.le_of_lt (a b : Real) : a < b → a ≤ b := by
  sorry

theorem le_sub (a b : Real) : 0 ≤ a - b ↔ a ≤ b := by
  sorry

theorem pos_iff_lt (a b : Real) : a < b ↔ 0 < b - a := by
  sorry

instance : Max Real := sorry

#check (inferInstance : Max Real)

theorem le_abs (a : Real) : a ≤ abs a := by
  sorry

theorem neg_le_abs (a : Real) : -a ≤ abs a := by
  sorry

theorem abs_le (a b : Real) (h₀ : -a ≤ b) (h₁ : a ≤ b) : abs a ≤ b := by
  sorry

theorem abs_zero : (0 : Real).abs = 0 := by
  sorry

theorem abs_triangle (a b : Real) : abs (a + b) ≤ abs a + abs b := by
  sorry

theorem neg_sub_neg_abs (a b : Real) : abs (-a - -b) = abs (a - b) := by
  sorry

theorem addtive_summation (n : Nat) (f g : Range n → Real) :
  Sumation n (fun i ↦ f i + g i) = Sumation n f + Sumation n g := by
  sorry

theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
  Sumation n f = Sumation n g := by
  sorry

theorem neg_summation (n : Nat) (f : Range n → Real) :
  -Sumation n f = Sumation n (fun i ↦ -f i) := by
  sorry

theorem sumation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
  0 ≤ Sumation n f := by
  sorry

def fpred' (n : Nat) (f : Range n.succ → Real) : Range n → Real :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ n => fun k => f ⟨k.val, Nat.lt_of_lt_of_le k.property (Nat.le_succ n.succ)⟩

def fmax' (n : Nat) (f : Range n → Real) : Real :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => max (f ⟨n, Nat.lt_succ_self n⟩) (fmax' n (fpred' n f))


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
  -- exact Classical.propDecidable _

def deriv (f : Real → Real) (a : Real) : Real :=
  if h : ∃ f', HasDerivAt f f' a then Classical.choose h else 0

-- -- 微分係数の具体例
-- example (n : Nat) : HasDerivAt (fun x ↦ x ^ n) (n * a ^ (n - 1)) a := by
--   sorry

-- 分割を定義
structure Partition (n : Nat) (a b : Real) where
  points : Range n.succ → Real
  increase : ∀ i : Range n, points (incl i) < points (addone i)
  left : points ⟨0, by simp⟩ = a
  right : points ⟨n, by simp⟩ = b

-- 代表点を定義
def IsRepr (a b : Real) (n : Nat) (Δ : Partition n a b)
  (ξ : Range n → Real) : Prop :=
  ∀ i : Range n, Δ.points (incl i) ≤ ξ i ∧ ξ i ≤ Δ.points (addone i)

def Partition.length (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) : Real :=
  Δ.points (addone i) - Δ.points (incl i)

theorem Partition.length_pos (n : Nat) (a b : Real) (Δ : Partition n a b) (i : Range n) :
  0 < Partition.length n a b Δ i := by
  simp [Partition.length]
  rw [← pos_iff_lt]
  exact Δ.increase i

theorem Partition.zero (a b : Real) (Δ : Partition 0 a b) : a = b := by
  have ha : Δ.points ⟨0, by simp⟩ = a := by rw [Δ.left]
  have hb : Δ.points ⟨0, by simp⟩ = b := by rw [Δ.right]
  rw [← ha, hb]

theorem summation_zero (f : Range 0 → Real) : Sumation 0 f = 0 := rfl

theorem Partition.length_sum (n : Nat) (a b : Real) (Δ : Partition n a b) :
  Sumation n (Partition.length n a b Δ) = b - a :=
  match n with
  | Nat.zero => by
    have : a = b := Partition.zero a b Δ
    rw [summation_zero]
    rw [this]
    rw [sub_self]
  | Nat.succ n => by
    let c := Δ.points ⟨n, sorry⟩
    let Δ' := Partition.mk (fun i => Δ.points (incl i)) sorry sorry sorry
    have h : Sumation n (Partition.length n a c Δ') = c - a := by
      exact Partition.length_sum n a c Δ
    have : b - a = (c - a) + (b - c) := by
      rw [add_sub_add]
      rw [sub_self]
    rw [this]
    sorry

def Partition.diam (n : Nat) (a b : Real) (Δ : Partition n a b) : Real :=
  fmax' n.succ Δ.points

-- リーマン和の定義
def RiemannSum (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) : Real :=
    Sumation n (fun i ↦ f (ξ i) * Δ.length i)

theorem const_riemann_sum (c a b : Real) (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun _ ↦ c) a b n Δ ξ = c * (b - a) := by
  rw [RiemannSum]
  rw [summation_smul]
  rw [Partition.length_sum]

theorem additive_riemann_sum (f g : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun t ↦ f t + g t) a b n Δ ξ = RiemannSum f a b n Δ ξ + RiemannSum g a b n Δ ξ := by
  rw [RiemannSum, RiemannSum, RiemannSum]
  rw [← addtive_summation]
  rw [summation_congr]
  intro i
  rw [add_mul]

theorem neg_riemann_sum (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) :
  RiemannSum (fun t ↦ -f t) a b n Δ ξ = -RiemannSum f a b n Δ ξ := by
  rw [RiemannSum, RiemannSum, neg_summation]
  apply summation_congr
  intro i
  rw [neg_mul]

theorem RiemannSum_nonneg (f : Real → Real) (a b : Real) (n : Nat)
  (Δ : Partition n a b) (ξ : Range n → Real) (h : ∀ x, 0 ≤ f x) :
  0 ≤ RiemannSum f a b n Δ ξ := by
  apply sumation_nonneg
  intro i
  apply mul_nonneg
  apply h (ξ i)
  apply Real.le_of_lt
  apply Partition.length_pos

-- 積分の定義
def HasIntegral (f : Real → Real) (a b : Real) (i : Real) : Prop :=
  ∀ (ε : Real), 0 < ε → ∃ (δ : Real), 0 < δ ∧ ∀ n : Nat, ∀ Δ : Partition n a b, ∀ ξ : Range n → Real,
    IsRepr a b n Δ ξ → (Partition.diam n a b Δ) < δ →
    abs (RiemannSum f a b n Δ ξ - i) < ε

instance : Decidable (∃ i, HasIntegral f a b i) := by sorry

def Integral (f : Real → Real) (a b : Real) : Real :=
  if h : ∃ i, HasIntegral f a b i then Classical.choose h else 0

theorem HasIntegral_iff (f : Real → Real) (a b : Real) (i : Real) :
  HasIntegral f a b i ↔ Integral f a b = i := by
  sorry

theorem integral_congr (f g : Real → Real) (a b : Real) (h : ∀ x, f x = g x) :
  Integral f a b = Integral g a b := by
  sorry

-- 定数関数の積分

theorem const_integral (c a b : Real) : Integral (fun _ ↦ c) a b = c * (b - a) := by
  rw [← HasIntegral_iff]
  intro ε hε
  apply Exists.intro 1
  constructor
  · exact zero_lt_one
  · intros n Δ ξ _ _
    rw [const_riemann_sum]
    rw [sub_self]
    rw [abs_zero]
    exact hε

-- 積分の線形性

theorem additive_integral (f g : Real → Real) (a b : Real) :
  Integral (fun t ↦ f t + g t) a b = Integral f a b + Integral g a b := by
  rw [← HasIntegral_iff]
  have hf : HasIntegral f a b (Integral f a b) := by rw [HasIntegral_iff]
  have hg : HasIntegral g a b (Integral g a b) := by rw [HasIntegral_iff]
  intro ε hε
  have hε2 : ε / 2 > 0 := by apply pos_half; exact hε
  rcases hf (ε / 2) hε2 with ⟨δf, hδf⟩
  rcases hg (ε / 2) hε2 with ⟨δg, hδg⟩
  apply Exists.intro (min δf δg)
  constructor
  · apply min_pos; exact hδf.1; exact hδg.1
  · intros n Δ ξ h h'
    rw [additive_riemann_sum]
    rw [add_sub_add]
    have hf' := hδf.2 n Δ ξ h sorry
    have hg' := hδg.2 n Δ ξ h sorry
    sorry

theorem neg_integral (f : Real → Real) (a b : Real) :
  Integral (fun t ↦ -f t) a b = -Integral f a b := by
  rw [← HasIntegral_iff]
  have : HasIntegral f a b (Integral f a b) := by rw [HasIntegral_iff]
  intro ε hε
  rcases this ε hε with ⟨δ, hδ⟩
  apply Exists.intro δ
  constructor
  · exact hδ.1
  · intro n Δ ξ h h'
    rw [neg_riemann_sum]
    rw [neg_sub_neg_abs]
    exact hδ.2 n Δ ξ h h'

theorem sub_integral (f g : Real → Real) (a b : Real) :
  Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by
  rw [← add_neg_sub]
  rw [← neg_integral]
  rw [← additive_integral]
  apply integral_congr
  intro x
  rw [add_neg_sub]

-- 積分の区間についての加法性

theorem interval_add_integral (f : Real → Real) (a b c : Real) :
  Integral f a b + Integral f b c = Integral f a c := by
  symm
  rw [← HasIntegral_iff]
  have hab : HasIntegral f a b (Integral f a b) := by rw [HasIntegral_iff]
  have hbc : HasIntegral f b c (Integral f b c) := by rw [HasIntegral_iff]
  intro ε hε
  rcases hab (ε / 2) (pos_half ε hε) with ⟨δab, hab⟩
  rcases hbc (ε / 2) (pos_half ε hε) with ⟨δbc, hbc⟩
  apply Exists.intro (min δab δbc)
  constructor
  · apply min_pos; exact hab.1; exact hbc.1
  · intros n Δ ξ h h'
    let k := min sorry
    let Δ₁ := Partition.mk (fun i => sorry)
    let ξ₁ := fun i => sorry
    let Δ₂ := Partition.mk (fun i => sorry)
    let ξ₂ := fun i => sorry
    have : RiemannSum f a c n Δ ξ = RiemannSum f a b n Δ₁ ξ₁ + RiemannSum f b c n Δ₂ ξ₂ := by sorry
    -- 上は等式にはできない。代表点をうまく選んでも無理。誤差を許容する必要がある。

-- 積分の単調性

theorem integral_nonneg (f : Real → Real) (a b : Real) (h : a < b) (h' : ∀ x, 0 ≤ f x) :
  0 ≤ Integral f a b := by
  by_cases h'' : ∃ i, HasIntegral f a b i
  · rcases h'' with ⟨i, h''⟩
    have h₀ : 0 ≤ i := by
      rw [HasIntegral] at h''
      false_or_by_contra
      have : i < 0 := by sorry
      let ε := i / 2
      rcases h'' ε sorry with ⟨δ, hδ⟩
      let n := Nat.ceil (2 * (b - a) / δ)
      let Δ := Partition.mk (fun i => sorry)
      let ξ := fun i => sorry
    have h₁ : i = Integral f a b := by
      symm
      rw [← HasIntegral_iff]
      exact h''
    rw [← h₁]
    exact h₀
  · sorry

theorem integral_monotone (f g : Real → Real) (a b : Real) (h : a < b) (h' : ∀ x, f x ≤ g x) :
  Integral f a b ≤ Integral g a b := by
  rw [← le_sub]
  rw [← sub_integral]
  apply integral_nonneg _ _ _ h
  intro x
  rw [le_sub]
  exact h' x

-- 三角不等式

theorem int_triangle_ineq (f : Real → Real) (a b : Real) (h : a < b) :
  abs (Integral f a b) ≤ Integral (fun x ↦ abs (f x)) a b := by
  apply abs_le
  · rw [← neg_integral]
    have h₁ : ∀ x, -f x ≤ abs (f x) := fun x ↦ neg_le_abs (f x)
    apply integral_monotone (fun x ↦ -(f x)) (fun x ↦ abs (f x)) a b h h₁
  · have h₀ : ∀ x, f x ≤ abs (f x) := fun x ↦ le_abs (f x)
    apply integral_monotone f (fun x ↦ abs (f x)) a b h h₀

-- 微積分学の基本定理

theorem main (f : Real → Real) (a x : Real) (h : Continuous f) :
  HasDerivAt (fun x ↦ Integral f a x) (f x) x := by
  intro ε hε
  rcases h x ε hε with ⟨δ, hδ⟩
  simp
  apply Exists.intro δ
  constructor
  · exact hδ.1
  · intro y h₀ h₁
    have : Integral f a y - Integral f a x = Integral f x y := by
      rw [← interval_add_integral _ a x y]
      rw [add_sub_cancel]
    rw [this]
    have : f x = Integral (fun t ↦ f x) x y / (y - x) := by
      rw [const_integral]
      rw [mul_div_cancel]
    rw [this]
    have : Integral f x y / (y - x) - Integral (fun t => f x) x y / (y - x) =
      (Integral f x y - Integral (fun t => f x) x y) / (y - x) := by
      rw [div_sub_div]
    rw [this]
    rw [← sub_integral]
    have : ∀ t, (f t - f x).abs < ε := by sorry
    have : (Integral (fun t => (f t - f x).abs) x y) < ε * (y - x) := by
      sorry
    sorry
