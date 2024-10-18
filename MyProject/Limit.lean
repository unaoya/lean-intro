import MyProject.Lemmas

-- 古典論理、選択公理（無限直積が空でない、とは違う、型理論的な何か？）を使う
-- 全ての命題に真偽が決まるか？排中律？

noncomputable section

open Real Classical

-- 解析入門の実数の公理が全て成立することを確認し、名前をつける

-- 極限の定義

-- 関数の極限（HasLimAtの方がいい？）
def IsLimAt (f : Real → Real) (l : Real) (a : Real) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) < ε

def HasLimAt (f : Real → Real) (a : Real) : Prop :=
  ∃ l, IsLimAt f l a

def limit (f : Real → Real) (a : Real) (hf : HasLimAt f a) : Real :=
  choose hf

theorem limit_eq (f : Real → Real) (a : Real) (hf : HasLimAt f a) : IsLimAt f (limit f a hf) a :=
  choose_spec hf

def limit' (f : Real → Real) (a : Real) {l : Real} (hf : IsLimAt f l a) : Real := l

theorem limit_unique (f : Real → Real) (l₁ l₂ : Real) (a : Real) (h₁ : IsLimAt f l₁ a) (h₂ : IsLimAt f l₂ a) : l₁ = l₂ := by
  sorry

theorem limit_eq' (f : Real → Real) (a : Real) (l : Real) (h : IsLimAt f l a) : limit f a ⟨l, h⟩ = l := by
  rw [limit]
  sorry

theorem limit_eq_iff (f : Real → Real) (a : Real) (l : Real) (hf : HasLimAt f a) : IsLimAt f l a ↔ limit f a hf = l := by
  rw [limit]
  sorry

theorem limit_iff (f : Real → Real) (a : Real) (f' : Real) (hf : HasLimAt f a) : IsLimAt f f' a ↔ limit f a hf = f' := by
  rw [limit_eq_iff]

theorem limit_iff_le (f : Real → Real) (a : Real) (l : Real)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) ≤ ε) : IsLimAt f l a := by sorry

theorem limit_at0_iff_le (f : Real → Real) (l : Real)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x) ∧ abs (x) < δ → abs (f x - l) ≤ ε) : IsLimAt f l 0 := by sorry

def Continuous (f : Real → Real) : Prop :=
  ∀ a, ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

theorem continuous_sub (f g : Real → Real) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun t ↦ f t - g t) := by sorry

theorem continuous_const (c : Real) : Continuous (fun t ↦ c) := by sorry
