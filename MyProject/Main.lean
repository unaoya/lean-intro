import MyProject.Limit
import MyProject.Deriv
import MyProject.Integral

noncomputable section

open Real Classical

theorem nez_of_abs_pos {x : Real} (h : 0 < x.abs) : x ≠ 0 := by sorry

theorem pos_abs {x : Real} (h : 0 < x) : x.abs = x := by sorry

theorem abs_nonneg {x : Real} : 0 ≤ x.abs := by sorry

theorem le_trans {a b c : Real} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  apply Trans.trans h₁ h₂

theorem integral_sub_interval (f : Real → Real) (a b c : Real) :
    Integral f a b - Integral f a c = Integral f c b := by sorry

theorem integral_triangle_ineq (f : Real → Real) (a b: Real) :
    (Integral f a b).abs ≤ (Integral (fun t ↦ (f t).abs) a c).abs := by sorry

theorem integral_const (a b c : Real) : Integral (fun t ↦ c) a b = c * (b - a) := by sorry

theorem integral_sub (f g : Real → Real) (a b : Real) :
    Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by sorry

theorem div_abs_le (a b c : Real) (h : a.abs ≤ b.abs) : (a / c).abs ≤ (b / c).abs := by sorry

example (a b : Real) : a * b / b = a := by
  rw [mul_div_cancel]

theorem aux (a b c : Real) : a * (b + c - b) / c = a := sorry

def InInterval (a b : Real) (x : Real) : Prop :=
  if a ≤ b then a ≤ x ∧ x ≤ b else b ≤ x ∧ x ≤ a

def InInterval_abs {x h t : Real} : InInterval x (x + h) t → (t - x).abs ≤ h.abs := by
  sorry

-- このままだとa < bの場合のみになるので、そこを工夫する必要ある？
theorem integral_monotone' (f g : Real → Real) (a b : Real)
    (h : ∀ x, InInterval a b x → 0 ≤ f x ∧ 0 ≤ g x ∧ f x ≤ g x) :
    (Integral f a b).abs ≤ (Integral g a b).abs := by sorry


-- 微積分学の基本定理
theorem main (f : Real → Real) (a x : Real) (hf : Continuous f) :
    deriv (fun x ↦ Integral f a x) x = f x := by
  let F := fun x ↦ (Integral f a x)
  have h₀ : ∀ x y, F x - F y = Integral f y x := by
    intro x y
    apply integral_sub_interval
  have h₁ : ∀ x y f, abs (Integral f x y) ≤ abs (Integral (fun t ↦ abs (f t)) x y) := by
    intros x y f
    apply integral_triangle_ineq
  have h₂ : ∀ h, h ≠ 0 →
      ((F (x + h) - F x) / h - f x).abs ≤
        ((Integral (fun t ↦ (f t - f x).abs) x (x + h)) / h).abs := by
    intro h hnez
    calc
      ((F (x + h) - F x) / h - f x).abs = (Integral f x (x + h) / h - f x).abs := by rw [h₀]
      _ = (Integral f x (x + h) / h - (f x) * (x + h - x) / h).abs := by
        rw [aux (f x)]
      _ = (Integral f x (x + h) / h - Integral (fun t ↦ f x) x (x + h) / h).abs := by
        rw [integral_const _ _ (f x)]
      _ ≤ ((Integral (fun t ↦ (f t - f x).abs) x (x + h)) / h).abs := by
        rw [div_sub_div]
        rw [← integral_sub]
        apply div_abs_le
        apply h₁ x (x + h) (fun t ↦ f t - f x)
  have h₃ : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ t, (t - x).abs < δ → (f t - f x).abs < ε := by
    apply hf
  have h₄ : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ h, (0 < h.abs ∧ h.abs < δ) → ((F (x + h) - F x) / h - f x).abs ≤ ε := by
    intro ε hε
    rcases h₃ ε hε with ⟨δ, hδ⟩
    apply Exists.intro δ
    constructor
    · exact hδ.1
    · intro h ⟨hgt, hlt⟩
      refine le_trans (h₂ h (nez_of_abs_pos hgt)) ?h
      calc
        (Integral (fun t ↦ (f t - f x).abs) x (x + h) / h).abs ≤
            (Integral (fun t ↦ ε) x (x + h) / h).abs := by
          apply div_abs_le
          apply integral_monotone'
          intro t ht
          constructor
          · exact abs_nonneg
          · constructor
            · exact le_of_lt 0 ε hε
            · apply le_of_lt
              apply hδ.2
              apply le_lt_trans _ _ _ (InInterval_abs ht) hlt
        _ ≤ (ε * h / h).abs := by rw [integral_const]; rw [add_sub_cancel]; apply le_refl
        _ = ε := by rw [mul_div_cancel]; apply pos_abs hε
  have h₅ : limit (fun h ↦ (F (x + h) - F x) / h) 0 = f x := by
    apply limit_eq
    rw [limit_iff_le]
    simp at *
    exact h₄
  rw [deriv_iff]
  exact h₅
