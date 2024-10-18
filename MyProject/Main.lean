import MyProject.Deriv
import MyProject.Integral

open Real Classical

-- 微積分学の基本定理
theorem main' (f : Real → Real) (a x : Real) (hf : Continuous f) :
    let F := fun x ↦ (Integral f a x); HasDerivAt F (f x) x := by
  let F := fun x ↦ (Integral f a x)
  have h₀ (x y : Real) : F x - F y = Integral f y x := by apply integral_sub_interval
  have h₁ {x y f} (hf : Continuous f) : abs (Integral f x y) ≤ abs (Integral (fun t ↦ abs (f t)) x y) :=
    integral_triangle_ineq (continuous_integrable f x y hf)
  have h₂ : ∀ h, h ≠ 0 →
      ((F (x + h) - F x) / h - f x).abs ≤
        ((Integral (fun t ↦ (f t - f x).abs) x (x + h)) / h).abs := by
    intro h _
    calc
      ((F (x + h) - F x) / h - f x).abs = (Integral f x (x + h) / h - f x).abs := by rw [h₀]
      _ = (Integral f x (x + h) / h - (f x) * (x + h - x) / h).abs := by rw [aux]
      _ = (Integral f x (x + h) / h - Integral (fun _ ↦ f x) x (x + h) / h).abs := by rw [integral_const]
      _ ≤ ((Integral (fun t ↦ (f t - f x).abs) x (x + h)) / h).abs := by
        rw [div_sub_div, ← integral_sub]
        exact div_abs_le
          (h₁ (continuous_sub f (fun _ ↦ f x) hf (continuous_const (f x))))
  have h₃ : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ t, (t - x).abs < δ → (f t - f x).abs < ε := by apply hf
  have h₄ : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ h, (0 < h.abs ∧ h.abs < δ) → ((F (x + h) - F x) / h - f x).abs ≤ ε := by
    intro ε hε
    rcases h₃ ε hε with ⟨δ, hδ⟩
    refine Exists.intro δ ⟨hδ.1, ?hh⟩
    · intro h ⟨hgt, hlt⟩
      refine le_trans (h₂ h (nez_of_abs_pos hgt)) ?h
      calc
        (Integral (fun t ↦ (f t - f x).abs) x (x + h) / h).abs ≤
            (Integral (fun _ ↦ ε) x (x + h) / h).abs := by
          apply div_abs_le
          apply integral_monotone'
          · intro x; apply abs_nonneg
          · exact fun _ ↦ le_of_lt hε
          · exact fun t ht ↦ le_of_lt (hδ.2 _ (le_lt_trans (InInterval_abs ht) hlt))
        _ = ε := by rw [integral_const, add_sub_cancel, mul_div_cancel]; apply pos_abs hε
  have : IsLimAt (fun h ↦ (F (x + h) - F x) / h) (f x) 0 := by -- showにしたいが
    exact limit_at0_iff_le _ _ h₄
  exact this

theorem main (f : Real → Real) (a x : Real) (hf : Continuous f) :
    let F := fun x ↦ (Integral f a x);
    deriv F x (main' f a x hf) = f x := rfl
