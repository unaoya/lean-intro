import MyProject.Real.Order

noncomputable section

open Real Classical
open Range

-- 上限の近似

theorem sup_near (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ B, ∀ x, S x → x ≤ B)
    (γ : Real) (hγ : 0 < γ) : ∃ x, S x ∧ Real.sup S hne hbdd - γ < x := by
  cases Classical.em (∃ x, S x ∧ Real.sup S hne hbdd - γ < x) with
  | inl hex => exact hex
  | inr hnex =>
    exfalso
    have hub : ∀ x, S x → x ≤ Real.sup S hne hbdd - γ := fun x hx =>
      (Classical.em (Real.sup S hne hbdd - γ < x)).elim
        (fun hlt => absurd ⟨x, hx, hlt⟩ hnex) not_lt_imp_le
    have hle := Real.sup_lub S hne hbdd _ hub
    have h1 := LinearOrderedField.add_le_add (Real.sup S hne hbdd)
      (Real.sup S hne hbdd - γ) (-(Real.sup S hne hbdd)) hle
    rw [AddCommGroup.add_neg] at h1
    rw [show Real.sup S hne hbdd - γ + -(Real.sup S hne hbdd) = -γ from by
          show Real.sup S hne hbdd + -γ + -(Real.sup S hne hbdd) = -γ
          rw [add_comm (Real.sup S hne hbdd) (-γ),
              add_assoc, AddCommGroup.add_neg, AddCommGroup.add_zero]] at h1
    have h2 : γ ≤ 0 :=
      calc γ = 0 + γ := (AddCommGroup.zero_add γ).symm
        _ ≤ -γ + γ := LinearOrderedField.add_le_add 0 (-γ) γ h1
        _ = 0 := AddCommGroup.neg_add γ
    exact hγ.2 (LinearOrderedField.le_asymm 0 γ hγ.1 h2)

#check (inferInstance : Max Real)

#check "all done"
