import MyProject.Integral.Linearity

noncomputable section

open Real Classical Range

-- 積分の単調性
-- 極限の単調性を使いたい

theorem cast_le (n m : Nat) : n ≤ m → (n : Real) ≤ m := by
  intro h
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · subst heq; exact le_refl _
  · exact le_of_lt (cast_lt n m hlt)

theorem increse' (n : Nat) (a b : Real) (bnonneg : 0 ≤ b) :
  ∀ i : Range n, a + i.incl.val * b ≤ a + i.addone.val * b := by
  intro i
  apply add_left_le
  apply nonneg_mul_nonneg _ _ _ bnonneg
  apply cast_le
  exact Nat.le_succ i.val

private theorem nat_ne_zero_of_pos_cast (m : Nat) (h : 0 < (m : Real)) : m ≠ 0 := by
  intro hm; subst hm; exact h.2 rfl

theorem integral_nonneg (f : Real → Real) (a b : Real)
    (h : a ≤ b) (fnn : ∀ x, InInterval a b x → 0 ≤ f x)
    (hf : IsIntegrable f a b) : 0 ≤ Integral f a b := by
  obtain ⟨I, hI⟩ := hf
  have hI_eq : Integral f a b = I := IsIntegral_iff _ _ _ _ h hI
  rw [hI_eq]
  cases Classical.em (0 ≤ I) with
  | inl hge => exact hge
  | inr hlt =>
    exfalso
    have hI_neg : I < 0 := ne_le_lt 0 I hlt
    have hε : 0 < -I := neg_neg_pos I hI_neg
    obtain ⟨δ, hδ, hh⟩ := hI (-I) hε
    cases Classical.em (a = b) with
    | inl heq =>
      subst heq
      let Δ : Partition 0 a a := ⟨fun _ => a,
        fun i => absurd i.property (Nat.not_lt_zero _), rfl, rfl⟩
      let ξ : Range 0 → Real := fun i => absurd i.property (Nat.not_lt_zero _)
      have hr : Δ.IsRepr ξ := fun i => absurd i.property (Nat.not_lt_zero _)
      have hd : Partition.diam Δ < δ := by show fmax' 0 _ < δ; exact hδ
      have hRS := hh ⟨0, Δ, ξ, hr⟩ hd
      have hRS0 : RiemannSum f Δ ξ = 0 := rfl
      rw [hRS0] at hRS
      have h0I : ((0 : Real) - I) = -I := by
        show (0 : Real) + -I = -I
        calc (0 : Real) + -I = -I + (0 : Real) := add_comm _ _
          _ = -I := add_zero _
      rw [h0I, pos_abs hε] at hRS
      exact hRS.2 rfl
    | inr hne =>
      obtain ⟨⟨m, Δ, ξ, hr⟩, hd⟩ := exists_fine_partition a b δ h hδ
      have habs := hh ⟨m, Δ, ξ, hr⟩ hd
      have hRS_nn : 0 ≤ RiemannSum f Δ ξ :=
        RiemannSum_nonneg f Δ ξ fnn hr
      have h1 : RiemannSum f Δ ξ - I < -I :=
        le_lt_trans (le_abs _) habs
      have h2 : RiemannSum f Δ ξ < 0 := by
        have := add_left_lt I (RiemannSum f Δ ξ - I) (-I) h1
        rw [show I + (RiemannSum f Δ ξ - I) = RiemannSum f Δ ξ from
            add_sub_cancel' I (RiemannSum f Δ ξ),
            show I + -I = (0 : Real) from sub_self I] at this
        exact this
      exact h2.2 (le_antisymm _ _ h2.1 hRS_nn)

theorem integral_monotone (f g : Real → Real) (a b : Real)
    (h : a ≤ b) (h' : ∀ x, InInterval a b x → f x ≤ g x)
    (hf : IsIntegrable f a b) (hg : IsIntegrable g a b) :
    Integral f a b ≤ Integral g a b := by
  rw [← le_sub, ← sub_integral g f a b h hg hf]
  apply integral_nonneg _ _ _ h
  · intro x hx
    rw [le_sub]
    exact h' x hx
  · apply integrable_sub
    exact hg
    exact hf

theorem integral_monotone' (f g : Real → Real) (a b : Real)
    (hab : a ≤ b)
    (hf : ∃ i, IsIntegral f a b i)
    (hg : ∃ i, IsIntegral g a b i)
    (fnonneg : ∀ x, 0 ≤ f x)
    (gnonneg : ∀ x, 0 ≤ g x)
    (h : ∀ x, InInterval a b x → f x ≤ g x) :
    (Integral f a b).abs ≤ (Integral g a b).abs := by
  have hf_nn : 0 ≤ Integral f a b :=
    integral_nonneg f a b hab (fun x _ => fnonneg x) hf
  have hg_nn : 0 ≤ Integral g a b :=
    integral_nonneg g a b hab (fun x _ => gnonneg x) hg
  rw [nonneg_abs hf_nn, nonneg_abs hg_nn]
  exact integral_monotone f g a b hab h hf hg
