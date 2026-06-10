import MyProject.Integral.Linearity
import MyProject.Integral.Interval

noncomputable section

open Real Classical Range

-- 積分の単調性
-- 極限の単調性を使いたい

theorem cast_le (n m : Nat) : n ≤ m → (n : Real) ≤ m := by
  intro h
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · subst heq; exact le_refl _
  · exact Real.le_of_lt (cast_lt n m hlt)

theorem nonneg_nonneg_div_nonneg (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ a / b := by
  cases Classical.em (b = 0) with
  | inl heq =>
    have : a / b = 0 := by
      show a * Field.inv b = 0
      calc a * Field.inv b = a * 0 := by rw [heq, Real.inv_zero]
        _ = 0 * a := by rw [MulCommMonoid.mul_comm]
        _ = 0 := zero_mul' a
    rw [this]; exact le_refl 0
  | inr hne =>
    exact nonneg_div_nonneg a b ha ⟨hb, fun h => hne h.symm⟩

theorem mul_div_assoc (a b c : Real) : a * b / c = a * (b / c) := by
  show a * b * Field.inv c = a * (b * Field.inv c)
  exact MulCommMonoid.mul_assoc a b (Field.inv c)

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
      have hRS := hh 0 Δ ξ hr hd
      have hRS0 : RiemannSum f Δ ξ = 0 := rfl
      rw [hRS0] at hRS
      have h0I : ((0 : Real) - I) = -I := by
        show (0 : Real) + -I = -I
        calc (0 : Real) + -I = -I + (0 : Real) := AddCommGroup.add_comm _ _
          _ = -I := add_zero _
      rw [h0I, pos_abs hε] at hRS
      exact hRS.2 rfl
    | inr hne =>
      have hab_lt : a < b := ⟨h, hne⟩
      have hba_pos : 0 < b - a := (pos_iff_lt a b).mp hab_lt
      have hba_div : 0 < (b - a) / δ := pos_div_pos _ _ hba_pos hδ
      let m := ceil ((b - a) / δ)
      have hm_lt : (b - a) / δ < (m : Real) := ceil_lt _
      have hm_pos : 0 < (m : Real) := lt_trans 0 ((b - a) / δ) (m : Real) hba_div hm_lt
      have hm_nonneg : 0 ≤ (m : Real) := Real.le_of_lt hm_pos
      have hba_nn : 0 ≤ b - a := (nonneg_iff_le a b).mp h
      let Δ : Partition m a b := {
        points := fun i => a + (i.val : Real) * (b - a) / (m : Real),
        increase := by
          intro i; apply add_left_le; apply div_right_le
          · exact hm_nonneg
          · apply nonneg_mul_nonneg
            exact hba_nn
            exact Real.le_of_lt (cast_lt i.val (i.val + 1) (Nat.lt_succ_self _))
        left := by
          show a + (0 : Real) * (b - a) / (m : Real) = a
          rw [zero_mul', zero_div, add_zero]
        right := by
          show a + (m : Real) * (b - a) / (m : Real) = b
          rw [mul_div_cancel' (m : Real) (b - a) hm_pos.2.symm, add_sub_cancel' a b]
      }
      let ξ : Range m → Real := fun i => a + (i.val : Real) * (b - a) / (m : Real)
      have hr : Δ.IsRepr ξ := by
        apply Partition.le_isrepr; intro i; exact ⟨le_refl _, Δ.increase i⟩
      have hd : Partition.diam Δ < δ := by
        apply fmax'_lt m _ δ hδ
        intro i
        show (a + ((i.val + 1 : Nat) : Real) * (b - a) / ↑m) -
             (a + ↑i.val * (b - a) / ↑m) < δ
        rw [add_sub_add' a, div_sub_div, mul_sub_mul]
        show ((Nat.cast (i.val + 1) : Real) - ↑i.val) * (b - a) / ↑m < δ
        rw [show ((Nat.cast (i.val + 1) : Real)) = (i.val : Real) + 1 from cast_addone_val m i,
            add_sub_cancel (i.val : Real) 1, one_mul]
        exact (div_lt_iff (b - a) δ (m : Real) hδ hm_pos).mp hm_lt
      have habs := hh m Δ ξ hr hd
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
      exact h2.2 (LinearOrderedField.le_asymm _ _ h2.1 hRS_nn)

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
