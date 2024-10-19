import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 積分の区間についての加法性

-- リーマン可積分なら有界であることを示し、それを用いる。

theorem integrable_bounded (f : Real → Real) (a b : Real) (i : Real)
  (h : IsIntegral f a b i) : ∃ M, ∀ x, InInterval a b x → abs (f x) ≤ M := by
  sorry

theorem interval_add_integrable (f : Real → Real) (a b c : Real)
  (hab : IsIntegral f a b i) (hbc : IsIntegral f b c j) :
  IsIntegral f a c (i + j) := by sorry
  -- intro ε hε
  -- rcases integrable_bounded f a b i hab with ⟨Mab, hab'⟩
  -- rcases integrable_bounded f b c j hbc with ⟨Mbc, hbc'⟩
  -- rcases hab (ε / 3) (pos_div_pos ε 3 hε _) with ⟨δab, hab⟩
  -- rcases hbc (ε / 3) (pos_div_pos ε 3 hε _) with ⟨δbc, hbc⟩
  -- let δM := (ε / 3) / (Mab + Mbc)
  -- apply Exists.intro (min δab (min δbc δM))
  -- constructor
  -- · apply min_pos; exact hab.1; sorry  -- exact hbc.1
  -- · intros n Δ ξ h h'
  --   sorry
    -- let k : Nat := sorry
    -- let Δ₁ : Partition _ a b := by apply Partition.mk; sorry; sorry; sorry; sorry
    -- let ξ₁ := fun i => sorry
    -- let Δ₂ := Partition.mk (fun i => sorry)
    -- let ξ₂ := fun i => sorry
    -- have : RiemannSum f a c n Δ ξ = RiemannSum f a b n Δ₁ ξ₁ + RiemannSum f b c n Δ₂ ξ₂ := by sorry
    -- 上は等式にはできない。代表点をうまく選んでも無理。誤差を許容する必要がある。


theorem interval_add_integral (f : Real → Real) (a b c : Real) :
  Integral f a b + Integral f b c = Integral f a c := by
  symm
  rw [← IsIntegral_iff]
  have hab : IsIntegral f a b (Integral f a b) := by rw [IsIntegral_iff]
  have hbc : IsIntegral f b c (Integral f b c) := by rw [IsIntegral_iff]
  apply interval_add_integrable _ _ _ _ hab hbc

theorem integral_sub_interval' (f : Real → Real) (a b c : Real) :
    Integral f a b - Integral f a c = Integral f c b := by sorry
