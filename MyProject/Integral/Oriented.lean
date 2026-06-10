import MyProject.Integral.IntervalAdd

noncomputable section

-- ============================================================
-- 向き付き積分
-- ============================================================

/-- 向き付き積分：a > b のときは符号を反転する。
区間の加法性 oint_add_integral / oint_sub_interval が a b c の順序によらず成立する。 -/
noncomputable def OIntegral (f : Real → Real) (a b : Real) : Real :=
  if a ≤ b then Integral f a b else -(Integral f b a)

theorem OIntegral_of_le (f : Real → Real) {a b : Real} (h : a ≤ b) :
    OIntegral f a b = Integral f a b := by
  show (if a ≤ b then Integral f a b else -(Integral f b a)) = Integral f a b
  rw [if_pos h]

theorem OIntegral_of_ge (f : Real → Real) {a b : Real} (h : b ≤ a) :
    OIntegral f a b = -(Integral f b a) := by
  cases Classical.em (a ≤ b) with
  | inl hab =>
    have heq : a = b := LinearOrderedField.le_asymm a b hab h
    subst heq
    show (if a ≤ a then Integral f a a else -(Integral f a a)) = -(Integral f a a)
    rw [if_pos (le_refl a), integral_self, neg_zero]
  | inr hnab =>
    show (if a ≤ b then Integral f a b else -(Integral f b a)) = -(Integral f b a)
    rw [if_neg hnab]

-- 向きの反転
theorem OIntegral_swap (f : Real → Real) (a b : Real) :
    OIntegral f a b = -(OIntegral f b a) := by
  cases LinearOrderedField.le_total a b with
  | inl h => rw [OIntegral_of_le f h, OIntegral_of_ge f h, neg_neg]
  | inr h => rw [OIntegral_of_ge f h, OIntegral_of_le f h]

theorem OIntegral_self (f : Real → Real) (a : Real) : OIntegral f a a = 0 := by
  rw [OIntegral_of_le f (le_refl a)]
  exact integral_self f a

-- 向き付き積分の加法性（a, b, c の順序によらず成立）
theorem oint_add_integral (f : Real → Real) (hint : ∀ u v, IsIntegrable f u v)
    (a b c : Real) :
    OIntegral f a b + OIntegral f b c = OIntegral f a c := by
  cases LinearOrderedField.le_total a b with
  | inl hab =>
    cases LinearOrderedField.le_total b c with
    | inl hbc =>
      -- a ≤ b ≤ c
      rw [OIntegral_of_le f hab, OIntegral_of_le f hbc, OIntegral_of_le f (le_trans hab hbc)]
      exact interval_add_integral f a b c hab hbc (hint a b) (hint b c)
    | inr hcb =>
      cases LinearOrderedField.le_total a c with
      | inl hac =>
        -- a ≤ c ≤ b
        rw [OIntegral_of_le f hab, OIntegral_of_ge f hcb, OIntegral_of_le f hac,
            ← interval_add_integral f a c b hac hcb (hint a c) (hint c b)]
        exact add_neg_cancel_right _ _
      | inr hca =>
        -- c ≤ a ≤ b
        rw [OIntegral_of_le f hab, OIntegral_of_ge f hcb, OIntegral_of_ge f hca,
            ← interval_add_integral f c a b hca hab (hint c a) (hint a b), neg_add_distrib]
        exact add_neg_neg_cancel _ _
  | inr hba =>
    cases LinearOrderedField.le_total b c with
    | inl hbc =>
      cases LinearOrderedField.le_total a c with
      | inl hac =>
        -- b ≤ a ≤ c
        rw [OIntegral_of_ge f hba, OIntegral_of_le f hbc, OIntegral_of_le f hac,
            ← interval_add_integral f b a c hba hac (hint b a) (hint a c)]
        exact neg_add_cancel_left _ _
      | inr hca =>
        -- b ≤ c ≤ a
        rw [OIntegral_of_ge f hba, OIntegral_of_le f hbc, OIntegral_of_ge f hca,
            ← interval_add_integral f b c a hbc hca (hint b c) (hint c a), neg_add_distrib]
        exact neg_neg_cancel_left _ _
    | inr hcb =>
      -- c ≤ b ≤ a
      rw [OIntegral_of_ge f hba, OIntegral_of_ge f hcb,
          OIntegral_of_ge f (le_trans hcb hba),
          ← interval_add_integral f c b a hcb hba (hint c b) (hint b a), neg_add_distrib]
      exact add_comm _ _

-- 区間の差：削除した integral_sub_interval の向き付き版（順序の仮定なしで成立）
theorem oint_sub_interval (f : Real → Real) (hint : ∀ u v, IsIntegrable f u v)
    (a b c : Real) :
    OIntegral f a b - OIntegral f a c = OIntegral f c b := by
  rw [← oint_add_integral f hint a c b]
  exact add_sub_cancel _ _

