import MyProject.Lemmas

-- 古典論理、選択公理（無限直積が空でない、とは違う、型理論的な何か？）を使う
-- 全ての命題に真偽が決まるか？排中律？

noncomputable section

open Real Classical

-- 解析入門の実数の公理が全て成立することを確認し、名前をつける

-- 極限の定義

-- 関数の極限
def IsLimAt (f : Real → Real) (l : Real) (a : Real) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) < ε

def HasLimAt (f : Real → Real) (a : Real) : Prop :=
  ∃ l, IsLimAt f l a

def limit (f : Real → Real) (a : Real) (hf : HasLimAt f a) : Real :=
  choose hf

theorem limit_eq (f : Real → Real) (a : Real) (hf : HasLimAt f a) : IsLimAt f (limit f a hf) a :=
  choose_spec hf

def limit' (f : Real → Real) (a : Real) {l : Real} (_hf : IsLimAt f l a) : Real := l

-- Helper: sub_eq_zero_iff
private theorem sub_eq_zero_imp (a b : Real) (h : a - b = 0) : a = b := by
  have h1 : a + -b + b = (0 : Real) + b := congrArg (· + b) h
  rw [add_assoc, AddCommGroup.neg_add, AddCommGroup.add_zero] at h1
  rw [h1, add_comm, add_zero]

-- Helper: abs is positive when argument is nonzero
private theorem abs_pos_of_ne {x : Real} (h : x ≠ 0) : 0 < abs x := by
  cases le_total (0 : Real) x with
  | inl hle =>
    have hlt : 0 < x := lt_of_le_of_ne hle (fun heq => h heq.symm)
    rw [pos_abs hlt]; exact hlt
  | inr hle =>
    have hlt : x < 0 := lt_of_le_of_ne hle h
    have hneg_pos : 0 < -x := neg_neg_pos x hlt
    have hle2 : x ≤ -x := le_trans hle (le_of_lt hneg_pos)
    rw [show abs x = -x from by show (if x ≤ -x then -x else x) = -x; rw [if_pos hle2]]
    exact hneg_pos

-- PROOF 1: limit_unique
theorem limit_unique (f : Real → Real) (l₁ l₂ : Real) (a : Real)
    (h₁ : IsLimAt f l₁ a) (h₂ : IsLimAt f l₂ a) : l₁ = l₂ := by
  cases Classical.em (l₁ = l₂) with
  | inl heq => exact heq
  | inr hne =>
    exfalso
    -- l₁ - l₂ ≠ 0
    have hsub_ne : l₁ - l₂ ≠ 0 := fun heq => hne (sub_eq_zero_imp l₁ l₂ heq)
    -- ε = |l₁ - l₂| / 2 > 0
    have habs_pos : 0 < abs (l₁ - l₂) := abs_pos_of_ne hsub_ne
    have heps := pos_half (abs (l₁ - l₂)) habs_pos
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h₁ (abs (l₁ - l₂) / 2) heps
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := h₂ (abs (l₁ - l₂) / 2) heps
    -- δ = min δ₁ δ₂
    have hδ_pos : 0 < min δ₁ δ₂ := min_pos δ₁ δ₂ hδ₁_pos hδ₂_pos
    -- x = a + (min δ₁ δ₂)/2
    have hδ_half_pos : 0 < min δ₁ δ₂ / 2 := pos_half (min δ₁ δ₂) hδ_pos
    -- |x - a| = (min δ₁ δ₂)/2 where x = a + (min δ₁ δ₂)/2
    have hxa_eq : a + min δ₁ δ₂ / 2 - a = min δ₁ δ₂ / 2 := add_sub_cancel a (min δ₁ δ₂ / 2)
    have hxa_abs : abs (a + min δ₁ δ₂ / 2 - a) = min δ₁ δ₂ / 2 := by
      rw [hxa_eq]; exact pos_abs hδ_half_pos
    -- 0 < |x - a|
    have hxa_pos : 0 < abs (a + min δ₁ δ₂ / 2 - a) := by rw [hxa_abs]; exact hδ_half_pos
    -- (min δ₁ δ₂)/2 < min δ₁ δ₂
    have hδ_half_lt : min δ₁ δ₂ / 2 < min δ₁ δ₂ := half_lt hδ_pos
    -- |x - a| < δ₁ and |x - a| < δ₂
    have hxa_lt_δ₁ : abs (a + min δ₁ δ₂ / 2 - a) < δ₁ := by
      rw [hxa_abs]
      exact lt_le_trans _ _ δ₁ hδ_half_lt (min_left_le δ₁ δ₂)
    have hxa_lt_δ₂ : abs (a + min δ₁ δ₂ / 2 - a) < δ₂ := by
      rw [hxa_abs]
      exact lt_le_trans _ _ δ₂ hδ_half_lt (min_right_le δ₁ δ₂)
    -- |f x - l₁| < ε and |f x - l₂| < ε
    have hfx1 := hδ₁ (a + min δ₁ δ₂ / 2) ⟨hxa_pos, hxa_lt_δ₁⟩
    have hfx2 := hδ₂ (a + min δ₁ δ₂ / 2) ⟨hxa_pos, hxa_lt_δ₂⟩
    -- |l₁ - l₂| ≤ |l₁ - fx| + |fx - l₂| < ε + ε = |l₁ - l₂| で矛盾
    have hcontra : abs (l₁ - l₂) < abs (l₁ - l₂) :=
      le_lt_trans (abs_sub_le_add l₁ (f (a + min δ₁ δ₂ / 2)) l₂)
        (by rw [abs_sub_comm l₁ (f (a + min δ₁ δ₂ / 2))]
            calc abs (f (a + min δ₁ δ₂ / 2) - l₁) + abs (f (a + min δ₁ δ₂ / 2) - l₂)
                < abs (l₁ - l₂) / 2 + abs (l₁ - l₂) / 2 := lt_add_lt _ _ _ _ hfx1 hfx2
              _ = abs (l₁ - l₂) := half_add _)
    exact hcontra.2 rfl

-- PROOF 2: limit_eq'
theorem limit_eq' (f : Real → Real) (a : Real) (l : Real) (h : IsLimAt f l a) : limit f a ⟨l, h⟩ = l := by
  have hfla : HasLimAt f a := ⟨l, h⟩
  have hspec : IsLimAt f (choose hfla) a := choose_spec hfla
  exact limit_unique f (choose hfla) l a hspec h

-- PROOF 3: limit_eq_iff
theorem limit_eq_iff (f : Real → Real) (a : Real) (l : Real) (hf : HasLimAt f a) : IsLimAt f l a ↔ limit f a hf = l := by
  rw [limit]
  constructor
  · intro hlim
    exact limit_unique f (choose hf) l a (choose_spec hf) hlim
  · intro heq
    rw [← heq]
    exact choose_spec hf

theorem limit_iff (f : Real → Real) (a : Real) (f' : Real) (hf : HasLimAt f a) : IsLimAt f f' a ↔ limit f a hf = f' := by
  rw [limit_eq_iff]

-- PROOF 4: limit_iff_le
theorem limit_iff_le (f : Real → Real) (a : Real) (l : Real)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x - a) ∧ abs (x - a) < δ → abs (f x - l) ≤ ε) : IsLimAt f l a := by
  intro ε hε
  have hε2 := pos_half ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h (ε / 2) hε2
  exact ⟨δ, hδ_pos, fun x hx => by
    have hle := hδ x hx
    exact le_lt_trans hle (half_lt hε)⟩

-- PROOF 5: limit_at0_iff_le
theorem limit_at0_iff_le (f : Real → Real) (l : Real)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x, 0 < abs (x) ∧ abs (x) < δ → abs (f x - l) ≤ ε) : IsLimAt f l 0 := by
  apply limit_iff_le
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
  exact ⟨δ, hδ_pos, fun x hx => by
    have : abs (x - 0) = abs x := sub_zero_abs x
    rw [this] at hx
    exact hδ x hx⟩

def Continuous (f : Real → Real) : Prop :=
  ∀ a, ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

-- PROOF 6: continuous_sub
theorem continuous_sub (f g : Real → Real) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun t ↦ f t - g t) := by
  intro a ε hε
  have hε2 := pos_half ε hε
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hf a (ε / 2) hε2
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hg a (ε / 2) hε2
  refine ⟨min δ₁ δ₂, min_pos δ₁ δ₂ hδ₁_pos hδ₂_pos, fun x hx => ?_⟩
  have hx1 : abs (x - a) < δ₁ :=
    lt_le_trans (abs (x - a)) (min δ₁ δ₂) δ₁ hx (min_left_le δ₁ δ₂)
  have hx2 : abs (x - a) < δ₂ :=
    lt_le_trans (abs (x - a)) (min δ₁ δ₂) δ₂ hx (min_right_le δ₁ δ₂)
  have hf_bound := hδ₁ x hx1
  have hg_bound := hδ₂ x hx2
  -- f x - g x - (f a - g a) = (f x - f a) + (-(g x) - -(g a))
  have hsplit : (fun t ↦ f t - g t) x - (fun t ↦ f t - g t) a = (f x - f a) + (-(g x) - -(g a)) :=
    show f x + -(g x) - (f a + -(g a)) = (f x - f a) + (-(g x) - -(g a)) from
    add_sub_add (f x) (-(g x)) (f a) (-(g a))
  rw [hsplit]
  have habs_neg_g : abs (-(g x) - -(g a)) = abs (g x - g a) := neg_sub_neg_abs (g x) (g a)
  have htri := abs_triangle (f x - f a) (-(g x) - -(g a))
  calc abs ((f x - f a) + (-(g x) - -(g a)))
      ≤ abs (f x - f a) + abs (-(g x) - -(g a)) := htri
    _ = abs (f x - f a) + abs (g x - g a) := by rw [habs_neg_g]
    _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ hf_bound hg_bound
    _ = ε := half_add ε

-- PROOF 7: continuous_const
theorem continuous_const (c : Real) : Continuous (fun _ ↦ c) := by
  intro a ε hε
  exact ⟨1, zero_lt_one, fun x _ => by
    show abs (c - c) < ε
    rw [sub_self c, abs_zero]
    exact hε⟩
