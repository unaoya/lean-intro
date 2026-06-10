import MyProject.Integral.RiemannSum

noncomputable section

open Real Classical

-- 積分の定義
def IsIntegral (f : Real → Real) (a b : Real) (i : Real) : Prop :=
  ∀ (ε : Real), 0 < ε → ∃ (δ : Real), 0 < δ ∧ ∀ n : Nat, ∀ Δ : Partition n a b, ∀ ξ : Range n → Real,
    Δ.IsRepr ξ → (Partition.diam Δ) < δ →
    abs (RiemannSum f Δ ξ - i) < ε

theorem sub_zero_eq (x y : Real) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    have := (add_sub_cancel' y x).symm
    rw [h, add_zero] at this
    exact this
  · intro h
    rw [h, sub_self]

theorem lt_epsilon_zero (x : Real) (h : ∀ ε, 0 < ε → x.abs < ε) : x = 0 := by
  cases Classical.em (x = 0) with
  | inl heq => exact heq
  | inr hne =>
    exfalso
    have hpos : 0 < x.abs := by
      constructor
      · exact abs_nonneg
      · intro heq
        exact hne (by
          have h1 := le_abs x
          have h2 := neg_le_abs x
          rw [← heq] at h1 h2
          have h3 := neg_neg_nonneg _ h2
          rw [neg_neg] at h3
          exact LinearOrderedField.le_asymm _ _ h1 h3)
    exact (lt_neq _ _ (h x.abs hpos)) rfl

-- Helper: 0 ≤ (n : Real) for Nat n
private theorem my_cast_nonneg (n : Nat) : (0 : Real) ≤ (n : Real) := by
  cases n with
  | zero => exact le_refl 0
  | succ m => exact Real.le_of_lt (cast_lt 0 (m + 1) (Nat.zero_lt_succ m))

-- Helper: (n : Real) ≤ (n + 1 : Real)
private theorem cast_le_succ (n : Nat) : (n : Real) ≤ ((n + 1 : Nat) : Real) :=
  Real.le_of_lt (cast_lt n (n + 1) (Nat.lt_succ_self n))


-- Helper: m ≠ 0 when 0 ≤ x < (m : Real)
private theorem nat_ne_zero_of_nonneg_lt (x : Real) (m : Nat) (hx : 0 ≤ x) (hlt : x < (m : Real)) :
    m ≠ 0 := by
  intro hm; subst hm; exact (le_lt_trans hx hlt).2 rfl

-- Helper: 0 < (m : Real) for m ≠ 0
private theorem cast_pos_of_ne (m : Nat) (hm : m ≠ 0) : (0 : Real) < (m : Real) := by
  cases m with
  | zero => exact absurd rfl hm
  | succ k => exact cast_pos_succ k

-- Equal partition: points i = a + i * (b-a) / m
def equalPartition (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) : Partition m a b where
  points := fun i => a + (i.val : Real) * (b - a) / (m : Real)
  increase := by
    intro i
    apply add_left_le
    apply div_right_le
    · exact cast_pos_of_ne m hm
    · exact nonneg_mul_nonneg _ _ _ ((nonneg_iff_le a b).mp hab) (cast_le_succ i.val)
  left := by
    show a + (0 : Real) * (b - a) / (m : Real) = a
    rw [zero_mul', zero_div, add_zero]
  right := by
    show a + (m : Real) * (b - a) / (m : Real) = b
    have hm' : (m : Real) ≠ (0 : Real) := by
      intro h; apply hm
      cases m with
      | zero => rfl
      | succ n => exact absurd h (cast_lt 0 (n + 1) (Nat.zero_lt_succ n)).2.symm
    rw [mul_div_cancel' (m : Real) (b - a) hm']
    exact add_sub_cancel' a b

-- Length of each subinterval = (b-a)/m
theorem equalPartition_length (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b)
    (i : Range m) :
    (equalPartition m a b hm hab).length i = (b - a) / (m : Real) := by
  show (a + ((i.val + 1 : Nat) : Real) * (b - a) / (m : Real)) -
       (a + (i.val : Real) * (b - a) / (m : Real)) = (b - a) / (m : Real)
  rw [add_sub_add' a, div_sub_div, mul_sub_mul]
  show (((i.val + 1 : Nat) : Real) - (i.val : Real)) * (b - a) / (m : Real) = (b - a) / (m : Real)
  rw [show ((Nat.cast (i.val + 1) : Real)) = (i.val : Real) + 1 from cast_addone_val m i]
  rw [add_sub_cancel (i.val : Real) 1, one_mul]

-- Repr: ξ i = left endpoint of each subinterval
def equalPartitionRepr (m : Nat) (a b : Real) (_hm : m ≠ 0) (_hab : a ≤ b) :
    Range m → Real :=
  fun i => a + (i.val : Real) * (b - a) / (m : Real)

theorem equalPartitionRepr_isrepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    (equalPartition m a b hm hab).IsRepr (equalPartitionRepr m a b hm hab) := by
  apply Partition.le_isrepr
  intro i
  exact ⟨le_refl _, (equalPartition m a b hm hab).increase i⟩

-- Diam of equal partition < δ
theorem equalPartition_diam_lt (m : Nat) (a b δ : Real) (hm : m ≠ 0) (hab : a ≤ b)
    (hδ : 0 < δ) (hlt : (b - a) / δ < (m : Real)) :
    Partition.diam (equalPartition m a b hm hab) < δ := by
  have hm_pos : 0 < (m : Real) := by
    cases m with
    | zero => exact absurd rfl hm
    | succ n => exact cast_lt 0 (n + 1) (Nat.zero_lt_succ n)
  apply fmax'_lt m _ δ hδ
  intro i
  rw [equalPartition_length m a b hm hab i]
  exact (div_lt_iff (b - a) δ (m : Real) hδ hm_pos).mp hlt

-- 任意の細かさの等分割の存在
theorem exists_fine_partition (a b δ : Real) (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ (n : Nat) (Δ : Partition n a b) (ξ : Range n → Real),
      Δ.IsRepr ξ ∧ Partition.diam Δ < δ := by
  have hba_nn : 0 ≤ b - a := (nonneg_iff_le a b).mp hab
  have hba_div_nn : 0 ≤ (b - a) / δ := nonneg_div_nonneg (b - a) δ hba_nn hδ
  have hm_lt : (b - a) / δ < ((ceil ((b - a) / δ)) : Real) := ceil_lt _
  have hm_ne : ceil ((b - a) / δ) ≠ 0 :=
    nat_ne_zero_of_nonneg_lt _ _ hba_div_nn hm_lt
  exact ⟨ceil ((b - a) / δ), equalPartition _ a b hm_ne hab,
    equalPartitionRepr _ a b hm_ne hab,
    equalPartitionRepr_isrepr _ a b hm_ne hab,
    equalPartition_diam_lt _ a b δ hm_ne hab hδ hm_lt⟩

-- 一意性
theorem integral_unique (f : Real → Real) (a b : Real) (i j : Real)
    (hab : a ≤ b) (hi : IsIntegral f a b i) (hj : IsIntegral f a b j) : i = j := by
  have : ∀ ε, 0 < ε → (i - j).abs < ε := by
    intro ε hε
    rcases hi (ε / 2) (pos_half ε hε) with ⟨δi, ⟨hδi1, hδi2⟩⟩
    rcases hj (ε / 2) (pos_half ε hε) with ⟨δj, ⟨hδj1, hδj2⟩⟩
    have hδ : 0 < min δi δj := min_pos δi δj hδi1 hδj1
    obtain ⟨m, Δ, ξ, h_repr, h_diam⟩ := exists_fine_partition a b (min δi δj) hab hδ
    let RS := RiemannSum f Δ ξ
    have h_i : (RS - i).abs < ε / 2 :=
      hδi2 m Δ ξ h_repr (lt_le_trans _ _ _ h_diam (min_left_le δi δj))
    have h_j : (RS - j).abs < ε / 2 :=
      hδj2 m Δ ξ h_repr (lt_le_trans _ _ _ h_diam (min_right_le δi δj))
    calc (i - j).abs
        = ((RS - j) + (i - RS)).abs := by rw [telescope_2 j i RS]
      _ ≤ (RS - j).abs + (i - RS).abs := abs_triangle (RS - j) (i - RS)
      _ = (RS - j).abs + (RS - i).abs := by
          rw [show i - RS = -(RS - i) from (neg_sub RS i).symm, abs_neg]
      _ < ε / 2 + ε / 2 := lt_add_lt _ _ _ _ h_j h_i
      _ = ε := half_add ε
  rw [← sub_zero_eq]
  exact lt_epsilon_zero _ this

def IsIntegrable (f : Real → Real) (a b : Real) : Prop :=
  ∃ i, IsIntegral f a b i

-- 向きなし積分。本当はa ≤ bを仮定する必要あり
def Integral (f : Real → Real) (a b : Real) : Real :=
  dite (IsIntegrable f a b) (λ h => Classical.choose h) (λ _ => 0)
  -- if h : IsIntegrable f a b then Classical.choose h else 0

theorem IsIntegral_iff (f : Real → Real) (a b : Real) (i : Real)
    (hab : a ≤ b) (h : IsIntegral f a b i) :
    Integral f a b = i := by
  unfold Integral
  have h₀ : IsIntegrable f a b := ⟨i, h⟩
  rw [dif_pos h₀]
  exact integral_unique _ _ _ _ _ hab (Classical.choose_spec h₀) h

-- [a,a] 上の積分は 0
theorem isintegral_self (f : Real → Real) (a : Real) : IsIntegral f a a 0 := by
  intro ε hε
  refine ⟨1, zero_lt_one, fun n Δ ξ hr _ => ?_⟩
  have hpts : ∀ (i : Range n.succ), Δ.points i = a :=
    fun i => (LinearOrderedField.le_asymm _ _ (Δ.left_le_point i) (Δ.point_le_right i)).symm
  have hxi : ∀ (i : Range n), ξ i = a := by
    intro i
    have hi := hr i
    dsimp [InInterval] at hi
    rw [hpts (Range.incl i), hpts (Range.addone i), if_pos (le_refl a)] at hi
    exact (LinearOrderedField.le_asymm _ _ hi.1 hi.2).symm
  have hRS : RiemannSum f Δ ξ = RiemannSum (fun _ => f a) Δ ξ := by
    unfold RiemannSum; apply summation_congr; intro i; rw [hxi i]
  rw [hRS, const_riemann_sum, sub_self,
      show f a * (0 : Real) = 0 from by
        rw [mul_comm]; exact zero_mul' _,
      sub_self, abs_zero]
  exact hε

theorem integral_self (f : Real → Real) (a : Real) : Integral f a a = 0 :=
  IsIntegral_iff f a a 0 (le_refl a) (isintegral_self f a)

-- b < a のときは分割が存在しないため、（特に 0 を）積分値にできる
theorem isintegral_of_not_le (f : Real → Real) {a b : Real} (h : ¬(a ≤ b)) :
    IsIntegral f a b 0 :=
  fun _ _ => ⟨1, zero_lt_one, fun _ Δ _ _ _ => absurd Δ.left_le_right h⟩

-- 逆は言えない。積分の値が0でないなら可積分は言えるが。

theorem integral_congr (f g : Real → Real) (a b : Real) (hab : a ≤ b) (h : ∀ x, f x = g x) :
  Integral f a b = Integral g a b := by
  have hRS : ∀ n (Δ : Partition n a b) (ξ : Range n → Real),
      RiemannSum f Δ ξ = RiemannSum g Δ ξ := by
    intro n Δ ξ
    unfold RiemannSum
    apply summation_congr
    intro i; rw [h (ξ i)]
  have hfg : ∀ i, IsIntegral f a b i → IsIntegral g a b i := fun i hi ε hε => by
    rcases hi ε hε with ⟨δ, hδ, hh⟩
    exact ⟨δ, hδ, fun n Δ ξ hr hd => by rw [← hRS]; exact hh n Δ ξ hr hd⟩
  have hgf : ∀ i, IsIntegral g a b i → IsIntegral f a b i := fun i hi ε hε => by
    rcases hi ε hε with ⟨δ, hδ, hh⟩
    exact ⟨δ, hδ, fun n Δ ξ hr hd => by rw [hRS]; exact hh n Δ ξ hr hd⟩
  unfold Integral
  cases Classical.em (IsIntegrable f a b) with
  | inl hf =>
    have hg : IsIntegrable g a b := by rcases hf with ⟨i, hi⟩; exact ⟨i, hfg i hi⟩
    rw [dif_pos hf, dif_pos hg]
    exact integral_unique g a b _ _ hab (hfg _ (Classical.choose_spec hf)) (Classical.choose_spec hg)
  | inr hf =>
    have hg : ¬IsIntegrable g a b := fun ⟨i, hi⟩ => hf ⟨i, hgf i hi⟩
    rw [dif_neg hf, dif_neg hg]
