-- Text/C07_Induction.lean — Ch7 sorry を埋める道具 II（calc・順序・帰納法・Σ 補題コーパス）
-- 順序の補題（calc の Trans から両側評価・移項まで）と Σ の基本性質を帰納法で獲得する。
-- 注意: この章まで古典論理ゼロ（not_lt_imp_le 等の古典補題は C11）
import Text.C06_Tactics

open Range

-- ============================================================
-- 順序の基本（クラスの公理の取り出しと推移律の変種）
-- ============================================================

theorem le_refl (a : Real) : a ≤ a := LinearOrderedField.le_refl a
theorem le_trans {a b c : Real} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  LinearOrderedField.le_trans a b c h₁ h₂
theorem le_antisymm (a b : Real) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  LinearOrderedField.le_antisymm a b h₁ h₂
theorem le_total (a b : Real) : a ≤ b ∨ b ≤ a := LinearOrderedField.le_total a b
theorem add_le_add_right (a b c : Real) (h : a ≤ b) : a + c ≤ b + c :=
  LinearOrderedField.add_le_add a b c h

theorem lt_trans (a b c : Real) : a < b → b < c → a < c := by
  intro ⟨hab, _⟩ ⟨hbc, hne_bc⟩
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne_bc (le_antisymm b c hbc (heq ▸ hab))⟩

theorem lt_le_trans (a b c : Real) : a < b → b ≤ c → a < c := by
  intro ⟨hab, hne⟩ hbc
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne (le_antisymm a b hab (heq ▸ hbc))⟩

theorem le_lt_trans {a b c : Real} : a ≤ b → b < c → a < c := by
  intro hab ⟨hbc, hne⟩
  exact ⟨LinearOrderedField.le_trans a b c hab hbc,
    fun heq => hne (le_antisymm b c hbc (heq ▸ hab))⟩

-- calc 用の Trans インスタンス（calc は機構で動く——種明かしの素材）
instance : Trans (LE.le : Real → Real → Prop) LE.le LE.le :=
  ⟨fun h₁ h₂ => le_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LE.le LT.lt :=
  ⟨fun h₁ h₂ => lt_le_trans _ _ _ h₁ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => le_lt_trans h₁ h₂⟩
instance : Trans (LT.lt : Real → Real → Prop) LT.lt LT.lt :=
  ⟨fun h₁ h₂ => lt_trans _ _ _ h₁ h₂⟩
instance : Trans (Eq : Real → Real → Prop) LE.le LE.le := ⟨fun h₁ h₂ => h₁ ▸ h₂⟩
instance : Trans (LE.le : Real → Real → Prop) Eq LE.le := ⟨fun h₁ h₂ => h₂ ▸ h₁⟩

-- ============================================================
-- 加法と順序
-- ============================================================

theorem add_left_le (a b c : Real) : b ≤ c → a + b ≤ a + c := by
  intro h
  have h1 := add_le_add_right b c a h
  rw [add_comm b a, add_comm c a] at h1; exact h1

theorem add_left_lt (a b c : Real) : b < c → a + b < a + c := by
  intro ⟨hle, hne⟩
  exact ⟨add_left_le a b c hle, fun h => hne (add_left_cancel' a b c h)⟩

theorem add_lt_add_right (a b c : Real) : a < b → a + c < b + c := by
  intro h
  rw [add_comm a c, add_comm b c]
  exact add_left_lt c a b h

theorem add_le_add' {a b c d : Real} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right a b c h₁) (add_left_le b c d h₂)

theorem nonneg_iff_le (a b : Real) : a ≤ b ↔ 0 ≤ b - a := by
  constructor
  · intro h
    have h1 := add_le_add_right a b (-a) h
    rw [add_neg'] at h1; exact h1
  · intro h
    have h1 := add_le_add_right (0 : Real) (b + -a) a h
    rw [zero_add'] at h1
    rw [show b + -a + a = b from by
      calc b + -a + a = b + (-a + a) := add_assoc _ _ _
        _ = b + 0 := by rw [neg_add']
        _ = b := add_zero' _] at h1
    exact h1

theorem neg_neg_nonneg (a : Real) : a ≤ 0 → 0 ≤ -a := by
  intro h
  have h1 := add_le_add_right a (0 : Real) (-a) h
  rw [add_neg', zero_add'] at h1; exact h1

theorem sub_pos_of_lt {a b : Real} (h : a < b) : 0 < b - a := by
  refine ⟨(nonneg_iff_le a b).mp h.1, fun heq => h.2 ?_⟩
  have h' : a + (b - a) = a + 0 := by rw [← heq]
  rw [add_sub_cancel', add_zero'] at h'
  exact h'.symm

theorem neg_le_neg' {a b : Real} (h : a ≤ b) : -b ≤ -a := by
  have h1 := add_le_add_right a b (-a + -b) h
  rw [show a + (-a + -b) = -b from by
      rw [← add_assoc, add_neg', zero_add'],
    show b + (-a + -b) = -a from by
      rw [add_comm (-a) (-b), ← add_assoc, add_neg', zero_add']] at h1
  exact h1

theorem neg_lt_neg {a b : Real} (h : a < b) : -b < -a :=
  ⟨neg_le_neg' h.1, fun e => h.2 (by
    have e2 := congrArg (fun z => -z) e
    simp only [] at e2
    rw [show -(-b) = b from neg_neg b, show -(-a) = a from neg_neg a] at e2
    exact e2.symm)⟩

theorem sub_le_sub_right {a b : Real} (h : a ≤ b) (c : Real) : a - c ≤ b - c :=
  add_le_add_right a b (-c) h

theorem sub_le_sub_left {a b : Real} (h : a ≤ b) (c : Real) : c - b ≤ c - a :=
  add_left_le c (-b) (-a) (neg_le_neg' h)

theorem sub_lt_sub_left {a b : Real} (h : a < b) (c : Real) : c - b < c - a :=
  add_left_lt c (-b) (-a) (neg_lt_neg h)

-- ============================================================
-- 移項の小物（両側評価の組み立てに繰り返し使う）
-- ============================================================

theorem lt_add_of_sub_lt {a b c : Real} (h : a - b < c) : a < c + b := by
  have h1 := add_lt_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

theorem sub_lt_swap {a b c : Real} (h : a - b < c) : a - c < b := by
  have h1 := lt_add_of_sub_lt h
  have h2 := add_lt_add_right a (c + b) (-c) h1
  rwa [show c + b + -c = b from by
    rw [add_comm c b, add_assoc, add_neg', add_zero']] at h2

theorem sub_lt_of_lt_add {a b c : Real} (h : a < b + c) : a - b < c := by
  have h1 := add_lt_add_right a (b + c) (-b) h
  have h2 : (b + c) + -b = c := by
    rw [add_comm b c, add_assoc, add_neg', add_zero']
  rwa [h2] at h1

theorem sub_lt_self (z : Real) {h : Real} (hh : 0 < h) : z - h < z := by
  have hneg : -h < (0 : Real) := by
    have := neg_lt_neg hh; rwa [neg_zero] at this
  have := add_left_lt z (-h) 0 hneg
  rwa [add_zero'] at this

theorem le_add_of_sub_le {a b c : Real} (h : a - b ≤ c) : a ≤ c + b := by
  have h1 := add_le_add_right (a - b) c b h
  rwa [sub_add_cancel] at h1

theorem le_of_add_nonneg_eq {a b c : Real} (h : a + b = c) (hb : 0 ≤ b) : a ≤ c := by
  have h1 := add_left_le a 0 b hb
  rw [add_zero'] at h1
  exact h ▸ h1

theorem le_of_nonneg_add_eq {a b c : Real} (h : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  have h1 := add_le_add_right 0 a b ha
  rw [zero_add'] at h1
  exact h ▸ h1

theorem lt_add_pos (a b : Real) (hb : 0 < b) : a < a + b := by
  have h := add_left_lt a 0 b hb
  rwa [add_zero'] at h

theorem le_add_nonneg (a b : Real) (hb : 0 ≤ b) : a ≤ a + b := by
  have h := add_left_le a 0 b hb
  rwa [add_zero'] at h

-- ============================================================
-- 乗法の順序（0 < 1 は公理からの定理——nontrivial の出番）
-- ============================================================

theorem mul_nonneg (a b : Real) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b :=
  LinearOrderedField.mul_nonneg a b h h'

theorem nonmul_neg_le (a b c : Real) (hc : 0 ≤ c) (hab : 0 ≤ b - a) :
    0 ≤ b * c - a * c := by
  rw [show b * c - a * c = b * c + -(a * c) from rfl,
      show -(a * c) = (-a) * c from (neg_mul a c).symm,
      show b * c + (-a) * c = (b + -a) * c from (CommRing.right_distrib b (-a) c).symm]
  exact mul_nonneg (b + -a) c hab hc

theorem nonneg_mul_nonneg (a b c : Real) (h : 0 ≤ c) : a ≤ b → a * c ≤ b * c := by
  intro hab; rw [nonneg_iff_le] at hab ⊢
  exact nonmul_neg_le a b c h hab

theorem mul_right_lt (a b c : Real) : 0 < c → a < b → a * c < b * c := by
  intro ⟨hc, hnc⟩ ⟨hab, hne⟩
  constructor
  · exact nonneg_mul_nonneg a b c hc hab
  · intro heq; apply hne
    have hcne : c ≠ (0 : Real) := hnc.symm
    calc a = a * c * Field.inv c := by
          rw [mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]
      _ = b * c * Field.inv c := by rw [heq]
      _ = b := by rw [mul_assoc,
              show c * Field.inv c = (1 : Real) from Field.mul_inv c hcne, mul_one_b]

theorem zero_lt_one : (0 : Real) < 1 := by
  cases le_total (0 : Real) 1 with
  | inl h => exact ⟨h, fun heq => Field.nontrivial heq⟩
  | inr h =>
    have h0 : (0 : Real) ≤ -1 := neg_neg_nonneg 1 h
    have h1 : (0 : Real) ≤ (-1) * (-1) := mul_nonneg (-1) (-1) h0 h0
    have h2 : (-1 : Real) * (-1) = 1 := by
      calc (-1 : Real) * (-1) = -(1 * (-1)) := neg_mul 1 (-1)
        _ = -(-(1 * 1)) := by rw [mul_neg]
        _ = 1 * 1 := neg_neg _
        _ = 1 := one_mul_b 1
    rw [h2] at h1
    exact absurd (le_antisymm (0 : Real) (1 : Real) h1 h) Field.nontrivial

-- リテラル 2 はまだ無い: 1 + 1 で書く（リテラル機構は Ch8）
theorem zero_lt_one_one : (0 : Real) < 1 + 1 := by
  have h1 := add_left_lt 1 0 1 zero_lt_one
  rw [add_zero'] at h1
  exact lt_trans 0 1 (1 + 1) zero_lt_one h1

theorem one_one_ne_zero : ((1 : Real) + 1) ≠ 0 := ne_of_gt zero_lt_one_one

theorem pos_inv (b : Real) (hb : 0 < b) : 0 < Field.inv b := by
  have hbne : b ≠ (0 : Real) := hb.2.symm
  constructor
  · cases le_total (0 : Real) (Field.inv b) with
    | inl h => exact h
    | inr h =>
      exfalso
      have h0 : (0 : Real) ≤ -(Field.inv b) := neg_neg_nonneg _ h
      have h1 : (0 : Real) ≤ b * -(Field.inv b) :=
        mul_nonneg b (-(Field.inv b)) hb.1 h0
      rw [mul_neg, show b * Field.inv b = (1 : Real) from Field.mul_inv b hbne] at h1
      have h2 : (1 : Real) ≤ 0 := by
        have := add_le_add_right (0 : Real) (-(1 : Real)) (1 : Real) h1
        rw [zero_add', neg_add'] at this; exact this
      exact zero_lt_one.2 (le_antisymm (0 : Real) (1 : Real) zero_lt_one.1 h2)
  · intro h
    exact Field.nontrivial (show (0 : Real) = 1 from by
      calc (0 : Real) = b * 0 := (mul_zero' b).symm
        _ = b * Field.inv b := by rw [h]
        _ = 1 := Field.mul_inv b hbne)

theorem pos_mul_pos (a b : Real) : 0 < a → 0 < b → 0 < a * b := by
  intro ha hb
  exact ⟨mul_nonneg a b ha.1 hb.1, fun h =>
    ha.2 (by
      calc (0 : Real) = 0 * Field.inv b := (zero_mul' _).symm
        _ = (a * b) * Field.inv b := by rw [h]
        _ = a * (b * Field.inv b) := mul_assoc _ _ _
        _ = a * 1 := by rw [show b * Field.inv b = (1 : Real) from Field.mul_inv b hb.2.symm]
        _ = a := mul_one_b a)⟩

-- ============================================================
-- Σ 補題コーパス（帰納法の訓練場。添字の付け替え fun k => f ⟨k.val, …⟩ が主役）
-- ============================================================

theorem summation_congr (n : Nat) (f g : Range n → Real) (h : ∀ i, f i = g i) :
    Summation n f = Summation n g := congrArg (Summation n) (funext h)

theorem summation_all_zero (n : Nat) :
    Summation n (fun _ : Range n => (0 : Real)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Summation m (fun _ : Range m => (0 : Real)) + (0 : Real) = 0
    rw [ih, zero_add']

theorem additive_summation (n : Nat) (f g : Range n → Real) :
    Summation n (fun i => f i + g i) = Summation n f + Summation n g := by
  induction n with
  | zero => exact (zero_add' 0).symm
  | succ n ih =>
    show Summation n (fun k => f (incl k) + g (incl k))
        + (f ⟨n, Nat.lt_succ_self n⟩ + g ⟨n, Nat.lt_succ_self n⟩)
      = (Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩)
        + (Summation n (fun k => g (incl k)) + g ⟨n, Nat.lt_succ_self n⟩)
    rw [ih (fun k => f (incl k)) (fun k => g (incl k))]
    exact add_four_comm _ _ _ _

theorem summation_mul_left : ∀ (n : Nat) (f : Range n → Real) (c : Real),
    Summation n (fun i => c * f i) = c * Summation n f := by
  intro n
  induction n with
  | zero => intro f c; exact (mul_zero' c).symm
  | succ m ih =>
    intro f c
    show Summation m (fun k => c * f (Range.incl k)) + c * f ⟨m, Nat.lt_succ_self m⟩
        = c * (Summation m (fun k => f (Range.incl k)) + f ⟨m, Nat.lt_succ_self m⟩)
    rw [ih (fun k => f (Range.incl k)) c, CommRing.left_distrib]

theorem neg_summation (n : Nat) (f : Range n → Real) :
    -Summation n f = Summation n (fun i => -f i) := by
  induction n with
  | zero => exact neg_zero
  | succ m ih =>
    show -(Summation m (fun k => f (incl k)) + f ⟨m, Nat.lt_succ_self m⟩)
        = Summation m (fun k => -(f (incl k))) + -(f ⟨m, Nat.lt_succ_self m⟩)
    rw [neg_add_distrib, ih (fun k => f (incl k))]

/-- Σ レベルの差: `Σ F - Σ G = Σ (F - G)`（加法＋符号の系）。 -/
theorem sub_summation (n : Nat) (F G : Range n → Real) :
    Summation n F - Summation n G = Summation n (fun i => F i - G i) := by
  show Summation n F + -Summation n G = Summation n (fun i => F i - G i)
  rw [neg_summation n G]
  exact (additive_summation n F (fun i => -G i)).symm

theorem summation_nonneg (n : Nat) (f : Range n → Real) (h : ∀ i, 0 ≤ f i) :
    0 ≤ Summation n f := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    show (0 : Real) ≤ Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩
    have h1 : (0 : Real) ≤ Summation n (fun k => f (incl k)) :=
      ih (fun k => f (incl k)) (fun i => h (incl i))
    calc (0 : Real) = 0 + 0 := (add_zero' 0).symm
      _ ≤ Summation n (fun k => f (incl k)) + 0 := add_le_add_right 0 _ 0 h1
      _ ≤ Summation n (fun k => f (incl k)) + f ⟨n, Nat.lt_succ_self n⟩ :=
          add_left_le _ 0 _ (h ⟨n, Nat.lt_succ_self n⟩)

theorem summation_le : ∀ (n : Nat) (f g : Range n → Real),
    (∀ i, f i ≤ g i) → Summation n f ≤ Summation n g := by
  intro n
  induction n with
  | zero => intro f g _; exact le_refl 0
  | succ m ih =>
    intro f g h
    exact add_le_add' (ih _ _ (fun k => h (Range.incl k))) (h ⟨m, Nat.lt_succ_self m⟩)

-- ボス戦: 望遠鏡和（最初の本格的帰納法証明）
theorem summation_telescope : ∀ (n : Nat) (g : Range (n + 1) → Real),
    Summation n (fun i => g (Range.addone i) - g (Range.incl i))
      = g ⟨n, Nat.lt_succ_self n⟩ - g ⟨0, Nat.succ_pos n⟩ := by
  intro n
  induction n with
  | zero => intro g; exact (sub_self _).symm
  | succ m ih =>
    intro g
    show Summation m (fun k =>
          g (Range.addone (Range.incl k)) - g (Range.incl (Range.incl k)))
        + (g (Range.addone ⟨m, Nat.lt_succ_self m⟩)
            - g (Range.incl ⟨m, Nat.lt_succ_self m⟩)) = _
    have h := ih (fun j => g (Range.incl j))
    rw [show (fun k : Range m =>
          g (Range.addone (Range.incl k)) - g (Range.incl (Range.incl k)))
        = (fun k : Range m =>
          g (Range.incl (Range.addone k)) - g (Range.incl (Range.incl k))) from rfl]
    rw [h]
    exact (telescope_2 (g ⟨0, Nat.succ_pos (m + 1)⟩)
      (g ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
      (g ⟨m, Nat.lt_succ_of_lt (Nat.lt_succ_self m)⟩)).symm

/-- Σ_{i<n} i の閉じた式（**純粋に Nat の恒等式**）: `(1+1)·Σ i + n = n·n`
（⟺ `Σ_{i<n} i = n(n−1)/2`）。Summation は和があれば定義でき Nat でも使える——
これは Real ではなく Nat の式。減算を避けた形にして cast がきれいに通るようにしてある。 -/
theorem sum_id_nat (n : Nat) :
    (1 + 1) * Summation n (fun i => i.val) + n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsucc : Summation (n + 1) (fun i => i.val) = Summation n (fun i => i.val) + n := rfl
    rw [hsucc, show (n + 1) * (n + 1) = n * n + (1 + 1) * n + 1 from by
      rw [Nat.succ_mul, Nat.mul_succ]; omega]
    omega

-- ============================================================
-- 脇道: Σ は線形形式である
--    additive_summation と summation_mul_left の 2 本は、数学者の言葉では
--    「有限数列のなすベクトル空間 (Range n → Real) 上の線形形式」という 1 つの主張。
--    ベクトル空間の公理と線形写像を class で自作して、そう言い直してみる
--    （class 設計の応用・関数型へのインスタンス・funext の活躍どころ）
-- ============================================================

-- ANCHOR: vector_space
-- Real 上のベクトル空間（• は core の SMul の記法）
class VectorSpace (V : Type) extends Add V, Neg V, Zero V, SMul Real V where
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  add_comm : ∀ u v : V, u + v = v + u
  add_zero : ∀ v : V, v + 0 = v
  add_neg : ∀ v : V, v + -v = 0
  one_smul : ∀ v : V, (1 : Real) • v = v
  mul_smul : ∀ (a b : Real) (v : V), (a * b) • v = a • (b • v)
  smul_add : ∀ (a : Real) (u v : V), a • (u + v) = a • u + a • v
  add_smul : ∀ (a b : Real) (v : V), (a + b) • v = a • v + b • v

-- 線形写像（線形形式は W = Real の場合）
def IsLinearMap {V W : Type} [VectorSpace V] [VectorSpace W] (T : V → W) : Prop :=
  (∀ u v : V, T (u + v) = T u + T v) ∧
  (∀ (c : Real) (v : V), T (c • v) = c • T v)
-- ANCHOR_END: vector_space

-- Real 自身は Real 上のベクトル空間（• は単なる積）
noncomputable instance : VectorSpace Real where
  smul := fun c x => c * x
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero'
  add_neg := add_neg'
  one_smul := one_mul_b
  mul_smul := mul_assoc
  smul_add := CommRing.left_distrib
  add_smul := CommRing.right_distrib

-- 有限数列の空間 Range n → Real（演算はすべて各点で——funext の出番）
noncomputable instance (n : Nat) : VectorSpace (Range n → Real) where
  add := fun f g => fun i => f i + g i
  neg := fun f => fun i => -(f i)
  zero := fun _ => 0
  smul := fun c f => fun i => c * f i
  add_assoc := fun f g h => funext fun i => add_assoc (f i) (g i) (h i)
  add_comm := fun f g => funext fun i => add_comm (f i) (g i)
  add_zero := fun f => funext fun i => add_zero' (f i)
  add_neg := fun f => funext fun i => add_neg' (f i)
  one_smul := fun f => funext fun i => one_mul_b (f i)
  mul_smul := fun a b f => funext fun i => mul_assoc a b (f i)
  smul_add := fun a f g => funext fun i => CommRing.left_distrib a (f i) (g i)
  add_smul := fun a b f => funext fun i => CommRing.right_distrib a b (f i)

-- ANCHOR: summation_linear
-- Σ は線形形式（証明は corpus の 2 本がそのまま——「線形」という 1 概念に束ねられる）
theorem summation_isLinear (n : Nat) :
    IsLinearMap (fun f : Range n → Real => Summation n f) :=
  ⟨fun f g => additive_summation n f g,
   fun c f => summation_mul_left n f c⟩
-- ANCHOR_END: summation_linear

-- ============================================================
-- Partition の基本性質（induction を読者自身の構造に適用する実地）
--    隣接単調（公理 increase）→ 大域単調（points_mono・induction）→ 端点評価・
--    タグの所属。すべて Ch9 の性質証明が消費する。
-- ============================================================

/-- 各小区間の長さは非負（分点が広義単調だから）。 -/
theorem length_nonneg {n : Nat} {u v : Real} (Δ : Partition n u v) (i : Range n) :
    0 ≤ Δ.length i :=
  (nonneg_iff_le _ _).mp (Δ.increase i)

/-- 長さの総和は区間幅: `Σ length = v - u`。望遠鏡和（`summation_telescope`）で潰れる。 -/
theorem length_sum {n : Nat} {u v : Real} (Δ : Partition n u v) :
    Summation n (fun i => Δ.length i) = v - u := by
  show Summation n (fun i => Δ.points (Range.addone i) - Δ.points (Range.incl i)) = v - u
  rw [summation_telescope n Δ.points, Δ.right, Δ.left]

/-- 分点列の単調性: 添字 `k.val ≤ lv` なら `points k ≤ points ⟨lv,_⟩`。隣接単調（公理
`increase`）から **induction** で大域単調を導く（well-founded 再帰は不要）。 -/
theorem points_mono {n : Nat} {u v : Real} (Δ : Partition n u v) (k : Range (n + 1)) :
    ∀ (lv : Nat) (hl : lv < n + 1), k.val ≤ lv → Δ.points k ≤ Δ.points ⟨lv, hl⟩ := by
  intro lv
  induction lv with
  | zero =>
    intro hl hk
    have hke : k = ⟨0, hl⟩ := Subtype.ext (Nat.le_zero.mp hk)
    rw [hke]; exact le_refl _
  | succ m ih =>
    intro hl hk
    rcases Nat.lt_or_ge k.val (m + 1) with hlt | hge
    · have hm : m < n + 1 := Nat.lt_of_succ_lt hl
      have hmn : m < n := Nat.lt_of_succ_lt_succ hl
      exact le_trans (ih hm (Nat.le_of_lt_succ hlt)) (Δ.increase ⟨m, hmn⟩)
    · have hke : k = ⟨m + 1, hl⟩ := Subtype.ext (Nat.le_antisymm hk hge)
      rw [hke]; exact le_refl _

/-- すべての分点は左端 `u` 以上（単調性＋`Δ.left`）。 -/
theorem left_le_point {n : Nat} {u v : Real} (Δ : Partition n u v)
    (i : Range (n + 1)) : u ≤ Δ.points i := by
  have h := points_mono Δ ⟨0, Nat.succ_pos n⟩ i.val i.property (Nat.zero_le _)
  rw [Δ.left] at h
  exact h

/-- すべての分点は右端 `v` 以下（単調性＋`Δ.right`）。 -/
theorem point_le_right {n : Nat} {u v : Real} (Δ : Partition n u v)
    (i : Range (n + 1)) : Δ.points i ≤ v := by
  have h := points_mono Δ i n (Nat.lt_succ_self n) (Nat.le_of_lt_succ i.property)
  rw [Δ.right] at h
  exact h

/-- 代表点系のタグは区間 `[u, v]` 内にある（IsRepr＝小区間内・端点評価から区間全体へ。
raw 版。`TaggedPartition` に束ねた版は Ch12）。 -/
theorem tag_mem' {n : Nat} {u v : Real} (Δ : Partition n u v) (ξ : Range n → Real)
    (hr : Δ.IsRepr ξ) (i : Range n) : u ≤ ξ i ∧ ξ i ≤ v := by
  have h1 : Δ.points ⟨0, Nat.succ_pos n⟩ ≤ Δ.points (Range.incl i) :=
    points_mono Δ ⟨0, Nat.succ_pos n⟩ i.val (Nat.lt_succ_of_lt i.property) (Nat.zero_le _)
  have h2 : Δ.points (Range.addone i) ≤ Δ.points ⟨n, Nat.lt_succ_self n⟩ :=
    points_mono Δ (Range.addone i) n (Nat.lt_succ_self n) i.property
  constructor
  · calc u = Δ.points ⟨0, Nat.succ_pos n⟩ := Δ.left.symm
      _ ≤ Δ.points (Range.incl i) := h1
      _ ≤ ξ i := (hr i).1
  · calc ξ i ≤ Δ.points (Range.addone i) := (hr i).2
      _ ≤ Δ.points ⟨n, Nat.lt_succ_self n⟩ := h2
      _ = v := Δ.right
