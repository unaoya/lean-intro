-- Text/C11_Numbers.lean — Ch11 具体例 y = x の n 等分
-- リテラルの一般機構（Ch3 のエラーの回収）・除法・cast 補題（構成的な部分のみ——
-- sup を使う archimedean 系は C11 へ。この分割線が「公理の節約」の教材）・
-- equalPartition・sum_id
-- TODO(P4): RS = (n+1)/(2n)（右端タグ）・(n−1)/(2n)（左端タグ）の計算演習
import Text.C10_Induction

noncomputable section

open Range

-- ============================================================
-- §1 リテラルの一般機構と除法
-- ============================================================

-- 自然数の埋め込み（構造的再帰）
-- ANCHOR: of_nat
noncomputable def Real.ofNat : Nat → Real
  | 0 => 0
  | n + 1 => Real.ofNat n + 1
-- ANCHOR_END: of_nat

-- リテラル 2 以上（Ch3 の failed to synthesize がここで消える）
noncomputable instance (n : Nat) : OfNat Real (n + 2) := ⟨Real.ofNat (n + 2)⟩

-- 変数の埋め込み ↑n（リテラル用 OfNat との対比）
noncomputable instance : NatCast Real := ⟨Real.ofNat⟩

-- 除法の記法（等分割の分点式のため）
noncomputable instance : Div Real := ⟨fun a b => a * Field.inv b⟩

-- defeq の観察: 「数の 2 つの建て方」の分かれ目。
-- cast は代数の 0 と 1 から建てた（代数一次）。重なる点の等式の「強さ」が違う:
-- cast 0 = 0 は構成により rfl（defeq）、cast 1 = 1 は命題的（証明が要る）。
-- もし全リテラルを cast で配線したら (1 : Real) の中身は 0 + 1 になり、
-- 公理には計算が無いので 1 と defeq にならない——rfl 証明が死ぬ（Ch7 の 2 種の等しさ）。
-- これが mathlib の Nat.AtLeastTwo（リテラル 0/1/2 以上の担当の排他分割）の理由
-- ANCHOR: cast_defeq
example : Real.ofNat 0 = 0 := rfl        -- defeq（構成どおり）
example : Real.ofNat 1 = 0 + 1 := rfl    -- 中身は 0 + 1
#check_failure (rfl : Real.ofNat 1 = 1)  -- 0 + 1 と 1 は defeq でない（公理に計算は無い）
theorem cast_one : ((1 : Nat) : Real) = 1 := zero_add' 1  -- 命題的にはもちろん等しい
-- ANCHOR_END: cast_defeq

-- ============================================================
-- ダイヤモンド事件: 「2 つ目の値を正準にすると事故」（class 深い機構の悪い例）
--   リテラルの担当を 0/1/2 以上で排他分割する理由——同じ型に 2 つインスタンスを
--   登録すると機構は黙って 1 つを選び、事故は静かに起きる。Ch2 の「class＝自動で
--   見つかる構造」の影の側面。本物の NatCast ダイヤモンドの語りは原稿側。
-- ============================================================

-- ANCHOR: diamond
namespace DiamondIncident

class Price (α : Type) where
  value : α → Nat

structure Coin where
  v : Nat

instance viaFace : Price Coin := ⟨fun c => c.v⟩
instance viaDouble : Price Coin := ⟨fun c => c.v + c.v⟩

-- どちらが選ばれているか？ 機構は後者（viaDouble）を黙って選ぶ
example : Price.value (⟨3⟩ : Coin) = 6 := rfl

end DiamondIncident
-- ANCHOR_END: diamond

-- ============================================================
-- §2 除法の補題（中点・半分・等分の計算部品）
-- ============================================================

theorem zero_div (a : Real) : 0 / a = 0 := by
  show (0 : Real) * Field.inv a = 0; exact zero_mul' _

theorem mul_div_cancel' (a b : Real) (ha : a ≠ (0 : Real)) : a * b / a = b := by
  show a * b * Field.inv a = b
  calc a * b * Field.inv a = b * a * Field.inv a := by rw [mul_comm a b]
    _ = b * (a * Field.inv a) := mul_assoc b a (Field.inv a)
    _ = b * 1 := by rw [show a * Field.inv a = (1 : Real) from Field.mul_inv a ha]
    _ = b := mul_one_b b

theorem div_mul_cancel (a c : Real) (hc : c ≠ (0 : Real)) : a / c * c = a := by
  show a * Field.inv c * c = a
  rw [mul_assoc, show Field.inv c * c = (1 : Real) from Field.inv_mul c hc, mul_one_b]

theorem div_sub_div (a b c : Real) : (a / c) - (b / c) = (a - b) / c := by
  show a * Field.inv c + -(b * Field.inv c) = (a + -b) * Field.inv c
  rw [show -(b * Field.inv c) = (-b) * Field.inv c from by rw [neg_mul]]
  exact (CommRing.right_distrib a (-b) (Field.inv c)).symm

theorem div_add_div (a b c : Real) : a / c + b / c = (a + b) / c :=
  (CommRing.right_distrib a b (Field.inv c)).symm

theorem half_add (a : Real) : a / (1 + 1) + a / (1 + 1) = a := by
  show a * Field.inv (1 + 1) + a * Field.inv (1 + 1) = a
  rw [← CommRing.left_distrib]
  suffices h : Field.inv ((1 : Real) + 1) + Field.inv ((1 : Real) + 1) = (1 : Real) by
    rw [h, mul_one_b]
  have h1 : ((1 : Real) + 1) * Field.inv ((1 : Real) + 1) = (1 : Real) :=
    Field.mul_inv (1 + 1) one_one_ne_zero
  rw [CommRing.right_distrib, one_mul_b] at h1; exact h1

-- x は (x + x) の半分
theorem double_half (x : Real) : (x + x) / (1 + 1) = x := by
  rw [(div_add_div x x (1 + 1)).symm]
  exact half_add x

theorem pos_half (a : Real) (h : 0 < a) : 0 < a / (1 + 1) :=
  pos_mul_pos a (Field.inv (1 + 1)) h (pos_inv (1 + 1) zero_lt_one_one)

theorem half_lt {ε : Real} (hε : 0 < ε) : ε / (1 + 1) < ε := by
  have h := add_left_lt (ε / (1 + 1)) 0 (ε / (1 + 1)) (pos_half ε hε)
  rw [add_zero'] at h
  rw [half_add ε] at h
  exact h

theorem pos_div_pos (a b : Real) : 0 < a → 0 < b → 0 < a / b :=
  fun ha hb => pos_mul_pos a (Field.inv b) ha (pos_inv b hb)

theorem nonneg_div_nonneg (a b : Real) : 0 ≤ a → 0 < b → 0 ≤ a / b :=
  fun ha hb => mul_nonneg a (Field.inv b) ha (pos_inv b hb).1

theorem div_right_lt (a b c : Real) : 0 < c → a < b → a / c < b / c :=
  fun hc hab => mul_right_lt a b (Field.inv c) (pos_inv c hc) hab

theorem div_right_le (a b c : Real) : 0 < c → a ≤ b → a / c ≤ b / c :=
  fun hc hab => nonneg_mul_nonneg a b (Field.inv c) (pos_inv c hc).1 hab

-- ============================================================
-- §3 cast 補題（構成的な部分のみ）
-- ============================================================

-- ofNat の定義（| 0 | n+1）により再帰方程式は rfl
theorem succ_ofNat (n : Nat) : Real.ofNat (n + 1) = Real.ofNat n + (1 : Real) := rfl

theorem cast_nonneg (n : Nat) : (0 : Real) ≤ (n : Real) := by
  show (0 : Real) ≤ Real.ofNat n
  induction n with
  | zero => exact le_refl 0
  | succ m ih =>
    rw [succ_ofNat]
    exact add_nonneg' ih zero_lt_one.1

theorem cast_pos_succ (n : Nat) : (0 : Real) < ((n + 1 : Nat) : Real) := by
  show (0 : Real) < Real.ofNat (n + 1)
  rw [succ_ofNat]
  exact lt_le_trans 0 1 (Real.ofNat n + 1) zero_lt_one
    (by calc (1 : Real) = 0 + 1 := (zero_add' 1).symm
        _ ≤ Real.ofNat n + 1 := add_le_add_right 0 (Real.ofNat n) 1 (cast_nonneg n))

theorem cast_add (n m : Nat) : (n : Real) + (m : Real) = ((n + m : Nat) : Real) := by
  show Real.ofNat n + Real.ofNat m = Real.ofNat (n + m)
  induction m with
  | zero => rw [Nat.add_zero]; exact add_zero' _
  | succ m ih =>
    have eq2 : n + (m + 1) = (n + m) + 1 := Nat.add_succ n m
    rw [succ_ofNat, eq2, succ_ofNat]
    calc Real.ofNat n + (Real.ofNat m + 1)
      = (Real.ofNat n + Real.ofNat m) + 1 := (add_assoc _ _ _).symm
      _ = Real.ofNat (n + m) + 1 := by rw [ih]

theorem cast_lt (a b : Nat) : a < b → (a : Real) < (b : Real) := by
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt h
  have hassoc : a + d + 1 = a + (d + 1) := Nat.add_assoc a d 1
  rw [hd, hassoc]
  have h_eq : ((a + (d + 1) : Nat) : Real) = (a : Real) + ((d + 1 : Nat) : Real) :=
    (cast_add a (d + 1)).symm
  rw [h_eq]
  have hpos : (0 : Real) < ((d + 1 : Nat) : Real) := cast_pos_succ d
  have h1 := add_left_lt (a : Real) 0 ((d + 1 : Nat) : Real) hpos
  rw [add_zero'] at h1; exact h1

theorem cast_le_succ (n : Nat) : (n : Real) ≤ ((n + 1 : Nat) : Real) :=
  le_of_lt (cast_lt n (n + 1) (Nat.lt_succ_self n))

/-- cast は乗法を保つ: `((n*m : Nat) : Real) = (n:Real)*(m:Real)`。 -/
theorem cast_mul (n m : Nat) : ((n * m : Nat) : Real) = (n : Real) * (m : Real) := by
  induction m with
  | zero =>
    rw [Nat.mul_zero, show ((0 : Nat) : Real) = 0 from rfl, mul_zero']
  | succ m ih =>
    rw [Nat.mul_succ, ← cast_add (n * m) n, ih,
        show ((m + 1 : Nat) : Real) = (m : Real) + 1 from by rw [← cast_add m 1, cast_one],
        CommRing.left_distrib, mul_one_b]

/-- cast は順序を保つ（単調）: `a ≤ b → (a:Real) ≤ (b:Real)`。 -/
theorem cast_le (a b : Nat) (h : a ≤ b) : (a : Real) ≤ (b : Real) := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · rw [heq]; exact le_refl _
  · exact le_of_lt (cast_lt a b hlt)

-- ============================================================
-- cast は「射」: 構造を保つ写像（順序付き半環の準同型）。0・1・+・×・≤ を保つ。
--   「Nat → Real は何らかの構造の射」を述語 IsNatHom で明示する。
-- ============================================================

-- ANCHOR: cast_hom
/-- Nat → Real が「順序付き半環の準同型」であること: 0・1・+・×・≤ を保つ。 -/
structure IsNatHom (φ : Nat → Real) : Prop where
  map_zero : φ 0 = 0
  map_one : φ 1 = 1
  map_add : ∀ a b, φ (a + b) = φ a + φ b
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  map_mono : ∀ a b, a ≤ b → φ a ≤ φ b

/-- cast `(· : Real)` は準同型（0/1/+/×/≤ を保つ＝構造を保つ射）。 -/
theorem cast_isHom : IsNatHom (fun n => (n : Real)) :=
  ⟨rfl, cast_one, fun a b => (cast_add a b).symm, fun a b => cast_mul a b,
   fun a b => cast_le a b⟩

/-- 準同型は Σ と可換: `((Σ f : Nat) : Real) = Σ (cast ∘ f)`。cast が和を保つこと
（`map_add`）の帰結——Σ を Nat で計算してから cast しても、各項を cast してから Σ しても
同じ。「構造の射は構造的な演算（有限和）と可換」という一般論の実例。 -/
theorem cast_summation : ∀ (n : Nat) (f : Range n → Nat),
    ((Summation n f : Nat) : Real) = Summation n (fun i => ((f i : Nat) : Real)) := by
  intro n
  induction n with
  | zero => intro f; rfl
  | succ m ih =>
    intro f
    show ((Summation m (fun k => f (Range.incl k)) + f ⟨m, Nat.lt_succ_self m⟩ : Nat) : Real)
        = Summation m (fun k => ((f (Range.incl k) : Nat) : Real))
          + ((f ⟨m, Nat.lt_succ_self m⟩ : Nat) : Real)
    rw [← cast_add, ih (fun k => f (Range.incl k))]
-- ANCHOR_END: cast_hom

theorem cast_pos_of_ne (m : Nat) (hm : m ≠ 0) : (0 : Real) < (m : Real) := by
  cases m with
  | zero => exact absurd rfl hm
  | succ k => exact cast_pos_succ k

-- ============================================================
-- §4 n 等分: points i = a + i * (b−a) / m
-- ============================================================

-- ANCHOR: equal_partition
noncomputable def equalPartition (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    Partition m a b where
  points := fun i => a + ((i.val : Nat) : Real) * (b - a) / (m : Real)
  increase := by
    intro i
    apply add_left_le
    apply div_right_le _ _ _ (cast_pos_of_ne m hm)
    exact nonneg_mul_nonneg _ _ _ ((nonneg_iff_le a b).mp hab) (cast_le_succ i.val)
  left := by
    show a + ((0 : Nat) : Real) * (b - a) / (m : Real) = a
    show a + (0 : Real) * (b - a) / (m : Real) = a
    rw [zero_mul', zero_div, add_zero]
  right := by
    show a + ((m : Nat) : Real) * (b - a) / (m : Real) = b
    have hm' : ((m : Nat) : Real) ≠ (0 : Real) := ne_of_gt (cast_pos_of_ne m hm)
    rw [mul_div_cancel' (m : Real) (b - a) hm']
    exact add_sub_cancel' a b
-- ANCHOR_END: equal_partition

theorem equalPartition_length (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b)
    (i : Range m) :
    (equalPartition m a b hm hab).length i = (b - a) / (m : Real) := by
  show (a + (((i.val + 1 : Nat)) : Real) * (b - a) / (m : Real)) -
       (a + ((i.val : Nat) : Real) * (b - a) / (m : Real)) = (b - a) / (m : Real)
  rw [add_sub_add' a, div_sub_div, mul_sub_mul]
  show ((((i.val + 1 : Nat)) : Real) - ((i.val : Nat) : Real)) * (b - a) / (m : Real)
      = (b - a) / (m : Real)
  rw [show (((i.val + 1 : Nat)) : Real) = ((i.val : Nat) : Real) + 1 from succ_ofNat i.val]
  rw [add_sub_cancel ((i.val : Nat) : Real) 1, one_mul]

/-- 代表点 = 各小区間の左端（一般の `Partition.leftRepr` を等分割に適用したもの）。 -/
noncomputable def equalPartitionRepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    Range m → Real :=
  (equalPartition m a b hm hab).leftRepr

/-- 等分割の左端タグは代表点系——一般の `Partition.leftRepr_isRepr` の特例（等分割固有の
計算は不要）。 -/
theorem equalPartitionRepr_isrepr (m : Nat) (a b : Real) (hm : m ≠ 0) (hab : a ≤ b) :
    (equalPartition m a b hm hab).IsRepr (equalPartitionRepr m a b hm hab) :=
  (equalPartition m a b hm hab).leftRepr_isRepr

-- 注: Σ_{i<n} i の閉じた式は **Nat の恒等式** `sum_id_nat`（C07）。Real での y=x の
-- RS 計算（RS=(n−1)/(2n)）はそれを cast（射 `cast_isHom`・Σ 可換 `cast_summation`）で
-- 運んで行う——TODO(P4): 等分割 [0,1] 上の RiemannSum (fun x => x) の計算。

-- 章末監査: 古典論理ゼロ（[Real, Real.instLOF] のみ・cast の射性も構成的）
#print axioms cast_mul
#print axioms equalPartition
