-- Text/C15_Integral.lean — Ch15 リーマン積分の定義
-- TaggedPartition（∀ 量化のための束ね）・Fine の ∀ 形・Near（3 種の ε-δ の統一語彙）・
-- IsIntegral・dite＋choose の Integral・監査 3 層
-- TODO(P4): ∫ 記法の自作（Ch5 の再演）・IsLimAt（演習）
import Text.C14_Archimedes

noncomputable section

open Classical
open Range

-- ============================================================
-- §1 タグ付き分割: 4 つ組を 1 変数に束ねる（structure の設計基準の再訪）
-- ============================================================

-- ANCHOR: tagged_partition
structure TaggedPartition (a b : Real) where
  n : Nat
  Δ : Partition n a b
  ξ : Range n → Real
  repr : Δ.IsRepr ξ

namespace TaggedPartition

noncomputable def sum {a b : Real} (P : TaggedPartition a b) (f : Real → Real) : Real :=
  RiemannSum f P.Δ P.ξ

-- 細かさ: ∀ 形（diam / max を使わない——Ch14 の実験の帰結を設計に）
def Fine {a b : Real} (P : TaggedPartition a b) (δ : Real) : Prop :=
  ∀ i, P.Δ.length i < δ

end TaggedPartition
-- ANCHOR_END: tagged_partition

-- タグの所属（Ch10 の raw 版を束ねた形で）
theorem tag_mem {u v : Real} (P : TaggedPartition u v) (i : Range P.n) :
    u ≤ P.ξ i ∧ P.ξ i ≤ v :=
  tag_mem' P.Δ P.ξ P.repr i

-- 定数関数のリーマン和（同上）
theorem const_sum {u v : Real} (P : TaggedPartition u v) (c : Real) :
    P.sum (fun _ => c) = c * (v - u) :=
  riemann_sum_const P.Δ P.ξ c

-- 任意の細かさのタグ付き分割の存在（Ch12 の等分割を束ねる）
theorem exists_fine_partition (a b δ : Real) (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ P : TaggedPartition a b, P.Fine δ := by
  obtain ⟨m, hm, hfine⟩ := exists_fine_equalPartition a b δ hab hδ
  exact ⟨⟨m, equalPartition m a b hm hab, equalPartitionRepr m a b hm hab,
    equalPartitionRepr_isrepr m a b hm hab⟩, hfine⟩

-- ============================================================
-- §2 Near: 3 種の ε-δ の統一語彙（abs-free の両側形）
-- ============================================================

-- ANCHOR: near
def Near (ε c x : Real) : Prop := c - ε < x ∧ x < c + ε
-- ANCHOR_END: near

theorem near_self {z ε : Real} (hε : 0 < ε) : Near ε z z := by
  constructor
  · have hneg : -ε < (0 : Real) := by
      have h := neg_lt_neg hε; rwa [neg_zero] at h
    have h := add_left_lt z (-ε) 0 hneg
    rwa [add_zero'] at h
  · have h := add_left_lt z 0 ε hε
    rwa [add_zero'] at h

-- 点 x での連続性（2 つ目の ε-δ。IsLimAt は演習）
def ContinuousAt (f : Real → Real) (x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ t, Near δ x t → Near ε (f x) (f t)

-- ============================================================
-- §3 積分の定義: 網目 → 0 の極限（3 つ目の ε-δ）
-- ============================================================

-- ANCHOR: is_integral
def IsIntegral (f : Real → Real) (a b i : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ P : TaggedPartition a b, P.Fine δ → Near ε i (P.sum f)

def IsIntegrable (f : Real → Real) (a b : Real) : Prop :=
  ∃ i, IsIntegral f a b i
-- ANCHOR_END: is_integral

-- 主定義: dite ＋ choose ＋ junk 値 0。
-- 古典性は 2 箇所から入る: choose（値の取り出し）と dite の Decidable（propDecidable）
-- ANCHOR: integral
noncomputable def Integral (f : Real → Real) (a b : Real) : Real :=
  if h : a ≤ b ∧ IsIntegrable f a b then Classical.choose h.2 else 0
-- ANCHOR_END: integral

-- 証明引数核: 「最終的にリーマン和の下界になる値」の集合の sup。
-- 非空性・有界性の証明を引数に取れば choice ゼロで値が書ける（証人はデータ）
def LowerRS (f : Real → Real) (a b : Real) : Real → Prop :=
  fun y => ∃ δ, 0 < δ ∧ ∀ P : TaggedPartition a b, P.Fine δ → y ≤ P.sum f

noncomputable def Integral' (f : Real → Real) (a b : Real)
    (hne : ∃ y, LowerRS f a b y)
    (hbdd : ∃ M, ∀ y, LowerRS f a b y → y ≤ M) : Real :=
  Real.sup (LowerRS f a b) hne hbdd

-- ============================================================
-- §4 監査 3 層: IsIntegral = 古典ゼロ／Integral = +choice（2 箇所）／
--    Integral' = +sup・choice フリー
-- ============================================================

#print axioms IsIntegral
#print axioms Integral
#print axioms Integral'
