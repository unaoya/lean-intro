-- Text/Proto/Integral.lean — 試作: リーマン積分の定義
-- 「分割の長さを小さくする極限。それが存在するとき可積分といい、その値を積分とする」
import Text.Proto.Partition

-- 近さの述語（脱 abs: 両側で書く。極限・連続・積分をすべてこの述語で書く予定）
def Near (ε c x : Real) : Prop := c - ε < x ∧ x < c + ε

-- 積分の定義: 網目 → 0 の極限（ε-δ、abs-free・∀ 形の細かさ）
def IsIntegral (f : Real → Real) (a b i : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ P : TaggedPartition a b, P.Fine δ → Near ε i (P.sum f)

-- 可積分: 極限が存在すること
def IsIntegrable (f : Real → Real) (a b : Real) : Prop :=
  ∃ i, IsIntegral f a b i

-- ============================================================
-- 積分（値の取り出し）— 2 つの形を併置して公理監査を比較する
-- ============================================================

-- 主定義: dite ＋ choose ＋ junk 値 0。
-- 古典性は 2 箇所から入る: choose（値の取り出し）と dite の Decidable（propDecidable）
open Classical in
noncomputable def Integral (f : Real → Real) (a b : Real) : Real :=
  if h : a ≤ b ∧ IsIntegrable f a b then Classical.choose h.2 else 0

-- 証明引数核: 「最終的にリーマン和の下界になる値」の集合の sup。
-- 非空性・有界性の証明を引数に取れば choice ゼロで値が書ける（証人はデータ）
def LowerRS (f : Real → Real) (a b : Real) : Real → Prop :=
  fun y => ∃ δ, 0 < δ ∧ ∀ P : TaggedPartition a b, P.Fine δ → y ≤ P.sum f

noncomputable def Integral' (f : Real → Real) (a b : Real)
    (hne : ∃ y, LowerRS f a b y)
    (hbdd : ∃ M, ∀ y, LowerRS f a b y → y ≤ M) : Real :=
  Real.sup (LowerRS f a b) hne hbdd

-- ============================================================
-- 公理監査の実験（試作の検証ポイント）
-- ============================================================

#print axioms IsIntegral   -- 確認済: [Real, Real.instLOF]（古典公理ゼロ）
#print axioms Integral     -- 確認済: 上記 + propext, Classical.choice, Quot.sound
#print axioms Integral'    -- 確認済: [Real, Real.instLOF, Real.sup]（choice ゼロ）

-- 最小性の実験（確認済 2026-06-12）: Axioms.lean の sup 公理 3 本をコメントアウトしても
-- Integral' 以外（IsIntegral・IsIntegrable・Integral まで）はビルドが通る
-- ——リーマン積分の「定義」に完備性は不要で、sup が要るのは値の sup 構成と存在定理から
