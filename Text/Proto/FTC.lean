-- Text/Proto/FTC.lean — M3: 片側 FTC の statement の書き比べ（証明は M4 以降）
-- 全域の F を作らない（源泉 A の決定）。積分値は仮定形（IsIntegral f u v J → …）で
-- 持ち回り、一意性フリーの「核」として述べる（FTC の 2 段構造）。
import Text.Proto.Unique

-- 点 x での連続性（abs-free・Near 統一）
def ContinuousAt (f : Real → Real) (x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ t, Near δ x t → Near ε (f x) (f t)

-- ============================================================
-- 形 S: 跨ぎ形（u ≤ x ≤ v の差分商）
-- 「∫ᵤᵛ f は f(x)·(v−u) に誤差 ε·(v−u) で等しい」
-- ============================================================

def HasStraddleDeriv (f : Real → Real) (a b x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ u v J, a ≤ u → u ≤ x → x ≤ v → v ≤ b → u < v → v - u < δ →
      IsIntegral f u v J → Near (ε * (v - u)) (f x * (v - u)) J

-- ============================================================
-- 形 LR: 右微分・左微分の対
-- ============================================================

def HasRightDeriv (f : Real → Real) (b x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ v J, x < v → v ≤ b → v - x < δ →
      IsIntegral f x v J → Near (ε * (v - x)) (f x * (v - x)) J

def HasLeftDeriv (f : Real → Real) (a x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ u J, a ≤ u → u < x → x - u < δ →
      IsIntegral f u x J → Near (ε * (x - u)) (f x * (x - u)) J

-- ============================================================
-- 形の比較: S は LR を直ちに含む（u = x または v = x と置くだけ）。
-- 逆向き（LR → S）は区間加法性 ∫ᵤᵛ = ∫ᵤˣ + ∫ₓᵛ が要る——つまり S の方が強い。
-- ============================================================

theorem right_of_straddle {f : Real → Real} {a b x : Real}
    (hax : a ≤ x) (h : HasStraddleDeriv f a b x) : HasRightDeriv f b x := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  exact ⟨δ, hδ, fun v J hxv hvb hδv hJ =>
    H x v J hax (le_refl x) (le_of_lt hxv) hvb hxv hδv hJ⟩

theorem left_of_straddle {f : Real → Real} {a b x : Real}
    (hxb : x ≤ b) (h : HasStraddleDeriv f a b x) : HasLeftDeriv f a x := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  exact ⟨δ, hδ, fun u J hau hux hδu hJ =>
    H u x J hau (le_of_lt hux) (le_refl x) hxb hux hδu hJ⟩

-- ============================================================
-- 最終定理の予定形（M4 以降で証明）:
--
-- theorem ftc_core (f : Real → Real) (a b x : Real)
--     (hax : a ≤ x) (hxb : x ≤ b) (hcont : ContinuousAt f x) :
--     HasStraddleDeriv f a b x
--
-- 証明の見込み: ε に対し連続性の δ を取る。u ≤ x ≤ v, v − u < δ なら
-- [u,v] 上の任意の t で Near δ x t なので Near ε (f x) (f t)。
-- 両側評価 f x − ε ≤ f t ≤ f x + ε を単調性で積分し（脱 abs ルート）、
-- 定数の積分 c·(v−u) で挟む。区間加法性すら不要——跨ぎ形の利点。
-- 実体化（Integral 関数で述べる古典的系・一意性の橋を 1 回使用）はその後。
-- ============================================================

#print axioms right_of_straddle
