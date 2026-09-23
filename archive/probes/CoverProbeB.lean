/-!
# 試作B: 「一意持ち上げ」interface と共通の代数層

被覆理論を二層に分ける:

1. **持ち上げ補題** — 空間の種類に依存する(グラフ: リストの帰納法/位相空間:
   コンパクト性)。ここでは公理化して仮定する。
2. **その上の代数** — モノドロミー、π₁ のファイバー作用、ファイバー間の全単射。
   持ち上げ補題だけから出る。この試作はこの層を一度だけ書く。

グラフの被覆と位相空間の被覆は、この interface の2つの実例になる予定。
「離散と連続の類似」は、同じパラメータつき定理の2つの instantiation という
形式化された事実になる。
-/

namespace CoverProbe

/-- 「道のホモトピー類の連接構造」の抽象化。
    実例: グラフの π₁ 亜群(既約語)、位相空間の基本亜群。 -/
structure PathSystem (X : Type) where
  Hom : X → X → Type
  refl : (x : X) → Hom x x
  trans : {x y z : X} → Hom x y → Hom y z → Hom x z
  symm : {x y : X} → Hom x y → Hom y x
  refl_trans : ∀ {x y : X} (γ : Hom x y), trans (refl x) γ = γ
  trans_refl : ∀ {x y : X} (γ : Hom x y), trans γ (refl y) = γ
  trans_assoc : ∀ {x y z w : X} (γ : Hom x y) (δ : Hom y z) (ε : Hom z w),
    trans (trans γ δ) ε = trans γ (trans δ ε)
  symm_trans : ∀ {x y : X} (γ : Hom x y), trans (symm γ) γ = refl y
  trans_symm : ∀ {x y : X} (γ : Hom x y), trans γ (symm γ) = refl x

/-- 被覆の抽象化: ファイバー族 `F` と、道のホモトピー類に沿った一意持ち上げが
    定める輸送 `transport`。「持ち上げの一意存在」を証明したあとに得られる
    データがちょうどこれである。 -/
structure LiftSystem {X : Type} (P : PathSystem X) (F : X → Type) where
  transport : {x y : X} → P.Hom x y → F x → F y
  transport_refl : ∀ (x : X) (a : F x), transport (P.refl x) a = a
  transport_trans : ∀ {x y z : X} (γ : P.Hom x y) (δ : P.Hom y z) (a : F x),
    transport (P.trans γ δ) a = transport δ (transport γ a)

namespace LiftSystem

variable {X : Type} {P : PathSystem X} {F : X → Type} (L : LiftSystem P F)

/-! ## ここから下がグラフと位相空間で共有される「代数層」 -/

theorem transport_symm_transport {x y : X} (γ : P.Hom x y) (a : F x) :
    L.transport (P.symm γ) (L.transport γ a) = a := by
  rw [← L.transport_trans, P.trans_symm, L.transport_refl]

theorem transport_transport_symm {x y : X} (γ : P.Hom x y) (b : F y) :
    L.transport γ (L.transport (P.symm γ) b) = b := by
  rw [← L.transport_trans, P.symm_trans, L.transport_refl]

/-- モノドロミーは単射。 -/
theorem transport_injective {x y : X} (γ : P.Hom x y) {a a' : F x}
    (h : L.transport γ a = L.transport γ a') : a = a' := by
  have h' := congrArg (L.transport (P.symm γ)) h
  rw [L.transport_symm_transport, L.transport_symm_transport] at h'
  exact h'

/-- モノドロミーは全射。 -/
theorem transport_surjective {x y : X} (γ : P.Hom x y) (b : F y) :
    ∃ a : F x, L.transport γ a = b :=
  ⟨L.transport (P.symm γ) b, L.transport_transport_symm γ b⟩

/-- **ファイバーの同型**: 道 `γ : x → y` があればファイバー `F x` と `F y` は
    全単射。「連結な底空間の被覆のファイバーはすべて同じ大きさ」の抽象形。 -/
def fiberEquiv {x y : X} (γ : P.Hom x y) :
    { fg : (F x → F y) × (F y → F x) //
      (∀ a, fg.2 (fg.1 a) = a) ∧ (∀ b, fg.1 (fg.2 b) = b) } :=
  ⟨(L.transport γ, L.transport (P.symm γ)),
    L.transport_symm_transport γ, L.transport_transport_symm γ⟩

/-! ## モノドロミー作用

基点 `x` のループ `P.Hom x x` は `trans` を積、`refl x` を単位元、`symm` を
逆元として群をなす(群の公理は `PathSystem` の公理そのもの)。その `F x` への
作用の法則も `LiftSystem` の公理そのものである:

* `transport_refl` — 単位元は恒等に作用
* `transport_trans` — 積の作用は作用の合成

つまり「π₁ がファイバーにモノドロミーで作用する」という定理は、この interface
の水準では**公理の言い換え**になる。各論(グラフ/位相空間)の仕事はすべて
「一意持ち上げの証明」に集約される。 -/

theorem monodromy_one {x : X} (a : F x) :
    L.transport (P.refl x) a = a := L.transport_refl x a

theorem monodromy_mul {x : X} (γ δ : P.Hom x x) (a : F x) :
    L.transport (P.trans γ δ) a = L.transport δ (L.transport γ a) :=
  L.transport_trans γ δ a

end LiftSystem

/-- 健全性チェック: 自明な被覆(1点ファイバー)は任意の `PathSystem` 上の
    `LiftSystem` になる。 -/
example {X : Type} (P : PathSystem X) : LiftSystem P (fun _ => Unit) where
  transport _ _ := ()
  transport_refl _ _ := rfl
  transport_trans _ _ _ := rfl

end CoverProbe
