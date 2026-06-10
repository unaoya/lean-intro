# Tsudoi6 — 微積分学の基本定理の形式化（mathlib 非依存）

Lean 4 で、実数を公理的に導入し（`MyProject/Axioms.lean`）、リーマン積分を構成して
微積分学の基本定理（FTC）を完全証明したプロジェクト。`sorry` ゼロ・警告ゼロ。

## 主定理（MyProject/Main.lean）

```lean
theorem main' (f : Real → Real) (a x : Real) (hf : Continuous f) :
    let F := fun x ↦ (OIntegral f a x); HasDerivAt F (f x) x
```

連続関数の不定積分（向き付き積分）は至るところ微分可能で、導関数は元の関数。

## 公理（MyProject/Axioms.lean に集約、計 5 本）

1. `Real : Type`
2. `Real.instLOF : LinearOrderedField Real` — 体と順序の公理
3. `Real.sup` / `Real.sup_ub` / `Real.sup_lub` — 連続性（上限公理）

アルキメデスの性質は上限公理から定理として導出（`Real/Cast.lean`）。
他は Lean 標準の `propext` / `Classical.choice` / `Quot.sound` のみ
（ルートモジュール `MyProject.lean` の `#print axioms main` で常時監査）。
実数は公理的導入で完結とし、構成的定義（Cauchy 列等）は扱わない。

## 構成

```
MyProject/
  Range.lean               Range・有限和 Summation・自然数の min
  Axioms.lean              代数構造のクラス階層＋実数の公理（5 本）
  Real/                    実数の基本補題（Algebra → Order → {Div, Sup} → Abs
                           → MinMax → Summation → Cast → Interval の鎖）
  Lemmas.lean              ↑の umbrella
  Limit.lean               極限（IsLimAt）
  Continuity.lean          連続性・一様連続性・有界性
  Deriv.lean               微分（HasDerivAt）
  Integral/
    Partition.lean         分割・TaggedPartition
    Insert.lean            分割への点挿入と小区間探索
    RiemannSum.lean        リーマン和と点挿入評価
    Refine.lean            細分比較（ステップ関数の原始関数・共通エンベロープ）
    Def.lean               積分の定義・等分割・一意性
    Criterion.lean         コーシー型可積分判定（sup 構成）
    Constant/Linearity/Bounded/IntervalAdd/Monotone   基本性質
    Oscillation.lean       振動和による |f| の評価
    Continuous.lean        連続 ⇒ 可積分
    Abs.lean               |f| の可積分性・三角不等式
    Oriented.lean          向き付き積分 OIntegral
  Main.lean                微積分学の基本定理
```

## ビルド

```
lake build
```
