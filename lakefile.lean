import Lake
open Lake DSL

package «lean_intro» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- 実数の基礎（Range/Summation・公理（クラス含む）・基本補題 Real/）
lean_lib «RealNumbers» where
  globs := #[
    .one `MyProject.Range,
    .one `MyProject.Axioms,
    .andSubmodules `MyProject.Real,
    .one `MyProject.Lemmas
  ]

-- 微積分学の基本定理（RealNumbers に依存）
@[default_target]
lean_lib «Calculus» where
  globs := #[
    .one `MyProject,
    .one `MyProject.Main,
    .one `MyProject.Deriv,
    .one `MyProject.Limit,
    .one `MyProject.Continuity,
    .andSubmodules `MyProject.Integral
  ]

-- 教材（Text/ 配下、MyProject 非依存・デフォルトビルド対象外）
lean_lib «Text» where
  globs := #[.andSubmodules `Text, .one `Text]

-- 教材 第一部「型と項で証明する」（Text/book/src/part1/ に md と lean を共置）
lean_lib «TextI» where
  srcDir := "Text/book/src/part1"
  roots := #[`Ch1_Types, `Ch2_Proposition, `Ch3_Calc, `Ch4_InductiveType]  -- Ch3_DependentFunction は Ch1_Types に統合

-- 別教材（Top/ 配下、mathlib 非依存・標準ライブラリのみ・デフォルトビルド対象外）
lean_lib «Top» where
  srcDir := "Top"
  roots := #[`Test]
