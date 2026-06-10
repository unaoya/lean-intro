import Lake
open Lake DSL

package «my_project» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- 実数の基礎（Structure, NatNum, Real, Lemmas）
lean_lib «RealNumbers» where
  globs := #[
    .one `MyProject.Numbers.Structure,
    .one `MyProject.Numbers.NatNum,
    .one `MyProject.Numbers.Real,
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
    .andSubmodules `MyProject.Integral
  ]
