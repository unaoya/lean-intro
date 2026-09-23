import Lake
open Lake DSL

-- 2往復構成に改める前の旧版（比較・参照用）。読む順 Intro1 → CH → Intro2 → Top → Extra。
package «lean_intro_original» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib «LeanIntroOriginal» where
  srcDir := "src"
  roots := #[`Intro1, `CH, `Intro2, `Top, `Extra,
    `Intro1Sol, `CHSol, `Intro2Sol, `TopSol, `ExtraSol]
