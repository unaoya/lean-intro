import Lake
open Lake DSL

-- 受講者用ファイル（tools/student.py が src/ から自動生成）。解答は含まない。
package «lean_intro_student» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib «LeanIntroStudent» where
  srcDir := "src"
  roots := #[`Intro1a, `CH1, `Intro1b, `CH2, `Intro2, `Top, `Extra, `Ascoli]
