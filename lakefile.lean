import Lake
open Lake DSL

package «lean_intro» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- 教材本体（src/ 配下、mathlib 非依存・Lean 標準ライブラリのみ）。
-- 本文 5 ファイル（読む順 Intro1 → CH → Intro2 → Top → Extra）に加えて、
-- ✏ 練習の解答 *Sol も roots に入れてある＝解答も常に Lean に検査される。
@[default_target]
lean_lib «LeanIntro» where
  srcDir := "src"
  roots := #[`Intro1, `CH, `Intro2, `Top, `Extra, `ExtraSol, `Intro1Sol, `CHSol, `Intro2Sol, `TopSol]
