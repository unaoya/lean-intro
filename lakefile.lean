import Lake
open Lake DSL

package «lean_intro» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- 教材本体（src/ 配下、mathlib 非依存・Lean 標準ライブラリのみ）。
-- 本文 8 ファイル（ファイル名の番号順）に加えて、
-- ✏ 練習の解答 *Sol も roots に入れてある＝解答も常に Lean に検査される。
lean_lib «LeanIntro» where
  srcDir := "src"
  roots := #[`«01_TypesAndTerms», `«02_Forall», `«03_InductiveTypes», `«04_Exists», `«05_MathematicalTools», `«06_Topology», `«07_Exercises», `«08_Ascoli»,
    `«01_TypesAndTermsSol», `«02_ForallSol», `«03_InductiveTypesSol», `«04_ExistsSol», `«05_MathematicalToolsSol», `«06_TopologySol», `«07_ExercisesSol», `«08_AscoliSol»]

-- Lean の検査に成功したあと、同じ本文から通読版・講義版の HTML/PDF を作る。
-- Lean の検査だけなら `lake build LeanIntro`。
@[default_target]
target textbook pkg : Unit := do
  let checked ← LeanIntro.fetch
  checked.mapM fun _ => do
    proc { cmd := "python3", args := #["-B", "tools/lean2html.py", "--if-needed"], cwd := some pkg.dir }
