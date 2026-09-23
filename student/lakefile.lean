import Lake
open Lake DSL

-- 受講者用ファイル（tools/student.py が src/ から自動生成）。解答は含まない。
package «lean_intro_student» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib «LeanIntroStudent» where
  srcDir := "src"
  roots := #[`«01_TypesAndTerms», `«02_Forall», `«03_InductiveTypes», `«04_Exists», `«05_MathematicalTools», `«06_Topology», `«07_Exercises», `«08_Ascoli», `«09_Covering»]
