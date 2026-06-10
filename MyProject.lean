-- This module serves as the root of the `MyProject` library.
-- Import modules here that should be built as part of the library.
import MyProject.Main

-- 公理監査：主定理が依存する公理を常時表示する。
-- Real / Real.instLOF / Real.sup / Real.sup_ub / Real.sup_lub（＋Lean 標準の
-- propext / Classical.choice / Quot.sound）以外が現れたら退行を疑うこと。
#print axioms main
