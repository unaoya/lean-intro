-- テキスト用 Lean ソースの umbrella。`lake build Text` でビルドする。
-- 構成 v3（2026-06-13）:
--   本編 = 章ソース C01–C15 の線形 import 連鎖（FTC は可積分仮定版 ftc_of_integrable、Ch15）
--   発展部「存在定理への登山」 = E1–E5（連続⇒可積分とその機構。本編の後に接続し、
--   主線はこれに依存しない）
-- Text/Proto/ は試作の記録（M1–M7、設計書参照）としてそのまま温存している。
import Text.C01_FirstProofs
import Text.C02_Structures
import Text.C10_Automation
import Text.C15_FTC
import Text.E5_Summit
