-- テキスト用 Lean ソースの umbrella。`lake build Text` でビルドする。
-- 章ソース C01–C16 は線形の import 連鎖（章末の現在地マップに対応）。
-- 付録ソース A / B1–B3 は C14 と C15 の間に挟まる（C15 が部品として引用するため）。
-- Text/Proto/ は試作の記録（M1–M7、設計書参照）としてそのまま温存している。
import Text.C01_FirstProofs
import Text.C03_Class
import Text.C10_Automation
import Text.C16_FTC
