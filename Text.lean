-- テキスト用 Lean ソースの umbrella。`lake build Text` でビルドする。
-- 章ソースは線形の import 連鎖（章末の現在地マップに対応）。
-- 2026-06-12 決定: FTC は可積分仮定版（ftc_of_integrable）のみ——存在定理
-- （連続⇒可積分）の機構一式（旧 C15・A・B1–B3）は主線から削除した。
-- 全証明は Text/Proto/（試作の記録 M1–M7、設計書参照）に温存している。
import Text.C01_FirstProofs
import Text.C03_Class
import Text.C10_Automation
import Text.C16_FTC
