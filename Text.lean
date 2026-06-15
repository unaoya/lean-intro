-- テキスト用 Lean ソースの umbrella。`lake build Text` でビルドする。
-- 構成 v4（2026-06-15）:
--   第 I 部 = 章ソース C01–C13 の線形 import 連鎖（リーマン和の定義→y=x→性質。
--     到達点②＝C12 y=x・到達点③＝C13 性質）。証明の弧は単一テーマに分割:
--     C06 タクティク入門 / C07 書き換えと2つの等しさ / C08 自動化と自作タクティク /
--     C09 順序と calc / C10 帰納法。数の体系 C11・y=x 具体例 C12・性質 C13
--   第 II 部 = C14–C18（アルキメデス→積分→一意性→直接計算→FTC ftc_of_integrable）
--   発展部「存在定理への登山」 = E1–E5（連続⇒可積分。本編の後に接続し主線は非依存）
-- C01/C02 は主線に import されない葉なので明示 import。C03 以降は連鎖経由で入る。
-- Text/Proto/ は試作の記録（M1–M7、設計書参照）としてそのまま温存している。
import Text.C01_FirstProofs
import Text.C02_Structures
import Text.C16_FTC
import Text.E5_Summit
