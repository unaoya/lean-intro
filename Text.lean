-- テキスト用 Lean ソースの umbrella。`lake build Text` でビルドする。
-- 構成 v7（2026-06-16）:
--   第 I 部 = C01–C13 の線形 import 連鎖（命題=型 → 型の構成 → 構造と class → 実数 →
--     リーマン和の定義 → 数学的構造とその射 → 道具 4 章 → 帰納法+性質 → 数の体系 → y=x）。
--     到達点②＝C13 y=x・到達点③＝C11 性質
--   第 II 部 = C14–C18（アルキメデス→積分→一意性→直接計算→FTC ftc_of_integrable）
--   発展部 = ext4「フィルターで統一」のみ（mathlib 橋の読み物・コード未実装）。連続⇒可積分の
--     大規模証明（旧 E1–E5）は教材から外し、参照実装も削除した（2026-06-16）。
-- C01 は葉。C02_Types 以降は連鎖で入る（C18_FTC が終端）。
-- Text/Proto/ は試作の記録（M1–M7、設計書参照）としてそのまま温存している。
import Text.C01_FirstProofs
import Text.C02_Types
import Text.C03_Structures
import Text.C18_FTC
