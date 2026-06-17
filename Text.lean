-- テキスト用 Lean ソースの umbrella（第二部以降）。`lake build Text` でビルドする。
-- 構成 v8（2026-06-17）:
--   第一部「型と項で証明する」= Text/book/src/part1/（Ch1_Proposition〜Ch5_Calc・md と lean を共置）。
--     lean_lib «TextI»（`lake build TextI`）で別ターゲット。命題=型 → 型を作る → 依存関数 →
--     帰納型と再帰 → calc。
--   第二部「リーマン和と道具」= C03_Structures〜C13_Example（構造と class → 実数 → リーマン和 →
--     構造の射 → 道具 4 章 → 帰納法+性質 → 数の体系 → y=x）。
--   第三部「積分と FTC」= C14_Archimedes〜C18_FTC。
--   発展部 = ext4「フィルターで統一」（mathlib 橋の読み物・コード未実装）。
-- C03_Structures は第一部 Ch2_Types（TextI）を import。連鎖で C18_FTC が終端。
-- Text/Proto/ は試作の記録（M1–M7、設計書参照）としてそのまま温存している。
import Text.C03_Structures
import Text.C18_FTC
