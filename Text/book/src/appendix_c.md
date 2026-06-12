# 付録 C mathlib への橋

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 役割: 本書の各概念の mathlib 対応表と、次の一冊への導線

## C.1 対応表

- Real（公理）↔ mathlib の構成された ℝ（Cauchy 列の商——「公理的存在と定理的存在」Ch13 の議論の実例）
- Range/Summation ↔ Fin/Finset.sum・Partition ↔ BoxIntegral 系・IsIntegral ↔ Riemann/HK 積分
- 本書の補題 corpus ↔ mathlib の対応補題名（執筆時に表を作成）

## C.2 何が変わるか

- sSup は choose で定義される（完備性が定理になる世界）・Decidable と classical の扱い・simp/ring/linarith に任せてよくなる部分

## C.3 発展節: フィルターで統一する

- Filter＋Tendsto を自作（50〜100 行）し、IsLimAt・ContinuousAt・IsIntegral が同一概念の 3 インスタンスであることを同値定理 3 本の演習で
- 「3 種の ε-δ」の縦糸の完結・BoxIntegral への最短の橋

## C.4 次の一冊

- Mathematics in Lean を推薦（本書との読み替え表つき）
