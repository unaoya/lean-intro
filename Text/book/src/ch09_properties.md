# Ch9 リーマン和の性質 5 本（到達点③）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 一般の分割で何が言えるか
- 到達点: 後段が消費する性質 5 本（到達点③）。第 I 部古典ゼロの監査
- 新しい Lean 機能: なし（総合演習 II）——だが述語の設計（IsRepr）が初登場
- コード: C09_Properties.lean（Proto: FTCCore§分割補題＋Criterion§両側評価 → ~120 行）

## 9.1 additive / neg — Σ の線形性の持ち上げ

- Σ→RS の 2 層対応（積分への 3 層対応の予告）。sub は系として軽演習

## 9.2 const — 望遠鏡和の快感

- length_sum（Σ length = b − a、telescope_sum の回収）→ const_sum

## 9.3 nonneg — 反例が定義を生む

- タグが区間外なら非負にならない**反例**から IsRepr が必然として登場
- tag_mem・points_mono（Nat 帰納法の好例——well-founded 不要）・length_nonneg

## 9.4 両側評価 rs_bound

- `lo·(v−u) ≤ RS ≤ hi·(v−u)`（sum_le_const / const_le_sum）。**abs を使わない**——理由は「第 II 部で明かす」と予告（Ch11 素朴定義実験への伏線）
- 生の不等式 2 本で書く（述語化しない——「同じ形が 3 回出たら昇格」の方針を一言）

## 9.5 章末監査 — 第 I 部の総決算

- 全定理の `#print axioms` が [Real, instLOF]（＋propext/Quot.sound の説明は最小限に留め Ch16 へ）
- 第 I 部は**構成的**——その意味の予告（BHK の転調は Ch11–12 で）

## 引き

- 「同じ証明パターンを何度繰り返しただろう。手を自動化しよう（間奏へ）」
