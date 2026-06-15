# Ch9 リーマン和の性質 5 本（到達点③）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 一般の分割で何が言えるか
- 到達点: 後段が消費する性質 5 本（到達点③）。第 I 部古典ゼロの監査
- 新しい Lean 機能: なし（総合演習 II）。**IsRepr の定義は Ch5・幾何補題（points_mono 等）は Ch7 に移動済**——ここは「使う」側
- コード: C09_Properties.lean（性質 5 本＋反例。IsRepr=C05・幾何/tag_mem'=C07・equalPartitionRepr_isrepr=C08）

## 9.1 線形性 — RS は f について線形写像（加法＋スカラー倍）

- **線形性の本体は加法 `RS(f+g)=RS f+RS g` とスカラー倍 `RS(c·f)=c·RS f` の 2 本**（Σ の `additive_summation`・`summation_mul_left` の持ち上げ）。`riemann_sum_isLinear : IsLinearMap (fun f => RS f Δ ξ)`＝Ch7 の `summation_isLinear` の RS 版
- **符号 `RS(-f)=-RS f`（c=−1 の場合）と差 `RS(f-g)=RS f-RS g` はここから「出てくる」系**
- Σ→RS の 2 層対応（積分への 3 層対応の予告）

## 9.2 const — 望遠鏡和の快感

- `length_sum`（Σ length = b − a、telescope の回収）は **C07（Partition 幾何）**に配置。ここでは const がそれを消費
- ⚠ `sub_summation`（Σ の性質）は C07 へ・`length_sum`（Partition の性質）も C07 へ移動済（RS の性質ではないため・2026-06-15）

## 9.3 nonneg — 反例が「なぜ IsRepr が必須か」を実演する

- IsRepr（代表点の妥当性）は **Ch5 で定義済**。ここでは性質4で**使い**、タグを区間外にすると非負が**壊れる反例**で「妥当性条件が飾りでない」ことを見せる
- 使う道具: `tag_mem'`（タグは [u,v] 内）・`points_mono`・`length_nonneg`——いずれも **Ch7 で証明済**（読者自身の構造への帰納法の実地）

## 9.4 両側評価 rs_bound

- `lo·(v−u) ≤ RS ≤ hi·(v−u)`（sum_le_const / const_le_sum）。**abs を使わない**——理由は「第 II 部で明かす」と予告（Ch11 素朴定義実験への伏線）
- 生の不等式 2 本で書く（述語化しない——「同じ形が 3 回出たら昇格」の方針を一言）

## 9.5 章末監査 — 第 I 部の総決算

- 全定理の `#print axioms` が [Real, instLOF]（＋propext/Quot.sound の説明は最小限に留め Ch15 へ）
- 第 I 部は**構成的**——その意味の予告（BHK の転調は Ch11–12 で）

## 引き

- 「同じ証明パターンを何度繰り返しただろう。手を自動化しよう（間奏へ）」
