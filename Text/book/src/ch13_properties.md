# Ch13 リーマン和の性質 5 本（到達点③）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 一般の分割で何が言えるか
- 到達点: 後段が消費する性質 5 本（到達点③）。第 I 部古典ゼロの監査
- 新しい Lean 機能: **関数空間 `Real → Real` の中置代数**（`VectorSpace` が含む Add/Neg/SMul ＋ Sub インスタンスで `f + g`・`-f`・`c • f`・`f - g` を中置で——被積分関数を点ごと演算で扱い、線形性を `fun x => f x + g x` でなく `f + g` で述べる）。それ以外は総合演習 II。**IsRepr の定義は Ch5・幾何補題（points_mono 等）は Ch7 に移動済**——ここは「使う」側
- コード: C13_Properties.lean（性質 5 本＋反例。**関数空間の VectorSpace/Sub インスタンスを補題の前に置き f+g 表記で線形性を述べる**。IsRepr=C05・幾何/tag_mem'=C07・equalPartitionRepr_isrepr=C08）

## 9.1 線形性 — RS は f について線形写像（加法＋スカラー倍）

- **被積分関数の代数を中置で**: 関数空間 `Real → Real` の VectorSpace（Ch10）＋ Sub で `RS(f + g)`・`RS(c • f)`・`RS(-f)`・`RS(f - g)` と書く（点ごと演算・`(f+g) x = f x + g x` は `rfl`）。一般化した my_abel もこの関数空間でそのまま動く（順序は無いので lin は不可）
- **線形性は Ch10 の塔を合成して帰着**（一気に証明しない）: `RS f Δ ξ = WeightedSum Δ.length (i↦f(ξ i))` は defeq なので、`riemann_sum_isLinear = isLinear_comp (weightedSum_isLinear Δ.length) (precompose_isLinear ξ)` の**合成 1 行**。Σの線形性 → 重みつきΣの線形性 →（引き戻し）→ RS の線形性、と積み上がる
- **加法 `RS(f + g)=RS f+RS g`・スカラー倍 `RS(c • f)=c·RS f` は `riemann_sum_isLinear` の射影**（`.1`/`.2`）で 1 行・**符号 `RS(-f)=-RS f`（c=−1）と差 `RS(f-g)=RS f-RS g` はそこから出る系**
- Σ→重みつきΣ→RS の 3 層対応（積分への対応の予告）

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
