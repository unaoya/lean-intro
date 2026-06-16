# Ch15 リーマン積分の定義

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 分割を細かくした極限をどう述べるか
- 到達点: IsIntegral / Integral が読めて書ける。監査 3 層が言える
- 新しい Lean 機能: dite＋choose・∫ 記法（Ch6 の再演）
- コード: C15_Integral.lean（Proto: Partition 残部＋Integral＋FTC(ContinuousAt) → ~70 行）

## 15.1 TaggedPartition と Fine

- 4 つ組（n・Δ・ξ・repr）を 1 変数に束ねる——∀ 量化のための structure（Ch5 の設計基準の再訪）
- 細かさは **∀ 形** `∀ i, length i < δ`（diam/max を使わない——Ch14 の素朴定義実験の帰結を設計に）

## 15.2 Near — 3 種の ε-δ の統一

- `Near ε c x := c − ε < x ∧ x < c + ε`（abs-free 両側形）。IsLimAt（演習）・ContinuousAt・IsIntegral が同じ語彙になる
- 「3 種の ε-δ は同じ形・違うのは添字集合」（Ch16 の非空性への伏線）

## 15.3 IsIntegral — 網目の極限

- ∀ε∃δ∀P の 3 段ネスト。杉浦の定義と一字一句対応
- コラム: 定義の選択肢（Darboux=sup で値が直接書ける／HK=δ を関数に／フィルター=発展節へ）

## 15.4 Integral 関数 — dite と choose

- `if h : a ≤ b ∧ IsIntegrable … then choose h.2 else 0`（junk 値の設計）
- 🪟 窓: 計算的読みの終わり — noncomputable という傷跡（choose の証明項は計算できない。BHK の転調）

## 15.5 ∫ 記法の自作（Ch6 の再演）

## 15.6 監査 3 層

- IsIntegral=[Real, instLOF]（古典ゼロ）／Integral=+choice（**choose と dite の propDecidable の 2 箇所**）／Integral'=+sup・choice フリー（証明引数版——「積分を関数として書く」発展節の入口）
- sup 最小性実験の対: Integral' だけが sup を使う

## 引き

- 「値は定義した。だがこの値、本当にひとつに決まっているのか？」
