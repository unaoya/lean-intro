# Ch4 有限和 — 帰納型と再帰

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 有限和とは何か
- 到達点: Range と Summation が読めて書ける。CH 対応表が完結する
- 新しい Lean 機能: 帰納型【鍵 3】・Subtype・構造的再帰・rfl=defeq の予告編
- コード: C04_Summation.lean（Proto/Sum 29 行 → ~25 行）

## 4.1 #print で種明かし — すべては帰納型だった

- Nat・And・Or・False・Eq を `#print`。Ch1 から使ってきた論理結合子の正体
- **CH 対応のパンチライン**: 原始は（依存）関数型だけ、残りは全部帰納型——「論理は依存関数と帰納型で実現できる」

## 4.2 自然演繹と recursor

- 導入則↔コンストラクタ・除去則↔recursor（`#print And.rec` / `Or.rec`）
- 🪟 窓: 自然演繹と recursor — 除去則の正体（induction タクティクの種明かしの予告）

## 4.3 Range — 証明を抱えた添字

- `Range n := { i : Nat // i < n }`（Subtype＝依存和の実物、CH 表 ∃ 行の Type 側親戚）
- incl / addone（隣接分点を安全に参照する 2 つの埋め込み）

## 4.4 Summation — 構造的再帰

- `(n : Nat) → (Range n → α) → α` という型自体が依存関数の実物
- コラム: なぜ List でないのか（表現の選択の損得勘定表——長さは型へ・整合性命題は消す）

## 4.5 計算で証明される定理

- summation_zero / summation_succ は **rfl で証明できる**（定義の再帰方程式＝defeq の予告編、Ch7 の主題へ）

## 演習

- Range の操作（incl/addone の値の確認を show で）・小さい n での Summation の手計算

## 引き

- 「和は書けた。分割をデータとしてどう表す？」
