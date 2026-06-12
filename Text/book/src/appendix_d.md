# 付録 D my_ring を作る — proof by reflection

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 役割: Ch10 の入口の続き。柱 B（道具を開ける）の完結（飛ばしても本線に影響なし）
- コード: MyProject/Tactic/ または Text 付録ソース（P4 開発）

## D.1 発想 — 表現の切り替えの極限

- 操作側の表現を「計算」にまで磨く: 多項式 AST（帰納型の応用回収）→ 正規形（ソート済み単項式リスト）→ DecidableEq で比較

## D.2 健全性

- `eval ρ e = eval ρ (norm e)` を帰納法で——輸送補題としての健全性定理

## D.3 reify と elab

- 項から AST への持ち上げ（elab は最小限）。「reify → 健全性適用 → decide / rfl」

## D.4 完成と回収

- Ch8 の手計算・Ch14 の代数小物が 1 行になる
- **omega や decide が「どういう種類の物体か」、作ったから分かる**——柱 B の到達点。リフレクション＝「証明はプログラムである」（CH 対応との合流）
- linarith は読み物。mathlib の ring / linarith への接続
