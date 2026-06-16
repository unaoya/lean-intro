# 発展 3 細分の機械 — 挿入・σ 写像・エンベロープ

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 役割: 発展 1 部品 (iii) の全文精読（E1–E3、約 1050 行）
- 本書最重量の機械。3 段で読む

## B.1 点の挿入の幾何（E1_Insert）

- find_interval（has_min の応用——Ch12 の探索の実戦）・insertPoint・点/長さ補題・insertPoint_fine（∀-Fine 形が保たれる）

## B.2 挿入によるリーマン和の変化（E2_InsertBound）

- Σ 補題の追加分（split_term——添字の組み替えのボス級）
- rs_insert_bound: 核となる等式 RS' − RS = (f c − f(ξk))·len k。**choice フリー**（監査小ネタ）
- rs_multi_insert_bound: m 点挿入の累積評価 m·((M+M)·δ)。find_interval 経由で choice が付く

## B.3 細分比較とエンベロープ（E3_Refine）

- rmin（素朴 if の min——証明装置として不可避。Ch12 の実験の実戦版）・stepAnti（区分定数の原始関数）・望遠鏡和で rs_refine_eq
- refine_parent（σ 写像の存在）・rs_refine_compare（挿入誤差 θ＋細分比較 B の合成）・rs_compare

## B.4 独立節: 振動和・|f| の可積分性・区間加法性

- 脱 abs ルート採用により **FTC 非依存になった発展話題**（参照実装 Oscillation/Abs/IntervalAdd の紹介）
- view（split_at の帰納原理 API 化）による整理の可能性（表現の切り替えの糸の回収）
