# 付録 A 一様連続性を読む

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 役割: Ch15 部品 (i) の全文精読（Proto/UnifCont 307 行 → 付録ソース）
- 読み物として独立（本線は statement で通過済み）

## A.1 Near/NearLe ツールキットの拡張

- near_symm / near_trans / nearle_near_trans / near_mono / nearle_to_near——「両側述語の三角不等式群」

## A.2 min を使わない合流

- exists_min2（le_total 場合分け）・exists_abs_bound（|f u| の代替境界）——脱 min/abs の徹底が証明をどう変えるか

## A.3 連結性論法 — sup 帰納

- S(t) = 「[u,t] 上 ε-一様連続」。sup が v に達することの背理法（t₀ の取り出し・c の δc-近傍での貼り合わせ・c+η への延長）
- 数学的注: u ≤ v で成立（u < v は不要——試作で判明）

## A.4 有界性 — 鎖の帰納法

- δ/2 刻みの N 歩（ceil=アルキメデス）・NearLe k (f u) (f t) の帰納——abs 版より素直になる例
