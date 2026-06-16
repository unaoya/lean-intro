# Ch16 一意性 — choose の仕様書

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 積分値は本当にひとつに決まっているのか
- 到達点: integral_unique と橋。何が「アルキメデスの値段」かが言える
- 新しい Lean 機能: なし（証明パターンの章: ε/2 定石・min-free 合流）
- コード: C16_Unique.lean（Proto/Unique → ~90 行）

## 16.1 極限なのに一意が自明でない

- ε/2 論法自体は 2 行。点列で無料だった「添字はいくらでも先がある」が、分割ネットでは**「任意の δ より細かい分割の存在」＝アルキメデスの値段**（Ch12 の exists_fine_partition がここで請求される）
- vacuous truth の実例: b < a なら TaggedPartition が空で全 i が「積分値」になる——非空性が定理になる

## 16.2 min-free 合流 — exists_min2 イディオム

- 2 つの δ の合流を le_total の場合分け＋fine_mono で（min 関数を作らない——Ch12 の実験の帰結その 2）

## 16.3 integral_unique 精読

- le_of_forall_lt_add（∀ε で押さえる→≤）・両側 Near の突き合わせ

## 16.4 橋 — integral_eq_of_isIntegral

- 「choose が拾った値はあなたの導出した値に等しい」＝**choose の仕様書**。dif_pos と choose_spec の機構
- choose と sup の精密な関係（公理的存在は Skolem 化の自由・定理的存在は choose）

## 16.5 橋の応用 — 値の等式たち

- const の積分値 `∫c = c(b−a)` を橋で 1 本導出して見せる
- 線形性・単調性等の ε/2 持ち上げ（v1 対応表）は**発展演習**へ——落ち: **主線（FTC）はこれらを一切使わない**（Ch18 で種明かし）

## 引き

- 「理屈は揃った。実際に積分をひとつ、定義から直接計算してみせよう」
