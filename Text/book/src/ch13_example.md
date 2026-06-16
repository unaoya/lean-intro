# Ch13 具体例 — y = x の n 等分（到達点②）

<!-- 下書き（配置設計版）: 節立てメモ。本文未執筆。構成v6 -->
<!-- 構成v6: equalPartition の完成は Ch12 へ。本章は y=x の計算に純化 -->

- 前章からの問い: 数は建ち、等分割も完成した。具体例（y=x のリーマン和）を計算する
- 到達点: [0,1] の n 等分・左端タグで **y=x の RS を閉じた式に**（到達点②）。`(1+1)·n²·RS = n²−n`（⟺ RS=(n−1)/(2n)）
- 新しい Lean 機能: なし（Ch12 の数・等分割＋Ch9 の自作タクティクの応用）
- コード: C13_Example.lean（sum_id_real・riemann_sum_id。equalPartition は Ch12 で完成済み）

## 13.1 等分割と代表点の回収（Ch12）

- **等分割 `equalPartition`（分点 `a + i·(b−a)/m`）は Ch12 で完成済み**——`increase`/`left`/`right` も `equalPartition_length` = (b−a)/m も。ここではそれを [0,1]・左端タグで使うだけ
- 代表点は Ch5 の一般 `leftRepr`、妥当性は `equalPartitionRepr_isrepr`（Ch11 `leftRepr_isRepr` の特例）

## 13.2 Nat の恒等式を cast で Real に運ぶ

- `Σ_{i<n} i` の閉じた式は **Nat の恒等式 `sum_id_nat`（Ch11）**: `(1+1)·Σi + n = n·n`（減算なし→cast がきれいに通る）
- **`sum_id_real`**: それを cast（射）で Real へ。`congrArg` で両辺を cast し、`cast_add`/`cast_mul`/**`cast_summation`（Σ と可換）** でばらす——Ch12 の「cast は射」が効く場面

## 13.3 リーマン和を畳む（ANCHOR `rs_id`）

- **`riemann_sum_id`**: RS = Σ_i (ξ_i · length_i)。各小区間の寄与 `ξ_i · length_i = (1/n²)·i` を **my_ring**（Ch9・`/` 対応）で畳み、Σ を `summation_mul_left` で外に出し、`sum_id_real` で閉じ、`n²·(1/n²)=1` を `Field.mul_inv` で相殺、最後の移項を **my_abel** で。**自作タクティクが到達点②を貫通**
- 分母を払った形 `(1+1)·n²·RS = n²−n` で証明（割った形 (n−1)/(2n) は将来の field タクティクで）。「n→∞ で 1/2 に見える——だが極限はまだ定義していない」（第 II 部への遠い引き）

## 13.4 章末監査

- `#print axioms riemann_sum_id` = [Real, propext, Quot.sound, instLOF]——**古典論理ゼロ**（choice/sup なし）。到達点②まで構成的に届いた

## 引き

- 「具体例は計算できた。第 I 部（構成的な世界）はここで閉じる。第 II 部では sup と choice を入れ、積分そのものを定義する——BHK の転調へ」
