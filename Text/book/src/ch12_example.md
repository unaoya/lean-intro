# Ch12 具体例 — y = x の n 等分（到達点②）

<!-- 下書き（配置設計版）: 節立てメモ -->
<!-- 2026-06-15 分割: 旧 Ch11 の y=x 計算部。到達点② を実装で達成（旧 TODO） -->

- 前章からの問い: 数は建った。具体例（y=x のリーマン和）を計算する
- 到達点: [0,1] の n 等分・左端タグで **y=x の RS を閉じた式に**（到達点②）。`(1+1)·n²·RS = n²−n`（⟺ RS=(n−1)/(2n)）
- 新しい Lean 機能: なし（Ch11 の数＋Ch8 の自作タクティクの応用）
- コード: C12_Example.lean（§4 equalPartition §5 sum_id_real・riemann_sum_id）

## 12.1 一般の等分割と代表点

- `equalPartition`（分点 `a + i·(b−a)/m`）の `increase`/`left`/`right` 証明（除法補題の応用）・`equalPartition_length` = (b−a)/m・分点が i/n の確認（show の練習）
- 代表点は **C05 の一般 `leftRepr`/`rightRepr` を適用**（左端・右端は任意 Partition で IsRepr＝`equalPartitionRepr_isrepr` は `leftRepr_isRepr` の特例）——一般構成を y=x の前に確立

## 12.2 Nat の恒等式を cast で Real に運ぶ

- `Σ_{i<n} i` の閉じた式は **Nat の恒等式 `sum_id_nat`（Ch10）**: `(1+1)·Σi + n = n·n`（減算なし→cast がきれいに通る）
- **`sum_id_real`**: それを cast（射）で Real へ。`congrArg` で両辺を cast し、`cast_add`/`cast_mul`/**`cast_summation`（Σ と可換）** でばらす——Ch11 の「cast は射」が効く場面

## 12.3 リーマン和を畳む（ANCHOR `rs_id`）

- **`riemann_sum_id`**: RS = Σ_i (ξ_i · length_i)。各小区間の寄与 `ξ_i · length_i = (1/n²)·i` を **my_ring**（Ch8・`/` 対応）で畳み、Σ を `summation_mul_left` で外に出し、`sum_id_real` で閉じ、`n²·(1/n²)=1` を `Field.mul_inv` で相殺、最後の移項を **my_abel** で。**自作タクティクが到達点②を貫通**
- 分母を払った形 `(1+1)·n²·RS = n²−n` で証明（割った形 (n−1)/(2n) は将来の field タクティクで）。「n→∞ で 1/2 に見える——だが極限はまだ定義していない」（第 II 部への遠い引き）

## 12.4 章末監査

- `#print axioms riemann_sum_id` = [Real, propext, Quot.sound, instLOF]——**古典論理ゼロ**（choice/sup なし）。到達点②まで構成的に届いた

## 引き

- 「具体例は計算できた。一般の分割で何が言えるか——性質を証明しよう」
