# Ch11 アルキメデスと探索 — ∃ から値を選び取る

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 値を「選び取る」とはどういう操作か
- 到達点: archimedean（白眉①）と exists_fine_partition。choice の侵入を監査で観察できる
- 新しい Lean 機能: ∃/obtain・Classical.em/by_cases・noncomputable def・**sup 公理の初使用**
- コード: C11_Archimedes.lean（Proto: Cast 後半＋EqualPartition(fine)＋Lemmas 古典部 → ~160 行）

## 11.1 第 II 部の開幕 — 何が変わるか

- 第 I 部は一度も「存在する」から値を取り出さなかった。極限を語るにはそれが要る
- 🪟 窓の予告: BHK の転調（本格的には Ch12）

## 11.2 ∃ から値を選び取る 3 つの方法

- (1) **sup**: 公理が Skolem 化済み——choice 不要でデータが手に入る（Ch2 の設計の回収）
- (2) **探索**: Nat の述語の最小値 has_min（strongRecOn）——choice 不要だが noncomputable
- (3) **分岐**: Classical.em / by_cases——命題で場合分けする権利（古典論理の入口）

## 11.3 白眉①: アルキメデス

- sup_near（sup のすぐ下に元がある）→ archimedean（∃ n, a < n）——**上限公理から有限性が出る**驚き
- 監査: ここで初めて Real.sup が `#print axioms` に現れる

## 11.4 探索の道具: has_min・natMin・ceil

- 古典順序補題（not_lt_imp_le 等——byContradiction）もここで初登場（**第 I 部に置けなかった理由**を監査で確認）

## 11.5 アルキメデスが細かい分割を製造する

- equalPartition_fine・**exists_fine_partition**（∀δ>0 に n 等分が応える）——第 II 部全体の燃料

## 11.6 素朴定義実験

- `max a b := if a ≤ b then b else a` を実際に書く → Decidable 失敗 → propDecidable → noncomputable → 監査に choice
- **Ch9 の種明かし**: 両側評価は abs の言い換えだった——主線が max/abs 抜きで設計されている理由
- コラム: 杉浦流「最小の継承的集合」と cast の像述語の同値（発展演習）

## 引き

- 「道具は揃った。『分割を細かくした極限』を定義しよう」
