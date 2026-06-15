# Ch9 順序と calc — ≤/< のスカラー代数

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 新設: Ch6 の順序コーパス＋≤/< 混在 calc を独立章に（1章1テーマ） -->

- 前章からの問い: 等式は simp で畳めた。順序（≤/<）の補題はどう獲得し、どう鎖にするか
- 到達点: 順序の補題コーパスを獲得する。`≤`/`<` 混在の calc が設計できる（Trans）
- 新しい Lean 機能: `≤`/`<` 混在の calc（Trans インスタンス）（`=` の calc は Ch1・rw は Ch7・simp は Ch8）
- コード: C09_Order.lean（順序基本＋Trans・加法と順序・移項の小物・乗法順序）

## 9.1 公理から順序の基本

- 公理の取り出し: le_refl/le_trans/le_antisymm/le_total・add_le_add（**1 行の term mode 射影**——Ch3 で一度見た「公理は定理」の本格展開）
- 推移律の変種（lt_trans・lt_le_trans・le_lt_trans）

## 9.2 ≤/< 混在の calc を設計する

- `=` の calc は Ch1 既出。ここで `≤`/`<` を混ぜた鎖を組む——**Trans インスタンス**（le-le / lt-le / le-lt / Eq-le）が calc の機構を支える（種明かしの素材・Ch6 の「タクティクは機構で動く」の回収）
- 不等式の鎖の組み立て方（Ch12 の両側評価で繰り返し使う形）。simp/my_ring（Ch8）で等式変形の段を畳める

## 9.3 加法と順序・移項の小物

- 加法と順序（add_left_le・add_le_add'・nonneg_iff_le）・符号と差（neg_le_neg'・sub_le_sub）
- 移項の小物（lt_add_of_sub_lt・sub_lt_swap・sub_lt_self 等——両側評価の組み立て部品）

## 9.4 乗法の順序

- mul_nonneg・nonneg_mul_nonneg・mul_right_lt・**`zero_lt_one` は公理からの定理**（nontrivial の出番）・pos_inv・pos_mul_pos
- リテラル 2 はまだ無いので `1 + 1` で書く（リテラル機構は Ch11）

## 9.5 順序の自作タクティク — 2 方式の比較（ANCHOR `order_tac_demo`）

- Ch8 で等式を反射タクティクに任せた。順序も自作する（linarith は無い）。**2 つの設計を作って比べる**:
- **mono（順序のみ・構造的）**: 目標 `L ≤ R` の構造を下って単調性補題（add_le_add'・sub_le_sub）を適用し、葉を仮定で閉じる「gcongr-lite」。再帰 `macro_rules` で短く書ける。`f(a) ≤ f(b)` 型に強い
- **lin（順序体・意味的）**: `a ≤ b` を `0 ≤ b−a` に帰し、**Ch8 の `my_ring`（D）の正規化を流用**して `b−a` を仮定差の和に正規化し非負を示す「linarith-lite」。**推移律 `a≤c`（from a≤b,b≤c）など線形結合**を扱える（mono は構造一致しないので不可）
- 比較の要点: 構造的（mono）vs 意味的（lin）。**lin が代数基盤（my_ring）を再利用**するのが「順序体タクティク」の旨味。一般の係数探索（LP）は係数1の仮定和に限定（発展）。`<` 版・乗法の単調性（符号条件付き）は発展課題

## 演習

- 順序ドリル（nonneg_iff_le / neg_le_neg' / sub_lt_swap 等を自分で）・混在 calc の鎖を 1 本設計

## 引き

- 「スカラー（1 個の実数）の代数は揃った。だが Σ（有限和）の性質は、項数 n についての帰納法が要る」
