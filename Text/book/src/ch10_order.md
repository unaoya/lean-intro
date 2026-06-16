# Ch10 順序と calc — ≤/< のスカラー代数

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 新設: Ch7 の順序コーパス＋≤/< 混在 calc を独立章に（1章1テーマ） -->

- 前章からの問い: 等式は simp で畳めた。順序（≤/<）の補題はどう獲得し、どう鎖にするか
- 到達点: 順序の補題を **成り立つ最小の順序クラスで型多相に**述べる。`≤`/`<` 混在の calc が設計できる（Trans）
- 新しい Lean 機能: **順序クラスの階層**（OrderedAddCommMonoid→OrderedAddCommGroup→OrderedField→LinearOrderedField＝補題の最小構造）・**型多相な補題**・`≤`/`<` 混在の calc（Trans インスタンス）（`=` の calc は Ch1・rw は Ch8・simp は Ch9）
- コード: C10_Order.lean（最小クラスで述べた順序補題＋Trans・lin の型多相化）

## 10.1 補題を「成り立つ最小の順序クラス」で述べる

- **方針転換（2026-06-15）**: Ch4 のように Real へ公理を取り出すのは**やめる**。補題は最初から型多相で、**その補題が成り立つ最小の構造**を型クラスで明示する——「この事実は何があれば言えるか」を型が語る:
  - 加法と順序だけ（neg 不要）→ `OrderedAddCommMonoid`（le_refl/le_trans/add_le_add'・add_nonneg'）
  - 符号も要る → `OrderedAddCommGroup`（nonneg_iff_le・neg_le_neg'）
  - 乗法の非負性 → `OrderedField`（mul_nonneg・nonneg_mul_nonneg）
  - 線形性（le_total）→ `LinearOrderedField`
- コード上、この階層は C03 の代数階層（AddCommMonoid を土台に積み直す）の延長として置く。Ch4 の散文では LinearOrderedField を一括で読み、**中間の順序クラスは本章で初めて「補題の最小構造」として活用**する
- 推移律の変種（lt_trans・lt_le_trans・le_lt_trans）。`<` は Real の `LT`（≤∧≠）に依存するので Real 専用（順序クラスに lt を積む一般化は発展課題）

## 10.2 ≤/< 混在の calc を設計する

- `=` の calc は Ch1 既出。ここで `≤`/`<` を混ぜた鎖を組む——**Trans インスタンス**（le-le / lt-le / le-lt / Eq-le）が calc の機構を支える（種明かしの素材・Ch7 の「タクティクは機構で動く」の回収）
- 不等式の鎖の組み立て方（Ch11 の両側評価で初登場・Ch18 の FTC で繰り返し使う形）。simp/my_ring（Ch9）で等式変形の段を畳める

## 10.3 加法と順序・移項の小物

- 加法と順序（add_left_le・add_le_add'・nonneg_iff_le）・符号と差（neg_le_neg'・sub_le_sub）
- 移項の小物（lt_add_of_sub_lt・sub_lt_swap・sub_lt_self 等——両側評価の組み立て部品）

## 10.4 乗法の順序

- mul_nonneg・nonneg_mul_nonneg・mul_right_lt・**`zero_lt_one` は公理からの定理**（nontrivial の出番）・pos_inv・pos_mul_pos
- リテラル 2 はまだ無いので `1 + 1` で書く（リテラル機構は Ch12）

## 10.5 順序の自作タクティク — 2 方式の比較（ANCHOR `order_tac_demo`）

- Ch9 で等式を反射タクティクに任せた。順序も自作する（linarith は無い）。**2 つの設計を作って比べる**:
- **mono（順序のみ・構造的）**: 目標 `L ≤ R` の構造を下って単調性補題（add_le_add'・sub_le_sub）を適用し、葉を仮定で閉じる「gcongr-lite」。再帰 `macro_rules` で短く書ける。`f(a) ≤ f(b)` 型に強い
- **lin（順序体・意味的）**: `a ≤ b` を `0 ≤ b + -a` に帰し、**Ch9 の `my_ring`（一般化済）の正規化を流用**して `b + -a` を仮定差の和に正規化し非負を示す「linarith-lite」。**推移律 `a≤c`（from a≤b,b≤c）など線形結合**を扱える（mono は構造一致しないので不可）。my_ring が型多相になったので **lin もゴールの型 α を取り出して型多相**（任意の OrderedField で動く）
- 比較の要点: 構造的（mono）vs 意味的（lin）。**lin が代数基盤（my_ring）を再利用**するのが「順序体タクティク」の旨味。**lin を ≤ 核の直後に置き、`sub_le_sub` 等の派生補題を `by lin` で畳む**（「tactic を先に作って補題を畳む」設計）。一般の係数探索（LP）は係数1の仮定和に限定（発展）。`<` 版・乗法の単調性（符号条件付き）は発展課題

## 演習

- 順序ドリル（nonneg_iff_le / neg_le_neg' / sub_lt_swap 等を自分で）・混在 calc の鎖を 1 本設計

## 引き

- 「スカラー（1 個の実数）の代数は揃った。だが Σ（有限和）の性質は、項数 n についての帰納法が要る」
