# Ch6 sorry を埋める道具 — tactic mode と実数のスカラー代数

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 順序コーパス＋≤/< 混在 calc・Trans を C07 から統合 -->

- 前章からの問い: 残った sorry をどう埋めるか
- 到達点: 基本タクティクで短い証明が書ける。実数のスカラー代数（`=` と `≤`/`<`）の補題が獲得できる。`≤`/`<` 混在の calc が設計できる。「なぜタクティクで証明になるのか」に答えられる
- 新しい Lean 機能: by・ゴール状態・intro/exact/apply/rw/have/show・term↔tactic の往復・One bridge・≤/< 混在の calc（Trans）
- コード: C06_Tactics.lean（等式コーパス＋順序コーパス＋Trans → スカラー代数の道具箱）

## 6.1 by とゴール状態

- ゴール表示の読み方（Ch0 の体験の回収）。intro / exact から

## 6.2 apply と「穴」

- **apply の正体はメタ変数＋単一化**: ゴールに穴 `?m.123` を開けて埋める——`_` も暗黙引数も同じ穴（Ch2・Ch3 と機構レベルで接続）

## 6.3 rw・have・show

- 等式での書き換え（defeq の深掘りは Ch7）・補助ゴール・ゴールの言い換え。One bridge（`instance : One Real`——Ch4 Zero bridge の対・リテラル 1 の窓口）

## 6.4 種明かし: タクティクは証明項を書く機械

- by 証明を `#print` して生成された λ 項を見る。intro=fun・exact=項の埋め込み
- term と tactic の往復（同じ補題を両方で書く演習）

## 6.5 信頼の構造 — De Bruijn 基準

- タクティクは信じない。タクティクが吐いた項を検査する小さなカーネルだけを信じる
- 🪟 窓: カーネルと De Bruijn 基準 — 何を信じているのか

## 6.6 等式のスカラー代数コーパス

- 群・環の恒等式を rw/calc のドリルとして獲得: add_neg'・neg_neg・mul_sub・add_sub_cancel・telescope_2 など
- 「sub は a + -b の略記」——defeq の最初の実感（Ch7 への布石）

## 6.7 順序のスカラー代数コーパス

- 公理の取り出し: le_refl/le_trans/le_antisymm/le_total・add_le_add（**1 行の term mode 射影**——タクティク不要のものは正直にそう書く）
- 加法と順序（add_left_le・add_le_add'・nonneg_iff_le）・符号と差（neg_le_neg'・sub_le_sub）・移項の小物（lt_add_of_sub_lt・sub_lt_swap 等——両側評価の組み立て部品）
- 乗法の順序（mul_nonneg・nonneg_mul_nonneg・mul_right_lt）・**`zero_lt_one` は公理からの定理**（nontrivial の出番）・pos_inv・pos_mul_pos。リテラル 2 はまだ無いので `1 + 1` で書く（リテラル機構は Ch8）
- ⚠ 順序コーパスは等式コーパスの後（nonneg_iff_le 等が add/sub 恒等式を使う）

## 6.8 ≤/< 混在の calc を設計する

- `=` の calc は Ch1 既出。ここで `≤`/`<` を混ぜた鎖を組む——**Trans インスタンス**（le-le / lt-le / le-lt / Eq-le）が calc の機構を支える（種明かしの素材）
- 不等式の鎖の組み立て方（両側評価の証明で繰り返し使う形）

## 演習

- 等式ドリル（add_neg' / zero_add' / neg_neg 等）・順序ドリル（nonneg_iff_le / neg_le_neg' / sub_lt_swap 等を自分で）——需要駆動（trivialPartition と Ch7 以降が消費する分だけ）

## 引き

- 「rw が効くときと効かないときがある。等しさには 2 種類あるのか？」
