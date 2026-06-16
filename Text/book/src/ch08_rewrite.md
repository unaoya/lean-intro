# Ch8 書き換えと 2 つの等しさ — rw と defeq

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 新設: Ch7 の等式コーパス＋旧 defeq 章の rw/defeq を統合（1章1テーマ） -->

- 前章からの問い: rw が効くときと効かないときがある。等しさには 2 種類あるのか
- 到達点: defeq（計算で同じ）と構文的等しさ（rw が見る）を区別できる。群・環の等式コーパスを rw/calc で獲得する
- 新しい Lean 機能: rw・defeq と rfl/show・term↔tactic の `▸`（`=` の calc は Ch1 既出）
- コード: C08_Rewrite.lean（等式/環コーパス本体: 消去・ゼロ・符号・引き算の整理・telescope_2）

## 8.1 等しさは 2 種類ある

- `a - b = a + -b := rfl` が通る——defeq（計算で同じ・カーネルが畳む）。だが rw は構文（見た目が同じ部分項）しか書き換えない
- show による defeq の言い換え（Ch7 の `show …` の正体）。「sub は a + -b の略記」を実感する。🪟 窓: 正規化と `#reduce` — 証明の簡約

## 8.2 種明かし: rw の正体

- `Eq.mpr`＋motive（congrArg）。`#print` で rw 証明の項を見る——なぜ構文的でなければならないかが機構で腑に落ちる
- **rw の罠 2 種（試作の実戦例）**: ① 意図しない部分項を先に潰す → 引数明示で回避 ② パターン捕獲（q を (q+q)/2 に書き換えると (p+q) 内の q も巻き込む）→ 独立補題への切り出しで回避

## 8.3 等式のスカラー代数コーパス

- 群・環の恒等式を rw/calc のドリルとして獲得: add_left_cancel'（Ch7 既出）を足場に、mul_zero'・zero_mul'・neg_zero・neg_neg・neg_mul・mul_neg・neg_add_distrib・mul_sub
- 引き算の整理（sub は a + -b）: sub_self・sub_zero・neg_sub・add_sub_cancel 系・add_sub_add・mul_sub_mul・add_four_comm
- ボス: telescope_2（`b − a = (c − a) + (b − c)`＝Ch11 の望遠鏡和の部品）・add_half_sub_full（E 部の誤差ずらし）

## 演習

- 等式ドリル（neg_neg / mul_sub / add_sub_cancel 等を自分で）・defeq か命題的等式かの判定ドリル（rfl が通るか #check_failure で確かめる）

## 引き

- 「等式を 1 本ずつ手で書いてきた。同じパターンを機械に任せられないか？——simp に教えよう」
