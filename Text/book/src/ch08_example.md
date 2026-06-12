# Ch8 具体例 — y = x の n 等分（到達点②）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: sorry を消し、具体例を計算する
- 到達点: equalPartition 上の RS = (n+1)/(2n) が証明できる（到達点②）
- 新しい Lean 機能: OfNat 物語の回収・Real.ofNat（構造的再帰）・NatCast・Div・cast 補題
- コード: C08_Numbers.lean（Proto: Numerals＋Cast 前半＋EqualPartition＋Example§2 → ~150 行）
- ⚠ 肥大時は 2 章に分割（分割の梯子 / y=x の計算）——執筆時判断

## 8.1 梯子①: 1 分割の sorry が消える日

- trivialPartition.increase を Ch6–7 の道具で完成（道具の最初の獲物）

## 8.2 梯子②: 2 等分 — リテラル 2 の正体

- `(2 : Real)` エラー（Ch3 の伏線）の回収: OfNat 1・Real.ofNat・OfNat (n+2) の設計。除法 `Div` の初登場（中点 (a+b)/2）

## 8.3 梯子③: n 等分 — NatCast

- 変数 n の埋め込み `↑i` とリテラル用 OfNat の対比。equalPartition（分点 a + i·(b−a)/m）の increase 証明
- 分点が i/n であることの確認（show の練習）

## 8.4 数の 2 つの建て方とダイヤモンドの規律（2026-06-12 議論）

- **(i) 代数一次（採用・mathlib 式）**: 0/1 は代数のフィールドが一次、cast はその上に建てる。リテラルは 0（Ch2・Zero bridge）/1（Ch6・One bridge）/2 以上（本章・Real.ofNat）で**担当を排他分割**——mathlib `Nat.AtLeastTwo` の手作り版。重なる点は cast 0 = 0 が**構成により rfl**、cast 1 = 1 は zero_add' で命題的（succ_ofNat が rfl なのはこの建て方のおかげ）
- **defeq の観察を機械で**（C08 の ANCHOR: cast_defeq）: `Real.ofNat 0 = 0 := rfl` は通り、`Real.ofNat 1 = 0 + 1 := rfl` で中身が見え、`#check_failure (rfl : Real.ofNat 1 = 1)` で **defeq でないこと自体がビルドで検証される**（公理には計算が無い——Ch7 の「2 種の等しさ」の実戦例）。命題的等式は cast_one := zero_add' 1
- **(ii) cast 一括ルート（演習: 試して壊す）**: 全リテラルを ofNat 経由にすると (1:Real) ≡ 0+1 が代数の one と defeq でない → one 系補題に橋が要り rfl が死ぬ。**ダイヤモンドの一般原則「①重なる経路は defeq に ②揃わないなら担当を排他分割」**——mathlib が AtLeastTwo を持つ理由が (ii) の失敗から分かる
- 菱形の縦糸の完成: Ch3 悪い菱形 → Ch4 良い配線（bridge）→ 本章 排他分割 → 付録 C で mathlib 実物

## 8.5 cast 補題 — 構成的な部分だけ

- succ_ofNat・cast_nonneg・cast_add・cast_lt・cast_le_succ
- **分割線の明示**: sup を使う archimedean 系は Ch11 へ送る——「この章は古典公理ゼロで済む」という公理の節約を設計として見せる

## 8.6 名物演習: sum_id

- `(1+1)·Σi = n·(n−1)` 形（リテラル 2 を使わない形がそのまま教材——なぜこの形かの議論込み）。帰納法＋cast 計算

## 8.7 RS = (n+1)/(2n)

- 右端タグで (n+1)/(2n)・左端タグで (n−1)/(2n)。「n→∞ で 1/2 に見える——だが極限はまだ定義していない」（第 II 部への遠い引き）

## 8.8 章末監査

- `#print axioms sum_id` = [Real, instLOF]——**古典論理ゼロ**（試作実測値）

## 引き

- 「具体例は計算できた。一般の分割で何が言えるか——性質を証明しよう」
