# Ch2 実数を 5 本の公理で読む — 依存型・量化子・universe

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 実数とは何か
- 到達点: C02_Axioms.lean の全行が「読める」。最初の実数証明が書ける
- 新しい Lean 機能: 署名の読み方・依存型・∀/∃=Π/Σ・Prop vs Type・universe・namespace/open
- コード: C02_Axioms.lean（Proto/Axioms 74 行 → ~60 行。Ch3 と共用）

## 2.1 署名が読めれば半分わかる

- ∀・→・暗黙引数 {}・instance 引数 []。読む練習: le_trans の署名

## 2.2 階層クラスを「読む」

- AddCommGroup → … → LinearOrderedField の 5 段 extends 連鎖を読む（class の機構は Ch3 に送る——ここでは「公理の束」として）
- 公理の編集という行為: 杉浦の R1〜R17 列挙との対比（公理設計の論点表: 0 はデータ・sup は Skolem 化・列挙でなく束）

## 2.3 公理 5 本

- `axiom Real`・`axiom Real.instLOF`・sup 3 本。「信じるものはこれで全部」
- 🪟 窓: 公理と noncomputable — 実行コードの無い数（noncomputable の源泉 1）

## 2.4 Real.sup の署名精読 = 依存型【鍵 1】

- 「証明を引数に取り、型が項に依存する」関数。CH 表の ∀=Π・∃=Σ 行を裏付け
- 🪟 窓: 「存在する」をデータに格上げする — Skolem 化と公理の構造化

## 2.5 Prop vs Type・universe【鍵 2】

- Sort 階層。本書の全コードは Type 0 と Prop で完結する——その事実を universe 理解の素材に
- 🪟 窓: 証明無関係性と Prop — なぜ命題の宇宙は特別か

## 2.6 最初の実数証明: `<` の 3 兄弟

- le_of_lt=射影・lt_of_le_of_ne=構成・ne_of_gt=¬は関数——Ch1 の論理が Real に着地する瞬間

## 演習

- 署名読解ドリル・`<` の 3 兄弟の変種・**sup 最小性実験**（sup 公理 3 行を消しても C05 までビルドが通ることを後で確認する予約）

## 引き

- 「公理は読めた。だが `a + b` の `+` はどこから来た？」
