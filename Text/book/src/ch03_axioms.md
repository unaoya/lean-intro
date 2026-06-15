# Ch3 実数を公理で読む — 依存型・量化子・universe

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。read-axioms 章（2026-06-15 スワップで Ch2 から入替） -->

- 前章からの問い: 道具（構造と class）は揃った。実数の公理をどう読むか
- 到達点: C03_Axioms.lean の全行が「読める」。最初の実数証明が書ける
- 新しい Lean 機能: 依存型【鍵1】・∀/∃=Π/Σ・Prop vs Type・universe【鍵2】・axiom・namespace/open
- コード: C03_Axioms.lean（階層・公理5本・zero_bridge・根幹2行・check_failure・three_brothers）

> 執筆メモ（ユーザー・relocate 元 ch02）:
> - 実数の公理を書くことが目標。実数を構成するのではない（デデキンド切断やコーシー列の話はしない）。杉浦も公理的にやる。一言で言えば完備全順序体。
> - 一気にやると多すぎるので段階的に。まず群の公理から（Ch2 で見た構造の積み上げ）。

## 3.1 階層クラスを「読む」（ANCHOR `hierarchy`）

- AddCommGroup → … → LinearOrderedField の 5 段 extends 連鎖を読む。Ch2 の「構造＝データ」の見方で「公理を束ねたレコードの型」として読める
- 公理の編集という行為: 杉浦の R1〜R17 列挙との対比（公理設計の論点表: 0 はデータ・sup は Skolem 化・列挙でなく束）

## 3.2 公理 5 本（ANCHOR `axioms`）

- `axiom Real`・`axiom Real.instLOF`・sup 3 本。「信じるものはこれで全部」
- 🪟 窓: 公理と noncomputable — 実行コードの無い数（noncomputable の源泉 1）

## 3.3 Real.sup の署名精読 = 依存型【鍵 1】・∀∃ の導入/除去

- 「証明を引数に取り、型が項に依存する」関数。CH 表の **∀=Π・∃=Σ（帰納型）** 行を裏付け
- **導入/除去の縦糸を ∀∃ で埋める**: `∀ x, P x` は**依存関数**（→ と同じ関数・codomain が x に依存するだけ）——導入=`fun`／除去=適用。`∃ x, P x` は**帰納型 `Exists`**（依存和 Σ）——導入=`⟨a,h⟩`（証人＋証明）／除去=`.elim`（場合分け＝cases）。**→ ∀ ¬ は依存関数・∧ ∨ ∃ ⊥ ⊤ = は帰納型**——この「2 つの原始」への還元は Ch4 で `#print` 確認（CH 表のパンチライン回収）
- 🪟 窓: 「存在する」をデータに格上げする — Skolem 化と公理の構造化
- ∃ vs データ（0 をデータにする理由＝choose と監査）の本格議論はここ（Ch2 の予告を回収）

## 3.4 Prop vs Type・universe【鍵 2】

- Sort 階層。本書の全コードは Type 0 と Prop で完結する——その事実を universe 理解の素材に
- 🪟 窓: 証明無関係性と Prop — なぜ命題の宇宙は特別か

## 3.5 根幹の 2 行・class は自動で見つかる（最小機構の実物）

- `#check Real.instLOF`・`inferInstance`・`a + b` が解決される——Ch2 の「class＝自動で見つかる構造」の実物
- check_failure（ANCHOR `check_failure`）: 今 ℝ には 0 のインスタンスしかない → `(1:Real)`・`(2:Real)` はまだ失敗する（1 は Ch6・2 以上は Ch8 の伏線）。`#check_failure` で伏線がビルドに固定される
- ⚠ 解決の深い機構・ダイヤモンド事件は Ch8（NatCast の排他分割の動機として後置）

## 3.6 最初の実数証明: `<` の 3 兄弟（ANCHOR `three_brothers`）

- le_of_lt=射影・lt_of_le_of_ne=構成・ne_of_gt=¬は関数——Ch1 の論理が Real に着地する瞬間

## 演習

- 署名読解ドリル・`<` の 3 兄弟の変種・**sup 最小性実験**（sup 公理 3 行を消しても C05 までビルドが通ることを後で確認する予約）

## 引き

- 「実数は読めた。リーマン和には Σ が要る。有限和とは何か？」
