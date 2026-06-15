# Ch5 分割とリーマン和の定義 — structure と notation（到達点①）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 分割をデータとしてどう表すか
- 到達点: **リーマン和の定義が書ける**（到達点①）。ただし sorry が 1 つ残って幕
- 新しい Lean 機能: structure（双子章・後編）・**open と dot 記法**（namespace 縦糸 3/3）・notation 自作
- コード: C05_RiemannSum.lean（Proto/Partition 定義部 → ~35 行）

## 5.1 証明を運ぶレコード — structure Partition

- points / increase / left / right——データと証明が同居する依存レコード
- 双子章・後編: リトマス試験表の structure 側を埋める（∀ で量化する・名前で呼ぶ・2 つ目があって当たり前）

## 5.2 反転演習

- 「Partition を class にしてみよ」→ 分割を走る ∀ が書けない。「LinearOrderedField を structure にしてみよ」→ `a + b` のたびに名指し。壊れたコードを読む

## 5.2b 名前空間の旨味 — open と dot 記法（namespace 縦糸 3/3）

- **旨味 1（`open Range`）**: Ch4 で `Range.incl`/`Range.addone` と名付けたが、`open Range` でこのファイルでは接頭辞 `Range.` を省いて `incl`/`addone` と書ける（Partition のフィールドが多用する）
- **旨味 2（dot 記法 `Δ.length`）**: `length` を `namespace Partition` に置くと `Δ : Partition n a b` に対し `Δ.length i`（＝`Partition.length Δ i`）と書ける。Lean は `Δ` の型 `Partition …` を見て同名 namespace から `length` を探し `Δ` を第 1 引数に差し込む。構造体フィールド `Δ.points` と同じ記法で自作関数も呼べる——`Δ.IsRepr`・`Δ.leftRepr` も全部これ
- **縦糸の回収**: Ch3 アクセス → Ch4 作る → **Ch5 開いて省く＋dot 記法**。3 段で名前空間の使い道が一周する

## 5.3 リーマン和の定義は 1 行

- length・RiemannSum。この 1 行に前章までの全部（class・帰納型・Subtype・構造的再帰・structure）が映っている
- 入り込む証明は添字の Nat 不等式の項埋めのみ——2 幕構成の根拠を体感

## 5.4 記法の自作 — notation 初登場

- Σ 記法とリーマン和の記法を「定義したらすぐ」自作する（メタプログラミング導入の第 1 段）

## 5.5 伏線回収: And も structure だった

- `#print And`（Ch1 の ⟨,⟩・.1/.2 が structure の機構そのものだった）

## 5.6 クリフハンガー: trivialPartition

- 1 分割（分点 a・b——リテラルも除法も不要、自明の極み）を書き始める——`increase` が添字の場合分けなしに書けない。**sorry のまま幕**

## 引き

- 「定義はできた。sorry を埋める道具が要る」
