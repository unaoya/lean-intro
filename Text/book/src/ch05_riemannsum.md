# Ch5 リーマン和の定義 — 構造的再帰（Summation）と structure（到達点①）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆。構成v7 -->
<!-- 構成v7 再編（2026-06-17）: sumTo・sum_to_formula・recursor_reveal は第一部 Ch4/Ch5 へ移動。
     本章は Summation の定義から始め、リーマン和へ組み上げることに集中。 -->

- 前章からの問い: **第一部 Ch4 で sumTo（Nat→Nat の構造的再帰）を見た。それを族の和に一般化する**
- 到達点: Summation・Partition・RiemannSum が読めて書ける（**到達点①＝リーマン和の定義が書ける**）。ただし trivialPartition の `increase` が sorry のまま 1 つ残って幕
- 新しい Lean 機能: 構造的再帰（第一部 Ch4 の `Nat.rec` を依存 motive に拡張）・**open/dot 記法**（namespace 縦糸の回収）・structure（双子章・後編）・notation 自作・rfl=defeq の予告編
- コード: C05_Summation.lean（Summation・Partition・RiemannSum・IsRepr・leftRepr・trivialPartition。sumTo は第一部 Ch4・Range は第II部 Ch2・加群は Ch6）

## 書くべきこと

Summationの定義。パターンまっちによる定義。Natは直和ではなく帰納的に定義されているので少し難しいが、zeroかsuccのどちらかである。

自明な事実を証明してみる。rflで証明できる！

分割、代表点を定義すればリーマン和が定義できる。分割や代表点もstructureとして定義する。分割の例として自明な分割がある。等分割もあるが後で。increaseの照明が面倒？（実は簡単ではない？）あと自然数と実数を結びつける必要があるので。

## 5.1 Summation — 構造的再帰（ANCHOR `summation`）

- `(n : Nat) → (Range n → α) → α`（Range は Ch2 の Subtype 実例）。型自体が依存関数の実物。sumTo を「添字つき族 `Range n → α` の和」へ一般化したもの
- **(B) 依存関数型の項作り**が効く: motive `C n = (Range n → α) → α` が n に依存し、zero で `C 0` の項（空和 0）、succ で `C n` の項 `ih` から `C (n+1)` の項を組む。**再帰はそのまま・依存が加わった**——第一部 Ch4 の sumTo（非依存）との差分はこの一点
- パターンマッチ（zero/succ）による定義: zero で `0`、succ で「`Range n` 部分の和 ＋ 端の項 `f ⟨n, …⟩`」（`Range.incl` で添字を埋め込む）
- コラム: なぜ List でないのか（表現の選択の損得勘定表——長さは型へ・整合性命題は消す）

## 5.2 計算で証明される定理（ANCHOR `summation_rfl`）

- summation_zero / summation_succ は **rfl で証明できる**（定義の再帰方程式＝defeq の予告編、Ch8 の主題へ）

## 5.3 Summation について最初の証明（ANCHOR `summation_first_proofs`）

- Summation は `Nat.rec` で定義した。それを**除去規則として証明に走らせる**のが induction（第一部 Ch4 の recursor の回収）:
  - (1) `summation_congr`: `congrArg` だけ（除去規則すら不要）
  - (2) `summation_all_zero`: **term mode のまま**（`by` 不使用）`Nat.rec` の除去で全零和=0 を証明。succ の段の `summation_all_zero n` が IH そのもの
- **縦糸**: 「定義する再帰」と「証明する帰納」は同じ recursor。ergonomic な `cases`/`induction` タクティクは Ch7 以降、Σ 補題の本格コーパスは **Ch11**。第一部 Ch1（∨ の cases）→ 第一部 Ch4（`Nat.rec` の型を読む）→ Ch5（Nat の induction を term で）→ Ch11（タクティク＋コーパス）で除去規則の糸を張る
- ⚠ 第一部・Ch5 は term mode 基調。ここは `Nat.rec` による term mode の除去で `by` を使わない

## 5.4 証明を運ぶレコード — structure Partition

- points / increase / left / right——データ（分点列）と証明（広義単調・両端）が同居する依存レコード（ANCHOR `partition`）
- 双子章・後編: リトマス試験表の structure 側を埋める（∀ で量化する・名前で呼ぶ・2 つ目があって当たり前）
- 反転演習: 「Partition を class にしてみよ」→ 分割を走る ∀ が書けない。「LinearOrderedField を structure にしてみよ」→ `a + b` のたびに名指し。壊れたコードを読む

## 5.5 名前空間の旨味 — open と dot 記法（namespace 縦糸の回収）

- **旨味 1（`open Range`）**: 第一部 Ch2 で `namespace Range` を作り `Range.incl`/`Range.addone` と名付けた。`open Range` でこのファイルでは接頭辞 `Range.` を省いて `incl`/`addone` と書ける（Partition のフィールドが多用する）
- **旨味 2（dot 記法 `Δ.length`）**: `length` を `namespace Partition` に置くと `Δ : Partition n a b` に対し `Δ.length i`（＝`Partition.length Δ i`）と書ける。`Δ.points`・`Δ.IsRepr`・`Δ.leftRepr` も全部これ
- **縦糸の回収**: 第一部 Ch1/Ch4 で既存の名前空間を読む（アクセス）→ 第一部 Ch2 で `namespace Range` を作る → **Ch5 で開いて省く＋dot 記法**——名前空間の使い道が一周する

## 5.6 リーマン和の定義は 1 行

- length・RiemannSum（ANCHOR `riemann_sum`）。この 1 行に前章までの全部（class・帰納型・Subtype・構造的再帰・structure）が映っている
- 代表点系 IsRepr・leftRepr/rightRepr（ANCHOR `is_repr`・`endpoint_repr`）も定義として置く（妥当性 leftRepr_isRepr の**証明**は順序 le_refl が要るので Ch11）
- 入り込む証明は添字の Nat 不等式の項埋めのみ——2 幕構成の根拠を体感

## 5.7 記法の自作 — notation 初登場

- Σ 記法とリーマン和の記法を「定義したらすぐ」自作する（メタプログラミング導入の第 1 段）

## 5.8 クリフハンガー: trivialPartition

- 1 分割（分点 a・b——リテラルも除法も不要、自明の極み）を書き始める（ANCHOR `trivial_partition`）。`points` は **`match i.val with | 0 => a | _+1 => b`**——Nat の zero/succ で分岐（Summation と同じスタイル。if-then-else は Decidable を陰に持ち込むので避ける）。`left`/`right` は `rfl` で通る
- だが `increase` は添字の場合分けなしに書けない。**著者版（コード本体）は increase を完成させてあるが、読者版では `increase := sorry` のまま幕**——Ch7 タクティク入門の初仕事で読者自身が埋める演習にする（クリフハンガー）

## 演習

- 小さい n での Summation の手計算（`sumTo` は第一部 Ch4 を参照）
- **型シグネチャの設計**（本文素材）:
  - Summation の契約は最小の `[Add α] [Zero α]`（二項演算とゼロの値）。**意味論のクラス（Zero/One）とリテラル整形の窓口（OfNat）の分離**を本文で——core には Zero/One と一方向 bridge（Zero.toOfNat0/One.toOfNat1）が mathlib から昇格して入っており、本書は公理の zero を `instance : Zero Real` で登録するだけ（C04 の ANCHOR: zero_bridge）。「bridge は一方向・値は defeq」＝**良い菱形の規律**（Ch4 の悪い菱形トイデモの回収。数の建て方の本格論は cast 定義 Ch6・証明 Ch12）
  - 演習: `n` を implicit にできるか？ 変えてみて何が起きるか（依存型の見せ場が消える・rw の制御）
- コラム: mathlib の Σ 事情——`List.sum` は `[Add][Zero]` で足りるのに `Finset.sum` は AddCommMonoid を要求する（Finset＝順列で割った商なので well-definedness に可換性・結合性が要る）。**添字集合の表現を緩くすると代数の契約が重くなる**——「表現の選択」の糸との交差点

## 引き

- 「リーマン和は定義できた（到達点①）。だが trivialPartition の sorry を埋める道具がまだ無い。その前に——和や分割が住む**数学的構造**（加群・cast）を次章で見渡す」
