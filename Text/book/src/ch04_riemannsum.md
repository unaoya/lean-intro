# Ch4 リーマン和の定義 — 帰納型・構造的再帰・structure（到達点①）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆。構成v6 -->

- 前章からの問い: 有限和と分割をデータとしてどう表すか
- 到達点: Range・Summation・Partition・RiemannSum が読めて書ける（**到達点①＝リーマン和の定義が書ける**）。CH 対応表が完結する。ただし trivialPartition の `increase` が sorry のまま 1 つ残って幕
- 新しい Lean 機能: 帰納型【鍵 3】・Subtype・構造的再帰・**namespace を作る＋open/dot 記法**（縦糸 2-3/3）・structure（双子章・後編）・notation 自作・rfl=defeq の予告編
- コード: C04_Summation.lean（Range・Summation・Partition・RiemannSum・IsRepr・leftRepr・trivialPartition。**加群は次章 Ch5 へ分離**）

## 書くべきこと

Subtypeについて書く必要がある。
Subtypeの作り方と使い方。
Subtypeの項の作り方と使い方。
型 a に対し、a上のPropがあればSubtypeが作れる。
Structureで定義するのと同じ？

Subtypeの例として、nより小さい自然数のなす型を作る。
これはさらにnを引数にもつ関数であることに注意する。
Range 0, Range 1などがそれぞれ型である。
集合論的には{0,1,\ldots,n-1}である。
Range n \to Range n+1をinclとaddoneの二つ作る。
incl k = k, addone k = k+1である。
ただし、条件を満たす証明（Prop型のi < nを型に持つ項）をつける必要がある。
これは要するにk < nならばk < n+1とk < n ならばk +1 < n + 1である。
すでに既存の証明が標準ライブラリにあるので流用する。

Summationの定義。
パターンまっちによる定義。
直和集合上の関数をどう定義するか？
Natは直和ではなく帰納的に定義されているので少し難しいが、
zeroかsuccのどちらかである。

自明な事実を証明してみる。
rflで証明できる！

分割、代表点を定義すればリーマン和が定義できる。
分割や代表点もstructureとして定義する。
分割の例として自明な分割がある。
等分割もあるが後で。
increaseの照明が面倒？（実は簡単ではない？）
あと自然数と実数を結びつける必要があるので。

## 4.1 #print で種明かし — すべては帰納型だった

- Nat・And・Or・False・Eq を `#print`。Ch1 から使ってきた論理結合子の正体
- **CH 対応のパンチライン**: 原始は（依存）関数型だけ、残りは全部帰納型——「論理は依存関数と帰納型で実現できる」

## 4.2 自然演繹と recursor

- 導入則↔コンストラクタ・除去則↔recursor（`#print And.rec` / `Or.rec`）
- 🪟 窓: 自然演繹と recursor — 除去則の正体（induction タクティクの種明かしの予告）

## 4.3 Range — 証明を抱えた添字

- `Range n := { i : Nat // i < n }`（Subtype＝依存和の実物、CH 表 ∃ 行の Type 側親戚）。`Range 0`・`Range 1`… がそれぞれ型（集合論の {0,…,n−1}）・`n` を引数に取る関数でもある
- **Subtype の項と関数の基本動作**（ANCHOR `range_intro`）: 項を作る = 値＋「範囲内」の証明を `⟨2, …⟩` で組む（導入）／取り出す = `.val`（除去）。**Range「から」の関数**（domain が Range・射影 `i.val`）と **Range「へ」の関数**（codomain が Range・値＋証明を添える）の 2 方向を最小例で見せる
- **依存型の限界の予告**: `Range 3` からの関数を `i.val` の `0/1/2` で場合分けすると、`i.val < 3` ゆえ 3 枝で尽きるはずなのに **Nat 全体の網羅にもう 1 枝（到達不能なダミー）が要る**——型 `Range 3` だけからは Lean が「i.val は 2 以下」を読めない。証明を使って網羅を絞るのは後の章（§4.12 trivialPartition も同じ構図——だから `increase` が sorry になる）
- incl / addone（ANCHOR `range_funcs`）は **Range「への」関数の実戦**——`Range n` の項から `Range (n+1)` の項を作る（値は同じ/+1、添える証明だけ既存補題 `Nat.lt_succ_of_lt`/`Nat.succ_lt_succ` で作り替える）。隣接分点を安全に参照する 2 つの埋め込み
- **名前空間を作る（namespace 縦糸 2/3）**: `namespace Range … end Range` で囲むと `incl` は外から `Range.incl` になる。Range に関わる操作を 1 つの接頭辞に束ね、衝突を避け、所属を名前で示す。Ch3＝既存の名前空間を読む（アクセス）の対＝**自分で作る**。`open` で省く・dot 記法の旨味はこの章の後半（§4.8）

## 4.4 Summation — 構造的再帰

- `(n : Nat) → (Range n → α) → α` という型自体が依存関数の実物
- コラム: なぜ List でないのか（表現の選択の損得勘定表——長さは型へ・整合性命題は消す）

## 4.5 計算で証明される定理

- summation_zero / summation_succ は **rfl で証明できる**（定義の再帰方程式＝defeq の予告編、Ch7 の主題へ）

## 4.6 帰納型を使う — 除去規則（recursor）と cases／induction

- **骨格**: どの帰納型にも **導入規則**（構成子＝値を作る）と **除去規則**（recursor＝値を使う）がある。除去規則は同じ形だが、**構成子が再帰的な引数を持つと、その分だけ帰納法の仮定 (IH) を受け取る**——再帰の有無が `cases` と `induction` を分ける
- **Ch1 の回収**: ∨ の `.elim`（or_swap・and_or_distrib の場合分け）は**∨ の除去規則＝cases**だった——∨ は非再帰なので IH 無し。Ch1 で既にやっていた
- **対比を機械で**（ANCHOR `eliminators`・`#check @Or.rec` / `#check @Nat.rec`）: `Or.rec` は各構成子の引数を受けるだけ（IH 無し＝cases）。`Nat.rec` は succ の段で `motive n`（＝IH）も受ける（Nat が再帰だから＝induction）。**IH が「再帰している箇所」にちょうど現れる**のが型に見える
- **CH 対応のパンチライン**（ANCHOR `ch_punchline`・Ch1 の表を回収）: `#print And`/`Or`/`Exists`/`False` で「これらは帰納型（構成子＋recursor）」が、`#check fun A B => A → B`/`fun P => ∀ n, P n` で「→/∀ は Π（依存関数）」が見える。**論理 = 依存関数（→ ∀ ¬）＋ 帰納型（∧ ∨ ∃ ⊥ ⊤ =）**——だから**2 つの原始（Π＋帰納型）の導入/除去規則だけ**で論理は尽きる
- **Summation について最初の証明**（ANCHOR `summation_first_proofs`）: Summation は `Nat.rec` で定義した。それを**除去規則として証明に走らせる**のが induction:
  - (1) `summation_congr`: `congrArg` だけ（除去規則すら不要）
  - (2) `summation_all_zero`: **term mode のまま**（`by` 不使用）`Nat.rec` の除去で全零和=0 を証明。succ の段の `summation_all_zero n` が IH そのもの
- **縦糸**: 「定義する再帰」と「証明する帰納」は同じ recursor。ergonomic な `cases`/`induction` タクティクは Ch6 以降、Σ 補題の本格コーパスは **Ch10**。Ch1（∨ の cases）→ Ch4（Nat の induction）→ Ch10（タクティク＋コーパス）で除去規則の糸を張る
- ⚠ Ch1–5 は term mode 基調。ここは `Nat.rec` による term mode の除去で `by` を使わない

## 4.7 証明を運ぶレコード — structure Partition

- points / increase / left / right——データ（分点列）と証明（広義単調・両端）が同居する依存レコード（ANCHOR `partition`）
- 双子章・後編: リトマス試験表の structure 側を埋める（∀ で量化する・名前で呼ぶ・2 つ目があって当たり前）
- 反転演習: 「Partition を class にしてみよ」→ 分割を走る ∀ が書けない。「LinearOrderedField を structure にしてみよ」→ `a + b` のたびに名指し。壊れたコードを読む

## 4.8 名前空間の旨味 — open と dot 記法（namespace 縦糸 3/3）

- **旨味 1（`open Range`）**: §4.3 で `Range.incl`/`Range.addone` と名付けたが、`open Range` でこのファイルでは接頭辞 `Range.` を省いて `incl`/`addone` と書ける（Partition のフィールドが多用する）
- **旨味 2（dot 記法 `Δ.length`）**: `length` を `namespace Partition` に置くと `Δ : Partition n a b` に対し `Δ.length i`（＝`Partition.length Δ i`）と書ける。Lean は `Δ` の型 `Partition …` を見て同名 namespace から `length` を探し `Δ` を第 1 引数に差し込む。`Δ.points`・`Δ.IsRepr`・`Δ.leftRepr` も全部これ
- **縦糸の回収**: Ch3 アクセス → Ch4 作る → **Ch4 後半 開いて省く＋dot 記法**。3 段で名前空間の使い道が一周する

## 4.9 リーマン和の定義は 1 行

- length・RiemannSum（ANCHOR `riemann_sum`）。この 1 行に前章までの全部（class・帰納型・Subtype・構造的再帰・structure）が映っている
- 代表点系 IsRepr・leftRepr/rightRepr（ANCHOR `is_repr`・`endpoint_repr`）も定義として置く（妥当性 leftRepr_isRepr の**証明**は順序 le_refl が要るので Ch10）
- 入り込む証明は添字の Nat 不等式の項埋めのみ——2 幕構成の根拠を体感

## 4.10 記法の自作 — notation 初登場

- Σ 記法とリーマン和の記法を「定義したらすぐ」自作する（メタプログラミング導入の第 1 段）

## 4.11 伏線回収: And も structure だった

- `#print And`（Ch1 の ⟨,⟩・.1/.2 が structure の機構そのものだった）

## 4.12 クリフハンガー: trivialPartition

- 1 分割（分点 a・b——リテラルも除法も不要、自明の極み）を書き始める（ANCHOR `trivial_partition`）。`points` は **`match i.val with | 0 => a | _+1 => b`**——Nat の zero/succ で分岐（§4.6 のパターンマッチ・Summation と同じスタイル。if-then-else は Decidable を陰に持ち込むので避ける）。`left`/`right` は `rfl` で通る
- だが `increase` は **添字の場合分けなしに書けない**——読者版では **sorry のまま幕**（Ch6 タクティク入門の初仕事で埋める）

## 演習

- Range の操作（incl/addone の値の確認を show で）・小さい n での Summation の手計算
- **型シグネチャの設計**（本文素材）:
  - Summation の契約は最小の `[Add α] [Zero α]`（二項演算とゼロの値）。**意味論のクラス（Zero/One）とリテラル整形の窓口（OfNat）の分離**を本文で——core には Zero/One と一方向 bridge（Zero.toOfNat0/One.toOfNat1）が mathlib から昇格して入っており、本書は公理の zero を `instance : Zero Real` で登録するだけ（C03 の ANCHOR: zero_bridge）。「bridge は一方向・値は defeq」＝**良い菱形の規律**（Ch3 の悪い菱形トイデモの回収。数の建て方の本格論は cast 定義 Ch5・証明 Ch11）
  - 演習: `n` を implicit にできるか？ 変えてみて何が起きるか（依存型の見せ場が消える・rw の制御）——implicit 引数は Ch2 で読み、Ch4 で自分の定義に書き、Ch6 で機構を種明かしする 3 段配置
- コラム: mathlib の Σ 事情——`List.sum` は `[Add][Zero]` で足りるのに `Finset.sum` は AddCommMonoid を要求する（Finset＝順列で割った商なので well-definedness に可換性・結合性が要る）。**添字集合の表現を緩くすると代数の契約が重くなる**——「表現の選択」の糸との交差点

## 引き

- 「リーマン和は定義できた（到達点①）。だが trivialPartition の sorry を埋める道具がまだ無い。その前に——和や分割が住む**数学的構造**（加群・cast）を次章で見渡す」
