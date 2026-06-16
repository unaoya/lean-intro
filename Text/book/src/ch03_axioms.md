# Ch3 実数を公理で読む — 依存型・量化子・universe

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。read-axioms 章（2026-06-15 スワップで Ch2 から入替） -->

- 前章からの問い: 構造の機構と Nat の裸の演算子クラスは揃った。それに**法則を被せた階層**で実数の公理をどう読むか
- 到達点: C03_Axioms.lean の全行が「読める」。最初の実数証明が書ける
- 新しい Lean 機能: class の階層（extends の塔）・依存型【鍵1】・∀/∃=Π/Σ・Prop vs Type・universe【鍵2】・axiom・namespace/open
- コード: C03_Axioms.lean（階層・公理5本・zero_bridge・根幹2行・check_failure・three_brothers）
- **役割分担**: この章は「法則を被せた**階層**」——Ch2 の演算子クラス（Add 等）に結合律・可換律…を被せて class で積み上げ（モノイド→群→環→体→順序）、実数を全順序体として読む。依存型・∀∃・universe・ダイヤモンドもここ

> 執筆メモ（ユーザー・relocate 元 ch02）:
> - 実数の公理を書くことが目標。実数を構成するのではない（デデキンド切断やコーシー列の話はしない）。杉浦も公理的にやる。一言で言えば完備全順序体。
> - 一気にやると多すぎるので段階的に。まず群の公理から（Ch2 で見た構造の積み上げ）。

## ここで書くべきこと

目標は微積分学の基本定理だが、実数は公理的に扱う。
集合論的に構成するわけではない。
一言で言えば、完備な全順序体の理論である。
完備性（あるいは連続性）は後で扱うことにして、
ここでは全順序体（あるいはそのような数学的構造）をleanでどのように扱うかの一例を紹介する。
実際にはmathlibを用いるのがいい。
mathlibそのものではないが、それに近い実装。

（Natが標準ライブラリで持つ構造 Add/Mul/Zero/One/Sub/LE/LT＝演算子クラスは Ch2 §2.2b に移動。
　名前が notation と対応することも Ch2 で。ここではそれを受けて、法則を被せた階層を class で積む。）

Ch2 の演算子クラス（裸の Add など）に法則を被せていく:
モノイド、群、環、体、それらと整合的な順序構造。
これらを順に拡張する（extends の塔）。
最後にダイヤモンド（同じ型に構造が 2 経路で載るときの合流の規律）。



## 3.1 階層クラスを「読む」— 演算子クラスに法則を被せる（ANCHOR `hierarchy`）

- **Ch2 の Nat 演算子クラス（裸の `Add`）に法則を被せる**: `class AddCommMonoid extends Add` は「`Add`（二項演算）＋結合律・可換律・単位律」を束ねた class。AddCommMonoid → AddCommGroup（逆元）→ CommRing（乗法）→ Field（逆元）→（順序を被せて）→ LinearOrderedField の extends の塔を読む。Ch2 の「構造＝データ」「class＝自動で見つかる構造」の見方で「公理を束ねたレコードの型」として読める
- 加法は「可換モノイド（逆元なし）→ 可換群（逆元あり）」の 2 段で積む——**補題が成り立つ最小構造**を分ける土台（活用は Ch9）。順序の中間クラス（OrderedAddCommMonoid 等）はコードに在るが、Ch3 では LinearOrderedField を**頂点として一括で**読み、最小構造の使い分けは Ch9 へ送る
- **階層の菱形（ダイヤモンドの予告）**: 順序を被せる段の `OrderedAddCommGroup extends AddCommGroup, OrderedAddCommMonoid` で親 `AddCommMonoid` が 2 経路で来ても **1 つに合流する**のが extends の規律（同じ構造が 2 度載らない）。NatCast での本格的なダイヤモンド事件は Ch11
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

## 3.4b 名前空間との最初の接触 = アクセス（namespace 縦糸 1/3）

- ドット付きの名前（`Real.sup`・`Real.instLOF`・`AddCommGroup.add_neg`・`LinearOrderedField.le_trans`）は `名前空間.名前` という階層化された参照。`le_trans` は `LinearOrderedField` の中に整理されている——フルパスで名指せばどこからでも引ける
- **この段階はまだ「既にある名前空間を読む」だけ**。自分で作るのは Ch4（`namespace Range`）、`open` で接頭辞を省く旨味は Ch5——縦糸: **Ch3 アクセス → Ch4 作る → Ch5 開いて省く＋dot 記法**

## 3.5 根幹の 2 行・class は自動で見つかる（最小機構の実物）

- `#check Real.instLOF`・`inferInstance`・`a + b` が解決される——Ch2 の「class＝自動で見つかる構造」の実物
- check_failure（ANCHOR `check_failure`）: 今 ℝ には 0 のインスタンスしかない → `(1:Real)`・`(2:Real)` はまだ失敗する（1 は Ch6・2 以上は Ch8 の伏線）。`#check_failure` で伏線がビルドに固定される
- ⚠ 解決の深い機構・ダイヤモンド事件の**本格**（NatCast の排他分割）は Ch11（数の体系）。ここでは階層の菱形（§3.1）の合流を軽く観察するに留める

## 3.6 最初の実数証明: `<` の 3 兄弟（ANCHOR `three_brothers`）

- le_of_lt=射影・lt_of_le_of_ne=構成・ne_of_gt=¬は関数——Ch1 の論理が Real に着地する瞬間

## 演習

- 署名読解ドリル・`<` の 3 兄弟の変種・**sup 最小性実験**（sup 公理 3 行を消しても C05 までビルドが通ることを後で確認する予約）

## 引き

- 「実数は読めた。リーマン和には Σ が要る。有限和とは何か？」
