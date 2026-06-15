# 前半（序章〜Ch9）執筆ガイド＆レビュー基準

リーマン和を**定義し、基本性質を証明するまで**（序章〜Ch9）の本文執筆フェーズの単一参照。
設計書 `docs/textbook_plan.md` の散在する方針を前半に絞って統合し、レビューの照合基準を明文化する。
詳細の再導出はせず、必要に応じて設計書の該当節へポインタする。

> 関連: 構成 v3 = 本編 第 I 部 Ch0–10／第 II 部 Ch11–15（FTC は Ch15）／発展部 E1–E5／付録 C・D。
> 本ガイドは **Ch0–Ch9**（第 I 部から間奏 Ch10 を除いた「定義＋性質」の弧）を扱う。

---

## 1. 役割分担とワークフロー

- **ユーザー（執筆）**: `Text/book/src/chNN_*.md` の配置メモを土台に散文を展開する。
- **私（レビュー＆方針管理）**: 各章ドラフトを §4 の不変条件で照合し、次を指摘する——
  早すぎる機能初出／縦糸の張り忘れ・回収漏れ／引きの欠落／コード引用の誤り／監査主張の未検証。
- **今回スコープ外（P4 へ）**: 演習の sorry 化＋`Solutions` 分離・`#include` ANCHOR 配線・mdbook 導入・
  Ch10 間奏・第 II 部・発展部。

執筆の単位はコードではなく散文。コード（C01–C09）は完成・ビルド通過済みで、原稿はそれを ANCHOR 引用する。

---

## 2. 共通方針の要点

| 項目 | 要点 | 設計書の該当節 |
|---|---|---|
| 読者像・トーン | 数学既知（ε-δ・上限公理・リーマン積分）／Lean ゼロ。数学説明は最小、紙面は Lean 固有概念に集中 | 「2. 読者と方針」 |
| 2 幕構成 | 幕1 序章〜Ch5＝**定義の幕**（書く・証明技術ほぼ不要）／幕2 Ch6〜Ch9＝**証明の幕**（sorry を埋める）。「RS の記述に要る Lean 機能は 6 つ・入り込む証明は添字の Nat 不等式の項埋めのみ」が根拠 | 「第 I 部のストーリー」 |
| 3 到達点 | ① 定義が書ける（Ch5）② 具体例が計算できる（Ch8）③ 性質 5 本が証明できる（Ch9） | 同上 |
| 🪟 理論の窓 | 理論的深掘りは名前付きコラムに隔離。**飛ばしても本線（演習）が通る二重底**。前半の窓: BHK(Ch1)・公理と noncomputable(Ch2)・証明無関係性と Prop(Ch2)・自然演繹と recursor(Ch4)・カーネルと De Bruijn(Ch6)・正規化と #reduce(Ch7) | 「縦断スレッド」 |
| 引きの連鎖 | 各章は**前章末に残した問い**で開く。章末に次章への引きを置く（§3 の表に明記） | 「第 I 部のストーリー」 |
| 現在地マップ | 章末に import 図のうち「読めるようになったファイル」を塗りつぶす | 同上 |
| 執筆規約 | ①独立（MyProject を import しない）②コード引用は ANCHOR `{{#include}}`（手書きコピペ禁止）③`lake build Text` ④演習は本文中に sorry・模範解答は `namespace Solutions` | `Text/README.md`・「4.2/4.3」 |

---

## 3. 章別ブリーフ（序章〜Ch9）

各章: **開く問い** ／ **到達点** ／ **新機能（初出）** ／ **ANCHOR**（引用可能ブロック）／ **縦糸**（▲張る・▼回収）／ **演習候補** ／ **引き** ／ ⚠注意。
配置メモの詳細は各 `chNN_*.md` を、素材は設計書を参照（ここは統合と相互参照のみ・新情報は足さない）。

### 序章 — 挑戦状（`ch00_intro.md`、対応コードなし）
- 問い: あなたは ε-δ を知っている。では機械に説明できるか
- 到達点: 本書の約束（公理 5 本＋カーネルまで切り詰める）と読み方が伝わる
- 新機能: —（`main'` と `#print axioms` の出力 8 行を見せるのみ）
- ▲3 つの鍵を予告・▲監査文化を予告・▲第 I 部=構成的／第 II 部=古典的の予告
- 引き: Ch0 へ「まだ読めない main'。読めるようになるのが本書」
- ⚠ `main'` は MyProject 参照（可積分仮定版 FTC が本編到達点・連続版は参照実装、と注記）

### Ch0 — 環境構築（`ch00_setup.md`、対応コードなし）
- 問い: 序章の挑戦をどう始めるか
- 到達点: clone → 演習着手 10 分・3 道具を知る
- 新機能: `#check`／`#print`／`#print axioms`（監査文化の起点）
- ▲監査 3 道具（§4e の起点）
- 引き: Ch1 へ「ゴール表示の `⊢` とは何か」

### Ch1 — 最初の証明（`ch01_term.md`、C01）
- 問い: `⊢` とは何か
- 到達点: 命題論理の証明を**項**として手書きできる（Real 不要・タクティク不要）
- 新機能: 命題=型・証明=項（term mode）・`fun`・`⟨⟩`・射影
- ANCHOR: `my_first_theorem`・`and_swap`
- ▲CH 対応 6 表を提示・🪟BHK 解釈
- 演習候補: `and_assoc'`・`and_or_distrib`・`imp_trans`・`double_neg_intro`（C01 内に既存）
- 引き: Ch2 へ「実数とは何か。公理を読みに行こう」

### Ch2 — 実数を 5 本の公理で読む（`ch02_axioms.md`、C02）
- 問い: 実数とは何か
- 到達点: 「数学的構造はデータ」の見方を得て、C02 の階層・公理が**読める**・最初の実数証明
- 新機能: 署名の読み方・**依存型【鍵1】**・∀/∃=Π/Σ・**Prop vs Type・universe【鍵2】**・暗黙引数（**読む**）・`axiom`・namespace/open
- ANCHOR: `structure_as_data`・`hierarchy`・`axioms`・`zero_bridge`・`three_brothers`
- **開くビート「数学的構造をどう書くか」（2026-06-15 追加・階層を読む前の接着剤）**: 5 段の梯子——
  ① 型=集合(carrier)。Ch1 では型は命題、ここでは「住人を持つ集合」の顔
  ② 構造=データ: 演算と「それが法則を満たす証明」を 1 つの項に束ねたもの。**Ch1 の `⟨h.2, h.1⟩` ペアの大きい版**
  ③ `Add α`・`AddCommGroup α` は「α 上の構造の型」。`Add : Type → Type` は依存型【鍵1】の最初の顔
  ④ 同じ carrier に構造は複数載る（ANCHOR `structure_as_data`: `Add Nat` の住人を `⟨⟩` で 2 つ＝普通の加法と乗法。**Add は法則を持たない→乗法すら住人になれる→法則は AddCommGroup 以降が束ねる→だから階層がある**）
  ⑤ これを携えて C02 の `class … extends … where …` が「α 上の構造を束ねたレコードの宣言」として読める
- ▲依存型・universe を正面で・▼CH 表の ∀∃ 行を裏付け・🪟公理と noncomputable・🪟証明無関係性と Prop
- 演習候補: 署名読解ドリル・`<` の 3 兄弟の変種・**sup 最小性実験**（sup 3 行を消しても C05 までビルドが通る）
- 引き: Ch3 へ「`a + b` の `+` はどこから来た？」
- ⚠ **境界**: 概念（構造＝データ・複数載る）=Ch2／`class`・`instance` の**機構**（解決・ダイヤモンド）=Ch3（「この `class` の仕組みは Ch3 で」と送る）／`structure` キーワードと「And も構造」種明かし=Ch5。実演は `def` でなく `example`（`def … : クラス型` は reducible 警告が出る・`example` は警告ゼロで Ch3 既出）
- ⚠ **∃ vs データ（Q3=予告のみ）**: 「0・演算はデータとして束ねる（∃ 主張ではなく）。理由（choose が要り監査に choice 混入）は後で」を**予告 1 行**に留める。本格議論は sup 導入時／Ch3 の公理設計の論点
- ⚠ noncomputable の源泉①（公理に実行コードがない）をここで正直に説明。設計書「公理設計の論点」を素材に
- ⚠ **肥大注意**: 構造の見方ビート追加で Ch2 は重い。肥大時は 2 分割（構造の見方／公理を読む）を予約（Ch8 と同方針）

### Ch3 — + と 0 はどこから来るか（`ch03_class.md`、C03＝実演専用）
- 問い: `+` や `0` はどこから来たか
- 到達点: インスタンス解決が「見える」・`(2:Real)` がエラーになる理由が言える
- 新機能: class・instance・インスタンス解決（双子章・前編）
- ANCHOR: `check_failure`・`diamond`
- ▲菱形の**悪い例**（diamond トイデモ・§4d の起点）・▲`(2:Real)` エラー（Ch8 で回収）・▼CH 表の量化子（C02 を素材に再訪）
- 演習候補: 「0 を ∃ で置いたら何が壊れるか」議論（コードは Ch11 の choose 学習後に再訪）
- 引き: Ch4 へ「リーマン和には Σ が要る。有限和とは何か？」
- ⚠ C03 は「0 だけの世界」（リテラル 1・2 がまだ無い）でこそ `#check_failure` が成立。import 連鎖の葉

### Ch4 — 有限和（`ch04_inductive.md`、C04）
- 問い: 有限和とは何か
- 到達点: Range/Summation が読めて書ける・CH 対応表が完結する
- 新機能: **帰納型【鍵3】**・Subtype・構造的再帰・rfl=defeq の予告編・**Zero bridge**
- ANCHOR: `range`・`summation`・`summation_rfl`
- ▲帰納型を正面で・▼**CH 表のパンチライン**（`#print Or` 等で「論理は依存関数＋帰納型」）・🪟recursor（`#print And.rec`）・▲Zero bridge＝菱形の**良い配線**（Ch3 の対）・🪟「なぜ List でないのか」
- 演習候補: 型シグネチャ設計（`[Add][Zero]` は最小契約か・自作 Zero／Real 特化との書き比べ）・`n` を implicit にできるか・小さい n で Summation 手計算
- 引き: Ch5 へ「分割をデータとしてどう表す？」
- ⚠ Summation は `[Add α][Zero α]`・n は explicit（2026-06-12 決定）。Finset.sum が AddCommMonoid を要る理由（商と well-defined）はコラム

### Ch5 — 分割とリーマン和の定義（`ch05_structure.md`、C05・到達点①）
- 問い: 分割をどう表すか
- 到達点: **リーマン和の定義が書ける**（到達点①）・ただし sorry が 1 つ残って幕
- 新機能: structure（双子章・後編）・notation 自作・暗黙引数（**書く**: `length {n}{a b}`）
- ANCHOR: `partition`・`riemann_sum`・`trivial_partition`
- ▼`And` も structure だった（`#print And`・Ch1 の `⟨⟩` 回収）・▲notation 初登場（自動化糸の起点）・▲trivialPartition の sorry クリフハンガー（Ch8 で回収）
- 演習候補: 反転演習（Partition を class にすると IsIntegral が書けない／LOF を structure にすると `a+b` のたびに名指し）
- 引き: Ch6 へ「定義はできた。sorry を埋める道具が要る」
- ⚠ TaggedPartition・IsRepr はまだ出さない（Ch12・Ch9）。RS の定義 1 行に前章までの全部が映る、を体感させる

### Ch6 — sorry を埋める道具 I（`ch06_tactic.md`、C06）
- 問い: 残った sorry をどう埋めるか
- 到達点: 基本タクティクで短い証明・「なぜタクティクで証明になるか」に答えられる
- 新機能: `by`・ゴール状態・intro/exact/apply/rw/have/show・term↔tactic の往復
- ANCHOR: （未付与——特定の補題証明を引用する段で付ける。§5 参照）
- ▲種明かしの糸の起点（カーネル/De Bruijn・タクティクは項を書く機械）・▼apply=メタ変数＋単一化（`_`も暗黙引数も同じ穴・Ch2/3 と接続）・🪟カーネルと De Bruijn 基準
- 演習候補: C06 の基礎補題ドリル（add_neg'・zero_add'・neg_neg 等を自分で）
- 引き: Ch7 へ「rw が効くとき効かないとき。等しさは 2 種類？」

### Ch7 — sorry を埋める道具 II（`ch07_defeq.md`、C07）
- 問い: 等しさには 2 種類あるのか
- 到達点: calc が設計できる・帰納法で Σ 補題コーパスが証明できる
- 新機能: defeq と rw の構文性・rfl/show・calc・Trans・induction・omega・**One bridge**
- ANCHOR: `vector_space`・`summation_linear`（脇道）
- ▼rw=Eq.mpr＋motive（種明かし）・▼induction=recursor 適用（Ch4 回収）・▲One bridge（菱形）・**rw の罠 2 種**（引数明示・独立補題への切り出し）・🪟正規化と #reduce
- 演習候補: コーパス 9 本の sorry 埋め・脇道「Σ は線形形式」（VectorSpace 自作・関数空間インスタンス・summation_isLinear＝corpus 2 本のペア）
- 引き: Ch8 へ「Ch5 の sorry を消しに行こう→2 等分・n 等分」
- ⚠ telescope_sum がボス戦（最初の本格帰納法・Ch9 length_sum と Ch14 中点和の部品）

### Ch8 — 具体例 y=x の n 等分（`ch08_example.md`、C08・到達点②）
- 問い: sorry を消し、具体例を計算する
- 到達点: equalPartition 上の RS=(n+1)/(2n)（到達点②）
- 新機能: OfNat 物語の回収・`Real.ofNat`（構造的再帰）・NatCast・Div・cast 補題
- ANCHOR: `of_nat`・`equal_partition`・`sum_id`・`cast_defeq`
- ▼`(2:Real)` エラー回収（Ch3）・▼trivialPartition の sorry 消える（Ch5）・▲菱形の排他分割（0/1/2 以上＝AtLeastTwo 手作り）・**defeq 観察**（`ofNat 1 = 0+1` は rfl・`= 1` は `#check_failure`）
- 演習候補: 分点が i/n の確認（show）・`sum_id`（`(1+1)·Σi = n(n−1)`）・cast 一括ルートを試して壊す
- 引き: Ch9 へ「一般の分割で何が言える？性質を証明しよう」
- ⚠ cast 補題は**構成的な部分のみ**（archimedean 系の sup 利用は Ch11 へ送る＝公理の節約を設計として見せる）。肥大時は 2 章分割を予約

### Ch9 — リーマン和の性質 5 本（`ch09_properties.md`、C09・到達点③）
- 問い: 一般の分割で何が言えるか
- 到達点: 後段が消費する性質 5 本（到達点③）・第 I 部古典ゼロの監査
- 新機能: なし（総合演習）——ただし**述語の設計（IsRepr）**が初登場
- ANCHOR: `is_repr`（性質 5 本は未付与・§5 参照）
- ▲両側評価（脱 abs・理由は Ch11 予告）・▲IsRepr（反例が要求）・▼第 I 部古典ゼロの総決算（監査の段階の山）
- 演習候補: additive/neg/const（望遠鏡和）/nonneg（反例から IsRepr）/両側 rs_bound・章末 `#print axioms`
- 引き: Ch10 へ「同じパターンを繰り返した。手を自動化しよう（間奏へ）」
- ⚠ 性質 5 本は**生の不等式 2 本**で書く（NearLe 述語への昇格は発展部）。「同じ形が 3 回出たら昇格」の方針を一言

---

## 4. 横断不変条件チェックリスト（レビューの照合基準）

各章ドラフトを以下で照合する。違反は「方針管理」上の指摘事項。

- **(a) 機能初出の単調性**: §3 の「新機能」に挙がるのは**前章までに登場していない**機能だけ。既出機能を「新規」として説明していないか。簡単→難しいの順が崩れていないか（例: tactic mode は Ch6 まで出さない）。**この不変条件は Lean の*キーワード/機構*が基準**——「数学的構造をデータとみなす視点」（Ch2）のような*概念*は keyword ではないので、`structure`/`class`/`instance` の機構を Ch5/Ch3 に残したまま Ch2 で導入してよい
- **(b) CH 対応 6 表**: Ch1 で提示 → Ch2 で ∀∃=Π/Σ を裏付け → Ch4 で `#print` により完結（∧∨∃=も帰納型）。表の各行が「いつ裏付くか」と整合しているか
- **(c) 種明かしの糸**: Ch6 カーネル/De Bruijn・apply=メタ変数 → Ch7 rw=Eq.mpr・induction=recursor（Ch4 の recursor を回収）・omega 予告。「使う→仕組みを覗く」の順序が保たれているか
- **(d) 菱形の糸**: Ch3 悪い菱形（diamond）→ Ch4 Zero bridge・Ch6 One bridge（良い配線）→ Ch8 排他分割（AtLeastTwo）。良い／悪いの対比が崩れていないか
- **(e) 監査の段階**: Ch0 で 3 道具導入 → 各章末で `#print axioms` → Ch9 で「第 I 部は古典公理ゼロ」を総決算。不変条件は **`Classical.choice` と `Real.sup` 系が前半の監査に出ないこと**（出たら設計違反）。`propext`・`Quot.sound` は標準の無害公理で、`rs_le_const` 等に現れてよい（説明は最小限に留め Ch15 へ送る）。「古典公理ゼロ」＝ choice ゼロの意味だと本文で明確化する
- **(f) 脱 abs/min/diam 方針**: 前半に abs・max・min・diam を持ち込まない。Ch9 の第 5 性質は両側評価（生の不等式 2 本）。理由（abs は古典性を呼ぶ）は Ch11 へ予告のみ
- **(g) コード引用の正確性**: ANCHOR が実在するか（§5 の未付与リストに注意）。defeq・監査の主張が**実ビルドと一致**するか（`cast_defeq` の `#check_failure`、章末 `#print axioms` の値など、机上で書かず実行値を貼る）
- **(h) 3 つの鍵の言及**: 依存型(Ch2)・universe(Ch2)・帰納型(Ch4)が正面で扱われ、他章の解説でも意識的に言及されているか

---

## 5. 前半スキャフォールドの既知 TODO（執筆中に発生する配線作業）

本文に集中するパスのため以下は未整備。**引用が必要になった段で**対応（多くは P4）。

- **C02_Axioms**: `structure_as_data` 実演を追加済（2026-06-15・`example` で `Add Nat` の住人 2 つ・警告ゼロ）
- **C06_Tactics**: ANCHOR 未付与（タクティク corpus）。特定の補題証明を引用する段で `ANCHOR:` を付ける
- **C09_Properties**: 性質 5 本（riemann_sum_add/neg/const/nonneg・rs_le_const）の ANCHOR 未付与（`is_repr` のみ済）
- **序章/Ch0**: 対応 C** ファイルなし。`main'` 引用は MyProject 参照・監査出力は**実行値**を貼る
- **演習の sorry 化＋Solutions 分離・`#include` 配線・mdbook 導入**: P4（今回はインライン引用で可・ANCHOR は維持し後で変換）
- **Ch10 間奏（C10）・付録 D（my_ring）**: 前半の範囲外
