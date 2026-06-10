# Lean 入門教材 設計書

— 公理 5 本から微積分学の基本定理へ、そして自動化の自作まで —

本書は Tsudoi6 リポジトリ（mathlib 非依存・公理的実数で微積分学の基本定理 FTC を sorry ゼロで完全証明、約 4300 行）を素材とする Lean 4 入門教材の設計書である。

## 1. コンセプトと差別化

**「`#print axioms` が示す 5 本の公理以外、何も信じない」**

- 実数の公理（線形順序体＋上限公理）だけから出発し、リーマン積分を構成して FTC を証明する一本道を、読者が演習で自ら登る。
- mathlib を使わない。`ring` / `linarith` / `simp` の強力版のような自動化もない。すべての補題が目の前で手作りされる——ブラックボックスゼロ。
- その上で第 III 部において、**第 I・II 部で手作業だった証明の自動化（`my_ring` 等）を読者自身が作る**。「道具を使う」のではなく「道具を使い、最後にその道具を自作する」構成は既存教材（TPiL4 / MIL）にない本書独自の弧である。
- 数学の説明は最小限（読者は数学既知）。紙面は Lean 固有の概念に集中する。
- **縦糸は Lean の 3 つの鍵 — universe・依存型・帰納型。** 序章で予告し、依存型は Ch3（∀=Π としての量化子・署名読解）、universe は Ch3（Prop vs Type と Sort 階層 — 本書の全コードが Type 0 と Prop で完結することを universe 理解の教材として使う）、帰納型は Ch6（And/Or/Exists/Eq も Nat も帰納型という「正体」）で正面から扱い、Ch15（多項式 AST）で帰納型の応用として回収する。

## 2. 読者と方針（確定事項）

| 項目 | 決定 |
|---|---|
| 想定読者 | 数学の院生・研究者。ε-δ・上限公理・リーマン積分は既知。Lean 経験ゼロ。プログラミング経験は不問 |
| 形式 | Web 本（Markdown、公開先は後決め）＋同一リポジトリの演習コード |
| 学習スタイル | **演習駆動**（sorry 穴埋めが主、Mathematics in Lean 方式） |
| 範囲 | 背骨を厳選（重い証明 Refine / Oscillation / IntervalAdd / 一様連続は付録の読み物） |
| 本体コード | 教材都合の変更 OK（ただし公理 5 本・sorry ゼロ・FTC 主定理は不変） |
| toolchain | 執筆前に最新安定版へ更新（現: v4.12.0-rc1） |
| 旧資産 | Sample/・Demo/・talk/ 等は現状維持（演習は新規作成、アイデアのみ参考） |
| 強調する柱 | **Lean の 3 つの鍵: universe・依存型・帰納型**（Ch3・Ch6 で正面から扱い、全章の解説で意識的に言及する） |
| 扱わないもの | Monad/IO・universe 多相の実践（本書のコードは Type 0 と Prop で完結 — その事実自体を Ch3 の universe 解説の素材にする）。メタプログラミングは第 III 部で必要な範囲のみ |

## 3. 章立て

**設計原則: 1 章 = 1 つの Lean 機能。**機械の軸が主、数学の進行は素材。**Lean 学習の順序を優先し、数学的順序は従とする。** 第 I 部はリーマン和の定義と性質を到達点とし、第 II 部で積分を定義してその存在（連続⇒可積分）に登り、第 III 部で自動化を自作する。

### 数学的背骨（全体の物語）

```
1. リーマン和の定義            （定義のみ・証明技術ゼロで書ける）
2. リーマン和の性質 5 本        （帰納法・代数補題・IsRepr がここで動機付きで入る）
3. 積分の定義 ＝ 網目の極限     （ε-δ ネスト・choose・一意性）
4. 積分の性質                  （2 の各性質の ε/2 持ち上げ）
5. 連続 ⇒ 可積分              （山頂）
6. FTC
```

- 段 2 の「リーマン和の性質」は後段で実際に使う 5 本に厳選する: `additive_riemann_sum` / `neg_riemann_sum` / `const_riemann_sum`（望遠鏡和 `length_sum` が最初の本格的帰納法）/ `RiemannSum_nonneg`（**ここで IsRepr / InInterval が「タグが区間内になければ非負にならない」という反例込みの動機で初登場**）/ `rs_abs_bound`。点挿入系（rs_insert_bound 等）は存在定理の機械なので付録 B。
- 段 3 では読者が 3 種類の ε-δ（`IsLimAt`＝点列なし関数極限・`Continuous`・`IsIntegral`＝分割の網目に関するネット収束）を比較できる。「ε-δ という同じ形の異なる実例」を Lean の型の違いとして見せる。
- 段 4 は段 2 との対応表が章の構造になる:

| リーマン和の性質 | （持ち上げ） | 積分の性質 |
|---|---|---|
| additive_riemann_sum | ε/2 論法 | isintegral_add |
| const_riemann_sum | δ 任意 | const_has_integral |
| RiemannSum_nonneg | 矛盾論法 | integral_nonneg |
| rs_abs_bound | sup 構成の有界性 | integrable_of_cauchy 内部 |

- 段 5「連続⇒可積分」は難易度の異なる 4 部品に分解して扱いを変える:
  (i) 一様連続性 `continuous_unif_cont`（sup による区間帰納、308 行）= **statement 精読＋付録 A**
  (ii) コーシー型判定 `integrable_of_cauchy`（sup で積分値を構成する 55 行）= **本文精読＋誘導演習**
  (iii) 細分比較 `rs_compare`（多点挿入・階段原始関数、269 行）= **statement 精読＋付録 B**
  (iv) 組み立て `continuous_integrable`（41 行）= **本文完全精読**
  「補題を 2 本引用すれば主定理の証明は明快」という論文読解と同型の経験をさせる。`#print axioms` が sorry の混入を許さないので、引用した補題も証明済みであることが保証されている。

### 第 I 部 リーマン和への道（Ch1–8、1 章 1 概念）

| 章 | 主役の Lean 機能 | 数学素材（演習対象） |
|---|---|---|
| Ch0 | 環境構築・lake・`#check` / `#print` / `#print axioms` | リポジトリの歩き方 |
| Ch1 | **term mode の証明**: 命題=型・証明=項、`fun`、適用、`⟨⟩`、`Eq.refl` / `Eq.trans` / `congrArg` | Nat 等式・命題論理（新規演習 C01）＋実コードの `le_of_lt` / `lt_of_le_of_ne` / `ne_of_gt`（`<` が `≤ ∧ ≠` のペアである体系を活かす） |
| Ch2 | **tactic mode の証明**: ゴール状態、intro / exact / apply / rw / calc / have / show、`by`、term↔tactic の相互変換 | Ch1 と同素材の再訪＋∀ε>0∃δ>0 型トイ命題（新規演習 C02） |
| Ch3 | **依存型・量化子・universe**【鍵 1・2】: `∀`=Π、`∃`、`{}` / `[]` / `()` と暗黙引数、カリー化、署名の読み方、namespace / section / open、**Prop vs Type と Sort 階層** | Axioms.lean の公理 5 本の型を精読（`Real.sup` の「証明を引数に取り、型が項に依存する」署名が依存型の決定的標本） |
| Ch4 | **class と instance**（双子章・前編）: 代数階層、`extends`、インスタンス解決、`OfNat` と数値リテラル、`axiom`＋`instance` による実数導入。structure との比較表の **class 側の列だけ**ここで埋める | Real/Algebra.lean の補題演習。コラム: NatCast 二重インスタンス事件（ダイヤモンド） |
| Ch5 | **defeq と rw の構文性**: `rfl` の意味（`a + -b = a - b := rfl`）、`show` 正規化、rw が失敗するとき、calc の設計 | Real/Order・Div・Abs（half_add / abs_triangle / abs_le 等）。「なぜこの show 行があるか」型読解問題 |
| Ch6 | **帰納型と再帰**【鍵 3】: `inductive` の一般論（And / Or / Exists / Eq も Nat も帰納型 — Ch1–2 の道具の正体）、`Subtype`（`Range n`）、構造的再帰（`Summation`）、`induction`、`omega`、`@[simp]` | Real/Summation（additive_summation / telescope_sum 等）＋ cast_nonneg / cast_lt |
| Ch7 | **structure**（双子章・後編）: フィールド・射影・匿名コンストラクタ・intro-pattern 分解、証明を運ぶレコード（`increase`）。Ch4 の比較表の structure 側を埋めて完成させ、「Partition を class にしてみよ」演習で差を確定 | `Partition`、equalPartition 構成演習（フィールド穴埋め）。種明かし: Ch1 の `⟨h, hne⟩`（And）も structure だった |
| Ch8 | **第 I 部の到達点: リーマン和の定義と性質**（総合章: 暗黙引数を持つ定義の設計と、自分の定義への API 構築） | `RiemannSum` の定義＋性質 5 本（additive / neg / const / nonneg / abs_bound）。IsRepr / InInterval が動機付きで初登場 |

順序の設計判断: ① 量化子は ∀=Π の必然から依存型と同じ Ch3 に置く（TPiL4 の「Quantifiers and Equality」相当）。② class（Ch4）が structure（Ch7）より先なのは TPiL4 と逆だが、Ch3 で Axioms.lean を精読する以上 class の説明を遅らせるとブラックボックスが生じ本書の理念に反する。前方参照＋Ch7 での回収で処理。③ **古典論理と choice は第 I 部に置かない**: リーマン和とその性質までは構成的に進められる（choice が要るのは積分の定義の `Classical.choose` と分割の存在定理から）。必要になる直前＝第 II 部冒頭に置く。

### structure と class の扱い（双子章方式）

両者は機械的にはほぼ同一（class = structure ＋ `@[class]`、instance = def ＋ `@[instance]`）なので、**「2 つの別概念」ではなく「1 つの仕組み＋値の渡し方の自動化」として正直に教える**。説明は 3 段:

1. **機械的な真実**: フィールド・射影・`⟨⟩`・`extends` はすべて共通。違いは `(Δ : Partition n a b)`（明示引数・名指しで渡す）か `[LinearOrderedField Real]`（インスタンス引数・機構が探して渡す）かだけ。
2. **設計判断の基準**: その添字（型）に対して値が**正準に 1 つ**なら class（「ℝ と言えば足し算は決まっている」という暗黙の了解の機械化）、**多数あって量化・構成・受け渡しの対象**なら structure（「[a,b] の分割全体を走る」の機械化）。読者用リトマス試験:

| 問い | structure なら | class なら |
|---|---|---|
| `∀ x, …` と量化したいか | する（`∀ P : TaggedPartition a b, …`） | しない |
| 使用時に名前を呼ぶか | 呼ぶ（`Δ.points`） | 現れない（`a + b`） |
| 2 つ目の値が存在したら | 当たり前（分割は無数） | 事故（NatCast ダイヤモンド事件） |

3. **反転演習で確定させる**: 「`Partition` を class にしてみよ」→ 分割を任意に走る ∀ が書けず **`IsIntegral` が定義不能になる**（積分の定義そのものが Partition = structure の理由）。逆に「`LinearOrderedField` を structure にしてみよ」→ 全補題が構造を引数に取り、`a + b` のたびに「どの + か」を指定する羽目になる。どちらも壊れたコードを数行見せ、エラーを読む演習にする。

章割り上は Ch4（class 側）と Ch7（structure 側）の**双子章**とし、同じ比較表を 2 章かけて完成させる。Ch7 で「Ch1 から使っていた `And` も structure だった」（`#print And`）の種明かしを行い、Ch6 の帰納型と合わせて 3 章にまたがる伏線を回収する。

### 第 I 部のストーリー（リーマン和への道）

**設計の仕掛け**: ① 各章は「前章の最後に残った問い」で開く**連鎖構造**。② 章末に import 図のうち「読めるようになったファイル」を塗りつぶす**現在地マップ**（進捗を領土として見せる）。③ 第 I 部は **2 本の糸**でできていることを各章冒頭で明示する — *定義の糸*（リーマン和を**書く**ために必要: Ch1→3→4→6→7→8 前半）と*証明の糸*（性質を**示す**ために必要: Ch2→5→6 の帰納法→8 後半）。

リーマン和の**記述**に必要なのは正確に 6 つ（`def`/`fun`・型の言語と暗黙引数・class が効いているという理解・帰納型と構造的再帰・Subtype・structure 宣言の読解）であり、記述に入り込む証明は「添字が範囲内にある」という Nat 不等式の項埋め（`⟨k.val, Nat.lt_trans …⟩`）のみ。この事実を第 I 部の設計根拠として序文で示す。

各章のビート:

- **序章（挑戦状）**: 「あなたは ε-δ を知っている。では機械に説明できるか」。`main'` の statement と `#print axioms main` の 8 行だけ見せ、3 つの鍵を予告。第 I 部の約束は控えめに「リーマン和を自分の手で定義するところまで」。
- **Ch0**: 本文の半分はリポジトリそのもの。`main'` にカーソルを置きゴール表示を体験して閉じる——まだ読めない。読めるようになるのがこの本。
- **Ch1**: `1 = 1` から「証明は項」。実コード初日: `<` が `≤ ∧ ≠` である体系を活かし `le_of_lt`（射影）/ `lt_of_le_of_ne`（構成）/ `ne_of_gt`（¬は関数）。引き:「項の手書きはすぐ破綻する」
- **Ch2**: `by` とゴール状態。Ch1 と同じ定理を tactic で再証明、`exact` が両世界の橋。引き:「署名の `{}` や `[]` は何だ？」
- **Ch3**: 署名が読めれば半分わかる。クライマックスは公理 5 本の精読 — `Real.sup` の「証明を引数に取り、型が項に依存する」署名。Prop vs Type から Sort 階層へ。引き:「`+` や `0` はどこから来た？」
- **Ch4**: 根幹の 2 行 `axiom Real.instLOF` ＋ `instance`。リテラル `(2 : Real)` の正体。双子章前編＋ダイヤモンド事件コラム。引き: 章末演習で読者は初めて rw の失敗に遭遇する（仕組まれた挫折）。
- **Ch5**: 等しさには 2 種類ある。`a + -b = a - b := rfl` が通るのに rw は区別する。show・calc 設計。「なぜこの show 行があるか」読解問題。引き:「Σ とは何か？」
- **Ch6**: `#print Or` で種明かし — Ch1 から使ってきた ∧∨∃= も Nat もすべて帰納型。その目で `Range`（証明を抱えた添字）と `Summation`（構造的再帰）を読み、初の帰納法証明へ。引き:「分割をデータとしてどう表す？」
- **Ch7**: 証明を運ぶレコード `Partition`。双子章後編（比較表完成＋反転演習）。equalPartition フィールド穴埋め。引き:「役者が揃った」
- **Ch8**: リーマン和の定義は 1 行 — この 1 行に第 I 部の全章が映っている。後半は性質 5 本の総合演習: 望遠鏡和 `Σ length = b − a` の快感、`RiemannSum_nonneg` の反例から IsRepr が必然として登場。幕引き:「この和はどこへ向かうのか。それに答えるには値をひとつ選び取る力が要る（第 II 部、choice と極限へ）」

### 第 II 部 積分 — 定義・性質・存在（Ch9–13）

| 章 | 主役テーマ | 数学素材 |
|---|---|---|
| Ch9 | **古典論理と choice**: `Classical.em` / `by_cases` / `absurd`、`choose` / `choose_spec`、`noncomputable`（構成的だった第 I 部との対比で導入） | `min`（Nat の最小値）・ceil・sup_near・**archimedean**（上限公理→定理、白眉その 1）・exists_fine_partition |
| Ch10 | **積分の定義**: 3 種の ε-δ 比較（IsLimAt / Continuous / IsIntegral）、`TaggedPartition` への束ね直し、`dite`＋`Classical.choose` による定義、well-definedness | `IsIntegral`・`IsIntegrable`・`Integral`・`integral_unique`・`isintegral_self` / `integral_of_not_le`（junk 値の設計判断はコードコメントに経緯ごと残っている） |
| Ch11 | **積分の性質 ＝ リーマン和の性質の ε/2 持ち上げ**（対応表が章の構造。`min δf δg` パターンの定石化） | const_has_integral・**isintegral_add**（ε/2 論法の最純形）・isintegral_neg・integral_nonneg・integral_monotone |
| Ch12 | **山頂: 連続 ⇒ 可積分**（4 部品分解。大規模証明のアーキテクチャ: private・section・分割統治・import DAG） | (ii) integrable_of_cauchy 精読＋ sup 構成 4 ブロック誘導演習、(iv) continuous_integrable 完全精読、(i)(iii) は statement 精読＋付録参照 |
| Ch13 | **FTC**: statement 中の `let`、`#print axioms` 監査の意味。コラム: `propext` / `Quot.sound` / `Classical.choice` とは何か | OIntegral（向き付き積分）・**main'**（calc 骨格演習）・main |

### 第 III 部 自動化を自作する（Ch14–15）— 本書の弧の回収

| 章 | 主役の Lean 機能 | 内容 |
|---|---|---|
| Ch14 | **notation とタクティクの合成**: `notation` / `macro` / `macro_rules`、simp セット設計、`ac_rfl` を支える `Std.Associative` インスタンスの仕組み | `∫ x in a..b, f` 記法の自作（本体に積分記法が無いことを逆手に取る）＋頻出パターンを `real_simp` / `triangle` 等の自作タクティクに固める演習 |
| Ch15 | **proof by reflection で my_ring を作る**（白眉その 2）: 多項式 AST（帰納型【鍵 3】の応用回収）→ 正規化関数 → 健全性定理 → `rfl` / `decide`。ゴールの reify（`elab`）は最小限 | 自作 `my_ring` で第 I 部の手書き calc を 1 行に置換。linarith は読み物。mathlib の `ring` / `linarith` への接続 |

第 III 部の素材コード `MyProject/Tactic/`（Ch14: 記法と合成タクティク、Ch15: `MyRing.lean` = AST / norm / soundness ＋ reifier）は新規開発が必要（P4 の章執筆ループ内。本体ビルドに含めるが背骨の import 鎖には不干渉）。

**my_ring 設計方針**: 可換環の項を Nat 係数多項式の正規形（ソート済み単項式リスト）に正規化し、`DecidableEq` で正規形を比較。健全性 `eval ρ e = eval ρ (norm e)` を帰納法で証明し、タクティクは「reify → 健全性適用 → `decide` / `rfl`」。

### 付録

- 付録 A: 一様連続性を読む（UniformContinuity — Ch12 部品 (i) の全証明）
- 付録 B: 細分・振動和・区間加法性（Insert / Refine / Oscillation / IntervalAdd — Ch12 部品 (iii) ほか）
- 付録 C: mathlib への橋（本書の各概念の mathlib 対応表。MIL を次の一冊として推薦）

## 4. 演習機構の設計

### 4.1 配置

```
Exercises/
  C01_FirstProofs.lean      -- Ch1（本体に対応物なし）
  C02_TacticsLogic.lean     -- Ch2（同上）
  C03_Axioms.lean           -- 以降、本体ファイルのミラー
  ...
  C15_MyRing.lean
  Solutions/                -- C01/C02 等、本体に対応物がない問題の解答
Exercises.lean              -- umbrella
```

### 4.2 核心規則（名前衝突なし・本体＝模範解答）

**各演習ファイルは「ミラー対象の本体ファイルが import しているモジュールだけ」を import し、対象補題を同名・同文で再掲して証明を sorry 化する。**

- 名前衝突なし: 本体の同名定理は import されていないため再宣言エラーにならない
- カンニング不能: 解こうとしている補題そのものが環境に存在しない
- **本体ファイルがそのまま模範解答**: 解答提供コストゼロ・解答の陳腐化ゼロ。本文から「解答は `MyProject/Real/Order.lean`」とリンクするだけ

### 4.3 lakefile（sorry 警告の隔離）

```lean
-- @[default_target] は Calculus のまま変えない
lean_lib «Exercises» where
  globs := #[.andSubmodules `Exercises, .one `Exercises]
```

- 通常の `lake build` は従来どおり警告ゼロを維持。sorry 警告は `lake build Exercises` のときだけ
- 読者の検証: ① VS Code 上で sorry を埋めて波線が消えることを確認（主経路）② 章単位 `lake build Exercises.C04_OrderAbs` ③ 全完了後 `lake build Exercises` が警告ゼロなら修了

### 4.4 ドリフト検査

`scripts/check_exercises.py`（新設）: 演習ファイルの定理シグネチャ（`:=` / `:= by` 手前まで）を本体の同名宣言とトークン列比較し、「本体を変更したのに演習を直し忘れた」を CI で検出する。

## 5. book/ 原稿の規約

- **mdBook** 構成: `book/book.toml`＋`book/src/SUMMARY.md`＋章ごとの md
- **コード引用は手書きコピペ禁止**。本体・演習の .lean に ANCHOR コメントを入れ、`{{#include ../../MyProject/Integral/Def.lean:integral_unique}}` 方式で実ファイルから抜粋する。ビルド対象の実コードが唯一の出典となり、本体改修と原稿が自動同期する
- 各章冒頭に「より深く: TPiL ch.X / MIL ch.Y」参照ボックス

## 6. 作業フェーズと完了条件

| フェーズ | 内容 | 完了条件 |
|---|---|---|
| **P1 toolchain 更新** | `lean-toolchain` を最新安定版へ。先に Range.lean の無名 `WellFoundedRelation` インスタンスに明示名を付けてから更新（自動生成名 `Range.instWellFoundedRelation` への直接参照が壊れやすいため）。コア Nat 補題のリネーム等はエラー駆動で修正 | `lake build` 警告ゼロ・`#print axioms main` が公理 5 本＋標準 3 本のまま |
| **P2 教材向け本体改修** | ① Range.lean の `has_min` を技巧的な形から素直な `Nat.strongRecOn` 適用形へ書き直し（Ch6 の教材対象）② Integral/Def.lean の private キャスト系ヘルパー（my_cast_nonneg / cast_le_succ / nat_ne_zero_of_nonneg_lt / cast_pos_of_ne）を Real/Cast.lean へ公開移動（4.2 の規則の成立条件）③ Continuity.lean を 2 分割（Continuous 定義＋continuous_sub/const = Ch7 と、UniformContinuity.lean = 付録 A）④ 命名修正: `IsIntegral_iff` → `integral_eq_of_isIntegral`、Real/Algebra.lean のプライム混在エイリアス一本化 ⑤ 清掃: 未使用 typo クラス `CompletLinearOrderedField`、`#check` 残骸等 ⑥ 背骨の主要定義に doc comment | ビルド・公理監査グリーン |
| **P3 演習基盤＋book 骨格** | Exercises/ 雛形＋機構実証として C03・C04 を実作＋lakefile 追記＋`scripts/check_exercises.py`＋book/ 骨格（SUMMARY.md・ch00 ドラフト・各章スタブ）＋README を教材リポジトリとして更新 | `lake build` 警告ゼロ・`lake build Exercises` は sorry 警告のみ・ドリフト検査が機能 |
| **P4 章執筆ループ** | 章ごとに「演習作成 → 自力 1 周で難度調整 → 原稿 md 執筆（include 配線）→ ドリフト検査」。推奨順: Ch3→4→6→7→8（第 I 部の背骨確認）→9→10→11→1→2→5→12→13→14→15（`MyProject/Tactic/` 開発含む）→0→付録 | 各章: 演習が sorry 以外で警告ゼロ・原稿ビルド成功 |
| **P5 公開** | 公開先決定（Zenn / GitHub Pages）、deploy 整備、Ch0 に導線 | 公開 URL で全章閲覧可・clone から演習着手まで 10 分以内 |

## 7. 既存教材との関係・参考文献

- **Theorem Proving in Lean 4**（Avigad, de Moura, Kong, Ullrich）: 概念順（DTT → 命題と証明 → 量化子 → Tactics → … → 帰納型 → 構造体 → 型クラス → 公理と計算）は本書第 I 部とほぼ整合。差分は ① 型クラスの前倒し（Ch4、Axioms.lean 読解に必須）② TPiL ch6「Interacting with Lean」（namespace / section / open）は Ch3 に吸収 ③ conv は不使用のため扱わない。トピックの過不足はこの 3 点で説明できることを確認済み
- **Mathematics in Lean**（Avigad, Massot）: 演習方式（リポジトリ clone・本文中に随時 sorry・解答同梱）を採用。ただし MIL の ring / linarith 等の自動化は本書では不使用——「MIL が自動化に任せる部分を全て手で組み、最後にその自動化を自作する」が本書の差別化
- **The Mechanics of Proof**（Macbeth）: 制限タクティクセットで数学を教える方針が近い。序章の文献案内に含める
- **Metaprogramming in Lean 4**（Paulino 他）: 第 III 部の「より深く」の参照先
