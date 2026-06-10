# Lean 入門教材 設計書

— 公理 5 本から微積分学の基本定理へ、そして自動化の自作まで —

本書は Tsudoi6 リポジトリ（mathlib 非依存・公理的実数で微積分学の基本定理 FTC を sorry ゼロで完全証明、約 4300 行）を素材とする Lean 4 入門教材の設計書である。

## 1. コンセプトと差別化

**「`#print axioms` が示す 5 本の公理以外、何も信じない」**

- 実数の公理（線形順序体＋上限公理）だけから出発し、リーマン積分を構成して FTC を証明する一本道を、読者が演習で自ら登る。
- mathlib を使わない。`ring` / `linarith` / `simp` の強力版のような自動化もない。すべての補題が目の前で手作りされる——ブラックボックスゼロ。
- その上で第 III 部において、**第 I・II 部で手作業だった証明の自動化（`my_ring` 等）を読者自身が作る**。「道具を使う」のではなく「道具を使い、最後にその道具を自作する」構成は既存教材（TPiL4 / MIL）にない本書独自の弧である。
- 数学の説明は最小限（読者は数学既知）。紙面は Lean 固有の概念に集中する。

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
| 扱わないもの | universe・Monad/IO（全コードが Type 0 と Prop で完結することを序章で明言）。メタプログラミングは第 III 部で必要な範囲のみ |

## 3. 章立て

**設計原則: 1 章 = 1 つの Lean 機能。**機械の軸が主、数学の進行は素材。第 I 部で Lean 機能を一つずつ習得し、第 II 部は統合応用として FTC に登り、第 III 部で自動化を自作する。数学の進行は本体の import 鎖（公理 → 実数補題 → 有限和 → 分割 → 積分 → FTC）と完全に整合する。

### 第 I 部 Lean の機能（Ch1–8、1 章 1 概念）

| 章 | 主役の Lean 機能 | 数学素材（演習対象） |
|---|---|---|
| Ch0 | 環境構築・lake・`#check` / `#print` / `#print axioms` | リポジトリの歩き方 |
| Ch1 | **term mode の証明**: 命題=型・証明=項、`fun`、適用、`⟨⟩`、`Eq.refl` / `Eq.trans` / `congrArg` | Nat 等式・命題論理（新規演習 C01） |
| Ch2 | **tactic mode の証明**: ゴール状態、intro / exact / apply / rw / calc / have / show、`by`、term↔tactic の相互変換 | 量化子・∀ε>0∃δ>0 型トイ命題（新規演習 C02） |
| Ch3 | **依存型と暗黙引数**: `∀`=Π、`{}` / `[]` / `()`、カリー化、署名の読み方 | Axioms.lean の公理 5 本の型を精読 |
| Ch4 | **class と instance**: 代数階層の設計、`extends`、インスタンス解決、`OfNat` と数値リテラル、`axiom`＋`instance` による実数導入 | Real/Algebra.lean の補題（add_left_cancel' / neg_neg / telescope_2 等） |
| Ch5 | **defeq と rw の構文性**: `rfl` の意味、`show` 正規化、rw が失敗するとき、calc の設計 | Real/Order・Div・Abs（half_add / abs_triangle / abs_le 等） |
| Ch6 | **古典論理と choice**: `Classical.em` / `by_cases` / `absurd`、`choose` / `choose_spec`、`noncomputable` | sup_near・**archimedean**（上限公理→定理、白眉その 1）・ceil |
| Ch7 | **Subtype・再帰・帰納法**: `Range n`、構造的再帰（Summation）、`induction`、`omega`、`@[simp]` | Real/Summation（additive_summation / telescope_sum 等） |
| Ch8 | **structure**: フィールド・射影・匿名コンストラクタ・intro-pattern 分解 | Partition / TaggedPartition、equalPartition 構成演習 |

### 第 II 部 統合応用 — FTC へ（Ch9–12、新概念は最小限）

| 章 | 統合テーマ（復習される Lean 機能） | 数学素材 |
|---|---|---|
| Ch9 | choose で定義を作る（`dite` / `dif_pos`、定義の well-definedness） | RiemannSum・IsIntegral・Integral・integral_unique |
| Ch10 | ε/2 論法の定石化（部品合成・`min δf δg` パターン） | 定数関数の積分・isintegral_add / neg・単調性 |
| Ch11 | 大規模証明のアーキテクチャ（private・section・分割統治、誘導演習＋読解） | integrable_bounded・integrable_of_cauchy・連続⇒可積分 |
| Ch12 | 総仕上げ（statement 中の `let`、`#print axioms` 監査の意味） | OIntegral・**main'**（calc 骨格演習）・main |

### 第 III 部 自動化を自作する（Ch13–14）— 本書の弧の回収

| 章 | 主役の Lean 機能 | 内容 |
|---|---|---|
| Ch13 | **タクティクの合成**: `macro` / `macro_rules`、simp セット設計（`@[simp]` 属性の戦略、`simp only` カスタムセット）、`ac_rfl` を支える `Std.Associative` インスタンスの仕組み | 第 I・II 部で繰り返したパターン（三角不等式分解・min 分配・移項）を `real_simp` / `triangle` 等の自作タクティクに固める演習 |
| Ch14 | **proof by reflection で my_ring を作る**（白眉その 2）: 多項式 AST（帰納型の本格応用）→ 正規化関数 → 健全性定理 → `rfl` / `decide` による証明。ゴールの reify（`elab` による Expr 操作）は最小限の解説 | 自作 `my_ring` で第 I 部の手書き calc 証明を 1 行に置換してみせる。linarith は仕組みの読み物。mathlib の `ring` / `linarith` の実装思想への接続 |

第 III 部の素材コード `MyProject/Tactic/`（Ch13: 合成タクティク群、Ch14: `MyRing.lean` = AST / norm / soundness ＋ reifier）は新規開発が必要（P4 の章執筆ループ内。本体ビルドに含めるが背骨の import 鎖には不干渉）。

**my_ring 設計方針**: 可換環の項を Nat 係数多項式の正規形（ソート済み単項式リスト）に正規化し、`DecidableEq` で正規形を比較。健全性 `eval ρ e = eval ρ (norm e)` を帰納法で証明し、タクティクは「reify → 健全性適用 → `decide` / `rfl`」。

### 付録

- 付録 A: 一様連続性を読む（UniformContinuity）
- 付録 B: 細分・振動和・区間加法性（Insert / Refine / Oscillation / IntervalAdd）
- 付録 C: mathlib への橋（本書の各概念の mathlib 対応表。MIL を次の一冊として推薦）

## 4. 演習機構の設計

### 4.1 配置

```
Exercises/
  C01_FirstProofs.lean      -- Ch1（本体に対応物なし）
  C02_TacticsLogic.lean     -- Ch2（同上）
  C03_Axioms.lean           -- 以降、本体ファイルのミラー
  ...
  C14_MyRing.lean
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
| **P4 章執筆ループ** | 章ごとに「演習作成 → 自力 1 周で難度調整 → 原稿 md 執筆（include 配線）→ ドリフト検査」。推奨順: Ch3→4→8→9→10→1→2→5→6→7→11→12→13→14（`MyProject/Tactic/` 開発含む）→0→付録 | 各章: 演習が sorry 以外で警告ゼロ・原稿ビルド成功 |
| **P5 公開** | 公開先決定（Zenn / GitHub Pages）、deploy 整備、Ch0 に導線 | 公開 URL で全章閲覧可・clone から演習着手まで 10 分以内 |

## 7. 既存教材との関係・参考文献

- **Theorem Proving in Lean 4**（Avigad, de Moura, Kong, Ullrich）: 概念順（DTT → 命題と証明 → 量化子 → Tactics → … → 帰納型 → 構造体 → 型クラス → 公理と計算）は本書第 I 部とほぼ整合。型クラスのみ意図的に前倒し（Ch4、Axioms.lean 読解に必須）。conv は不使用のため扱わない
- **Mathematics in Lean**（Avigad, Massot）: 演習方式（リポジトリ clone・本文中に随時 sorry・解答同梱）を採用。ただし MIL の ring / linarith 等の自動化は本書では不使用——「MIL が自動化に任せる部分を全て手で組み、最後にその自動化を自作する」が本書の差別化
- **The Mechanics of Proof**（Macbeth）: 制限タクティクセットで数学を教える方針が近い。序章の文献案内に含める
- **Metaprogramming in Lean 4**（Paulino 他）: 第 III 部の「より深く」の参照先
