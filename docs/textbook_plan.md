# Lean 入門教材 設計書

— 公理 5 本から微積分学の基本定理へ、そして自動化の自作まで —

本書は Tsudoi6 リポジトリ（mathlib 非依存・公理的実数で微積分学の基本定理 FTC を sorry ゼロで完全証明、約 4300 行）を素材とする Lean 4 入門教材の設計書である。

## 1. コンセプトと差別化

**「`#print axioms` が示す 5 本の公理以外、何も信じない」**

- 実数の公理（線形順序体＋上限公理）だけから出発し、リーマン積分を構成して FTC を証明する一本道を、読者が演習で自ら登る。
- mathlib を使わない。`ring` / `linarith` / `simp` の強力版のような自動化もない。すべての補題が目の前で手作りされる——ブラックボックスゼロ。
- その上で**手作業だった証明の自動化を読者自身が作り、以後の章で使う**（Ch5 の記法自作 → Ch10 間奏のタクティク合成 → Ch11 発展の my_ring → 第 II 部での活用）。「道具を使い、その道具を自作し、自作した道具で先へ進む」ループは既存教材（TPiL4 / MIL）にない本書独自の弧である。
- 数学の説明は最小限（読者は数学既知）。紙面は Lean 固有の概念に集中する。
- **縦糸は Lean の 3 つの鍵 — universe・依存型・帰納型。** 序章で予告し、依存型と universe は Ch2（∀=Π としての量化子・`Real.sup` の署名・Prop vs Type と Sort 階層 — 本書の全コードが Type 0 と Prop で完結することを universe 理解の教材として使う）、帰納型は Ch4（And/Or/Exists/Eq も Nat も帰納型という「正体」）で正面から扱い、Ch11（多項式 AST）で帰納型の応用として回収する。

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
| 強調する柱 | **Lean の 3 つの鍵: universe・依存型・帰納型**（Ch2・Ch4 で正面から扱い、全章の解説で意識的に言及する） |
| 扱わないもの | Monad/IO・universe 多相の実践（本書のコードは Type 0 と Prop で完結 — その事実自体を Ch2 の universe 解説の素材にする）。メタプログラミングは自動化章（Ch10・Ch11 ほか）で必要な範囲のみ |

## 3. 章立て

**設計原則: ゴール駆動。** 数学の到達点が章を決め、Lean の機能は「その過程で必要になった瞬間」に解説する。第 I 部のゴールはリーマン和の**定義・簡単な具体例・後で使う基本性質の証明**（締めに自動化の自作）。第 II 部でリーマン積分の定義 → 連続関数の可積分性 → FTC と進む。自動化（notation・タクティク自作・my_ring）は独立の部にせず本編に編み込む。

### 数学的背骨（全体の物語）

```
1. リーマン和の定義            （定義のみ・証明技術ゼロで書ける）
2. 具体例: y = x の n 等分     （証明技術の需要が爆発する場所）
3. リーマン和の性質 5 本        （帰納法・代数補題・IsRepr が動機付きで入る）
4. 積分の定義 ＝ 網目の極限     （ε-δ ネスト・choose・一意性）
5. 積分の性質                  （3 の各性質の ε/2 持ち上げ）
6. 連続 ⇒ 可積分              （山頂）
7. FTC
```

- 段 3 の「リーマン和の性質」は後段で実際に使う 5 本に厳選: `additive_riemann_sum` / `neg_riemann_sum` / `const_riemann_sum`（望遠鏡和 `length_sum`）/ `RiemannSum_nonneg`（**IsRepr / InInterval が「タグが区間内になければ非負にならない」という反例込みの動機で初登場**）/ `rs_abs_bound`。点挿入系は付録 B。
- 段 4 では 3 種類の ε-δ（`IsLimAt`・`Continuous`・`IsIntegral`＝網目に関するネット収束）を比較する。
- 段 5 は段 3 との対応表が章の構造になる:

| リーマン和の性質 | （持ち上げ） | 積分の性質 |
|---|---|---|
| additive_riemann_sum | ε/2 論法 | isintegral_add |
| const_riemann_sum | δ 任意 | const_has_integral |
| RiemannSum_nonneg | 矛盾論法 | integral_nonneg |
| rs_abs_bound | sup 構成の有界性 | integrable_of_cauchy 内部 |

- 段 6「連続⇒可積分」は難易度の異なる 4 部品に分解して扱いを変える:
  (i) 一様連続性 `continuous_unif_cont`（sup による区間帰納、308 行）= **statement 精読＋付録 A**
  (ii) コーシー型判定 `integrable_of_cauchy`（sup で積分値を構成する 55 行）= **本文精読＋誘導演習**
  (iii) 細分比較 `rs_compare`（多点挿入・階段原始関数、269 行）= **statement 精読＋付録 B**
  (iv) 組み立て `continuous_integrable`（41 行）= **本文完全精読**
  「補題を 2 本引用すれば主定理の証明は明快」という論文読解と同型の経験。`#print axioms` が sorry の混入を許さないので、引用した補題も証明済みであることが保証されている。

### 第 I 部 リーマン和（Ch0–11）

3 つの到達点: **① 定義が書ける（Ch5）② 具体例が計算できる（Ch8）③ 性質 5 本が証明できる（Ch9）**。締めに自動化（Ch10 間奏・Ch11 発展）。

| 章 | 数学の歩み | そこで必要になる Lean 機能 |
|---|---|---|
| Ch0 | 環境構築・リポジトリの歩き方 | lake・`#check` / `#print` / `#print axioms` |
| Ch1 | 最初の証明（`1 = 1`、`<` の 3 兄弟） | **命題=型・証明=項**（term mode、`fun`・`⟨⟩`・射影） |
| Ch2 | **実数の公理 5 本を読む** | 署名の読み方・**依存型**（`Real.sup`）・量化子・Prop vs Type・**universe**【鍵 1・2】・namespace / open |
| Ch3 | `+` と `0` はどこから来るか | **class と instance**（双子章・前編）・`axiom`＋`instance`・リテラルの正体・ダイヤモンド事件コラム |
| Ch4 | 有限和 Σ を手に入れる | **帰納型**【鍵 3】（∧∨∃= も Nat も帰納型 — Ch1 の道具の正体）・Subtype（`Range`）・構造的再帰（`Summation`） |
| Ch5 | 分割を表現し、**リーマン和を定義する**（到達点①） | **structure**（双子章・後編、証明を運ぶレコード）・**notation**（Σ 記法とリーマン和の記法を「定義したらすぐ」自作する）。章末: equalPartition を書き始めるが `increase` が **sorry のまま残る** |
| Ch6 | sorry を埋める道具 I | **tactic mode**（ゴール状態・intro / exact / apply / rw / have / show・term↔tactic の往復） |
| Ch7 | sorry を埋める道具 II | **defeq と rw の構文性**・`rfl` / `show`・calc 設計・**帰納法による証明**（summation 補題・cast 補題 = Ch8 への部品） |
| Ch8 | **具体例: y = x を [0,1] の n 等分で計算**（到達点②） | 総合演習 I: equalPartition のフィールド証明（**Ch5 の sorry がここで消える**）・分点 = i/n・`sum_id`・**RS = (n+1)/(2n)**（左端タグとの対比） |
| Ch9 | **後で使う性質 5 本**（到達点③） | 総合演習 II: additive / neg / const / nonneg / abs_bound。`RiemannSum_nonneg` の反例から **IsRepr** 登場 |
| Ch10 | 間奏: 自分の手を自動化する | **simp セット設計・`macro` / `macro_rules`**（`real_simp` / `triangle` 自作）・`ac_rfl` の種明かし（`Std.Associative`）。以後の演習で自作タクティク使用可 |
| Ch11 | **発展: my_ring を作る**（飛ばしても本線に影響なし） | **proof by reflection**: 多項式 AST（帰納型【鍵 3】の応用回収）→ 正規化 → 健全性 → `rfl` / `decide`。reify（`elab`）は最小限。**Ch8 の手計算を 1 行にして見せる**。linarith は読み物、mathlib の ring / linarith に接続 |

順序の設計判断: ① **tactic mode が Ch6 まで遅れるのは妥協ではなく主張** — リーマン和の記述に証明技術は不要（入り込む証明は添字の Nat 不等式の項埋めのみ）という事実を章構造で体現する。② 旧設計の「実数補題の章」は解体し、**需要駆動の演習素材**に降格（順序・除法の補題は `increase` 証明が、絶対値の補題は `rs_abs_bound` が要求した時に解く——「この補題は何のためにあるのか」が常に明確）。③ 古典論理と choice は第 I 部に置かない（リーマン和とその性質までは構成的に進められる）。④ class（Ch3）が structure（Ch5）より先なのは Ch2 で Axioms.lean を精読するため（双子章方式で処理）。

### structure と class の扱い（双子章方式）

両者は機械的にはほぼ同一（class = structure ＋ `@[class]`、instance = def ＋ `@[instance]`）なので、**「2 つの別概念」ではなく「1 つの仕組み＋値の渡し方の自動化」として正直に教える**。説明は 3 段:

1. **機械的な真実**: フィールド・射影・`⟨⟩`・`extends` はすべて共通。違いは `(Δ : Partition n a b)`（明示引数・名指しで渡す）か `[LinearOrderedField Real]`（インスタンス引数・機構が探して渡す）かだけ。
2. **設計判断の基準**: その添字（型）に対して値が**正準に 1 つ**なら class（「ℝ と言えば足し算は決まっている」という暗黙の了解の機械化）、**多数あって量化・構成・受け渡しの対象**なら structure（「[a,b] の分割全体を走る」の機械化）。読者用リトマス試験:

| 問い | structure なら | class なら |
|---|---|---|
| `∀ x, …` と量化したいか | する（`∀ P : TaggedPartition a b, …`） | しない |
| 使用時に名前を呼ぶか | 呼ぶ（`Δ.points`） | 現れない（`a + b`） |
| 2 つ目の値が存在したら | 当たり前（分割は無数） | 事故（NatCast ダイヤモンド事件） |

3. **反転演習で確定させる**: 「`Partition` を class にしてみよ」→ 分割を任意に走る ∀ が書けず **`IsIntegral` が定義不能になる**。逆に「`LinearOrderedField` を structure にしてみよ」→ `a + b` のたびに「どの + か」を指定する羽目になる。どちらも壊れたコードを読む演習に。

章割り上は Ch3（class 側）と Ch5（structure 側）の**双子章**とし、同じ比較表を 2 章かけて完成させる。Ch5 で「Ch1 から使っていた `And` も structure だった」（`#print And`）の種明かしを行い、Ch4 の帰納型と合わせて伏線を回収する。

### 第 I 部のストーリー（リーマン和への道）

**設計の仕掛け**: ① 各章は「前章の最後に残った問い」で開く**連鎖構造**。② 章末に import 図のうち「読めるようになったファイル」を塗りつぶす**現在地マップ**。③ 第 I 部は**2 幕構成** — 前半 Ch1–5 は*定義の幕*（リーマン和を**書く**: 証明技術ほぼ不要）、後半 Ch6–9 は*証明の幕*（sorry を**埋める**）。リーマン和の記述に必要なのは正確に 6 つ（`def`/`fun`・型の言語と暗黙引数・class が効いているという理解・帰納型と構造的再帰・Subtype・structure 宣言の読解）であり、記述に入り込む証明は添字の Nat 不等式の項埋めのみ——この事実を 2 幕構成の設計根拠として序文で示す。

各章のビート:

- **序章（挑戦状）**: 「あなたは ε-δ を知っている。では機械に説明できるか」。`main'` と `#print axioms main` の 8 行だけ見せ、3 つの鍵を予告。第 I 部の約束は「リーマン和を自分の手で定義し、計算し、性質を証明するところまで」。
- **Ch0**: 本文の半分はリポジトリそのもの。`main'` にカーソルを置きゴール表示を体験して閉じる——まだ読めない。読めるようになるのがこの本。
- **Ch1**: `1 = 1` から「証明は項」。実コード初日: `le_of_lt`（射影）/ `lt_of_le_of_ne`（構成）/ `ne_of_gt`（¬は関数）。引き:「実数とは何か。公理を読みに行こう」
- **Ch2**: 署名が読めれば半分わかる。公理 5 本の精読 — `Real.sup` の「証明を引数に取り、型が項に依存する」署名。Prop vs Type から Sort 階層へ。引き:「`+` や `0` はどこから来た？」
- **Ch3**: 根幹の 2 行 `axiom Real.instLOF` ＋ `instance`。リテラル `(2 : Real)` の正体。双子章前編＋ダイヤモンド事件コラム。引き:「リーマン和には Σ が要る。有限和とは何か？」
- **Ch4**: `#print Or` で種明かし — Ch1 から使ってきた ∧∨∃= も Nat もすべて帰納型。その目で `Range`（証明を抱えた添字）と `Summation`（構造的再帰）を読む。引き:「分割をデータとしてどう表す？」
- **Ch5**: 証明を運ぶレコード `Partition`（双子章後編・反転演習）。**リーマン和の定義は 1 行** — この 1 行に前章までの全部が映っている。定義したらすぐ **Σ 記法とリーマン和の記法を自作**（notation 初登場）。章末、equalPartition を書き始める——が、`increase` フィールドが埋まらない。**sorry が残ったまま幕**。
- **Ch6**: sorry を埋めるために。`by` とゴール状態、基本タクティク、term↔tactic の往復。
- **Ch7**: 等しさには 2 種類ある（`a + -b = a - b := rfl` が通るのに rw は区別する）。show・calc 設計。帰納法による証明 — summation 補題と cast 補題を獲得（Ch8 への部品）。
- **Ch8**: **sorry が消える日**。equalPartition 完成、分点 = i/n、`sum_id`、そして **RS = (n+1)/(2n)**。到達点②。
- **Ch9**: 性質 5 本の総合演習。望遠鏡和の快感、`RiemannSum_nonneg` の反例から IsRepr が必然として登場。到達点③。
- **Ch10（間奏）**: Ch6–9 で繰り返したパターン（三角不等式分解・min 分配・移項）を道具に固める。simp セット・macro 合成・ac_rfl の種明かし。
- **Ch11（発展）**: my_ring。Ch8 で手計算した代数が 1 行になる。第 I 部の幕引き:「和は手なずけた。この和は、分割を細かくしたときどこへ向かうのか——それに答えるには値をひとつ選び取る力が要る（第 II 部へ）」

### 貫通する具体例: y = x の [0,1] n 等分（Ch8 → Ch13 をまたぐ物語）

**n 等分の表現方針**: 自然数を Real の部分集合として構成する必要はない。型理論の正道は「`Nat`（帰納型）からの埋め込み」であり、本体に実装済み（`Real.ofNat` の構造的再帰・`NatCast` インスタンス・cast 補題群・`equalPartition` の分点 `a + i·(b−a)/m`）。代替案 2 つも素材として回収する:

- **杉浦流「最小の継承的集合」**は Prop の非可述性で 1 行で書ける（`InductiveSet x := ∀ S : Real → Prop, S 0 → (∀ y, S y → S (y+1)) → S x`）。これが cast の像述語 `fun x => ∃ n : Nat, x = ↑n`（**archimedean の証明に既出**）と同値であることを Ch12 のコラム＋発展演習にする — Ch2 の universe（Prop への量化）の生きた応用であり、原典（杉浦）との接続点。
- **「n·x = 1 の解」**は独立の構成にはならない（n 回足すことを述べるのに Nat が要る）が、「順序体では 0 < n·1、ゆえに標数 0 で 1/n が存在」は本体の実定理（`cast_pos_succ`）。「1/n は n·x = 1 の唯一解」を小演習にする。

**Ch8 名物演習**: `equalPartition n 0 1` の分点が `i/n` であることの確認（show の練習）→ 新補題 `sum_id : Summation n (fun i => (i.val : Real)) = n(n−1)/2` を帰納法＋cast 計算で証明（旧 NatNum.lean に sorry 付きで眠っていた式の回収）→ 右端タグで **RS = (n+1)/(2n)**、左端タグで (n−1)/(2n)。

**Ch13 誘導演習**: f = id は「定義から直接」可積分性を示せる稀有な例。中点和が望遠鏡和になり（Σ midᵢ·lenᵢ = (b²−a²)/2）、任意のタグで |ξᵢ − midᵢ| ≤ diam/2 だから **|RS − (b²−a²)/2| ≤ diam·(b−a)/2** — よって `IsIntegral id a b ((b²−a²)/2)`。`integral_unique` で Ch8 の「n 等分の極限 (n+1)/2n → 1/2」と「∫₀¹ x = 1/2」が繋がり、具体例が 2 部をまたいで閉じる。

必要な本体追加（P4 で開発）: `sum_id`（Real/Summation.lean）・`isintegral_id`（Integral/ 配下、中点望遠鏡和の補題込み）・Σ / リーマン和 / ∫ の記法。

### 第 II 部 リーマン積分（Ch12–16）

| 章 | 数学の歩み | Lean 機能・教材要素 |
|---|---|---|
| Ch12 | 選び取る力 — 分割の存在と値の取り出し | **古典論理と choice**（`Classical.em` / `by_cases` / `choose` / `noncomputable`、**構成的だった第 I 部との対比**で導入）。`min`・ceil・sup_near・**archimedean**（白眉①）・exists_fine_partition。コラム＋発展演習: 杉浦流「最小の継承的集合」との同値 |
| Ch13 | **リーマン積分の定義**＝網目の極限・well-definedness | 3 種の ε-δ 比較（IsLimAt / Continuous / IsIntegral）・`TaggedPartition`・`dite`＋choose・`integral_unique`。**∫ 記法を定義した直後に自作**（Ch5 の再演）。誘導演習: `IsIntegral id`（貫通具体例がここで閉じる） |
| Ch14 | 積分の性質 ＝ **Ch9 の 5 性質の ε/2 持ち上げ**（対応表が章の構造） | `min δf δg` 定石・isintegral_add（最純形）。演習: ε/2 定石を macro に固める（Ch10 の応用） |
| Ch15 | **山頂: 連続 ⇒ 可積分**（4 部品分解） | 大規模証明のアーキテクチャ（private・section・import DAG）。(ii) integrable_of_cauchy 精読＋ sup 構成 4 ブロック誘導演習・(iv) continuous_integrable 完全精読・(i)(iii) は statement 精読＋付録 |
| Ch16 | **FTC** | statement 中の `let`・`#print axioms` 監査の意味。コラム: `propext` / `Quot.sound` / `Classical.choice` とは何か |

### 自動化の編み込み（独立の「第 III 部」は置かない）

自動化は **Ch5（Σ・リーマン和の記法）→ Ch10（間奏: simp セット・macro 合成）→ Ch11（発展: my_ring）→ Ch13（∫ 記法の再演）→ Ch14（ε/2 macro 演習）** と本編に編み込む。「作った道具を以後の章で使う」ループが本の中で回り、学習曲線も notation（数行）→ macro 合成（中）→ リフレクション（重）の 3 段に分散される。

- 演習で自作タクティクを許す際は「**模範解答（本体）は手書き。自作道具は加速装置**」と明記し、本体=模範解答の原則を保つ。
- 素材コード `MyProject/Tactic/`（合成タクティク・`MyRing.lean`）と本体への記法追加は P4 で開発（背骨の import 鎖には不干渉）。
- **my_ring 設計方針**: 可換環の項を Nat 係数多項式の正規形（ソート済み単項式リスト）に正規化し、`DecidableEq` で正規形を比較。健全性 `eval ρ e = eval ρ (norm e)` を帰納法で証明し、タクティクは「reify → 健全性適用 → `decide` / `rfl`」。

### 付録

- 付録 A: 一様連続性を読む（UniformContinuity — Ch15 部品 (i) の全証明）
- 付録 B: 細分・振動和・区間加法性（Insert / Refine / Oscillation / IntervalAdd — Ch15 部品 (iii) ほか）
- 付録 C: mathlib への橋（本書の各概念の mathlib 対応表。MIL を次の一冊として推薦）

## 4. 演習機構の設計

### 4.1 配置

```
Exercises/
  C01_FirstProofs.lean      -- Ch1（本体に対応物なし）
  C02_Axioms.lean           -- Ch2（署名読解クイズ）
  C03_Algebra.lean          -- 以降、本体ファイルのミラー
  ...
  C16_FTC.lean
  Solutions/                -- C01 等、本体に対応物がない問題の解答
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
- 読者の検証: ① VS Code 上で sorry を埋めて波線が消えることを確認（主経路）② 章単位 `lake build Exercises.C03_Algebra` ③ 全完了後 `lake build Exercises` が警告ゼロなら修了

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
| **P2 教材向け本体改修** | ① Range.lean の `has_min` を技巧的な形から素直な `Nat.strongRecOn` 適用形へ書き直し（Ch12 の教材対象）② Integral/Def.lean の private キャスト系ヘルパー（my_cast_nonneg / cast_le_succ / nat_ne_zero_of_nonneg_lt / cast_pos_of_ne）を Real/Cast.lean へ公開移動（4.2 の規則の成立条件）③ Continuity.lean を 2 分割（Continuous 定義＋continuous_sub/const = Ch13 と、UniformContinuity.lean = 付録 A）④ 命名修正: `IsIntegral_iff` → `integral_eq_of_isIntegral`、Real/Algebra.lean のプライム混在エイリアス一本化 ⑤ 清掃: 未使用 typo クラス `CompletLinearOrderedField`、`#check` 残骸等 ⑥ 背骨の主要定義に doc comment | ビルド・公理監査グリーン |
| **P3 演習基盤＋book 骨格** | Exercises/ 雛形＋機構実証として C03（Real/Algebra ミラー）・C07（Order/Abs ミラー）を実作＋lakefile 追記＋`scripts/check_exercises.py`＋book/ 骨格（SUMMARY.md・ch00 ドラフト・各章スタブ）＋README を教材リポジトリとして更新 | `lake build` 警告ゼロ・`lake build Exercises` は sorry 警告のみ・ドリフト検査が機能 |
| **P4 章執筆ループ** | 章ごとに「演習作成 → 自力 1 周で難度調整 → 原稿 md 執筆（include 配線）→ ドリフト検査」。推奨順: 第 I 部の背骨 Ch3〜9 → 第 II 部 Ch12〜16 → Ch1・2 → Ch10・11（`MyProject/Tactic/` 開発含む）→ Ch0 → 付録 | 各章: 演習が sorry 以外で警告ゼロ・原稿ビルド成功 |
| **P5 公開** | 公開先決定（Zenn / GitHub Pages）、deploy 整備、Ch0 に導線 | 公開 URL で全章閲覧可・clone から演習着手まで 10 分以内 |

## 7. 既存教材との関係・参考文献

- **Theorem Proving in Lean 4**（Avigad, de Moura, Kong, Ullrich）: 概念順（DTT → 命題と証明 → 量化子 → Tactics → … → 帰納型 → 構造体 → 型クラス → 公理と計算）は本書第 I 部とほぼ整合。差分は ① 型クラスの前倒し（Ch3、Axioms.lean 読解に必須）② TPiL ch6「Interacting with Lean」（namespace / section / open）は Ch2 に吸収 ③ conv は不使用のため扱わない。トピックの過不足はこの 3 点で説明できることを確認済み
- **Mathematics in Lean**（Avigad, Massot）: 演習方式（リポジトリ clone・本文中に随時 sorry・解答同梱）を採用。ただし MIL の ring / linarith 等の自動化は本書では不使用——「MIL が自動化に任せる部分を全て手で組み、その自動化を本編の中で自作して以後の章で使う」が本書の差別化
- **The Mechanics of Proof**（Macbeth）: 制限タクティクセットで数学を教える方針が近い。序章の文献案内に含める
- **Metaprogramming in Lean 4**（Paulino 他）: 自動化章（Ch5 の notation・Ch10・Ch11）の「より深く」の参照先
