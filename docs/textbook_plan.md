# Lean 入門教材 設計書

— 公理 5 本から微積分学の基本定理へ、そして自動化の自作まで —

本書は Tsudoi6 リポジトリ（mathlib 非依存・公理的実数で微積分学の基本定理 FTC を sorry ゼロで完全証明、約 4300 行）を素材とする Lean 4 入門教材の設計書である。

## 1. コンセプトと差別化

**統一テーゼ:「数学も、道具も、開けて見る」——信じる対象を 5 本の公理と 1 つの小さなカーネルまで切り詰める**

本書は 2 本の柱を持つ。どちらも「ブラックボックスゼロ」という同じテーゼの現れである:

- **柱 A（数学を開ける）**: 実数の公理（線形順序体＋上限公理）だけから出発し、mathlib なし・自動化なしでリーマン積分を構成し FTC を証明する一本道を、読者が演習で自ら登る。監査装置は `#print axioms`。
- **柱 B（道具を開ける）**: 単に Lean を書けるようにするのではなく、**その仕組みまで解説する**。タクティクが「なぜ証明になるのか」を `#print`（生成された証明項）と De Bruijn 基準（信じるのはタクティクではなく、その出力を検査する小さなカーネル）で答え、rw・simp・apply・omega の中身を開け、最後は読者がタクティクを自作する。**入門書でタクティクの内部まで踏み込むのは既存教材にない本書最大の特徴**（TPiL4 は扱わず、MIL は意図的にブラックボックス、Metaprogramming in Lean 4 は入門書でない）。
- 2 本の柱は Ch11（my_ring）で合流する: リフレクションは「証明はプログラムである」（柱 B'＝CH 対応）を実用に投じる行為そのものであり、読者は omega や decide が「どういう種類の物体か」を自作によって知る。
- その上で**手作業だった証明の自動化を読者自身が作り、以後の章で使う**（Ch5 の記法自作 → Ch10 間奏のタクティク合成 → Ch11 発展の my_ring → 第 II 部での活用）。「道具を使い、その道具を自作し、自作した道具で先へ進む」ループは既存教材（TPiL4 / MIL）にない本書独自の弧である。
- 数学の説明は最小限（読者は数学既知）。紙面は Lean 固有の概念に集中する。
- **CH 対応は数学者向けに理論的背景まで踏み込む**: BHK 解釈を意味論として先に置き、CH 対応を「BHK の型理論による実装」として導入。自然演繹との対応（導入則↔コンストラクタ・**除去則↔recursor**）を `#print And.rec` 等の実コーディングで裏付け、納得感を持たせる（§3 の縦断スレッド (a)）。**タクティクには種明かしの糸**（縦断スレッド (b)）と**「理論の窓」コラム系列**を通す。
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

- 段 3 の「リーマン和の性質」は後段で実際に使う 5 本に厳選: `additive_riemann_sum` / `neg_riemann_sum` / `const_riemann_sum`（望遠鏡和 `length_sum`）/ `RiemannSum_nonneg`（**IsRepr / InInterval が「タグが区間内になければ非負にならない」という反例込みの動機で初登場**）/ `rs_bound`（両側評価。abs は第 II 部まで登場しないため）。点挿入系は付録 B。
- 段 4 では 3 種類の ε-δ（`IsLimAt`・`Continuous`・`IsIntegral`＝網目に関するネット収束）を比較する。
- 段 5 は段 3 との対応表が章の構造になる:

| リーマン和の性質 | （持ち上げ） | 積分の性質 |
|---|---|---|
| additive_riemann_sum | ε/2 論法 | isintegral_add |
| const_riemann_sum | δ 任意 | const_has_integral |
| RiemannSum_nonneg | 矛盾論法 | integral_nonneg |
| rs_bound（両側評価） | sup 構成の有界性 | integrable_of_cauchy 内部 |

- 段 6「連続⇒可積分」は難易度の異なる 4 部品に分解して扱いを変える:
  (i) 一様連続性 `continuous_unif_cont`（sup による区間帰納、308 行）= **statement 精読＋付録 A**
  (ii) コーシー型判定 `integrable_of_cauchy`（sup で積分値を構成する 55 行）= **本文精読＋誘導演習**
  (iii) 細分比較 `rs_compare`（多点挿入・階段原始関数、269 行）= **statement 精読＋付録 B**
  (iv) 組み立て `continuous_integrable`（41 行）= **本文完全精読**
  「補題を 2 本引用すれば主定理の証明は明快」という論文読解と同型の経験。`#print axioms` が sorry の混入を許さないので、引用した補題も証明済みであることが保証されている。

### テキスト構成 v2（ゼロベース再確定、2026-06-12。以下の v1 章表は素材庫として保持）

試作 M1–M7 完了後にゼロベースで再構成した確定版。設計原理は **2 本の梯子の同時単調性**——数学は依存順に積み上げ、Lean 機能は簡単→難しいの順にしか初出させない。試作の実測（機能の初出点・公理監査の勾配・行数の重量配分）で両梯子の整合を検証済み。部の切れ目＝**古典論理の入口**（第 I 部は監査 [Real, instLOF] のみで完結、という実測事実が部構成になる）。

**ユーザー決定（2026-06-12）**: ① FTC は一式を最終章に置く（機構→山頂→FTC の古典的順序。核の前置案は不採用）② 自動化の間奏章は 1 つだけ（旧 Ch10+Ch11 を統合し、my_ring 本体は付録/発展演習へ降格）。

| 章 | 数学の歩み | Lean 機能の初出（詳細素材は v1 対応章を参照） |
|---|---|---|
| **第 I 部 リーマン和（構成的な世界）** | | 監査: [Real, instLOF] のみ |
| Ch0 | 環境構築 | lake・#check/#print/#print axioms |
| Ch1 | 証明はデータ（論理） | 命題=型・証明=項・fun・⟨⟩・射影 |
| Ch2 | 実数を 5 本の公理で読む | 署名読解・依存型（sup）・Prop/Type・universe |
| Ch3 | + と 0 はどこから来るか | class・instance（双子章前編）・インスタンス解決 |
| Ch4 | 有限和 Σ | 帰納型・Subtype（Range）・構造的再帰・rfl=defeq |
| Ch5 | 分割とリーマン和（**到達点①**） | structure（双子章後編）・notation 自作・sorry クリフハンガー |
| Ch6 | sorry を埋める道具 I | tactic mode（intro/exact/apply/rw/have/show）・種明かし |
| Ch7 | sorry を埋める道具 II | defeq と rw の構文性・calc・帰納法（Σ補題コーパス） |
| Ch8 | y = x の n 等分（**到達点②**） | 3 段の梯子・OfNat 伏線回収・NatCast・cast 補題・sum_id（肥大時 2 分割予約は維持） |
| Ch9 | リーマン和の性質 5 本（**到達点③**） | 総合演習・**両側評価=脱 abs の入口**・第 I 部古典ゼロ監査 |
| Ch10 | 間奏: 自分の手を自動化する | simp セット・macro 自作・my_ring は**入口のみ**（本体は付録/発展演習） |
| **第 II 部 積分と FTC（古典的な世界）** | | choice → sup が順に入る |
| Ch11 | アルキメデスと探索 | ∃/obtain・Classical.em/by_cases・has_min・ceil・**sup 初使用**（archimedean=白眉①）・exists_fine_partition・素朴定義実験 |
| Ch12 | 積分の定義 | Near 統一の 3 種 ε-δ・∀ 形の細かさ・dite+choose・noncomputable・監査 3 層 |
| Ch13 | 一意性 | ε/2＋ネットの非空性・min-free 合流（exists_min2 イディオム）・橋=choose の仕様書（橋の応用: 値の等式たち） |
| Ch14 | 直接証明: ∫x = (b²−a²)/2 | 中点望遠鏡和・**sup なし監査**（完備性不要の発見）・y=x の物語が部をまたいで閉じる |
| Ch15 | 山頂: 連続 ⇒ 可積分 | 大規模証明のアーキテクチャ・4 部品分解（(ii)判定+(iv)組立=本文精読、(i)一様連続+(iii)細分=statement 精読＋付録。重量実測: 細分 1047 ≫ 一様連続 307 ≫ 判定 114 ≫ 組立 82 行） |
| Ch16 | **FTC**（核＋実体化） | ftc_core（局所・一意性フリー）→ 橋 1 回で実体化・監査総決算（公理の勾配表）・「全域化の代価」コラム |

**v1 からの変更点と理由**:
1. **積分の性質の章（旧 Ch14）を主線から廃止** — 試作の発見「ftc_core は加法性・線形性・一意性を一切使わない」を構成に反映。性質群は Ch13 の橋の応用（節）＋発展演習へ。
2. **∫x の直接証明を章に昇格（新 Ch14）** — 旧 Ch13 の誘導演習から独立。sup なし監査の発見・一意性直後の具体的計算というペース配分・貫通具体例の閉じ目を 1 章で担う。肥大/縮小の調整点として予約。
3. **間奏は Ch10 の 1 章のみ** — my_ring（旧 Ch11）は入口だけ本文、本体は付録/発展演習へ。
4. 新旧対応: 旧 Ch0–9 → 新 Ch0–9（同一）、旧 Ch10+11 → 新 Ch10、旧 Ch12 → 新 Ch11、旧 Ch13 → 新 Ch12（+∫x は新 Ch14 へ）、旧 Ch15 → 新 Ch15、旧 Ch16 → 新 Ch16。v1 表の章別素材はこの対応で引き継ぐ。

### 章別詳細設計 v2（2026-06-12。v1 素材の移植＋試作コードの章割り付け）

#### Text/ 最終ファイル計画（Proto → 章の割り付け）

Proto/ は試作の記録としてそのまま温存し、執筆時に章対応の C** ファイルへ整形して写す（命名・順序・コメントを章の進行に最適化）。章とファイルはほぼ 1:1（Ch0 のみファイルなし。C03 は実演・実験専用、C06/C07 は演習集）。

| Text ファイル | 章 | 内容 | Proto 整形元 | 行数目安 |
|---|---|---|---|---|
| C01_FirstProofs | Ch1 | 論理ウォームアップ | 新規 | 40 |
| C02_Axioms | Ch2–3 | 階層クラス・公理 5 本・instance・最小インスタンス・`<` の 3 兄弟 | Axioms (74) | 60 |
| C03_Class | Ch3 | **実演・実験専用**（根幹 2 行の観察・`#check_failure (1/2 : Real)`・ダイヤモンド事件トイデモ。定義は足さない・import 連鎖の葉） | 新規（2026-06-12 決定で C03 復活） | 45 |
| C04_Summation | Ch4 | Range・incl/addone・Summation・zero/succ (rfl) | Sum (29) | 25 |
| C05_RiemannSum | Ch5 | Partition・length・RiemannSum・Σ/RS 記法・trivialPartition（sorry） | Partition の定義部 | 35 |
| C06_Tactics | Ch6 | タクティク演習集（代数補題の基礎部） | Lemmas 基礎部 | 60 |
| C07_Induction | Ch7 | Σ補題コーパス 9 本・Trans・calc 演習 | FTCCore§Σ＋InsertBound§1＋Refine§3 を再配列 | 120 |
| C08_Numbers | Ch8 | OfNat/ofNat/NatCast・cast 補題（構成的部）・equalPartition・sum_id・RS=(n+1)/(2n) | Numerals＋Cast 前半＋EqualPartition＋Example§2 | 150 |
| C09_Properties | Ch9 | IsRepr・tag_mem・points_mono・length_sum・const_sum・additive/neg/nonneg・両側 rs_bound | FTCCore§分割＋Criterion§両側評価 | 120 |
| C10_Automation | Ch10 | simp セット・macro 合成・my_ring 入口 | 新規（P4 開発） | 80 |
| C11_Archimedes | Ch11 | sup_near・archimedean・has_min・natMin・ceil・exists_fine_partition・古典順序補題・素朴定義実験 | Cast 後半＋EqualPartition(fine)＋Lemmas 古典部 | 160 |
| C12_Integral | Ch12 | TaggedPartition・Fine・Near・IsIntegral・Integral・Integral'・ContinuousAt・∫記法 | Partition 残部＋Integral＋FTC(ContinuousAt) | 70 |
| C13_Unique | Ch13 | integral_unique・橋・橋の応用（値の等式） | Unique | 90 |
| C14_Example | Ch14 | 代数小物・degenerate_sum・isintegral_id・integral_id | Example（sum_id 除く） | 200 |
| C15_Summit | Ch15 | NearLe 基本・integrable_of_cauchy・continuous_integrable・(i)(iii) の statement 集 | Criterion＋Main 前半＋InsertBound§2 | 250 |
| C16_FTC | Ch16 | HasStraddleDeriv・ftc_core（核の部品込み）・ftc 実体化 | FTC＋FTCCore 核部＋Main 後半 | 380 |
| 付録 A | — | 一様連続性・有界性の全文 | UnifCont (307) | 310 |
| 付録 B | — | 挿入・細分機械の全文 | Insert＋InsertBound＋Refine (1047) | 1050 |

#### 第 I 部の章詳細（v1 素材は対応章をそのまま引き継ぎ、差分のみ記す）

- **Ch0–Ch8**: v1 素材庫の同番章のとおり（連鎖構造・ビート・双子章・クリフハンガー・3 段の梯子・肥大時 2 分割予約、すべて維持）。試作からの更新点:
  - **Ch7 の種明かしに「rw の罠 2 種」を追加**（試作知見 5: 引数明示・独立補題への切り出し——実戦で遭遇した実例つき）。
  - **Ch8 の sum_id は (1+1)·Σi = n·(n−1) 形**（リテラル 2 の演出と脱リテラル設計の両立。監査 [Real, instLOF] = 古典ゼロの実測値を章末に）。cast 補題は構成的部（succ_ofNat・cast_nonneg・cast_add・cast_lt・cast_le_succ）のみ——sup を使う archimedean 系は Ch11 へ送る、という**分割線そのものを「公理の節約」の教材**にする。
- **Ch9 リーマン和の性質 5 本**: additive / neg / const（望遠鏡和 length_sum 経由）/ nonneg（反例から IsRepr・tag_mem 登場）/ **両側 rs_bound**（試作の sum_le_const / const_le_sum がそのまま教材形）。points_mono（Nat 帰納法の好例・well-founded 不要）もここ。章末監査で第 I 部古典ゼロを確認。
- **Ch10 間奏**: v1 Ch10 のとおり（simp セット・macro・ac_rfl 種明かし）＋ my_ring は「Ch8 の手計算が 1 行になる」デモと AST の入口だけ本文、実装は付録/発展演習（v1 Ch11 を圧縮）。

#### 第 II 部の章詳細

- **Ch11 アルキメデスと探索**（旧 Ch12 を改題・拡充）: 主役は「**∃ から値を選び取る 3 つの方法**」——(1) sup（公理が Skolem 化済み・choice 不要）→ sup_near → **archimedean（白眉①）**、(2) Nat の最小値探索 has_min（strongRecOn——choice 不要だが定義は noncomputable）→ natMin → ceil、(3) Classical.em / by_cases（命題の分岐）。素材は Cast 後半＋exists_fine_partition（equalPartition_fine 込み: 「アルキメデスが細かい分割を製造する」）。**素朴定義実験**をここで実施（max を if で定義 → 監査に choice。Ch9 の両側評価が abs の言い換えだった種明かしと、第 I 部にこれを置かなかった理由の回収）。古典順序補題（not_lt_imp_le 等）もここで初登場。コラム: 杉浦流「最小の継承的集合」との同値。
- **Ch12 積分の定義**（旧 Ch13 前半）: TaggedPartition（∀ 量化のための束ね）・Fine の ∀ 形・**Near 統一の 3 種 ε-δ**（IsLimAt は演習・ContinuousAt・IsIntegral）・dite＋choose の Integral・∫ 記法の自作（Ch5 の再演）・**監査 3 層**（IsIntegral=古典ゼロ／Integral=+choice（choose と propDecidable の 2 箇所）／Integral'=+sup・choice フリー）。🪟「計算的読みの終わり——noncomputable という傷跡」。sup 最小性実験の対: 「Integral' だけが sup を使う」。
- **Ch13 一意性**（旧 Ch13 後半＋旧 Ch14 の残置分）: ε/2＋ネットの非空性（アルキメデスの値段——Ch11 の exists_fine_partition がここで請求される）・**min-free 合流の exists_min2 イディオム**（試作知見 2。v1 の調和平均手筋は置き換え）・橋 integral_eq_of_isIntegral=choose の仕様書。**節「橋の応用」**: const の積分値等式を橋で 1 本導出して見せ、線形性・単調性等の持ち上げ（旧 Ch14 の対応表）は発展演習へ——**主線（FTC）はこれらを使わない**という試作の発見を明示するのが節の落ち。
- **Ch14 直接証明: ∫x = (b²−a²)/2**（新設）: f=id は定義から直接可積分性を示せる稀有な例。中点和が望遠鏡和になる（Ch7 の telescope_sum・Ch9 の length_sum の回収）→ 任意タグとの差は各小区間 ±len/2 → ±(δ/2)(b−a)。**監査: sup なし**（「定義から直接」は完備性不要——どこで sup が要るのかの対照実験）。integral_id（橋の 2 回目）で Ch8 の (n+1)/(2n) → 1/2 と接続し、**貫通具体例が部をまたいで閉じる**。平方差 add_mul_sub 等の代数小物は my_ring（Ch10）の活躍どころ。
- **Ch15 山頂: 連続 ⇒ 可積分**: v1 Ch15 のとおり 4 部品分解＋大規模証明のアーキテクチャ。精読配分は重量実測で確定: **(ii) integrable_of_cauchy（114 行）=本文精読＋sup 構成 4 ブロック誘導演習・(iv) continuous_integrable（82 行）=本文完全精読**（誤差配分 ε/4+ε/4 の脱リテラル処理込み）・(i) 一様連続（307 行）と (iii) 細分（1047 行）= statement 精読＋付録 A/B。**NearLe ツールキット**（trans/symm/mono/of_add——abs 三角不等式の置換、試作知見 1）は statement 読解に必要な分を本文で導入。(iii) の rmin（証明装置の min・choice の源）は Ch11 の素朴定義実験の「実戦での再会」として一言。退化区間 [u,u] の処理（全分点が潰れる）も小教材。
- **Ch16 FTC**: ftc_core の**核の 3 部品**（const_isintegral・isintegral_le_of_le / le_isintegral_of_le=両側比較）を誘導演習で作らせてから核を本文精読——**核は完全に局所的**（hax/hxb 不使用・区間加法性も一意性も存在定理も不要、という試作の発見が章の主張）。実体化 ftc は橋 1 回（Ch13 の再演）。締めに**監査総決算**: 公理の勾配表（試作完了データの表をそのまま使う）で「どの数学がどの公理を要求したか」を一望。コラム: 「全域化の代価」・propext / Quot.sound / Classical.choice とは何か・🪟「FTC はどこまで構成的か」。

#### 横断的な確定事項（v2）

1. **Lemmas.lean（381 行）の分配**: 代数・順序の補題は需要駆動で C06–C09 の演習に（v1 の方針どおり）。**Classical を使う補題（not_lt_imp_le 等）は第 I 部に置けない**——分配時に監査でチェックする（試作で実証済みの分割線）。
2. **Σ補題の最終配置**: zero/succ（Ch4・rfl）→ 線形性・順序・congr・telescope（Ch7）→ all_zero/one_term/split_term（付録 B。split_term は挿入機械の部品）。neg_summation/sub_summation は Ch9 の軽演習。
3. **Near/NearLe の導入順**: Near は Ch12（定義と同時）、NearLe は Ch15（評価の言葉として）。第 I 部の両側評価（Ch9）は述語化せず生の不等式で書く——「同じ形が 3 回出たら述語に昇格する」という抽象化のタイミング自体を教材にする。
4. **検証手順（執筆時）**: 各 C** ファイル完成ごとに `lake build Text`＋章末の `#print axioms` が設計どおりか確認（第 I 部=古典ゼロ、Ch12 の 3 層、Ch14 の sup なし、Ch16 の勾配表）。sup 最小性実験（コメントアウトで C05 が通る）も Ch2 演習として再現。

### 【v1 素材庫】第 I 部 リーマン和（旧 Ch0–11）

3 つの到達点: **① 定義が書ける（Ch5）② 具体例が計算できる（Ch8）③ 性質 5 本が証明できる（Ch9）**。締めに自動化（Ch10 間奏・Ch11 発展）。

| 章 | 数学の歩み | そこで必要になる Lean 機能 |
|---|---|---|
| Ch0 | 環境構築・リポジトリの歩き方 | lake・`#check` / `#print` / `#print axioms` |
| Ch1 | 最初の証明（`1 = 1`、論理の項証明。Real 不要） | **命題=型・証明=項**（term mode、`fun`・`⟨⟩`・射影）。**CH 対応の 6 対応表を提示**（スレッド (a) の起点） |
| Ch2 | **実数の公理 5 本を読む** | 署名の読み方・**依存型**（`Real.sup`）・量化子・Prop vs Type・**universe**【鍵 1・2】・namespace / open。CH 表の量化子行を裏付け（∀=依存関数 Π・∃=依存和）。🪟 公理と noncomputable。締めに**最初の実数証明**: `<` の 3 兄弟（`le_of_lt`=射影・`lt_of_le_of_ne`=構成・`ne_of_gt`=¬は関数——Ch1 の論理が Real に着地する瞬間） |
| Ch3 | `+` と `0` はどこから来るか（新ファイルなし、C02 を素材に教える章） | **class と instance**（双子章・前編）・`axiom`＋`instance`・インスタンス解決。`#check (2 : Real)` が**エラーになる**実演（failed to synthesize——機構がエラーとして見える。Ch8 で回収）・ダイヤモンド事件コラム |
| Ch4 | 有限和 Σ を手に入れる | **帰納型**【鍵 3】・Subtype（`Range`）・構造的再帰（`Summation`）。**CH 対応のパンチライン**: ∧∨∃=False も Nat もすべて帰納型——「論理は依存関数＋帰納型で実現できる」（`#print` で確認）。コラム:「なぜ List でないのか」（表現の選択の論点）。章末に `summation_zero` / `succ`（rfl） |
| Ch5 | 分割を表現し、**リーマン和を定義する**（到達点①） | **structure**（双子章・後編、証明を運ぶレコード）・**notation**（Σ 記法とリーマン和の記法を「定義したらすぐ」自作する）。章末: **1 分割（trivialPartition）**——リテラルも除法も不要、なのに `increase` が書けず **sorry のまま残る** |
| Ch6 | sorry を埋める道具 I | **tactic mode**（ゴール状態・intro / exact / apply / rw / have / show・term↔tactic の往復）。**種明かし: タクティクは証明項を書く機械**（by 証明を `#print` して生成された λ 項を見る） |
| Ch7 | sorry を埋める道具 II | **defeq と rw の構文性**・`rfl` / `show`・calc 設計・**帰納法による証明**（Summation 補題コーパス 7 本＝添字付け替えの訓練場。cast 補題は NatCast 導入後の Ch8 で）。種明かし: **rw の正体 = `Eq.mpr`＋motive**——構文的である理由が機構レベルで腑に落ちる |
| Ch8 | **具体例: y = x を [0,1] の n 等分で計算**（到達点②） | **3 段の梯子**: ① 1 分割の sorry を消す（道具の最初の獲物）② 2 等分——リテラル `2`（OfNat 物語＝Ch3 の伏線回収）と除法が初登場 ③ n 等分——**NatCast**（↑i、リテラル用 OfNat との対比）・cast 補題・`sum_id`。仕上げに **RS = (n+1)/(2n)**（左端タグとの対比）。⚠ 肥大時は 2 章に分割予約 |
| Ch9 | **後で使う性質 5 本**（到達点③） | 総合演習 II: additive / neg / const / nonneg / **rs_bound（両側評価——abs は使わない。第 I 部の構成性を守る）**。`RiemannSum_nonneg` の反例から **IsRepr** 登場。章末の `#print axioms`: **第 I 部は古典公理ゼロ**を監査 |
| Ch10 | 間奏: 自分の手を自動化する | **simp セット設計・`macro` / `macro_rules`**（`real_simp` / `triangle` 自作）・`ac_rfl` の種明かし（`Std.Associative`）。種明かし: **simp の正体 = 停止を期待する有向書き換え系**（セット設計＝規則の設計）。以後の演習で自作タクティク使用可 |
| Ch11 | **発展: my_ring を作る**（飛ばしても本線に影響なし） | **proof by reflection**: 多項式 AST（帰納型【鍵 3】の応用回収）→ 正規化 → 健全性 → `rfl` / `decide`。reify（`elab`）は最小限。**Ch8 の手計算を 1 行にして見せる**。linarith は読み物、mathlib の ring / linarith に接続 |

順序の設計判断: ① **tactic mode が Ch6 まで遅れるのは妥協ではなく主張** — リーマン和の記述に証明技術は不要（入り込む証明は添字の Nat 不等式の項埋めのみ）という事実を章構造で体現する。② 旧設計の「実数補題の章」は解体し、**需要駆動の演習素材**に降格（順序・除法の補題は `increase` 証明が、絶対値の補題は `rs_abs_bound` が要求した時に解く——「この補題は何のためにあるのか」が常に明確）。③ 古典論理と choice は第 I 部に置かない（リーマン和とその性質までは構成的に進められる）。④ class（Ch3）が structure（Ch5）より先なのは Ch2 で Axioms.lean を精読するため（双子章方式で処理）。

### 縦断スレッド: CH 対応の段階的裏付けとタクティクの種明かし

**(a) Curry–Howard 対応**は概念説明だけで終わらせず、理論的背景（数学者向け）と Lean の機能による段階的裏付けの両輪で進める。意味論としてまず **BHK 解釈**（∧ の証明とはペア、∃ の証明とは実例と証明の組…）を置き、CH 対応を「BHK の型理論による実装」として導入する。Ch1 で次の対応表を提示し、章が進むごとに `#print` で「Lean では実際にそうなっている」ことを確認していく:

| 論理 | 型構成 | Lean での実現 | 裏付け |
|---|---|---|---|
| かつ ∧ | 直積 | `And`（1 コンストラクタ帰納型 = structure） | Ch1 提示 → Ch4 正体 → Ch5 双子章で再訪 |
| または ∨ | 直和 | `Or`（2 コンストラクタ帰納型） | Ch1 → Ch4 |
| ならば → | 関数 | 原始（関数型） | Ch1 |
| 否定 ¬ | Bot への関数 | `P → False`。`False` は 0 コンストラクタ帰納型 | Ch1 → Ch4 |
| 全称 ∀ | 依存関数 Π | 原始（依存関数型） | Ch2 |
| 存在 ∃ | 依存和 Σ | `Exists`（帰納型）。Type 側の親戚: `Sigma`・`Subtype`（`Range` として Ch4 に実物登場） | Ch2 → Ch4 |

**Ch4 がパンチライン**: 6 対応のうち原始は（依存）関数型だけで、残りはすべて帰納型——**「論理は依存関数と帰納型で実現できる」**。さらに自然演繹との対応を完成させる: **導入則↔コンストラクタ、除去則↔recursor**（`#print And.rec` / `Or.rec`——「帰納法の原理とは除去則のことだった」）。これは `induction` タクティクの種明かし（recursor 適用の糖衣）としてスレッド (b) とも交差する。3 つの鍵のうち 2 つ（依存型・帰納型）が CH 対応の説明と一体化し、別々の話題ではなくなる。

CH/BHK の物語は第 II 部冒頭で**転調**する: `Classical.choose` の証明項は計算できない——**`noncomputable` キーワードは、計算的読み（BHK）を離れたことを Lean が正直に表示する傷跡**である。「第 I 部は構成的・choice は第 II 部冒頭」という本書の構造に、柱 B' が理論的意味を与える（Ch12）。

**(b) タクティクの種明かしの糸**。「tactic で証明できるのは分かるが、なぜそれが証明なのか」という数学者の引っかかりに、完全でなくとも第 I 部の時点で答える:

| 章 | 種明かし |
|---|---|
| Ch6 | **信頼の構造（De Bruijn 基準）**: タクティクは信じない——タクティクが吐いた項を検査する小さなカーネルだけを信じる。タクティクがどれだけ複雑でもバグっていても健全性は壊れない（壊れるなら型検査で落ちる）。その上で**タクティクは証明項を書く機械**: by 証明を `#print` し、生成された λ 項を見る。intro=fun、exact=項の埋め込み。**apply の正体はメタ変数＋単一化**: ゴールに「穴」（`?m.123`）を開け、単一化で埋める——`_` も暗黙引数も同じ穴（Ch2 と機構レベルで接続） |
| Ch7 | **rw の正体**: `Eq.mpr`＋motive（congrArg）。`#print` で rw 証明の項を見れば、rw が構文的でなければならない理由（本章のテーマ）が機構レベルで腑に落ちる。**omega / decide の正体**: 決定手続き＋`Decidable` インスタンス＋カーネル計算による証明——Ch11 への伏線 |
| Ch10 | **simp の正体**: 停止を期待する有向書き換え系。simp セット設計＝書き換え規則系の設計。macro によるタクティク合成で「タクティクを作る」側へ一歩 |
| Ch11 | **実装そのもの**: reflection と最小限の elab。読者は決定手続きを自作し、「omega がどういう種類の物体か、作ったから分かる」で柱 B が完結。同時にリフレクション＝「証明はプログラムである」の実演として柱 B'（CH）と合流 |

この糸は notation（Ch5）→ macro（Ch10）→ elab（Ch11）の段階的メタプログラミング導入と合流する。「使う→仕組みを覗く→作る」を全タクティクについて回す。

**🪟「理論の窓」コラム系列**: 理論的深掘りは名前付きの再帰コラムとして規格化し、本線（演習）はコラムを飛ばしても通れるようにする。コラムを全部読むと型理論の入門コース半分が裏に通る二重底構造:

| 窓 | 章 |
|---|---|
| BHK 解釈 — 構成主義の意味論 | Ch1 |
| 公理と noncomputable — 実行コードの無い数 | Ch2 |
| 「存在する」をデータに格上げする — Skolem 化と公理の構造化 | Ch2–3 |
| 証明無関係性と Prop — なぜ命題の宇宙は特別か | Ch2 |
| 自然演繹と recursor — 除去則の正体 | Ch4 |
| カーネルと De Bruijn 基準 — 何を信じているのか | Ch6 |
| 正規化と `#reduce` — 証明の簡約 | Ch7 |
| 決定手続きとリフレクション | Ch11 |
| 計算的読みの終わり — noncomputable という傷跡 | Ch12 |
| FTC はどこまで構成的か — 3 つの源泉と Bishop | Ch16 |

### 公理設計の論点（Ch2–3 の本文素材、2026-06-12 議論の記録）

杉浦の教科書は実数の公理を**列挙**する（R1〜R17 スタイル）。Lean への翻訳は写経ではなく、**公理たちに構造を編集して与える行為**である——これを Ch2–3 の語りの芯とする。3 つの設計判断が同じ軸の 3 段階をなす:

| 問い | 本書の選択 | 理由 |
|---|---|---|
| 0 は「∃ 加法単位元」か、データ（フィールド）か | **データ** | ∃ は Prop 住まいで、項として名指しするには `Classical.choose` が要る（一意性は数学的安心であって取り出しの免罪符ではない）。choose は計算規則を持たず rfl / defeq が死ぬ。∃ 案では Classical.choice がほぼ全定理の公理監査に混入し「第 I 部は古典公理ゼロ」が崩壊する |
| sup は「∃ 上限」か、関数＋spec か | **関数＋spec 2 本（Skolem 化）** | 同上。証人はデータ、性質は Prop |
| 公理は 20 本の列挙か、階層クラス＋`instLOF` 1 本の束か | **束** | 論理的には同値（カリー化の関係）だが: ① 監査が 5 本で一望できる ② 「順序体とは何か」が再利用可能な概念として残る ③ 構成的実数に将来差し替えるならインスタンス 1 個の交換で済む ④ 補題の所属（`AddCommGroup.add_comm`）から「どの段の公理しか使っていないか」が読める |

共通原理: **使い回す対象には構造（データ・束）を与え、主張だけのものは Prop に残す**。`Real.instLOF` の正体（「Real 上の順序体構造一式」という 1 個のレコードを公理で名指しし、instance で正準登録する根幹の 2 行）はこの文脈で教える。noncomputable の 2 源泉の区別（設計決定 7）もここに接続する。

### 表現の選択の論点: Summation は List ではなく添字つき族（Ch4 の本文素材、2026-06-12 議論の記録）

有限和は `List Real → Real`（foldr）でも定義できる。本書が `Summation : (n : Nat) → (Range n → α) → α` を選ぶ理由と、その損得勘定ごと教材にする:

| 観点 | List Real | Range n → α（採用） |
|---|---|---|
| 長さの住所 | 値レベル（`l.length`、命題で語る） | **型レベル**（「ちょうど n 項」が型検査で保証） |
| リーマン和との噛み合わせ | ξ・points の**長さ整合命題が API 全体に伝播**（`tags.length + 1 = points.length` の運搬係になる）。隣接ペアは zip、添字を跨ぐ述語（IsRepr）が書きにくい | 3 つの族（ξ・points・length）が**同じ `i : Range n` で同期**——整合性命題が丸ごと消える |
| 帰納法 | nil/cons の構造帰納法が素直（**和の代数法則だけなら List が楽**） | Nat 帰納法＋添字の付け替え `fun k => f ⟨k.val, …⟩` が必要（本書で最も手のかかる証明パターンの一つ） |
| 教材価値 | 依存型を回避してしまう | 型 `(n : Nat) → (Range n → α) → α` 自体が**依存関数の実物**【鍵 1】。`Vector α n` との同型・Subtype の復習素材 |
| mathlib への橋 | List.sum（解析では脇役） | **Finset.sum（∑ i ∈ Finset.range n）の手作り版**——付録 C がまっすぐ架かる |

要点: **Range 版の代償＝証明項つき添字の運搬、利得＝長さの静的保証と族の同期**。和の法則だけなら List が軽く、分割と組むと逆転する。

この節と「公理設計の論点」は対をなし、第 I 部に設計思想の糸をもう 1 本通す: **形式化とは表現の選択であり、選択には型レベル / 値レベルの損得勘定がある**（証人はデータ・主張は Prop／長さは型へ・整合性命題は消す）。Ch4 で「なぜ List でないのか」コラムまたは本文の設計議論として扱う。

### Summation 補題コーパス（第 I 部の 9 本、Ch4 / Ch7 素材、2026-06-12 確定）

参照実装で下流が実際に消費する補題から逆算した、第 I 部に置く Summation の基本性質:

| 群 | 補題 | 主張 | 後の用途 | 配置 |
|---|---|---|---|---|
| 計算規則 | `summation_zero` / `summation_succ` | Σ₀ f = 0／Σₙ₊₁ f = Σₙ(f∘incl) + f(n) | 全帰納法の基底・ステップ。**証明は rfl**（定義の等式は計算で証明される——defeq の予告編） | **Ch4 末**（タクティク不要） |
| 線形性 | `additive_summation` / `summation_smul` / `neg_summation` | Σ(f+g)=Σf+Σg／Σ(c·f)=c·Σf／Σ(−f)=−Σf | → RS の additive / const / neg → 積分の線形性（**Σ→RS→積分の 3 層対応**） | Ch7（帰納法演習） |
| 順序 | `summation_nonneg` / `summation_le` | 0≤f→0≤Σf／f≤g→Σf≤Σg | → RiemannSum_nonneg / rs_bound → 単調性・sup 構成 | Ch7 |
| 横断 | `summation_congr` | (∀i, f i = g i) → Σf = Σg | ほぼ全証明で使用。**rw は束縛子の下に入れない**——その限界と congruence 補題という回避策を同時に教える（Ch7 のテーマと接続） | Ch7 |
| ボス | `telescope_sum` | Σ(g(i+1)−g(i)) = g(n)−g(0) | → `length_sum`（Σ length = b−a、const に必須）→ Ch13 `isintegral_id` の中点望遠鏡和 → 付録 B の階段原始関数。**最初の本格的帰納法証明** | Ch7 の山場 |

`sum_id`（Σi = n(n−1)/2）は cast が要るため Ch8。**意図的に第 I 部へ置かないもの**: `abs_summation_le`（abs 自体が第 II 部）・`summation_split_at` / `summation_first` 等の分割系（点挿入機械＝付録 B の部品）。`sub_summation` は additive＋neg の系として Ch9 の軽い演習に置いてよい。

### 表現の切り替えと view（2026-06-12 議論の記録）

「定義に効く表現と操作に効く表現が違う」問題への対処は 3 段の解像度で捉える:

| 解像度 | 内容 | 本書での扱い |
|---|---|---|
| 完全版（データ精錬） | 第二表現＋対応（多くは商や retraction）＋ API 全面の輸送補題。**輸送コストは定理数でなく API の面積に比例** | Partition には採用しない（輸送税 ＞ 添字地獄の削減）。概念は紹介し、mathlib の Finset（= List を商で正準化した完全版の実例）と対比 |
| **軽量版（view ＝ 導出帰納原理）** | 第二の型を作らず、**帰納原理だけを定理として増設**する（木表現の唯一の資産は帰納原理）。`Partition.split_first` / `split_at` を API 化すれば glue 流の帰納法が現行表現上でそのまま回る——商・等価性・輸送補題が全て不要 | **採用候補（P4 で付録 B 改善の選択肢として予約）**。参照実装の IntervalAdd は証明内部で手動分解しており、view の API 昇格はその整理。`induction … using` の一般論（帰納原理は型に焼き付いたものが全てではない）として Ch7 の種明かしと接続 |
| 極限形（reflection） | 操作側の表現を**計算（決定手続き）**にまで磨き、健全性定理を輸送補題とする | **Ch11 の my_ring がそのもの**——「表現切り替えの糸」の終点として明示 |

設計思想の糸に追加: **表現は増やさず view を増やす／本当に切り替えるなら輸送補題が税金／その極限が reflection**。

### 分割への操作の地図と FTC の真の依存（2026-06-12 記録、脱 abs ルート採用）

分割への操作は 4 種しかなく、消費先は正確に特定できる:

| 操作 | 実装 | 消費する定理 | 章 |
|---|---|---|---|
| ① 構成（n 等分） | equalPartition＋exists_fine_partition | 一意性・コーシー判定の有界性・単調性 | Ch8・Ch12–13 |
| ② 点の挿入 | find_interval＋insertPoint＋rs_insert_bound 系 | 細分比較（③の部品） | 付録 B |
| ③ 細分への写像 | refine_parent（σ）＋rs_refine_eq | rs_compare／abs_rs_compare → 山頂 | 付録 B |
| ④ 分解（1 点で切る） | IntervalAdd 内の手動 ΔL/ΔR 構築 | **区間加法性** → FTC の心臓部 | 付録 B |

**主線は操作フリー**（第 I 部全体・積分の定義・線形性・単調性は①のみ、しかも①は構成であって加工ではない）。操作の爆発は付録 B の 2 大機械（②③＝山頂、④＝区間加法性）に正確に封じ込められており、表現 A の選択と章構成が整合している。view（split_at）の API 化の投資先も自動的にここに決まる。

**連続⇒可積分は FTC に二重に必要**: (a) F(x) = ∫ₐˣ f の Integral は「可積分でなければ 0」のジャンク設計なので、可積分性がなければ F がそもそも目的の関数でない (b) oint_sub_interval が `∀ u v, IsIntegrable f u v` を要求（Main.lean:24 の hint）。FTC の主張が Continuous f だけを仮定する以上、導出するしかない（可積分性を仮定に置く「modulo 版」なら山頂なしで述べられる——正直な代替として序文の脚注候補）。

**【採用】脱 abs ルート**: 参照実装の FTC は `integral_triangle_ineq`（|∫g| ≤ ∫|g|）経由で `abs_integrable`（振動和機械）を引き込むが、**両側評価で代替できる**——区間上 −ε ≤ f t − f x ≤ ε から `integral_monotone` を 2 回で −εh ≤ ∫(f−fx) ≤ εh、最後に実数レベルの |·| に直すだけ。∫|g| は不要。**Text 版の main' はこのルートで書く**。帰結: Oscillation / Abs 系（|f| の可積分性・積分の三角不等式）は FTC の依存から完全に外れ、「美しいが経路外」の発展話題（付録 B の独立節）に降格。Text の主線は「定義・一意性／定数積分／線形性／単調性（両側）／区間加法性／連続⇒可積分／片側 FTC の組み立て」で閉じる（OIntegral はハイブリッド方針によりコラムへ）。

### 積分の定義の形式化（2026-06-12 確定）

**主定義は現行（Riemann／タグ付き ε-δ＋∃＋choose＋junk 全域化）を採用**。決め手: 杉浦の定義と一字一句対応・第 I 部資産（RS・TaggedPartition）が直行・3 つ目の ε-δ という縦糸の完成。検討した代替: Darboux（sup で値が直接書ける・山頂が軽くなるが、同値定理が要り教科書とずれる——Ch13 の対比素材）／等分割極限（題材変更、脚注）／フィルター（下記）／HK（「δ を関数にするだけ」コラム）／Newton（脚注）。

**choose と sup の精密な関係（Ch13 本文級）**: 本書の `Real.sup` は関数形の公理（Skolem 化済み）なので choose 不要——だが mathlib のように実数を構成すると完備性は「∃ 上限」という*定理*になり、sSup は choose で定義される。一般原理: **公理的存在は Skolem 化の自由がある。定理的存在から値を取り出すには choose しかない——ただし証明を引数に取る関数にすれば choose 無しでデータ化できる**。

**選択公理の侵入箇所の 3 層分析（Ch15 後の発展節「積分を関数として書く」として予約）**:

| 層 | 実装 | 公理 |
|---|---|---|
| 核 | `Integral f (hab : a ≤ b) (hint : IsIntegrable f a b) := Real.sup (S f a b) …`（S = 最終的に RS の下界になる値の集合——Criterion の構成の定義への昇格。hne/hbdd は hint から証明可能） | **choice ゼロ** |
| 全域化の皮 | junk 値 0 の dite | propDecidable（choice 由来） |
| 向きの皮 | OIntegral の `if a ≤ x` | 同上 |

現行定義 (a) の choice は実は 2 箇所（choose と dite の propDecidable）——Ch13 で監査の精密化として一言。

**フィルターの言葉**: 定義は ε-δ のまま、**FTC 後の発展節「フィルターで統一する」**を予約——Filter＋Tendsto を自作（50〜100 行）し、IsLimAt・Continuous・IsIntegral が同一概念の 3 インスタンスであることを同値定理 3 本の演習で示す。「3 種の ε-δ 比較」の縦糸が統一として完結し、mathlib（BoxIntegral）への橋が最短になる。

### ハイブリッド方針の確定（2026-06-12）: 片側 FTC ＋徹底脱 max/abs、公理系は現状維持

選択公理 3 源泉の分析を受けた決定。**完全構成的化（余推移的 <・Cauchy 完備性 lim・モジュラス付き連続性）は採らない**——公理系は現状（sup・古典）を維持し、構成的化の全分析（源泉 A/B/C・Bishop・ACω とモジュラス）は理論の窓「FTC はどこまで構成的か」で語る。

**源泉 A 採用——FTC の片側化**: 全域の F を作らない。主張は「u ≤ x ≤ v を跨ぐ差分商」形（(∫ᵤᵛ f) − f(x)·(v−u) の両側評価）または左右微分の対で述べる（最終形は試作時に確定）。帰結: **OIntegral と向きの場合分けが主線から消える**——区間加法性は a ≤ u ≤ v の素直な形だけで足りる。OIntegral・全域化・HasDerivAt（全域 F 前提の微分）は Ch16 のコラム**「全域化の代価」**へ（choice が買っているのは「どんな x でも」という普遍性そのものだった、という源泉 A の分析）。

**源泉 B 採用——仕様からの徹底排除**（Text の定義群は参照実装と意図的に異なる。§4.4 の方針で差分記録）:

| 対象 | 旧（参照実装） | Text の形 |
|---|---|---|
| 細かさ | `diam Δ < δ`（fmax'・max） | **`∀ i, length Δ i < δ`**（∀ 形。diam / fmax' は主線から消滅） |
| IsIntegral | `abs (RS − i) < ε` | **両側** `i − ε < RS ∧ RS < i + ε` |
| IsLimAt / Continuous | `abs (x − a) < δ` 等 | **両側** `a − δ < x ∧ x < a + δ`（＋ `x ≠ a`） |
| 評価系 | rs_abs_bound 等 | すべて両側（採用済み） |
| ε/2 合流 | `min δf δg` | **調和平均手筋 `δf·δg/(δf+δg)`**（正かつ両方以下。min を使わない合流——それ自体を小教材に） |

**「素朴に max / abs を定義するとどうなるか」は本文で記述する**（ユーザー指定、Ch12）: 読者が `max a b := if a ≤ b then b else a` を実際に書き、`Decidable (a ≤ b)` の失敗 → `Classical.propDecidable` → `noncomputable` → `#print axioms` に Classical.choice が現れる過程を観察する**実験**。「if による定義は表現の選択であり、古典性の侵入点——主線が max/abs 抜きで設計されている理由」の回収。旧設計の「Ch12 の BHK 具体物」の役割をこの実験が引き継ぐ。

主線の監査目標の更新: 第 I 部は古典公理ゼロ（従来どおり）。第 II 部は choice が入る（choose・dite の propDecidable・em）が、**侵入箇所をすべて名指しできる**ことが柱 A の到達点。

### 一意性と FTC の 2 段構造（2026-06-12 記録、試作 M1 の帰結）

**一意性の正体 ＝ ε/2 ＋ ネットの非空性**。数学的には「極限の一意性」そのもの（ε/2 は 2 行）だが、点列で無料だった「添字はいくらでも先がある」（ℕ の非有界性）が、分割ネットでは**「任意の δ より細かい分割の存在」＝アルキメデスの値段**として請求される。空なら任意の i が空虚に極限になり一意性は実際に崩れる（実例: b < a では TaggedPartition が空で IsIntegral f a b i が全 i で成立——参照実装の vacuous truth 問題そのもの）。「3 種の ε-δ は同じ形・違うのは添字集合、自明でない添字集合は非空性が定理になる」——Ch13 の本文素材に昇格。

**一意性の役割は「choose の仕様書」**: Integral レベルの値の等式（const_integral・線形性・区間加法性）はすべて橋 `integral_eq_of_isIntegral`（中身が一意性）を通る。値関数を持つこと自体の代価（Integral' の sup 版でも「sup S = 導出値」という橋＝一意性の別名が要る）。

**FTC は 2 段で書く**: ① **核（一意性フリー）**——「F が不定積分関数（∀ u v, u ≤ v → IsIntegral f u v (F v − F u)）なら連続点で F′ = f」を IsIntegral レベルの補題だけで証明（choose・一意性が現れない解析の本体）② **実体化（一意性をちょうど 1 回）**——F := Integral f a · が不定積分関数であることを橋で示す。解析と帳簿の分離が証明の構造として見える。

### 試作の完了データ（M1–M7、2026-06-12 記録）

**Text/Proto/ 全 18 ファイル・計 2979 行・sorry ゼロ・MyProject 非依存**で、公理→定義→一意性→FTC 核→4 部品→組み立て→具体例まで貫通した。ハイブリッド方針（片側 FTC・徹底脱 max/abs/min/diam・リテラル 2 不使用）は**全行程で破綻なし**。

| ファイル | 行 | 内容（マイルストーン） |
|---|---|---|
| Axioms / Numerals / Sum / Lemmas / Cast | 74+15+29+381+138 | 公理・リテラル・Σ・補題corpus・cast（M1–M4 で漸増） |
| Partition / EqualPartition / Integral | 59+77+47 | 定義一式（M1） |
| Unique / FTC / FTCCore | 80+68+226 | 一意性（M2）・statement（M3）・核 ftc_core（M4） |
| Criterion | 114 | コーシー判定・sup 構成（M5(ii)） |
| Insert / InsertBound / Refine | 207+425+415 | 挿入幾何（M5(iii)-A）・RS 挿入評価（-B）・σ 写像とエンベロープ（-C） |
| UnifCont | 307 | 一様連続性・有界性（M5(i)） |
| Main | 82 | 連続⇒可積分＋FTC 実体化（M5(iv)+M6） |
| Example | 235 | sum_id・isintegral_id・integral_id（M7） |

**公理監査の物語（そのまま Ch16 の素材になる勾配）**:

| 定理 | 監査 | 読み |
|---|---|---|
| `sum_id` | [Real, instLOF] | 帰納法と cast だけ——**古典論理ゼロ** |
| `rs_insert_bound` | +propext, Quot.sound | 命題の等値と funext 圏のみ。**choice フリー** |
| `rs_multi_insert_bound` | +choice | `find_interval`（has_min ＋ Classical.em の探索）の値段 |
| `rs_refine_eq` | +choice | **rmin（素朴 if 定義の min）が源**——素朴定義実験の実例が主線の証明装置に |
| `isintegral_id` | choice あり・**sup なし** | 「定義から直接」の可積分性は**完備性不要** |
| `continuous_unif_cont` | +sup, sup_ub, sup_lub | **sup 公理はここで初登場**（連結性論法の値段） |
| `ftc` / `integral_id` | 全公理 | 実体化（橋 = 一意性 = アルキメデス）で揃う |

**試作で得た知見（執筆時に反映）**:
1. **NearLe ツールキットが abs 三角不等式を完全に置換**: `NearLe c x y := x−c ≤ y ∧ y ≤ x+c` に nearle_trans / nearle_symm / nearle_mono / nearle_of_add、Near 側に near_trans / near_symm / near_mono / nearle_to_near。挿入評価の `2M` は `M+M`、累積は `m·((M+M)·δ)` の ∀-Fine 形で diam 不要。
2. **min の不可避点は 2 箇所だけ**: ① stepAnti（細分比較の証明装置）の rmin——素朴 if 定義で choice が監査に出る（Ch12 の実験と呼応させる）② δ の合流——こちらは `exists_min2`（le_total 場合分けで「両方以下の正数」を出す）で **min 関数なしで済む**。
3. **一様連続性は u ≤ v で成立**（参照実装の u < v より弱い仮定で通った）。有界性の鎖帰納は `NearLe k (f u) (f t)` が abs 版より素直。
4. **誤差配分の脱リテラル**: ε/4 は `ε/(1+1)/(1+1)`、`div_mul_cancel` 等で `ε'·(v−u)+θ = ε/2 < ε` を機械的に処理できる。
5. **rw の罠 2 種**（Ch7 のタクティク種明かし素材）: ① `rw [right_distrib]` が意図しない `(M+M)*δ` を先に潰す→**引数明示**で回避 ② `q = (q+q)/2` の書き換えが `(p+q)` 内の q も巻き込む（パターン捕獲）→**独立補題への切り出し**（half_dist_hi/lo）で回避。
6. **構成順の差し替え**: Proto の依存順は 公理→Σ→分割→積分→一意性→FTC文→核→判定→挿入→細分→一様連続→組み立て→具体例。第 II 部の章立て（Ch13 定義 → Ch15 山頂 → Ch16 FTC）と整合し、Ch15 の 4 部品分解は (ii)判定 ≪ (iii)細分（1047 行で最重量）≫ (i)一様連続 ≫ (iv)組み立て（82 行で最軽量）という重量配分が実測できた。

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
- **Ch1**: `1 = 1` から「証明は項」。CH 対応の 6 対応表を提示（以後の章で裏付けると予告）。素材は論理と Nat のみ。引き:「実数とは何か。公理を読みに行こう」
- **Ch2**: 署名が読めれば半分わかる。公理 5 本の精読 — `Real.sup` の「証明を引数に取り、型が項に依存する」署名。Prop vs Type から Sort 階層へ。締めに最初の実数証明: `<` の 3 兄弟（`le_of_lt`=射影 / `lt_of_le_of_ne`=構成 / `ne_of_gt`=¬は関数）——Ch1 の論理が Real に着地する。引き:「`+` や `0` はどこから来た？」
- **Ch3**: 根幹の 2 行 `axiom Real.instLOF` ＋ `instance`。リテラル `(2 : Real)` の正体。双子章前編＋ダイヤモンド事件コラム。引き:「リーマン和には Σ が要る。有限和とは何か？」
- **Ch4**: `#print Or` で種明かし — Ch1 から使ってきた ∧∨∃= も Nat もすべて帰納型。**CH 表が完結する**:「論理は依存関数と帰納型で実現できる」。その目で `Range`（証明を抱えた添字＝依存和の実物）と `Summation`（構造的再帰）を読む。引き:「分割をデータとしてどう表す？」
- **Ch5**: 証明を運ぶレコード `Partition`（双子章後編・反転演習）。**リーマン和の定義は 1 行** — この 1 行に前章までの全部が映っている。定義したらすぐ **Σ 記法とリーマン和の記法を自作**（notation 初登場）。章末、1 分割 trivialPartition（分点 a・b——リテラルも除法も不要、自明の極み）を書き始める——が、`increase` が添字の場合分けなしには書けない。**sorry が残ったまま幕**。
- **Ch6**: sorry を埋めるために。`by` とゴール状態、基本タクティク、term↔tactic の往復。種明かし: by 証明を `#print` すると λ 項が出てくる——タクティクは項を書く機械。
- **Ch7**: 等しさには 2 種類ある（`a + -b = a - b := rfl` が通るのに rw は区別する）。show・calc 設計。帰納法による証明 — summation 補題と cast 補題を獲得（Ch8 への部品）。
- **Ch8**: **sorry が消える日**。1 分割 → 2 等分（リテラル `2`、Ch3 のエラーの伏線回収）→ n 等分（**NatCast**）の 3 段を登り、cast 補題・`sum_id`・**RS = (n+1)/(2n)** へ。到達点②。
- **Ch9**: 性質 5 本の総合演習。望遠鏡和の快感、`RiemannSum_nonneg` の反例から IsRepr が必然として登場。到達点③。
- **Ch10（間奏）**: Ch6–9 で繰り返したパターン（三角不等式分解・min 分配・移項）を道具に固める。simp セット・macro 合成・ac_rfl の種明かし。
- **Ch11（発展）**: my_ring。Ch8 で手計算した代数が 1 行になる。第 I 部の幕引き:「和は手なずけた。この和は、分割を細かくしたときどこへ向かうのか——それに答えるには値をひとつ選び取る力が要る（第 II 部へ）」

### 第 I 部前半の Text 骨格設計（最短経路の確定、2026-06-11）

リーマン和の定義（到達点①）に至る Text/ の独立ソースを、ファイル単位で確定する。**計約 155 行・4 ファイルで到達点①に達する**（章とファイルは 1:1 でない——Ch3 は新ファイルを持たず C02 を素材に教える章。C06/C07 は道具章の演習集）:

| Text ファイル | 内容 | 行数目安 | 章 | 強制される Lean 機能 |
|---|---|---|---|---|
| C01_FirstProofs.lean | 論理ウォームアップ（Real 不要。1=1、∧∨→¬ の項証明、CH 表の素材） | 〜40 | Ch1 | def / fun / ⟨⟩ / 射影 |
| C02_Axioms.lean | 代数階層クラス（AddCommGroup→MulCommMonoid→CommRing→Field→LinearOrderedField、**同型＋命名改善**）＋`axiom Real`＋`axiom Real.instLOF`＋`instance`＋sup 公理 3 本＋最小インスタンス 3 つ（**OfNat 0**=Σの基底・**Sub**=length・**LT**=≤∧≠）＋締めに `<` の 3 兄弟（最初の実数証明） | 〜60 | Ch2 精読・Ch3 素材 | 署名読解・依存型・class（読み） |
| C04_Summation.lean | `Range`（Subtype）・`incl` / `addone`・`Summation` | 〜25 | Ch4 | 帰納型・Subtype・構造的再帰 |
| C05_RiemannSum.lean | `structure Partition`・`length`・`RiemannSum`・Σ / RS 記法・**1 分割（trivialPartition）**の骨格（分点 a・b のみ。リテラル・除法とも不要。フィールド sorry＝クリフハンガー） | 〜30 | Ch5 | structure・notation |

設計決定:

1. **公理はフル契約**: Ch2 で 5 本全部（sup 込み）を提示する。sup は RS に不要だが依存型の決定的標本であり、「公理 5 本」が本のアイデンティティ。**最小性の実験**を演習化する:「sup 公理 3 行を消しても C05 まではコンパイルする——RS の定義が実際に使うのは + · × · − · 0 · ≤ だけ」（不要な公理を仮定しない、という形式化の感覚を養う）。
2. **階層は参照実装と同型＋命名改善**: 同じ 5 段 extends 連鎖（双子章・階層設計の教材価値）。ただし独立コードの利点で命名のワートを修正——誤名 `LinearOrderedField.mul_pos`（実態は nonneg）→ `mul_nonneg` 等。参照実装との差分は §4.4 の方針どおり記録する。
3. **派生インスタンス（Min / Max / Abs / NonNeg 等）は Ch2 に含めない**: 必要になった章で読者が定義する演習に（例: Ch9 で「abs を max で定義せよ」）。需要駆動の原則と一貫。
4. 「RS の定義に入り込む証明は添字の Nat 不等式の項埋めのみ」（2 幕構成の根拠）は、この骨格を実際にビルドすることでコードとして検証する。骨格執筆時の検証: `lake build Text` 成功（sorry は 2 等分の意図的なもののみ）＋ sup 公理をコメントアウトしても C05 がビルドできることの確認。
5. **数の段階導入（リテラルも NatCast も後回し）**: RS の定義に要る Real のリテラルは `0` ただ 1 つ（Σ の基底）。リテラル機構（OfNat 1・(n+2)・`Real.ofNat`）と変数埋め込み（NatCast）はすべて Ch8 へ。**Ch5 のクリフハンガーは 1 分割（trivialPartition）**——リテラルも除法も不要で、「自明の極み」の increase すら添字の場合分けなしには書けない。**Ch8 は 3 段の梯子**: 1 分割完成（Ch6–7 の道具の最初の獲物）→ 2 等分（リテラル 2＝OfNat 物語の回収・除法の初使用）→ n 等分（NatCast・cast 補題・`sum_id`）。数の導入（0 → リテラル → 埋め込み）と分割の一般化（1 → 2 → n）が並走する。Ch3 では `#check (2 : Real)` が**エラーになること**（failed to synthesize OfNat Real 2）をインスタンス解決の実演に使い、Ch8 で回収する伏線とする。
6. **abs / max / min / diam は第 II 部へ**（第 I 部の構成性を守る）: 実数の `max` は `if a ≤ b` を要し、≤ の分岐には `Classical.propDecidable` が要る——abs を Ch9 に置くと「第 I 部は構成的」が静かに破れる。よって Ch9 の第 5 性質は**両側評価 `rs_bound`: −M(b−a) ≤ RS ∧ RS ≤ M(b−a)** に言い換える（後段の sup 構成が消費するのはこの形なので数学的損失ゼロ）。「実数の max / abs は場合分けすら noncomputable」は **Ch12 の素朴定義実験**（ハイブリッド方針の節を参照）として活きる。第 I 部（Ch1–9）は**古典公理ゼロ**——章ごとに `#print axioms` で構成的であることすら監査できる。
7. **noncomputable の 2 つの源泉を区別して教える**: (i) 公理的 Real に実行コードが無いこと（Ch2 から `noncomputable` が必要になる理由——正直な表示）と (ii) 証明・分岐レベルの古典原理（propDecidable・choice、Ch12）。理論の窓に「公理と noncomputable」（Ch2）を追加。
8. **Ch8 肥大の監視点**: 梯子 3 段＋OfNat 物語＋NatCast＋cast 補題＋`sum_id`＋RS 計算は 1 章として重い。執筆時に 2 分割（分割の梯子 / y=x の計算）の可能性を予約。

### 貫通する具体例: y = x の [0,1] n 等分（Ch8 → Ch13 をまたぐ物語）

**n 等分の表現方針**: 自然数を Real の部分集合として構成する必要はない。型理論の正道は「`Nat`（帰納型）からの埋め込み」であり、本体に実装済み（`Real.ofNat` の構造的再帰・`NatCast` インスタンス・cast 補題群・`equalPartition` の分点 `a + i·(b−a)/m`）。代替案 2 つも素材として回収する:

- **杉浦流「最小の継承的集合」**は Prop の非可述性で 1 行で書ける（`InductiveSet x := ∀ S : Real → Prop, S 0 → (∀ y, S y → S (y+1)) → S x`）。これが cast の像述語 `fun x => ∃ n : Nat, x = ↑n`（**archimedean の証明に既出**）と同値であることを Ch12 のコラム＋発展演習にする — Ch2 の universe（Prop への量化）の生きた応用であり、原典（杉浦）との接続点。
- **「n·x = 1 の解」**は独立の構成にはならない（n 回足すことを述べるのに Nat が要る）が、「順序体では 0 < n·1、ゆえに標数 0 で 1/n が存在」は本体の実定理（`cast_pos_succ`）。「1/n は n·x = 1 の唯一解」を小演習にする。

**Ch8 名物演習**: `equalPartition n 0 1` の分点が `i/n` であることの確認（show の練習）→ 新補題 `sum_id : Summation n (fun i => (i.val : Real)) = n(n−1)/2` を帰納法＋cast 計算で証明（旧 NatNum.lean に sorry 付きで眠っていた式の回収）→ 右端タグで **RS = (n+1)/(2n)**、左端タグで (n−1)/(2n)。

**Ch13 誘導演習**: f = id は「定義から直接」可積分性を示せる稀有な例。中点和が望遠鏡和になり（Σ midᵢ·lenᵢ = (b²−a²)/2）、任意のタグで |ξᵢ − midᵢ| ≤ diam/2 だから **|RS − (b²−a²)/2| ≤ diam·(b−a)/2** — よって `IsIntegral id a b ((b²−a²)/2)`。`integral_unique` で Ch8 の「n 等分の極限 (n+1)/2n → 1/2」と「∫₀¹ x = 1/2」が繋がり、具体例が 2 部をまたいで閉じる。

必要な本体追加（P4 で開発）: `sum_id`（Real/Summation.lean）・`isintegral_id`（Integral/ 配下、中点望遠鏡和の補題込み）・Σ / リーマン和 / ∫ の記法。

### 【v1 素材庫】第 II 部 リーマン積分（旧 Ch12–16）

| 章 | 数学の歩み | Lean 機能・教材要素 |
|---|---|---|
| Ch12 | 選び取る力 — 分割の存在と値の取り出し | **古典論理と choice**（`Classical.em` / `by_cases` / `choose` / `noncomputable`、**構成的だった第 I 部との対比**で導入）。🪟 **BHK の転調**: 証明・分岐レベルで古典原理が入る（noncomputable の第 2 の源泉）。**素朴定義実験**: `max a b := if a ≤ b then b else a` を書いてみて、propDecidable → noncomputable → 監査に choice が現れるのを観察（主線が max/abs 抜きである理由の回収。Ch9 の両側評価が abs の言い換えだったことも）。`min`（Nat 述語の最小値）・ceil・sup_near・**archimedean**（白眉①）・exists_fine_partition。コラム＋発展演習: 杉浦流「最小の継承的集合」との同値 |
| Ch13 | **リーマン積分の定義**＝網目の極限・well-definedness | 3 種の ε-δ 比較（IsLimAt / Continuous / IsIntegral——いずれも **abs-free の両側形**）・細かさは **∀ 形**（diam を使わない）・`TaggedPartition`・`dite`＋choose・`integral_unique`。**∫ 記法を定義した直後に自作**（Ch5 の再演）。誘導演習: `IsIntegral id`（貫通具体例がここで閉じる、両側評価で） |
| Ch14 | 積分の性質 ＝ **Ch9 の 5 性質の ε/2 持ち上げ**（対応表が章の構造） | `min δf δg` 定石・isintegral_add（最純形）。演習: ε/2 定石を macro に固める（Ch10 の応用） |
| Ch15 | **山頂: 連続 ⇒ 可積分**（4 部品分解） | 大規模証明のアーキテクチャ（private・section・import DAG）。(ii) integrable_of_cauchy 精読＋ sup 構成 4 ブロック誘導演習・(iv) continuous_integrable 完全精読・(i)(iii) は statement 精読＋付録 |
| Ch16 | **片側 FTC**（u ≤ x ≤ v 跨ぎ形 or 左右微分の対、全域 F を作らない） | `#print axioms` 監査の意味（choice の侵入箇所を全部名指しする）。コラム: **「全域化の代価」**（OIntegral・HasDerivAt——choice が買うのは普遍性、源泉 A の分析）・`propext` / `Quot.sound` / `Classical.choice` とは何か |

### 自動化の編み込み（独立の「第 III 部」は置かない）

自動化は **Ch5（Σ・リーマン和の記法）→ Ch10（間奏: simp セット・macro 合成）→ Ch11（発展: my_ring）→ Ch13（∫ 記法の再演）→ Ch14（ε/2 macro 演習）** と本編に編み込む。「作った道具を以後の章で使う」ループが本の中で回り、学習曲線も notation（数行）→ macro 合成（中）→ リフレクション（重）の 3 段に分散される。

- 演習で自作タクティクを許す際は「**模範解答（本体）は手書き。自作道具は加速装置**」と明記し、本体=模範解答の原則を保つ。
- 素材コード `MyProject/Tactic/`（合成タクティク・`MyRing.lean`）と本体への記法追加は P4 で開発（背骨の import 鎖には不干渉）。
- **my_ring 設計方針**: 可換環の項を Nat 係数多項式の正規形（ソート済み単項式リスト）に正規化し、`DecidableEq` で正規形を比較。健全性 `eval ρ e = eval ρ (norm e)` を帰納法で証明し、タクティクは「reify → 健全性適用 → `decide` / `rfl`」。

### 付録

- 付録 A: 一様連続性を読む（UniformContinuity — Ch15 部品 (i) の全証明）
- 付録 B: 細分・区間加法性（Insert / Refine / IntervalAdd — Ch15 部品 (iii) と FTC の④分解）。独立節として振動和（Oscillation / Abs — **脱 abs ルート採用により FTC 非依存の発展話題**: |f| の可積分性・積分の三角不等式）
- 付録 C: mathlib への橋（本書の各概念の mathlib 対応表。MIL を次の一冊として推薦）

## 4. テキスト用コードと演習の機構

### 4.1 大原則: テキスト用ソースは独立（2026-06-11 決定）

教材の Lean ソースは **`Text/` 配下に置き、`MyProject` を import しない**。教材で構築する世界（公理・Range・Summation・Partition・RiemannSum・積分…）は読者と共にゼロから書き、Text 内で自己完結させる。

- **`MyProject/` の役割は「参照実装」に変わる**: FTC が本当に sorry ゼロで証明できることの保証（`#print axioms` 監査つき）であり、教材の設計・証明の出典。本文から「完全版は `MyProject/...` 参照」とリンクする。
- 利点: 教材コードを章の進行に最適な順序・命名・粒度で書ける（参照実装の歴史的事情から自由）。教材の改良が本体を壊さない・逆も然り。
- 旧設計の「ミラー＋上流 import のみ規則・本体=模範解答」は廃止。

### 4.2 配置とビルド

```
Text/
  README.md        — 構成と執筆規約
  book/            — 原稿（mdBook、§5）
  C01_*.lean …     — 章ごとのテキスト用ソース（演習 sorry を本文中に埋め込み）
Text.lean          — umbrella
```

lakefile（実装済み）: `lean_lib «Text»`（デフォルトビルド対象外）。通常の `lake build` は警告ゼロを維持し、教材は `lake build Text` でビルドする。読者の検証は ① VS Code で sorry を埋めて波線が消える（主経路）② `lake build Text.C05_Structure` の章単位 ③ 全完了後 `lake build Text` が sorry 警告ゼロ。

### 4.3 演習と解答

演習は MIL 方式（本文中に随時 sorry）。模範解答は各章ファイル末尾の `namespace Solutions` または `Text/Solutions/` 配下に置く（独立方式では本体が解答を兼ねないため、解答は Text 内に明示的に持つ）。

### 4.4 参照実装との整合

Text のコードは MyProject の定義と意図的に同型（命名・引数順は教材都合で変えてよい）。大きな乖離が出た場合は docs/textbook_plan.md に差分の理由を記録する。機械的なドリフト検査は独立方式では不要になったが、`lake build Text` 自体が常時の検証になる。

## 5. book/ 原稿の規約

- **mdBook** 構成: `Text/book/book.toml`＋`Text/book/src/SUMMARY.md`＋章ごとの md（骨格は作成済み）
- **コード引用は手書きコピペ禁止**。本体・演習の .lean に ANCHOR コメントを入れ、`{{#include ../../C05_Structure.lean:riemann_sum}}` 方式で **Text/ の実ファイル**から抜粋する。ビルド対象の実コードが唯一の出典となり、コード改修と原稿が自動同期する
- 各章冒頭に「より深く: TPiL ch.X / MIL ch.Y」参照ボックス

## 6. 作業フェーズと完了条件

| フェーズ | 内容 | 完了条件 |
|---|---|---|
| **P1 toolchain 更新** | `lean-toolchain` を最新安定版へ。先に Range.lean の無名 `WellFoundedRelation` インスタンスに明示名を付けてから更新（自動生成名 `Range.instWellFoundedRelation` への直接参照が壊れやすいため）。コア Nat 補題のリネーム等はエラー駆動で修正 | `lake build` 警告ゼロ・`#print axioms main` が公理 5 本＋標準 3 本のまま |
| **P2 教材向け本体改修** | ① Range.lean の `has_min` を技巧的な形から素直な `Nat.strongRecOn` 適用形へ書き直し（Ch12 の教材対象）② Integral/Def.lean の private キャスト系ヘルパー（my_cast_nonneg / cast_le_succ / nat_ne_zero_of_nonneg_lt / cast_pos_of_ne）を Real/Cast.lean へ公開移動（参照実装の可読性向上）③ Continuity.lean を 2 分割（Continuous 定義＋continuous_sub/const = Ch13 と、UniformContinuity.lean = 付録 A）④ 命名修正: `IsIntegral_iff` → `integral_eq_of_isIntegral`、Real/Algebra.lean のプライム混在エイリアス一本化 ⑤ 清掃: 未使用 typo クラス `CompletLinearOrderedField`、`#check` 残骸等 ⑥ 背骨の主要定義に doc comment | ビルド・公理監査グリーン |
| **P3 教材基盤** | Text/ 雛形＋lakefile の `lean_lib «Text»`（実施済み 2026-06-11）。続き: 章ソースの実作開始（C01〜）・book/ 章スタブ・README を教材リポジトリとして更新 | `lake build` 警告ゼロ・`lake build Text` がビルド可能 |
| **P4 章執筆ループ** | 章ごとに「演習作成 → 自力 1 周で難度調整 → 原稿 md 執筆（include 配線）→ ドリフト検査」。推奨順: 第 I 部の背骨 Ch3〜9 → 第 II 部 Ch12〜16 → Ch1・2 → Ch10・11（`MyProject/Tactic/` 開発含む）→ Ch0 → 付録 | 各章: 演習が sorry 以外で警告ゼロ・原稿ビルド成功 |
| **P5 公開** | 公開先決定（Zenn / GitHub Pages）、deploy 整備、Ch0 に導線 | 公開 URL で全章閲覧可・clone から演習着手まで 10 分以内 |

## 7. 既存教材との関係・参考文献

- **Theorem Proving in Lean 4**（Avigad, de Moura, Kong, Ullrich）: 概念順（DTT → 命題と証明 → 量化子 → Tactics → … → 帰納型 → 構造体 → 型クラス → 公理と計算）は本書第 I 部とほぼ整合。差分は ① 型クラスの前倒し（Ch3、Axioms.lean 読解に必須）② TPiL ch6「Interacting with Lean」（namespace / section / open）は Ch2 に吸収 ③ conv は不使用のため扱わない。トピックの過不足はこの 3 点で説明できることを確認済み
- **Mathematics in Lean**（Avigad, Massot）: 演習方式（リポジトリ clone・本文中に随時 sorry・解答同梱）を採用。ただし MIL の ring / linarith 等の自動化は本書では不使用——「MIL が自動化に任せる部分を全て手で組み、その自動化を本編の中で自作して以後の章で使う」が本書の差別化
- **The Mechanics of Proof**（Macbeth）: 制限タクティクセットで数学を教える方針が近い。序章の文献案内に含める
- **Metaprogramming in Lean 4**（Paulino 他）: 自動化章（Ch5 の notation・Ch10・Ch11）の「より深く」の参照先
- **差別化の検証（柱 B の空白地帯）**: TPiL4 は CH を扱うがトイ例でタクティク内部は扱わない。MIL はタクティクを意図的にブラックボックスにする設計。Metaprogramming in Lean 4 は内部そのものだが入門書でなく数学もない。Mechanics of Proof はタクティクを制限するが開けない。「**入門書でありながらタクティクを開け、数学者向けに CH 対応を理論（BHK・自然演繹）ごと、本物の数学（FTC）の上で**」という組み合わせは空白地帯であり、序章で明示する本書の存在意義
