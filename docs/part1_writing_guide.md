# 前半（序章〜Ch12）執筆ガイド＆レビュー基準

リーマン和を**定義し、基本性質を証明するまで**（序章〜Ch12）の本文執筆フェーズの単一参照。
設計書 `docs/textbook_plan.md` の散在する方針を前半に絞って統合し、レビューの照合基準を明文化する。
詳細の再導出はせず、必要に応じて設計書の該当節へポインタする。

> 関連: 構成 v4（2026-06-15）= 本編 第 I 部 Ch0–12／第 II 部 Ch13–17（FTC は Ch17）／発展部 E1–E5／付録 C・D。
> 本ガイドは **Ch0–Ch12**（第 I 部＝リーマン和の定義〜性質。証明の弧は Ch6 タクティク入門／
> Ch7 書き換えと2つの等しさ／Ch8 自動化と自作タクティク／Ch9 順序と calc／Ch10 帰納法の単一テーマ 5 章）を扱う。

---

## 1. 役割分担とワークフロー

- **ユーザー（執筆）**: `Text/book/src/chNN_*.md` の配置メモを土台に散文を展開する。
- **私（レビュー＆方針管理）**: 各章ドラフトを §4 の不変条件で照合し、次を指摘する——
  早すぎる機能初出／縦糸の張り忘れ・回収漏れ／引きの欠落／コード引用の誤り／監査主張の未検証。
- **今回スコープ外（P4 へ）**: 演習の sorry 化＋`Solutions` 分離・`#include` ANCHOR 配線・mdbook 導入・
  第 II 部・発展部。

執筆の単位はコードではなく散文。コード（C01–C12）は完成・ビルド通過済みで、原稿はそれを ANCHOR 引用する。

---

## 2. 共通方針の要点

| 項目 | 要点 | 設計書の該当節 |
|---|---|---|
| 読者像・トーン | 数学既知（ε-δ・上限公理・リーマン積分）／Lean ゼロ。数学説明は最小、紙面は Lean 固有概念に集中 | 「2. 読者と方針」 |
| 2 幕構成 | 幕1 序章〜Ch5＝**定義の幕**（書く・証明は少量の term のみ）／幕2 Ch6〜Ch12＝**証明の幕**（道具を獲得→sorry を埋める→具体例・性質に至る）。証明の弧（Ch6–10）は単一テーマ 5 章: タクティク入門／書き換えと2つの等しさ／自動化と自作タクティク／順序と calc／帰納法 | 「第 I 部のストーリー」 |
| 3 到達点 | ① 定義が書ける（Ch5）② 具体例が計算できる（Ch11）③ 性質 5 本が証明できる（Ch12） | 同上 |
| 🪟 理論の窓 | 理論的深掘りは名前付きコラムに隔離。**飛ばしても本線（演習）が通る二重底**。前半の窓: BHK(Ch1)・公理と noncomputable(Ch3)・証明無関係性と Prop(Ch3)・自然演繹と recursor(Ch4)・カーネルと De Bruijn(Ch6)・正規化と #reduce(Ch7)・simp と書き換え系(Ch8) | 「縦断スレッド」 |
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
- 到達点: clone → 演習着手 10 分・3 道具を知る・**docstring を読める**
- 新機能: `#check`／`#print`／`#print axioms`（監査文化の起点）・**docstring `/-- -/`**（2026-06-15 ここで導入）
- ▲監査 3 道具（§4e の起点）・▲**docstring**（読む側の道具・1 段落。`--` との違い・hover/#check/#print に出る・本書の Text/ は docstring 付き。書く側の習慣は C01 以降で自然に・`/-! -/` は一言）
- 引き: Ch1 へ「ゴール表示の `⊢` とは何か」
- ⚠ Ch0 は自前コードなし。docstring は既存コード（MyProject や Text/）に hover して見せる

### Ch1 — 最初の証明（`ch01_term.md`、C01）
- 問い: `⊢` とは何か
- 到達点: 命題論理の証明を**項**として手書きできる・**等式を calc で繋げる**（Real 不要・タクティク不要・term mode）
- 新機能: 命題=型・証明=項（term mode）・`fun`・`⟨⟩`・射影・**calc（等式の連鎖・term mode）**（2026-06-15 Ch7 から前出し）
- ANCHOR: `my_first_theorem`・`and_swap`・`calc_warmup`・`nat_interchange`
- ▲CH 対応 6 表を提示・🪟BHK 解釈・▲**calc で等式証明**（`nat_interchange` ＝ Ch2 抽象版の具体先取り）
- 演習候補: `and_assoc'`・`and_or_distrib`・`imp_trans`・`double_neg_intro`・**乗法版 interchange を calc で**（`Solutions.nat_interchange_mul` に解答）
- 引き: Ch2 へ「`+` の式は繋げた。`×` でも繰り返すのか？——実数とは何か・式の繰り返しをどう束ねるか＝『構造』」
- ⚠ calc は **term mode**（`by` を使わない）。`by`=tactic mode は Ch6・`≤`/`<` 混在の calc と Trans は Ch7（ここは `=` の calc だけ）

### Ch2 — 数学的構造と class の仕組み（`ch02_structures.md`、C02_Structures）※2026-06-15 スワップ
- 問い: 実数とは何か（→ 実数は「構造」で与えられる。まず構造を掴む）
- 到達点: 「構造＝データ・class＝自動で見つかる構造」の見方・一般構造で 1 回証明して複数インスタンスに適用する経験
- 新機能: **structure キーワード**・署名の読み方・暗黙引数（**読む**）・**class（最小: 自動解決される構造）**
- ANCHOR: `structure_as_data`・`general_proof`・`local_notation`・`and_is_structure`
- ビート: ① 型=集合(carrier)・構造=データ（Ch1 の `⟨h.2,h.1⟩` の大きい版・`structure` キーワード）② `structure_as_data`（`Add Nat` の住人 2 つ・Add は法則を持たない→階層がある動機）③ **`general_proof`**（`CommMonoidStr`＋交換則を assoc/comm だけで証明＝**Ch1 `nat_interchange` の抽象版**・calc 既出で読める→`natAdd`/`natMul` に適用・`+`/`*` に defeq 一致＝抽象化の威力・乗法版の直接労力が無料に）④ `local_notation`（固定構造に記法 `⋆` は当てられる・だが多相 `+` は不可→class の動機・L39 回収）⑤ class 最小導入（自動で見つかる構造）⑥ `and_is_structure`（`#print And`・Ch1 の `⟨⟩` の正体）
- ▲structure＝データの視点・▲抽象化（1 回証明→多数適用）・▲class の最小概念
- 演習候補: `Add Nat` の住人をもう 1 つ・`CommMonoidStr` の別インスタンス・`n` を implicit に（Ch4 への布石）
- 引き: Ch3 へ「道具は揃った。実数の公理を読もう——それは『構造』として書かれている」
- ⚠ **制約**: ℝ は `class` のまま（`a+b` 記法）。教材の例（`general_proof`）は素の `structure`＋explicit で完結（`def` 可・警告ゼロ・instance 不要）
- ⚠ **境界**: 概念＝Ch2／class の**深い機構**（解決・`(2:Real)` 観察）＝Ch3 の軽い回・**diamond と排他分割＝Ch8**。`structure` キーワードは Ch2（Ch5 から前出し）・Ch5 は structure を Partition に適用＋設計判断
- ⚠ **class は最小限**: 「自動で見つかる structure」だけ。解決の仕組み・diamond は後章

### Ch3 — 実数を公理で読む（`ch03_axioms.md`、C03_Axioms）※2026-06-15 スワップ
- 問い: 道具（構造と class）は揃った。実数の公理をどう読むか
- 到達点: C03_Axioms の全行が**読める**・最初の実数証明
- 新機能: **依存型【鍵1】**・∀/∃=Π/Σ・**Prop vs Type・universe【鍵2】**・`axiom`・namespace/open
- ANCHOR: `hierarchy`・`axioms`・`zero_bridge`・`check_failure`・`three_brothers`
- ▲依存型・universe を正面で（Real.sup の署名）・▼CH 表の ∀∃ 行を裏付け・🪟公理と noncomputable・🪟証明無関係性と Prop・🪟存在をデータに格上げ
- ビート: 階層を読む（Ch2 の構造観で）・公理 5 本・**Real.sup の署名＝依存型**（∃ vs データの本格議論＝Ch2 予告の回収）・Prop/universe・根幹 2 行（class＝自動解決の実物）・check_failure（今 ℝ は 0 のみ→`(1/2:Real)` は失敗・Ch6/Ch8 伏線）・`<` の 3 兄弟
- 演習候補: 署名読解ドリル・`<` の 3 兄弟の変種・**sup 最小性実験**（sup 3 行を消しても C05 までビルドが通る）
- 引き: Ch4 へ「リーマン和には Σ が要る。有限和とは何か？」
- ⚠ noncomputable の源泉①（公理に実行コードがない）をここで正直に説明・公理設計の論点（0=データ・sup=Skolem・束）
- ⚠ check_failure は「0 だけの世界」（リテラル 1・2 がまだ無い）で成立。深い解決機構・diamond は Ch8 へ

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
- 到達点: **リーマン和の定義が書ける**（到達点①）・代表点の妥当性 `IsRepr` も定義・ただし sorry が 1 つ残って幕
- 新機能: structure（双子章・後編）・notation 自作・暗黙引数（**書く**: `length {n}{a b}`）
- ANCHOR: `partition`・`riemann_sum`・**`is_repr`**・**`endpoint_repr`**・`trivial_partition`
- ▼`And` も structure だった（`#print And`・Ch1 の `⟨⟩` 回収）・▲notation 初登場（自動化糸の起点）・▲**IsRepr**（代表点の妥当性＝タグは小区間内・RS は任意 ξ で計算できるが「リーマン和」と呼ぶには妥当なタグを課す）・▲**leftRepr/rightRepr**（代表点を左端・右端に取るのは**任意の Partition で一般化**できる・IsRepr が自明に成立）・▲trivialPartition の sorry クリフハンガー（Ch8 で回収）
- 演習候補: 反転演習（Partition を class にすると IsIntegral が書けない／LOF を structure にすると `a+b` のたびに名指し）
- 引き: Ch6 へ「定義はできた。sorry を埋める道具が要る」
- ⚠ **IsRepr はここで定義**（2026-06-15 移動・C09 から）——代表点は概念の一部。効く場面（性質4・非負）と「落とすと壊れる」反例は Ch9。TaggedPartition（束ねた版）は Ch12。RS の定義 1 行に前章までの全部が映る、を体感させる

> 証明の弧（Ch6–10）は 2026-06-15 に単一テーマ 5 章へ再分割（旧 C06 肥大＝独立 3 テーマの解消・自動化を前倒し）。各章は短く 1 テーマ。

### Ch6 — タクティク入門（`ch06_tactic.md`、C06_Tactics）
- 問い: 残った sorry をどう埋めるか
- 到達点: 基本タクティクで短い証明・「なぜタクティクで証明になるか（項を書く機械）」に答えられる
- 新機能: `by`・ゴール状態・intro/exact/apply/have/show・term↔tactic の往復・**One bridge**
- ANCHOR: （未付与——§5 参照）
- ▲種明かしの糸の起点（カーネル/De Bruijn・タクティクは項を書く機械）・▼apply=メタ変数＋単一化（`_`も暗黙引数も同じ穴・Ch2/3 と接続）・🪟カーネルと De Bruijn 基準・▲trivialPartition.increase の sorry を埋める（道具の初仕事）・公理射影を term で（add_neg' 等＝1 行）＋ add_left_cancel'（次章の足場）
- 演習候補: trivialPartition.increase を自分で・公理射影を term と tactic 両方で
- 引き: Ch7 へ「rw が効くとき効かないとき。等しさは 2 種類？」
- ⚠ ここは機構と信頼が主題。等式コーパス本体は Ch7・順序は Ch9

### Ch7 — 書き換えと 2 つの等しさ（`ch07_rewrite.md`、C07_Rewrite）
- 問い: 等しさには 2 種類あるのか
- 到達点: defeq（計算で同じ）と構文的等しさ（rw が見る）を区別・群環の等式コーパスを rw/calc で獲得
- 新機能: rw・defeq と rfl/show・`▸`（`=` の calc は Ch1）
- ANCHOR: （未付与——特定の補題証明を引用する段で。§5）
- ▼rw=Eq.mpr＋motive（種明かし）・**rw の罠 2 種**（引数明示・独立補題への切り出し）・▲「sub は a + -b」＝defeq の実感・🪟正規化と #reduce・▲**等式コーパス**（mul_zero'・neg_neg・neg_mul・mul_sub・引き算の整理・telescope_2＝Ch10 望遠鏡和の部品・add_half_sub_full＝E 部）
- 演習候補: 等式ドリル（neg_neg・mul_sub・add_sub_cancel 等）・rfl が通るか #check_failure で判定
- 引き: Ch8 へ「等式を 1 本ずつ手で。同じパターンを機械に任せられないか」

### Ch8 — 自動化と自作タクティク（`ch08_automation.md`、C08_Automation）※2026-06-15 旧 Ch10 間奏を前倒し・本章化＋反射 my_abel/my_ring 実装
- 問い: 繰り返した等式の証明パターンを道具にできないか
- 到達点: バニラ（simp/omega/ac_rfl）を押さえ、**自分の公理から proof by reflection で my_abel（加法群）・my_ring（環）を自作**できる。以後の章で使える
- 新機能: simp / simp only・omega・**ac_rfl**（Std.Associative/Commutative）・**メタプログラミング**（inductive 構文・elab・isDefEq・mkDecideProof による反射）
- ANCHOR: `simp_demo`・`omega_demo`・`ac_demo`・**`my_abel_demo`**・**`my_ring_demo`**
- 🪟simp＝停止する有向書き換え（限界: 並べ替え＋相殺は不可・実測）・▲ac_rfl はインスタンスを食べる（逆元相殺は不可）・▲**proof by reflection の三幕**（構文 Expr＋eval ／ normalize＋健全性 eval e=nfEval(normalize e) ／ メタで反射＋decide）・▲**my_abel**（正規形＝符号付き原子の整列リスト・相殺は add_neg'/neg_add'）→**my_ring**（原子→単項式・分配 crossMul・my_abel を包含）・▲applySign/xnorB をパターンマッチ定義にして defeq を通すメタの工夫
- 演習候補: simp で閉じる/閉じない命題の判定・my_abel/my_ring を別の恒等式に・reify に新しい演算を足す
- 引き: Ch9 へ「等式は反射で畳めた。順序（≤/<）はどう自動化するか——順序のみ／順序体の道具を比べる」
- ⚠ mathlib の ring/abel/linarith は**無い**（unknown tactic・実測）ので全部自作。register_simp_attr も当 core で不可。全デモは実ビルドで通す（机上禁止）。「本体=模範解答・自作道具は加速装置」の運用を明記。反射の一般化（多項式正規形）と mathlib 対応は付録 C/D

### Ch9 — 順序と calc（`ch09_order.md`、C09_Order）※2026-06-15 旧 C06 の順序コーパスを独立章化
- 問い: 等式は畳めた。順序の補題はどう獲得し、どう鎖にするか
- 到達点: 順序コーパスを獲得・**`≤`/`<` 混在の calc を設計できる**（Trans）
- 新機能: **calc の深掘り（`≤`/`<` 混在・Trans）**（`=` の calc は Ch1・rw は Ch7・simp は Ch8）
- ANCHOR: （未付与——§5）
- ▲公理から順序基本（le_refl/trans/antisymm/total・add_le_add＝1 行 term 射影・Ch3 の「公理は定理」の本格展開）・▲Trans＝calc の機構（種明かし回収）・▲加法と順序・移項の小物（両側評価の部品）・▲乗法順序（mul_nonneg・**zero_lt_one は定理**＝nontrivial・pos_inv）
- 演習候補: 順序ドリル（nonneg_iff_le・neg_le_neg'・sub_lt_swap）・混在 calc を 1 本設計
- 引き: Ch10 へ「スカラーの代数は揃った。Σ（有限和）の性質は項数 n の帰納法が要る」
- ⚠ 順序コーパスは等式（Ch6/7）の後・simp/my_ring（Ch8）で等式変形の段を畳める・リテラル 2 は無いので `1+1`・古典補題は第 II 部

### Ch10 — 帰納法（`ch10_induction.md`、C10_Induction）※2026-06-15 旧「defeq・帰納法」から defeq を Ch7 へ分離
- 問い: スカラーの代数は揃った。Σ の性質は帰納法が要る
- 到達点: 帰納法で Σ 補題コーパス＋**Partition の大域単調性**が証明できる
- 新機能: **induction**（rfl/show は Ch7・omega は Ch8 既出）
- ANCHOR: `vector_space`・`summation_linear`（脇道）。Partition 幾何（points_mono 等）は ANCHOR 未付与（§5）
- ▼induction=recursor 適用（Ch4 回収）・▲Σ コーパス（添字の付け替え `fun k => f ⟨k.val,…⟩`＝最も手のかかるパターン・順序評価は Ch9 を呼ぶ・等式段は Ch8 simp で畳む）・▲ボス戦 telescope_sum（Ch7 telescope_2 が部品）・▲**Partition 基本性質**（`points_mono`＝大域単調を induction で・left/right_le_point・tag_mem'＝読者自身の構造への帰納法の実地）・脇道「Σ は線形形式」・`sum_id_nat`
- 演習候補: コーパス 9 本の sorry 埋め・脇道「Σ は線形形式」・`points_mono` を induction で・`sum_id_nat`
- 引き: Ch11 へ「道具は揃った。Ch5 の sorry を消して 2 等分・n 等分へ」
- ⚠ telescope_sum がボス戦（Ch12 length_sum と Ch16 中点和の部品）。幾何の証明は order 補題（`nonneg_iff_le` 等＝**Ch9**）を使う

### Ch11 — 具体例 y=x の n 等分（`ch11_example.md`、C11_Numbers・到達点②）
- 問い: sorry を消し、具体例を計算する
- 到達点: equalPartition 上の RS=(n+1)/(2n)（到達点②）
- 新機能: OfNat 物語の回収・`Real.ofNat`（構造的再帰）・NatCast・Div・cast 補題・**cast は射（準同型）**
- ANCHOR: `of_nat`・`equal_partition`・`cast_defeq`・**`cast_hom`**（`sum_id` は C10 へ移動）
- ▼`(2:Real)` エラー回収（Ch3）・▼trivialPartition の sorry 消える（Ch5）・▲菱形の排他分割（0/1/2 以上＝AtLeastTwo 手作り）・**defeq 観察**・▲**cast は構造を保つ射**（`IsNatHom`＝0/1/+/×/≤ を保つ準同型・`cast_isHom`・`cast_summation`＝Σ と可換。Ch10 の `IsLinearMap` と並ぶ「射」の述語）
- ▲**一般の等分割を先に**: cast 補題（射）→ 一般の `equalPartition`・`length`・代表点（C05 の一般 `leftRepr`/`rightRepr` を適用・`equalPartitionRepr_isrepr` は `leftRepr_isRepr` の特例）→ y=x の RS 計算（TODO・`sum_id_nat` を cast で運ぶ）
- 演習候補: 分点が i/n の確認（show）・cast 一括ルートを試して壊す・`cast_mul`/`cast_summation` を自分で
- 引き: Ch12 へ「一般の分割で何が言える？性質を証明しよう」
- ⚠ **sum_id は Nat の式 `sum_id_nat`＝C10**。Real の RS 計算はそれを cast（射）で運ぶ。⚠ cast 補題は**構成的な部分のみ**（archimedean 系の sup 利用は Ch13 へ）。肥大時は 2 章分割を予約

### Ch12 — リーマン和の性質 5 本（`ch12_properties.md`、C12_Properties・到達点③）
- 問い: 一般の分割で何が言えるか
- 到達点: 後段が消費する性質 5 本（到達点③）・第 I 部古典ゼロの監査
- 新機能: なし（総合演習）。**IsRepr の定義は Ch5・幾何補題は Ch10 に移動済**——ここは「使う」側
- ANCHOR: なし（性質 5 本・docstring 済・ANCHOR は §5。`is_repr` は Ch5 へ移動）
- ▲**線形性＝加法＋スカラー倍**（RS は f について線形写像 `riemann_sum_isLinear`・Ch10 summation_isLinear の RS 版。符号・差はここから出る系）/ const / nonneg / 両側評価（脱 abs・理由は Ch13 予告）・▲**反例で IsRepr の必要性を実演**（定義は Ch5・タグを区間外にすると nonneg が壊れる）・▼第 I 部古典ゼロの総決算（監査の段階の山）
- 演習候補: additive/neg/const/nonneg/両側 rs_bound・**IsRepr を落とした反例**・章末 `#print axioms`
- 引き: Ch13 へ「分割を細かくしたとき和はどこへ向かう？値をひとつ選び取る力が要る（第 II 部へ）」
- ⚠ 性質 5 本は**生の不等式 2 本**で書く（NearLe 述語への昇格は発展部）。「同じ形が 3 回出たら昇格」の方針を一言。`length_sum` は const と密結合なので C12（幾何だが移さない）

---

## 4. 横断不変条件チェックリスト（レビューの照合基準）

各章ドラフトを以下で照合する。違反は「方針管理」上の指摘事項。

- **(a) 機能初出の単調性**（2026-06-15 証明の弧 Fine 分割 反映）: §3 の「新機能」に挙がるのは**前章までに登場していない**機能だけ。簡単→難しいの順が崩れていないか（例: tactic mode `by` は Ch6 まで出さない）。初出: **calc（`=`・term mode）=Ch1**・**structure キーワード=Ch2**・class（最小: 自動解決される構造）=Ch2・依存型/universe=Ch3・**tactic mode（by）=Ch6**・**rw/defeq=Ch7**・**simp/omega/ac_rfl/macro=Ch8**・**calc 深掘り（`≤`/`<`・Trans）=Ch9**・**induction=Ch10**・class 深い機構（解決・diamond）=Ch11。calc は term mode なので Ch1（`by` 不要）で導入してよい——`by`/tactic mode との区別を本文で明示
- **(b) CH 対応 6 表**: Ch1 で提示 → **Ch3** で ∀∃=Π/Σ を裏付け（Real.sup の署名）→ Ch4 で `#print` により完結（∧∨∃=も帰納型）。表の各行が「いつ裏付くか」と整合しているか
- **(c) 種明かしの糸**: Ch6 カーネル/De Bruijn・apply=メタ変数 → Ch7 rw=Eq.mpr → Ch8 simp＝停止する書き換え系・macro → Ch10 induction=recursor（Ch4 の recursor を回収）。「使う→仕組みを覗く」の順序が保たれているか
- **(d) 菱形の糸**（2026-06-15 反映）: Ch4 Zero bridge・Ch6 One bridge（良い配線が先）→ **Ch11 で diamond（悪い例）＋排他分割（AtLeastTwo・修正）** をまとめて。Ch2 は「class＝自動で見つかる構造」の良い面のみ。良い→悪い→修正の順が崩れていないか
- **(e) 監査の段階**: Ch0 で 3 道具導入 → 各章末で `#print axioms` → Ch12 で「第 I 部は古典公理ゼロ」を総決算。不変条件は **`Classical.choice` と `Real.sup` 系が前半の監査に出ないこと**（出たら設計違反）。`propext`・`Quot.sound` は標準の無害公理で、`rs_le_const` 等に現れてよい（説明は最小限に留め Ch17 へ送る）。「古典公理ゼロ」＝ choice ゼロの意味だと本文で明確化する
- **(f) 脱 abs/min/diam 方針**: 前半に abs・max・min・diam を持ち込まない。Ch12 の第 5 性質は両側評価（生の不等式 2 本）。理由（abs は古典性を呼ぶ）は Ch13 へ予告のみ
- **(g) コード引用の正確性**: ANCHOR が実在するか（§5 の未付与リストに注意）。defeq・監査の主張が**実ビルドと一致**するか（`cast_defeq` の `#check_failure`、章末 `#print axioms` の値など、机上で書かず実行値を貼る）
- **(h) 3 つの鍵の言及**（2026-06-15 スワップ反映）: 依存型(**Ch3**・Real.sup)・universe(**Ch3**)・帰納型(Ch4)が正面で扱われ、他章の解説でも意識的に言及されているか。structure キーワードは Ch2

---

## 5. 前半スキャフォールドの既知 TODO（執筆中に発生する配線作業）

本文に集中するパスのため以下は未整備。**引用が必要になった段で**対応（多くは P4）。

- **Ch2/Ch3 スワップ済（2026-06-15）**: 新 C02_Structures.lean（structure_as_data・general_proof・and_is_structure）＝Ch2 machinery／C02_Axioms→C03_Axioms.lean（階層・公理・根幹2行・check_failure・three_brothers）＝Ch3／旧 C03_Class は解体（diamond は C08_Numbers へ）。md は ch02_structures.md・ch03_axioms.md
- **証明の弧 Fine 分割＋自動化前倒し＋Part II 改番（2026-06-15・構成 v4）**: 「章を短く 1 テーマに・自動化でコーパスを畳む工夫をコーパスの途中に」というユーザー方針で、旧 C06（424 行・80 宣言・独立 3 テーマ）を**単一テーマ 5 章**に分割: **Ch6 タクティク入門**（C06_Tactics）／**Ch7 書き換えと 2 つの等しさ**（新 C07_Rewrite・等式コーパス＋defeq）／**Ch8 自動化と自作タクティク**（C08_Automation・旧 Ch10 間奏を前倒し本章化＝simp/omega/ac_rfl/my_ring・load-bearing）／**Ch9 順序と calc**（新 C09_Order・順序コーパス＋混在 calc）／**Ch10 帰納法**（C10_Induction・旧 C07）。到達点②③は **Ch11 具体例**（C11_Numbers・旧 C08）・**Ch12 性質**（C12_Properties・旧 C09）。**Part II 改番** C13–C17（旧 C11–C15・FTC=Ch17）。新 import 連鎖は線形で C08 自動化が C09/C10 の前。**term/tactic の吟味**: 自明な公理射影（`le_refl := …` 等）は該当章（Ch6/Ch9）に置き Ch1–5 へは散らさない（少量の term 証明は Ch3 に意図的追加済＝公理体感・class 納得）
- **C06/C07/C09**: ANCHOR 未付与（タクティク/等式/順序 corpus）。特定の補題証明を引用する段で `ANCHOR:` を付ける
- **IsRepr/幾何/Σ補題の配置（2026-06-15）**: `IsRepr` 定義→**C05**（ANCHOR `is_repr`）／純 Partition 幾何（length_nonneg・points_mono・left/right_le_point・tag_mem'）と **`length_sum`**→**C10_Induction**（induction の実地）／**`sub_summation`**→**C10_Induction**（Σ corpus）／`equalPartitionRepr_isrepr`→**C11_Numbers**。C12_Properties は RS の性質に絞る。反例は Ch12 で「IsRepr が必須な理由の実演」として残す
- **RS 線形性＝加法＋スカラー倍（2026-06-15）**: `riemann_sum_add`＋`riemann_sum_smul`＝線形性の本体（`riemann_sum_isLinear : IsLinearMap …`・**Ch10** summation_isLinear の RS 版・VectorSpace (Real→Real) 各点インスタンスを C12 に追加）。`riemann_sum_neg`（c=−1）・`riemann_sum_sub` はそこから出る系
- **cast は射（2026-06-15）**: ① `sum_id` は Nat の恒等式 `sum_id_nat`＝**C10_Induction**② **cast を「射」として明示**＝C11_Numbers（`IsNatHom`＋`cast_isHom`・`cast_mul`/`cast_le`・`cast_summation`＝Σ と可換。**Ch10** IsLinearMap と並ぶ「射」の述語）③ **代表点を左端・右端に取る一般化**＝C05。`equalPartitionRepr` は `leftRepr` を適用。監査例は `cast_mul`（C11・C17 とも・[Real, instLOF] 古典ゼロ）。**等分点の formula の扱いは別途検討（ユーザー留保）**
- **C12_Properties**: 性質 5 本（riemann_sum_add/neg/const/nonneg・rs_le_const）の ANCHOR 未付与（docstring は済）
- **docstring の整合**: Ch0 で「Text/ のコードは docstring 付き」と述べる以上、各 C** ファイルにも docstring を順次付ける（現状 C12 全宣言＋C05 の is_repr・C10 の幾何・C11 の equalPartitionRepr 系が済）。新規・改稿する宣言には `/-- -/` を付ける運用に
- **Ch8 自動化＝反射タクティク実装済（2026-06-15）**: バニラ（simp/omega/ac_rfl）の実測検証後、**proof by reflection で `my_abel`（加法群）・`my_ring`（環）を C08_Automation に実装**（mathlib の ring/abel/linarith が無いため自作）。my_ring は my_abel を包含し、`a+b-a=b`〜`(a+b)*(c+d)=…` を一行で閉じる。**follow-up**: 既存コーパス（C07/C09/C10）の手証明を my_abel/my_ring に置換して重い章を縮小・反射の一般化（多項式正規形・Horner）は付録 D・順序タクティク（順序のみ／順序体）は次フェーズ
- **序章/Ch0**: 対応 C** ファイルなし。`main'` 引用は MyProject 参照・監査出力は**実行値**を貼る
- **演習の sorry 化＋Solutions 分離・`#include` 配線・mdbook 導入**: P4（今回はインライン引用で可・ANCHOR は維持し後で変換）
- **付録 D（反射版 my_ring）**: Ch8 の入口デモの本体。前半の範囲外
- **コメント内 Ch 番号の掃除**: 改番で .lean／.md のコメント・本文中の旧 Ch 番号参照が一部残存。引用・精読の段で順次修正（ビルドには無関係）
