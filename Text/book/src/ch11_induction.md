# Ch11 帰納法 — 加群の線形性・Σ コーパス・リーマン和の性質（到達点③）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆。構成v6 -->
<!-- 構成v6: 旧 Ch14「リーマン和の性質」を本章後半に統合（性質は cast 不要で帰納法章に置ける） -->

- 前章からの問い: スカラーの代数は揃った。だが Σ（有限和）の性質と、リーマン和の性質は項数 n の帰納法が要る
- 到達点: 帰納法で Σ 補題コーパス＋Partition の大域単調性を証明し、**加群の線形性**（Ch6 で定義した Module・IsLinearMap の実例）を積み上げ、**リーマン和の性質 5 本（到達点③）**まで到達する。第 I 部古典ゼロの監査
- 新しい Lean 機能: induction（rfl/show・omega は Ch8/Ch9 既出）・数列空間/関数空間の中置代数（Ch6 の Module を `f + g`・`f ≤ g` で使う）
- コード: C11_Induction.lean（Σ補題コーパス＋Partition 幾何＋線形性の塔＋sum_id_nat＋RS 性質 5 本）

## 11.1 帰納法 — recursor の糖衣

- induction タクティク＝Ch5 の recursor 適用（種明かしの回収）。基底と帰納段の構造
- 等式変形の段は Ch8 の rw／Ch9 の simp・my_ring で畳める——「前章までの道具を帰納法に組み込む」

## 11.2 Σ 補題コーパス

- 線形性（additive/smul/neg）・順序（nonneg/le）・congr（**rw は束縛子の下に入れない**——限界と congruence 補題という回避策）
- 添字の付け替え `fun k => f ⟨k.val, …⟩`——本書で最も手のかかるパターンの訓練場
- 順序の評価（summation_nonneg・summation_le）は Ch10 の順序コーパス（add_le_add' 等）を呼ぶ

## 11.3 ボス戦: telescope_sum

- 最初の本格的帰納法証明。Σ(g(i+1)−g(i)) = g(n)−g(0)（Ch8 の telescope_2 が部品。→ §10.8 length_sum・Ch17 中点和）

## 11.4 Partition の基本性質 — 読者自身の構造への帰納法

- 隣接単調（公理 `increase`）→ **`points_mono`＝大域単調を induction で**導く（well-founded 再帰は不要）。`left_le_point`/`point_le_right`（端点評価）・`tag_mem'`（代表点は [u,v] 内）
- `length_nonneg`（小区間長は非負・`nonneg_iff_le` から）・`length_sum`（Σ length = v−u・telescope で潰れる）
- 「自分で定義した帰納型（Range・Partition）に帰納法を適用する」最初の実地。すべて本章後半の RS 性質証明が消費する

## 11.5 Σ は線形写像である — 加群 Ch6 の最初の実例

- additive_summation と summation_mul_left の 2 本は、数学者の言葉では「有限数列のなすベクトル空間上の線形形式」という **1 つの主張**——そう言い直してみる（ANCHOR `summation_linear`）
- **加群 Module は Ch6 で定義済み**（`Range n → Real` も `Real → Real` も funModule で自動的に加群）。`summation_isLinear` の証明が **corpus の 2 本をペアにするだけ**であることを見る——「概念（Ch6 の IsLinearMap）を定義すると、すでに証明していたことが 1 つの主張に束ねられる」
- mathlib 対応（Module・LinearMap・Finset.sum の線形性）は付録 C へ

## 11.6 線形性を積み上げる: Σ → 重みつき Σ →（引き戻し）→ RS（ANCHOR `weighted_summation`）

- **線形性は合成と特殊化で次の層に伝播する**——RS の線形性を一気に証明せず、層で積む:
  - `isLinear_comp`: **線形写像の合成は線形**（U→V→W）。「線形性が合成で保たれる」一般道具
  - `WeightedSum w g := Σ (g i * w i)`: Σ に対角重み w を入れた線形形式。**リーマン和はこの特殊化**（重み = 小区間の長さ・被加数 = タグでの値・`RS f Δ ξ = WeightedSum Δ.length (i↦f(ξ i))` は defeq）
  - `weightedSum_isLinear w`: 重みつき Σ は被加数について線形（証明は `weightedSum_add`/`smul`＝分配・結合 → corpus 2 本）
  - `precompose_isLinear ξ`: **引き戻し `f ↦ (i↦f(ξ i))` は線形**（関数空間 → 数列空間・各点なので `⟨rfl, rfl⟩`）
- **単調性も並行に積む**（線形性の順序版・ANCHOR `weighted_summation` 末尾）: 数列空間 `Range n → Real` に**点ごと半順序** `instance : LE`（`f ≤ g := ∀ i, f i ≤ g i`・線形でない＝le_total 無し）を入れ、`summation_le` を `f ≤ g` の中置で述べる。`weightedSum_le`（重み非負なら被加数について単調＝各成分 `nonneg_mul_nonneg` → `summation_le`）

## 11.7 RS は f について線形写像 — 塔の合成で 1 行

- **被積分関数の代数を中置で**: 関数空間 `Real → Real` の加群（Ch6 funModule）＋ Sub で `RS(f + g)`・`RS(c • f)`・`RS(-f)`・`RS(f - g)` と書く（点ごと演算・`(f+g) x = f x + g x` は rfl）。一般化した my_abel もこの関数空間でそのまま動く（順序は無いので lin は不可）
- **§10.6 の塔を合成して帰着**（一気に証明しない）: `riemann_sum_isLinear = isLinear_comp (weightedSum_isLinear Δ.length) (precompose_isLinear ξ)` の**合成 1 行**
- **加法 `RS(f + g)=RS f+RS g`・スカラー倍 `RS(c • f)=c·RS f` は射影**（`.1`/`.2`）で 1 行・**符号と差はそこから出る系**
- Σ→重みつきΣ→RS の 3 層対応（積分への対応の予告）

## 11.8 const — 望遠鏡和の快感

- `length_sum`（Σ length = b − a・§10.4 の telescope の回収）を const が消費。`riemann_sum_const`（定数関数の RS = c(b−a)）

## 11.9 単調性 — riemann_sum_le（nonneg・両側評価の親）

- **RS の単調性 `f ≤ g (区間上) ⇒ RS f ≤ RS g`（IsRepr 必須）を中心に据える**。§10.6 の重みつき Σ の単調性 `weightedSum_le`（重み = length ≥ 0）に帰着——線形性が「合成で帰着」だったのと並行に、**単調性も Σ→重みつきΣ→RS と積み上がる**
- nonneg・両側評価は**この特殊化**: nonneg ＝ 下を `const 0` で・上側 ＝ 上を `const c` で・下側 ＝ 下を `const c` で。各々 `riemann_sum_le` ＋ `riemann_sum_const` で 2 行

## 11.10 nonneg — 反例が「なぜ IsRepr が必須か」を実演する

- **単調性 `riemann_sum_le` の系**（`const 0` との比較）。IsRepr（代表点の妥当性）は **Ch5 で定義済**。ここでは**使い**、タグを区間外にすると非負が**壊れる反例**で「妥当性条件が飾りでない」ことを見せる
- 使う道具: `tag_mem'`・`points_mono`・`length_nonneg`——いずれも §10.4 で証明済

## 11.11 両側評価 rs_bound

- `c·(v−u) ≤ RS ≤ c·(v−u)`（`rs_le_const` / `const_le_rs`）も**単調性 `riemann_sum_le` の系**（定数関数との比較）。**abs を使わない**——理由は「第 II 部で明かす」と予告（Ch14 素朴定義実験への伏線）
- 生の不等式 2 本で書く（述語化しない——「同じ形が 3 回出たら昇格」の方針を一言）

## 11.12 sum_id_nat — Σ_{i<n} i は Nat の恒等式

- `(1+1)·Σ i + n = n·n`（⟺ Σ_{i<n} i = n(n−1)/2）。Summation は和があれば定義でき **Nat でも使える**——これは Real ではなく **Nat の式**。減算を避けた形にして Ch12 で cast がきれいに通るようにしてある
- 帰納法＋omega（Ch9）の合わせ技（n·n は omega の外なので succ_mul/mul_succ で展開してから omega）

## 11.13 章末監査 — 第 I 部の総決算

- 全定理の `#print axioms` が [Real, instLOF]（＋propext/Quot.sound の説明は最小限に留め Ch15 へ）
- 第 I 部は**構成的**——その意味の予告（BHK の転調は Ch14–14 で）

## 演習

- コーパスのうち本文精読 3 本・残り sorry 埋め・`points_mono` を induction で・`sum_id_nat`・nonneg の反例を自分で作る

## 引き

- 「道具は揃い、リーマン和の性質も手に入った。Ch5 の sorry を消し、数を建てて（cast）2 等分・n 等分の**具体計算**へ」
