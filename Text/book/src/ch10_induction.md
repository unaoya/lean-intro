# Ch10 帰納法 — Σ コーパスと大域単調性

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 旧「defeq・帰納法」章から defeq を Ch7 へ分離。本章は帰納法に純化 -->

- 前章からの問い: スカラーの代数は揃った。だが Σ（有限和）の性質は項数 n の帰納法が要る
- 到達点: 帰納法で Σ 補題コーパス＋Partition の大域単調性が証明できる
- 新しい Lean 機能: induction（rfl/show・omega は Ch7/Ch8 既出）
- コード: C10_Induction.lean（Σ補題コーパス 9 本＋Partition 幾何＋線形脇道＋sum_id_nat。Proto: FTCCore§Σ＋Refine§3 を再配列）

## 10.1 帰納法 — recursor の糖衣

- induction タクティク＝Ch4 の recursor 適用（種明かしの回収）。基底と帰納段の構造
- 等式変形の段は Ch7 の rw／Ch8 の simp・my_ring で畳める——「前章までの道具を帰納法に組み込む」

## 10.2 Σ 補題コーパス

- 線形性（additive/smul/neg）・順序（nonneg/le）・congr（**rw は束縛子の下に入れない**——限界と congruence 補題という回避策）
- 添字の付け替え `fun k => f ⟨k.val, …⟩`——本書で最も手のかかるパターンの訓練場
- 順序の評価（summation_nonneg・summation_le）は Ch9 の順序コーパス（add_le_add' 等）を呼ぶ

## 10.3 ボス戦: telescope_sum

- 最初の本格的帰納法証明。Σ(g(i+1)−g(i)) = g(n)−g(0)（Ch7 の telescope_2 が部品。→ Ch12 length_sum・Ch16 中点和）

## 10.4 Partition の基本性質 — 読者自身の構造への帰納法

- 隣接単調（公理 `increase`）→ **`points_mono`＝大域単調を induction で**導く（well-founded 再帰は不要）。`left_le_point`/`point_le_right`（端点評価）・`tag_mem'`（代表点は [u,v] 内）
- `length_nonneg`（小区間長は非負・`nonneg_iff_le` から）・`length_sum`（Σ length = v−u・telescope で潰れる）
- 「自分で定義した帰納型（Range・Partition）に帰納法を適用する」最初の実地。すべて Ch12 の性質証明が消費する

## 10.5 脇道: Σ は線形形式である（2026-06-12 追加）

- additive_summation と summation_mul_left の 2 本は、数学者の言葉では「有限数列のなすベクトル空間上の線形形式」という **1 つの主張**——そう言い直してみる（C10 の ANCHOR: vector_space / summation_linear）
- `class VectorSpace (V) extends Add V, Neg V, Zero V, SMul Real V`（公理 8 本）を自作——Ch2 の class 設計の応用。`•` は core の SMul の記法
- **関数型へのインスタンス**: Range n → Real に各点演算で instance を与える（公理の証明はすべて funext＋Real の対応補題 1 行——funext の活躍どころ）。Real 自身も Real 上のベクトル空間（• = 積）
- `IsLinearMap` を定義し、`summation_isLinear` の証明が **corpus の 2 本をペアにするだけ**であることを見る——「概念を定義すると、すでに証明していたことが 1 つの主張に束ねられる」
- mathlib 対応（Module・LinearMap・Finset.sum の線形性）は付録 C へ

## 10.6 線形性を積み上げる: Σ → 重みつき Σ →（引き戻し）→ RS（ANCHOR `weighted_summation`）

- **線形性は合成と特殊化で次の層に伝播する**——RS の線形性（Ch13）を一気に証明せず、層で積む:
  - `isLinear_comp`: **線形写像の合成は線形**（U→V→W）。「線形性が合成で保たれる」一般道具
  - `WeightedSum w g := Σ (g i * w i)`: Σ に対角重み w を入れた線形形式。**リーマン和はこの特殊化**（重み = 小区間の長さ・被加数 = タグでの値・`RS f Δ ξ = WeightedSum Δ.length (i↦f(ξ i))` は defeq）
  - `weightedSum_isLinear w`: 重みつき Σ は被加数について線形（証明は `weightedSum_add`/`smul`＝分配・結合 → corpus 2 本）
  - `precompose_isLinear ξ`: **引き戻し `f ↦ (i↦f(ξ i))` は線形**（関数空間 → 数列空間・各点なので `⟨rfl, rfl⟩`）
- Ch13 で `riemann_sum_isLinear = isLinear_comp (weightedSum_isLinear Δ.length) (precompose_isLinear ξ)` と**合成 1 行**で出る——「Σの線形性 → 重みつきΣ → RS」の積み上げが見える

## 10.6 sum_id_nat — Σ_{i<n} i は Nat の恒等式

- `(1+1)·Σ i + n = n·n`（⟺ Σ_{i<n} i = n(n−1)/2）。Summation は和があれば定義でき **Nat でも使える**——これは Real ではなく **Nat の式**。減算を避けた形にして Ch11 で cast がきれいに通るようにしてある
- 帰納法＋omega（Ch8）の合わせ技（n·n は omega の外なので succ_mul/mul_succ で展開してから omega）

## 演習

- コーパス 9 本のうち本文精読 3 本・残り sorry 埋め・`points_mono` を induction で・`sum_id_nat`

## 引き

- 「道具は揃った。Ch5 の sorry を消しに行こう——そして 2 等分・n 等分へ」
