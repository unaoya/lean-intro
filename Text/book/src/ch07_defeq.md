# Ch7 sorry を埋める道具 II — 等しさは 2 種類・帰納法

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 順序コーパス＋≤/< 混在 calc・Trans は Ch6 へ移動。本章は defeq+induction に純化 -->

- 前章からの問い: 等しさには 2 種類あるのか（Ch6 で rw が効く場面・効かない場面を見た）
- 到達点: defeq と構文的等しさを区別できる。帰納法で Σ 補題コーパス＋Partition の大域単調性が証明できる
- 新しい Lean 機能: defeq と rw の構文性・rfl/show・induction・omega（≤/< 混在 calc・Trans・順序コーパスは Ch6 で獲得済み・`=` の calc は Ch1）
- コード: C07_Induction.lean（Σ補題コーパス 9 本＋Partition 幾何＋線形脇道＋sum_id_nat。Proto: FTCCore§Σ＋Refine§3 を再配列）

## 7.1 等しさは 2 種類ある

- `a + -b = a - b := rfl` が通るのに rw は区別する——defeq（計算で同じ）と構文（見た目が同じ）
- show による defeq の言い換え（Ch6 の `show a + -b = …` の正体）。🪟 窓: 正規化と `#reduce` — 証明の簡約

## 7.2 種明かし: rw の正体

- `Eq.mpr`＋motive（congrArg）。`#print` で rw 証明の項を見る——構文的でなければならない理由が機構で腑に落ちる
- **rw の罠 2 種（試作の実戦例）**: ① 意図しない部分項を先に潰す → 引数明示で回避 ② パターン捕獲（q を (q+q)/2 に書き換えると (p+q) 内の q も巻き込む）→ 独立補題への切り出しで回避

## 7.3 帰納法 — recursor の糖衣

- induction タクティク＝Ch4 の recursor 適用（種明かしの回収）。omega（Nat の決定手続き——正体は Ch10/付録 D への伏線）

## 7.4 Σ 補題コーパス

- 線形性（additive/smul/neg）・順序（nonneg/le）・congr（**rw は束縛子の下に入れない**——限界と congruence 補題という回避策）
- 添字の付け替え `fun k => f ⟨k.val, …⟩`——本書で最も手のかかるパターンの訓練場
- 順序の評価（summation_nonneg・summation_le）は Ch6 の順序コーパス（add_le_add' 等）を呼ぶ——「Ch6 の道具を帰納法に組み込む」

## 7.5 ボス戦: telescope_sum

- 最初の本格的帰納法証明。Σ(g(i+1)−g(i)) = g(n)−g(0)（→ Ch9 length_sum・Ch14 中点和の部品）

## 7.6 Partition の基本性質 — 読者自身の構造への帰納法

- 隣接単調（公理 `increase`）→ **`points_mono`＝大域単調を induction で**導く（well-founded 再帰は不要）。`left_le_point`/`point_le_right`（端点評価）・`tag_mem'`（代表点は [u,v] 内）
- `length_nonneg`（小区間長は非負・`nonneg_iff_le` から）・`length_sum`（Σ length = v−u・telescope で潰れる）
- 「自分で定義した帰納型（Range・Partition）に帰納法を適用する」最初の実地。すべて Ch9 の性質証明が消費する

## 7.7 脇道: Σ は線形形式である（2026-06-12 追加）

- additive_summation と summation_mul_left の 2 本は、数学者の言葉では「有限数列のなすベクトル空間上の線形形式」という **1 つの主張**——そう言い直してみる（C07 の ANCHOR: vector_space / summation_linear）
- `class VectorSpace (V) extends Add V, Neg V, Zero V, SMul Real V`（公理 8 本）を自作——Ch2 の class 設計の応用。`•` は core の SMul の記法
- **関数型へのインスタンス**: Range n → Real に各点演算で instance を与える（公理の証明はすべて funext＋Real の対応補題 1 行——funext の活躍どころ）。Real 自身も Real 上のベクトル空間（• = 積）
- `IsLinearMap` を定義し、`summation_isLinear` の証明が **corpus の 2 本をペアにするだけ**であることを見る——「概念を定義すると、すでに証明していたことが 1 つの主張に束ねられる」
- mathlib 対応（Module・LinearMap・Finset.sum の線形性）は付録 C へ。発展演習: RiemannSum も f について線形（Ch9 の additive/neg の言い直し）・線形形式の表現（Σ の双対基底）

## 7.8 sum_id_nat — Σ_{i<n} i は Nat の恒等式

- `(1+1)·Σ i + n = n·n`（⟺ Σ_{i<n} i = n(n−1)/2）。Summation は和があれば定義でき **Nat でも使える**——これは Real ではなく **Nat の式**。減算を避けた形にして Ch8 で cast がきれいに通るようにしてある
- 帰納法＋omega の合わせ技（n·n は omega の外なので succ_mul/mul_succ で展開してから omega）

## 演習

- コーパス 9 本のうち本文精読 3 本・残り sorry 埋め・`points_mono` を induction で・`sum_id_nat`

## 引き

- 「道具は揃った。Ch5 の sorry を消しに行こう——そして 2 等分・n 等分へ」
