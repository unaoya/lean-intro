# Ch4 有限和 — 帰納型と再帰

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 有限和とは何か
- 到達点: Range と Summation が読めて書ける。CH 対応表が完結する
- 新しい Lean 機能: 帰納型【鍵 3】・Subtype・構造的再帰・rfl=defeq の予告編
- コード: C04_Summation.lean（Proto/Sum 29 行 → ~25 行）

## 4.1 #print で種明かし — すべては帰納型だった

- Nat・And・Or・False・Eq を `#print`。Ch1 から使ってきた論理結合子の正体
- **CH 対応のパンチライン**: 原始は（依存）関数型だけ、残りは全部帰納型——「論理は依存関数と帰納型で実現できる」

## 4.2 自然演繹と recursor

- 導入則↔コンストラクタ・除去則↔recursor（`#print And.rec` / `Or.rec`）
- 🪟 窓: 自然演繹と recursor — 除去則の正体（induction タクティクの種明かしの予告）

## 4.3 Range — 証明を抱えた添字

- `Range n := { i : Nat // i < n }`（Subtype＝依存和の実物、CH 表 ∃ 行の Type 側親戚）
- incl / addone（隣接分点を安全に参照する 2 つの埋め込み）

## 4.4 Summation — 構造的再帰

- `(n : Nat) → (Range n → α) → α` という型自体が依存関数の実物
- コラム: なぜ List でないのか（表現の選択の損得勘定表——長さは型へ・整合性命題は消す）

## 4.5 計算で証明される定理

- summation_zero / summation_succ は **rfl で証明できる**（定義の再帰方程式＝defeq の予告編、Ch7 の主題へ）

## 4.x 帰納型を使う — 除去規則（recursor）と cases／induction（2026-06-15 追加）

- **骨格**: どの帰納型にも **導入規則**（構成子＝値を作る）と **除去規則**（recursor＝値を使う）がある。除去規則は同じ形だが、**構成子が再帰的な引数を持つと、その分だけ帰納法の仮定 (IH) を受け取る**——再帰の有無が `cases` と `induction` を分ける
- **Ch1 の回収**: ∨ の `.elim`（or_swap・and_or_distrib の場合分け）は**∨ の除去規則＝cases**だった——∨ は非再帰なので IH 無し。Ch1 で既にやっていた
- **対比を機械で**（ANCHOR `eliminators`・`#check @Or.rec` / `#check @Nat.rec`）: `Or.rec` は各構成子の引数を受けるだけ（IH 無し＝cases）。`Nat.rec` は succ の段で `motive n`（＝IH）も受ける（Nat が再帰だから＝induction）。**IH が「再帰している箇所」にちょうど現れる**のが型に見える
- **CH 対応のパンチライン**（ANCHOR `ch_punchline`・Ch1 の表を回収）: `#print And`/`Or`/`Exists`/`False` で「これらは帰納型（構成子＋recursor）」が、`#check fun A B => A → B`/`fun P => ∀ n, P n` で「→/∀ は Π（依存関数）」が見える。**論理 = 依存関数（→ ∀ ¬）＋ 帰納型（∧ ∨ ∃ ⊥ ⊤ =）**——だから**2 つの原始（Π＋帰納型）の導入/除去規則だけ**で論理は尽きる。→ と ∀ が同じ関数なのが核（codomain の依存だけ違う）。「論理は依存関数＋帰納型」を `#print` で実機確認する縦糸の回収点
- **Summation について最初の証明**（ANCHOR `summation_first_proofs`）: Summation は `Nat.rec` で定義した。それを**除去規則として証明に走らせる**のが induction:
  - (1) `summation_congr`: `congrArg` だけ（除去規則すら不要）
  - (2) `summation_all_zero`: **term mode のまま**（`by` 不使用）`Nat.rec` の除去で全零和=0 を証明。succ の段の `summation_all_zero n` が IH そのもの
- **縦糸**: 「定義する再帰」と「証明する帰納」は同じ recursor。ergonomic な `cases`/`induction` タクティクは Ch6 以降、Σ 補題の本格コーパスは **Ch10**。Ch1（∨ の cases）→ Ch4（Nat の induction）→ Ch10（タクティク＋コーパス）で除去規則の糸を張る
- ⚠ Ch1–5 は term mode 基調。ここは `Nat.rec` による term mode の除去で `by` を使わない——「帰納法＝除去規則の適用」を機構レベルで見せる予告

## 演習

- Range の操作（incl/addone の値の確認を show で）・小さい n での Summation の手計算
- **型シグネチャの設計**（2026-06-12 決定: 本文素材）:
  - Summation の契約は最小の `[Add α] [Zero α]`（二項演算とゼロの値）。**意味論のクラス（Zero/One）とリテラル整形の窓口（OfNat）の分離**を本文で——core には Zero/One と一方向 bridge（Zero.toOfNat0/One.toOfNat1）が mathlib から昇格して入っており、本書は公理の zero を `instance : Zero Real` で登録するだけ（C02 の ANCHOR: zero_bridge）。「bridge は一方向・値は defeq」＝**良い菱形の規律**（Ch3 の悪い菱形トイデモの回収。数の建て方の本格論は Ch8）
  - 演習: `n` を implicit にできるか？ 変えてみて何が起きるか（依存型の見せ場が消える・rw の制御）——implicit 引数は Ch2 で読み、Ch5 で初めて自分の定義に書き、Ch6 で機構を種明かしする 3 段配置への橋渡し
- コラム: mathlib の Σ 事情——`List.sum` は `[Add][Zero]` で足りるのに `Finset.sum` は AddCommMonoid を要求する（Finset＝順列で割った商なので well-definedness に可換性・結合性が要る）。**添字集合の表現を緩くすると代数の契約が重くなる**——「表現の選択」の糸との交差点

## 引き

- 「和は書けた。分割をデータとしてどう表す？」
