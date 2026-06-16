# Ch5 数学的構造とその射 — 加群・順序半環の射 cast・分割の例

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆。構成v6 で新設した章 -->

- 前章からの問い: リーマン和は定義できた。和や分割が住む**数学的構造**はどう書くか
- 到達点: 加群（Real 上の Module）・順序半環の射（cast）を**定義として**持ち、関数空間が自動で加群になる仕組みを見る。分割の具体例（等分割）の分点式を見る。**ここは「構造と射の輪郭」を term で描く章——tactic も順序補題もまだ使わない**
- 新しい Lean 機能: class の再訪（Ch2 の構造観の具体化）・**誘導 instance**（行き先から構造を持ち上げる）・term mode の構造定義（`funext` で点ごと）・cast/リテラルの定義（OfNat/NatCast/Div）・述語による「射」の抽象（Monotone・IsOrderedSemiringHom）
- コード: C05_Structures.lean（Module＋funModule・IsLinearMap・Real.ofNat/OfNat/NatCast/Div・Monotone・IsOrderedSemiringHom・equalPoints）
- ⚠ 設計の核: ここは**定義と概念だけ**。証明本体は順序・帰納法が要るので後回し——Σ/リーマン和の線形性は Ch10、cast が射である証明（≤/+/× を保つ）と等分割の完成は Ch11

## 5.1 加群 — Real 上の Module（構造）

- `class Module (V)` extends Add/Neg/Zero/SMul ＋ 8 公理（ANCHOR `module`）。Ch2 で「class＝自動で見つかる構造」を学んだ、その具体例。スカラーは Real（スカラー単位 1 は C03 で前倒し済み）
- Real 自身が Real 上の加群（• は積・公理は階層クラス Ch3 のフィールドから直接）

## 5.2 行き先から構造を持ち上げる — 関数空間も加群

- ★ **誘導 instance** `funModule : [Module V] → Module (α → V)`（ANCHOR `module` 末尾）: 行き先 V が加群なら任意の射 `α → V` も各点演算で加群。証明は V の加群公理を `funext` で点ごとに持ち上げるだけ（term mode）
- これで `Range n → Real` も `Real → Real` も**個別インスタンス不要**で加群に——リーマン和の線形性（Ch10）・被積分関数の中置代数 `f + g`（第 II 部）の土台

## 5.3 線形写像 — 射の概念

- `IsLinearMap T := (加法を保つ) ∧ (スカラー倍を保つ)`（ANCHOR `module`）。「構造を保つ写像＝射」の最初の例。Σ がこの射であること（`summation_isLinear`）の**証明は Ch10**——ここは概念の定義だけ

## 5.4 cast — Nat を Real に埋め込む（定義）

- `Real.ofNat`（構造的再帰 0↦0, n+1↦(n の像)+1・ANCHOR `of_nat`）と窓口 instance: リテラル 2 以上の `OfNat`（Ch3 の `failed to synthesize OfNat Real 2` がここで解決）・変数の埋め込み `NatCast`・除法 `Div`（等分割の分点式のため）
- 🪟 数の 2 つの建て方（予告）: cast は代数の 0/1 から積む。`cast 0 = 0` は構成により rfl だが `cast 1 = 1` は命題的——この defeq の綻びと cast が射である証明は Ch11（Ch7「2 つの等しさ」の実戦）

## 5.5 順序写像 Monotone — 順序の射

- `Monotone φ := ∀ a b, a ≤ b → φ a ≤ φ b`（ANCHOR `monotone`）。順序集合間の「順序を保つ写像」を抽象的に述べる述語。`≤` の保存だけを取り出した射

## 5.6 順序半環の射 — IsOrderedSemiringHom（概念）

- `structure IsOrderedSemiringHom φ`（map_zero/one/add/mul ＋ monotone・ANCHOR `cast_hom`）: Nat → Real が 0・1・+・×・≤ を保つこと。Nat と Real を順序半環とみなしたときの準同型
- **設計の眼目**: cast 固有の性質（nonneg・狭義単調・単射・Σ と可換）は、この「射であること」から**一般論として**出る。cast がこの実例だという証明（cast_le・cast_add/mul）は Ch11——ここは「射とは何か」の枠だけ置く

## 5.7 分割の具体例 — 等分割の分点式 equalPoints

- `equalPoints m a b := fun i => a + i·(b−a)/m`（ANCHOR `equal_points`）。Ch4 の Partition を cast と除法で具体的に作るための「材料」——cast（↑i.val）と除法（/m）が登場する最初の実例
- これが広義単調（increase）で両端が a,b になる証明には順序・除法・cast の順序系が要るので、**完全な Partition への組み上げ（equalPartition）は Ch11**。ここでは分点を与える関数だけを見せる（定義↔証明の分離・trivialPartition と同じ二段構え）

## 引き

- 「構造と射の輪郭は描けた。だが trivialPartition の sorry も、Σ が射であることも、cast が射であることも、まだ**証明できない**——証明を書く道具（タクティク）が要る。次章から道具を揃える」
