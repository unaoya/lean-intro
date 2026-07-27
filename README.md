# lean-intro — Lean 4 入門教材と、その素材となる FTC 形式化

Lean 4 の入門教材（`Text/`）と、その素材・参照実装である微積分学の基本定理（FTC）の形式化
（`MyProject/`）を収めたリポジトリ。どちらも **mathlib 非依存**で、実数を 5 本の公理から立ち上げている。

書名（暫定）: **Lean で読む・書く・開ける微積分 — 公理 5 本から微積分学の基本定理へ**

統一テーゼは「**数学も、道具も、開けて見る**」——信じる対象を 5 本の公理と 1 つの小さなカーネルまで
切り詰める。

- **柱 A（数学を開ける）**: 実数の公理だけから出発し、mathlib なしでリーマン積分を構成し FTC を
  証明する一本道を、読者が演習で自ら登る。監査装置は `#print axioms`
- **柱 B（道具を開ける）**: タクティクが「なぜ証明になるのか」を `#print`（生成された証明項）と
  De Bruijn 基準で答え、rw・simp・omega の中身を開け、最後は読者がタクティクを自作する

## 構成

```
Text/            教材の実体（教材コードは MyProject を import しない・自己完結）
  book/          原稿（mdBook）
    book.toml
    src/SUMMARY.md          目次（3 部＋発展部）
    src/part1/              第一部「型と項で証明する」（md と .lean を共置）
    src/chNN_*.md           第二部・第三部の章原稿
  C03_*.lean 〜 C18_*.lean  第二部・第三部のテキスト用 Lean ソース
  Proto/         試作の記録（M1–M7）
  NewChapter/    新章の試作（Cauchy・Dedekind）
Text.lean        第二部以降の umbrella

MyProject/       参照実装（FTC が sorry ゼロで証明されている保証・完成品の博物館）
MyProject.lean   ルートモジュール（#print axioms main で公理を常時監査）

docs/
  textbook_plan.md        教材の設計書
  part1_writing_guide.md  前半の執筆ガイド＆レビュー基準
```

教材の執筆規約は `Text/README.md`、章立ての最新確定版は `Text/book/src/SUMMARY.md` を参照。

## ビルド

```bash
lake build               # 参照実装（Calculus。デフォルトターゲット）
lake build Text          # 教材 第二部・第三部
lake build TextI         # 教材 第一部
mdbook build Text/book   # 原稿を book-html/ に出力
```

`lake build Text` / `TextI` は演習の `sorry` 警告を含む。これをデフォルトビルドから隔離するため、
`lake build` には教材ターゲットを含めていない。

## 参照実装について（MyProject/）

連続関数の向き付き積分は至るところ微分可能で、導関数は元の関数——という FTC を完全証明している
（`sorry` ゼロ・警告ゼロ）。

```lean
theorem main' (f : Real → Real) (a x : Real) (hf : Continuous f) :
    let F := fun x ↦ (OIntegral f a x); HasDerivAt F (f x) x
```

**公理は 5 本**（`MyProject/Axioms.lean` に集約）:

1. `Real : Type`
2. `Real.instLOF : LinearOrderedField Real` — 体と順序の公理
3. `Real.sup` / `Real.sup_ub` / `Real.sup_lub` — 連続性（上限公理）

アルキメデスの性質は上限公理から定理として導出（`Real/Cast.lean`）。他は Lean 標準の `propext` /
`Classical.choice` / `Quot.sound` のみで、`MyProject.lean` の `#print axioms main` が退行を常時監査する。
実数は公理的導入で完結とし、構成的定義（Cauchy 列等）は扱わない。

```
MyProject/
  Range.lean               Range・有限和 Summation・自然数の min
  Axioms.lean              代数構造のクラス階層＋実数の公理（5 本）
  Real/                    実数の基本補題（Algebra → Order → {Div, Sup} → Abs
                           → MinMax → Summation → Cast → Interval の鎖）
  Lemmas.lean              ↑の umbrella
  Limit.lean               極限（IsLimAt）
  Continuity.lean          連続性・一様連続性・有界性
  Deriv.lean               微分（HasDerivAt）
  Integral/
    Partition.lean         分割・TaggedPartition
    Insert.lean            分割への点挿入と小区間探索
    RiemannSum.lean        リーマン和と点挿入評価
    Refine.lean            細分比較（ステップ関数の原始関数・共通エンベロープ）
    Def.lean               積分の定義・等分割・一意性
    Criterion.lean         コーシー型可積分判定（sup 構成）
    Constant/Linearity/Bounded/IntervalAdd/Monotone   基本性質
    Oscillation.lean       振動和による |f| の評価
    Continuous.lean        連続 ⇒ 可積分
    Abs.lean               |f| の可積分性・三角不等式
    Oriented.lean          向き付き積分 OIntegral
  Main.lean                微積分学の基本定理
```

## 来歴

本リポジトリは Tsudoi6（`unaoya/my_project`）から教材と参照実装を分離して作られた。
講演資料（`talk/`・`abst/`）は分離元に残っている。分離後、`MyProject/` の正本は本リポジトリ側とする。
