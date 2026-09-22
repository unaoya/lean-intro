# lean-intro — Lean 4 で書く位相空間 · ミニ教材

*Lean for the Working Mathematician in the Age of AI* — AI がコードを書く時代の、働く数学者のための
Lean 入門。**Lean のコードを自分で書けるようになることは目標ではない**（それは AI に任せてよい）。

公開ページ: **https://unaoya.github.io/lean-intro/** （`src/*.lean` から自動生成）

mathlib を使わず、**Lean 4 の標準ライブラリだけ**で位相空間を組み立て、
「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」までを読む。

## 目標

- **目標1 — Lean を読めるようになる**。Lean のコードを読むとは、書かれた**項の型を推測する**ことである。
  そしてこの推測は**機械的な手順**で実行できる——だからコンピュータにも実行できる。
- **目標2 — 検証の仕組みを納得する**。項の型を推測するこの仕組みが、**定理の証明の検証に
  そのまま使える**ことを納得する。「なぜそれで証明の正しさを検証したと思えるのか」への答えがここにある。

目標1が主に `Intro1` の、目標2が `CH` の担当。`Intro2` で `Top` のための道具を揃え、
`Top` では現物の数学についてその両方を実感する。Lean を網羅的に紹介することは目的ではなく、
必要な最低限の機能しか説明しない。

## 構成

読む順は **Intro1 → CH → Intro2 → Top（→ 演習 Extra）**。

```
src/
  Intro1.lean   コードの読み方の基礎（項と型・関数・帰納型・structure）
  CH.lean       証明が検査される仕組み（Curry–Howard 対応）
  Intro2.lean   Top のための道具（class と instance・Fin・集合 Set・記法の自作・名前空間）
  Top.lean      位相空間（主定理: コンパクト → ハウスドルフの連続全単射は同相）
  Extra.lean    発展演習（位相空間の圏・自由忘却随伴・別定義との等価性・誘導位相）

  Intro1Sol.lean / CHSol.lean / Intro2Sol.lean / TopSol.lean
                本文の ✏ 練習の解答（`/-! SOL 固定ラベル:問題番号 -/` 区切り。HTML に折りたたみで埋め込まれる）
  ExtraSol.lean Extra の解答（sorry を埋めた版）

tools/lean2html.py  src/*.lean → docs/*.html の生成スクリプト（依存なし・標準ライブラリのみ）
tools/check_refs.py 固定ラベルの検査・節番号と参照番号の自動更新
docs/               生成された HTML（GitHub Pages の公開ディレクトリ。手で編集しない）
```

本文中のすべての Lean コードと Infoview 風の出力表示は、実際のコンパイラ出力で裏を取ってある。
解答ファイルも `lakefile.lean` の `roots` に入っているので、`lake build` で常に検査される。

## ビルドと生成

```bash
lake build                          # 教材の全ファイル（本文＋解答）を検査
python3 tools/lean2html.py          # src/*.lean → docs/*.html と pdf/all.pdf を再生成
python3 tools/lean2html.py --no-pdf # PDF を省いて HTML だけ再生成
```

`lake build` は `Extra.lean` の演習部分について `sorry` の警告を出す（演習なので意図どおり）。
それ以外の警告やエラーが出たら退行を疑うこと。

教材を書き換えたら `lake build` と `python3 tools/lean2html.py` を両方走らせ、
`docs/` の差分ごとコミットする（Pages の source は `main` ブランチの `/docs`）。

PDF（`pdf/all.pdf`・`.gitignore` 済み・未追跡）は HTML 生成と同時に作られる。
目次と全章を1つの印刷用ページにまとめ、headless Chrome に刷らせている
（練習の解答はすべて開いた状態、章の頭で改ページ、コードは折り返し）。
Chrome が見つからないときは PDF を飛ばして HTML 生成だけ成功する。
別の場所の Chrome/Chromium を使うなら環境変数 `CHROME` で指定する。

## 節の追加・移動と参照

節番号は並び順から自動生成する。見出しには固定ラベルを付け、参照はそのラベルを使う。
新しい見出し・参照に番号を手入力する必要はない:

```lean
/-! ## ドット記法 {#sec-Intro1.dot-notation}

説明は [節](#sec-Intro1.dependent-functions) を参照。
-/
```

`python3 tools/check_refs.py --fix` を実行すると、見出しに現在の節番号が入り、
参照の表示も `[6節](#sec-Intro1.dependent-functions)` のように更新される。
別章への参照にはファイル名も自動で付く。節を移動するときは、ラベルをそのまま残す。
`lean2html.py` も HTML 生成前に同じ同期を行い、`src/*.lean` を更新する。
同期後のソースと生成された `docs/` を一緒に管理する。

`python3 tools/check_refs.py` は読み取り専用の検査。未同期の番号や不明なラベルがあると失敗する。
解答の `SOL Intro1.dot-notation:1` も固定ラベルで対応するので、節移動時の番号修正は不要。
節内の練習ブロックを入れ替える場合は、解答側も同じ順序にする。

仕様は [tools/refcheck_spec.md](tools/refcheck_spec.md)。回帰テストは
`python3 -B -m unittest discover -s tools -p 'test_*.py'` で実行できる。

## 来歴

本リポジトリはもともと Tsudoi6（`unaoya/my_project`）から分離された、
公理 5 本からの微積分学の基本定理（FTC）の形式化と、それを素材とする入門教材のリポジトリだった。
現在はこのミニ教材の専用リポジトリであり、旧教材（`Text/` と `MyProject/`）は
コミット履歴ごと **`unaoya/lean-calculus`** へ移してある。
