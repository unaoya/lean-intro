# はじめての Lean — Lean 4 で書く位相空間

この教材の目的は、Lean のコードを書けるようになることではなく、
証明が検査される**仕組みを納得する**ことである（書く仕事は AI に任せてよい）。

公開ページ: **https://unaoya.github.io/lean-intro/** （`src/*.lean` から自動生成）

mathlib を使わず、**Lean 4 の標準ライブラリだけ**で位相空間を組み立て、
「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」までを読む。

## 目標

- **目標1 — Lean を読めるようになる**。Lean のコードを読むとは、書かれた**項の型を推測する**ことである。
  そしてこの推測は**機械的な手順**で実行できる——だからコンピュータにも実行できる。
- **目標2 — 検証の仕組みを納得する**。項の型を推測するこの仕組みが、**定理の証明の検証に
  そのまま使える**ことを納得する。「なぜそれで証明の正しさを検証したと思えるのか」への答えがここにある。

型の読み方（`Intro1a`・`Intro1b`）と証明の読み方（`CH1`・`CH2`）を2回往復して学ぶ。
`Intro2` で `Top` のための道具を揃え、
`Top` では現物の数学についてその両方を実感する。Lean を網羅的に紹介することは目的ではなく、
必要な最低限の機能しか説明しない。

## 構成

読む順は **Intro1a → CH1 → Intro1b → CH2 → Intro2 → Top（→ 演習 Extra）**。

```
src/
  Intro1a.lean  項と型・関数・依存関数・暗黙引数
  CH1.lean      ならば・全称・単射の合成・証明検査の核心
  Intro1b.lean  帰納型・場合分け・再帰・structure
  CH2.lean      組と場合分け・存在・偶数と全射・等式の仕組み・検査の詳説
  Intro2.lean   Top のための道具（class と instance・記法の自作・集合 Set・名前空間）
  Top.lean      位相空間（主定理: コンパクト → ハウスドルフの連続全単射は同相）
  Extra.lean    発展演習（位相空間の圏・自由忘却随伴・別定義との等価性・誘導位相）

  Intro1aSol.lean / CH1Sol.lean / Intro1bSol.lean / CH2Sol.lean / Intro2Sol.lean / TopSol.lean
                本文の ✏ 練習の解答（`/-! SOL 固定ラベル:問題番号 -/` 区切り。HTML に折りたたみで埋め込まれる）
  ExtraSol.lean Extra の解答（sorry を埋めた版）

tools/lean2html.py  src/*.lean → 通読版・講義版の HTML/PDF（Python 標準ライブラリのみ）
tools/slides.py     共通の本文を、文字を落とさず講義用の画面・表示段階に分割
tools/slides/       講義用の HTML/CSS/JavaScript テンプレート
slides/            章ごとの区切り設定。本文のコピーや段落の連番は持たない
tools/check_refs.py 固定ラベルの検査・節番号と参照番号の自動更新
docs/               生成された HTML（GitHub Pages の公開ディレクトリ。手で編集しない）
editions/original/  2往復構成に改める前の旧版（Intro1 → CH → …）。比較・参照用
                    （`python3 editions/original/build.py` で docs/original/ に生成）
archive/plans/      採用・実施済み／不採用の構成案。現在の作業計画ではない
```

本文中のすべての Lean コードと Infoview 風の出力表示は、実際のコンパイラ出力で裏を取ってある。
解答ファイルも `lakefile.lean` の `roots` に入っているので、`lake build` で常に検査される。

## ファイルの管理

普段編集するのは `src/`（本文・解答）、`slides/`（区切り設定）、`tools/`（生成器・表示・検査）。
`docs/` は公開用の生成物なので Git に含め、`pdf/` と `.lake/` は再生成できるため Git 管理しない。
スライドの試作用コピーと `prototypes/` は廃止済み。

旧教材は [editions/original/](editions/original/README.md)、過去の計画は
[archive/](archive/README.md) に分けて保存する。どちらも通常の `lake build` の入力には含まれない。
`docs/intro1.html` と `docs/ch.html` は古い公開URLを保つ転送ページであり、重複した教材ではない。
この2ファイルは通常の生成対象外なので、生成物を整理するときも残す。

## ビルドと生成

```bash
lake build                        # 本文＋解答を Lean で検査し、2種類の HTML と2種類の PDF を生成
lake build LeanIntro              # Lean の検査だけ
python3 tools/lean2html.py         # 両形式を強制再生成（Lean の検査は別途）
python3 tools/lean2html.py --no-pdf # PDF を省いて両形式の HTML を生成
```

`lake build` は `Extra.lean` の演習部分について `sorry` の警告を出す（演習なので意図どおり）。
それ以外の警告やエラーが出たら退行を疑うこと。

教材を書き換えたら `lake build` を走らせ、
`docs/` の差分ごとコミットする（Pages の source は `main` ブランチの `/docs`）。
入力と生成物の内容が前回と一致する場合、HTML/PDF の再生成は省く。
生成物を削除・編集した場合や、本文・解答・区切り設定・生成スクリプトを編集した場合は作り直す。

| 形式 | HTML | 全章をまとめた PDF |
| --- | --- | --- |
| 通読版 | `docs/index.html` と各章 | `pdf/all.pdf` |
| 講義スライド版 | `docs/slides/index.html` と各章 | `pdf/slides.pdf` |

本文・補足・解答の原本は `src/*.lean` だけ。両形式は同じ解析・参照解決・コード着色を共有する。
講義版は左右キー・Space で進み、コードの出力は次の操作で表示する。
補足・先取りの表示は切り替えられ、解答は折りたたんである。
Intro1a の区切りは内容に合わせて設定済み。他の章も見出し・コード・表示量から自動で分割する。
設定方法は [slides/README.md](slides/README.md) を参照。

PDF（`pdf/` は `.gitignore` 済み）は headless Chrome で生成する。
通読版は解答を開いた状態でまとめ、章の頭で改ページする。
講義版は 16:9 で、出力を見せる前・後をそれぞれ1ページにする。
補足・先取りも含め、解答は問題の後の別ページに展開するため、ページ数は HTML の画面数より多い。
Chrome が見つからない・PDF 出力に失敗した場合はビルドを失敗させる。
HTML だけでよい場合は明示的に `--no-pdf` を使う。
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
