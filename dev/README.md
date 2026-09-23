# はじめての Lean — 開発用（dev/）

教材を作る側のためのディレクトリ。受講者向けの説明はリポジトリ直下の [README](../README.md)。

このディレクトリは独立した Lake プロジェクトで、解説入りの本文（正本）と、そこから
公開ページ・受講者用ファイルを作る道具をまとめている。コマンドはすべて `dev/` で実行する。

| 生成物 | 場所 | 作る道具 |
| --- | --- | --- |
| 公開ページ（通読版・講義スライド） | リポジトリ直下の `docs/` | `tools/lean2html.py` |
| 受講者用プロジェクト（`LeanIntro/Original`・`Solutions`、`Start.lean`、`lakefile.lean`） | リポジトリ直下 | `tools/student.py`（lean2html から呼ばれる） |
| PDF | `dev/pdf/`（Git 管理外） | `tools/lean2html.py` |

公開ページ: **https://unaoya.github.io/lean-intro/** （`dev/src/*.lean` から自動生成）

mathlib を使わず、**Lean 4 の標準ライブラリだけ**で位相空間を組み立て、
「コンパクト空間からハウスドルフ空間への連続全単射は同相写像である」までを読む。

## 目標

- **目標1 — Lean を読めるようになる**。Lean のコードを読むとは、書かれた**項の型を推測する**ことである。
  そしてこの推測は**機械的な手順**で実行できる——だからコンピュータにも実行できる。
- **目標2 — 検証の仕組みを納得する**。項の型を推測するこの仕組みが、**定理の証明の検証に
  そのまま使える**ことを納得する。「なぜそれで証明の正しさを検証したと思えるのか」への答えがここにある。

型と項を学ぶ第1・3章と、型と命題を学ぶ第2・4章の順に進む。
第5章で数学を記述する道具を揃え、第6章で位相空間の定義から定理の証明までを読む。
Lean を網羅的に紹介することは目的ではなく、
必要な最低限の機能しか説明しない。

## 構成

本文は `dev/src/` にあり、ファイル名の番号順に読む。

| ファイル | 章タイトル・扱う内容 |
| --- | --- |
| `01_TypesAndTerms.lean` | 型と項 I — 関数と依存関数型 |
| `02_Forall.lean` | 型と命題 I — ならばと全称量化 |
| `03_InductiveTypes.lean` | 型と項 II — 帰納型と構造 |
| `04_Exists.lean` | 型と命題 II — かつ・または・否定・存在量化 |
| `05_MathematicalTools.lean` | 数学を記述する道具 |
| `06_Topology.lean` | 位相空間 |
| `07_Exercises.lean` | 発展演習 |
| `08_Ascoli.lean` | 発展演習 — Ascoli の定理 |
| `09_Covering.lean` | 発展演習 — グラフの被覆と基本群 |

解答は同じ名前に `Sol` を付けたファイルに置く。
第1〜6章の ✏ 練習の解答は `/-! SOL 固定ラベル:問題番号 -/` で区切り、HTML に埋め込む。
番号で始まるモジュール名は Lean では `import «01_TypesAndTerms»` のように書く。
HTML は小文字の同名ファイル、スライド設定は `slides/01_TypesAndTerms.json` などに対応する。

```
tools/lean2html.py  src/*.lean → 通読版・講義版の HTML/PDF（Python 標準ライブラリのみ）
tools/slides.py     共通の本文を、文字を落とさず講義用の画面・表示段階に分割
tools/slides/       講義用の HTML/CSS/JavaScript テンプレート
slides/            章ごとの区切り設定。本文のコピーや段落の連番は持たない
tools/check_refs.py 固定ラベルの検査・節番号と参照番号の自動更新
tools/student.py    src/*.lean → 受講者用プロジェクト（リポジトリ直下）。ひな形は tools/student/
../docs/            生成された HTML（GitHub Pages の公開ディレクトリ。手で編集しない）
../LeanIntro/       受講者用ファイル（Original/・Solutions/）。自動生成。MyWork/ は受講者の手元で作られる
```

受講者用ファイルは、本文から地の文・docstring・出力の表示ブロックを除き、コード・節見出し・
練習の問題文（番号はテキストと同じ通し番号）を残したもの。地の文の中のコード例はコメントアウトして残す。
受講者用の `lakefile.lean` は、VS Code で開いたときに `LeanIntro/MyWork/` を `Original/` から
自動で作る（既存のファイルは上書きしない）。章の一覧を lakefile に書き込むので、章を追加すると
lakefile が変わり、受講者の手元で新しい章が追加される。配布後に `Original/` を修正しても
受講者の `MyWork/` には反映されず、`Start.lean` が「更新された章」として知らせる。

本文中のすべての Lean コードと Infoview 風の出力表示は、実際のコンパイラ出力で裏を取ってある。
解答ファイルも `lakefile.lean` の `roots` に入っているので、`lake build` で常に検査される。

## ファイルの管理

普段編集するのは `src/`（本文・解答）、`slides/`（区切り設定）、`tools/`（生成器・表示・検査）。
`docs/` と受講者用プロジェクト（直下の `LeanIntro/`・`Start.lean`・`lakefile.lean`）は生成物だが、
公開・配布するので Git に含める。`pdf/` と `.lake/` は再生成できるため Git 管理しない。

古い公開 URL（`intro1.html`・`ch.html`、改名前の `intro1a.html`・`ch1.html` など）は、
新しい章への転送ページとして生成する（`LEGACY_CHAPTERS`）。
スライドの旧URLはページ位置と表示段階を引き継ぐ。本文の固定節ラベルは改名後も変えない。

## ビルドと生成

```bash
# すべて dev/ で実行する
lake build                        # 本文＋解答を Lean で検査し、2種類の HTML と2種類の PDF、受講者用ファイルを生成
lake -d .. build                  # 生成した受講者用プロジェクト（直下）がコンパイルできるか検査
lake build LeanIntro              # Lean の検査だけ
python3 tools/lean2html.py         # 両形式を強制再生成（Lean の検査は別途）
python3 tools/lean2html.py --no-pdf # PDF を省いて両形式の HTML を生成
```

`lake build` は `07_Exercises.lean` の演習部分について `sorry` の警告を出す（演習なので意図どおり）。
それ以外の警告やエラーが出たら退行を疑うこと。

教材を書き換えたら `lake build` と `lake -d .. build` を走らせ、
`docs/` と受講者用ファイルの差分ごとコミットする（Pages の source は `main` ブランチの `/docs`）。
入力と生成物の内容が前回と一致する場合、HTML/PDF の再生成は省く。
生成物を削除・編集した場合や、本文・解答・区切り設定・生成スクリプトを編集した場合は作り直す。

| 形式 | HTML | 対象章をまとめた PDF |
| --- | --- | --- |
| 通読版 | `../docs/index.html` と各章 | `pdf/all.pdf` |
| 講義スライド版 | `../docs/slides/index.html` と各章 | `pdf/slides.pdf` |

本文・補足・解答の原本は `src/*.lean` だけ。両形式は同じ解析・参照解決・コード着色を共有する。
スライド版は 01_TypesAndTerms・02_Forall・03_InductiveTypes・04_Exists・05_MathematicalTools の5章を対象とする。
冒頭の目的・目標・構成も通読版と共有し、`docs/slides/index.html` とスライドPDFの冒頭に含める。
その区切りは `slides/Index.json` で設定する。「講義の各章」のリンクから各章のスライドへ進める。
06_Topology・07_Exercises・08_Ascoli・09_Covering は通読版にのみ含める。
対象外の章は `tools/lean2html.py` の `SLIDE_EXCLUDED_CHAPTERS` で管理する。
講義版は左右キー・Space で進み、コードの出力は次の操作で表示する。
スライドの HTML・PDF は、標準では補足・先取りを省略する。解答は各問題の直後に追加表示する。
補足・先取りも含める場合は `python3 tools/lean2html.py --include-slide-notes` を実行する。
この場合は HTML に補足・先取りの表示切替が付く。次の `lake build` では標準の省略版に戻る。
5章すべてのページ境界を、内容のまとまりに合わせて JSON に設定している。
同じ話題をできるだけ1ページにまとめ、段落・コードブロック・箇条書き・表を順に表示する。
本筋のページを生成器が自動で分割し直すことはない。
ページ全体の高さに応じて上下の配置と行間・余白を調整し、段階表示でも本文の位置を保つ。
設定方法は [slides/README.md](slides/README.md) を参照。

PDF（`pdf/` は `.gitignore` 済み）は headless Chrome で生成する。
通読版は解答を開いた状態でまとめ、章の頭で改ページする。
講義版は 16:9 で、HTML の各表示段階をそれぞれ1ページにする。
問題と解答が同じ画面に収まる場合も表示段階ごとに刷るため、PDF のページ数は HTML の画面数より多い。
通読版は補足・先取りを含む。スライドPDFの補足・先取りは上記オプションを付けた場合に含む。
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
