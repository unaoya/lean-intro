# はじめての Lean — Lean 4 で書く位相空間

Lean 4 の入門教材です。目的は、Lean のコードを書けるようになることではなく、
証明が機械で検査される**仕組みを納得する**ことです。
mathlib を使わず、Lean 4 の標準ライブラリだけで、位相空間の定理の証明までを読みます。

**テキスト（Web ページ）: https://unaoya.github.io/lean-intro/**

## 使い方

テキストは Web ページで読みます。そのテキストを見ながら、VS Code で
このリポジトリの Lean のファイルを開き、コードを実際に動かして確かめます。

### 準備（最初に1回だけ）

1. [VS Code](https://code.visualstudio.com/) と、その拡張機能「Lean 4」をインストールする。
   あわせて [Git](https://git-scm.com/) をインストールする。
2. VS Code を開き、「Git リポジトリのクローン」を選んで、次の URL を入力する。

       https://github.com/unaoya/lean-intro

   保存先のフォルダを選ぶと、ダウンロードが始まる。終わったら「開く」を選ぶ。
3. 「このフォルダー内のファイルの作成者を信頼しますか」と聞かれたら、「信頼する」を選ぶ
   （信頼しないと Lean が動かない）。
4. 左のエクスプローラーから **`Start.lean`** を開く。右側の Infoview に次の表示が出れば完了。

       "Lean は動いています"
       準備はできています（書き込み用の LeanIntro/MyWork/ があります）。

   初めて開いたときは、Lean の準備に数分かかることがあります。表示されるまで待ってください。

### ファイルの場所

| フォルダ | 中身 | 書き込み |
| --- | --- | --- |
| `LeanIntro/MyWork/` | **自分で使うファイル**。テキストのコードを動かし、練習を解く | する |
| `LeanIntro/Original/` | 配布された元のファイル（`MyWork/` の元） | しない |
| `LeanIntro/Solutions/` | 練習の解答 | しない |

`MyWork/` は、`Start.lean` を開いたときに `Original/` から自動で作られます。
テキストの各章と、`MyWork/` のファイルは次のように対応します。
練習の番号も、テキストと同じです。

| テキストの章 | ファイル |
| --- | --- |
| 型と項 I — 関数と依存関数型 | `01_TypesAndTerms.lean` |
| 型と命題 I — ならばと全称量化 | `02_Forall.lean` |
| 型と項 II — 帰納型と構造 | `03_InductiveTypes.lean` |
| 型と命題 II — かつ・または・否定・存在量化 | `04_Exists.lean` |
| 数学を記述する道具 | `05_MathematicalTools.lean` |
| 位相空間 | `06_Topology.lean` |
| 発展演習 | `07_Exercises.lean` |
| 発展演習 — 実数 | `08_Real.lean` |
| 発展演習 — Ascoli の定理 | `09_Ascoli.lean` |
| 発展演習 — 実数版 Arzelà–Ascoli の定理 | `10_AscoliReal.lean` |
| 発展演習 — グラフの被覆と基本群 | `11_Covering.lean` |

### 教材が更新されたとき

VS Code の左下にある同期のボタン（または「ソース管理」の「プル」）で、最新の教材を取り込みます。
`MyWork/` に書き込んだ内容はそのまま残ります。

- **新しい章**は、次に Lean のファイルを開いたときに `MyWork/` に追加されます。
- **修正された章**は、`MyWork/` の同じファイルには反映されません。どの章が更新されたかは
  `Start.lean` を開くと表示されます。最新の内容にしたい場合は、`MyWork/` のそのファイルを
  削除してから `Start.lean` を開き直すと、新しいファイルが作られます（その章の書き込みは消えます）。

## 教材を作る側の方へ

本文（解説入りの Lean ファイル）・生成スクリプト・スライドの設定などは [`dev/`](dev/README.md) にあります。
`docs/`・`LeanIntro/`・`Start.lean`・`lakefile.lean` は `dev/` から自動生成するので、直接は編集しません。
