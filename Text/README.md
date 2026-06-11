# Text/ — Lean 入門教材

このディレクトリに教材の実態を置く。設計書は `docs/textbook_plan.md`。

## 構成

```
Text/
  README.md        — 本ファイル（構成と執筆規約）
  book/            — 原稿（mdBook 構成）
    book.toml
    src/SUMMARY.md — 目次（2 部 16 章＋付録）
    src/chNN_*.md  — 章原稿
  C01_*.lean …     — テキスト用 Lean ソース（章ごと）
Text.lean          — umbrella（リポジトリ直下）
```

## 執筆規約

1. **独立性**: テキスト用 Lean ソースは `MyProject` を import しない。教材で構築する世界は
   このディレクトリ内で自己完結させる（`MyProject/` は「FTC が本当に証明できる」ことの
   参照実装として温存し、設計・証明の出典として参照する）。
2. **コード引用は手書きコピペ禁止**: 原稿は `{{#include ../../C01_xxx.lean:anchor}}` で
   実ファイルから抜粋する（ANCHOR コメント方式）。テキスト用ソースが唯一の出典。
3. **ビルド**: `lake build Text`（デフォルトの `lake build` には含めない。
   演習の sorry 警告を本体ビルドから隔離するため）。
4. 章ファイルの命名: `C{章番号2桁}_{内容}.lean`。演習は本文中に sorry で埋め込み、
   模範解答は各章ファイル末尾の `namespace Solutions` または `Solutions/` 配下に置く。
