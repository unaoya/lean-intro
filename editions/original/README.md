# 旧教材（1往復構成）

2往復構成に移行する前の教材を、比較・参照のために保存している。
現在の教材はリポジトリ直下の `src/`。通常の編集・ビルドについては
[ルートの README](../../README.md) を参照。

旧版の読む順は Intro1 → CH → Intro2 → Top（→ Extra）。
このディレクトリは独立した Lake プロジェクトで、旧版の `.lean` と解答を検査できる。
リポジトリ直下の `lake build` は旧版をビルドしない。

リポジトリのルートから実行する場合:

```bash
lake -d editions/original build             # 旧版の Lean を検査
python3 -B editions/original/build.py        # 旧版の HTML と PDF を再生成
python3 -B editions/original/build.py --no-pdf # 旧版の HTML だけ再生成
```

公開HTMLは `docs/original/`、PDFは `editions/original/pdf/` に出力する。
生成器は現在の教材と共有するが、本文と章構成はこのディレクトリのものを使う。
PDFと `.lake/` は再生成できるキャッシュ・成果物なので Git 管理しない。

古い公開URLに対応する `docs/intro1.html`・`docs/ch.html` は、この旧版への転送ページ。
旧版を廃止する場合は、これらの転送先と現行目次の旧版リンクも一緒に見直す。
