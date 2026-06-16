# あとがき — 次の一冊へ

<!-- 下書き（配置設計版）。旧 付録 C.4 を巻末へ移動（2026-06-16） -->

- 本書は **公理から FTC まで**（柱 A: 数学のブラックボックスゼロ）と、**タクティク・CH 対応の仕組み**（柱 B: 道具を開ける）を一本で貫いた

## 次の一冊

- **Mathematics in Lean (MIL)** を推薦する——本書との**読み替え表**つき:
  - 本書の自作 `my_ring`/`my_abel` ↔ mathlib の `ring`/`abel`
  - 本書の自作 Real 公理（`LinearOrderedField`）↔ mathlib の `ℝ`（Cauchy 列の商で構成）
  - 本書の `Module`・`IsLinearMap` ↔ mathlib の `Module`・`LinearMap`
  - 本書の `Range`/`Summation` ↔ mathlib の `Fin`/`Finset.sum`
- mathlib の世界へ: 本書で「**中身を作った**」道具（ring・Filter・Module）が、mathlib では完成品として揃っている。**作った経験が、借りるときの理解になる**——それが本書（柱 B）の狙いだった
