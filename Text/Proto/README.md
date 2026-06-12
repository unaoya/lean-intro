# Text/Proto — 試作コード

教材本文（C01〜）に入れる前の試作場。`lake build Text` でビルド対象に含まれる
（lakefile の `.andSubmodules` により Proto/ 配下の .lean は自動でビルドされる）。

目標（第 1 マイルストーン）: リーマン積分の定義を書く。
「分割の長さを小さくする極限として定義し、それが存在するとき可積分、その値を積分とする」

設計の前提（docs/textbook_plan.md のハイブリッド方針）:
- MyProject を import しない（独立）
- 徹底脱 max/abs: 細かさは ∀ 形、評価は両側形
- 公理はフル契約（sup 込み）・階層は命名改善版
- 片側 FTC を見据える（OIntegral なし）

予定ファイル:
- Axioms.lean    — 代数階層クラス＋実数の公理＋最小インスタンス
- Sum.lean       — Range・Summation
- Partition.lean — Partition・length・TaggedPartition・RiemannSum
- Integral.lean  — IsIntegral・IsIntegrable・Integral
