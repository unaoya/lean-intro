# 発展 4 フィルターで統一する — IsLimAt・ContinuousAt・IsIntegral は同じ概念

<!-- 下書き（配置設計版）。旧 付録 C.3 を発展部へ移動（2026-06-16）。本編・他発展部に依存しない読み物 -->

- 役割: 本書の「3 種の ε-δ」（IsLimAt・ContinuousAt・IsIntegral）が、**フィルター（Filter）の言葉で同一概念の 3 インスタンス**であることを見せる。mathlib への最短の橋

## E4.1 Filter と Tendsto を自作

- Filter（上方閉な集合族）＋ Tendsto を 50〜100 行で自作する（core のみ）

## E4.2 3 つが同じになる

- IsLimAt・ContinuousAt・IsIntegral が「ある Filter に沿った Tendsto」の特殊化——**同値定理 3 本**を演習で示す
- 「3 種の ε-δ」の縦糸がここで完結する

## E4.3 mathlib への橋

- mathlib の `Filter`/`Tendsto`/`BoxIntegral` への最短の接続。次の一冊（あとがき）へ繋ぐ
