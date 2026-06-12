# Ch16 微積分学の基本定理

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 微分と積分が逆であることをどう述べ、どう証明するか
- 到達点: ftc（実体化版）。公理監査の総決算で本書が閉じる
- 新しい Lean 機能: なし（集大成）。監査の読み方が完成する
- コード: C16_FTC.lean（Proto: FTC＋FTCCore 核部＋Main 後半 → ~380 行）

## 16.1 片側 FTC の主張 — 全域の F を作らない

- HasStraddleDeriv（u ≤ x ≤ v を跨ぐ差分商の両側評価）。左右微分の対は系（right/left_of_straddle）
- なぜ全域 F を作らないか——コラム「全域化の代価」（OIntegral・HasDerivAt・choice が買うのは普遍性そのもの）

## 16.2 核の 3 部品を作る（誘導演習）

- const_isintegral（定数の積分）・isintegral_le_of_le / le_isintegral_of_le（両側比較——非空性をここでも使う）
- Ch9 の rs_bound・Ch11 の exists_fine_partition・Ch12 の Near が全部署に揃う

## 16.3 ftc_core 精読 — 核は完全に局所的

- 連続性@x → [u,v] 全体が δ-近傍 → 両側評価を積分に通す → ε/2 の strict 化
- **試作の発見が章の主張**: hax/hxb 不使用・区間加法性も線形性も一意性も存在定理も不要（Ch13 の落ちの回収）
- 2 段構造の前段=解析の本体（choose が一度も現れない）

## 16.4 実体化 — 橋を 1 回

- 連続 ⇒ 可積分（Ch15）で Integral が証人になり、橋（Ch13）で ftc_core に渡す。解析と帳簿の分離が証明の構造として見える

## 16.5 監査総決算

- 公理の勾配表（sum_id=[Real,instLOF] から ftc=全公理まで——どの数学がどの公理を要求したか一望）
- propext / Quot.sound / Classical.choice とは何か（最後にまとめて）
- 🪟 窓: FTC はどこまで構成的か — 3 つの源泉と Bishop

## 16.6 結び

- 「信じたものは公理 5 本とカーネルだけだった」。mathlib へ（付録 C）・フィルター統一の発展節・次の一冊（MIL）
