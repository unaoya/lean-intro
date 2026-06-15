# Ch18 微積分学の基本定理

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 一般に「微分と積分が逆」をどう述べるか
- 到達点: ftc_of_integrable（可積分仮定版——数学的に正直な最小仮定）。公理監査の総決算で本編が閉じる
- 新しい Lean 機能: なし（集大成）。監査の読み方が完成する
- コード: C15_FTC.lean（~190 行）

## 15.1 片側 FTC の主張 — 全域の F を作らない

- HasStraddleDeriv（u ≤ x ≤ v を跨ぐ差分商の両側評価）。左右微分の対は系（right/left_of_straddle）
- なぜ全域 F を作らないか——コラム「全域化の代価」（OIntegral・HasDerivAt・choice が買うのは普遍性そのもの）
- **仮定の検討（2026-06-13 決定の物語）**: FTC に本当に要るのは「部分区間ごとの可積分性」と「点 x での連続性」だけ——f の大域連続性は不要。古典的な 1 本仮定（IsIntegrable f a b）に弱めるには制限定理（可積分⇒部分区間でも可積分）が要る（発展課題）

## 15.2 核の部品を作る（誘導演習）

- 両側評価の束ね直し sum_le_const / const_le_sum（Ch9 の raw 版 → TaggedPartition 版）
- isintegral_le_of_le / le_isintegral_of_le（両側比較——非空性をここでも使う）
- Ch9 の rs_bound・Ch11 の exists_fine_partition・Ch12 の Near が全部署に揃う（const_isintegral は Ch13 済み）

## 15.3 ftc_core 精読 — 核は完全に局所的

- 連続性@x → [u,v] 全体が δ-近傍 → 両側評価を積分に通す → ε/2 の strict 化
- **試作の発見が章の主張**: hax/hxb 不使用・区間加法性も線形性も一意性も存在定理も不要（Ch13 の落ちの回収）
- 2 段構造の前段=解析の本体（choose が一度も現れない）

## 15.4 実体化 — 橋を 1 回

- ftc_of_integrable: 仮定の可積分性から Integral が証人になり、橋（Ch13）で ftc_core に渡す。解析と帳簿の分離が証明の構造として見える
- 連続関数への適用は発展部（存在定理）が可積分性を供給する——本編はここで論理的に完結

## 15.5 監査総決算

- 公理の勾配表（sum_id=[Real,instLOF] → archimedean → isintegral_id → integral_unique → ftc_core → ftc_of_integrable）
- propext / Quot.sound / Classical.choice とは何か（最後にまとめて）
- 🪟 窓: FTC はどこまで構成的か — 3 つの源泉と Bishop

## 15.6 結び

- 「信じたものは公理 5 本とカーネルだけだった」。続きへの導線: 発展部（存在定理への登山）・付録 C（mathlib への橋）・付録 D（my_ring）
