# Ch7 sorry を埋める道具 II — defeq・calc・帰納法

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->

- 前章からの問い: 等しさには 2 種類あるのか
- 到達点: calc が設計できる。帰納法で Σ 補題コーパスが証明できる
- 新しい Lean 機能: defeq と rw の構文性・rfl/show・calc・Trans・induction・omega
- コード: C07_Induction.lean（Σ補題コーパス 9 本＋Trans。Proto: FTCCore§Σ＋InsertBound§1＋Refine§3 を再配列 → ~120 行）

## 7.1 等しさは 2 種類ある

- `a + -b = a - b := rfl` が通るのに rw は区別する——defeq（計算で同じ）と構文（見た目が同じ）
- show による defeq の言い換え。🪟 窓: 正規化と `#reduce` — 証明の簡約

## 7.2 種明かし: rw の正体

- `Eq.mpr`＋motive（congrArg）。`#print` で rw 証明の項を見る——構文的でなければならない理由が機構で腑に落ちる
- **rw の罠 2 種（試作の実戦例）**: ① 意図しない部分項を先に潰す → 引数明示で回避 ② パターン捕獲（q を (q+q)/2 に書き換えると (p+q) 内の q も巻き込む）→ 独立補題への切り出しで回避

## 7.3 calc の設計

- Trans インスタンス（le-le / lt-le / le-lt / Eq-le）。不等式の鎖の組み立て方

## 7.4 帰納法 — recursor の糖衣

- induction タクティク＝Ch4 の recursor 適用（種明かしの回収）。omega（Nat の決定手続き——正体は Ch10/付録 D への伏線）

## 7.5 Σ 補題コーパス

- 線形性（additive/smul/neg）・順序（nonneg/le）・congr（**rw は束縛子の下に入れない**——限界と congruence 補題という回避策）
- 添字の付け替え `fun k => f ⟨k.val, …⟩`——本書で最も手のかかるパターンの訓練場

## 7.6 ボス戦: telescope_sum

- 最初の本格的帰納法証明。Σ(g(i+1)−g(i)) = g(n)−g(0)（→ Ch9 length_sum・Ch14 中点和の部品）

## 演習

- コーパス 9 本のうち本文精読 3 本・残り sorry 埋め

## 引き

- 「道具は揃った。Ch5 の sorry を消しに行こう——そして 2 等分・n 等分へ」
