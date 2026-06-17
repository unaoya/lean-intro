# Ch5 calc — 等式の証明も項

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。本文未執筆。構成v7 -->

- 前章からの問い: Ch4 で帰納型と再帰を見た。等式 `a = b` も命題＝型・その証明も項だった。複数の等式を 1 本ずつ繋ぐには？
- 到達点: calc 記法を読み書きでき、calc が実は `Eq.trans` の連鎖（1個の項）であることを確認できる。「記法はみな項を作る糖衣」という CH 対応の見方が一巡する
- 新しい Lean 機能: `calc`（term mode）・`Eq.trans`（`.trans`）・`congrArg`・`Nat.add_assoc`・`Nat.add_comm`
- コード: Ch5_Calc.lean（calc_warmup・nat_interchange・sum_to_formula・calc_is_term）

## 5.1 calc ウォームアップ — 等式を 1 本ずつ繋ぐ（term mode）

```lean
{{#include Ch5_Calc.lean:calc_warmup}}
```

等式 `a = b` も命題＝型・その証明も項。`calc` は複数の等式を 1 本ずつ繋ぐ記法で、`by` を使わない**term mode** のまま書く——各 `:=` の右にその 1 行を正当化する証明（項）を置く。

素材は Nat だけ（Real 不要）。`congrArg (fun x => …)` で「等式を文脈に持ち上げる」のが calc の各段の典型パターンだ。

## 5.2 交換則 — Nat.add_assoc と Nat.add_comm だけで

```lean
{{#include Ch5_Calc.lean:nat_interchange}}
```

`nat_interchange`: `(a+b)+(c+d) = (a+c)+(b+d)` を `Nat.add_assoc`・`Nat.add_comm` だけで繋ぐ。5 段の calc で等式の連鎖を組む実習。

**演習**: 乗法版 `(a*b)*(c*d) = (a*c)*(b*d)` を同じ calc で（`namespace Solutions` に解答）。

伏線: この式を第II部 Ch3 で「**任意の可換モノイド**」について 1 回証明し、`+` と `*` の両方に効かせる（具体→抽象）。

## 5.3 和の公式 2·sumTo n = n(n+1) を calc で

```lean
{{#include Ch5_Calc.lean:sum_to_formula}}
```

Ch4 で定義した `sumTo` の閉じた式を **tactic なし・term（calc）**で証明する。

- sumTo の再帰方程式に沿った帰納（`| 0 | n+1`）で各段を calc で繋ぐ
- 分配 `Nat.left_distrib` → 帰納法の仮定 `congrArg` → 括り直し `Nat.add_mul` → 可換 `Nat.mul_comm`
- 最後は `n+2` と `(n+1)+1` が **defeq** なので 1 段減る
- 除法版 `sumTo n = n(n+1)/2` も term で従う（Nat の `/` は切り捨てなので「先に 2 を払う」のが定石）

## 5.4 calc も項を作る — calc ≡ Eq.trans の連鎖

```lean
{{#include Ch5_Calc.lean:calc_is_term}}
```

2 段の calc は `Eq.trans`（`.trans`）の連鎖に **rfl で等しい**——calc が作っているのは 1 個の等式の項そのもの。

だから §5.3 の `two_mul_sumTo` の calc も、各段を `Eq.trans` でつないだ **1 個の等式の項**にすぎない。

- **パターンマッチ**（→ `Nat.brecOn`・Ch4）
- **calc**（→ `Eq.trans`）
- **（後の）タクティク**（→ 項の後書き補助・第II部 Ch7）

——記法はみな「項を作る」ための糖衣。これが Curry-Howard 対応：「証明＝項」の現れだ。

## 引き

- 「第一部（命題=型・証明=項）の枠組みが一巡した。次は——等式の証明が書けるようになった型と構造を**実数の数学**に乗り移す。第II部では実数の公理を読み、リーマン和を定義する（第II部 Ch3 から）」
