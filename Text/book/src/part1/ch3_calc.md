# Ch3 calc — 等式の証明も項

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。本文未執筆。構成v9（2026-06-17 再編） -->

- 前章からの問い: Ch2 で命題の論理結合子（∧∨→¬∀∃）が型の構成とパラレルであることを見た。等式 `a = b` も命題＝型・その証明も項だった。複数の等式を 1 本ずつ繋ぐには？
- 到達点: calc 記法を読み書きでき、calc が実は `Eq.trans` の連鎖（1個の項）であることを確認できる。「記法はみな項を作る糖衣」という CH 対応の見方を calc で体感する。この章の calc は Ch4 の和の公式（sum_to_formula）の**道具立て**になる
- 新しい Lean 機能: `calc`（term mode）・`Eq.trans`（`.trans`）・`congrArg`・`Nat.add_assoc`・`Nat.add_comm`
- コード: Ch3_Calc.lean（calc_warmup・nat_interchange・calc_is_term）

## 3.1 calc ウォームアップ — 等式を 1 本ずつ繋ぐ（term mode）

```lean
{{#include Ch3_Calc.lean:calc_warmup}}
```

等式 `a = b` も命題＝型・その証明も項。`calc` は複数の等式を 1 本ずつ繋ぐ記法で、`by` を使わない**term mode** のまま書く——各 `:=` の右にその 1 行を正当化する証明（項）を置く。

素材は Nat だけ（Real 不要）。`congrArg (fun x => …)` で「等式を文脈に持ち上げる」のが calc の各段の典型パターンだ。

## 3.2 交換則 — Nat.add_assoc と Nat.add_comm だけで

```lean
{{#include Ch3_Calc.lean:nat_interchange}}
```

`nat_interchange`: `(a+b)+(c+d) = (a+c)+(b+d)` を `Nat.add_assoc`・`Nat.add_comm` だけで繋ぐ。5 段の calc で等式の連鎖を組む実習。

**演習**: 乗法版 `(a*b)*(c*d) = (a*c)*(b*d)` を同じ calc で（`namespace Solutions` に解答）。

伏線: この式を第II部 Ch3 で「**任意の可換モノイド**」について 1 回証明し、`+` と `*` の両方に効かせる（具体→抽象）。

## 3.3 calc も項を作る — calc ≡ Eq.trans の連鎖

```lean
{{#include Ch3_Calc.lean:calc_is_term}}
```

2 段の calc は `Eq.trans`（`.trans`）の連鎖に **rfl で等しい**——calc が作っているのは 1 個の等式の項そのもの。

- **パターンマッチ**（→ `Nat.brecOn`・Ch4）
- **calc**（→ `Eq.trans`）
- **（後の）タクティク**（→ 項の後書き補助・第II部 Ch7）

——記法はみな「項を作る」ための糖衣。これが Curry-Howard 対応：「証明＝項」の現れだ。

## 引き

- 「calc の基本が身についた。次は——帰納型と再帰（Ch4）で sumTo を定義し、この calc を使って和の公式 sum_to_formula を証明する（第一部の最終目標）」
