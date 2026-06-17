# Ch4 帰納型と再帰（inductive type）

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。本文未執筆。構成v7 -->

- 前章からの問い: Ch3 で依存関数（Π 型）を見た。型理論の2原始のもう一本——帰納型の**使い方**（除去規則 recursor）を正面から扱う
- 到達点: recursor の型を読め、パターンマッチが recursor の糖衣であることを確認し、論理結合子が全て帰納型であることを `#print` で実機確認できる。Ch3 の依存関数と合わせて「論理の2原始」が揃う
- 新しい Lean 機能: `Nat.rec`・`#check @T.rec`・`#print`・構造的再帰 `| 0 | n+1`・`Nat.brecOn`
- コード: Ch4_InductiveType.lean（eliminators・sum_to・recursor_reveal・ch_punchline）

## 4.1 帰納型を「使う」 — recursor（除去規則）

```lean
{{#include Ch4_InductiveType.lean:eliminators}}
```

どの帰納型にも**導入規則**（構成子＝値を作る）と**除去規則**（recursor＝値を使う）がある。`#check @Or.rec` と `#check @Nat.rec` を並べると、**再帰の有無が cases（Or・有限型 Three）と induction（Nat）を分ける**のが型から直接見える:

- `Or.rec` は「`a → C` と `b → C` を受け取り `a ∨ b → C` を返す」——IH が無い（cases）
- `Nat.rec` は「zero での `motive 0` と、succ の段での `motive n → motive (n+1)` を受け取る」——`motive n` が帰納法の仮定 IH（Nat が再帰的な型だから）

## 4.2 sumTo — Nat 上の再帰関数

```lean
{{#include Ch4_InductiveType.lean:sum_to}}
```

`Nat.rec` の最小の実演として `sumTo n = 0+1+…+n` を書く。

- zero で 0（基底）、succ で「前の結果 `sumTo n` に n+1 を足す」（再帰段）
- 再帰方程式は `rfl` で計算される（`sumTo 3 = 6`）——defeq の予告
- ねらい: いきなり依存な Summation（第II部 Ch5）は複雑なので、まず Nat→Nat の素朴な再帰で zero/succ の形を体に入れる

## 4.3 パターンマッチの種明かし — 再帰（A）と依存関数型（B）の切り分け

```lean
{{#include Ch4_InductiveType.lean:recursor_reveal}}
```

**2 つの問題を分ける**:
- **(A) 再帰**: succ の段で「前の値 `ih`」を使うこと。sumTo は**これだけ**——戻り値の型 `Nat` は n に依らない
- **(B) 依存関数型の項作り**: `(n : Nat) → C n` の項を zero（`C 0` の項）と succ（`C n` の項 `ih` から `C (n+1)` の項）で組むこと＝`Nat.rec` の **motive** `C`。sumTo は `C n = Nat`（定数）なので (B) が退化し (A) だけが純粋に見える

**パターンマッチ `| 0 | n+1` は `Nat.rec` の糖衣**。`#print sumTo` すると `fun x => Nat.brecOn x sumTo._f`——`Nat.rec` から作られる「強帰納」版 `Nat.brecOn` に翻訳されている。

生の `Nat.rec` 直書き版 `sumTo'` を並べると、外延的には同じ関数だが定義的には別物（`brecOn ≠ rec`）。具体値 `sumTo 3 = sumTo' 3` は `rfl`、だが一般の n は defeq で繋がらず `sumTo n = sumTo' n` は induction で証明する。

🪟 窓: 「計算で一致するのに rfl で繋がらない」＝**defeq と命題等式「=」の違い**の最初の手応え（第II部 Ch8 の「2 つの等しさ」への布石）

## 4.4 論理結合子の正体 — #print 種明かし（2原始の完成）

```lean
{{#include Ch4_InductiveType.lean:ch_punchline}}
```

`#print And` / `Or` / `Exists` / `False` で「論理結合子はすべて帰納型（構成子＋recursor）」を実機確認する。Ch3 と合わせて:

**論理 = 依存関数（→ ∀ ¬・Ch3）＋ 帰納型（∧ ∨ ∃ ⊥ = ・Ch4）**——型理論の2原始の導入/除去規則だけで尽きる（Ch1 の CH 表のパンチラインを回収）。

## 引き

- 「型の2原始（依存関数・帰納型）が揃い、論理がこの2つで尽きることを実機確認した。最後に——等式の証明も项である。それを calc で 1 本ずつ繋ぐ（Ch5）」
