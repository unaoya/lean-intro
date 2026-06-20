# Ch2 命題 — 論理結合子の導入則と除去則

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。本文未執筆。構成v9（2026-06-17 再編） -->

- 前章からの問い: Ch1 で型の構成（×・⊕・→・Π・Subtype・Σ・帰納型）とその「導入/除去」を見た。命題の論理結合子はどう対応するのか
- 到達点: 命題の論理結合子（∧・∨・→・¬・∀・∃）を、Ch1 の型構成と**一対一でパラレル**に並べ、各結合子の「導入則（証明を作る）」と「除去則（証明を使う）」を手で書ける——これが Curry-Howard 対応（命題＝型・証明＝項）の核心
- 新しい Lean 機能: `And.intro`・`Or.inl`/`Or.inr`・`fun`（→/∀ の導入）・`⟨witness, proof⟩`（∃ の導入）・`.1`/`.2`・`.elim`・`False.elim`
- コード: Ch2_Proposition.lean（and_intro_elim・or_intro_elim・imp_intro_elim・neg・forall_intro_elim・exists_intro_elim・exercises）
- ★ **縦糸**: 「命題＝型・証明＝項（Curry-Howard）」をここで型構成とパラレルに体感する。後で `intro`/`cases`/`⟨⟩` が型と命題の**両方**で同じタクティクとして効く理由が明確になる

## はじめに — 命題と型のパラレル

Ch1 で見た積・和・関数型・依存関数型・Subtype・Σ は、命題の論理結合子と**一対一で対応**している。本章はその対応表を一行ずつ手で確認する。

最初の証明:

```lean
{{#include Ch2_Proposition.lean:my_first_theorem}}
```

命題 `0 = 0` の証明 `Eq.refl 0` は「型 `0 = 0` の項」だ——証明＝項の最小例。

`Prop` 型がある。`Prop` 型の項はやはり型になる。
これが命題に対応する型。 `0 = 0` も型である。

## 2.1 かつ ∧ ↔ 積 ×（Ch1 §1.1）

∧ は Ch1 の積 `×` とパラレル。導入則 = `And.intro`（`⟨_, _⟩`）、除去則 = `.1`/`.2`。


```lean
{{#include Ch2_Proposition.lean:and_intro_elim}}
```

メモ：導入則は要するにAかつBを証明するにはどうするかということ。
これはAの証明とBの証明を与えればいい。
つまりAの証明のBの証明の組を与えればいい。
除去則はAかつBが仮定にあるときに何ができるかということ。
Aを使うこともできるしBを使うこともできる。

`and_swap` は「ペアの成分を入れ替える」操作と全く同じ型推論で動く。

## 2.2 または ∨ ↔ 和 ⊕（Ch1 §1.2）

∨ は Ch1 の和 `⊕` とパラレル。導入則 = `Or.inl`/`Or.inr`、除去則 = `.elim`（場合分け）。∨ は非再帰なので帰納法の仮定（IH）は無い（「除去則=recursor」「再帰なら IH=induction」の全体像は Ch4）。

```lean
{{#include Ch2_Proposition.lean:or_intro_elim}}
```

メモ：導入則は要するにAまたはBを証明するにはどうするかということ。
これはAの証明かBの証明のどちらかを与えればいい。
つまりAを証明すればAまたはBを証明したことになるし、Bでも同様。
除去則はAまたはBが仮定にあるときに何ができるかということ。
（AまたはB）ならばCを示すには、AならばCとBならばCを示せばいい。

## 2.3 ならば → ↔ 関数型 α → β（Ch1 §1.3）

→ は Ch1 の関数型とパラレル。導入則 = `fun`（λ抽象）、除去則 = 適用（modus ponens は関数適用）。

```lean
{{#include Ch2_Proposition.lean:imp_intro_elim}}
```

## 2.4 否定 ¬ ↔ → False

`¬A = A → False`（False への関数）。導入/除去は `→` と同じ（fun・適用）。

```lean
{{#include Ch2_Proposition.lean:neg}}
```

`False` は構成子 0 の帰納型——除去 `False.elim` = 爆発律（全体像は Ch4）。

## 2.5 すべて ∀ ↔ 依存関数型 Π（Ch1 §1.3）

`∀ x, P x` は依存関数型 `(x : α) → P x`（codomain が `Prop`）。導入=`fun`、除去=適用。Ch1 の Π とパラレル。

```lean
{{#include Ch2_Proposition.lean:forall_intro_elim}}
```

## 2.6 存在 ∃ ↔ Subtype / 依存和 Σ（Ch1 §1.3b/§1.3c）

∃ は Ch1 の Subtype/Σ とパラレル。導入則 = `⟨witness, proof⟩`、除去則 = `.elim`（証拠を取り出して使う）。

```lean
{{#include Ch2_Proposition.lean:exists_intro_elim}}
```

違いは住む宇宙だけ: `∃ x, p x` は**証明（Prop）** で証人を計算的に取り出せない。`{x // p x}` は**データ（Type）** で `.val` で値が取り出せる（Ch1 の Subtype）。

## 演習

```lean
{{#include Ch2_Proposition.lean:exercises}}
```

- `and_assoc'`: `(A ∧ B) ∧ C → A ∧ (B ∧ C)`（∧ の結合性）
- `and_or_distrib`: `A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)`（分配律・`.elim` で場合分け）

## まとめ — Curry-Howard 対応表

| 命題 | 型（Ch1） | 導入則 | 除去則 |
|---|---|---|---|
| A ∧ B | `Prod ×`（§1.1） | `And.intro` / `⟨,⟩` | `.1` / `.2` |
| A ∨ B | `Sum ⊕`（§1.2） | `Or.inl` / `Or.inr` | `.elim`（cases） |
| A → B | 関数型 `→`（§1.3） | `fun` | 適用 `f a` |
| ¬ A | `A → False` | `fun` | 適用 |
| ∀ x, P x | 依存関数 Π（§1.3） | `fun` | 適用 |
| ∃ x, P x | `Subtype` / `Σ`（§1.3b/c） | `⟨witness, proof⟩` | `.elim` |

帰納型の残り（∧ ∨ ∃ ⊥ = が全て帰納型）の `#print` 確認は Ch4 でまとめて行う。

## 引き

- 「命題の論理結合子が型の構成とパラレルであることを確認した。次は——等式の証明も項だ。複数の等式を 1 本ずつ繋ぐ calc（Ch3）を習得し、Ch4 の和の公式への道具を整える」
