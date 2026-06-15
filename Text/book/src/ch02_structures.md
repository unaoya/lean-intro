# Ch2 数学的構造と class の仕組み

<!-- 下書き（配置設計版）: 節立てと内容の配置メモ。machinery 章（2026-06-15 スワップで Ch3 から入替） -->

- 前章からの問い: 実数とは何か（→ 実数は「構造」として与えられる。まず構造とは何か・Lean でどう書くかを掴む）
- 到達点: 「構造＝データ・class＝自動で見つかる構造」の見方を得る。一般構造で 1 回証明して複数インスタンスに適用する経験
- 新しい Lean 機能: structure キーワード・署名の読み方・暗黙引数（読む）・class（最小: 自動解決される構造）
- コード: C02_Structures.lean（structure_as_data・general_proof・And は structure）

> 執筆メモ（ユーザー・relocate 元 ch02）:
> - 集合とその上の群構造という定義をする。より正確には集合とその上の演算と結合律・単位律・逆元。
> - これらを性質として述べるか、構造とするか。普段はあまり区別しないが、構造とした方がいい？（選択公理との関係？ → 深い理由は後章、ここは予告）
> - Add や Neg・AddCommGroup・Zero などは全て型である。集合っぽくいうと、X に対して X 上の適切な演算の集合を対応させる写像。同じ集合でも群構造の定めかたはたくさんある。
> - Nat は既存のものがある。Nat にモノイド構造を載せてみよう。素朴には加法モノイドと乗法モノイドが定義できる（→ §2.3 の general_proof）。

## 2.1 型は集合、構造はデータ

- Ch1 では型は「命題」だった。ここでは型は「住人を持つ集合（carrier）」の顔
- 構造＝データ: 演算と「それが法則を満たす証明」を 1 つの項に束ねたもの——**Ch1 の `⟨h.2, h.1⟩` ペアの大きい版**。`structure` キーワードでこういうレコード型を作れる
- 署名の読み方（∀・→・暗黙引数 `{}`）は構造のフィールドを読むのに要る分だけここで

## 2.2 「α 上の構造」は型・住人が構造ひとつ（ANCHOR `structure_as_data`）

- `#check (Add Nat)` → `Add Nat : Type`。`Add α` の住人は「α 上の二項演算ひとつ」
- `example : Add Nat := ⟨Nat.add⟩` と `⟨fun a b => a*b⟩`——乗法すら住人になれる。**Add は法則を持たない**から
- 同じ集合 Nat に構造は複数載る。法則は構造の側（次節）が束ねる

## 2.3 一般構造で 1 回証明する（ANCHOR `general_proof`）

- `structure CommMonoidStr (α) where op; op_assoc; op_comm`（演算＋法則の証明を束ねる）
- 交換則 `(a⋆b)⋆(c⋆d) = (a⋆c)⋆(b⋆d)` を結合律＋可換律**だけ**から証明（公理ではない・C06 の add_four_comm と同型）
- `natAdd`・`natMul`（Nat の 2 つの可換モノイド・法則は core の定理を渡すだけ）→ 1 回の証明が `+` と `*` の両方に効く（`interchange natAdd …` が具体形に defeq 一致）
- **抽象化の威力**: structure を引数に渡すだけ——instance も class もまだ要らない

## 2.4 class＝自動で見つかる構造（最小導入）

- `M.op a b` は煩雑。ℝ では `a + b` と書きたい→それを叶えるのが `class`／`instance`＝「構造を Lean が自動で探して渡す」仕組み。だから次章 ℝ の公理は `class` で書く
- ⚠ ここは**最小限**: 「class = 自動で見つかる structure」だけ。解決の深い機構・`(2:Real)` エラー・ダイヤモンド事件は後章（Ch3 で軽く観察、深い話と diamond は Ch8）

## 2.5 種明かし: `⟨⟩` も structure だった（ANCHOR `and_is_structure`）

- `#print And` → And は structure。Ch1 で使った `⟨h.2, h.1⟩` の `⟨⟩` の正体（Ch4 帰納型・Ch5 Partition へ繋ぐ）

## 演習

- `Add Nat` の住人をもう 1 つ作る・`CommMonoidStr` の別インスタンス（Bool の ∧/∨ 等）・交換則を別の構造に適用
- structure 設計: `n` を implicit にできるか（Ch4 Summation への布石）

## 引き

- 「道具は揃った。実数の公理を読もう——それは『構造』として書かれている」
