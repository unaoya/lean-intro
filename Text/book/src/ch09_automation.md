# Ch9 自動化と自作タクティク — simp・omega・ac_rfl・反射で my_ring を作る

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 旧 Ch11 間奏を前倒し本章化＋反射ベース my_abel/my_ring を実装（B/D） -->

- 前章からの問い: 等式を 1 本ずつ手で書いてきた。同じパターンを機械に任せられないか
- 到達点: バニラ（simp/omega/ac_rfl）を押さえ、**自分の公理から proof by reflection で my_abel（加法群）・my_ring（環）を自作**できる。以後の章（順序・帰納法・y=x）で使える
- 新しい Lean 機能: simp / simp only・omega・**ac_rfl**（Std.Associative/Commutative）・**メタプログラミング**（inductive 構文・elab・isDefEq による反射）
- コード: C09_Automation.lean（§1-3 バニラ・§5 my_abel・§6 my_ring——全デモが実ビルドで通る）
- ⚠ mathlib の ring/abel/linarith は**無い**（unknown tactic）ので、すべて自作する
- ⚠ **読み方の指針**: §9.1–9.3（simp/omega/ac_rfl のバニラ）が本線。**§9.4 以降（proof by reflection・メタプログラミング）は「道具を開ける」柱 B に関心がある読者向けで、初読では飛ばしてよい**（自作タクティクは以後の章で使うが、中身を知らなくても使える）

## 9.1 simp — 自分の補題を渡して畳む

- Ch7/7 で手証明した補題を simp に渡すと、その合成でしかない派生恒等式は閉じる（ANCHOR `simp_demo`）。`simp only [...]` で既定セットを汚さない規律
- 🪟 窓: simp の正体＝停止を期待する有向書き換え系。**限界**: 並べ替えが要る相殺（`a+b-a=b` 型）は閉じない

## 9.2 omega — Nat の決定手続き

- 添字計算（Σ の境界・truncated subtraction）はこれで尽きる（ANCHOR `omega_demo`）。正体は決定手続き＋カーネル計算

## 9.3 ac_rfl — 結合・可換を道具に教える

- `Std.Associative`/`Std.Commutative` インスタンスを + に与えると ac_rfl が括弧・順序差を吸収（ANCHOR `ac_demo`）。だが**逆元の相殺は扱えない**——ここで反射が要る

## 9.4 proof by reflection の発想

- simp も ac_rfl も「並べ替え＋相殺」を閉じられない（実測）。そこで**式を構文（`inductive Expr`）として写し取り**、決定可能な**正規形**に潰して比較する
- 三幕構成: ① 構文 `Expr` と評価 `eval : Expr → (Nat→Real) → Real` ② 正規化 `normalize`（計算可能）と**健全性** `eval e = nfEval (normalize e)`（帰納法・自分の群/環公理だけ） ③ メタ（elab）で目標を `Expr` に反射し `normalize` の一致を `decide` で判定

## 9.5 my_abel — 加法可換群の反射（B）

- 正規形＝**符号付き原子の整列リスト**（係数なし・同原子の逆符号で相殺）。鍵の補題 `nfEval_ins`（整列挿入の健全性＝相殺は `add_neg'`/`neg_add'`）
- ANCHOR `my_abel_demo`: `a + b - a = b`・telescope `b + -a = (c+-a)+(b+-c)` が一行で閉じる（simp/ac_rfl では不可だったもの）
- メタ: `getAppFnArgs` で `HAdd`/`HSub`/`Neg` を判定・`isDefEq` で原子を同定・`mkDecideProof` で正規形一致を証明

## 9.6 my_ring — 可換環への拡張（D）

- 原子 → **単項式**（整列原子リスト＝積）へ一般化。正規形＝符号付き単項式のリスト。新補題 `nfEval_crossMul`（**分配律**で積を展開＝`left/right_distrib`）・`entEval_entMul`（符号は XNOR）
- `if`/`==` の Bool 簡約を避け **`applySign`/`xnorB` をパターンマッチ定義**にして defeq を通す（メタの教材的工夫）
- ANCHOR `my_ring_demo`: `a*(b+c)=a*b+a*c`・`(a+b)*(c+d)=…`・`a*b-b*a=0`（可換）が一行。`(1+1)*(a*b)` のリテラル係数も単項式の重複で扱う。**my_abel を包含**
- 反射の一般化（多項式正規形・Horner）への発展は読み物として触れる

## 9.7 完成と回収 — リフレクションは「証明はプログラム」（旧 付録 D を統合）

- Ch8 で手計算した等式・Ch13 の y=x の代数小物が、ここで作った my_ring/my_abel で **1 行**になる
- **omega や decide が「どういう種類の物体か」、自分で作ったから分かる**——柱 B（道具を開ける）の到達点。リフレクション＝「**証明はプログラムである**」（Ch1/Ch2 の CH 対応との合流: 項=証明・正規化=計算）
- 健全性定理（`eval e = nfEval (normalize e)`）が**輸送補題**——反射の心臓。これを帰納法で証明したから `decide` の一致が等式の証明に化ける
- **mathlib 対応**: mathlib の `ring`/`ring_nf`/`linarith` は同じ発想の本格版（多項式の Horner 正規形・Positivstellensatz）。本書は core だけで「動く最小の ring」を自作した——mathlib があれば借りられるが、**作ると中身が分かる**。`linarith` は §10 の `lin` と対比して読み物に

## 運用の約束

- 以後の章（Ch10 順序・Ch11 帰納法・Ch13 y=x）で自作道具の使用可。「模範解答は手書き・自作道具は加速装置」（本体=模範解答の原則）

## 引き

- 「等式は反射で畳めた。では順序（≤/<）はどう自動化するか——順序のみの道具と、順序体（順序＋代数）の道具を作って比べよう」
