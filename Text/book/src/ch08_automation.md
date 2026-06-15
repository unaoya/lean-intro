# Ch8 自動化と自作タクティク — simp・omega・my_ring

<!-- 下書き（配置設計版）: 節立てと内容の配置メモのみ。本文未執筆 -->
<!-- 2026-06-15 再編: 旧 Ch10 間奏をコーパスの途中（Ch7 の後）へ前倒し・本章化（load-bearing） -->

- 前章からの問い: 等式を 1 本ずつ手で書いてきた。同じパターンを機械に任せられないか
- 到達点: simp に自分の補題を渡して派生恒等式を畳める。omega・ac_rfl・自作 my_ring macro を以後の章（順序・帰納法・y=x）で使える。my_ring が「どういう種類の物体か」の入口
- 新しい Lean 機能: simp / simp only・omega・ac_rfl（Std.Associative/Commutative）・macro
- コード: C08_Automation.lean（§1 simp デモ §2 omega §3 ac_rfl §4 my_ring macro——全デモが実ビルドで通る）
- ⚠ mathlib の ring/linarith/group は無いので**自作する**。本格的な反射版 my_ring は付録 D（本章は入口）

## 8.1 simp に環の等式を教える

- **種明かし: simp の正体＝停止を期待する有向書き換え系**。Ch6/7 で手証明した補題を渡すと、それらの合成でしかない派生恒等式は simp が閉じる（ANCHOR `simp_demo`）
- `simp only [...]` は渡した規則だけを使う——既定の simp セットを汚さず下流の証明の挙動を変えない規律（register_simp_attr は当 core で不可のため明示リスト＋macro 方式）

## 8.2 omega — Nat の決定手続き

- 添字計算（Σ の境界・truncated subtraction）はこれで尽きる（ANCHOR `omega_demo`）。正体（決定手続き＋カーネル計算）は付録 D。Ch10 の sum_id_nat でも稼働

## 8.3 ac_rfl — 結合・可換を道具に教える

- `Std.Associative` / `Std.Commutative` インスタンスを + に与えると、ac_rfl が括弧・順序の差を吸収（ANCHOR `ac_demo`）——「タクティクにインスタンス（代数の事実）を食べさせて自動化する」。simp の有向書き換えでは捌けない並べ替えを担当

## 8.4 自作タクティク my_ring

- macro でタクティクを綴る（Ch5 notation → 本章 macro → 付録 D elab の 3 段の真ん中・Ch6「タクティクは項を書く機械」の発展）。my_ring＝simp セットの合成を 1 語に（ANCHOR `my_ring`）
- **限界の正直**: これは方向的正規化の ring-lite。クロス項の相殺など並べ替えが要る等式は苦手——その限界が、式を AST として走査し正規形を比較する**反射版**（付録 D）の動機になる

## 運用の約束

- 以後の章（Ch9 順序・Ch10 帰納法・Ch11 y=x）で自作道具の使用可。ただし「模範解答は手書き・自作道具は加速装置」（本体=模範解答の原則）

## 引き

- 「等式は畳めた。では順序（≤/<）はどう獲得し、どう鎖（calc）にするか」
