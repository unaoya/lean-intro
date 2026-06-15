# Ch11 数の体系 — リテラル・除法・cast

<!-- 下書き（配置設計版）: 節立てメモ -->
<!-- 2026-06-15 分割: 旧 Ch11（数＋y=x）の数の体系部。y=x 計算は Ch12 へ -->

- 前章からの問い: sorry を消し、具体例を計算する準備として「数」を建てる
- 到達点: リテラル（2 以上）・`↑n`・除法が使える・cast 補題（cast は射）。これが y=x 計算（Ch12）の土台
- 新しい Lean 機能: OfNat 物語の回収・`Real.ofNat`（構造的再帰）・NatCast・Div・cast 補題
- コード: C11_Numbers.lean（§1 リテラルと除法 §2 除法補題 §3 cast 補題）

## 11.1 リテラル 2 の正体（Ch3 の伏線回収）

- `(2 : Real)` エラー（Ch3）の回収: OfNat 1（Ch6 既出）・`Real.ofNat`（構造的再帰）・OfNat (n+2) の設計。除法 `Div` の初登場（中点 (a+b)/2）

## 11.2 数の 2 つの建て方とダイヤモンドの規律

- **(i) 代数一次（採用・mathlib 式）**: 0/1 は代数のフィールドが一次、cast はその上に建てる。リテラルは 0（Ch3）/1（Ch6）/2 以上（本章 Real.ofNat）で**担当を排他分割**——mathlib `Nat.AtLeastTwo` の手作り版
- **defeq の観察**（ANCHOR `cast_defeq`）: `Real.ofNat 0 = 0 := rfl` は通り、`Real.ofNat 1 = 0 + 1 := rfl` で中身が見え、`#check_failure (rfl : Real.ofNat 1 = 1)` で **defeq でないことがビルドで検証**（Ch7 の「2 種の等しさ」の実戦）
- **(ii) cast 一括ルート（演習: 試して壊す）**: 全リテラルを ofNat 経由にすると one 系の rfl が死ぬ——AtLeastTwo の理由。**ダイヤモンド事件**（ANCHOR `diamond`・同型に 2 インスタンスで機構が黙って 1 つを選ぶ）。菱形の縦糸完成: Ch3 悪い菱形→Ch4/Ch6 良い配線→本章 排他分割→付録 C

## 11.3 除法の補題と自作タクティク my_field

- 中点・半分・等分の部品: zero_div・mul_div_cancel'・div_mul_cancel（**inv 相殺の土台**＝Field.mul_inv を直接使う）・**div_sub_div/div_add_div（my_ring で・Ch8 の reify が `/` 対応）**
- **自作タクティク `my_field`**: 分数を結合し `div_eq_iff`（非ゼロ条件付き）で**分母を払い**、残りの多項式恒等式を **my_ring** で閉じる（field_simp＋ring の自作）。非ゼロは仮定 `c ≠ 0` か `one_one_ne_zero` から自動で探す。**half_add・double_half（係数·inv の相殺）が一行**に——B/D（反射）に続く E（体）の道具
- 順序＋除法: pos_half・half_lt・pos_div_pos・div_right_le 等（pos_mul_pos/mul_nonneg＋pos_inv）
- ⚠ inv 相殺の土台補題（mul_div_cancel'・div_mul_cancel）は my_field の構成要素なので手証明。my_field はその上の派生・下流を畳む（cast_add 同様の「土台と自動化」の分担）

## 11.4 cast は「射」——構造を保つ写像（ANCHOR `cast_hom`）

- **cast の順序系を `cast_le` 基盤で構造化（2026-06-16）**: `cast_le`（順序保存）を**帰納の基盤**にし、nonneg・le_succ・lt・単射・pos をすべてその帰結にする（線形性/RS 単調性の階層化と同じ精神）:
  - **`cast_le`（基盤）**: `b = a + k` の k について帰納・各ステップ `cast m ≤ cast m + 1`（`0 ≤ 1` のみ）——**`cast_nonneg` を使わず**証明するのが鍵
  - `cast_nonneg = cast_le 0 n`・`cast_le_succ = cast_le n (n+1)`
  - `cast_lt = cast_le (a+1 ≤ b) + (cast a < cast a + 1)`（狭義単調）
  - **`cast_inj`（単射）= 狭義単調 `cast_lt` の帰結**（三分法で a<b・b<a を ≠ で排除）
  - `cast_pos_succ = cast_lt 0 (n+1)`・`cast_pos_of_ne = cast_lt 0 m`
  - 依存は線形: `cast_le → {nonneg, le_succ, lt} → {inj, pos}`。`cast_add`/`cast_mul`（+/× の準同型）は独立帰納
- **cast は 0・1・+・×・≤ を保つ＝順序付き半環の準同型**。述語 `IsNatHom` で「Nat → Real は構造の射」を明示し `cast_isHom` で証明（Ch10 の `IsLinearMap` と並ぶ「射」）。`cast_summation`＝**Σ と可換**（Ch12 の y=x 計算で使う）
- **分割線**: sup を使う archimedean 系は第 II 部へ——「この章は古典公理ゼロ」

## 11.5 章末監査

- `#print axioms cast_mul` = [Real, instLOF]——**古典論理ゼロ**（cast の射性も構成的）

## 引き

- 「数は建った。これで [0,1] の n 等分の上で y=x のリーマン和を計算できる」
