# Ch12 数の体系 — cast の証明本体・除法・等分割の完成

<!-- 下書き（配置設計版）: 節立てメモ。本文未執筆。構成v7 -->
<!-- 構成v7: cast の「定義」(Real.ofNat/OfNat/NatCast/Div・射の概念)は Ch6 へ前倒し。
     本章は道具(Ch7-10)が揃ったので「cast が射であることの証明本体」と等分割の完成を扱う -->

- 前章からの問い: Ch6 で cast と等分割の分点式を**定義**した。その性質（射であること・等分割の単調性）を、道具が揃った今**証明**する
- 到達点: cast が「順序半環の射」であることを証明し、順序系（≤/+/×/単射）を一般論から導く・除法補題と my_field・**等分割 equalPartition を完成**（increase の証明）。これが y=x 計算（Ch13）の土台
- 新しい Lean 機能: なし（Ch7–10 の道具の応用——induction・my_ring・順序補題・自作 my_field）
- コード: C12_Numbers.lean（cast_defeq・除法補題・cast 補題本体・IsOrderedSemiringHom メソッド・equalPartition）

## 12.1 defeq の綻び — cast 1 = 1 は rfl で死ぬ（Ch6 の回収）

- cast の定義（`Real.ofNat`・OfNat 2 以上・NatCast・Div）は **Ch6 で済み**。ここはその defeq の含意から（ANCHOR `cast_defeq`）: `Real.ofNat 0 = 0 := rfl` は通り、`Real.ofNat 1 = 0 + 1 := rfl` で中身が見え、`#check_failure (rfl : Real.ofNat 1 = 1)` で **defeq でないことがビルドで検証**（Ch8「2 種の等しさ」の実戦）。`cast_one` は命題的に証明する
- **数の 2 つの建て方とダイヤモンドの規律**: 0/1 は代数のフィールドが一次、cast はその上。リテラルは 0（Ch4）/1（Ch4 One bridge）/2 以上（Ch6 `Real.ofNat`）で**担当を排他分割**——mathlib `Nat.AtLeastTwo` の手作り版。全リテラルを ofNat 経由にすると one 系の rfl が死ぬ（演習: 試して壊す）。**ダイヤモンド事件**（ANCHOR `diamond`）。菱形の縦糸: Ch4 悪い菱形→Ch4/Ch6 良い配線→本章 排他分割→付録 C

## 12.2 除法の補題と自作タクティク my_field

- 中点・半分・等分の部品: zero_div・mul_div_cancel'・div_mul_cancel（**inv 相殺の土台**＝Field.mul_inv を直接使う）・**div_sub_div/div_add_div（my_ring で・Ch9 の reify が `/` 対応）**
- **自作タクティク `my_field`**: 分数を結合し `div_eq_iff`（非ゼロ条件付き）で**分母を払い**、残りの多項式恒等式を **my_ring** で閉じる（field_simp＋ring の自作）。非ゼロは仮定 `c ≠ 0` か `one_one_ne_zero` から自動で探す——B/D（反射）に続く体の道具
- 順序＋除法: pos_half・half_lt・pos_div_pos・div_right_le 等（pos_mul_pos/mul_nonneg＋pos_inv）
- ⚠ inv 相殺の土台補題は my_field の構成要素なので手証明。my_field はその上の派生・下流を畳む

## 12.3 cast は「射」だった — Ch6 の概念を証明で実現（ANCHOR `cast_hom`）

- **Ch6 で `Monotone`・`IsOrderedSemiringHom` を概念として定義した**。ここで cast がその実例であることを証明し、順序系を一般論から出す:
  - **`cast_le : Monotone (Nat-cast)`**＝「cast は順序写像」。基盤証明は `b = a + k` の k 帰納・各ステップ `cast m ≤ cast m + 1`（`0 ≤ 1` のみ・**`cast_nonneg` を使わない**）——cast 固有の順序事実はこれだけ
  - **順序系は「射の一般論」から**（cast 非依存・`IsOrderedSemiringHom` のメソッド）: `nonneg` = monotone ＋ map_zero／**`succ_step`（`φ n < φ(n+1)`）= map_add ＋ map_one ＋ 0<1**／`strictMono` = monotone ＋ succ_step／`injective` = strictMono ＋ 三分法
  - **cast への適用**: `cast_isHom : IsOrderedSemiringHom (Nat-cast)`（`cast_le`＋`cast_add`/`mul` だけが cast 固有）。`cast_nonneg/lt/inj/pos_*` はそのメソッド。**Ch6 の IsLinearMap／Ch11 の RS 単調性と同じ「中核概念から帰結を導く」精神**
  - **`map_summation`（射は Σ と交換）も一般論**: `φ(Σ f) = Σ(φ∘f)` は `map_zero`＋`map_add` だけの帰結。`cast_summation = cast_isHom.map_summation`（Ch13 の y=x で使う）
- **分割線**: sup を使う archimedean 系は第 II 部へ——「この章は古典公理ゼロ」

## 12.4 等分割の完成 — equalPartition（Ch6 の分点式に証明を与える）

- Ch6 で分点式 `equalPoints m a b = a + i·(b−a)/m` を**定義**した。ここで道具が揃ったので、それを完全な `Partition` に組み上げる（ANCHOR `equal_partition`）:
  - `increase`（広義単調）: `add_left_le` → `div_right_le`（cast_pos_of_ne）→ `nonneg_mul_nonneg`（`nonneg_iff_le` ＋ `cast_le_succ`）——**§12.3 の cast 順序系がここで効く**
  - `left`/`right`（両端 = a, b）: zero_mul・zero_div・`mul_div_cancel'`（除法補題 §12.2）
  - `equalPartition_length` = (b−a)/m（telescope・succ_ofNat・my_ring）
- 代表点は **Ch5 の一般 `leftRepr`/`rightRepr` を適用**（`equalPartitionRepr_isrepr` は Ch11 の `leftRepr_isRepr` の特例）——一般構成を y=x の前に確立

## 12.5 章末監査

- `#print axioms cast_mul` = [Real, instLOF]・`equalPartition` = [Real, propext, instLOF]——**古典論理ゼロ**（cast の射性も等分割も構成的）

## 引き

- 「数は建ち、等分割も完成した。これで [0,1] の n 等分の上で y=x のリーマン和を計算できる」
