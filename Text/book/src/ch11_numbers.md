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

- **cast を抽象的に「順序写像」「順序半環の射」として定式化し、補題を一般論から出す（2026-06-16）**:
  - **`Monotone φ`（順序写像）**: 順序集合間の射 `∀ a b, a ≤ b → φ a ≤ φ b` を抽象述語で定義。**`cast_le : Monotone (Nat-cast)`**＝「cast は順序写像」。基盤証明は `b = a + k` の k 帰納・各ステップ `cast m ≤ cast m + 1`（`0 ≤ 1` のみ・**`cast_nonneg` を使わない**）——cast 固有の順序事実はこれだけ
  - **`IsOrderedSemiringHom φ`（順序半環の射）**: `map_zero`/`map_one`/`map_add`/`map_mul`＋`monotone : Monotone φ`。Nat・Real を順序半環とみた準同型（旧 `IsNatHom` を改名）
  - **順序系は「射の一般論」から**（cast 非依存・`IsOrderedSemiringHom` のメソッド）:
    - `nonneg` = monotone ＋ map_zero
    - **`succ_step`（`φ n < φ(n+1)`）= map_add ＋ map_one ＋ 0<1**（`φ(n+1)=φ n+1>φ n`）——strict の鍵
    - `strictMono`（lt）= monotone ＋ succ_step（離散）／ `injective`（単射）= strictMono ＋ 三分法
  - **cast への適用**: `cast_nonneg/lt/inj = cast_isHom.{nonneg,strictMono,injective}`・`cast_pos_* = cast_lt 0 ·`。cast 固有の証明は `cast_le`＋`cast_add`/`mul` だけ（Ch10 の `IsLinearMap`／RS 単調性と同じ「中核概念から帰結を導く」精神）
  - `cast_isHom : IsOrderedSemiringHom (Nat-cast)`
  - **`map_summation`（射は Σ と交換）も一般論**: `φ(Σ f) = Σ(φ∘f)` は **`map_zero`＋`map_add` だけ**の帰結（順序・乗法は不要＝厳密には加法準同型で成立・Σ が Nat/Real 両方で `[Add][Zero]` 定義だから運べる）。`cast_summation = cast_isHom.map_summation`（Ch12 の y=x 計算で使う）。`IsLinearMap`（Σ の線形性）と響き合う「構造の射は構造的演算と交換」
- **分割線**: sup を使う archimedean 系は第 II 部へ——「この章は古典公理ゼロ」

## 11.5 章末監査

- `#print axioms cast_mul` = [Real, instLOF]——**古典論理ゼロ**（cast の射性も構成的）

## 引き

- 「数は建った。これで [0,1] の n 等分の上で y=x のリーマン和を計算できる」
