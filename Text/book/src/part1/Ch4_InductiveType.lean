-- Text/book/src/part1/Ch4_InductiveType.lean — 第一部 Ch4 帰納型と再帰（inductive type）
-- 型理論の2つの基本のもう一本が **inductive type**（帰納型）。Ch1 で Three を「作った」。
-- ここではその「使い方」＝除去規則 recursor を見て、再帰的な帰納型 Nat 上に sumTo を定義し、
-- パターンマッチが recursor の糖衣であることを種明かしする。最後に #print で論理結合子が
-- すべて帰納型だったことを確認し、Ch1 の依存関数と合わせて「論理の2原始」が揃う。
import Ch3_Calc

-- ============================================================
-- §4.0 帰納型で型を作る: 有限集合 Three とその上の関数（導入＝構成子）
-- ============================================================

-- ANCHOR: finite
-- 導入（Three「への」関数＝構成子）: 3 つの住人を構成子で並べた有限集合（≅ {0,1,2}）
inductive Three where
  | a
  | b
  | c

#check Three
#check Three.a

-- 除去（Three「からの」関数）: パターンマッチで各構成子を捌く（有限集合上の自然数値関数）
def label : Three → Nat
  | .a => 0
  | .b => 1
  | .c => 2

#check label Three.a
#check label .a

-- Three「への」関数（別の型から作る）も構成子で
def pick : Bool → Three
  | true  => .a
  | false => .c
-- ANCHOR_END: finite

-- ============================================================
-- §4.1 帰納型を「使う」: 除去規則 recursor
--   どの帰納型にも 導入規則（構成子＝値を作る）と 除去規則（recursor＝値を使う）がある。
--   構成子が再帰的な引数を持つ（Nat の succ）と、その分だけ「帰納法の仮定 (IH)」を受け取る——
--   再帰の有無が cases（Or・有限型 Three）と induction（Nat）を分ける。
-- ============================================================

-- ANCHOR: eliminators
#check @Three.rec  -- 上の §4.0 で作った有限型 Three の除去規則（各構成子 a/b/c の場合を与える・IH 無し）
#check @Or.rec     -- (a → C) → (b → C) → (a ∨ b) → C        ← 各構成子の引数だけ・IH 無し（=cases）
#check @Nat.rec    -- motive 0 → ((n) → motive n → motive (n+1)) → (n) → motive n
                   --                        ↑ motive n = 帰納法の仮定 IH（Nat が再帰だから）
-- ANCHOR_END: eliminators

-- ============================================================
-- §4.2 構造的再帰の入門: sumTo（Nat 上の再帰関数）
-- ============================================================

-- 帰納的定義の入門: 自然数からの写像を「zero でどうなるか／succ でどうなるか」の2段で定める
-- （上の Nat.rec の実演）。まず簡単な例 sumTo n = 0 + 1 + … + n から始める。
-- ANCHOR: sum_to
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)   -- succ の段で「前の結果 sumTo n」に n+1 を足す
example : sumTo 3 = 6 := rfl     -- 0+1+2+3 = 6（再帰方程式は定義どおり rfl で計算される）
-- ANCHOR_END: sum_to

-- ============================================================
-- §4.3 パターンマッチの種明かし: 再帰(A)と依存関数型(B)を切り分ける
--   (A) 再帰: succ の段で「前の値 ih」を使うこと。sumTo はこれ**だけ**——戻り値の型 Nat は n に依らない。
--   (B) 依存関数型の項作り: `(n : Nat) → C n` の項を zero（C 0 の項）と succ（C n の項 ih から
--       C (n+1) の項）で組むこと＝Nat.rec の motive C。sumTo は C n = Nat（定数）なので (B) が退化し
--       (A) だけが純粋に見える（依存 (B) が効く Summation は第二部）。
--   Ch1 の依存関数（motive C は依存関数）と Ch4 の帰納型（Nat.rec）がここで出会う。
-- ============================================================

-- ANCHOR: recursor_reveal
-- 生の Nat.rec で sumTo を書き下すと（パターンマッチが内部で組んでいる「種」）:
def sumTo' : Nat → Nat :=
  fun n => Nat.rec 0 (fun n ih => ih + (n + 1)) n

-- パターンマッチ版 sumTo を #print すると `fun x => Nat.brecOn x sumTo._f`——Nat.rec から作られる
-- 「強帰納」版 Nat.brecOn（succ の段でそれまでの全部の値を使える）に翻訳されている:
#print sumTo
-- 生 rec 版 sumTo' とは外延的に同じ関数だが、定義的には別物（brecOn ≠ rec）。具体値なら計算で一致:
example : sumTo 3 = sumTo' 3 := rfl
-- だが一般の n では defeq で繋がらず、命題等式として induction で証明する必要がある
-- （defeq と「=」の違いの予告——第二部の 2 つの等しさへ）:
theorem sumTo_eq : (n : Nat) → sumTo n = sumTo' n
  | 0 => rfl
  | n + 1 => congrArg (· + (n + 1)) (sumTo_eq n)
-- ANCHOR_END: recursor_reveal

-- ============================================================
-- §4.4 論理結合子の正体: #print 種明かし（帰納型の柱の完成）
--   Ch1 で →・∀ が依存関数だと見た。残りの ∧∨∃⊥= はすべて帰納型——これで論理の2原始が揃う。
-- ============================================================

-- ANCHOR: ch_punchline
#print And      -- structure（構成子 intro 1 つ・除去 .1 .2 = And.rec）——Ch1 §1 の積と同じ
#print Or       -- inductive（構成子 inl/inr・除去 .elim = Or.rec）——Ch1 §2 の和と同じ
#print Exists   -- inductive（構成子 intro 1 つ・依存・除去 .elim = Exists.rec）——Ch1 Subtype と同じ
#print False    -- inductive（構成子 0・除去 False.elim = 爆発律）
-- 結論: **論理 = 依存関数（→ ∀ ¬・Ch1 §3）＋ 帰納型（∧ ∨ ∃ ⊥ = ・本章）**。型理論の2原始だけで尽きる。
-- ANCHOR_END: ch_punchline

-- ============================================================
-- §4.5 最終目標: 1 から n までの和の公式を calc で（Ch3 で学んだ calc を使う）
--   sumTo の再帰方程式に沿った帰納（| 0 | n+1）で各段を calc で繋ぐ。除法 n(n+1)/2 は Nat の
--   切り捨てが絡むので、まず 2 を払った形 2·sumTo n = n(n+1) を示してから 2 で割るのが素直。
-- ============================================================

-- ANCHOR: sum_to_formula
theorem two_mul_sumTo : (n : Nat) → 2 * sumTo n = n * (n + 1)
  | 0 => rfl
  | n + 1 =>
    calc 2 * sumTo (n + 1)
        = 2 * (sumTo n + (n + 1))     := rfl                                   -- sumTo の定義
      _ = 2 * sumTo n + 2 * (n + 1)   := Nat.left_distrib 2 (sumTo n) (n + 1)   -- 分配
      _ = n * (n + 1) + 2 * (n + 1)   := congrArg (· + 2 * (n + 1)) (two_mul_sumTo n)  -- 帰納法の仮定
      _ = (n + 2) * (n + 1)           := (Nat.add_mul n 2 (n + 1)).symm         -- 括り直し
      _ = (n + 1) * (n + 1 + 1)       := Nat.mul_comm (n + 2) (n + 1)           -- 可換（n+2 ≡ n+1+1）

theorem sumTo_formula (n : Nat) : sumTo n = n * (n + 1) / 2 :=
  (Nat.mul_div_cancel_left (sumTo n) (Nat.succ_pos 1)).symm.trans
    (congrArg (· / 2) (two_mul_sumTo n))
-- ANCHOR_END: sum_to_formula
