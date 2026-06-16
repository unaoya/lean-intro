-- Text/C02_Types.lean — Ch2 型を作る（型の構成と CH 対応）
-- Ch1 で「命題＝型・証明＝項」を見た。ここでは型を「作る」基本手段——積・和・関数・帰納型・
-- 商——を並べ、それぞれの「導入（項を作る＝その型への関数）」と「除去（項を使う＝その型からの
-- 関数）」を、命題の論理結合子（∧・∨・→）と対比する。これが Curry-Howard 対応の骨格。
-- 後で intro/cases/⟨⟩ が型と命題の両方で同じタクティクとして効く（Ch5 で recursor 種明かし）。
import Text.C01_FirstProofs

-- ============================================================
-- §1 積 α × β ↔ ∧: ペアを作る／取り出す
-- ============================================================

-- ANCHOR: product
-- 導入（項を作る＝α×β「への」関数）: ⟨a, b⟩
example (a : Nat) (b : Bool) : Nat × Bool := ⟨a, b⟩
-- 除去（項を使う＝α×β「からの」関数）: .1 / .2
example (p : Nat × Bool) : Nat := p.1
example (p : Nat × Bool) : Bool := p.2
-- 対比: 命題の ∧ も同じ機構（A ∧ B を ⟨h1, h2⟩ で作り .1/.2 で使う）——Ch1 の ⟨h.2, h.1⟩ がこれ
example (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩
-- ANCHOR_END: product

-- ============================================================
-- §2 和 α ⊕ β ↔ ∨: どちらかを入れる／場合分けで使う
-- ============================================================

-- ANCHOR: sum
-- 導入（α⊕β「への」関数）: Sum.inl / Sum.inr
example (a : Nat) : Nat ⊕ Bool := Sum.inl a
example (b : Bool) : Nat ⊕ Bool := Sum.inr b
-- 除去（α⊕β「からの」関数）: 場合分け（match）
def sumToNat (s : Nat ⊕ Bool) : Nat := match s with
  | Sum.inl n => n
  | Sum.inr b => if b then 1 else 0
-- 対比: 命題の ∨ も同じ（Or.inl/inr で導入・.elim で除去）——Ch1 の or_swap がこれ
example (A B : Prop) (h : A ∨ B) : B ∨ A := h.elim Or.inr Or.inl
-- ANCHOR_END: sum

-- ============================================================
-- §3 関数 α → β ↔ →: 関数を作る／適用する
-- ============================================================

-- ANCHOR: arrow
-- 導入（α→β「への」関数＝関数そのもの）: fun
example : Nat → Nat := fun n => n + 1
-- 除去（使う）: 適用
example (f : Nat → Nat) (n : Nat) : Nat := f n
-- 対比: 命題の → も同じ関数（A → B の証明は fun で作り適用で使う）——型も命題も → は関数
example (A B : Prop) (f : A → B) (a : A) : B := f a
-- ANCHOR_END: arrow

-- ============================================================
-- §4 帰納型で型を作る: 有限集合 Three とその上の関数
-- ============================================================

-- ANCHOR: finite
-- 導入（Three「への」関数＝構成子）: 3 つの住人を構成子で並べた有限集合（≅ {0,1,2}）
inductive Three where
  | a
  | b
  | c

-- 除去（Three「からの」関数）: パターンマッチで各構成子を捌く（有限集合上の自然数値関数）
def label : Three → Nat
  | .a => 0
  | .b => 1
  | .c => 2

-- Three「への」関数（別の型から作る）も構成子で
def pick : Bool → Three
  | true  => .a
  | false => .c
-- ANCHOR_END: finite

-- ============================================================
-- §5 商 Quotient: 同値関係で割る（整数 (Nat×Nat)/~ の予告）
-- ============================================================

-- ANCHOR: quotient
-- 整数 = (Nat × Nat)/~、(a,b) ~ (c,d) ⟺ a+d = c+b（直感: (a,b) は差 a−b・(n,n) は 0）
--   ※ iseqv（反射/対称/推移）は omega（Ch9 の自動化）に任せる——ここでは結果だけ借りる
instance intSetoid : Setoid (Nat × Nat) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv := ⟨fun _ => by omega, fun h => by omega, fun h1 h2 => by omega⟩

def IntByQuot := Quotient intSetoid
-- 導入（IntByQuot「への」関数）: Quotient.mk（代表を入れる）
example : IntByQuot := Quotient.mk intSetoid (3, 1)   -- 整数 2（= 3 − 1）
-- 0 の同一視: (n,n) はどれも (0,0) と同じ整数（差が 0）
example (n : Nat) : ((0, 0) : Nat × Nat) ≈ (n, n) := by show (0:Nat) + n = n + 0; omega
-- 除去（IntByQuot「からの」関数）: Quotient.lift（well-defined を示して使う）は発展で
-- ANCHOR_END: quotient

-- ============================================================
-- §6 まとめ: 導入＝その型「へ」・除去＝その型「から」——型も命題も同じ機構
-- ============================================================

-- 型の構成（×・⊕・→・帰納型）と命題の構成（∧・∨・→・帰納的命題）は同じ機構:
--   導入 = 項を作る = その型「への」関数（⟨⟩・inl/inr・fun・構成子）
--   除去 = 項を使う = その型「からの」関数（.1/.2・match・適用・パターンマッチ）
-- Curry-Howard 対応:「型 ↔ 命題・項 ↔ 証明」。だから後で intro/cases/⟨⟩ が
-- 型と命題の両方で同じタクティクとして効く（Ch5 で recursor として種明かし・Ch7 で実戦）。
#check @Prod        -- 積（×）
#check @Sum         -- 和（⊕）
#check @Quotient    -- 商
