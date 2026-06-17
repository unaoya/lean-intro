-- Text/book/src/part1/Ch1_Types.lean — 第一部 Ch1 型を作る（型の構成・依存関数）
-- 型を「作る」基本手段——積・和・関数・依存関数・部分型・依存和・帰納型——を並べ、それぞれの
-- 「導入（項を作る＝その型への関数）」と「除去（項を使う＝その型からの関数）」を見る。次章 Ch2 で
-- 命題の論理結合子（∧・∨・→・¬・∀・∃）をこれと**パラレル**に並べ、Curry-Howard 対応を回収する。
-- 後で intro/cases/⟨⟩ が型と命題の両方で同じタクティクとして効く（Ch4 で recursor 種明かし）。

-- ============================================================
-- §1 積 α × β ↔ ∧: ペアを作る／取り出す
-- ============================================================

-- ANCHOR: product
-- 「正式な」導入は Prod.mk: α と β の項から α × β の項を作る関数
#check @Prod.mk        -- {α β} → α → β → α × β（2 引数の関数として読める）
example (a : Nat) (b : Bool) : Nat × Bool := Prod.mk a b
-- `⟨a, b⟩` は Prod.mk a b の略記（anonymous constructor——型から構成子を推論して埋める）
example (a : Nat) (b : Bool) : Nat × Bool := ⟨a, b⟩
-- 「正式な」除去は Prod.fst / Prod.snd: α × β の項から各成分を取り出す関数
#check @Prod.fst       -- {α β} → α × β → α
#check @Prod.snd       -- {α β} → α × β → β
example (p : Nat × Bool) : Nat := Prod.fst p
example (p : Nat × Bool) : Bool := Prod.snd p
-- `p.fst`/`p.1`・`p.snd`/`p.2` は Prod.fst p / Prod.snd p の略記（dot 記法）
example (p : Nat × Bool) : Nat := p.fst
example (p : Nat × Bool) : Nat := p.1
example (p : Nat × Bool) : Bool := p.2
-- 対比: 命題の ∧ も同じ機構（正式には And.intro で作り And.left/And.right で使う・⟨⟩/.1/.2 は略記）
#check @And.intro      -- {a b : Prop} → a → b → a ∧ b
example (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.2, h.1⟩
-- ANCHOR_END: product

-- ============================================================
-- §2 和 α ⊕ β ↔ ∨: どちらかを入れる／場合分けで使う
-- ============================================================

-- ANCHOR: sum
-- 集合論の「直和」α ⊔ β（disjoint union）に対応する型: α の項にも β の項にも「左/右」のタグを
-- 付けて 1 つの型に集める——どちらから来たかを忘れない（だから disjoint）。
-- 「正式な」導入は Sum.inl / Sum.inr——α（または β）から α ⊕ β への**自然な射（包含）**:
#check @Sum.inl        -- {α β} → α → α ⊕ β（α を左成分として包む射）
#check @Sum.inr        -- {α β} → β → α ⊕ β（β を右成分として包む射）
example (a : Nat) : Nat ⊕ Bool := Sum.inl a
example (b : Bool) : Nat ⊕ Bool := Sum.inr b
-- 「正式な」除去は場合分け（match——どちらの射で作られたかで分岐）。集合論で「α⊔β 上の関数は
-- α 上の関数と β 上の関数の対で決まる」（直和の普遍性）のと同じ:
def sumToNat (s : Nat ⊕ Bool) : Nat := match s with
  | Sum.inl n => n
  | Sum.inr b => if b then 1 else 0
-- 対比: 命題の ∨ も同じ（正式には Or.inl/Or.inr で導入・Or.elim で除去）——Ch2 の or_swap がこれ
#check @Or.inl         -- {a b : Prop} → a → a ∨ b
example (A B : Prop) (h : A ∨ B) : B ∨ A := h.elim Or.inr Or.inl
-- ANCHOR_END: sum

-- ============================================================
-- §3 関数 α → β と依存関数型 (x : α) → β x（型理論のもう一本の原始 dependent function）
--   関数型は集合論では α×β の部分集合だが、型理論では**プリミティブ**。本当のプリミティブは
--   依存関数型 Π で、命題の →・∀ もすべてこの依存関数（Ch2 で命題側とパラレル・Ch4 末で2原始を確認）。
-- ============================================================

-- 関数型 α → β: 導入 fun（関数を作る）・除去 並置＝関数適用（`f n`）
-- ANCHOR: arrow
example : Nat → Nat := fun n => n + 1
example (f : Nat → Nat) (n : Nat) : Nat := f n
-- ANCHOR_END: arrow

-- 依存関数型 (x : α) → β x が真のプリミティブ（行き先 β が引数 x に依存）
-- ANCHOR: dependent
#check (Nat → Nat)                 -- 非依存の関数型
#check ((n : Nat) → Fin (n + 1))   -- 依存関数型（Fin は core の有限型・下の §3d Range と同型）
#check (fun n : Nat => (0 : Fin (n + 1)))   -- (n : Nat) → Fin (n + 1)
-- ANCHOR_END: dependent

-- 命題の → と ∀ も依存関数（Ch2 で命題側とパラレルに回収）
-- ANCHOR: prop_as_function
example (A B : Prop) (f : A → B) (a : A) : B := f a   -- → は関数（適用 f a）
#check (∀ n : Nat, n = n)                              -- ∀ は codomain が Prop の依存関数
example : ∀ n : Nat, n = n := fun n => Eq.refl n
-- ANCHOR_END: prop_as_function

-- ============================================================
-- §3b Subtype {x : α // p x}: 値と「述語 p を満たす証明」を束ねる（∃ の Type 側）
-- ============================================================

-- ANCHOR: subtype
-- {x : α // p x} は「述語 p を満たす α の項」の型（p : α → Prop）。
-- 「正式な」導入は Subtype.mk: 値 x と「p x の証明」のペア
#check @Subtype.mk     -- {α} {p : α → Prop} → (val : α) → p val → {x // p x}
example : {n : Nat // n < 5} := Subtype.mk 3 (by omega)
example : {n : Nat // n < 5} := ⟨3, by omega⟩          -- ⟨_, _⟩ は Subtype.mk の略記
-- 「正式な」除去は .val（値）/ .property（証明）
#check @Subtype.val    -- {α} {p} → {x // p x} → α
example (s : {n : Nat // n < 5}) : Nat := s.val
example (s : {n : Nat // n < 5}) : s.val < 5 := s.property
-- 対比: 命題の ∃ も同じ依存ペア（⟨witness, proof⟩ で導入）。Subtype は「∃ をデータに格上げ」した
-- 型——∃ x, p x は証明（Prop）、{x // p x} は値が取り出せるデータ（Type）。Range n = {i // i < n}
-- （第二部 Summation の添字）はこの実例
-- ANCHOR_END: subtype

-- ============================================================
-- §3c 依存和 Σ x : α, β x: Subtype の一般化——第 2 成分を「証明」から「型の族」へ
-- ============================================================

-- ANCHOR: sigma
-- Subtype の第 2 成分は**証明** p x : Prop だった。これを一般の**型** β x : Type にすると
-- 依存和 Σ x : α, β x になる。集合論では「族 {β x}_x の直和（disjoint union）」——各 x ごとの
-- 集合 β x を x でタグ付けして集めたもの。**Subtype は β x が Prop（命題）である特別な場合**。
#check @Sigma.mk       -- {α} {β : α → Type} → (fst : α) → β fst → Σ x, β x
-- 例: 「n と、Fin (n+1) の項」のペア（第 2 成分の型 Fin (n+1) が第 1 成分 n に依存）
example : Σ n : Nat, Fin (n + 1) := ⟨2, 0⟩            -- n=2 と Fin 3 の項 0
-- 除去: .1（第 1 成分）/ .2（第 2 成分・その型は .1 に依存）
example (s : Σ n : Nat, Fin (n + 1)) : Nat := s.1
-- ⚠ 気になる点: Subtype では第 2 成分が Prop。「Prop も型の族のメンバーになれる」——Prop は
-- Sort 0・Type は Sort (u+1) で**地続き**（Sort 階層）。第 2 成分に証明（Prop）を選べば Subtype、
-- 一般の型（Type）を選べば本来の Σ。この Prop と Type の地続き性は第二部の universe で正面から扱う
-- ANCHOR_END: sigma

-- ============================================================
-- §3d Range n = {i : Nat // i < n}: Subtype の実例（第二部 Summation の添字に使う・core の Fin n と同型）
--   core には同じ役割の Fin n（structure { val : Nat, isLt : val < n }）があるが、ここでは
--   Subtype の実例として Range を自作し「述語を満たす値」を明示する（第二部 Summation の添字）。
-- ============================================================

-- ANCHOR: range
def Range (n : Nat) := { i : Nat // i < n }
-- ANCHOR_END: range

-- ANCHOR: range_intro
-- Range の「項」と「関数」の基本動作（§3b Subtype の導入と除去の実例）:
--   項を作る = 値と「範囲内」の証明を ⟨_, _⟩ で組む（導入）／取り出す = .val（除去）
example : Range 3 := ⟨2, Nat.lt_succ_self 2⟩      -- 値 2 ＋ 証明 2 < 3（= 2 < 2+1）
example (i : Range 3) : Nat := i.val              -- Range「から」の関数（domain が Range・射影）
-- Range 3「から」の関数を i.val の 0/1/2 で場合分け。i.val < 3 ゆえ 0/1/2 で尽きるが、
-- 型 `Range 3` だけからは Lean にそれが分からない——Nat 全体の網羅に最後の枝が要る（依存型の限界）
example (i : Range 3) : Nat := match i.val with
  | 0 => 10
  | 1 => 20
  | 2 => 30
  | _ => 0                                        -- i.val < 3 ゆえ到達しない（網羅性のためのダミー）
-- Range「へ」の関数（codomain が Range）は値を作り範囲内の証明を添える——下の incl/addone が実戦
-- ANCHOR_END: range_intro

-- ANCHOR: range_funcs
-- 名前空間を**作る**（Ch1 で読んだ既存の名前空間アクセスの対）: `namespace Range … end Range` で
--   囲むと、中で定義した `incl` は外から `Range.incl` になる。Range に関わる操作を 1 つの接頭辞に
--   束ね、衝突を避け、所属を名前で示す。（後で `open Range` で接頭辞を省ける——第二部 Summation の分割定義で実演）
namespace Range

-- incl/addone は「Range への関数」の実戦（Range n の項から Range (n+1) の項を作る——値は同じ / +1、
-- 添える「範囲内」の証明だけを既存補題 Nat.lt_succ_of_lt / Nat.succ_lt_succ で作り替える）
def incl {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val, Nat.lt_succ_of_lt k.property⟩

def addone {n : Nat} : Range n → Range (n + 1) :=
  fun k => ⟨k.val + 1, Nat.succ_lt_succ k.property⟩

end Range
-- ANCHOR_END: range_funcs

-- ============================================================
-- §4 帰納型で型を作る: 有限集合 Three とその上の関数
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
-- §4b 帰納型を「使う」: 除去規則 recursor と #print 種明かし（論理結合子の正体）は、
--   第一部 Ch4（inductive type）でまとめて扱う。Three（§4）はここで「作り」、Ch4 でその
--   recursor を見る——「2 章で型を作り → 4 章でその使い方（recursor）」という配置。
-- ============================================================

-- ============================================================
-- 商 Quotient（整数 (Nat×Nat)/~ の構成例）は第一部では扱わず、第二部以降で扱う。
-- ============================================================

-- ============================================================
-- §6 まとめ: 導入＝その型「へ」・除去＝その型「から」——型も命題も同じ機構
-- ============================================================

-- 型の構成（×・⊕・→・帰納型）と命題の構成（∧・∨・→・帰納的命題）は同じ機構:
--   導入 = 項を作る = その型「への」関数（⟨⟩・inl/inr・fun・構成子）
--   除去 = 項を使う = その型「からの」関数（.1/.2・match・適用・パターンマッチ）
-- Curry-Howard 対応:「型 ↔ 命題・項 ↔ 証明」。だから後で intro/cases/⟨⟩ が
-- 型と命題の両方で同じタクティクとして効く（Ch4 で recursor として種明かし・第II部 Ch7 で実戦）。
#check @Prod        -- 積（×）
#check @Sum         -- 和（⊕）
#check @Subtype     -- 部分型（∃ の Type 側）
