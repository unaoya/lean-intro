-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。
-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。

import LeanIntro.Original.«02_Forall»
import LeanIntro.Original.«03_InductiveTypes»

-- # 型と命題 II — かつ・または・否定・存在量化

-- ## 1. 存在と依存和 — 偶数・全射の例から

theorem exists_eq_two : ∃ n : Nat, n = 2 :=
  ⟨2, rfl⟩

#check exists_eq_two

-- ### 例1: 任意の自然数 n について、n + n は偶数

#check Nat.two_mul

#check (2 * 3 = 3 + 3)

#check Nat.two_mul 3

#check Eq.symm

#check Eq.symm (Nat.two_mul 3)

theorem even_double : ∀ n : Nat, ∃ k, n + n = 2 * k :=
  fun n => ⟨n, Eq.symm (Nat.two_mul n)⟩

#check even_double

def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

#check IsEven

theorem isEven_double : ∀ n : Nat, IsEven (n + n) :=
  fun n => ⟨n, Eq.symm (Nat.two_mul n)⟩

#check isEven_double

-- ### 例2: 存在するものを使う

theorem exists_map {α : Type} {Q R : α → Prop} :
    (∀ a, Q a → R a) → (∃ a, Q a) → ∃ a, R a :=
  fun hqr h =>
    match h with
    | ⟨a, ha⟩ => ⟨a, hqr a ha⟩

#check exists_map

-- ### 等式に関数を適用する・等式をつなぐ

#check congrArg

#check Eq.trans

-- ### 例3: 全射どうしの合成は全射

example {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : ∀ c, ∃ b, g b = c) (hf : ∀ b, ∃ a, f a = b) :
    ∀ c, ∃ a, g (f a) = c :=
  fun c =>
    match hg c with
    | ⟨b, hb⟩ =>
      match hf b with
      | ⟨a, ha⟩ => ⟨a, Eq.trans (congrArg g ha) hb⟩

theorem comp_surjective {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Surjective (fun x => g (f x)) :=
  fun c =>
    match hg c with
    | ⟨b, hb⟩ =>
      match hf b with
      | ⟨a, ha⟩ => ⟨a, Eq.trans (congrArg g ha) hb⟩

#check comp_surjective

-- ### 整理 — 依存和と「存在する」

def mkSigma {α : Type} {P : α → Type} (a : α) (b : P a) : (a : α) × P a := ⟨a, b⟩

#check mkSigma

theorem mkExists {α : Type} {Q : α → Prop} (a : α) (h : Q a) : ∃ a, Q a := ⟨a, h⟩

#check mkExists

def currySigma {α γ : Type} {P : α → Type} : (((a : α) × P a) → γ) → ((a : α) → P a → γ) :=
  fun f a b => f ⟨a, b⟩

#check currySigma

theorem curryExists {α : Type} {r : Prop} {Q : α → Prop} : ((∃ a, Q a) → r) → (∀ a, Q a → r) :=
  fun f a b => f ⟨a, b⟩

#check curryExists

/- ✏ 練習
96. `example : ∃ n : Nat, IsZero n := ⟨0, rfl⟩` が通ることを確かめよ。

97. 任意の自然数 `n` について `n + n + n` が3の倍数であることを示せ。
   `theorem triple_multiple : ∀ n : Nat, ∃ k, n + n + n = 3 * k` を書け。
   ヒントとして、`Nat.succ_mul 2 n` は `3 * n = 2 * n + n` を与える。
   `Nat.two_mul n` と、上で使った `congrArg`・`Eq.trans` を組み合わせよ。
-/

-- ## 2. 直積型と「かつ」

def mkProd {α β : Type} (a : α) (b : β) : α × β := ⟨a, b⟩

#check mkProd

theorem mkAnd {p q : Prop} (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

#check mkAnd

def swapProd {α β : Type} : α × β → β × α := fun x => ⟨x.snd, x.fst⟩

#check swapProd

theorem swapAnd {p q : Prop} : p ∧ q → q ∧ p := fun h => ⟨h.right, h.left⟩

#check swapAnd

/- ✏ 練習
98. `theorem and_left {p q : Prop} : p ∧ q → p` と型側の対応物
   `def fst' {α β : Type} : α × β → α` を書き比べよ。
99. `theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r)` を `⟨…⟩` と `.left`・`.right` で書け。
100. 具体的な命題でも示し方は同じであることを、
   `example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩` で確かめよ。

101. 各点で二つの証明を組にして、
   `theorem all_and {α : Type} {Q R : α → Prop} :
   (∀ a, Q a) → (∀ a, R a) → ∀ a, Q a ∧ R a` を書け。

102. `theorem exists_left {α : Type} {Q R : α → Prop} :
   (∃ a, Q a ∧ R a) → ∃ a, Q a` を書け。
   証人はそのまま使い、根拠の左側だけを取り出す。
-/

-- ## 3. 直和型と「または」

def inlSum {α β : Type} (a : α) : α ⊕ β := .inl a

#check inlSum

theorem inlOr {p q : Prop} (hp : p) : p ∨ q := .inl hp

#check inlOr

def swapSum {α β : Type} : α ⊕ β → β ⊕ α := fun x =>
  match x with
  | .inl a => .inr a
  | .inr b => .inl b

#check swapSum

theorem swapOr {p q : Prop} : p ∨ q → q ∨ p := fun h =>
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

#check swapOr

def elimSum {α β γ : Type} : α ⊕ β → (α → γ) → (β → γ) → γ := fun x f g =>
  match x with
  | .inl a => f a
  | .inr b => g b

#check elimSum

theorem elimOr {p q r : Prop} : p ∨ q → (p → r) → (q → r) → r := fun h f g =>
  match h with
  | .inl hp => f hp
  | .inr hq => g hq

#check elimOr

/- ✏ 練習
103. `theorem or_idem {p : Prop} : p ∨ p → p` を `match` で書け（どちらの札でも中身は同じ）。
104. `theorem or_map {p q r : Prop} : (p → q) → p ∨ r → q ∨ r` を書け
   （札を見て、左のときだけ関数を適用する）。
105. `example : (1 = 2) ∨ (2 = 2) := .inr rfl` が通ることを確かめよ
   （左の札が**偽の命題**でも、右から入れる）。
-/

-- ## 4. 空の型と「⊥」

def elimEmpty {α : Type} : Empty → α := fun e => e.elim

#check elimEmpty

theorem elimFalse {p : Prop} : False → p := fun h => h.elim

#check elimFalse

theorem notIntro {p : Prop} (h : p → False) : ¬p := h

#check notIntro

-- ### False と True

/- ✏ 練習
106. `theorem noContra {p q : Prop} : p → ¬p → q` を書け。ヒント: `¬p` は `p → False` なので、
   適用すると `False` が出る。あとは `.elim`。
107. `theorem dni {p : Prop} : p → ¬¬p` を書け（`¬¬p` を**示す**向き。ほとんど1語で書ける）。
   書けたら、逆向き `¬¬p → p` にも挑戦して、**書けない**ことを確かめよ。
   書き方は `06_Topology.lean` の2節 `compl_compl`（`Classical.byContradiction` を使う）で、
   その代償（公理への依存）は末尾の公理の節で分かる。
108. `example : ¬False := fun h => h` が通ることを確かめよ
   （`¬False` は `False → False`——恒等関数が証明になる）。
-/

-- ## 5. 偶数と偶数の和は偶数

#check Nat.mul_add

theorem isEven_add {n m : Nat} (hn : IsEven n)
    (hm : IsEven m) : IsEven (n + m) :=
  match hn with
  | ⟨k, hk⟩ =>
    match hm with
    | ⟨l, hl⟩ =>
      let h1 : n + m = 2 * k + m :=
        congrArg (fun x => x + m) hk
      let h2 : 2 * k + m = 2 * k + 2 * l :=
        congrArg (fun x => 2 * k + x) hl
      let h3 : 2 * k + 2 * l = 2 * (k + l) :=
        Eq.symm (Nat.mul_add 2 k l)
      ⟨k + l, Eq.trans (Eq.trans h1 h2) h3⟩

#check isEven_add

-- ### 補足: 「既知」だった 2n = n + n を自分で証明する

theorem succ_add' : ∀ (n m : Nat), (n + 1) + m = (n + m) + 1 := fun n m =>
  match m with
  | 0     => rfl                                  -- 両辺とも計算で n + 1
  | j + 1 => congrArg (· + 1) (succ_add' n j)     -- 帰納法の仮定は再帰呼び出し

theorem two_mul_from_scratch : ∀ n : Nat, 2 * n = n + n := fun n =>
  match n with
  | 0     => rfl
  | k + 1 =>
    (congrArg (· + 2) (two_mul_from_scratch k)).trans -- 2(k+1) = 2k+2 = (k+k)+2
      ((congrArg (· + 1) (succ_add' k k)).symm :
        (k + k) + 2 = (k + 1) + (k + 1))           -- 型注釈はふつうの証明の式変形の写し

#check two_mul_from_scratch

#print axioms two_mul_from_scratch

-- （補足・先取りここまで）

/- ✏ 練習
109. `theorem isEven_two_mul : ∀ n : Nat, IsEven (2 * n)` を `isEven_double` に
   ならって書け（証人は `n`、根拠は `rfl` で済む——なぜ済むのかも考えること）。
110. 「n が偶数なら n + 2 も偶数」を、本文と同じ段構え
   （ふつうの証明 → 論理式 → 形式化を意識した版 → 項）で自分で書け。
   ヒント: 証人は `k + 1`。式変形の最後は `Nat.mul_succ` の対称形が使える。
111. `example : IsEven 10 := ⟨5, rfl⟩` が通ることを確かめよ
   （例1の一般論の、具体的な1点での実例である）。
-/

-- ## 6. 等式と自然数の証明 — 計算・帰納法・構成子

example (n : Nat) : n + 0 = n := rfl

example (n : Nat) : 0 + n = n := Nat.zero_add n

-- ### 整理 — 自然数の命題と構成子

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive Eq {α : Sort u} : α → α → Prop
--   | refl (a : α) : Eq a a

example : 0 = 0 := Eq.refl 0
example : 0 = 0 := rfl        -- 略記。引数の `0` は型 `0 = 0` の側から決まる

-- ### rfl の型を読む

#check rfl

-- ### 順序 `Nat.le`

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive Nat.le (n : Nat) : Nat → Prop
--   | refl : Nat.le n n
--   | step {m} : Nat.le n m → Nat.le n (succ m)   -- `succ m` は `m + 1`

example : 0 ≤ 0 := Nat.le.refl
example : 0 ≤ 1 := Nat.le.step Nat.le.refl
example : 0 ≤ 2 := Nat.le.step (Nat.le.step Nat.le.refl)

-- ### 等式の法則は公理ではない

#print axioms Eq.symm

-- ### 「全部」と「別々」も出てくる

#check @Signal.rec

-- ### 補足: 対称に見えて `rfl` が通らない `0 * n`

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- theorem all_zero_mul : ∀ n : Nat, IsZero (0 * n) := fun n => rfl

/- ✏ 練習
112. `example : IsZero (0 * 5) := rfl` が通ることを確かめよ。
   `IsZero (5 * 0)` は `rfl` と `all_mul_zero 5` の両方で証明できるか。
-/

-- （補足・先取りここまで）

-- ### 補足: 定義的等しさと、等しいことの証明

example (n : Nat) : n + 0 = n := rfl

example (n : Nat) : 0 + n = n := Nat.zero_add n

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl

-- （補足・先取りここまで）

-- ### 補足: 構成子が別々であることと `noConfusion`

example : true ≠ false := fun h => Bool.noConfusion h

example {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.noConfusion h (fun h' => h')

#print axioms Bool.noConfusion

-- （補足・先取りここまで）

-- ### 補足: 等式をもう1つ作る実験

inductive MyEq {α : Type} (a : α) : α → Prop where
  | refl : MyEq a a

#check MyEq

theorem MyEq.symm {α : Type} {a b : α} (h : MyEq a b) : MyEq b a :=
  match h with
  | .refl => .refl

#check MyEq.symm

#print MyEq.symm

#check @MyEq.rec

theorem MyEq.symm' {α : Type} {a b : α} (h : MyEq a b) : MyEq b a :=
  MyEq.rec (motive := fun c _ => MyEq c a) MyEq.refl h

example : MyEq (1 + 1) 2 := .refl

theorem myEq_iff_eq {α : Type} {a b : α} : MyEq a b ↔ a = b :=
  ⟨fun h => match h with | .refl => rfl,
   fun h => match h with | rfl => .refl⟩

#check myEq_iff_eq

example {α : Type} {a b : α} : MyEq a b = (a = b) := propext myEq_iff_eq

-- （補足・先取りここまで）

/- ✏ 練習
113. `example : 1 ≤ 3` を `Nat.le` の構成子**だけ**で書け（`step` は何回要るか）。
-/

/- ✏ 練習
114. （補足の確認）本文の `MyEq.symm` にならって、`MyEq.trans` を自分で証明せよ
   （`h₂` を `match` で分ければ `h₁` がそのまま答えになる）。
115. （補足の確認）逆向きの橋 `theorem MyEq.ofEq {α : Type} {a b : α} (h : a = b) : MyEq a b` を
   `match` で書け（今度は `Eq` の側で場合分けして、`MyEq` の構成子を置く）。
-/

-- （補足・先取りここまで）

-- ## 7. 示すときと使うときのまとめ

example {α β : Type} : α × β → β × α := fun x =>
  match x with
  | ⟨a, b⟩ => ⟨b, a⟩

example {p q : Prop} : p ∧ q → q ∧ p := fun x =>
  match x with
  | ⟨a, b⟩ => ⟨b, a⟩

/- ✏ 練習
116. 対照表を見ながら、`theorem andToOr {p q : Prop} : p ∧ q → p ∨ q` の証明項を書け
   （`∧` から取り出し、`∨` を示す形に包む——1行で書ける）。
-/

-- ## 8. 補足: 証明検査 — エラボレータとカーネル

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- example : ∀ n : Nat, n - 1 + 1 = n := fun n => Nat.sub_add_cancel _

-- （補足・先取りここまで）

-- ## 9. 補足: データの組と存在の証明の違い

def sigmaFst {α : Type} {P : α → Type} (s : (a : α) × P a) : α := s.fst

def sigmaSnd {α : Type} {P : α → Type} (s : (a : α) × P a) : P s.fst := s.snd

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def existsFst {α : Type} {Q : α → Prop} (h : ∃ a, Q a) : α :=
--   match h with
--   | ⟨a, _⟩ => a

theorem existsElim {α : Type} {r : Prop} {Q : α → Prop}
    (h : ∃ a, Q a) (hr : ∀ a, Q a → r) : r :=
  match h with
  | ⟨a, ha⟩ => hr a ha

theorem orElimToProp {p q r : Prop} (h : p ∨ q) (f : p → r) (g : q → r) : r :=
  h.elim f g

/- ✏ 練習
117. 上の `existsFst` を試し、エラーメッセージを確かめよ。
-/

-- （補足・先取りここまで）
