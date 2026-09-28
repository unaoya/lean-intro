-- はじめての Lean — 03_InductiveTypes（ブラウザ版・自動生成）
-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、
-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。

-- # 型と項 II — 帰納型

-- ## 1. 構成子と場合分け

inductive Signal : Type where
  | red : Signal
  | yellow : Signal
  | green : Signal

#check Signal.red

-- ### match で項を使う

#eval match Signal.red with
  | Signal.red => 0
  | Signal.yellow => 1
  | Signal.green => 2

-- ### 関数の本体で場合分けする

def Signal.next : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.green
  | Signal.yellow => Signal.red
  | Signal.green => Signal.yellow

#eval Signal.next Signal.red

/- ✏ 練習
40. `Signal.red`、`Signal.yellow`、`Signal.green` をそれぞれ `0`、`1`、`2` に送る
   `signalCode : Signal → Nat` を定義せよ。各枝の型を確かめ、`signalCode Signal.yellow` の値を予想せよ。

41. `Signal.next` と逆向きに色を送る `prev : Signal → Signal` を書け。
   `prev (Signal.next Signal.red)` の値を確かめよ。
-/

-- ### 一点の型と空の型

inductive MyUnit : Type where
  | unit : MyUnit

inductive MyEmpty : Type

def emptyToNat (e : MyEmpty) : Nat := nomatch e

-- ## 2. 直和と直積

inductive TaggedSum : Type where
  | inn (n : Nat) : TaggedSum
  | inb (b : Bool) : TaggedSum

#check TaggedSum.inn

#check TaggedSum.inb

-- ### 中身を受け取る場合分け

def valueOf : TaggedSum → Nat := fun x =>
  match x with
  | TaggedSum.inn n => n
  | TaggedSum.inb _ => 0

#eval valueOf (TaggedSum.inn 7)

#eval valueOf (TaggedSum.inb true)

-- ### 構成子が違う場合と、同じ場合

#check TaggedSum.inn.inj

-- ### 中身の型をパラメータにする

inductive MySum (A B : Type) : Type where
  | inl (a : A) : MySum A B
  | inr (b : B) : MySum A B

#check MySum.inl

-- ### 補足: 型をパラメータにした取り出し関数

def getLeft {A B : Type} (d : A) : MySum A B → A := fun x =>
  match x with
  | MySum.inl a => a
  | MySum.inr _ => d

#check getLeft

#eval getLeft 0 (MySum.inr true)

-- （補足・先取りここまで）

/- ✏ 練習
42. `swapSum : MySum A B → MySum B A` を定義せよ。
   左側から来た項は右側へ、右側から来た項は左側へ送ること。
-/

-- ### 組も帰納型で作る

inductive MyPair (A B : Type) : Type where
  | mk (a : A) (b : B) : MyPair A B

#check (MyPair.mk 3 true : MyPair Nat Bool)

-- ### 組を使うときも match

def pairFirst {A B : Type} : MyPair A B → A := fun p =>
  match p with
  | MyPair.mk a _ => a

#eval pairFirst (MyPair.mk 3 true)

def swapPair {A B : Type} : A × B → B × A := fun p =>
  match p with
  | Prod.mk a b => Prod.mk b a

/- ✏ 練習
43. 写像 `f : X → A` と `g : X → B` から、`x` を組 `(f x, g x)` に送る
   `pairMaps : X → MyPair A B` を定義せよ。型 `X A B` と写像 `f g` も引数に取ること。
-/

-- ## 3. 依存する組

inductive Numbered : Type where
  | mk (n : Nat) (i : Fin n) : Numbered

#check Numbered.mk

-- ### 依存する組を作る

def numberedThree : Numbered := Numbered.mk 3 (2 : Fin 3)
def numberedFive : Numbered := Numbered.mk 5 (4 : Fin 5)

#check Numbered.mk 3

-- ### 第一成分を取り出す

def Numbered.size : Numbered → Nat := fun p =>
  match p with
  | Numbered.mk n _ => n

#eval Numbered.size numberedThree

-- ### 第二成分の型も入力から決まる

def Numbered.index (p : Numbered) : Fin (Numbered.size p) :=
  match p with
  | Numbered.mk _ i => i

#check Numbered.index numberedThree

-- ### 一般の依存和

inductive FamilyPair (A : Type) (B : A → Type) : Type where
  | mk (a : A) (b : B a) : FamilyPair A B

def numberedSigma : (n : Nat) × Fin n := Sigma.mk 3 (2 : Fin 3)

#check numberedSigma

-- ### すべての添字で選ぶか、一つの添字を選ぶか

/- ✏ 練習
44. `n : Nat` から、大きさが `n + 1` で番号が最後の `n` である組を返す
   `attachLast : Nat → Numbered` を定義せよ。標準の `Fin.last : (n : Nat) → Fin (n + 1)` を使ってよい。
   `Numbered.size (attachLast 3)` と `Numbered.index (attachLast 3)` の値も確かめよ。
-/

-- ## 4. 自然数と再帰

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat.succ (MyNat.succ MyNat.zero)

-- ### 自分より小さい項を使う

def myAdd : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | MyNat.zero => m
  | MyNat.succ k => MyNat.succ (myAdd m k)

#reduce myAdd (MyNat.succ MyNat.zero) (MyNat.succ MyNat.zero)

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def loop (n : MyNat) : MyNat := loop n

/- ✏ 練習
45. `MyNat.zero` を `0` に、`MyNat.succ k` を `toNat k + 1` に送る
   `toNat : MyNat → Nat` を再帰で定義せよ。
-/

-- ### 各自然数への証明を再帰で作る

def zero_add_by_rec : ∀ n : Nat, 0 + n = n := fun n =>
  match n with
  | Nat.zero => rfl
  | Nat.succ k => congrArg Nat.succ (zero_add_by_rec k)

-- ### 補足: 定義から計算して一致することと、等式を証明すること

def add_zero_by_rfl (n : Nat) : n + 0 = n := rfl

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def zero_add_bad (n : Nat) : 0 + n = n := rfl

def zero_mul_by_rec : ∀ n : Nat, 0 * n = 0 := fun n =>
  match n with
  | Nat.zero => rfl
  | Nat.succ k => zero_mul_by_rec k

-- （補足・先取りここまで）

-- ### 補足: 2n = n + n を定義から証明する

def succ_add_from_scratch : ∀ n m : Nat, (n + 1) + m = (n + m) + 1 := fun n m =>
  match m with
  | Nat.zero => rfl
  | Nat.succ k => congrArg (fun x => x + 1) (succ_add_from_scratch n k)

def two_mul_from_scratch : ∀ n : Nat, 2 * n = n + n := fun n =>
  match n with
  | Nat.zero => rfl
  | Nat.succ k =>
    Eq.trans (congrArg (fun x => x + 2) (two_mul_from_scratch k))
      (Eq.symm (congrArg (fun x => x + 1) (succ_add_from_scratch k k)))

#check two_mul_from_scratch

#print axioms two_mul_from_scratch

-- （補足・先取りここまで）

-- ## 5. 等式と自然数の不等式

-- ### Eq の構成子を読む

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive Eq {A : Sort u} : A → A → Prop where
--   | refl (a : A) : Eq a a

-- ### 対称性を自分で証明する

def eqSymmByMatch {A : Sort u} {a b : A} (h : a = b) : b = a :=
  match h with
  | Eq.refl _ => Eq.refl a

-- ### 推移性を証明する

def eqTransByMatch {A : Sort u} {a b c : A}
    (hab : a = b) (hbc : b = c) : a = c :=
  match hbc with
  | Eq.refl _ => hab

-- ### congrArg に相当する関数を作る

def congrArgByMatch {A : Sort u} {B : Sort v}
    (f : A → B) {a b : A} (h : a = b) : f a = f b :=
  match h with
  | Eq.refl _ => Eq.refl (f a)

#print axioms eqSymmByMatch

-- ### 補足: 等式をもう一つ作る実験

inductive MyEq {A : Type} (a : A) : A → Prop where
  | refl : MyEq a a

#check MyEq

def MyEq.symm {A : Type} {a b : A} (h : MyEq a b) : MyEq b a :=
  match h with
  | MyEq.refl => MyEq.refl

def MyEq.trans {A : Type} {a b c : A} (h₁ : MyEq a b) (h₂ : MyEq b c) : MyEq a c :=
  match h₁ with
  | MyEq.refl => h₂

def MyEq.toEq {A : Type} {a b : A} (h : MyEq a b) : a = b :=
  match h with
  | MyEq.refl => Eq.refl a

def MyEq.ofEq {A : Type} {a b : A} (h : a = b) : MyEq a b :=
  match h with
  | Eq.refl _ => MyEq.refl

-- （補足・先取りここまで）

-- ### 自然数の不等式 Nat.le

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive Nat.le (n : Nat) : Nat → Prop where
--   | refl : Nat.le n n
--   | step {m} : Nat.le n m → Nat.le n (Nat.succ m)

-- ### 2 ≤ 4 の証明を作る

def two_le_four : 2 ≤ 4 := Nat.le.step (Nat.le.step Nat.le.refl)

#check Nat.le.step two_le_four

-- ### 両辺に一つ加えても順序は保たれる

def succLeSuccByMatch (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 :=
  match h with
  | Nat.le.refl => Nat.le.refl
  | Nat.le.step h' => Nat.le.step (succLeSuccByMatch n _ h')

/- ✏ 練習
46. `1 ≤ 3` の証明を `Nat.le.refl` と `Nat.le.step` だけで作れ。
   次に、それを `succLeSuccByMatch` に渡して得られる証明の型を答えよ。
-/

/- 6. ✏ 練習 — 章末問題
構成子を使って項を作ることと、`match` で使うことを組み合わせよう。
本体を書く前に、受け取る項と返す項の型を確認する。

47. 族 `B : A → Type` と依存関数 `f : (a : A) → B a` がある。
   各 `a` に組 `(a, f a)` を対応させる `graphOf` を、`FamilyPair` の構成子で定義せよ。

48. `leAddRight : ∀ n k : Nat, n ≤ n + k` を、`k` に関する再帰で証明せよ。
   零の場合は `Nat.le.refl`、次の数の場合は再帰呼び出しと `Nat.le.step` を使う。

49. 自然数 `n m` と、`h : n = m`、`hn : 0 ≤ n` を受け取り、`0 ≤ m` を返す
   `zeroLeOfEq` を定義せよ。`h` を `match` で使い、枝の中で要求される型を説明せよ。
-/
