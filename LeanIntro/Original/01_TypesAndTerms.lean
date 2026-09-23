-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。
-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。

-- # 型と項 I — 関数と依存関数型

-- ## 1. 項と型

#check 3

#check true

#check Nat

#check Type

-- ### 補足（初読は飛ばしてよい）: 宇宙の階段

#check Type 1

-- （補足・先取りここまで）

#check 3 + 4

#check 1 + 1 = 2

#check 2 < 1

#check Prop

/- ✏ 練習
1. `#check Bool` と `#check Type 2` の表示を予想してから確かめよ。
2. `#check 3 < 5` と `#check 5 < 3` の表示をそれぞれ予想してから確かめよ。
   命題の真偽が異なっても、同じ型が付くことを説明せよ。
-/

-- ## 2. def — 新しい項を定義する

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def 名前 : 型 := 項

def x : Nat := 2

#check x

def y : Nat := x

#check y

#eval x

#print x

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def bad : Nat := true

-- ### コメントと docstring

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def x : Nat := 2   -- `--` から行末まではコメント
--
-- /- 複数行にわたる
--    コメントはこう書く -/

/- ✏ 練習
3. `def z : Nat := 5` を自分で宣言し、`#check z`・`#eval z`・`#print z`
   の表示をそれぞれ予想してから確かめよ。
4. 本文の `def x : Nat := 2` が使える状態で、`def oops : Bool := x` は受理されるか。
   予想してから試し、エラーメッセージを本文の例と見比べよ。
   別のファイルで試す場合は、先に `def x : Nat := 2` を書くこと。
-/

-- ## 3. 関数

def double : Nat → Nat := fun n => n + n

#check double

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def bad2 : Nat → Nat := fun n => true

-- ### 適用の書き方

#check double 21

#eval double 21

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- #check double true

/- ✏ 練習（書く）
5. 関数 inc : ℕ → ℕ を inc(n) = n + 1 で定める。これを `fun` を用いて Lean で定義せよ。
   `#check inc` の型と `#eval inc 4` の値を予想してから確かめよ。
6. 関数 f : ℕ → ℕ を f(n) = 2n + 3 で定める。これを `fun` を用いて Lean で定義せよ
   （掛け算は `*` と書く）。`#check f` の型と `#eval f 4` の値を予想してから確かめよ。
-/

-- ### 表示の読み方: binder 形式

def double' (n : Nat) : Nat := n + n

#check double'

/- ✏ 練習
7. 関数 triple : ℕ → ℕ、triple(n) = n + n + n を binder 形式で定義せよ。
   `#check triple` の表示を予想してから確かめよ。
8. `#eval double (double 5)` の値を予想してから実行せよ。
9. 先ほどの inc(n) = n + 1 を、今度は binder 形式で `inc'` という名前で定義せよ。
   `#check inc'` の表示と `#eval inc' 4` の値を予想して確かめ、`inc` と比較せよ。
10. 同様に f(n) = 2n + 3 を、binder 形式で `f'` という名前で定義せよ。
   `#check f'` の表示と `#eval f' 4` の値を予想して確かめ、`f` と比較せよ。
-/

-- ### 多変数関数はカリー化で表す

def plus : Nat → Nat → Nat := fun a => fun b => a + b

#check plus

#check plus 3

#check plus 3 4

#eval plus 3 4

/- ✏ 練習（書く）
11. 関数 addThree : ℕ → ℕ、addThree(n) = 3 + n を、`plus 3 : Nat → Nat` を使って
   Lean で定義せよ。`#check addThree` と `#eval addThree 4` の表示を予想してから確かめよ。
12. 関数 g : ℕ × ℕ → ℕ、g(a, b) = 2a + 3b を、カリー化して Lean で定義せよ。
   型は `Nat → Nat → Nat` とし、`fun a => fun b => …` を使うこと。
   `#check g`・`#check g 2` の型と `#eval g 2 4` の値を予想してから確かめよ。
-/

-- ### 多変数関数の binder 形式

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def plus (a : Nat) (b : Nat) : Nat := a + b

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def plus (a b : Nat) : Nat := a + b

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def plus : Nat → Nat → Nat := fun a b => a + b

/- ✏ 練習（書く）
13. 先ほどの g(a, b) = 2a + 3b を、binder 形式で2通りに書け。
   `g'` は `(a : Nat) (b : Nat)` と分け、`g''` は `(a b : Nat)` とまとめること。
   `#check g'`・`#check g''` の表示と、`#eval g' 2 4`・`#eval g'' 2 4` の値を
   予想してから確かめよ。
-/

def addMul (a b c : Nat) : Nat := a + b * c

#check addMul

-- ### 関数を引数として受け取る

def applyTo21 (F : Nat → Nat) : Nat := F 21

#check applyTo21

#eval applyTo21 double

-- ### 型の異なる引数の binder 形式

def applyAt (F : Nat → Nat) (n : Nat) : Nat := F n
#check applyAt

/- ✏ 練習（書く）
14. 写像 twice : Map(ℕ, ℕ) → Map(ℕ, ℕ) を、F ↦ (n ↦ F(F(n))) で定める。
   つまり、F を同じ入力に2回使うのではなく、1回目の結果にもう一度 F を適用する。
   これを Lean で `def twice (F : Nat → Nat) : Nat → Nat := …` と定義せよ。
   `#check twice`・`#check twice double` の表示と `#eval twice double 3` の値を
   予想してから確かめよ。
15. 写像 thrice : Map(ℕ, ℕ) → Map(ℕ, ℕ) を、F ↦ (n ↦ F(F(F(n)))) で定める。
   これを Lean で定義し、`#check thrice`・`#check thrice double` の表示と
   `#eval thrice double 3` の値を予想してから確かめよ。
-/

-- ### 定義域や行き先が型でもよい

def Map : Type → Type → Type := fun A B => A → B

#check Map

/- ✏ 練習
16. `#check Map Nat Bool` の表示を予想してから確かめよ。また、数学でいう
   関数 double : ℕ → ℕ、double(n) = n + n を、`Map Nat Nat` 型の項としても使えるか考えよ。
   `def double2 : Map Nat Nat := double` が受理されるか予想してから試せ。
   受理されたら、`#check double2` の表示も予想してから確かめよ。
17. `#check Map Nat` の表示を予想してから確かめよ
   （`Map` に1つだけ渡すと、何が返るか。`plus 3` の型を読んだのと同じ手順で考える）。
-/

-- ### 先取り（詳しくは 05_MathematicalTools）: `Nat.add` と `HAdd.hAdd`

#check Nat.add

#check (HAdd.hAdd : Nat → Nat → Nat)

-- （補足・先取りここまで）

-- ### 型はどう決まるか——下から計算し、上から期待を伝える

#check 2

#check (2 : Int)

#check (2 + 3 : Int)

#check double (plus 3 4)

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- #check double plus

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def later : Nat := sorry

/- ✏ 練習
18. `#check` する**前に**型を計算せよ: `(3 + 4) * 2`、`plus (double 3)`、
   `applyTo21 (plus 3)`、`fun n : Nat => plus n n`。それから確かめよ。
19. `#eval applyTo21 (plus 100)` の値を予想してから実行せよ。
20. 次の2つの写像を Lean で定義し、`#check` の表示を予想してから確かめよ:
   * evalAt : Map(ℕ, ℕ) × ℕ → ℕ、evalAt(F, n) = F(n)。カリー化して定義すること。
     `#eval evalAt double 5` の値も予想してから実行せよ。
   * shift : Map(ℕ, ℕ) → Map(ℕ, ℕ)、F ↦ (n ↦ F(n + 1))。
     関数を受け取って**関数を返す**関数である。
     `#eval shift double 3` の値も予想してから実行せよ。
21. 「型から項を書く」練習: Map(ℕ, ℕ) → ℕ という写像を、**中身の違うもので2つ**考えよ
   （例えば F ↦ F(21) と F ↦ 0）。それらを Lean で `useF1`・`useF2` と名付けて定義し、
   型を予想してから `#check` で確かめよ。どちらも `(Nat → Nat) → Nat` 型になるはずである。
   同じ型に項は何通りもある——型は仕様であって、中身までは決めない。
22. （発展）写像 G : B → C と F : A → B に合成 G ∘ F : A → C を対応させる写像を考える。
   型 A・B・C も引数に取り、これを Lean で
   `compose (A B C : Type) (G : B → C) (F : A → B) : A → C` と定義せよ。
   `#check compose` の表示と、
   `#eval compose Nat Nat Nat double (fun n => n + 1) 3` の値を予想してから
   確かめよ。
23. （発展）`evalAt` と `shift` を一般化し、任意の A・B に対する写像 Map(A, B) × A → B、(F, a) ↦ F(a) と、
   写像 g : A → A に対する変換 Map(A, A) → Map(A, A)、F ↦ (a ↦ F(g(a))) を考える。
   型や g も引数として受け取るように、Lean で
   `evalAt' (A B : Type) (F : A → B) (a : A) : B` と
   `shift' (A : Type) (g : A → A) (F : A → A) : A → A` を定義せよ。
   両者の `#check` の表示と、
   `#eval evalAt' Nat Nat double 5` と `#eval shift' Nat (fun x => x + 1) double 3`
   の値を予想してから確かめ、元の版と比較せよ。
-/

-- ## 4. 依存関数型 — 入力によって結果の型が変わる

def idAt (α : Type) (a : α) : α := a

#check idAt

#check idAt Nat

#check idAt Bool

#eval idAt Nat 42

-- ### 数を添字にする型の族

#check Fin

def Tuple : Nat → Type := fun n => Fin n → Nat

#check Tuple

#check Tuple 3

def constTuple : (n : Nat) → Tuple n :=
  fun n => fun (_i : Fin n) => 7

#check constTuple

#check constTuple 3

#check constTuple 4

-- ### 数を返す依存関数の例

def zeroIndex : (n : Nat) → Fin (n + 1) := fun _ => 0

#check zeroIndex

#check zeroIndex 2

#check zeroIndex 4

-- ### 依存する適用の規則

/- ✏ 練習
24. `#check idAt (Nat → Nat)` の表示と、`#eval idAt (Nat → Nat) double 21` の値を予想せよ。
25. 集合 A の要素 a に対して、集合 B 上の定数写像を対応させる
   `constAt (A B : Type) (a : A) : B → A` を書け。
   `#check constAt Nat Bool 5` と `#eval constAt Nat Bool 5 true` を確かめよ。
-/

/- ✏ 練習
26. `Tuple 2` を定義で展開すると、どんな型になるか。
   `constTuple 2` の内側の引数と結果の型を答えよ。
27. n と自然数 a を受け取り、すべての成分が a である n 個組を返す
   `repeatTuple (n : Nat) (a : Nat) : Tuple n` を書け。
-/

-- ### 型引数を補ってもらう — 明示引数と暗黙引数

def idImplicit {α : Type} (a : α) : α := a

#check idImplicit

#check idImplicit 3

#check idImplicit true

-- ### 補足（初読は飛ばしてよい）: ライブラリにもある型の族

#check Vector Nat 3

def zeros : (n : Nat) → Vector Nat n := fun n => Vector.replicate n 0

#check zeros 3

#check zeros 4

-- （補足・先取りここまで）
