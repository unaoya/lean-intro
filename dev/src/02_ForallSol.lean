import «02_Forall»

/-!
`02_Forall.lean` の練習の解答。本文の順に、型と項を確かめる。
-/

/-! SOL CH.reading-proofs:1 -/

#check fun (P Q : Prop) (hP : P) (hPQ : P → Q) => hPQ hP

/-!
    fun P Q hP hPQ ↦ hPQ hP : ∀ (P Q : Prop), P → (P → Q) → Q

`hPQ : P → Q` の入力型 `P` と `hP : P` が一致するので、適用結果の型は
`hPQ` の出力型 `Q` になる。
-/

/-! SOL CH.reading-proofs:2 -/

theorem use_imp (P Q : Prop) (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP

/-!
引数の順が変わっても、適用する項 `hPQ hP` は変わらない。
-/

/-! SOL CH.reading-proofs:1 -/

theorem imp_refl (P : Prop) : P → P :=
  fun hP => hP

/-!
受け取った `hP : P` をそのまま返すので、関数全体の型は `P → P`。
-/

/-! SOL CH.reading-proofs:2 -/

theorem imp_trans3 (P Q R S : Prop)
    (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) : P → S :=
  fun hP => hRS (hQR (hPQ hP))

/-!
内側から `hPQ hP : Q`、`hQR (hPQ hP) : R`、
`hRS (hQR (hPQ hP)) : S` と型が決まる。
-/

/-! SOL CH.propositions:1 -/

#check 3 < 5

/-!
    3 < 5 : Prop
-/

#check 3 = 5

/-!
    3 = 5 : Prop

`3 = 5` は偽の命題だが、偽の命題も命題——型は同じ `Prop` である。
-/

/-! SOL CH.propositions:2 -/

theorem two_add_three : 2 + 3 = 5 := rfl

/-!
`2 + 3` は計算で `5` になるので、`rfl` が型検査を通る。
-/

/-! SOL CH.propositions:3 -/

/-!
受理されない。`rfl` が与える `a = a` という型を、宣言された型 `2 + 2 = 5` と
照合しようとしても、`2 + 2` と `5` は定義的に等しくないからである。
この宣言を実行すると、エラーに次の部分が現れる:

    theorem oops : 2 + 2 = 5 := rfl

    error: Not a definitional equality: the left-hand side
      2 + 2
    is not definitionally equal to the right-hand side
      5

`Not a definitional equality` は「定義的に等しくない」という意味である。
定義的等しさと、等式を別の証明で示せることの違いは、
[`04_Exists.lean` の5節](#sec-CH2.computation)の補足「定義的等しさと、等しいことの証明」で説明する。
この例の命題は偽だが、一般に `rfl` が使えないだけで命題が偽だとは判断できない。
補足の `0 + n = n` は、`rfl` では済まなくても証明できる例である。
-/

/-! SOL CH.implication:1 -/

def apply2 {α : Type} : (α → α) → α → α := fun f a => f (f a)

theorem applyTwice {p : Prop} : (p → p) → p → p := fun f h => f (f h)

#check apply2

/-!
    apply2 {α : Type} : (α → α) → α → α
-/

#check applyTwice

/-!
    applyTwice {p : Prop} : (p → p) → p → p
-/

/-!
`:=` の右は同じ字面。型の世界の「関数を2回適用」と、命題の世界の
「推論を2回適用」が、同じ項で書ける。

次に、`fun` で受け取っていた引数をコロンの左に移し、binder 形式で書く:
-/

def apply2Binder {α : Type} (f : α → α) (a : α) : α := f (f a)

theorem applyTwiceBinder {p : Prop} (f : p → p) (h : p) : p := f (f h)

#check apply2Binder

/-!
    apply2Binder {α : Type} (f : α → α) (a : α) : α
-/

#check applyTwiceBinder

/-!
    applyTwiceBinder {p : Prop} (f : p → p) (h : p) : p

最後の2つの引数を矢印形式に読み替えれば、それぞれ
`(α → α) → α → α` と `(p → p) → p → p` になる。
宣言の書き方が変わっただけで、型も、受け取った引数から作る項も変わらない。
-/

/-! SOL CH.implication:2 -/

theorem imp_swap {p q r : Prop} : (p → q → r) → q → p → r :=
  fun h hq hp => h hp hq

/-!
外側では `q` の証明、次に `p` の証明を受け取るが、`h` はまず `p`、次に `q`
を要求するので、適用は `h hp hq` の順になる。
-/

/-! SOL CH.implication:3 -/

example : Nat → Nat := fun h => h

example : (1 = 1) → (1 = 1) := fun h => h

/-!
どちらも通る。恒等関数という同じ項が、型の世界でも命題の世界でも働く。
-/

/-! SOL CH.implication:4 -/

#check applyFun double 3

/-!
    applyFun double 3 : Nat

`f = double`（`β = Nat`）、`a = 3` が代入され、結果の型は `Nat`。
-/

/-! SOL CH1.forall-examples:1 -/

/-!
`h : g (f x) = g (f y)` を `hg` に渡すと
`hg (f x) (f y) h : f x = f y`。それを `hf` に渡すと
`hf x y (hg (f x) (f y) h) : x = y` となる。
-/

/-! SOL CH1.forall-examples:2 -/

theorem id_injective (α : Type) : Function.Injective (fun x : α => x) :=
  fun x y h => (h : x = y)

/-!
恒等関数について仮定される等式は最初から `x = y` なので、その証明 `h` を
そのまま返せばよい。
-/

/-! SOL CH.dependent-products:1 -/

#check applyForall all_mul_zero 7

/-!
    applyForall all_mul_zero 7 : IsZero (7 * 0)

`∀ n, IsZero (n * 0)` に点 `7` を代入した、特殊化された命題の証明になる。
-/
