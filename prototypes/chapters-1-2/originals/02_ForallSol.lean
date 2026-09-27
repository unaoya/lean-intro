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
[`04_Exists.lean` の6節](#sec-CH.nat-proofs)の補足「定義的等しさと、等しいことの証明」で説明する。
この例の命題は偽だが、一般に `rfl` が使えないだけで命題が偽だとは判断できない。
補足の `0 + n = n` は、`rfl` では済まなくても証明できる例である。
-/

/-! SOL CH.implication:1 -/

theorem keep_left (P Q : Prop) : P → Q → P :=
  fun hP _ => hP

/-!
最初に受け取った `hP : P` を返す。`Q` の証明は使わなくてよい。
-/

/-! SOL CH.implication:2 -/

theorem use_two (P Q R : Prop)
    (h : P → Q → R) (hP : P) (hQ : Q) : R :=
  h hP hQ

/-!
`h hP : Q → R`、さらに `h hP hQ : R` となる。
-/

/-! SOL CH1.forall-examples:1 -/

section
variable {α β γ : Type} {f : α → β} {g : β → γ}
variable (hg : ∀ u v, g u = g v → u = v) (hf : ∀ x y, f x = f y → x = y)
variable (x y : α) (h : g (f x) = g (f y))

#check hg (f x) (f y) h

/-!
    hg (f x) (f y) h : f x = f y
-/

#check hf x y (hg (f x) (f y) h)

/-!
    hf x y (hg (f x) (f y) h) : x = y

`hg` を使って `f x = f y` の証明を作り、それを `hf` に渡すと `x = y` の証明になる。
上の `section` と `variable` は、この確認に使う仮定をまとめて置いている。
-/

end

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
