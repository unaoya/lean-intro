-- はじめての Lean — 02_Forall（ブラウザ版・自動生成）
-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、
-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。

-- # 型と命題 I — ならばと全称量化

-- ## 1. 単射の合成 — 対象と仮定を受け取る

/- ✏ 練習
28. `#check 3 = 5` と `#check 5 = 5` の表示を予想せよ。
   `#check` の結果から、命題が真かどうかを判断できるか。
-/

-- ### 単射性を、全称量化と「ならば」で書く

def comp_injective (A B C : Type) (f : A → B) (g : B → C)
    (hf : ∀ x y : A, f x = f y → x = y)
    (hg : ∀ u v : B, g u = g v → u = v) :
    ∀ x y : A, g (f x) = g (f y) → x = y :=
  fun x y h => hf x y (hg (f x) (f y) h)

-- ## 2. 左キャンセル — 関数を引数として受け取る

def cancel_pointwise (X A B : Type) (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y)
    (u v : X → A) (h : ∀ t : X, f (u t) = f (v t)) :
    ∀ t : X, u t = v t :=
  fun t => hf (u t) (v t) (h t)

/- ✏ 練習
29. 単射 f : A→ B と u,v : X→ A、
   `h : ∀ t : X, f (u t) = f (v t)` を受け取ったとする。
   `∀ t : X, u t = v t` の証明を書け。
   `h` 全体を単射性に渡すのではなく、どの項を渡せばよいか説明せよ。
-/

-- ## 3. Eq と rfl — 等式の保証を作る

#check Eq

#check (Eq : Nat → Nat → Prop)

-- ### 自分自身との等式を保証する Eq.refl

#check Eq.refl

#check Eq.refl 2

-- ### rfl は、対象を暗黙引数にしたもの

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def rfl {α : Sort u} {a : α} : a = a := Eq.refl a

#check @rfl

-- ### 計算して一致するときは rfl

def one_add_one : 1 + 1 = 2 := rfl

#check one_add_one

def one_add_one_explicit : 1 + 1 = 2 := Eq.refl 2

/- ✏ 練習
30. `def two_add_three : 2 + 3 = 5 := …` の右辺を `rfl` で埋めよ。
   `rfl` が使える理由を説明せよ。

31. `def oops : 2 + 2 = 5 := rfl` は受理されるか。
   受理されないなら、どの二つの項が計算しても一致しないのかを説明せよ。
-/

-- ### 対象ごとの等式を保証する

def all_refl : ∀ n : Nat, n = n :=
  fun n => (rfl : n = n)

#check all_refl

#check all_refl 7

/- ✏ 練習
32. `all_refl 12` の型を予想せよ。さらに `fun n : Nat => all_refl (n + 1)` の型を答えよ。
-/

-- ### Eq.symm — 等式の向きを逆にする

#check Eq.symm

-- ### Eq.trans — 二つの等式をつなぐ

#check Eq.trans

-- ### congrArg — 両辺に同じ関数を適用する

#check congrArg

-- ## 4. 左逆を持つ写像は単射

def injective_of_left_inverse (A B : Type)
    (f : A → B) (g : B → A)
    (hgf : ∀ x : A, g (f x) = x) :
    ∀ x y : A, f x = f y → x = y :=
  fun x y h =>
    Eq.trans (Eq.symm (hgf x))
      (Eq.trans (congrArg g h) (hgf y))

/- ✏ 練習
33. 左逆の証明で使った `hgf : ∀ x : A, g (f x) = x` と
   `h : f x = f y` があるとする。
   `Eq.symm (hgf x)`、`congrArg g h`、`hgf y` の型を答え、
   それぞれが x=g(f(x))=g(f(y))=y のどの等号に対応するか説明せよ。
-/

-- ## 5. 章末問題

/- ✏ 練習 — 単射と左キャンセル
34. 三つの単射 f : A→ B、g : B→ C、k : C→ D の合成が単射であることを示せ。
   それぞれの単射性を `∀ x y, f x = f y → x = y` の形で仮定し、
   `∀ x y, k (g (f x)) = k (g (f y)) → x = y` の証明を書け。
35. （発展）単射 f:A→ B に対して、写像
   L_f:Map(X,A)\toMap(X,B) を L_f(u)=f∘ u と定めると、L_f も単射である。
   この事実を Lean で形式化せよ。まず `X A B : Type` と `f : A → B` を引数に取り、
   L_f を `leftCompose` という名前で定義せよ。
   次に `hf : ∀ x y : A, f x = f y → x = y` を仮定し、
   `leftCompose X A B f` の単射性の証明を `leftCompose_injective` として書け。

**ヒント1 — 写像を定義する。** Map(X,A) に対応する型は `X → A` である。
`leftCompose X A B f` の型は `(X → A) → (X → B)` である。
関数 `u` を受け取り、さらに対象 `t` を受け取って `f (u t)` を返す項を書こう。

**ヒント2 — 等式を各点で使う。** `u`、`v` と、その像が等しいという証明 `h` を受け取る。
関数を対象 `t` で評価する写像 `fun w : X → B => w t` を `congrArg` に渡すと、
`h` から `f (u t) = f (v t)` の証明を得られる。それを `hf` に渡そう。

**ヒント3 — 関数どうしの等式に戻す。** 各点での等式の証明
`k : ∀ t : X, u t = v t` から、`funext k : u = v` が得られる。
これを**関数外延性**という。`fun t => …` で各点の証明をまとめ、`funext` に渡そう。

36. f : ℕ→ℕ について、任意の u,v : ℕ→ℕ に対する
   点ごとの左キャンセルを仮定する。
   この仮定から f の単射性を示せ。u,v に定数関数を使うとよい。

       hcancel : ∀ u v : Nat → Nat,
         (∀ t : Nat, f (u t) = f (v t)) → ∀ t : Nat, u t = v t

37. 三つの単調写像 f,g,k : ℕ→ℕ の合成が単調であることを示せ。
   本文と同じ形で三つの単調性を仮定し、`fun` と適用だけで証明せよ。
38. f : A→ B が単射で、g : B→ A が f(g(y))=y をすべての y∈ B で満たすとする。
    このとき g(f(x))=x がすべての x∈ A で成り立つことを示せ。
    f の単射性を、どの二つの対象に適用すればよいか考えること。
-/
