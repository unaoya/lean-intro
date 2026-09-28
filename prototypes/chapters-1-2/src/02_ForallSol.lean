import «02_Forall»

/-!
試作第2章の解答。証明はすべて def で定義する。
-/

/-! SOL Trial2.injective-composition-exercise-8bd08815:1 -/

def comp_monotone (f g : Nat → Nat)
    (hf : ∀ x y : Nat, x ≤ y → f x ≤ f y)
    (hg : ∀ u v : Nat, u ≤ v → g u ≤ g v) :
    ∀ x y : Nat, x ≤ y → g (f x) ≤ g (f y) :=
  fun x y h => hg (f x) (f y) (hf x y h)

/-!
`x`、`y` と `h : x ≤ y` を受け取り、`hf x y h : f x ≤ f y` を作る。
これを `hg (f x) (f y)` に渡せばよい。
単射の合成とは逆に、もとの不等式から像の不等式へ進む。
-/

/-! SOL Trial2.practice-review-1:1 -/

#check 3 = 5

/-!
    3 = 5 : Prop
-/

#check 5 = 5

/-!
    5 = 5 : Prop

どちらも命題なので型は `Prop`。`#check` は、命題を表す項の型を調べている。
真偽や証明の有無を調べているわけではない。
-/

/-! SOL Trial2.practice-review-2:1 -/

def two_add_three : 2 + 3 = 5 := rfl

/-!
左辺を計算すると `5` になり、右辺と一致するので `rfl` が使える。
-/

/-! SOL Trial2.practice-review-2:2 -/

/-!
受理されない。`2 + 2` を計算した `4` と、右辺の `5` が一致しない。
エラーには次の説明が現れる。

    error: Not a definitional equality: the left-hand side
      2 + 2
    is not definitionally equal to the right-hand side
      5

一般に、`rfl` が使えないだけで命題が偽だとは判断できない。
ここで失敗したのは、計算して両辺を一致させるという確かめ方である。
-/

/-! SOL Trial2.practice-review-4:1 -/

#check all_refl 12

/-!
    all_refl 12 : 12 = 12
-/

#check fun n : Nat => all_refl (n + 1)

/-!
    fun n ↦ all_refl (n + 1) : ∀ (n : Nat), n + 1 = n + 1

`all_refl` に `n + 1` を渡すので、返される証明の型にも `n + 1` が入る。
全体は `n` を受け取って、その等式の証明を返す依存関数である。
-/

/-! SOL Trial2.practice-exercise-bab90c50:1 -/

def three_comp_injective (A B C D : Type)
    (f : A → B) (g : B → C) (k : C → D)
    (hf : ∀ x y, f x = f y → x = y)
    (hg : ∀ x y, g x = g y → x = y)
    (hk : ∀ x y, k x = k y → x = y) :
    ∀ x y, k (g (f x)) = k (g (f y)) → x = y :=
  fun x y h => hf x y (hg (f x) (f y) (hk (g (f x)) (g (f y)) h))

/-!
最初に `hk` で `g (f x) = g (f y)`、次に `hg` で `f x = f y`、
最後に `hf` で `x = y` を得る。外側の写像の単射性から順に使う。
-/

/-! SOL Trial2.practice-review-6:1 -/

def cancel_pointwise_again (X A B : Type)
    (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y)
    (u v : X → A) (h : ∀ t : X, f (u t) = f (v t)) :
    ∀ t : X, u t = v t :=
  fun t => hf (u t) (v t) (h t)

/-!
`h` は全称命題の証明なので、まず対象 `t` を渡す。
得られた `h t : f (u t) = f (v t)` が、`hf (u t) (v t)` の要求する入力である。
各点で `u t = v t` の証明を作り、`fun t => …` で全体の証明にする。
-/

/-! SOL Trial2.practice-exercise-bab90c50:2 -/

def leftCompose (X A B : Type) (f : A → B) :
    Map (Map X A) (Map X B) :=
  fun u => fun t => f (u t)

/-!
この写像の単射性を証明する。
-/

def leftCompose_injective (X A B : Type) (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y) :
    ∀ u v : Map X A,
      leftCompose X A B f u = leftCompose X A B f v →
      u = v :=
  fun u v h =>
    funext (fun t =>
      hf (u t) (v t) (congrArg (fun w : Map X B => w t) h))

/-!
`congrArg` で得た証明の型は、定義を展開すると `f (u t) = f (v t)` となる。
`hf` で `u t = v t` を得て、各点の証明を `funext` に渡すと `u = v` が得られる。
-/

/-! SOL Trial2.practice-exercise-bab90c50:3 -/

def injective_of_pointwise_cancel (f : Nat → Nat)
    (hcancel : ∀ u v : Nat → Nat,
      (∀ t : Nat, f (u t) = f (v t)) → ∀ t : Nat, u t = v t) :
    ∀ x y : Nat, f x = f y → x = y :=
  fun x y h => hcancel (fun _ => x) (fun _ => y) (fun _ => h) 0

/-!
定数関数 `fun _ => x` と `fun _ => y` を渡す。
それらに `f` を合成した結果が各点で等しいことは、どの点でも `h` を返して示せる。
`hcancel` の結論に対象 `0` を渡せば、`x = y` が得られる。
ここでは、前提の証明を返す関数自体も、引数として渡している。
-/

/-! SOL Trial2.practice-exercise-bab90c50:4 -/

def three_comp_monotone (f g k : Nat → Nat)
    (hf : ∀ x y, x ≤ y → f x ≤ f y)
    (hg : ∀ x y, x ≤ y → g x ≤ g y)
    (hk : ∀ x y, x ≤ y → k x ≤ k y) :
    ∀ x y, x ≤ y → k (g (f x)) ≤ k (g (f y)) :=
  fun x y h => hk (g (f x)) (g (f y)) (hg (f x) (f y) (hf x y h))

/-!
`hf`、`hg`、`hk` の順に、内側の写像から単調性を使う。
それぞれの結果の不等式が、次の単調性の仮定になる。
-/

/-! SOL Trial2.practice-review-10:1 -/

/-!
三つの型は次のとおり。

    Eq.symm (hgf x) : x = g (f x)
    congrArg g h : g (f x) = g (f y)
    hgf y : g (f y) = y

並べると、数学の証明の三つの等号になる。
`Eq.trans` に渡すときには、一つ目の右辺と二つ目の左辺が一致している。
-/

/-! SOL Trial2.practice-exercise-bab90c50:5 -/

def left_inverse_of_right_inverse (A B : Type) (f : A → B) (g : B → A)
    (hf : ∀ x y : A, f x = f y → x = y)
    (hfg : ∀ y : B, f (g y) = y) :
    ∀ x : A, g (f x) = x :=
  fun x => hf (g (f x)) x (hfg (f x))

/-!
比べたい二つの対象は `g (f x)` と `x` である。
それらに `f` を適用した結果の等式 `f (g (f x)) = f x` は、`hfg (f x)` が与える。
この証明を単射性に渡せばよい。等号の書き換えをせず、二つの仮定の適用で証明できる。
-/
