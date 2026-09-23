import CH

/-!
`CH.lean` の ✏ 練習の解答。本文と同じく、引数はすべて宣言の中に書いてある。
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

theorem imp_trans3
    (P Q R S : Prop)
    (hPQ : P → Q)
    (hQR : Q → R)
    (hRS : R → S) :
    P → S :=
  fun hP => hRS (hQR (hPQ hP))

/-!
内側から `hPQ hP : Q`、`hQR (hPQ hP) : R`、
`hRS (hQR (hPQ hP)) : S` と型が決まる。
-/

/-! SOL CH.reading-proofs:1 -/

/-!
`h : g (f x) = g (f y)` を `hg` に渡すと
`hg (f x) (f y) h : f x = f y`。それを `hf` に渡すと
`hf x y (hg (f x) (f y) h) : x = y` となる。
-/

/-! SOL CH.reading-proofs:2 -/

theorem id_injective (α : Type) : Function.Injective (fun x : α => x) :=
  fun x y h => (h : x = y)

/-!
恒等関数について仮定される等式は最初から `x = y` なので、その証明 `h` を
そのまま返せばよい。
-/

/-! SOL CH.reading-proofs:1 -/

/-!
`match` の枝では `a : α`、`ha : Q a`。したがって
`hqr a : Q a → R a`、`hqr a ha : R a` となる。
-/

/-! SOL CH.reading-proofs:2 -/

theorem exists_map2 {α : Type} {P Q R : α → Prop} :
    (∀ a, P a → Q a) → (∀ a, Q a → R a) → (∃ a, P a) → ∃ a, R a :=
  fun hpq hqr h =>
    match h with
    | ⟨a, ha⟩ => ⟨a, hqr a (hpq a ha)⟩

/-!
存在証明から取り出した証人 `a` はそのまま使い、根拠だけを
`P a → Q a → R a` と2段階で移している。
-/

/-! SOL CH.reading-proofs:1 -/

theorem isEven_two_mul : ∀ n : Nat, IsEven (2 * n) :=
  fun n => ⟨n, rfl⟩

/-!
証人は `n`。示すべき根拠は `2 * n = 2 * n` そのものなので、`rfl` で済む
（`isEven_double` では `n + n = 2 * n` の変形が要ったが、ここでは
両辺が字面から一致している）。
-/

/-! SOL CH.reading-proofs:2 -/

/-!
**ふつうの証明**:

1. 仮定 `IsEven n` を分解し、`k` と `hk : n = 2 * k` を得る。
2. `hk` の両辺に右から 2 を足して、`n + 2 = 2 * k + 2`。
3. `2 * k + 2 = 2 * (k + 1)` は、既知の定理
   `Nat.mul_succ 2 k : 2 * (k + 1) = 2 * k + 2` の対称形。
4. 2〜3 をつないで `n + 2 = 2 * (k + 1)`。よって証人 `k + 1` で偶数である。∎

（1行で書けば「`n = 2k` と書けると `n + 2 = 2k + 2 = 2(k + 1)`。∎」である。）

**論理式**: ∀n (Even(n) → Even(n + 2))。

**形式化を意識した版**: 仮定を取る（ならばの証明）。`hn` は存在文なので、
取り出して `k` と `hk` に名前を付ける（存在の使い方）。示すべきは
（定義に戻ると）「`n + 2 = 2j` となる `j` の存在」。候補は `j = k + 1` で、
性質 `n + 2 = 2 * (k + 1)` は等式の連鎖——`hk` の両辺に `(· + 2)` を施し、
`Nat.mul_succ` の対称形とつなぐ。

**項**:
-/

theorem isEven_add_two : ∀ n : Nat, IsEven n → IsEven (n + 2) :=
  fun _ hn =>
    match hn with
    | ⟨k, hk⟩ => ⟨k + 1, (congrArg (· + 2) hk).trans (Nat.mul_succ 2 k).symm⟩

/-!
本文の例5と同じ部品（`match` の分解・`congrArg`・`.trans`・証人の組）だけで
書けている。
-/

/-! SOL CH.reading-proofs:3 -/

example : IsEven 10 := ⟨5, rfl⟩

/-!
証人 `5`、根拠は `10 = 2 * 5`——計算で一致するので `rfl`。
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
受理されない。`rfl` の型は `a = a` の形しか取れないのに、
宣言された型は `2 + 2 = 5`——両辺が計算で一致しない——だからである:

    theorem oops : 2 + 2 = 5 := rfl

    error: Not a definitional equality: the left-hand side
      2 + 2
    is not definitionally equal to the right-hand side
      5

「`rfl` は両辺が計算で一致するときだけ使える」という規則の破れが
そのまま報告されている。
-/

/-! SOL CH.implication:1 -/

def apply2 {α : Type} : (α → α) → α → α := fun f a => f (f a)

theorem applyTwice {p : Prop} : (p → p) → p → p := fun f h => f (f h)

/-!
`:=` の右は同じ字面。型の世界の「関数を2回適用」と、命題の世界の
「推論を2回適用」が、同じ項で書ける。
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

#check applyFun Nat.succ 3

/-!
    applyFun Nat.succ 3 : Nat

`f = Nat.succ`（`β = Nat`）、`a = 3` が代入され、結果の型は `Nat`。
-/

/-! SOL CH.products:1 -/

theorem and_left {p q : Prop} : p ∧ q → p := fun h => h.1

def fst' {α β : Type} : α × β → α := fun x => x.1

/-!
`∧` の証明の組から第1成分を取り出すのと、直積の組から第1成分を
取り出すのが、同じ字面 `.1` で書ける。
-/

/-! SOL CH.products:2 -/

theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩

/-!
左の入れ子から `.1.1`・`.1.2`・`.2` で3つの証明を取り出し、
右の入れ子の形に `⟨…⟩` で組み直す。
-/

/-! SOL CH.products:3 -/

example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩

/-!
具体的な命題でも、`∧` の示し方は「証明を2つ組にする」だけである。
-/

/-! SOL CH.sums:1 -/

theorem or_idem {p : Prop} : p ∨ p → p := fun h =>
  match h with
  | .inl hp => hp
  | .inr hp => hp

/-!
どちらの札でも中身は `p` の証明なので、そのまま返す。
-/

/-! SOL CH.sums:2 -/

theorem or_map {p q r : Prop} : (p → q) → p ∨ r → q ∨ r := fun f h =>
  match h with
  | .inl hp => .inl (f hp)
  | .inr hr => .inr hr

/-!
左の札のときだけ `f` を適用し、右の札はそのまま包み直す。
-/

/-! SOL CH.sums:3 -/

example : (1 = 2) ∨ (2 = 2) := .inr rfl

/-!
通る。`∨` を示すには片側の証明だけでよいので、左が偽の命題でも構わない。
-/

/-! SOL CH.empty-types:1 -/

theorem noContra {p q : Prop} : p → ¬p → q :=
  fun hp hnp => (hnp hp).elim

/-!
`hnp hp : False` ができるので、`False.elim` でどんな命題でも導ける。
-/

/-! SOL CH.empty-types:2 -/

theorem dni {p : Prop} : p → ¬¬p := fun hp hnp => hnp hp

/-!
`¬¬p` は `(p → False) → False`。`hnp : p → False` を受け取って
`hp` に適用するだけである。

逆向き `¬¬p → p` は書けない。手持ちは `hnn : (p → False) → False` だけで、
これをどう適用しても出てくるのは `False` であって、`p` の証明を**作る**
手段がない。この向きに必要なのが背理法（`Classical.byContradiction`）で、
[`Top.lean` 2節](#sec-Top.sets)の `compl_compl` がそれを使う。代償（公理への依存）は
本文末尾の公理の節のとおり。
-/

/-! SOL CH.empty-types:3 -/

example : ¬False := fun h => h

/-!
`¬False` は `False → False`——恒等関数が証明になる。
-/

/-! SOL CH.dependent-products:1 -/

theorem all_and {α : Type} {Q R : α → Prop} :
    (∀ a, Q a) → (∀ a, R a) → ∀ a, Q a ∧ R a :=
  fun hq hr a => ⟨hq a, hr a⟩

/-!
点 `a` を任意に取り、2つの一般論をその点で使って組にする。
-/

/-! SOL CH.dependent-products:2 -/

example : IsZero (0 * 5) := rfl

example : IsZero (5 * 0) := rfl

example : IsZero (5 * 0) := all_mul_zero 5

/-!
どれも通る。`0 * 5` も `5 * 0` も計算で `0` になるので `rfl` でよく、
後者は一般論 `all_mul_zero` に点 `5` を代入しても証明できる。
-/

/-! SOL CH.dependent-products:3 -/

#check applyForall all_mul_zero 7

/-!
    applyForall all_mul_zero 7 : IsZero (7 * 0)

`∀ n, IsZero (n * 0)` に点 `7` を代入した、特殊化された命題の証明になる。
-/

/-! SOL CH.dependent-sums:1 -/

theorem exists_left {α : Type} {Q R : α → Prop} :
    (∃ a, Q a ∧ R a) → ∃ a, Q a :=
  fun h =>
    match h with
    | ⟨a, hq, _⟩ => ⟨a, hq⟩

/-!
`∃` を分解して証人 `a` と根拠 `Q a ∧ R a` を取り出す。証人はそのまま、
根拠の左側 `hq : Q a` だけを包み直す。
-/

/-! SOL CH.dependent-sums:2 -/

#check (last 4).val

/-!
    ↑(last 4) : Nat

`.val` の適用が強制の印 `↑` で表示される。型は `Fin 5` の中身の `Nat`。
-/

/-! SOL CH.dependent-sums:3 -/

example : ∃ n : Nat, IsZero n := ⟨0, rfl⟩

/-!
証人 `0` と、`IsZero 0` すなわち `0 = 0` の証明 `rfl` の組である。
-/

/-! SOL CH.introduction-elimination:1 -/

theorem andToOr {p q : Prop} : p ∧ q → p ∨ q := fun h => .inl h.1

/-!
`∧` から `.1` で `p` の証明を取り出し、`∨` を示す形 `.inl` で包む。
（`.2` と `.inr` の組み合わせでもよい。）
-/

/-! SOL CH.nat-proofs:1 -/

example : 1 ≤ 3 := Nat.le.step (Nat.le.step Nat.le.refl)

/-!
`Nat.le.refl : 1 ≤ 1` から `step` を2回。`1 ≤ 2`、`1 ≤ 3` と1段ずつのぼる。
-/

/-! SOL CH.nat-proofs:2 -/

theorem MyEq.trans {α : Type} {a b c : α} (h₁ : MyEq a b) (h₂ : MyEq b c) :
    MyEq a c :=
  match h₂ with
  | .refl => h₁

/-!
`h₂` を場合分けすると構成子は `refl` しかなく、その枝では `c` は `b` と
同じものになる。するとゴールは `MyEq a b` に変わり、`h₁` がそのまま合う。
-/

/-! SOL CH.nat-proofs:3 -/

theorem MyEq.ofEq {α : Type} {a b : α} (h : a = b) : MyEq a b :=
  match h with
  | rfl => MyEq.refl

/-!
今度は `Eq` の側で場合分けする。構成子は `rfl` しかなく、その枝では
`b` は `a` と同じものになるので、`MyEq a a` の構成子 `refl` を置けばよい。
-/

/-! SOL CH.type-checking:1 -/

#check @Nat.add_sub_cancel

/-!
    Nat.add_sub_cancel : ∀ (n m : Nat), n + m - m = n

丸括弧＝明示引数なので、使うときは `n` と `m` を実際に渡す:
-/

example : ∀ n : Nat, n + 1 - 1 = n := fun n => Nat.add_sub_cancel n 1

/-!
`m := 1` とした `n + 1 - 1 = n` がちょうどゴールの形で、今度は穴が残らない。
-/

/-! SOL CH.type-checking:2 -/

#eval (3 : Nat) - 5

/-!
    0

自然数の引き算は `0` で切り捨てられる。
-/

/-! SOL CH.prop-elimination:1 -/

/-!
本文のとおり、次のエラーになる:

    def existsFst (h : ∃ a, Q a) : α := h.1

    error: Invalid projection: Cannot project a value of non-propositional type
      α
    from the expression
      h
    which has propositional type
      ∃ a, Q a

「命題の証明から、命題でないもの（ここでは `α` の項）を取り出すことは
許されない」という規則の破れが報告されている。
-/
