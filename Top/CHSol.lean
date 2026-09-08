import CH

/-!
`CH.lean` の ✏ 練習の解答。本文と違い、各解答は変数の前置き（`variable`）に
頼らず、引数をすべて宣言の中に書いてある。
-/

/-! SOL 0.1 -/

#check 3 < 5

/-!
    3 < 5 : Prop
-/

#check 3 = 5

/-!
    3 = 5 : Prop

`3 = 5` は偽の命題だが、偽の命題も命題——型は同じ `Prop` である。
-/

/-! SOL 0.2 -/

theorem two_add_three : 2 + 3 = 5 := rfl

/-!
`2 + 3` は計算で `5` になるので、`rfl` が型検査を通る。
-/

/-! SOL 0.3 -/

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

/-! SOL 1.1 -/

def apply2 {α : Type} : (α → α) → α → α := fun f a => f (f a)

theorem applyTwice {p : Prop} : (p → p) → p → p := fun f h => f (f h)

/-!
`:=` の右は同じ字面。型の世界の「関数を2回適用」と、命題の世界の
「推論を2回適用」が、同じ項で書ける。
-/

/-! SOL 1.2 -/

theorem chain {p q r : Prop} : (p → q) → (q → r) → p → r :=
  fun hpq hqr hp => hqr (hpq hp)

/-!
`hp : p` に「A より B」を適用して `q`、続けて「B より C」を適用して `r`。
-/

/-! SOL 1.3 -/

example : Nat → Nat := fun h => h

example : (1 = 1) → (1 = 1) := fun h => h

/-!
どちらも通る。恒等関数という同じ項が、型の世界でも命題の世界でも働く。
-/

/-! SOL 1.4 -/

#check applyFun Nat.succ 3

/-!
    applyFun Nat.succ 3 : Nat

`f = Nat.succ`（`β = Nat`）、`a = 3` が代入され、結果の型は `Nat`。
-/

/-! SOL 2.1 -/

theorem and_left {p q : Prop} : p ∧ q → p := fun h => h.1

def fst' {α β : Type} : α × β → α := fun x => x.1

/-!
`∧` の証明の組から第1成分を取り出すのと、直積の組から第1成分を
取り出すのが、同じ字面 `.1` で書ける。
-/

/-! SOL 2.2 -/

theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩

/-!
左の入れ子から `.1.1`・`.1.2`・`.2` で3つの証明を取り出し、
右の入れ子の形に `⟨…⟩` で組み直す。
-/

/-! SOL 2.3 -/

example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩

/-!
具体的な命題でも、`∧` の導入は「証明を2つ組にする」だけである。
-/

/-! SOL 3.1 -/

theorem or_idem {p : Prop} : p ∨ p → p := fun h =>
  match h with
  | .inl hp => hp
  | .inr hp => hp

/-!
どちらの札でも中身は `p` の証明なので、そのまま返す。
-/

/-! SOL 3.2 -/

theorem or_map {p q r : Prop} : (p → q) → p ∨ r → q ∨ r := fun f h =>
  match h with
  | .inl hp => .inl (f hp)
  | .inr hr => .inr hr

/-!
左の札のときだけ `f` を適用し、右の札はそのまま包み直す。
-/

/-! SOL 3.3 -/

example : (1 = 2) ∨ (2 = 2) := .inr rfl

/-!
通る。`∨` の導入は片側の証明だけでよいので、左が偽の命題でも構わない。
-/

/-! SOL 4.1 -/

theorem noContra {p q : Prop} : p → ¬p → q :=
  fun hp hnp => (hnp hp).elim

/-!
`hnp hp : False` ができるので、`False.elim` でどんな命題でも導ける。
-/

/-! SOL 4.2 -/

theorem dni {p : Prop} : p → ¬¬p := fun hp hnp => hnp hp

/-!
`¬¬p` は `(p → False) → False`。`hnp : p → False` を受け取って
`hp` に適用するだけである。

逆向き `¬¬p → p` は書けない。手持ちは `hnn : (p → False) → False` だけで、
これをどう適用しても出てくるのは `False` であって、`p` の証明を**作る**
手段がない。この向きに必要なのが背理法（`Classical.byContradiction`）で、
`Top.lean` 1節の `compl_compl` がそれを使う。代償（公理への依存）は
本文末尾の公理の節のとおり。
-/

/-! SOL 4.3 -/

example : ¬False := fun h => h

/-!
`¬False` は `False → False`——恒等関数が証明になる。
-/

/-! SOL 5.1 -/

theorem all_and {α : Type} {Q R : α → Prop} :
    (∀ a, Q a) → (∀ a, R a) → ∀ a, Q a ∧ R a :=
  fun hq hr a => ⟨hq a, hr a⟩

/-!
点 `a` を任意に取り、2つの一般論をその点で使って組にする。
-/

/-! SOL 5.2 -/

example : IsZero (0 * 5) := rfl

example : IsZero (5 * 0) := rfl

example : IsZero (5 * 0) := all_mul_zero 5

/-!
どれも通る。`0 * 5` も `5 * 0` も計算で `0` になるので `rfl` でよく、
後者は一般論 `all_mul_zero` に点 `5` を代入しても証明できる。
-/

/-! SOL 5.3 -/

#check applyForall all_mul_zero 7

/-!
    applyForall all_mul_zero 7 : IsZero (7 * 0)

`∀ n, IsZero (n * 0)` に点 `7` を代入した、特殊化された命題の証明になる。
-/

/-! SOL 6.1 -/

theorem exists_map {α : Type} {Q R : α → Prop} :
    (∀ a, Q a → R a) → (∃ a, Q a) → ∃ a, R a :=
  fun f h =>
    match h with
    | ⟨a, ha⟩ => ⟨a, f a ha⟩

/-!
`∃` を分解して証人 `a` と根拠 `ha` を取り出し、証人はそのまま、
根拠だけ `f a` で差し替えて組み直す。
-/

/-! SOL 6.2 -/

#check (last 4).val

/-!
    ↑(last 4) : Nat

`.val` の適用が強制の印 `↑` で表示される。型は `Fin 5` の中身の `Nat`。
-/

/-! SOL 6.3 -/

example : ∃ n : Nat, IsZero n := ⟨0, rfl⟩

/-!
証人 `0` と、`IsZero 0` すなわち `0 = 0` の証明 `rfl` の組である。
-/

/-! SOL 7.1 -/

theorem andToOr {p q : Prop} : p ∧ q → p ∨ q := fun h => .inl h.1

/-!
`∧` の除去（`.1`）で `p` の証明を取り出し、`∨` の導入（`.inl`）で包む。
（`.2` と `.inr` の組み合わせでもよい。）
-/

/-! SOL 8.1 -/

example : 1 ≤ 3 := Nat.le.step (Nat.le.step Nat.le.refl)

/-!
`Nat.le.refl : 1 ≤ 1` から `step` を2回。`1 ≤ 2`、`1 ≤ 3` と1段ずつのぼる。
-/

/-! SOL 8.2 -/

theorem MyEq.trans {α : Type} {a b c : α} (h₁ : MyEq a b) (h₂ : MyEq b c) :
    MyEq a c :=
  match h₂ with
  | .refl => h₁

/-!
`h₂` を場合分けすると構成子は `refl` しかなく、その枝では `c` は `b` と
同じものになる。するとゴールは `MyEq a b` に変わり、`h₁` がそのまま合う。
-/

/-! SOL 8.3 -/

theorem MyEq.ofEq {α : Type} {a b : α} (h : a = b) : MyEq a b :=
  match h with
  | rfl => MyEq.refl

/-!
今度は `Eq` の側で場合分けする。構成子は `rfl` しかなく、その枝では
`b` は `a` と同じものになるので、`MyEq a a` の構成子 `refl` を置けばよい。
-/

/-! SOL 9.1 -/

theorem isEven_two_mul : ∀ n : Nat, IsEven (2 * n) :=
  fun n => ⟨n, rfl⟩

/-!
証人は `n`。示すべき根拠は `2 * n = 2 * n` そのものなので、`rfl` で済む
（`isEven_double` では `n + n = 2 * n` の変形が要ったが、ここでは
両辺が字面から一致している）。
-/

/-! SOL 9.2 -/

/-!
**ふつうの証明**: `n` が偶数なら `n = 2k` と書ける。すると
`n + 2 = 2k + 2 = 2(k + 1)` だから、`n + 2` も偶数である。∎

**詳細版**:

1. 仮定 `IsEven n` すなわち `∃ k, n = 2 * k` を分解し、
   `k` と根拠 `hk : n = 2 * k` を得る（∃ の除去）。
2. 証人として `k + 1` を立てる（∃ の導入）。
3. 根拠として `n + 2 = 2 * (k + 1)` を示す。`hk` で `n` を `2 * k` に
   書き換えると、示すべきは `2 * k + 2 = 2 * (k + 1)`——これは
   `Nat.mul_succ 2 k : 2 * (k + 1) = 2 * k + 2` の対称形である。

**項**:
-/

theorem isEven_add_two : ∀ n : Nat, IsEven n → IsEven (n + 2) :=
  fun _ h =>
    match h with
    | ⟨k, hk⟩ => ⟨k + 1, hk ▸ (Nat.mul_succ 2 k).symm⟩

/-!
`hk ▸ e` は等式 `hk` による型の書き換え（本文 9節と同じ道具）。
-/

/-! SOL 9.3 -/

example : IsEven 10 := ⟨5, rfl⟩

/-!
証人 `5`、根拠は `10 = 2 * 5`——計算で一致するので `rfl`。
-/

/-! SOL 10.1 -/

#check @Nat.add_sub_cancel

/-!
    Nat.add_sub_cancel : ∀ (n m : Nat), n + m - m = n

丸括弧＝明示引数なので、使うときは `n` と `m` を実際に渡す:
-/

example : ∀ n : Nat, n + 1 - 1 = n := fun n => Nat.add_sub_cancel n 1

/-!
`m := 1` とした `n + 1 - 1 = n` がちょうどゴールの形で、今度は穴が残らない。
-/

/-! SOL 10.2 -/

#eval (3 : Nat) - 5

/-!
    0

自然数の引き算は `0` で切り捨てられる。
-/

/-! SOL 11.1 -/

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

/-! SOL 12.1 -/

theorem swapOrTac {p q : Prop} : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

#print swapOrTac

/-!
    theorem swapOrTac : ∀ {p q : Prop}, p ∨ q → q ∨ p :=
    fun {p q} h ↦ Or.casesOn (motive := fun t ↦ h = t → q ∨ p) h (fun hp h ↦ Or.inr hp) (fun hq h ↦ Or.inl hq) (Eq.refl h)

本文の `swapOr`（`match` で書いた項）と字面は一致しない——`cases` は
`Or.casesOn` を直接置くからである。それでも型は同じ `p ∨ q → q ∨ p` であり、
検査されるのはその型だけである。
-/

/-! SOL 12.2 -/

theorem idTac {p : Prop} : p → p := by
  intro h
  exact h

#print idTac

/-!
    theorem idTac : ∀ {p : Prop}, p → p :=
    fun {p} h ↦ h

こちらは手書きの `fun h => h` と同じ字面に戻る。
-/
