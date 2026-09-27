import «04_Exists»

/-!
`04_Exists.lean` の練習の解答。本文の順に、型と項を確かめる。
-/

/-! SOL CH.products:1 -/

theorem and_left {p q : Prop} : p ∧ q → p := fun h => h.left

def fst' {α β : Type} : α × β → α := fun x => x.fst

/-!
`∧` の証明の組から第1成分を取り出すのと、直積の組から第1成分を
取り出すのは、どちらも成分名による取り出しである。
-/

/-! SOL CH.products:2 -/

theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩

/-!
左の入れ子から `.left.left`・`.left.right`・`.right` で3つの証明を取り出し、
右の入れ子の形に `⟨…⟩` で組み直す。
-/

/-! SOL CH.products:3 -/

example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩

/-!
具体的な命題でも、`∧` の示し方は「証明を2つ組にする」だけである。
-/

/-! SOL CH.products:4 -/

theorem all_and {α : Type} {Q R : α → Prop} :
    (∀ a, Q a) → (∀ a, R a) → ∀ a, Q a ∧ R a :=
  fun hq hr a => ⟨hq a, hr a⟩

/-!
点 `a` を任意に取り、2つの一般論をその点で使って組にする。
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
[`06_Topology.lean` 2節](#sec-Top.sets)の `compl_compl` がそれを使う。代償（公理への依存）は
本文末尾の公理の節のとおり。
-/

/-! SOL CH.empty-types:3 -/

example : ¬False := fun h => h

/-!
`¬False` は `False → False`——恒等関数が証明になる。
-/

/-! SOL CH2.even-add:1 -/

theorem isEven_two_mul : ∀ n : Nat, IsEven (2 * n) :=
  fun n => ⟨n, rfl⟩

/-!
証人は `n`。示すべき根拠は `2 * n = 2 * n` そのものなので、`rfl` で済む
（`isEven_double` では `n + n = 2 * n` の変形が要ったが、ここでは
両辺が字面から一致している）。
-/

/-! SOL CH2.even-add:2 -/

/-!
**ふつうの証明**:

1. 仮定 `IsEven n` を分解し、`k` と `hk : n = 2 * k` を得る。
2. `hk` の両辺に右から 2 を足して、`n + 2 = 2 * k + 2`。
3. `2 * k + 2 = 2 * (k + 1)` は、既知の定理
   `Nat.mul_succ 2 k : 2 * (k + 1) = 2 * k + 2` の対称形。
4. 2〜3 をつないで `n + 2 = 2 * (k + 1)`。よって証人 `k + 1` で偶数である。∎

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
本文の偶数の和と同じ部品（`match` の分解・`congrArg`・`.trans`・証人の組）だけで
書けている。
-/

/-! SOL CH2.even-add:3 -/

example : IsEven 10 := ⟨5, rfl⟩

/-!
証人 `5`、根拠は `10 = 2 * 5`——計算で一致するので `rfl`。
-/

/-! SOL CH.products:5 -/

theorem exists_left {α : Type} {Q R : α → Prop} :
    (∃ a, Q a ∧ R a) → ∃ a, Q a :=
  fun h =>
    match h with
    | ⟨a, hqr⟩ => ⟨a, hqr.left⟩

/-!
`∃` を分解して証人 `a` と根拠 `Q a ∧ R a` を取り出す。証人はそのまま、
根拠の左側 `hq : Q a` だけを包み直す。
-/

/-! SOL CH.dependent-sums:1 -/

example : ∃ n : Nat, IsZero n := ⟨0, rfl⟩

/-!
証人 `0` と、`IsZero 0` すなわち `0 = 0` の証明 `rfl` の組である。
-/

/-! SOL CH.nat-proofs:1 -/

example : IsZero (0 * 5) := rfl

example : IsZero (5 * 0) := rfl

example : IsZero (5 * 0) := all_mul_zero 5

/-!
どれも通る。`0 * 5` も `5 * 0` も計算で `0` になるので `rfl` でよく、
後者は一般論 `all_mul_zero` に点 `5` を代入しても証明できる。
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

/-! SOL CH.introduction-elimination:1 -/

theorem andToOr {p q : Prop} : p ∧ q → p ∨ q := fun h => .inl h.left

/-!
`∧` から `.left` で `p` の証明を取り出し、`∨` を示す形 `.inl` で包む。
（`.right` と `.inr` の組み合わせでもよい。）
-/

/-! SOL CH2.checking-details:1 -/

#check @Nat.add_sub_cancel

/-!
    Nat.add_sub_cancel : ∀ (n m : Nat), n + m - m = n

丸括弧＝明示引数なので、使うときは `n` と `m` を実際に渡す:
-/

example : ∀ n : Nat, n + 1 - 1 = n := fun n => Nat.add_sub_cancel n 1

/-!
`m := 1` とした `n + 1 - 1 = n` がちょうどゴールの形で、今度は穴が残らない。
-/

/-! SOL CH2.checking-details:2 -/

#eval (3 : Nat) - 5

/-!
    0

自然数の引き算は `0` で切り捨てられる。
-/

/-! SOL CH.prop-elimination:1 -/

/-!
受理されない。`Exists` の証明を `match` で使っているが、行き先 `α : Type` は命題ではない。
報告の要点は `can only eliminate into Prop` である。
本文の `existsElim` は行き先が命題 `r` なので受理される。
-/

/-! SOL CH.dependent-sums:2 -/

theorem triple_multiple : ∀ n : Nat, ∃ k, n + n + n = 3 * k :=
  fun n => ⟨n, Eq.symm (Eq.trans (Nat.succ_mul 2 n)
    (congrArg (fun x => x + n) (Nat.two_mul n)))⟩

/-!
証人は `n`。`3 * n = 2 * n + n` の右辺を書き換えて `n + n + n` にし、
最後に等式を逆向きにする。
-/
