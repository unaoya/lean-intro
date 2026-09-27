import «03_InductiveTypes»

/-! SOL Trial3.constructors:1 -/

def signalCode : Signal → Nat := fun s =>
  match s with
  | Signal.red => 0
  | Signal.yellow => 1
  | Signal.green => 2
/-!
各枝で `Nat` の項を返す。黄色の場合の値は `1` である。
-/

/-! SOL Trial3.dependent-pairs:1 -/

def attachLast : Nat → Numbered := fun n =>
  Numbered.mk (n + 1) (lastIndex n)
/-!
大きさは `4`、番号は `Fin 4` の `3` である。
構成子の第一引数に `n + 1` を渡すと、第二引数に必要な型が `Fin (n + 1)` と決まる。
-/

/-! SOL Trial3.indexed:1 -/

def one_le_three : 1 ≤ 3 := Nat.le.step (Nat.le.step Nat.le.refl)

def two_le_four_again : 2 ≤ 4 := succLeSuccByMatch 1 3 one_le_three
/-!
`1 ≤ 1` から二段進む。両辺に一つ加えると、結果の型は `2 ≤ 4` である。
-/

/-! SOL Trial3.practice:1 -/

def prev : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.yellow
  | Signal.yellow => Signal.green
  | Signal.green => Signal.red
/-!
赤を次の色に送ると青、青を逆向きに送ると赤になる。
-/

/-! SOL Trial3.practice:2 -/

def swapSum {A B : Type} : MySum A B → MySum B A := fun s =>
  match s with
  | MySum.inl a => MySum.inr a
  | MySum.inr b => MySum.inl b
/-!
例えば左の枝では `a : A`。行き先 `MySum B A` では `A` が右側なので、`MySum.inr` を使う。
-/

/-! SOL Trial3.practice:3 -/

def pairMaps (X A B : Type) (f : X → A) (g : X → B) : X → MyPair A B :=
  fun x => MyPair.mk (f x) (g x)
/-!
それぞれ `f x : A`、`g x : B` なので、`MyPair.mk` の二つの引数に渡せる。
-/

/-! SOL Trial3.practice:4 -/

def graphOf (A : Type) (B : A → Type) (f : (a : A) → B a) :
    A → FamilyPair A B := fun a => FamilyPair.mk a (f a)
/-!
`a` を渡した後、構成子の第二引数に必要なのは `B a` の項である。
関数適用で得た `f a : B a` が、その型を持っている。
-/

/-! SOL Trial3.practice:5 -/

def toNat : MyNat → Nat := fun n =>
  match n with
  | MyNat.zero => 0
  | MyNat.succ k => toNat k + 1
/-!
小さい項 `k` への関数の値を使って、`succ k` への値を作っている。
-/

/-! SOL Trial3.practice:6 -/

def leAddRight : ∀ n k : Nat, n ≤ n + k := fun n k =>
  match k with
  | Nat.zero => Nat.le.refl
  | Nat.succ j => Nat.le.step (leAddRight n j)
/-!
次の数の枝では `n + Nat.succ j` が `Nat.succ (n + j)` に計算される。
そのため、`n ≤ n + j` の証明に `step` を適用すればよい。
-/

/-! SOL Trial3.practice:7 -/

def zeroLeOfEq (n m : Nat) (h : n = m) (hn : 0 ≤ n) : 0 ≤ m :=
  match h with
  | Eq.refl _ => hn
/-!
`Eq.refl` の枝では結論が `0 ≤ n` に特殊化され、`hn` をそのまま返せる。
-/
