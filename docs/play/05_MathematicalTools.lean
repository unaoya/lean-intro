-- はじめての Lean — 05_MathematicalTools（ブラウザ版・自動生成）
-- 先頭には、この章が使う前の章（01_TypesAndTerms・03_InductiveTypes・02_Forall・04_Exists）のコードをまとめてあります。
-- 本章は「ここから本章」の行から始まります（368 行目。Ctrl+G で行番号へ移動できます）。
-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、
-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。

-- ════════ 前の章のコード（読まなくてよい） ════════
-- ─── 01_TypesAndTerms ───
section

def x : Nat := 2

def y : Nat := x

def double : Nat → Nat := fun n => n + n

def double' (n : Nat) : Nat := n + n

def plus : Nat → Nat → Nat := fun a => fun b => a + b

def addMul (a b c : Nat) : Nat := a + b * c

def applyTo21 (F : Nat → Nat) : Nat := F 21

def applyAt (F : Nat → Nat) (n : Nat) : Nat := F n

def Map : Type → Type → Type := fun A B => A → B

def idAt (α : Type) (a : α) : α := a

def Tuple : Nat → Type := fun n => Fin n → Nat

def constTuple : (n : Nat) → Tuple n :=
  fun n => fun (_i : Fin n) => 7

def zeroIndex : (n : Nat) → Fin (n + 1) := fun _ => 0

def idImplicit {α : Type} (a : α) : α := a

def zeros : (n : Nat) → Vector Nat n := fun n => Vector.replicate n 0

end

-- ─── 03_InductiveTypes ───
section

inductive Signal : Type where
  | red : Signal
  | yellow : Signal
  | green : Signal

def Signal.next : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

def nextShort : Signal → Signal := fun s =>
  match s with
  | .red => .green
  | .green => .yellow
  | .yellow => .red

def isRed : Signal → Bool := fun s =>
  match s with
  | .red => true
  | .yellow => false
  | .green => false

inductive NatOrBool : Type where
  | nat (n : Nat) : NatOrBool
  | bool (b : Bool) : NatOrBool

def valueOf : NatOrBool → Nat := fun x =>
  match x with
  | .nat n => n
  | .bool _ => 0

inductive MySum (α β : Type) : Type where
  | inl (a : α) : MySum α β
  | inr (b : β) : MySum α β

def fromSum : MySum Nat Bool → Nat := fun x =>
  match x with
  | .inl n => n
  | .inr _ => 0

def getLeft {α β : Type} (d : α) : MySum α β → α := fun x =>
  match x with
  | .inl a => a
  | .inr _ => d

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def add : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | .zero   => m
  | .succ k => .succ (add m k)

inductive MyPoint : Type where
  | mk (x y : Nat) : MyPoint

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | .mk a _ => a

structure Point : Type where
  x : Nat
  y : Nat

def pointFromDot : Point := .mk 1 2

def pointFromPair : Point := ⟨1, 2⟩

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

structure Pair (α β : Type) : Type where
  fst : α
  snd : β

structure PointedType : Type 1 where
  carrier : Type
  point : carrier

def pointedNat : PointedType := ⟨Nat, 0⟩

inductive MyPointedType : Type 1 where
  | mk (carrier : Type) (point : carrier) : MyPointedType

def last : (n : Nat) → Fin (n + 1) := fun n => ⟨n, Nat.lt_succ_self n⟩

def first : (n : Nat) → Fin (n + 1) := fun _ => 0

end

-- ─── 02_Forall ───
section

theorem modus_ponens
    (P Q : Prop)
    (hP : P)
    (hPQ : P → Q) :
    Q :=
  hPQ hP

theorem imp_trans
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R :=
  fun hP =>
    hQR (hPQ hP)

theorem one_add_one : 1 + 1 = 2 := rfl

def constFun {α β : Type} (b : β) : α → β := fun _ => b

theorem constImp {p q : Prop} (hq : q) : p → q := fun _ => hq

def applyFun {α β : Type} (f : α → β) (a : α) : β := f a

theorem applyImp {p q : Prop} (h : p → q) (hp : p) : q := h hp

example {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : ∀ u v, g u = g v → u = v) (hf : ∀ u v, f u = f v → u = v) :
    ∀ x y, g (f x) = g (f y) → x = y :=
  fun x y h => hf x y (hg (f x) (f y) h)

theorem comp_injective {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Function.Injective g) (hf : Function.Injective f) :
    Function.Injective (fun x => g (f x)) :=
  fun x y h => hf (hg h : f x = f y)

theorem all_refl : ∀ n : Nat, n = n :=
  fun n => (rfl : n = n)

def mkPi {α : Type} {P : α → Type} (f : (a : α) → P a) : (a : α) → P a := fun a => f a

theorem mkForall {α : Type} {Q : α → Prop} (h : ∀ a, Q a) : ∀ a, Q a := fun a => h a

def applyPi {α : Type} {P : α → Type} (f : (a : α) → P a) (a : α) : P a := f a

theorem applyForall {α : Type} {Q : α → Prop} (h : ∀ a, Q a) (a : α) : Q a := h a

def IsZero : Nat → Prop := fun n => n = 0

theorem all_mul_zero : ∀ n : Nat, IsZero (n * 0) := fun _ => rfl

end

-- ─── 04_Exists ───
section

theorem exists_eq_two : ∃ n : Nat, n = 2 :=
  ⟨2, rfl⟩

theorem even_double : ∀ n : Nat, ∃ k, n + n = 2 * k :=
  fun n => ⟨n, Eq.symm (Nat.two_mul n)⟩

def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

theorem isEven_double : ∀ n : Nat, IsEven (n + n) :=
  fun n => ⟨n, Eq.symm (Nat.two_mul n)⟩

theorem exists_map {α : Type} {Q R : α → Prop} :
    (∀ a, Q a → R a) → (∃ a, Q a) → ∃ a, R a :=
  fun hqr h =>
    match h with
    | ⟨a, ha⟩ => ⟨a, hqr a ha⟩

example {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : ∀ c, ∃ b, g b = c) (hf : ∀ b, ∃ a, f a = b) :
    ∀ c, ∃ a, g (f a) = c :=
  fun c =>
    match hg c with
    | ⟨b, hb⟩ =>
      match hf b with
      | ⟨a, ha⟩ => ⟨a, Eq.trans (congrArg g ha) hb⟩

theorem comp_surjective {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Surjective (fun x => g (f x)) :=
  fun c =>
    match hg c with
    | ⟨b, hb⟩ =>
      match hf b with
      | ⟨a, ha⟩ => ⟨a, Eq.trans (congrArg g ha) hb⟩

def mkSigma {α : Type} {P : α → Type} (a : α) (b : P a) : (a : α) × P a := ⟨a, b⟩

theorem mkExists {α : Type} {Q : α → Prop} (a : α) (h : Q a) : ∃ a, Q a := ⟨a, h⟩

def currySigma {α γ : Type} {P : α → Type} : (((a : α) × P a) → γ) → ((a : α) → P a → γ) :=
  fun f a b => f ⟨a, b⟩

theorem curryExists {α : Type} {r : Prop} {Q : α → Prop} : ((∃ a, Q a) → r) → (∀ a, Q a → r) :=
  fun f a b => f ⟨a, b⟩

def mkProd {α β : Type} (a : α) (b : β) : α × β := ⟨a, b⟩

theorem mkAnd {p q : Prop} (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

def swapProd {α β : Type} : α × β → β × α := fun x => ⟨x.snd, x.fst⟩

theorem swapAnd {p q : Prop} : p ∧ q → q ∧ p := fun h => ⟨h.right, h.left⟩

def inlSum {α β : Type} (a : α) : α ⊕ β := .inl a

theorem inlOr {p q : Prop} (hp : p) : p ∨ q := .inl hp

def swapSum {α β : Type} : α ⊕ β → β ⊕ α := fun x =>
  match x with
  | .inl a => .inr a
  | .inr b => .inl b

theorem swapOr {p q : Prop} : p ∨ q → q ∨ p := fun h =>
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

def elimSum {α β γ : Type} : α ⊕ β → (α → γ) → (β → γ) → γ := fun x f g =>
  match x with
  | .inl a => f a
  | .inr b => g b

theorem elimOr {p q r : Prop} : p ∨ q → (p → r) → (q → r) → r := fun h f g =>
  match h with
  | .inl hp => f hp
  | .inr hq => g hq

def elimEmpty {α : Type} : Empty → α := fun e => e.elim

theorem elimFalse {p : Prop} : False → p := fun h => h.elim

theorem notIntro {p : Prop} (h : p → False) : ¬p := h

theorem isEven_add {n m : Nat} (hn : IsEven n)
    (hm : IsEven m) : IsEven (n + m) :=
  match hn with
  | ⟨k, hk⟩ =>
    match hm with
    | ⟨l, hl⟩ =>
      let h1 : n + m = 2 * k + m :=
        congrArg (fun x => x + m) hk
      let h2 : 2 * k + m = 2 * k + 2 * l :=
        congrArg (fun x => 2 * k + x) hl
      let h3 : 2 * k + 2 * l = 2 * (k + l) :=
        Eq.symm (Nat.mul_add 2 k l)
      ⟨k + l, Eq.trans (Eq.trans h1 h2) h3⟩

theorem succ_add' : ∀ (n m : Nat), (n + 1) + m = (n + m) + 1 := fun n m =>
  match m with
  | 0     => rfl
  | j + 1 => congrArg (· + 1) (succ_add' n j)

theorem two_mul_from_scratch : ∀ n : Nat, 2 * n = n + n := fun n =>
  match n with
  | 0     => rfl
  | k + 1 =>
    (congrArg (· + 2) (two_mul_from_scratch k)).trans
      ((congrArg (· + 1) (succ_add' k k)).symm :
        (k + k) + 2 = (k + 1) + (k + 1))

example (n : Nat) : n + 0 = n := rfl

example (n : Nat) : 0 + n = n := Nat.zero_add n

example : 0 = 0 := Eq.refl 0
example : 0 = 0 := rfl

example : 0 ≤ 0 := Nat.le.refl
example : 0 ≤ 1 := Nat.le.step Nat.le.refl
example : 0 ≤ 2 := Nat.le.step (Nat.le.step Nat.le.refl)

example (n : Nat) : n + 0 = n := rfl

example (n : Nat) : 0 + n = n := Nat.zero_add n

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl

example : true ≠ false := fun h => Bool.noConfusion h

example {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.noConfusion h (fun h' => h')

inductive MyEq {α : Type} (a : α) : α → Prop where
  | refl : MyEq a a

theorem MyEq.symm {α : Type} {a b : α} (h : MyEq a b) : MyEq b a :=
  match h with
  | .refl => .refl

theorem MyEq.symm' {α : Type} {a b : α} (h : MyEq a b) : MyEq b a :=
  MyEq.rec (motive := fun c _ => MyEq c a) MyEq.refl h

example : MyEq (1 + 1) 2 := .refl

theorem myEq_iff_eq {α : Type} {a b : α} : MyEq a b ↔ a = b :=
  ⟨fun h => match h with | .refl => rfl,
   fun h => match h with | rfl => .refl⟩

example {α : Type} {a b : α} : MyEq a b = (a = b) := propext myEq_iff_eq

example {α β : Type} : α × β → β × α := fun x =>
  match x with
  | ⟨a, b⟩ => ⟨b, a⟩

example {p q : Prop} : p ∧ q → q ∧ p := fun x =>
  match x with
  | ⟨a, b⟩ => ⟨b, a⟩

def sigmaFst {α : Type} {P : α → Type} (s : (a : α) × P a) : α := s.fst

def sigmaSnd {α : Type} {P : α → Type} (s : (a : α) × P a) : P s.fst := s.snd

theorem existsElim {α : Type} {r : Prop} {Q : α → Prop}
    (h : ∃ a, Q a) (hr : ∀ a, Q a → r) : r :=
  match h with
  | ⟨a, ha⟩ => hr a ha

theorem orElimToProp {p q r : Prop} (h : p ∨ q) (f : p → r) (g : q → r) : r :=
  h.elim f g

end

-- ════════ ここから本章：05_MathematicalTools ════════
-- # 数学を記述する道具

-- ## 1. class と instance

class Pointed (α : Type) : Type where
  point : α

#check Pointed

instance : Pointed Nat where
  point := 0

#check @inferInstance

example : Pointed Nat := inferInstance

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- example : Pointed Bool := inferInstance

def pointPair (α : Type) [Pointed α] : Pair α α := ⟨Pointed.point, Pointed.point⟩

#check pointPair

#eval (pointPair Nat).fst

-- ### 自作型にもインスタンスを与える

instance : Pointed Point where
  point := ⟨0, 0⟩

#check pointPair Point

#eval (pointPair Point).fst.x

-- ### インスタンスを受け取る定理

theorem pointPair_fst (α : Type) [Pointed α] : (pointPair α).fst = Pointed.point := rfl

#check pointPair_fst

-- 登録済みの型なら、どれにでも同じ定理が適用できる
example : (pointPair Nat).fst = Pointed.point := pointPair_fst Nat
example : (pointPair Point).fst = Pointed.point := pointPair_fst Point

-- ### 積に構造を誘導する

instance {α β : Type} [Pointed α] [Pointed β] : Pointed (Pair α β) where
  point := ⟨Pointed.point, Pointed.point⟩

#eval (Pointed.point : Pair Nat Point).snd.x

-- ### 記法もクラスで動いている

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- class Add (α : Type u) where
--   add : α → α → α

instance : Add Point where
  add p q := ⟨p.x + q.x, p.y + q.y⟩

#check Point.mk 1 2 + Point.mk 3 4

#eval (Point.mk 1 2 + Point.mk 3 4).x

/- ✏ 練習
本文で `Pointed` に対して行った操作を、**二項演算付きの型**（マグマと
呼ばれる）で一通り繰り返す。

120. 本文で `Pointed Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : Pointed Bool where point := false` を登録し、
   `example : Pointed Bool := inferInstance` と
   `example : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool` が
   通るようになることを確かめよ（登録した瞬間から、一般的な定理も適用できる）。
121. `Pointed` と同じ手順でマグマを自作する:
   `class Magma (α : Type) : Type where op : α → α → α` を宣言し、
   `instance : Magma Nat where op := Nat.add` を登録して、
   `example : Magma Nat := inferInstance` が通ることを確かめよ。
122. `pointPair` にならって、汎用関数
   `opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a` を書き、
   `#eval opSelf Nat 3` の値を予想してから確かめよ。
123. 本文の「積に構造を誘導する」にならって、成分ごとに演算する
   `instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β)` を登録し、
   `#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd` の値を
   予想してから確かめよ（探索の連鎖まで含めて、`Pointed` と同じに動く）。
124. `Add` にならって `instance : Mul Point where mul p q := ⟨p.x * q.x, p.y * q.y⟩`
   を登録し、`#eval (Point.mk 2 3 * Point.mk 4 5).x` の値を予想してから確かめよ。
-/

-- ## 2. 記法の自作 — syntax と macro_rules

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

#check ⟪1, true⟫

/- ✏ 練習
125. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。
126. `infixl:65 " ⊞ " => add` で、`03_InductiveTypes.lean` の `add`（`MyNat` の足し算）に
   中置記法を与え、`#reduce MyNat.zero.succ ⊞ MyNat.zero.succ` の表示を
   予想してから確かめよ。
-/

-- ## 3. 集合 — `Set` を自作する

def Set (X : Type) : Type := X → Prop

#check Set

def setOf {X : Type} (p : X → Prop) : Set X := p

#check setOf

syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x => $p)

#check Membership

instance {X : Type} : Membership X (Set X) := ⟨fun s a => s a⟩

#check (1 : Nat) ∈ ({n | n = 1} : Set Nat)

example : (1 : Nat) ∈ ({n | n = 1} : Set Nat) := rfl

instance {X : Type} : HasSubset (Set X) := ⟨fun s t => ∀ a, a ∈ s → a ∈ t⟩

#check ({n | n = 1} : Set Nat) ⊆ {n | n = 2}

theorem Set.subset_refl {X : Type} (s : Set X) : s ⊆ s := fun _ ha => ha

#check Set.subset_refl

/- ✏ 練習
127. 推移律を項で書け（各点で2つの仮定を順に適用する）:

       theorem Set.subset_trans {X : Type} {s t u : Set X}
           (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u

128. `def evens : Set Nat := {n | IsEven n}` と宣言せよ（`IsEven` は `04_Exists.lean`
   1節の述語）。`example : (4 : Nat) ∈ evens := ⟨2, rfl⟩` が通ることを確かめよ。
129. 全体集合 `def allNat : Set Nat := {_n | True}` を定義し、
   `theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat` を書け
   （各点の証明は `True.intro`。束縛子 `_n` の `_` は「使わない」印である）。
130. `def odds : Set Nat := {n | ¬IsEven n}` を宣言し、
   `#check (3 : Nat) ∈ odds` の表示を予想してから確かめよ。
-/

-- ## 4. namespace — 名前の接頭辞

namespace Geometry

def origin : Point := ⟨0, 0⟩

#check origin

end Geometry

#check Geometry.origin

/- ✏ 練習
131. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
-/
