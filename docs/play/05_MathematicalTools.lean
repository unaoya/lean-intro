-- はじめての Lean — 05_MathematicalTools（ブラウザ版・自動生成）
-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、
-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。

-- # 数学を記述する道具

-- ## 1. structure — フィールドを持つ型

inductive MyPoint : Type where
  | mk (x y : Nat) : MyPoint

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | MyPoint.mk a _ => a

structure Point : Type where
  x : Nat
  y : Nat

-- ### 構成子で作り、フィールドを取り出す

#check Point.mk
#check Point.x

#eval Point.x (Point.mk 1 2)

-- ### ドット記法で関数を適用する

#eval (Point.mk 1 2).x

-- ### 匿名構成子 — 期待される型から構成子を決める

def pointFromPair : Point := ⟨1, 2⟩
def pointFromDot : Point := .mk 1 2

#check (⟨1, 2⟩ : Point)

-- ### フィールド名を付けて書く

def point_pair_eq_mk : (⟨1, 2⟩ : Point) = Point.mk 1 2 := rfl
def point_fields_eq_mk : ({ x := 1, y := 2 } : Point) = Point.mk 1 2 := rfl

def exists_two : ∃ n : Nat, n = 2 := ⟨2, rfl⟩

-- ### 自分で定義した関数もドットで使える

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

#eval (Point.mk 1 2).swap.x

/- ✏ 練習
56. 型 `A` と二つの写像 `f g : A → Nat` から、各 `a` を組 `(f a, g a)` に送る
   `pairAt (A : Type) (f g : A → Nat) : A → Point` を定義せよ。
   `A = Nat`、`f n = n + 1`、`g n = 2 * n` とし、`3` を渡した結果の
   `x`・`y` を `#eval` で確かめよ。これは直積へ向かう写像を、成分の写像から作る操作である。
-/

-- ### 型をパラメータにする structure

structure Pair (α β : Type) : Type where
  fst : α
  snd : β

#check Pair.mk
#check Pair.fst

-- ### 二つの異なる型の項をまとめる

def natBoolPair : Pair Nat Bool := Pair.mk 3 true

#eval natBoolPair.fst
#eval natBoolPair.snd

/- ✏ 練習
57. `center : Point`、`radius : Nat` を持つ構造体 `Circle` を定義せよ。
   `makeCircle : Point → Nat → Circle` を構成子名と `⟨…⟩` の両方で書き、
   点 `(1,2)`、半径 `3` の円の `center.x` と `radius` を `#eval` で確かめよ。
-/

-- ## 2. 依存するフィールド

structure PointedType : Type 1 where
  carrier : Type
  point : carrier

#check PointedType.mk

-- ### 点付き集合を作る

def pointedNat : PointedType := ⟨Nat, 0⟩
def pointedBool : PointedType := ⟨Bool, true⟩

#check PointedType.mk Nat

-- ### 取り出す項の型も入力に依存する

#check PointedType.carrier
#check PointedType.point

#reduce pointedNat.point
#reduce pointedBool.point

/- ✏ 練習
58. 点付き集合 (A,a) と写像 f:A→ A から (A,f(a)) を作る
   `mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType` を書け。
   `#reduce (mapPointed pointedNat Nat.succ).point` の結果を予想して確かめよ。
-/

-- ## 3. 部分型 — 値と証明の組

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- structure Subtype {α : Type} (p : α → Prop) where
--   val : α
--   property : p val

def IsEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

def EvenNat : Type := {n : Nat // IsEven n}

def evenFour : EvenNat := Subtype.mk 4 (Exists.intro 2 rfl)

#check evenFour.val
#check evenFour.property

-- ### 値と、値についての保証を取り出す

#eval evenFour.val

def evenFourPlusFour : IsEven (evenFour.val + evenFour.val) :=
  Exists.intro 4 rfl

-- ### 存在の証明との違い

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- structure Fin (n : Nat) where
--   val : Nat
--   isLt : val < n

#check Nat.lt_succ_self

def lastFromProof : (n : Nat) → Fin (n + 1) :=
  fun n => Fin.mk n (Nat.lt_succ_self n)

#check lastFromProof 2
#eval (lastFromProof 2).val

-- ### 第1章の依存関数を、構成子まで読む

def lastFromProof_val (n : Nat) : (lastFromProof n).val = n := rfl
def lastFromProof_eq_last (n : Nat) : lastFromProof n = Fin.last n := rfl

-- ### 補足: Fin の数値リテラル

#eval (5 : Fin 3)

-- （補足・先取りここまで）

/- ✏ 練習
59. 二つの偶数の和を、偶数という条件を持つ値として返す
   `addEven (n m : EvenNat) : EvenNat` を書け。
   ヒント：値は `n.val + m.val` とする。`n.property` と `m.property` を `match` で分解し、
   得られた証人の和を新しい証人にする。第4章の偶数の和と同じ等式の計算を組み立てよ。
   `#eval (addEven evenFour evenFour).val` を確かめよ。
-/

-- ## 4. class と instance

class Pointed (α : Type) : Type where
  point : α

#check Pointed

instance : Pointed Nat where
  point := 0

#check @inferInstance

#check (inferInstance : Pointed Nat)

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- #check (inferInstance : Pointed Bool)

def pointPair (α : Type) [Pointed α] : Pair α α := ⟨Pointed.point, Pointed.point⟩

#check pointPair

#eval (pointPair Nat).fst

-- ### 自作型にもインスタンスを与える

instance : Pointed Point where
  point := ⟨0, 0⟩

#check pointPair Point

#eval (pointPair Point).fst.x

-- ### インスタンスを受け取る定理

def pointPair_fst (α : Type) [Pointed α] :
    (pointPair α).fst = Pointed.point := rfl

#check pointPair_fst

def pointPair_nat_fst : (pointPair Nat).fst = Pointed.point := pointPair_fst Nat
def pointPair_point_fst : (pointPair Point).fst = Pointed.point := pointPair_fst Point

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

-- ### 補足: 命題の `#eval` と `def` の展開

#eval 2 < 3

def z : Prop := 2 < 3

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- #eval z

def zFromLt (h : 2 < 3) : z := h

instance : Decidable z := inferInstanceAs (Decidable (2 < 3))

#eval z

-- （補足・先取りここまで）

-- ## 5. 記法の自作 — syntax と macro_rules

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

#check ⟪1, true⟫

/- ✏ 練習
60. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。
-/

-- ## 6. 集合 — `Set` を自作する

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

def one_mem_singleton : (1 : Nat) ∈ ({n | n = 1} : Set Nat) := rfl

instance {X : Type} : HasSubset (Set X) := ⟨fun s t => ∀ a, a ∈ s → a ∈ t⟩

#check ({n | n = 1} : Set Nat) ⊆ {n | n = 2}

def Set.subset_refl {X : Type} (s : Set X) : s ⊆ s := fun _ ha => ha

#check Set.subset_refl

/- ✏ 練習
61. 推移律を項で書け（各点で2つの仮定を順に適用する）:

       def Set.subset_trans {X : Type} {s t u : Set X}
           (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u
-/

-- ## 7. namespace — 名前の接頭辞

namespace Geometry

def origin : Point := ⟨0, 0⟩

#check origin

end Geometry

#check Geometry.origin

-- ### 補足: 短い名前と、型から補う名前

#check (.mk 1 2 : Point)
#check (.true : Bool)

-- （補足・先取りここまで）

/- 8. ✏ 練習 — 章末問題
62. 本文で `Pointed Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : Pointed Bool where point := false` を登録し、
   `#check (inferInstance : Pointed Bool)` と
   `def pointPair_bool_fst : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool` が
   通るようになることを確かめよ（登録した瞬間から、一般的な定理も適用できる）。

63. `Pointed` と同じ手順でマグマを自作する:
   `class Magma (α : Type) : Type where op : α → α → α` を宣言し、
   `instance : Magma Nat where op := Nat.add` を登録して、
   `#check (inferInstance : Magma Nat)` が通ることを確かめよ。

64. `pointPair` にならって、汎用関数
   `opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a` を書き、
   `#eval opSelf Nat 3` の値を予想してから確かめよ。

65. 本文の「積に構造を誘導する」にならって、成分ごとに演算する
   `instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β)` を登録し、
   `#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd` の値を
   予想してから確かめよ（探索の連鎖まで含めて、`Pointed` と同じに動く）。

66. `Add` にならって `instance : Mul Point where mul p q := ⟨p.x * q.x, p.y * q.y⟩`
   を登録し、`#eval (Point.mk 2 3 * Point.mk 4 5).x` の値を予想してから確かめよ。

67. `infixl:65 " ⊞ " => Nat.add` で、自然数の足し算に
   中置記法を与え、`#reduce 1 ⊞ 1` の表示を
   予想してから確かめよ。

68. `def evens : Set Nat := {n | IsEven n}` と宣言せよ（`IsEven` は `04_Exists.lean` 1節の述語）。`def four_mem_evens : (4 : Nat) ∈ evens := ⟨2, rfl⟩` が通ることを確かめよ。

69. 全体集合 `def allNat : Set Nat := {_n | True}` を定義し、
   `def subset_allNat : ∀ s : Set Nat, s ⊆ allNat` を書け
   （各点の証明は `True.intro`。束縛子 `_n` の `_` は「使わない」印である）。

70. `def odds : Set Nat := {n | ¬IsEven n}` を宣言し、
   `#check (3 : Nat) ∈ odds` の表示を予想してから確かめよ。

71. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
-/
