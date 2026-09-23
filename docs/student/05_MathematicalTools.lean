-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import «03_InductiveTypes»
import «04_Exists»

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

1. 本文で `Pointed Bool` が未登録のため `inferInstance` が失敗する例を見た。
   `instance : Pointed Bool where point := false` を登録し、
   `example : Pointed Bool := inferInstance` と
   `example : (pointPair Bool).fst = Pointed.point := pointPair_fst Bool` が
   通るようになることを確かめよ（登録した瞬間から、一般的な定理も適用できる）。
2. `Pointed` と同じ手順でマグマを自作する:
   `class Magma (α : Type) : Type where op : α → α → α` を宣言し、
   `instance : Magma Nat where op := Nat.add` を登録して、
   `example : Magma Nat := inferInstance` が通ることを確かめよ。
3. `pointPair` にならって、汎用関数
   `opSelf (α : Type) [Magma α] (a : α) : α := Magma.op a a` を書き、
   `#eval opSelf Nat 3` の値を予想してから確かめよ。
4. 本文の「積に構造を誘導する」にならって、成分ごとに演算する
   `instance {α β : Type} [Magma α] [Magma β] : Magma (Pair α β)` を登録し、
   `#eval (Magma.op (⟨1, 2⟩ : Pair Nat Nat) ⟨10, 20⟩).snd` の値を
   予想してから確かめよ（探索の連鎖まで含めて、`Pointed` と同じに動く）。
5. `Add` にならって `instance : Mul Point where mul p q := ⟨p.x * q.x, p.y * q.y⟩`
   を登録し、`#eval (Point.mk 2 3 * Point.mk 4 5).x` の値を予想してから確かめよ。
-/

-- ## 2. 記法の自作 — syntax と macro_rules

syntax "⟪" term ", " term "⟫" : term

macro_rules
  | `(⟪$x, $y⟫) => `(Pair.mk $x $y)

#check ⟪1, true⟫

/- ✏ 練習
1. `⟪1, true⟫` にならって、`Point` 用の記法（例えば `⟬x, y⟭`）を
   `syntax` と `macro_rules` で自作し、`#check ⟬1, 2⟭` で確かめよ。
2. `infixl:65 " ⊞ " => add` で、`03_InductiveTypes.lean` の `add`（`MyNat` の足し算）に
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
1. 推移律を項で書け（各点で2つの仮定を順に適用する）:

       theorem Set.subset_trans {X : Type} {s t u : Set X}
           (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u

2. `def evens : Set Nat := {n | IsEven n}` と宣言せよ（`IsEven` は `04_Exists.lean`
   4節の述語）。`example : (4 : Nat) ∈ evens := ⟨2, rfl⟩` が通ることを確かめよ。
3. 全体集合 `def allNat : Set Nat := {_n | True}` を定義し、
   `theorem subset_allNat : ∀ s : Set Nat, s ⊆ allNat` を書け
   （各点の証明は `True.intro`。束縛子 `_n` の `_` は「使わない」印である）。
4. `def odds : Set Nat := {n | ¬IsEven n}` を宣言し、
   `#check (3 : Nat) ∈ odds` の表示を予想してから確かめよ。
-/

-- ## 4. namespace — 名前の接頭辞

namespace Geometry

def origin : Point := ⟨0, 0⟩

#check origin

end Geometry

#check Geometry.origin

/- ✏ 練習
1. `namespace Geometry … end Geometry` をもう一度開いて `unitX : Point := ⟨1, 0⟩` を
   追加し、外から `#check Geometry.unitX` では見え、`#check unitX` では
   見えないことを確かめよ。
-/
