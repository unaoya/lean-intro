-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import Intro1a

-- # 証明を読む I — ならばと全称

-- ## 0. 証明するとは何をすることか

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- theorem 名前 (引数) : 命題 := 証明の項

theorem modus_ponens
    (P Q : Prop)
    (hP : P)
    (hPQ : P → Q) :
    Q :=
  hPQ hP

#check modus_ponens

/- ✏ 練習
1. 次の `#check` の結果を予想してから確かめよ。出力の最後が `Q` になるまでを、
   `P → Q` の入力型と出力型から説明せよ。

       #check fun (P Q : Prop) (hP : P) (hPQ : P → Q) => hPQ hP

2. 引数の順だけを入れ替えた
   `theorem use_imp (P Q : Prop) (hPQ : P → Q) (hP : P) : Q` の右辺を書け。
-/

-- ### 例2: 含意の推移

theorem imp_trans
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R :=
  fun hP =>
    hQR (hPQ hP)

#check imp_trans

/- ✏ 練習
1. `theorem imp_refl (P : Prop) : P → P` を書け。
2. `P → Q`、`Q → R`、`R → S` を順に使う
   `theorem imp_trans3 (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R)
   (hRS : R → S) : P → S` を書け。まず最も内側の適用の型から予想すること。
-/

-- ## 1. 整理 — 命題・theorem・rfl

-- ### theorem と def

theorem one_add_one : 1 + 1 = 2 := rfl

#check one_add_one

/- ✏ 練習
1. `#check 3 < 5` と `#check 3 = 5` の表示を予想してから確かめよ
   （偽の命題も命題である、を思い出すこと）。
2. `theorem two_add_three : 2 + 3 = 5 := rfl` を自分で宣言してみよ。
3. `theorem oops : 2 + 2 = 5 := rfl` は受理されるか。予想してから試し、
   エラーメッセージがどの規則の破れを指しているか読み取れ。
-/

-- ## 2. 整理 — 関数型と「ならば」

def constFun {α β : Type} (b : β) : α → β := fun _ => b

#check constFun

theorem constImp {p q : Prop} (hq : q) : p → q := fun _ => hq

#check constImp

def applyFun {α β : Type} (f : α → β) (a : α) : β := f a

#check applyFun

theorem applyImp {p q : Prop} (h : p → q) (hp : p) : q := h hp

#check applyImp

-- ここまで型側を `def`、命題側を `theorem` で書いたが、どちらの宣言も
-- 「コロンの右に書いたものを持つ項を、`:=` の右に差し出す」という同じ形をしている。
-- `theorem` と `def` は、指定された型の項を与え、型検査を受けるという点で共通している。
-- 以下のすべての対でも、この形は変わらない。

/- ✏ 練習
型側と命題側を**同じ字面**で書けることを、自分の手で確かめる。

1. 「2回適用」を両方の世界で書け:
   `def apply2 {α : Type} : (α → α) → α → α` と
   `theorem applyTwice {p : Prop} : (p → p) → p → p`。
   まず `fun` で引数を受け取る形で書き、次にその引数をコロンの左に移して、
   `apply2Binder`・`applyTwiceBinder` という名前で binder 形式でも書け。
   4つの宣言の型の表示を予想してから `#check` で確かめよ。
   表示を矢印形式に読み替えると、書き換えの前後で同じ型になることを説明せよ。
2. 仮定を受け取る順を入れ替える
   `theorem imp_swap {p q r : Prop} : (p → q → r) → q → p → r` を項で書け。
   `p` と `q` の証明をどの順に受け取っても、適用するときは関数の入力順に戻す。
3. 同じ字面 `fun h => h` が、型側の `example : Nat → Nat` と命題側の
   `example : (1 = 1) → (1 = 1)` の**両方**で通ることを確かめよ。
4. `#check applyFun double 3` の表示を予想してから確かめよ。
-/

-- ## 3. 全称と単射の合成

theorem all_refl : ∀ n : Nat, n = n :=
  fun n => (rfl : n = n)

#check all_refl

-- ### 例3: 単射どうしの合成は単射

example {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : ∀ u v, g u = g v → u = v) (hf : ∀ u v, f u = f v → u = v) :
    ∀ x y, g (f x) = g (f y) → x = y :=
  fun x y h => hf x y (hg (f x) (f y) h)

theorem comp_injective {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Function.Injective g) (hf : Function.Injective f) :
    Function.Injective (fun x => g (f x)) :=
  fun x y h => hf (hg h : f x = f y)

#check comp_injective

/- ✏ 練習
1. 定義を開いた最初の `example` で、`hg (f x) (f y) h` と
   `hf x y (hg (f x) (f y) h)` の型を内側から順に予想せよ。
2. 恒等関数が単射であることを示す
   `theorem id_injective (α : Type) : Function.Injective (fun x : α => x)` を書け。
-/

-- ## 4. 整理 — 依存積と「すべての」

def mkPi {α : Type} {P : α → Type} (f : (a : α) → P a) : (a : α) → P a := fun a => f a

#check mkPi

theorem mkForall {α : Type} {Q : α → Prop} (h : ∀ a, Q a) : ∀ a, Q a := fun a => h a

#check mkForall

def applyPi {α : Type} {P : α → Type} (f : (a : α) → P a) (a : α) : P a := f a

#check applyPi

theorem applyForall {α : Type} {Q : α → Prop} (h : ∀ a, Q a) (a : α) : Q a := h a

#check applyForall

-- ### 具体例: 述語と全称命題

def IsZero : Nat → Prop := fun n => n = 0

#check IsZero 3

theorem all_mul_zero : ∀ n : Nat, IsZero (n * 0) := fun _ => rfl

#check all_mul_zero

/- ✏ 練習
1. `#check applyForall all_mul_zero 7` の表示を予想してから確かめよ。
   引数7を渡すと、結果の命題にも7が入ることを説明せよ。
-/

-- ## 5. 型検査が証明の検査になる

#print axioms modus_ponens

-- ### 仮定を取り違えると、型が合わなくなる

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- theorem bad_trans (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R :=
--   fun hP => hQR hP
