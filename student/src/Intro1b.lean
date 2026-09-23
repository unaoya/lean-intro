-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import Intro1a

-- # 型と項 II — 帰納型と構造

-- ## 1. 帰納型（inductive type）

inductive Signal : Type where
  | red : Signal
  | yellow : Signal
  | green : Signal

#check Signal

#check Signal.red

-- ### `Bool` の定義を見に行く

#check Bool

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive Bool : Type where
--   | false : Bool
--   | true : Bool

-- ### 補足（初読は飛ばしてよい）: `true` と `.true`、`red` と `.red`

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- open Signal in
-- #check red

-- （補足・先取りここまで）

-- ### CH1 との接続: 仮定として使う・結論として示す

#eval match Signal.red with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

/- ✏ 練習
1. 上の `match` の対象を `Signal.yellow` に変えた項と、`Signal.green` に変えた項を
   書き、それぞれの値を予想してから `#eval` で確かめよ。
-/

def next : Signal → Signal := fun s =>
  match s with
  | Signal.red => Signal.green
  | Signal.green => Signal.yellow
  | Signal.yellow => Signal.red

#check next

#eval next Signal.red

/- ✏ 練習（書く）
1. `Signal.red`・`Signal.yellow`・`Signal.green` をそれぞれ `0`・`1`・`2` に
   送る `signalCode : Signal → Nat` を `match` で書け。それぞれの場合に返す項が
   同じ型になることを確かめ、`#eval signalCode Signal.yellow` の値を予想してから実行せよ。
-/

def isRed : Signal → Bool := fun s =>
  match s with
  | .red => true
  | .yellow => false
  | .green => false

#check isRed

/- ✏ 練習
1. `Signal` の「逆回り」`prev : Signal → Signal` を `match` で定義し、
   `#eval prev (next Signal.red)` の表示を予想してから確かめよ
   （`Signal.red` に戻ってくるはずである）。
2. `isRed` にならって `isGreen : Signal → Bool` を書き、
   `#eval isGreen Signal.red` の値を予想してから確かめよ。
3. `def stopSignal : Signal := .red` を宣言し、`#check stopSignal` と
   `#eval stopSignal` の表示を予想してから確かめよ。
   `.red` の接頭辞がどこから分かるかを説明せよ。
-/

-- ### 構成子は引数を取れる

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive Empty : Type

inductive NatOrBool : Type where
  | nat (n : Nat) : NatOrBool
  | bool (b : Bool) : NatOrBool

#check NatOrBool

#check NatOrBool.nat

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- inductive NatOrBool : Type where
--   | nat : Nat → NatOrBool
--   | bool : Bool → NatOrBool

def valueOf : NatOrBool → Nat := fun x =>
  match x with
  | .nat n => n
  | .bool _ => 0

#check valueOf

/- ✏ 練習（書く）
1. 中身の値には触れず、`.nat` の札なら `true`、`.bool` の札なら `false` を
   返す `tagOf : NatOrBool → Bool` を書け。不要な中身には `_` を使える。
   `#eval tagOf (NatOrBool.nat 3)` の値を予想してから確かめよ。
-/

/- ✏ 練習
1. `#eval valueOf (NatOrBool.bool true)` の値を予想してから確かめよ
   （どちらの場合に当たるか）。
2. 「`bool` の札なら中身を、`nat` の札なら `false` を返す」関数
   `flagOf : NatOrBool → Bool` を書き、`#eval flagOf (NatOrBool.bool true)` で
   確かめよ。
-/

-- ### 構成子の引数を複数にする

/- ✏ 練習（書く）
1. 自然数の組 `(a, b)` を表す型 `NatPair : Type` を `inductive` で定義せよ。
   構成子は `mk` の1つとし、自然数を2つ受け取るものとする。
   `#check NatPair.mk` と `#check NatPair.mk 3 5` の表示を予想して確かめよ。
2. 第1成分を返す写像 `firstNat : NatPair → Nat` と、第2成分を返す写像
   `secondNat : NatPair → Nat` を、それぞれ `match` で書け。
   両関数の型を `#check` し、`#eval firstNat (NatPair.mk 3 5)` と
   `#eval secondNat (NatPair.mk 3 5)` の値を予想して確かめよ。
-/

/- ✏ 練習（書く）
1. 自然数 `n` と真偽値 `flag` の組を表す型 `FlaggedNat : Type` を
   `inductive` で定義せよ。構成子は `mk` の1つとする。
   `#check FlaggedNat.mk` と `#check FlaggedNat.mk 3 true` の表示を予想して確かめよ。
2. 自然数の成分を返す `numberOf : FlaggedNat → Nat` と、真偽値の成分を返す
   `flagOfPair : FlaggedNat → Bool` を `match` で書け。
   両関数の型を `#check` し、`FlaggedNat.mk 3 true` に適用した値を予想して
   `#eval` で確かめよ。
-/

/- ✏ 練習（書く）
1. 次の3種類のデータを表す型 `MixedData : Type` を `inductive` で定義せよ。
   構成子 `pair` は自然数を2つ、`flagged` は自然数と真偽値を受け取り、
   `empty` は引数を受け取らないものとする。
   3つの構成子の型を予想して `#check` で確かめよ。
2. 写像 `readNumber : MixedData → Nat` を、`pair a b` は `a + b` に、
   `flagged n flag` は `n` に、`empty` は `0` に送るものとして定める。
   これを `match` で書き、型を `#check` せよ。さらに `MixedData.pair 3 5`、
   `MixedData.flagged 3 true`、`MixedData.empty` に適用した値を予想して `#eval` で確かめよ。
-/

-- ### 型をパラメータにする

inductive MySum (α β : Type) : Type where
  | inl (a : α) : MySum α β
  | inr (b : β) : MySum α β

#check MySum

#check MySum.inl

#check (MySum.inl 3 : MySum Nat Bool)

#check (MySum.inr true : MySum Nat Bool)

def fromSum : MySum Nat Bool → Nat := fun x =>
  match x with
  | .inl n => n
  | .inr _ => 0

#check fromSum

/- ✏ 練習（書く）
1. `MySum Bool Bool` の左右どちらの札からも、中身の `Bool` をそのまま返す
   `mergeBool : MySum Bool Bool → Bool` を書け。
   `#eval mergeBool (MySum.inl true)` と
   `#eval mergeBool (MySum.inr false)` を予想してから確かめよ。
-/

-- ### 補足（初読は飛ばしてよい）: 型をパラメータにした取り出し関数

def getLeft {α β : Type} (d : α) : MySum α β → α := fun x =>
  match x with
  | .inl a => a
  | .inr _ => d

#check getLeft

#eval getLeft 0 (MySum.inr true)

-- （補足・先取りここまで）

/- ✏ 練習
1. `#eval getLeft 7 (MySum.inl 3 : MySum Nat Bool)` の値を予想してから
   確かめよ。（`MySum.inl 3` だけでは `β` が決まらないので、型注釈で教えている。）
-/

-- ### 構成子は自分自身の型を引数に取れる（再帰）

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat

def add : MyNat → MyNat → MyNat := fun m n =>
  match n with
  | .zero   => m
  | .succ k => .succ (add m k)   -- 構造が小さくなる方向への再帰

#check add

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def loop (n : MyNat) : MyNat := loop n

#reduce add (.succ .zero) (.succ .zero)

/- ✏ 練習（書く）
1. `isZeroMyNat : MyNat → Bool` を `match` で書き、`.zero` なら `true`、
   `.succ _` なら `false` を返せ。`#eval isZeroMyNat MyNat.zero` と
   `#eval isZeroMyNat (MyNat.succ MyNat.zero)` の値を予想して確かめよ。
2. `toN : MyNat → Nat` を再帰で書け。`.zero` は `0`、`.succ k` は
   `toN k + 1` に送る。`#eval toN (MyNat.succ (MyNat.succ MyNat.zero))` の
   値を予想してから確かめよ。
-/

/- ✏ 練習
1. `MyNat` の項として 3 を `def myThree : MyNat := …`（`succ` 3回）と書き、
   `#reduce add myThree MyNat.zero` の表示を予想してから確かめよ。
2. 2点の列挙型 `inductive Two : Type where | a : Two | b : Two` を定義せよ。`Two` と `Bool` は
   集合としては同じ2点集合だが、型としては別物である。往復の関数
   `toBool : Two → Bool` と `ofBool : Bool → Two` を書き、
   `#eval toBool (ofBool true)` を確かめよ。
3. `Two → Bool` の関数は、集合のアナロジーで数えると 2 × 2 = 4 通り
   あるはずである。その4つすべてを `def g1 : Two → Bool := …` から `g4` まで
   書け（前問の `toBool` はその1つ）。有限型の間の関数を書くことは、
   **値の対応表を書くこと**にほかならない。
4. （発展）掛け算 `mul : MyNat → MyNat → MyNat` を、本文の `add` の再帰に
   ならって書け（`m × 0 = 0`、`m × (k + 1) = m × k + m` を写す:
   `.zero` の場合は `.zero`、`.succ k` の場合は `add (mul m k) m` を返す）。
   `#eval toN (mul myThree myThree)` の値を予想してから確かめよ
   （`toN`・`myThree` は前の練習で書いたもの）。
5. （発展）上で書いた `toN : MyNat → Nat` の逆向きの関数
   `ofN : Nat → MyNat` を書き、`#eval toN (ofN 3)` の値を予想してから確かめよ。
   （`ofN` では `Nat` の項を `match n with | 0 => … | k + 1 => …` で
   場合分けできる。`| k + 1` は `| .succ k` と同じ「後続の自然数」の場合で、
   `k` は一つ前の自然数を表す。したがって `ofN k` は元の入力より小さい数への
   再帰である。これは方程式 `n = k + 1` を解く操作ではなく、`Nat` の構成子に
   よる場合分けである。この書き方はここが初出である。また、**すべての** `n` で
   往復が恒等になることの証明には数学的帰納法が要る。`CH2.lean` のあとで
   戻ってくるとよい。）
-/

-- ## 2. structure

inductive MyPoint : Type where
  | mk (x y : Nat) : MyPoint

#check MyPoint

def MyPoint.x : MyPoint → Nat := fun p =>
  match p with
  | .mk a _ => a

#check MyPoint.x

structure Point : Type where
  x : Nat
  y : Nat

#check Point

#check Point.mk

def pointFromDot : Point := .mk 1 2

#check pointFromDot

#check Point.x

#eval (Point.mk 1 2).x

-- ### 直積の普遍性を思い出す

/- ✏ 練習（書く）
1. 型 `A` と2本の写像 `f g : A → Nat` が与えられたとする。
   a を組 (f(a), g(a)) に送る写像 `pairAt A f g : A → Point` を定めたい。
   `pairAt (A : Type) (f g : A → Nat) : A → Point` を書き、`#check pairAt` で型を確認せよ。
   A = Nat、f(n) = n + 1、g(n) = 2n として `3` を渡したときの
   第1・第2成分を予想し、`Point.x`・`Point.y` と `#eval` で確かめよ。
-/

/- ✏ 練習（書く）
1. `Point` の第1成分だけを1増やす `moveRight : Point → Point` を書け。
   成分の取り出しには `Point.x`・`Point.y`、作成には `Point.mk` を使う。
   `#eval Point.x (moveRight (Point.mk 1 2))` の値を予想して確かめよ。
-/

-- ### 自分で定義した関数もドットで使える

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

#check Point.swap

#eval (Point.mk 1 2).swap.x

/- ✏ 練習
1. `Point.zeroX (p : Point) : Point` を定義し、第1成分だけを `0` にせよ。
   本体では `p.y` と `.mk` の両方を使う。`#eval (Point.mk 1 2).zeroX.x`
   の値を予想して確かめよ。
2. `#eval (Point.mk 1 2).swap.swap.x` の値を予想してから確かめよ
   （2回入れ替えると元に戻るはずである）。またこの式を、ドットを使わず
   フルネームの適用だけで書き直すと何になるか、紙に書いてから `#eval` で
   一致を確かめよ。
-/

/- ✏ 練習
1. 次の structure を定義し、`#check` で構成子と取り出し関数が
   自動定義されていることを確かめよ:

       structure Circle : Type where
         center : Point
         radius : Nat

2. 点 p と自然数 n から、中心が p、半径が n の円を作る写像を、
   `makeCircle : Point → Nat → Circle` として書け。型を `#check` し、
   `#eval Circle.radius (makeCircle (Point.mk 1 2) 3)` の値を予想して確かめよ。
3. 円からその中心の第1座標を取り出す写像 `centerX : Circle → Nat` を書け。
   型を `#check` し、`#eval centerX (makeCircle (Point.mk 1 2) 3)` の値を予想して確かめよ。
-/

/- ✏ 練習
1. `#eval Point.y (Point.mk 1 2)` の値を予想してから確かめよ。
   さらに `(Point.mk 1 2).y` とも書けることを試し、同じ値が返ることを確かめよ。
2. フィールドの型は、自作の structure でもよい。長方形

       structure Rect : Type where
         corner : Point
         width : Nat
         height : Nat

   を定義し、`def r : Rect := ⟨⟨1, 2⟩, 10, 5⟩` が受理されることを確かめよ
   （`⟨ ⟩` の入れ子が `corner : Point` の分である）。`#eval r.corner.x` の
   値を予想してから確かめよ。`r.corner`、`r.corner.x` の順に型を追うこと。
3. 長方形から幅と高さの積を返す写像 `rectArea : Rect → Nat` を書け。
   型を `#check` し、前問の `r` に対する `#eval rectArea r` の値を予想して確かめよ。
-/

-- ### 型をパラメータにする structure

structure Pair (α β : Type) : Type where
  fst : α
  snd : β

#check Pair

#check Pair.mk

#check Pair.fst

-- ### フィールドを番号で指定する

#eval (Point.mk 1 2).1

#eval (Pair.mk 1 true).2

/- ✏ 練習
1. `#check Pair.mk true 0` の表示を予想してから確かめよ
   （`α`・`β` は何に決まるか）。
2. （発展）`Intro1a.lean` 3節の「カリー化」の正体を自分で書く。組を受け取る関数を
   「1つずつ受け取る」形に直す
   `curryP (F : Pair Nat Nat → Nat) : Nat → Nat → Nat` と、その逆向き
   `uncurryP (G : Nat → Nat → Nat) : Pair Nat Nat → Nat` を書け。
   `#check curryP`・`#check uncurryP` で型を確認し、
   `#eval curryP (fun p => p.fst + p.snd) 3 4` の値を予想してから確かめよ。
-/

-- ### フィールドは前のフィールドに依存してよい

structure PointedType : Type 1 where
  carrier : Type
  point : carrier

#check PointedType

#check PointedType.mk

def pointedNat : PointedType := ⟨Nat, 0⟩

#check pointedNat

-- ### 依存するフィールドも inductive で書ける

inductive MyPointedType : Type 1 where
  | mk (carrier : Type) (point : carrier) : MyPointedType

#check MyPointedType.mk

/- ✏ 練習
1. `def pointedBool : PointedType := ⟨Bool, true⟩` が受理されることを確かめよ。
   また `#check PointedType.mk Nat` の表示を予想してから確かめよ
   （第1引数を渡すと、第2引数の型が決まる）。
-/

/- ✏ 練習（書く）
1. 自然数 n を点付き集合 (Nat, n) に送る写像 `attachNat : Nat → PointedType` を書け。
   型を `#check` し、`#reduce (attachNat 3).point` の値を予想して確かめよ。
2. 点付き集合 (A, a) から台となる型 A を取り出す写像 `baseType : PointedType → Type` を書け。
   型を `#check` し、`#reduce (types := true) baseType pointedNat` と
   `#reduce (types := true) baseType pointedBool` の表示を予想して確かめよ。
   ここで `(types := true)` は、型そのものも計算して表示させる指定である。
   通常の `#reduce` は型の計算を省くので、今回はこの指定を付ける。
3. 点付き集合 (A, a) と写像 f : A → A から、点付き集合 (A, f(a)) を作る関数
   `mapPointed (p : PointedType) (f : p.carrier → p.carrier) : PointedType` を書け。
   型を `#check` し、`#reduce (mapPointed pointedNat Nat.succ).point` の値を予想して確かめよ。
-/

-- ### 復習: 取り出す値の型も入力で変わる

#check PointedType.point

/- ✏ 練習（書く）
1. 点付き集合 (A, a) から点 a を取り出す関数 `getPoint (p : PointedType) : p.carrier` を書け。
   `#check getPoint` の表示を予想して確かめ、結果の型が引数に依存している箇所を指摘せよ。
   さらに `#reduce getPoint pointedNat` と `#reduce getPoint pointedBool` の値を予想して確かめよ。
-/

-- （補足・先取りここまで）

-- ### 族の直積と直和を並べる

/- ✏ 練習
1. 型 α・β とその項 a・b から組を作る
   `makePair (α β : Type) (a : α) (b : β) : Pair α β` を書け。
   `#check makePair Nat Bool 3 true` を確かめよ。
2. 同じ引数から成分を交換した組を作る
   `swapAt (α β : Type) (a : α) (b : β) : Pair β α` を書け。
   `#check swapAt Nat Bool` で残りの型を確かめよ。
3. `#check idAt Signal` の表示を予想せよ。
-/

-- ## 3. まとめ練習 — 小さな型つき言語で書く

/- ✏ 練習
1. 写像 F : ℕ × ℕ → ℕ に対して、G(a, b) = F(b, a) で定まる写像
   G : ℕ × ℕ → ℕ を対応させる操作を考える。
   この対応 F ↦ G を、カリー化を使って
   `flipNat (F : Nat → Nat → Nat) : Nat → Nat → Nat` として書け。
   `#eval flipNat (fun a b => a - b) 3 10` の値を予想してから確かめよ。
2. 写像の集合の間の写像 T : Map(ℕ, ℕ) → Map(ℕ, ℕ) を、
   T(F) = F ∘ F ∘ F、すなわち T(F)(n) = F(F(F(n))) で定める。
   T を `iterate3 (F : Nat → Nat) : Nat → Nat` として書け。
   `#eval iterate3 double 1` の値を予想してから確かめよ。
3. 2点集合 B = \{true, false} と3点集合 S = \{red, yellow, green} を考える。
   写像 f : B → S を f(true) = green、f(false) = red で定め、
   写像 g : S → B を g(green) = true、g(red) = g(yellow) = false で定める。
   B を `Bool`、S を `Signal` で表し、f と g をそれぞれ
   `boolToSignal : Bool → Signal`、`signalToBool : Signal → Bool` として書け。
   合成 g ∘ f の true における値を予想し、
   `#eval signalToBool (boolToSignal true)` で確かめよ。
4. 写像 F : ℕ → ℕ に対して、写像 H : ℕ × ℕ → ℕ × ℕ を
   H(x, y) = (F(x), F(y)) で定める。
   直積 ℕ × ℕ を `Point` で表し、この対応 F ↦ H を
   `mapPoint (F : Nat → Nat) (p : Point) : Point` として書け。
   `#eval (mapPoint double (Point.mk 2 3)).y` の値を予想してから確かめよ。
5. 集合 A, B の直和の間の交換写像 s : A ⊔ B → B ⊔ A を考える。
   A 側の要素 a は、行き先の A 側、すなわち右側の要素 a に送り、
   B 側の要素 b は、行き先の B 側、すなわち左側の要素 b に送る。
   中身は変えず、左右の位置だけを入れ替える写像である。
   直和を `MySum` で表し、A, B も引数として受け取る
   `swapMySum (A B : Type) : MySum A B → MySum B A` を書け。
   `#eval fromSum (swapMySum Bool Nat (MySum.inl true))` の値を予想してから
   確かめよ（`fromSum : MySum Nat Bool → Nat` は1節で定義した）。
6. 各集合 A に対して、その要素 a を点付き集合 (A, a) に送る写像を考える。
   点付き集合を `PointedType` で表し、A も引数として受け取る
   `pointedOf (A : Type) (a : A) : PointedType` を書け。
   2節の `pointedNat` や練習の `pointedBool` を、
   どの型とその項からも作れるように一般化したものである。
   `#check pointedOf Bool true` の表示を予想してから確かめよ。
7. （発展）集合 A と写像 F : A → A に対して、その反復 F^n : A → A を、
   F^0 = id_A、F^n+1 = F ∘ F^n と定める。ここで id_A は A 上の恒等写像である。
   自然数 n と要素 a を F^n(a) に送る写像 ℕ × A → A を、A, F も引数に取り、
   `applyN (A : Type) (F : A → A) (n : Nat) (a : A) : A` として書け。
   `n` の `match` は `| 0 => …`・`| k + 1 => …` の形（1節の練習の
   `ofN` と同じ）。`#eval applyN Nat double 3 1` の値を予想してから確かめよ。
8. （発展）集合 A の対角写像 \Delta_A : A → A × A を、\Delta_A(a) = (a, a) で定める。
   直積を `Pair` で表し、どの型 A でも使える
   `diag (A : Type) (a : A) : Pair A A` を書け。
   `#eval (diag Nat 3).fst` の値を予想してから確かめよ。
   A の項として与えられているのは a だけであることにも注目せよ。
   `Intro1a.lean` 3節の練習（`(Nat → Nat) → Nat` の項を2つ書く）と比較し、
   **型の形によって、書ける項の自由度がどう変わるか**を考えよ。
-/

-- ## 付録: 記号の打ち方まとめ
