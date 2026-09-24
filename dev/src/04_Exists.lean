import «02_Forall»
import «03_InductiveTypes»

/-!
# 型と命題 II — かつ・または・否定・存在量化

`02_Forall.lean` では、含意と全称を関数と適用として読んだ。
`03_InductiveTypes.lean` では、構成子で項を作り、場合分けや射影で使う道具を学んだ。
この章で二つを合わせ、かつ・または・矛盾・存在の証明を読む。

まず、任意の自然数についての存在の証明と、全射の合成を読む。
存在と依存和の対応を整理した後、かつ・または・否定へ進み、偶数の和で道具を組み合わせる。
続いて、等式の証明で使う計算・帰納法と、命題を構成子で作る仕組みを確かめる。
最後に全体の対応をまとめ、検査の詳細と、型と命題の対応の限界を見る。
-/

/-!
## 1. 存在と依存和 — 偶数・全射の例から {#sec-CH2.existence}

「条件 `Q x` を満たす `x` が存在する」は `∃ x, Q x` と書く。示すときは、
実際の候補 `a` と、その候補が条件を満たす証明 `h : Q a` を
`⟨a, h⟩` で与える。たとえば、`2` に等しい自然数は存在する:
-/

theorem exists_eq_two : ∃ n : Nat, n = 2 :=
  ⟨2, rfl⟩

#check exists_eq_two

/-!
    exists_eq_two : ∃ n, n = 2

`Exists` は命題を作る帰納型で、その構成子 `Exists.intro` は証人と証明を受け取る。
`⟨a, h⟩` は、この構成子で証明を作る記法である。

ここで `2` が**証人**、`rfl` が `2 = 2` の証明である。`⟨a, h⟩` は組と同じ記法だが、
ここでは存在命題の構成子 `Exists.intro` を書いている。存在証明を一般の
データの組とまったく同じようには扱えない。別の命題を証明するために `match` で
分解できるが、証人を計算用の値としてそのまま射影することはできない。
理由は[9節](#sec-CH.prop-elimination)で見る。

`02_Forall.lean` で学んだ全称と、いま見た存在を組み合わせよう。

### 例1: 任意の自然数 n について、n + n は偶数

偶数の定義から確認する。「m は偶数」とは「半分になる数がある」、すなわち
**m = 2k となる k が存在する**ことである。

**ふつうの証明**。

1. 自然数 n を任意に取る。
2. 既知の定理 2n = n + n の左右を入れ替えて、n + n = 2n を得る。
3. よって「半分」の証人として n が取れ、n + n は偶数である。∎

**論理式**。証明の構造が見えたところで、主張そのものも形式の言葉に直して
おく。「任意の自然数 n について、n + n は偶数である」は、述語論理の
論理式では

    ∀n Even(n + n)

と書ける。述語 Even を定義まで開けば

    ∀n ∃k (n + n = 2k)

である。日本語の「任意の…について」「…となる—がある」が、量化子 ∀・∃ に
置き換わっただけである。形式化と呼ばれる作業には、この**主張の形式化**と、
これから行う**証明の形式化**の2段階がある——主張の側は、論理式で書けた
ことで論理的な骨格が見えた。Lean ではさらに、変数の型や使う定義を明示する。

**形式化を意識した版**。同じ証明を、各段で**何の証明の仕方を使っているか**を
名指ししながら読み直す。

まず自然数 n を任意に取り、この固定した n について「n + n は偶数」をこれから証明する
——**これが全称量化された命題の証明の仕方**である。「任意の自然数 n について」を
示すとは、自然数 n を1つ固定して（ただし自然数であること以外は何も仮定せずに）示すことに
ほかならない。

n を固定したら、偶数の**定義に戻る**。「m が偶数」とは「ある k が存在して
m = 2k となる」ことだった。いまの場合に当てはめると、示すべきは
「n + n = 2k となる k が存在する」である。そして**存在量化された命題の
証明の仕方**は、(i) 存在するものの**候補**を1つ挙げ、(ii) その候補が実際に
求められる性質を満たすことの**証明**を与える——この2つを**組として**与えることである。

各 `n` に対して、証人 `k` と等式 `n + n = 2 * k` の証明を組にして返す。
集合族の言葉では、$n$ を、$\bigsqcup_{k \in \mathbb{N}} (n+n=2k)$ の要素に送る
依存関数に対応する。ここで各等式は、その証明の型として見ている。

ここでは候補として k = n を取ればよい。すると満たすべき性質は n + n = 2n と
なり、これは成り立つので、証明が完成した。——ただし最後の一歩で、
**n + n = 2n を既知の定理として使っている**ことには注意しておく
（この「既知」を自分で底までたどるとどうなるかは、下の補足で掘り下げる）。

使った頭の動きは3つだけである: **全称の証明**（任意に取って示す）、
**定義に戻る**、**存在の証明**（候補+性質の証明）。

**項**。これを Lean に持ち込む。02_Forall で学んだ全称と、直前の小例で見た存在を使うと、
「任意の自然数 n について」は `∀ n : Nat, …`、「…となる k が存在する」は `∃ k, …` と書く。
すると主張が、論理式とほぼ字面どおりに対応する形で書ける:

    論理式:  ∀n ∃k (n + n = 2k)
    Lean:    ∀ n : Nat, ∃ k, n + n = 2 * k

違いは1つだけ——**束縛変数の走る範囲が型として明示される**（`∀ n : Nat`）。
述語論理では文脈が決めていたものが、Lean では型の仕事になる。
**Lean の命題は、型注釈のついた論理式**と読んでよい。
主張の形式化はこれで済んだ。残るは証明の形式化である。

02_Forall で見た `theorem` の形に当てはめ、コロンの右に命題、`:=` の右に
証明の項を書く。その前に、使う既知の定理の型も確認しておこう:
-/

#check Nat.two_mul

/-!
    Nat.two_mul (n : Nat) : 2 * n = n + n

`Nat.two_mul` は**依存関数**である。`n` を渡すと、その `n` に応じた
等式 `2 * n = n + n` の証明を返す。等式そのものと、その証明の型を区別して見よう。
-/

#check (2 * 3 = 3 + 3)

/-!
    2 * 3 = 3 + 3 : Prop
-/

#check Nat.two_mul 3

/-!
    Nat.two_mul 3 : 2 * 3 = 3 + 3

等式は `Prop` 型の項であり、`Nat.two_mul 3` はその等式を型として持つ項である。

いま必要なのは逆向きの等式なので、対称律を使う。`Eq.symm` は
`a = b` の証明を受け取り、`b = a` の証明を返す関数である。
-/

#check Eq.symm

/-!
    Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a

ここで `Sort u` は型の宇宙を表す記法で、いまは `α` を `Nat` として読む。
詳しくは[6節](#sec-CH.nat-proofs)の補足で扱う。
-/

#check Eq.symm (Nat.two_mul 3)

/-!
    Eq.symm (Nat.two_mul 3) : 3 + 3 = 2 * 3

`Eq.symm h` は `h.symm` とも書ける。構造の取り出しと同じドット記法を、
証明という項にも使っている。以下では、まず関数名を明記した形で書く。
-/

theorem even_double : ∀ n : Nat, ∃ k, n + n = 2 * k :=
  fun n => ⟨n, Eq.symm (Nat.two_mul n)⟩

#check even_double

/-!
    even_double (n : Nat) : ∃ k, n + n = 2 * k

エラーが出ない＝この項が宣言どおりの型を持つことを機械が確認した、
ということである。形式化を意識した版の頭の動きが、そのまま項の部品に
写っている:

* `fun n =>` が「n を任意に取る」——全称の証明は、**どの n を渡されても、
  その n での証明を返す関数**になる（[`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の
  `fun` そのもの）。
* `⟨n, …⟩` が「候補と、性質を満たす証明」——存在命題の構成子も
  [`03_InductiveTypes.lean` 2節](#sec-Intro1.structures)の組と同じ `⟨ ⟩` 記法で書ける。
  この候補のことを以後**証人**と呼ぶ。
* `Eq.symm (Nat.two_mul n)` が「既知の定理を使う」——既知の定理
  `Nat.two_mul n : 2 * n = n + n` は名前のついた完成品の項で、`n` を渡す
  **適用**の形で取り出す。`.symm` は等式の左右を入れ替える道具である。

ところで論理式の側では、述語 Even に名前を付けて ∀n Even(n + n) と
**略記**できた。Lean でも同じことができる——述語を**名前のついた定義**に
すればよい:
-/

/--
偶数であること: 半分になる数が存在する。
-/

def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

#check IsEven

/-!
    IsEven (n : Nat) : Prop
-/

/-!
主張は `∀ n : Nat, IsEven (n + n)` と略記できて——
-/

theorem isEven_double : ∀ n : Nat, IsEven (n + n) :=
  fun n => ⟨n, Eq.symm (Nat.two_mul n)⟩

#check isEven_double

/-!
    isEven_double (n : Nat) : IsEven (n + n)

**証明の項は一字も変わらない**。`IsEven (n + n)` と `∃ k, n + n = 2 * k` が
定義上同じであることは、型検査器が**定義を展開して勝手に照合してくれる**
からである（`Map Nat Nat` を計算すると `Nat → Nat` になったのと同じ）。
形式化を意識した版の「**定義に戻る**」に対応する部品が項のどこにもないのは、
このためである。以後は略記した `IsEven` の側を使う。

### 例2: 存在するものを使う

存在を**示す**ときは証人と根拠を `⟨a, ha⟩` で渡した。存在命題の証明を
**使う**ときは、その構成子を `match` で調べ、証人と根拠に名前を付ける。

次の小例では、「`Q a` ならば `R a`」がすべての `a` について成り立つとする。
さらに `Q a` を満たす `a` が存在するなら、同じ `a` が `R a` も満たす:
-/

theorem exists_map {α : Type} {Q R : α → Prop} :
    (∀ a, Q a → R a) → (∃ a, Q a) → ∃ a, R a :=
  fun hqr h =>
    match h with
    | ⟨a, ha⟩ => ⟨a, hqr a ha⟩

#check exists_map

/-!
    exists_map {α : Type} {Q R : α → Prop} : (∀ (a : α), Q a → R a) → (∃ a, Q a) → ∃ a, R a

型を順に追うと、`a : α`、`ha : Q a`、`hqr a : Q a → R a`、
したがって `hqr a ha : R a`。よって `⟨a, hqr a ha⟩ : ∃ a, R a` となる。
`match` の枝に入ったあとの型だけを見れば、`02_Forall.lean` の modus ponens と同じ関数適用である。
-/

/-!
### 等式に関数を適用する・等式をつなぐ

全射の合成では、`ha : f a = b` から `g (f a) = g b` を得て、
`hb : g b = c` とつなぐ。この二つの操作も、証明を受け取る関数である。
-/

#check congrArg

/-!
    congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂

`congrArg g ha` は、等式 `ha` の両辺に同じ関数 `g` を施した等式の証明になる。
-/

#check Eq.trans

/-!
    Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

`Eq.trans h₁ h₂` は、`a = b` と `b = c` の二つの証明を受け取り、`a = c` を返す。
これも `h₁.trans h₂` と書ける。以下では、何に何を渡すかが見える形で用いる。
-/

/-!
### 例3: 全射どうしの合成は全射

今度は、写像 f : A → B と g : B → C がともに全射であるとする。
その全射性をそれぞれ hf・hg と名付け、合成 g∘f : A → C も全射であることを示そう。

**ふつうの証明**。「c を取る。g の全射性より g b = c となる b があり、
f の全射性より f a = b となる a がある。すると g (f a) = g b = c。∎」

**論理式**。示すべき結論「合成 $g \circ f$ が全射」は、定義まで開くと

$$\forall c\, \exists a\, \bigl(g(f(a)) = c\bigr)$$

——例1と同じ「∀ の内側に ∃」の形が、関数の文脈で再登場する。

**形式化を意識した版**（ここまでの動きの総復習である）。
c を任意に取る（全称の証明）。全射の定義「どの点にも、そこへ送られてくる元が
ある」に戻ると、hg c は「g b = c となる b の存在」の証明——存在の使い方で
b と hb を**取り出す**（上の `exists_map` と同じ）。hf b からも a と ha を
取り出す。示すべきは
「g (f a) = c となる a の存在」だから、候補 a と性質の証明を
`⟨a, …⟩` で構成する（例1の前の存在の小例）。
性質 g (f a) = c は等式の連鎖で: ha の**両辺に g を施して** g (f a) = g b、
hb と**つなぐ**。∎

**項**。まず論理式をそのまま型に（仮定も全射の定義を開いた形で書く）:
-/

example {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : ∀ c, ∃ b, g b = c) (hf : ∀ b, ∃ a, f a = b) :
    ∀ c, ∃ a, g (f a) = c :=
  fun c =>
    match hg c with
    | ⟨b, hb⟩ =>
      match hf b with
      | ⟨a, ha⟩ => ⟨a, Eq.trans (congrArg g ha) hb⟩

/-!
ライブラリの述語 `Function.Surjective` で略記して書き直すと——
**証明の項は一字も変わらない**（定義上同じ命題だからである。例1と同じ）:
-/

theorem comp_surjective {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Surjective (fun x => g (f x)) :=
  fun c =>
    match hg c with
    | ⟨b, hb⟩ =>
      match hf b with
      | ⟨a, ha⟩ => ⟨a, Eq.trans (congrArg g ha) hb⟩

#check comp_surjective

/-!
    comp_surjective {α β γ : Type} {f : α → β} {g : β → γ} (hg : Function.Surjective g) (hf : Function.Surjective f) :
      Function.Surjective fun x ↦ g (f x)

[`02_Forall.lean` の1節](#sec-CH1.forall-examples)の単射の合成と並べると対になっている: 単射は `fun` と適用だけの世界、全射は存在の
構成子と `match` の世界。ここでは二つ目の対象 `hf b` が一つ目で得る `b` に依存するため、
二つの対象を独立に並べる形の `match` にはできない。入れ子の `match` は、「b を取り出した**あとの世界**で a を
取り出す」という証明の依存関係を、形として見せている。

-/

/-!
### 整理 — 依存和と「存在する」 {#sec-CH.dependent-sums}

偶数と全射の例では、`∃` の証明を `⟨証人, 根拠⟩` で作り、`match` で使った。
この二つの操作を、型の世界の依存和と並べて整理しよう。

直積 `α × β` を一般化して、第二成分の型が第一成分に依存してよいことにしたのが依存和
`(a : α) × P a`（`P : α → Type`、型の族）。命題側で対応するのが存在量化
`∃ a, Q a`（`Q : α → Prop`、命題の族）。

**示すとき**: `⟨a, b⟩`。「どの点か」と「その点で成り立つこと」を組にする。
存在を示すには、実際に点を1つ挙げて、それが条件を満たすことを言えばよい、というのと同じ。

**使うとき**: 組を分解する。型側は `.fst`・`.snd` で取り出せる。
存在の証明は、別の命題を証明するために `match` で分解する。
データとして第一成分を射影する操作との違いは、[9節](#sec-CH.prop-elimination)で詳しく見る。
-/

def mkSigma {α : Type} {P : α → Type} (a : α) (b : P a) : (a : α) × P a := ⟨a, b⟩

#check mkSigma

/-!
    mkSigma {α : Type} {P : α → Type} (a : α) (b : P a) : (a : α) × P a
-/

theorem mkExists {α : Type} {Q : α → Prop} (a : α) (h : Q a) : ∃ a, Q a := ⟨a, h⟩

#check mkExists

/-!
    mkExists {α : Type} {Q : α → Prop} (a : α) (h : Q a) : ∃ a, Q a

`mkSigma` と重なる。「存在を示すには証人 `a` と根拠 `h` を出せばよい」が、
そのまま引数の列になっている。
-/

/--
型側: 組を受け取る関数は、2引数の関数と同じこと（カリー化）。
-/

def currySigma {α γ : Type} {P : α → Type} : (((a : α) × P a) → γ) → ((a : α) → P a → γ) :=
  fun f a b => f ⟨a, b⟩

#check currySigma

/-!
    currySigma {α γ : Type} {P : α → Type} : ((a : α) × P a → γ) → (a : α) → P a → γ
-/

/--
命題側: 「存在するなら `r`」は「どの点についても、条件を満たすなら `r`」と同じこと。
`currySigma` と同じ証明項で書ける。
-/

theorem curryExists {α : Type} {r : Prop} {Q : α → Prop} : ((∃ a, Q a) → r) → (∀ a, Q a → r) :=
  fun f a b => f ⟨a, b⟩

#check curryExists

/-!
    curryExists {α : Type} {r : Prop} {Q : α → Prop} : ((∃ a, Q a) → r) → ∀ (a : α), Q a → r

`currySigma` と重なる（カリー化は命題の世界でも同じ形）。
-/

/-!
### ✏ 練習

1. `example : ∃ n : Nat, IsZero n := ⟨0, rfl⟩` が通ることを確かめよ。

2. 任意の自然数 `n` について `n + n + n` が3の倍数であることを示せ。
   `theorem triple_multiple : ∀ n : Nat, ∃ k, n + n + n = 3 * k` を書け。
   ヒントとして、`Nat.succ_mul 2 n` は `3 * n = 2 * n + n` を与える。
   `Nat.two_mul n` と、上で使った `congrArg`・`Eq.trans` を組み合わせよ。
-/

/-!
## 2. 直積型と「かつ」 {#sec-CH.products}

「p かつ q」から「q かつ p」を示す普通の証明を考えよう。
仮定から p と q を取り出し、結論に必要な順にそろえればよい。
この二つの動きが、組の射影と構成に対応する。

**示すとき**: `⟨a, b⟩` で作る。両方の成分を揃えれば組が作れる。
`p` の証明と `q` の証明を揃えれば `p ∧ q` の証明になる。

**使うとき**: `.left` と `.right` で取り出す。組からは各成分が取れる。
命題の言葉では、`p ∧ q` からは `p` も `q` も示せる。
証明項の言葉では、`h : p ∧ q` から `h.left : p` と `h.right : q` を作り、
それぞれ `p` の証明・`q` の証明として使える。
名前の付いたフィールドを取り出す書き方は、structure と同じである。
-/

def mkProd {α β : Type} (a : α) (b : β) : α × β := ⟨a, b⟩

#check mkProd

/-!
    mkProd {α β : Type} (a : α) (b : β) : α × β
-/

theorem mkAnd {p q : Prop} (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

#check mkAnd

/-!
    mkAnd {p q : Prop} (hp : p) (hq : q) : p ∧ q

`mkProd` の `×` が `∧` に変わっただけである。
-/

/--
型側: 組を入れ替える。
-/

def swapProd {α β : Type} : α × β → β × α := fun x => ⟨x.snd, x.fst⟩

#check swapProd

/-!
    swapProd {α β : Type} : α × β → β × α
-/

/--
命題側: 「かつ」を入れ替える。`swapProd` と同じように、二つの成分を交換する。
-/

theorem swapAnd {p q : Prop} : p ∧ q → q ∧ p := fun h => ⟨h.right, h.left⟩

#check swapAnd

/-!
    swapAnd {p q : Prop} : p ∧ q → q ∧ p

`swapProd` と同じ組み立て方であり、使うフィールド名だけが異なる。
-/

/-!
### ✏ 練習

1. `theorem and_left {p q : Prop} : p ∧ q → p` と型側の対応物
   `def fst' {α β : Type} : α × β → α` を書き比べよ。
2. `theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r)` を `⟨…⟩` と `.left`・`.right` で書け。
3. 具体的な命題でも示し方は同じであることを、
   `example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩` で確かめよ。

4. 各点で二つの証明を組にして、
   `theorem all_and {α : Type} {Q R : α → Prop} :
   (∀ a, Q a) → (∀ a, R a) → ∀ a, Q a ∧ R a` を書け。

5. `theorem exists_left {α : Type} {Q R : α → Prop} :
   (∃ a, Q a ∧ R a) → ∃ a, Q a` を書け。
   証人はそのまま使い、根拠の左側だけを取り出す。
-/

/-!
## 3. 直和型と「または」 {#sec-CH.sums}

**示すとき**: `.inl` か `.inr` のどちらかで作る。左右どちらかの成分があればよい。
`p` の証明があれば `p ∨ q` が言えるし、`q` の証明でもよい。

**使うとき**: 場合分け（`match`）。和の項を使うには、
左のときと右のときの両方について行き先を用意する必要がある。
「または」を使うときに場合分けするのと同じ。
-/

def inlSum {α β : Type} (a : α) : α ⊕ β := .inl a

#check inlSum

/-!
    inlSum {α β : Type} (a : α) : α ⊕ β
-/

theorem inlOr {p q : Prop} (hp : p) : p ∨ q := .inl hp

#check inlOr

/-!
    inlOr {p q : Prop} (hp : p) : p ∨ q

`inlSum` と重なる。
-/

/--
型側: 和を入れ替える。左なら右へ、右なら左へ。
-/

def swapSum {α β : Type} : α ⊕ β → β ⊕ α := fun x =>
  match x with
  | .inl a => .inr a
  | .inr b => .inl b

#check swapSum

/-!
    swapSum {α β : Type} : α ⊕ β → β ⊕ α
-/

/--
命題側: 「または」を入れ替える。これも同じ形の場合分けで書ける。
-/

theorem swapOr {p q : Prop} : p ∨ q → q ∨ p := fun h =>
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

#check swapOr

/-!
    swapOr {p q : Prop} : p ∨ q → q ∨ p

`swapSum` と重なる。
-/

/--
型側の「使うとき」を一般の形で書いたもの。
-/

def elimSum {α β γ : Type} : α ⊕ β → (α → γ) → (β → γ) → γ := fun x f g =>
  match x with
  | .inl a => f a
  | .inr b => g b

#check elimSum

/-!
    elimSum {α β γ : Type} : α ⊕ β → (α → γ) → (β → γ) → γ
-/

/--
命題側の「使うとき」。`Or.elim` と同じもの。字面は上と同じ。
-/

theorem elimOr {p q r : Prop} : p ∨ q → (p → r) → (q → r) → r := fun h f g =>
  match h with
  | .inl hp => f hp
  | .inr hq => g hq

#check elimOr

/-!
    elimOr {p q r : Prop} : p ∨ q → (p → r) → (q → r) → r

`elimSum` と重なる。「場合分けで示す」ことの正体が、この型である。
-/

/-!
### ✏ 練習

1. `theorem or_idem {p : Prop} : p ∨ p → p` を `match` で書け（どちらの札でも中身は同じ）。
2. `theorem or_map {p q r : Prop} : (p → q) → p ∨ r → q ∨ r` を書け
   （札を見て、左のときだけ関数を適用する）。
3. `example : (1 = 2) ∨ (2 = 2) := .inr rfl` が通ることを確かめよ
   （左の札が**偽の命題**でも、右から入れる）。
-/

/-!
## 4. 空の型と「⊥」 {#sec-CH.empty-types}

項が1つもない型が `Empty`、証明が1つもない命題が `False`。

**示すとき**: 手段が**ない**。これが空であることの意味そのもので、
作り方が用意されていないから項（証明）が存在しない。

**使うとき**: 場合分けすべき場合が1つもないので、
「もし項が手に入ったなら何でも作れる」という形になる。
矛盾からは何でも従う、というのと同じ。
-/

/--
型側: `Empty` の項があれば何の型の項でも作れる。
-/

def elimEmpty {α : Type} : Empty → α := fun e => e.elim

#check elimEmpty

/-!
    elimEmpty {α : Type} : Empty → α
-/

/--
命題側: 矛盾からは何でも従う。
-/

theorem elimFalse {p : Prop} : False → p := fun h => h.elim

#check elimFalse

/-!
    elimFalse {p : Prop} : False → p
-/

/--
否定 `¬p` は `p → False` のことなので、実は新しい作り方ではない。
-/

theorem notIntro {p : Prop} (h : p → False) : ¬p := h

#check notIntro

/-!
    notIntro {p : Prop} (h : p → False) : ¬p
-/

/-!
### False と True

`False` は構成子を持たない帰納型で、`Empty` に対応する命題である。
一方、`True` は構成子 `True.intro` を一つ持ち、いつでも証明できる。
型の世界で見た「項の作り方」が、命題の世界では「証明の作り方」になっている。
`true : Bool` はデータ、`True : Prop` は命題であり、この二つは区別する。
-/

/-!
### ✏ 練習

1. `theorem noContra {p q : Prop} : p → ¬p → q` を書け。ヒント: `¬p` は `p → False` なので、
   適用すると `False` が出る。あとは `.elim`。
2. `theorem dni {p : Prop} : p → ¬¬p` を書け（`¬¬p` を**示す**向き。ほとんど1語で書ける）。
   書けたら、逆向き `¬¬p → p` にも挑戦して、**書けない**ことを確かめよ。
   書き方は [`06_Topology.lean` の2節](#sec-Top.sets) `compl_compl`（`Classical.byContradiction` を使う）で、
   その代償（公理への依存）は末尾の公理の節で分かる。
3. `example : ¬False := fun h => h` が通ることを確かめよ
   （`¬False` は `False → False`——恒等関数が証明になる）。
-/

/-!
## 5. 偶数と偶数の和は偶数 {#sec-CH2.even-add}

**ふつうの証明**。

1. n, m を任意に取り、hn「n は偶数」・hm「m は偶数」を仮定する。
2. hn から、n = 2k となる k を取り、この等式を hk と名付ける。
3. hm から同様に l を取り、等式を hl と名付ける。
4. hk の両辺に右から m を足して、n + m = 2k + m。
5. hl の両辺に左から 2k を足して、2k + m = 2k + 2l。
6. 分配法則より 2k + 2l = 2(k + l)。4〜6 を = のつながりとして読めば
   n + m = 2(k + l)。
7. よって証人 k + l により、n + m は偶数である。∎

**論理式**。主張は

    ∀n ∀m (Even(n) → Even(m) → Even(n + m))

——n と m の全称量化の内側に、「ならば」（→）が2つ並ぶ形である
（Even(n) ∧ Even(m) → … と「かつ」でまとめても同値だが、仮定を1つずつ
取るふつうの証明の読みには、→ の並びのほうが対応する）。

**形式化を意識した版**。今度は仮定つきの命題である。「…ならば—」の証明の
仕方は、**仮定を取って**（名前を付けて）結論を示すこと——全称のときの
「n を取る」と同じ頭の動きである。

仮定 hn を**使う**番になったら、また定義に戻る。hn は「n = 2k となる k が
存在する」ことの証明である。**存在量化された命題の使い方**は、証明の仕方の
ちょうど逆で、**存在するものを1つ取り出して名前を付ける**——「k をそういう
数とする。以後 hk : n = 2 * k が使える」と宣言する動きである。hm からも
同様に l と hl を取り出す。

示すべきは（定義に戻ると）「n + m = 2j となる j の存在」。候補は j = k + l で、
満たすべき性質は n + m = 2(k + l) である。この等式は一度には出ないので、
**等式の連鎖**で作る: hk の**両辺に同じ操作 (· + m) を施して** n + m = 2k + m、
hl から同様に 2k + m = 2k + 2l、分配法則（既知の定理）で 2k + 2l = 2(k + l)、
最後に**3本の等式をつなぐ**。ふつうの証明で「= を続けて書く」ことの正体は、
この「両辺に同じ操作」と「つなぐ」の繰り返しである。

**項**。`IsEven n` は定義を開けば `∃ k, n = 2 * k` である。
帰納型 `Exists` の構成子を `match` で調べると、証人 `k` と根拠 `hk` が得られる。
もう一方の仮定も同じように、二つ目の `match` で分解する。

等式をつなぐ操作は、全射の合成で使った `congrArg` と `Eq.trans` である。
追加で使う分配法則の型を確認しよう。
-/

#check Nat.mul_add

/-!
    Nat.mul_add (n m k : Nat) : n * (m + k) = n * m + n * k

`Nat.mul_add 2 k l` の対称形により、`2 * k + 2 * l = 2 * (k + l)` が得られる。
途中の等式に型と名前を付け、何をつないでいるかが見える形で書く。
`let h : P := ...` は、この式の中で使う項に名前を付ける書き方である。
-/

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

#check isEven_add

/-!
    isEven_add {n m : Nat} (hn : IsEven n) (hm : IsEven m) : IsEven (n + m)

仮定 hn・hm が**引数**になっていることに注意——「ならばの証明=仮定を取る」も、
項では `fun` と同じ扱いである（ふつうの証明の (1) は引数の宣言に吸収されている）。
主張全体も論理式 ∀n ∀m (… → … → …) の写しである: 定理の引数の列は
∀ と → を [`01_TypesAndTerms.lean` 3節](#sec-Intro1.functions)の binder 形式で書いた
もので、n・m は値から決まるため暗黙引数 `{ }` になっている。

-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 「既知」だった 2n = n + n を自分で証明する

例1で使った `Nat.two_mul` を、今度は定義と計算まで自分でたどってみる。

**ふつうの証明**。

1. n = 0 のとき: 両辺とも 0。
2. n = k + 1 のとき: k での等式 2k = k + k が使えるとする。
   2(k + 1) = 2k + 2 = (k + k) + 2 = (k + 1) + (k + 1)。∎

**論理式**。主張は

    ∀n (2n = n + n)

——量化子1つと等式だけの、いちばん簡素な形である。今回は述語の略記も要らない。

**形式化を意識した版**。全称の証明の仕方には、「任意に取る」のほかにもう1つ、
自然数に固有の方法がある——**帰納法**である: 0 の場合を示し、
「k で成り立つ**ならば** k + 1 でも成り立つ」を示す。

0 の場合、示すべき 2·0 = 0 + 0 は**両辺とも計算すれば 0** になる。計算で
一致する等式には、それ以上の証明は要らない。k + 1 の場合のポイントは、
**帰納法の仮定 2k = k + k を「既知の定理」と同じ資格で使ってよい**こと——
あとは例2で覚えた等式の連鎖である。

ただし、連鎖の途中の1歩「(k + 1) + k = (k + k) + 1」が、また別の「既知」
（succ_add と呼ばれる事実）を呼んでしまう。信用しないと決めたので、
**これも同じ流儀（帰納法）で証明する**。今度の各段は計算と「両辺に + 1」
だけで閉じ、新しい既知はもう現れない——底に着いた。

**項**。帰納法は、[`03_InductiveTypes.lean` 1節](#sec-Intro1.inductive-types)の**再帰**
そのものとして書ける。「k での場合の証明」は、自分自身の再帰呼び出しで
手に入る（`toN` の再帰と同じ形である。また、計算で一致する等式の証明は
`rfl` と書く——[`02_Forall.lean` の0節](#sec-CH.propositions)で見た）:
-/

theorem succ_add' : ∀ (n m : Nat), (n + 1) + m = (n + m) + 1 := fun n m =>
  match m with
  | 0     => rfl                                  -- 両辺とも計算で n + 1
  | j + 1 => congrArg (· + 1) (succ_add' n j)     -- 帰納法の仮定は再帰呼び出し

theorem two_mul_from_scratch : ∀ n : Nat, 2 * n = n + n := fun n =>
  match n with
  | 0     => rfl
  | k + 1 =>
    (congrArg (· + 2) (two_mul_from_scratch k)).trans -- 2(k+1) = 2k+2 = (k+k)+2
      ((congrArg (· + 1) (succ_add' k k)).symm :
        (k + k) + 2 = (k + 1) + (k + 1))           -- 型注釈はふつうの証明の式変形の写し

#check two_mul_from_scratch

/-!
    two_mul_from_scratch (n : Nat) : 2 * n = n + n

どこまで掘っても、現れたのは同じ仕組みで書かれた項だけだった。
それを機械に確認させることもできる:
-/

#print axioms two_mul_from_scratch

/-!
    'two_mul_from_scratch' does not depend on any axioms

例1で「既知」と呼んだものは単なる未検査の信用ではない——**底（定義と計算）まで、
すべて検査済みの項**なのである。
-/

/-!
CALLOUT_END
-/

/-!
### ✏ 練習

1. `theorem isEven_two_mul : ∀ n : Nat, IsEven (2 * n)` を `isEven_double` に
   ならって書け（証人は `n`、根拠は `rfl` で済む——なぜ済むのかも考えること）。
2. 「n が偶数なら n + 2 も偶数」を、本文と同じ段構え
   （ふつうの証明 → 論理式 → 形式化を意識した版 → 項）で自分で書け。
   ヒント: 証人は `k + 1`。式変形の最後は `Nat.mul_succ` の対称形が使える。
3. `example : IsEven 10 := ⟨5, rfl⟩` が通ることを確かめよ
   （例1の一般論の、具体的な1点での実例である）。
-/

/-!
## 6. 等式と自然数の証明 — 計算・帰納法・構成子 {#sec-CH2.computation}

前の例では、既知の等式の証明を関数として使った。ここでは、等式の証明そのものが
どのように作られているかを見る。まず、計算で確かめられる例から始めよう。
-/

example (n : Nat) : n + 0 = n := rfl

/-!
`n + 0` は加算の定義から `n` に計算できる。このため、同じ項どうしの等式を示す
`rfl` が使える。もう一方の順に足す等式も成り立つが、こちらは既知の定理で示そう。
-/

example (n : Nat) : 0 + n = n := Nat.zero_add n

/-!
どちらも等式の証明だが、作り方は違う。`rfl` を使える仕組みと、
計算だけでは済まない場合を支える帰納法の仕組みを、順に整理する。
-/

/-!
### 整理 — 自然数の命題と構成子 {#sec-CH.nat-proofs}

ここまでの等式の例では、計算で両辺が一致すれば `rfl` で証明できた。
その仕組みを、等式 `Eq` の定義と構成子から整理しよう。さらに順序 `Nat.le` も見る。
`=` や `≤` といった命題を作るもの自体が、`03_InductiveTypes.lean` の `MyNat` などと
同じく**帰納型として定義されている**。

### 等しさ `Eq`

`a = b` は `Eq a b` の記法で、`Eq` は構成子を1つだけ持つ帰納型である。
表示中の `Sort u` は、`Prop` や `Type` などをまとめて扱う型の宇宙の表記である:

    inductive Eq {α : Sort u} : α → α → Prop
      | refl (a : α) : Eq a a

構成子 `refl` が作れるのは、両辺が同じ `Eq a a` の形の項だけ。
「`a = a` はいつでも証明できて、それが等しさの証明のすべて」というのが、
等しさの定義そのものになっている。
-/

example : 0 = 0 := Eq.refl 0
example : 0 = 0 := rfl        -- 略記。引数の `0` は型 `0 = 0` の側から決まる

/-!
一方 `0 = 1` という型の項は `refl` では作れず、実際この型に項は存在しない。
証明のない命題は、項のない型 `Empty`（[4節](#sec-CH.empty-types)）と同じ立場にある。

[`02_Forall.lean` の0節](#sec-CH.propositions)で `1 + 1 = 2` が `rfl` で証明できたのは、型検査が両辺を
**計算してから**比べるからである。`1 + 1` は計算すると `2` になるので、
`1 + 1 = 2` は `2 = 2` と同じ型であり、`refl` の射程に入る。

-/

/-!
-/

/-! CALLOUT_START optional -/
/-!
### 補足: Prop と Type をまとめて扱う Sort

`Sort` は、`Prop` と `Type`、`Type 1`、…をまとめて扱うための宇宙の表記である。
次の各行は、別々の型の対応ではなく、**同じものの2通りの書き方**を並べている。

| これまでの表記 | Sort による表記 |
|---|---|
| `Prop` | `Sort 0` |
| `Type`（`Type 0`） | `Sort 1` |
| `Type 1` | `Sort 2` |
| `Type u` | `Sort (u + 1)` |

`α : Sort u` と書けば、命題も通常の型も対象にできる。
例えば `u = 0` なら `α : Prop`、`u = 1` なら `α : Type` である。
この `u` は**宇宙のレベル**を表すパラメータで、通常の関数に渡す自然数の引数ではない。
具体的に使うときのレベルは、通常 Lean が推測する。

-/
/-! CALLOUT_END -/

/-!
### rfl の型を読む

等式の反射性は「どんな型の、どんな項 a についても、a = a」である。
だから `rfl` は、型とその項を受け取って `a = a` の証明を返すはずである。
型を確かめよう:
-/

#check rfl

/-!
    rfl.{u} {α : Sort u} {a : α} : a = a

表示を左から読もう。

* `.{u}` は、宇宙レベルをパラメータとして持つという表示。
* `{α : Sort u}` は、等式の両辺が属する型を受け取る暗黙引数。
* `{a : α}` は、その型の項を受け取る暗黙引数。
* 最後の `a = a` は結果の型。つまり、返す項はこの等式の証明である。

暗黙引数なので、普通は型や項を明示せず `rfl` とだけ書き、期待される等式から補ってもらう。
`rfl` は、等式の構成子を使った証明 `Eq.refl a` の、引数 `a` を暗黙にしたものである。
先ほどの `Eq` の定義にあった構成子が、この `Eq.refl` である。

`one_add_one` の右辺では、期待される型は `1 + 1 = 2` だった。
`rfl` が与える `a = a` という型を、この期待される型と照合する。
`1 + 1` と `2` は計算で一致するので、両方を同じ `a` として照合でき、受理される。

ここで型検査が何をしたかに注意。「項が指定された型を持つか」という
[`01_TypesAndTerms.lean` 2節](#sec-Intro1.definitions)以来の検査が、そのまま**証明の検査**になっている。
[1節](#sec-CH2.existence)で行った証明項の検査も、すべてこの見方の繰り返しだった。
-/

/-!
### 順序 `Nat.le`

`m ≤ n` も帰納型の記法で、こちらは構成子が2つある:

    inductive Nat.le (n : Nat) : Nat → Prop
      | refl : Nat.le n n
      | step {m} : Nat.le n m → Nat.le n (succ m)   -- `succ m` は `m + 1`

作り方は「`n ≤ n`」と「`n ≤ m` が作れているなら `n ≤ m + 1` も作れる」の2通り。
つまり `≤` の証明は、`refl` から出発して `step` を必要な回数だけ重ねた項である。
`zero` に `succ` を重ねて自然数を作るのと、まったく同じ手つきで証明が作れる。
-/

example : 0 ≤ 0 := Nat.le.refl
example : 0 ≤ 1 := Nat.le.step Nat.le.refl
example : 0 ≤ 2 := Nat.le.step (Nat.le.step Nat.le.refl)

/-!
`0 ≤ 2` を証明するとは、帰納型 `Nat.le` の
項を構成子から組み立てることに他ならず、出来上がった証明は
データと同じ資格でそこにある。`∧` `∨` `∃` `False` も同様に帰納型として
定義された命題であり（[2](#sec-CH.products)〜[4節](#sec-CH.empty-types)、[1節](#sec-CH.dependent-sums)）、示すときに使った `⟨_, _⟩` や `.inl` は、
それらの構成子だったのである。

### 等式の法則は公理ではない

ふつうの述語論理では、等式の反射律や代入原理は論理に組み込まれた**公理**である。
Lean では違う。いま見たとおり `Eq` はただの帰納型の宣言で、
等式に期待される振る舞いは、そこから実際に出てくる:

* 反射律は構成子 `refl` そのもの
* 代入原理（`a = b` なら、`P a` の証明から `P b` の証明が得られる）は、
  帰納型の宣言を受理したときに Lean が自動生成する**帰納法原理** `Eq.rec` そのもの
* 対称律・推移律・合同性は、そこから証明される**定理**
-/

#print axioms Eq.symm

/-!
    'Eq.symm' does not depend on any axioms

「公理に一切依存していない」という報告——対称律は、帰納型の仕組みだけから
**証明された**定理である。
-/

/-!
つまり Lean の基礎にあるのは等式の公理のリストではなく、
「（健全性の条件を満たす）帰納型の宣言に対して、構成子・帰納法原理・計算規則を
与える」という一般規則のほうである。等式に限らず、この教材に出てくる
`∧` `∨` `∃` `=` `≤` の論理法則はすべて、依存関数型・宇宙・帰納型という
土台から**定義と定理として**出てくる。

例外として土台の外から公理を足すこともあるが、この教材の
主定理が実際に依存するのは、外延性・選択・商型の健全性にあたる3つだけである。
それは `06_Topology.lean` の末尾で `#print axioms` により確認する。

### 「全部」と「別々」も出てくる

[`03_InductiveTypes.lean` 1節](#sec-Intro1.inductive-types)で、帰納型の宣言は2つのことを保証すると述べた:
構成子で作られたものが項の**全部**であること、そして違う作り方をした項は
**別々**であることである。この2つも公理ではなく、同じ一般規則から出てくる。

「全部」の保証の正体は、自動生成される帰納法原理そのものである。
`rec` は「各構成子の場合を与えれば、すべての項について定義・証明したことになる」
と言っており、`match` の場合分けがそれで尽くせるのはこれによる。
-/

#check @Signal.rec

/-!
    @Signal.rec : {motive : Signal → Sort u_1} →
      motive Signal.red → motive Signal.yellow → motive Signal.green → (t : Signal) → motive t

`motive` を命題の族 `P : Signal → Prop` として読むと、三つの色での証明から
`∀ t : Signal, P t` の証明を返す型になっている。
どの色を受け取っても、その色についての証明を返せることが「全部」を表している。
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 対称に見えて `rfl` が通らない `0 * n`

`02_Forall.lean` の `all_mul_zero` と同じ調子で `∀ n, IsZero (0 * n)` も書きたくなるが、こちらは通らない:

    theorem all_zero_mul : ∀ n : Nat, IsZero (0 * n) := fun n => rfl

    error: Type mismatch
      rfl
    has type
      ?m.10 = ?m.10
    but is expected to have type
      IsZero (0 * n)

理由は `*` の定義が**第2引数についての再帰**であること。`n * 0` は
第2引数が `0` なので計算が1歩で進むが、`0 * n` は第2引数が**変数のまま**
なので計算が止まり、`0 * n` と `0` は「計算で一致」しない。
数学では対称に見える2つの式が、定義のレベルでは非対称なのである
（下の練習の `0 * 5` が通るのは、`5` が具体的な数字で計算が最後まで走るから）。

変数 `n` のまま示すには `n` についての**数学的帰納法**が要る。Lean では
帰納法は再帰で書く——実物は `06_Topology.lean` の `mem_interFin` などで見る。
ライブラリではこの命題（の中身）は `Nat.zero_mul` として証明済みである。
-/

/-!
### ✏ 練習

1. `example : IsZero (0 * 5) := rfl` が通ることを確かめよ。
   `IsZero (5 * 0)` は `rfl` と `all_mul_zero 5` の両方で証明できるか。
-/

/-!
CALLOUT_END
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 定義的等しさと、等しいことの証明

型を照合するとき、Lean は書かれた文字列が一致するかだけを見ているのではない。
定義の展開や計算などによって同一視できる項を、**定義的に等しい**という
（definitional equality、略して defeq）。
`rfl` が等式の証明として使えるのは、その両辺が定義的に等しいと照合できるときである。

定義的に等しいことと、等式の証明を別に与えて等しさを示せることは区別しよう。
例えば、次の2つの等式は、どちらも任意の自然数について成り立つ。
しかし、`rfl` がそのまま使えるのは1つ目である:
-/

example (n : Nat) : n + 0 = n := rfl

/-!
自然数の加算は第2引数について再帰的に定義されている。
第2引数が `0` なら計算できるので、`n + 0` と `n` は定義的に等しい。
一方、`0 + n` は第2引数 `n` がまだ決まっていないため、この計算では `n` まで進まない。
したがって、次の証明の右辺を `rfl` に変えるとエラーになる。
ここではライブラリの定理 `Nat.zero_add n` を使えば証明できる:
-/

example (n : Nat) : 0 + n = n := Nat.zero_add n

/-!
つまり、**`rfl` が使えないことは、その命題が偽であることを意味しない**。
`0 + n = n` のように、定義的には一致しなくても証明できる等式がある。

また、「計算で一致する」は定義的等しさの入口の説明であり、規則のすべてではない。
例えば関数 `fun x => f x` と `f` の同一視や、[`02_Forall.lean` の0節](#sec-CH.propositions)の証明無関連性も含まれる。
後者は、同じ命題の2つの証明の等しさが `rfl` で示せることに現れる:
-/

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl

/-!
ここでは `P` 自体を証明したのではない。`P` の2つの証明を仮定し、
その2つが同一視されることを確かめたのである。
-/

/-!
CALLOUT_END
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 構成子が別々であることと `noConfusion`

「別々」には、これも宣言の受理時に自動生成される道具 `noConfusion` が使える。
「違う構成子どうしは等しくない」と「同じ構成子なら中身まで等しい
（構成子は単射）」の両方がこれで証明できる。実物を `Bool` と `Nat` で見る
（`a ≠ b` は `¬(a = b)` の記法。初出である）:
-/

example : true ≠ false := fun h => Bool.noConfusion h

example {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.noConfusion h (fun h' => h')

#print axioms Bool.noConfusion

/-!
    'Bool.noConfusion' does not depend on any axioms

`noConfusion` 自体も公理には依存していない——帰納型の仕組みから
**証明された**定理である。種明かしだけ述べると、「構成子を `match` で見分けて
`True`／`False` を割り当てる述語」を作り、`Eq.rec`（代入原理）で
`true = false` の仮定からゴール `False` へ運ぶ——どれも既出の道具である。
-/

/-!
CALLOUT_END
-/

/-!
CALLOUT_START optional
-/

/-!
### 補足: 等式をもう1つ作る実験

`Eq` が特別な組み込みでないことは、実際に作り直してみるとよく分かる。
同じ形の帰納型 `MyEq` を宣言すると、帰納法原理も同じ形で自動生成される。
-/

inductive MyEq {α : Type} (a : α) : α → Prop where
  | refl : MyEq a a

#check MyEq

/-!
    MyEq {α : Type} (a : α) : α → Prop
-/

/--
対称律は場合分け（`match`）だけで導ける。構成子は `refl` の1つ、つまり
`a` と `b` が同じ場合しかないので、返すべきものも `refl` で足りる。
推移律や代入原理も同様である。
-/

theorem MyEq.symm {α : Type} {a b : α} (h : MyEq a b) : MyEq b a :=
  match h with
  | .refl => .refl

#check MyEq.symm

/-!
    MyEq.symm {α : Type} {a b : α} (h : MyEq a b) : MyEq b a
-/

/-!
#### なぜこの `match` が通るのか——添字の単一化

（ここはこの補足の中でも特に細かい話である。飛ばして、次の `example` へ
進んでよい。）

上の証明をよく見ると、不思議なことが起きている。ゴールは `MyEq b a` なのに、
返しているのは `.refl`——その型は `MyEq a a` であって、`a` と `b` は
別の変数のはずである。なぜ型が合うのか。

鍵は、`MyEq` の宣言のコロンの**左右**の違いにある。`(a : α)` は
**パラメータ**（どの構成子でも共通・固定）、コロンの右の `α → Prop` の引数は
**添字**（構成子ごとに値を決められる）である。`MyEq a` は「各 `b` に命題
`MyEq a b` を割り当てる族」だが、唯一の構成子 `refl` は、この族のうち
**対角線 `MyEq a a` にしか項を作らない**。

ここで [`03_InductiveTypes.lean` 1節](#sec-Intro1.inductive-types)の原則——帰納型の項は、構成子で作られたものが
すべて——を当てはめる。手元には `h : MyEq a b` という項がある。項はすべて
構成子から作られ、構成子は `refl` だけで、`refl` が作る項の型は `MyEq a a`。
したがって、**`MyEq a b` に項があるということ自体が、`b` は実は `a` だったことを
意味する**。

添字つきの型への `match` は、この推論を実行している。枝に入るとき、
「どの構成子か」の列挙（`Signal` のときと同じ仕事）に加えて、「その構成子で
作られたのなら**添字は何でなければならないか**」の照合（単一化）が走る。
`refl` の枝の中では `b := a` と特殊化された世界になり、ゴール `MyEq b a` は
`MyEq a a` に書き換わる——だから右辺の `.refl` が受理される。

このことはコンパイル結果に現れる:
-/

#print MyEq.symm

/-!
    theorem MyEq.symm : ∀ {α : Type} {a b : α}, MyEq a b → MyEq b a :=
    fun {α} {a b} h ↦
      match b, h with
      | .(a), MyEq.refl => MyEq.refl

内部では **`b` も一緒にマッチされて**いて、そのパターンが `.(a)` になっている。
この `.( )` は**強制パターン**——「ここは自由な場合分けではない。`h` が `refl`
である以上、`a` であることが強制されている」という印である。

正体まで降りると、これは自動生成された帰納法原理の仕事である:
-/

#check @MyEq.rec

/-!
    @MyEq.rec : {α : Type} →
      {a : α} → {motive : (a_1 : α) → MyEq a a_1 → Sort u_1} → motive a ⋯ → {a_1 : α} → (t : MyEq a a_1) → motive a_1 t

読み: 「すべての添字 `a_1` と `t : MyEq a a_1` について `motive a_1 t`」を
結論するのに、要求される義務は **`refl` の場合の `motive a ⋯` ただ1つ**である。
「`refl` の場合だけ示せばよい」という形の中に、「そのとき添字は `a`」が
すでに織り込まれている。`match` を使わず、この帰納法原理を直接使っても書ける:
-/

theorem MyEq.symm' {α : Type} {a b : α} (h : MyEq a b) : MyEq b a :=
  MyEq.rec (motive := fun c _ => MyEq c a) MyEq.refl h

/-!
まとめると: `Signal` の `match` は場合の列挙だけだったが、添字つきの族への
`match` は枝ごとに**添字の情報が増える**（依存パターンマッチと呼ばれる）。
「等式で場合分けすると、両辺を同じものとして扱えるようになる」——これこそが
`Eq` の帰納法原理 `Eq.rec`（代入原理）の中身であり、[`06_Topology.lean` 1節](#sec-Top.tactics)で見る `rw` が
裏でやっていることの正体でもある。
-/

/--
型検査が両辺を計算してから比べる仕組みも `Eq` 専用ではないので、
`1 + 1 = 2` に当たる命題はやはり構成子だけで証明できる。
-/

example : MyEq (1 + 1) 2 := .refl

/-!
しかも、`Eq` と同値であることを系の中で証明できる。
`p ↔ q`（同値、`\iff` と打つ）はここが初出だが、これも「`p → q` の証明と
`q → p` の証明の組」という2フィールドの structure にすぎず、
`⟨→の証明, ←の証明⟩` で作れる。
両方向とも「相手の等式で場合分けして、自分の構成子を置く」だけである。
なお2つ目の `match h with | rfl => …` の `rfl` は、証明項ではなく**パターン**の
位置にある——「`Eq` の唯一の構成子 `Eq.refl` の場合」を表す書き方である。
-/

theorem myEq_iff_eq {α : Type} {a b : α} : MyEq a b ↔ a = b :=
  ⟨fun h => match h with | .refl => rfl,
   fun h => match h with | rfl => .refl⟩

#check myEq_iff_eq

/-!
    myEq_iff_eq {α : Type} {a b : α} : MyEq a b ↔ a = b
-/

/--
`propext : (p ↔ q) → p = q`（命題の外延性。`06_Topology.lean` の3公理の1つ）まで
使えば、同値であるにとどまらず、命題として**等しい**ことになる。
-/

example {α : Type} {a b : α} : MyEq a b = (a = b) := propext myEq_iff_eq

/-!
つまり2つ目の等式を作っても、衝突も分裂も起きず、同じものが増えるだけである。
実際 `h : MyEq a b` を「`a = b` が証明できた」と解釈しても問題ない——
上で示した同値 `myEq_iff_eq` が、その読み替えの正当化である。
`Eq` に残る特別さは論理の側にはなく、道具立ての側にある:
`=` という記法や、`rw`・`simp` などのタクティク（[`06_Topology.lean` 1節](#sec-Top.tactics)で登場する、証明の
もう1つの書き方の道具）は `Eq` に向けて作られているので、
`MyEq` では使えない。例えば `h : MyEq a b` で `rw [h]` とすると

    error: Invalid rewrite argument: Expected an equality or iff proof
    or definition name, but `h` is a proof of
      MyEq a b

と断られる。逆に言えば、それだけの違いしかない。
-/

/-!
CALLOUT_END
-/

/-!
### ✏ 練習

1. `example : 1 ≤ 3` を `Nat.le` の構成子**だけ**で書け（`step` は何回要るか）。
-/

/-! CALLOUT_START optional -/
/-!
### ✏ 練習

2. （補足の確認）本文の `MyEq.symm` にならって、`MyEq.trans` を自分で証明せよ
   （`h₂` を `match` で分ければ `h₁` がそのまま答えになる）。
3. （補足の確認）逆向きの橋 `theorem MyEq.ofEq {α : Type} {a b : α} (h : a = b) : MyEq a b` を
   `match` で書け（今度は `Eq` の側で場合分けして、`MyEq` の構成子を置く）。
-/
/-! CALLOUT_END -/

/-!
## 7. 示すときと使うときのまとめ {#sec-CH.introduction-elimination}

ここまでの例で使った頭の動きを並べると、次のようになる。

| 頭の動き | 項での正体 |
|---|---|
| 全称を示す: 任意に取る | `fun n => …` |
| ならばを示す: 仮定を取る | `fun h => …`（引数） |
| 全称・ならばを使う: 当てはめる | 適用 `hg h` |
| 存在を示す: 証人+根拠 | `⟨w, h⟩` |
| 存在を使う: 取り出して名付ける | `match` のパターン分解 |

| 頭の動き | 項での正体 |
|---|---|
| 定義に戻る | （書かない——型検査器が展開する） |
| 既知の定理を使う | 名前への適用 |
| 等式の連鎖 | `congrArg`・`.trans` |
| 計算で決着 | `rfl` |
| 「∎」 | 型検査が通ること |

主張を Lean の命題として定め、証明の筋道も与えられたあとなら、散文から項へ
進む仕事の多くは、省略されていた引数や中間項を明示することである。各段の
「文脈にあるか」「入力の型が合うか」「結果が目標の型か」という照合は、
**項の型検査**にそのまま写る。

もちろん、数学の主張にふさわしい定義を選ぶことや、証明を発見することまで
型検査が代わってくれるわけではない。ここで分かったのは、主張と証明項が
与えられたあと、その証明項が本当に主張の型を持つかは、局所的な規則を
積み重ねて機械的に検査できる、ということである。冒頭の主張——命題そのものを
型とみなし、その型の項を作ることが証明することである——も、もう奇妙には
響かないはずである。


示すときの形と使うときの形を並べると、左右で同じ形をしていることが見える。

| | 型 | 命題 | 示すとき | 使うとき |
|---|---|---|---|---|
| 関数 | `α → β` | `p → q` | `fun x => e` | `f a` |
| 積 | `α × β` | `p ∧ q` | `⟨a, b⟩` | 成分名で取り出す |
| 和 | `α ⊕ β` | `p ∨ q` | `.inl` / `.inr` | `match` で場合分け |
| 空 | `Empty` | `False` | なし | `.elim` |
| 依存積 | `(a : α) → P a` | `∀ a, Q a` | `fun x => e` | `f a` |
| 依存和 | `(a : α) × P a` | `∃ a, Q a` | `⟨a, b⟩` | `.fst` / `.snd`（`∃` は `match` のみ——[9節](#sec-CH.prop-elimination)） |

示すときの列は「その型（命題）を作るのに何が要るか」、
使うときの列は「その型（命題）を持っているとき何が言えるか」。
上の例で見たとおり、対応する両側は多くの場合まったく同じ字面で書ける。

字面が同じになるのは偶然ではない。証明を書くときにしていることは、
関数を書き、組を作り、場合分けをすること——つまり項の構成そのものである。
「命題 `p` を証明する」とは「`p` を型とみなして、その項を1つ作る」ことであり、
この対応が Curry–Howard 対応と呼ばれるものである。
-/

/--
型側と命題側で同じ項が通ることの確認。
`match` で二つを取り出して逆順に組み直す同じ式が、片方では組の入れ替え、
もう片方では「かつ」の入れ替えの証明になっている。
-/

example {α β : Type} : α × β → β × α := fun x =>
  match x with
  | ⟨a, b⟩ => ⟨b, a⟩

example {p q : Prop} : p ∧ q → q ∧ p := fun x =>
  match x with
  | ⟨a, b⟩ => ⟨b, a⟩

/-!
### ✏ 練習

1. 対照表を見ながら、`theorem andToOr {p q : Prop} : p ∧ q → p ∨ q` の証明項を書け
   （`∧` から取り出し、`∨` を示す形に包む——1行で書ける）。
-/

/-! CALLOUT_START optional -/

/-!
## 8. 補足: 証明検査 — エラボレータとカーネル {#sec-CH2.checking-details}

ソースコードから証明の検査までは二段階ある。
エラボレータは記法を展開し、暗黙引数や型の情報を補って項を組み立てる。
カーネルは、その項が指定された型を持つかを検査する。

例えば `Nat.sub_add_cancel` は、自然数の引き算で引く数が大きすぎないという仮定を要する。
`n - 1 + 1 = n` を全自然数で示そうとして仮定を省略すると、その穴が残る:

    example : ∀ n : Nat, n - 1 + 1 = n := fun n => Nat.sub_add_cancel _

    error: don't know how to synthesize placeholder for argument `h`
    context:
    n : Nat
    ⊢ 1 ≤ n

この例では `n = 0` が反例なので、穴は埋められない。
省略を補って項を完成させることと、完成した項を検査することの役割を区別しよう。
また、検査するのは書かれた命題についての証明であり、その命題が意図した数学を表すかは別の確認が要る。

### ✏ 練習

1. `#check @Nat.add_sub_cancel` で型を確かめ、
   `example : ∀ n : Nat, n + 1 - 1 = n` をこの定理で証明せよ。
2. `#eval (3 : Nat) - 5` の値を予想してから確かめよ。
-/

/-! CALLOUT_END -/
/-! CALLOUT_START optional -/

/-!
## 9. 補足: データの組と存在の証明の違い {#sec-CH.prop-elimination}

依存和の項はデータなので、成分を名前で取り出せる。
-/

def sigmaFst {α : Type} {P : α → Type} (s : (a : α) × P a) : α := s.fst

def sigmaSnd {α : Type} {P : α → Type} (s : (a : α) × P a) : P s.fst := s.snd

/-!
一方、存在命題の証明は、その証人を計算用の値として取り出すためのデータではない。
同じ命題の証明を区別しないという性質と整合するよう、`Exists` の証明を分解した結果は命題に限られる。

    def existsFst {α : Type} {Q : α → Prop} (h : ∃ a, Q a) : α :=
      match h with
      | ⟨a, _⟩ => a

これは受理されない。結論が命題ならば、本文と同じく証人と根拠を使って証明できる:
-/

theorem existsElim {α : Type} {r : Prop} {Q : α → Prop}
    (h : ∃ a, Q a) (hr : ∀ a, Q a → r) : r :=
  match h with
  | ⟨a, ha⟩ => hr a ha

/-!
「または」も、命題を示すために場合分けして使える。
-/

theorem orElimToProp {p q r : Prop} (h : p ∨ q) (f : p → r) (g : q → r) : r :=
  h.elim f g

/-!
なお、`False` や `Eq` には命題以外への除去も許される。
`False.elim` や等式によるデータの書き換えは、その例である。

### ✏ 練習

1. 上の `existsFst` を試し、エラーメッセージを確かめよ。
-/

/-! CALLOUT_END -/

/-!
これで、型と命題の対応を使い、証明を項として読む道具がそろった。
`06_Topology.lean` では、証明を命令の列で書くタクティクも使いながら、数学の理論を記述する。
紹介は[`06_Topology.lean` 1節](#sec-Top.tactics)で行う。
-/
