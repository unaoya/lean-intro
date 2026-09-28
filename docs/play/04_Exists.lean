-- はじめての Lean — 04_Exists（ブラウザ版・自動生成）
-- 書き換えた内容は、このページの URL に入っています。残したいときは URL をブックマークするか、
-- コードをコピーして保存してください。元に戻すときは、テキストのリンクから開き直します。

-- # 型と命題 II — かつ・または・否定・存在量化

-- ## 1. 存在の証明と全射の合成

def exists_eq_two : ∃ n : Nat, n = 2 := Exists.intro 2 rfl

-- ### 任意の自然数の二倍は偶数

def IsEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

def even_two_mul : ∀ n : Nat, IsEven (2 * n) :=
  fun n => Exists.intro n rfl

-- ### n + n の場合に必要な等式

#check Nat.two_mul

def even_double : ∀ n : Nat, IsEven (n + n) :=
  fun n => Exists.intro n (Eq.symm (Nat.two_mul n))

-- ### 二つの存在を使って、結論の存在を作る

def comp_surjective (A B C : Type) (f : A → B) (g : B → C)
    (hf : ∀ b : B, ∃ a : A, f a = b)
    (hg : ∀ c : C, ∃ b : B, g b = c) :
    ∀ c : C, ∃ a : A, g (f a) = c :=
  fun c =>
    match hg c with
    | Exists.intro b hb =>
      match hf b with
      | Exists.intro a ha =>
        Exists.intro a (Eq.trans (congrArg g ha) hb)

-- ### 全称量化と存在量化の二つの向き

/- ✏ 練習
50. f:A→ B が右逆 g:B→ A を持つ、すなわち `hfg : ∀ b : B, f (g b) = b` があるとする。
   `∀ b : B, ∃ a : A, f a = b` を証明する関数 `surjectiveOfRightInverse` を書け。証人には何を選ぶか。
-/

-- ### 等式の連鎖を項で書く

#check Nat.mul_add

-- ### 偶数の和の証明を完成させる

def isEven_add {n m : Nat} (hn : IsEven n) (hm : IsEven m) : IsEven (n + m) :=
  match hn with
  | Exists.intro k hk =>
    match hm with
    | Exists.intro l hl =>
      Exists.intro (k + l)
        (Eq.trans
          (Eq.trans (congrArg (fun x => x + m) hk)
            (congrArg (fun x => 2 * k + x) hl))
          (Eq.symm (Nat.mul_add 2 k l)))

/- ✏ 練習
51. 任意の自然数 `n` について、`IsEven n → IsEven (n + 2)` を証明せよ。
   `2` の偶数性を `Exists.intro` で示し、本文の `isEven_add` を使うこと。
-/

-- ## 2. かつ — 全単射の合成

def IsBijective (A B : Type) (f : A → B) : Prop :=
  (∀ x y : A, f x = f y → x = y) ∧ (∀ b : B, ∃ a : A, f a = b)

-- ### 全単射の合成の証明項

def comp_bijective (A B C : Type) (f : A → B) (g : B → C)
    (hf : IsBijective A B f) (hg : IsBijective B C g) :
    IsBijective A C (fun x => g (f x)) :=
  match hf with
  | And.intro hfi hfs =>
    match hg with
    | And.intro hgi hgs =>
      And.intro (fun x y h => hfi x y (hgi (f x) (f y) h))
        (comp_surjective A B C f g hfs hgs)

/- ✏ 練習
52. `f : A → B`、`g : A → C` と `b : B`、`c : C` に対して、
   `∃ a : A, f a = b ∧ g a = c` から `∃ a : A, f a = b` を証明せよ。
   二種類の構成子を `match` で使い、必要な根拠だけを取り出すこと。
-/

-- ## 3. または — 二つの場合を扱う

-- ### またはの証明を match で使う

def imageTwoPoints (A B : Type) (f : A → B) (x a b : A)
    (h : x = a ∨ x = b) : f x = f a ∨ f x = f b :=
  match h with
  | Or.inl hxa => Or.inl (congrArg f hxa)
  | Or.inr hxb => Or.inr (congrArg f hxb)

/- ✏ 練習
53. f:A→ B を単射とする。`f x = f a ∨ f x = f b` から `x = a ∨ x = b` を示せ。
   単射性の証明を `hf : ∀ x y : A, f x = f y → x = y` として受け取ること。
-/

-- ## 4. 否定 — 等しいと仮定して矛盾を作る

-- ### 単射性と否定を組み合わせる

def injectivePreservesNe (A B : Type) (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y)
    (x y : A) (hne : x ≠ y) : f x ≠ f y :=
  fun h => hne (hf x y h)

/- ✏ 練習
54. 任意の写像 f:A→ B について、`f x ≠ f y` ならば `x ≠ y` であることを示せ。
   単射性は仮定しない。`x = y` と仮定したとき、`congrArg` で何が得られるか考えよ。
-/

-- ### 帰納型の異なる構成子

def bool_true_ne_false_by_noConfusion : Bool.true ≠ Bool.false :=
  fun h => Bool.noConfusion h

-- ### 補足: 構成子が別々であることと noConfusion

def succ_injective_by_noConfusion {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.noConfusion h (fun h' => h')

#print axioms Bool.noConfusion

-- （補足・先取りここまで）

-- ## 5. 証明を作る・証明を使う

-- ## 6. 型検査が証明の検査になる

#print axioms comp_surjective

-- ### 省略を補う処理と、完成した項の検査

#check Nat.sub_add_cancel

-- 本文の例（コメントアウトしてある。名前が重なるものもある）:
-- def sub_one_add_one : ∀ n : Nat, n - 1 + 1 = n :=
--   fun n => Nat.sub_add_cancel _

def sub_one_add_one (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := Nat.sub_add_cancel h

/- 7. ✏ 練習 — 章末問題
数学の証明を書き、仮定と結論の型を確かめてから、Leanの項にしよう。

55. 三つの全射 f:A→ B、g:B→ C、k:C→ D の合成が全射であることを証明せよ。
   本文の `comp_surjective` を二回使う解答を書け。各適用に渡す型と写像を明示すること。
-/
