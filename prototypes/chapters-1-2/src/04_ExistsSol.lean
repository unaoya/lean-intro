import «04_Exists»

/-! SOL Trial4.existence:1 -/

def surjectiveOfRightInverse (A B : Type) (f : A → B) (g : B → A)
    (hfg : ∀ b : B, f (g b) = b) :
    ∀ b : B, ∃ a : A, f a = b :=
  fun b => Exists.intro (g b) (hfg b)
/-!
`b` を受け取り、証人に `g b` を選ぶ。
その根拠に要求される型は `f (g b) = b` であり、`hfg b` が与える。
-/

/-! SOL Trial4.practice:1 -/

def threeCompSurjective (A B C D : Type)
    (f : A → B) (g : B → C) (k : C → D)
    (hf : ∀ b, ∃ a, f a = b) (hg : ∀ c, ∃ b, g b = c)
    (hk : ∀ d, ∃ c, k c = d) :
    ∀ d, ∃ a, k (g (f a)) = d :=
  comp_surjective A C D (fun a => g (f a)) k
    (comp_surjective A B C f g hf hg) hk
/-!
内側の適用は `A → C` の全射性、外側の適用は `A → D` の全射性を証明する。
-/

/-! SOL Trial4.practice:2 -/

def existsFirst (A B C : Type) (f : A → B) (g : A → C) (b : B) (c : C)
    (h : ∃ a : A, f a = b ∧ g a = c) : ∃ a : A, f a = b :=
  match h with
  | Exists.intro a habc =>
    match habc with
    | And.intro hab _ => Exists.intro a hab
/-!
証人 `a` はそのまま使い、二つの根拠のうち左側の `hab : f a = b` を渡す。
-/

/-! SOL Trial4.practice:3 -/

def preimageTwoPoints (A B : Type) (f : A → B)
    (hf : ∀ x y : A, f x = f y → x = y) (x a b : A)
    (h : f x = f a ∨ f x = f b) : x = a ∨ x = b :=
  match h with
  | Or.inl hxa => Or.inl (hf x a hxa)
  | Or.inr hxb => Or.inr (hf x b hxb)
/-!
各枝で単射性を適用し、結論の対応する構成子へ証明を渡す。
-/

/-! SOL Trial4.practice:4 -/

def neOfImageNe (A B : Type) (f : A → B) (x y : A)
    (hne : f x ≠ f y) : x ≠ y :=
  fun h => hne (congrArg f h)
/-!
`h : x = y` から `congrArg f h : f x = f y` が得られ、それを `hne` に渡すと `False` が得られる。
-/

/-! SOL Trial4.practice:5 -/

def isEven_add_two : ∀ n : Nat, IsEven n → IsEven (n + 2) :=
  fun _ hn => isEven_add hn (Exists.intro 1 rfl)
/-!
`2 = 2 * 1` は計算で一致するので、証人 `1` と `rfl` で `IsEven 2` が示せる。
偶数の和についての関数に二つの証明を渡せばよい。
-/
