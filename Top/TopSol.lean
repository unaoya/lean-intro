import Top

/-!
`Top.lean` の ✏ 練習の解答。
-/

/-! SOL 1.1 -/

example : (2 : Nat) ∈ ({n | n < 5} : Set Nat) :=
  Nat.le.step (Nat.le.step Nat.le.refl)

/-!
`∈` と `setOf` を展開するとゴールは `2 < 5`、すなわち `2 + 1 ≤ 5`。
`Nat.le.refl : 3 ≤ 3` から `step` を2回で `3 ≤ 5` に届く（`CH.lean` 8節）。
-/

/-! SOL 1.2 -/

#print axioms Set.compl_compl

/-!
    'Set.compl_compl' depends on axioms: [propext, Classical.choice, Quot.sound]

背理法 `Classical.byContradiction` を使ったので、`Classical.choice` への
依存が現れる（`propext`・`Quot.sound` はその道連れ）。
-/

/-! SOL 2.1 -/

example : Function.Bijective (fun n : Nat => n) :=
  ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩

/-!
単射性: 仮定 `h : a₁ = a₂` がそのままゴール（恒等写像なので送り先の等式＝
元の等式）。先頭の `fun _ _` は2点 `a₁ a₂` のぶんの束縛である。
全射性: 点 `b` への証人は `b` 自身、根拠は `rfl`。
-/

/-! SOL 3.1 -/

example : (discrete Nat).IsOpen {n | n = 0} := trivial

/-!
離散位相の `IsOpen` は定義上どの集合でも `True`。証明は構成子 `trivial`。
-/

/-! SOL 4.1 -/

#check @Continuous

/-!
    @Continuous : {X : Type} → [TopologicalSpace X] → {Y : Type} → [TopologicalSpace Y] → (X → Y) → Prop

`@` 付きの表示では、暗黙引数も含めた引数の列が `→` でつながった
1本の関数型として見える。2つの空間の位相は、どちらも角括弧
`[TopologicalSpace X]`・`[TopologicalSpace Y]`——インスタンス引数——で並ぶ。
-/

/-! SOL 7.1 -/

#print axioms Set.subset_preimage_iUnion

/-!
    'Set.subset_preimage_iUnion' does not depend on any axioms

包含の付け替えだけの証明なので、公理は1つも要らない。
-/

/-! SOL 10.1 -/

#print axioms isOpen_empty

/-!
    'isOpen_empty' depends on axioms: [propext, Quot.sound]

`Set.ext`（中身は `funext` と `propext`）の使用で `propext` と
`Quot.sound`（`funext` の道連れ）が入るが、`Classical.choice` は入らない——
背理法なしの証明だったことが、ここからも確認できる。
-/

/-! SOL 10.2 -/

example : TopologicalSpace Bool := discrete Bool

/-!
`discrete` は「型を受け取って位相そのものを返す関数」なので、
`Bool` に適用するだけで項が得られる。
-/

/-! SOL 10.3 -/

/-!
角括弧（インスタンス引数）で現れる:

    IsCompact.isClosed {Y : Type} [TopologicalSpace Y] [Hausdorff Y] {K : Set Y} (hK : IsCompact K) : IsClosed K

「空間がハウスドルフ」は `[Hausdorff Y]`。位相と同じく空間に常置される
性質なので、登録簿から自動で供給される形になっている。波括弧は型や集合の
暗黙引数、丸括弧は明示的に渡す証明 `hK` である。
-/
