-- 受講者用ファイル（解説は HTML 版で読む）。tools/student.py が src/ から自動生成する。
-- 手で編集しないこと。

import «06_Topology»

-- # 発展演習: Ascoli の定理（ブルバキ流）

-- ## Part A: 一様構造

namespace Set

variable {α : Type}

theorem subset_antisymm {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  ext fun a => ⟨h₁ a, h₂ a⟩

def compRel (V W : Set (α × α)) : Set (α × α) := {p | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W}

def swapRel (V : Set (α × α)) : Set (α × α) := {p | (p.2, p.1) ∈ V}

theorem finite_of_list (L : List α) : Set.Finite {a | a ∈ L} :=
  ⟨L.length, L.get, fun _ ha => List.get_of_mem ha⟩

theorem Finite.exists_list {s : Set α} (hs : s.Finite) : ∃ L : List α, ∀ a ∈ s, a ∈ L :=
  have ⟨_, f, hf⟩ := hs
  ⟨List.ofFn f, fun a ha => List.mem_ofFn.mpr (hf a ha)⟩

end Set

class UniformSpace (α : Type) where
  /-- 近縁の全体。 -/
  Entourage : Set (Set (α × α))
  /-- 全体の関係は近縁。 -/
  univ_mem : Set.univ ∈ Entourage
  /-- 近縁より大きい関係は近縁。 -/
  mono : ∀ {V W : Set (α × α)}, V ∈ Entourage → V ⊆ W → W ∈ Entourage
  /-- 2つの近縁の共通部分は近縁。 -/
  inter_mem : ∀ {V W : Set (α × α)}, V ∈ Entourage → W ∈ Entourage → V ∩ W ∈ Entourage
  /-- 近縁は対角線を含む。 -/
  refl : ∀ {V : Set (α × α)}, V ∈ Entourage → ∀ a, (a, a) ∈ V
  /-- 近縁の逆関係は近縁。 -/
  symm : ∀ {V : Set (α × α)}, V ∈ Entourage → Set.swapRel V ∈ Entourage
  /-- 「半分」の近縁がある。 -/
  comp : ∀ {V : Set (α × α)}, V ∈ Entourage → ∃ W, W ∈ Entourage ∧ Set.compRel W W ⊆ V

notation "𝓤 " α:max => @UniformSpace.Entourage α _

namespace UniformSpace

variable {α : Type} [UniformSpace α]

theorem exists_half {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c, (a, b) ∈ W → (b, c) ∈ W → (a, c) ∈ V :=
  sorry

theorem exists_third {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c d, (a, b) ∈ W → (b, c) ∈ W → (c, d) ∈ W → (a, d) ∈ V :=
  sorry

instance toTopologicalSpace : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, ∃ V ∈ 𝓤 α, ∀ b, (a, b) ∈ V → b ∈ s
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

theorem exists_open_ball {V : Set (α × α)} (hV : V ∈ 𝓤 α) (a : α) :
    ∃ O : Set α, IsOpen O ∧ a ∈ O ∧ ∀ b ∈ O, (a, b) ∈ V :=
  sorry

end UniformSpace

open UniformSpace

-- ## Part B: 一様収束の一様構造と等連続性

section FunctionSpace

variable {X Y : Type} [UniformSpace Y]

def unifRel (V : Set (Y × Y)) : Set ((X → Y) × (X → Y)) := {p | ∀ x, (p.1 x, p.2 x) ∈ V}

instance uniformFun : UniformSpace (X → Y) where
  Entourage := {𝒱 | ∃ V ∈ 𝓤 Y, unifRel V ⊆ 𝒱}
  univ_mem := sorry
  mono := sorry
  inter_mem := sorry
  refl := sorry
  symm := sorry
  comp := sorry

variable [TopologicalSpace X]

def EquicontinuousAt (H : Set (X → Y)) (x : X) : Prop :=
  ∀ V ∈ 𝓤 Y, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ V

def Equicontinuous (H : Set (X → Y)) : Prop := ∀ x, EquicontinuousAt H x

theorem Equicontinuous.mono {H H' : Set (X → Y)} (hH : Equicontinuous H) (h : H' ⊆ H) :
    Equicontinuous H' :=
  sorry

theorem equicontinuous_singleton {f : X → Y} (hf : Continuous f) :
    Equicontinuous {g | g = f} :=
  sorry

-- ## Part C: 核心補題（Théorème 1 の有限版）

theorem Equicontinuous.finite_control [CompactSpace X] {H : Set (X → Y)}
    (hH : Equicontinuous H) {V : Set (Y × Y)} (hV : V ∈ 𝓤 Y) :
    ∃ W ∈ 𝓤 Y, ∃ P : List X, ∀ f ∈ H, ∀ g ∈ H,
      (∀ p ∈ P, (f p, g p) ∈ W) → ∀ x, (f x, g x) ∈ V :=
  sorry

end FunctionSpace

-- ## Part D: 全有界性と主定理

section TotallyBounded

variable {α : Type}

def Small (V : Set (α × α)) (A : Set α) : Prop := ∀ a ∈ A, ∀ b ∈ A, (a, b) ∈ V

def TotallyBounded [UniformSpace α] (s : Set α) : Prop :=
  ∀ V ∈ 𝓤 α, ∃ L : List (Set α), (∀ A ∈ L, Small V A) ∧ ∀ a ∈ s, ∃ A ∈ L, a ∈ A

def List.interCover (L M : List (Set α)) : List (Set α) :=
  L.flatMap fun A => M.map fun B => A ∩ B

theorem List.mem_interCover {L M : List (Set α)} {C : Set α} (h : C ∈ List.interCover L M) :
    ∃ A ∈ L, ∃ B ∈ M, C = A ∩ B := by
  have ⟨A, hA, hC⟩ := List.mem_flatMap.mp h
  have ⟨B, hB, hAB⟩ := List.mem_map.mp hC
  exact ⟨A, hA, B, hB, hAB.symm⟩

theorem List.interCover_covers {s : Set α} {L M : List (Set α)}
    (hL : ∀ a ∈ s, ∃ A ∈ L, a ∈ A) (hM : ∀ a ∈ s, ∃ B ∈ M, a ∈ B) :
    ∀ a ∈ s, ∃ C ∈ List.interCover L M, a ∈ C := by
  intro a ha
  have ⟨A, hA, haA⟩ := hL a ha
  have ⟨B, hB, haB⟩ := hM a ha
  exact ⟨A ∩ B, List.mem_flatMap.mpr ⟨A, hA, List.mem_map_of_mem hB⟩, haA, haB⟩

theorem TotallyBounded.subset [UniformSpace α] {s t : Set α} (hs : TotallyBounded s)
    (h : t ⊆ s) : TotallyBounded t :=
  sorry

variable {X Y : Type} [UniformSpace Y]

theorem finite_points_cover {H : Set (X → Y)}
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) {W : Set (Y × Y)} (hW : W ∈ 𝓤 Y) :
    ∀ P : List X, ∃ C : List (Set (X → Y)),
      (∀ S ∈ C, ∀ f ∈ S, ∀ g ∈ S, ∀ p ∈ P, (f p, g p) ∈ W) ∧ ∀ f ∈ H, ∃ S ∈ C, f ∈ S :=
  sorry

variable [TopologicalSpace X]

theorem ascoli [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) : TotallyBounded H :=
  sorry

end TotallyBounded

-- ## Part E: 反例——等連続性の仮定は外せない

namespace Counterexample

instance : TopologicalSpace (Option Nat) where
  IsOpen s := none ∈ s → ∃ N, ∀ n, N ≤ n → some n ∈ s
  isOpen_univ := fun _ => ⟨0, fun _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht ⟨h₁, h₂⟩
    have ⟨N₁, hN₁⟩ := hs h₁
    have ⟨N₂, hN₂⟩ := ht h₂
    exact ⟨N₁ + N₂, fun n hn =>
      ⟨hN₁ n (Nat.le_trans (Nat.le_add_right N₁ N₂) hn),
       hN₂ n (Nat.le_trans (Nat.le_add_left N₂ N₁) hn)⟩⟩
  isOpen_sUnion := by
    intro S hS ⟨s, hsS, hs⟩
    have ⟨N, hN⟩ := hS s hsS hs
    exact ⟨N, fun n hn => ⟨s, hsS, hN n hn⟩⟩

instance : CompactSpace (Option Nat) where
  isCompact_univ := sorry

def diagonal (α : Type) : Set (α × α) := {p | p.1 = p.2}

@[reducible] def discreteUniformity (α : Type) : UniformSpace α where
  Entourage := {V | ∀ a, (a, a) ∈ V}
  univ_mem := fun _ => trivial
  mono := fun hV h a => h _ (hV a)
  inter_mem := fun hV hW a => ⟨hV a, hW a⟩
  refl := fun hV => hV
  symm := fun hV a => hV a
  comp := fun hV =>
    ⟨diagonal α, fun _ => rfl, fun ⟨a, b⟩ ⟨z, (h₁ : a = z), (h₂ : z = b)⟩ => by
      rw [← h₂, ← h₁]
      exact hV a⟩

instance : UniformSpace Bool := discreteUniformity Bool

def δ (n : Nat) : Option Nat → Bool
  | none => false
  | some m => decide (m = n)

def H : Set (Option Nat → Bool) := {f | ∃ n, f = δ n}

theorem totallyBounded_bool (s : Set Bool) : TotallyBounded s :=
  sorry

theorem not_equicontinuousAt : ¬ EquicontinuousAt H none :=
  sorry

theorem exists_avoid (L : List (Set (Option Nat → Bool)))
    (hL : ∀ A ∈ L, Small (unifRel (diagonal Bool)) A) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ A ∈ L, δ n ∉ A :=
  sorry

theorem not_totallyBounded : ¬ TotallyBounded H :=
  sorry

end Counterexample

-- ## Part F: 逆向き——全有界なら等連続

section Converse

variable {X Y : Type} [UniformSpace Y]

theorem TotallyBounded.eval {H : Set (X → Y)} (hH : TotallyBounded H) (x : X) :
    TotallyBounded ((fun f => f x) '' H) :=
  sorry

variable [TopologicalSpace X]

theorem TotallyBounded.equicontinuous {H : Set (X → Y)} (hc : ∀ f ∈ H, Continuous f)
    (hH : TotallyBounded H) : Equicontinuous H :=
  sorry

end Converse

-- ## Part G: フィルターと Zorn の補題

structure Filter (α : Type) where
  /-- 属する集合の全体。 -/
  sets : Set (Set α)
  /-- 全体集合は属する。 -/
  univ_mem : Set.univ ∈ sets
  /-- 属する集合より大きい集合は属する。 -/
  mono : ∀ {s t : Set α}, s ∈ sets → s ⊆ t → t ∈ sets
  /-- 2つの共通部分も属する。 -/
  inter_mem : ∀ {s t : Set α}, s ∈ sets → t ∈ sets → s ∩ t ∈ sets

namespace Filter

variable {α β : Type}

instance : Membership (Set α) (Filter α) := ⟨fun F s => s ∈ F.sets⟩

structure IsUltra (F : Filter α) : Prop where
  /-- 空集合は属さない。 -/
  empty_not_mem : (∅ : Set α) ∉ F
  /-- どの集合も、それ自身か補集合が属する。 -/
  mem_or_compl_mem : ∀ s : Set α, s ∈ F ∨ sᶜ ∈ F

theorem IsUltra.compl_mem {F : Filter α} (hF : F.IsUltra) {s : Set α} (hs : s ∉ F) : sᶜ ∈ F :=
  (hF.mem_or_compl_mem s).resolve_left hs

theorem nonempty_of_mem {F : Filter α} (hF : (∅ : Set α) ∉ F) {s : Set α} (hs : s ∈ F) :
    ∃ a, a ∈ s :=
  Classical.byContradiction fun h => hF (F.mono hs fun a ha => h ⟨a, ha⟩)

def map (f : α → β) (F : Filter α) : Filter β where
  sets := {s | f ⁻¹' s ∈ F}
  univ_mem := F.univ_mem
  mono := fun hs h => F.mono hs fun a ha => h (f a) ha
  inter_mem := fun hs ht => F.inter_mem hs ht

theorem IsUltra.map {F : Filter α} (hF : F.IsUltra) (f : α → β) : (F.map f).IsUltra :=
  sorry

theorem mem_list_inter (F : Filter α) {I : Type} (s : I → Set α) :
    ∀ L : List I, (∀ i ∈ L, s i ∈ F) → {a | ∀ i ∈ L, a ∈ s i} ∈ F :=
  sorry

end Filter

-- ### Zorn の補題（包含順序の集合族版）

namespace Zorn

variable {β : Type}

def IsChain (c : Set (Set β)) : Prop := ∀ s ∈ c, ∀ t ∈ c, s ⊆ t ∨ t ⊆ s

open Classical in

noncomputable def next (𝔉 : Set (Set β)) (S : Set β) : Set β :=
  if h : ∃ T, T ∈ 𝔉 ∧ S ⊆ T ∧ T ≠ S then Classical.choose h else S

inductive Tower (𝔉 : Set (Set β)) (A : Set β) : Set β → Prop
  | base : Tower 𝔉 A A
  | next {S : Set β} : Tower 𝔉 A S → Tower 𝔉 A (next 𝔉 S)
  | sup (c : Set (Set β)) : (∀ S ∈ c, Tower 𝔉 A S) → IsChain c → (∃ S, S ∈ c) →
      Tower 𝔉 A (⋃₀ c)

variable {𝔉 : Set (Set β)} {A : Set β}

theorem subset_next (S : Set β) : S ⊆ next 𝔉 S := by
  unfold next
  split
  · next h => exact (Classical.choose_spec h).2.1
  · exact Set.subset_refl S

theorem next_mem {S : Set β} (hS : S ∈ 𝔉) : next 𝔉 S ∈ 𝔉 := by
  unfold next
  split
  · next h => exact (Classical.choose_spec h).1
  · exact hS

theorem Tower.mem (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {S : Set β} (hS : Tower 𝔉 A S) : S ∈ 𝔉 ∧ A ⊆ S :=
  sorry

def Extreme (𝔉 : Set (Set β)) (A C : Set β) : Prop :=
  ∀ T, Tower 𝔉 A T → T ⊆ C → T ≠ C → next 𝔉 T ⊆ C

theorem Extreme.dichotomy (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hCT : Tower 𝔉 A C) (hC : Extreme 𝔉 A C) {T : Set β}
    (hT : Tower 𝔉 A T) : T ⊆ C ∨ next 𝔉 C ⊆ T :=
  sorry

theorem Tower.extreme (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hC : Tower 𝔉 A C) : Extreme 𝔉 A C :=
  sorry

theorem Tower.isChain (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : IsChain {S | Tower 𝔉 A S} :=
  sorry

theorem exists_maximal (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : ∃ M, M ∈ 𝔉 ∧ A ⊆ M ∧ ∀ N, N ∈ 𝔉 → M ⊆ N → N = M :=
  sorry

end Zorn

namespace Filter

variable {α : Type}

theorem exists_ultra (F : Filter α) (hF : (∅ : Set α) ∉ F) :
    ∃ G : Filter α, G.IsUltra ∧ F.sets ⊆ G.sets :=
  sorry

end Filter

-- ## Part H: 主定理のコンパクト版

section Compact

def Filter.ConvergesTo {X : Type} [TopologicalSpace X] (F : Filter X) (a : X) : Prop :=
  ∀ U, IsOpen U → a ∈ U → U ∈ F

variable {X : Type} [TopologicalSpace X]

theorem isCompact_of_ultra {K : Set X}
    (h : ∀ F : Filter X, F.IsUltra → K ∈ F → ∃ a, a ∈ K ∧ F.ConvergesTo a) : IsCompact K :=
  sorry

theorem IsCompact.ultra_converges {K : Set X} (hK : IsCompact K) {F : Filter X}
    (hF : F.IsUltra) (hKF : K ∈ F) : ∃ a, a ∈ K ∧ F.ConvergesTo a :=
  sorry

theorem Filter.IsUltra.mem_of_cover {α : Type} {F : Filter α} (hF : F.IsUltra) :
    ∀ (L : List (Set α)) (s : Set α), s ∈ F → (∀ a ∈ s, ∃ A ∈ L, a ∈ A) → ∃ A ∈ L, A ∈ F :=
  sorry

variable {α : Type} [UniformSpace α]

theorem IsCompact.totallyBounded {K : Set α} (hK : IsCompact K) : TotallyBounded K :=
  sorry

def Filter.Cauchy (F : Filter α) : Prop := ∀ V ∈ 𝓤 α, ∃ A, A ∈ F ∧ Small V A

theorem Filter.IsUltra.cauchy {F : Filter α} (hF : F.IsUltra) {s : Set α}
    (hs : TotallyBounded s) (hsF : s ∈ F) : F.Cauchy :=
  sorry

end Compact

section AscoliCompact

variable {X Y : Type} [UniformSpace Y]

theorem Filter.Cauchy.convergesTo_of_pointwise {F : Filter (X → Y)} (hF : F.Cauchy)
    (hne : (∅ : Set (X → Y)) ∉ F) (φ : X → Y)
    (hφ : ∀ x, (F.map fun f => f x).ConvergesTo (φ x)) : F.ConvergesTo φ :=
  sorry

variable [TopologicalSpace X]

theorem ascoli_compact [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, ∃ K : Set Y, IsCompact K ∧ (fun f => f x) '' H ⊆ K) (hcl : IsClosed H) :
    IsCompact H :=
  sorry

end AscoliCompact

-- できたら確認: 主定理（全有界版・コンパクト版）が使う公理
-- #print axioms ascoli
-- #print axioms ascoli_compact
