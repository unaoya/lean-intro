-- 解答（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。

import LeanIntro.Original.«06_Topology»

-- # 発展演習 Ascoli の解答

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
  Entourage : Set (Set (α × α))
  univ_mem : Set.univ ∈ Entourage
  mono : ∀ {V W : Set (α × α)}, V ∈ Entourage → V ⊆ W → W ∈ Entourage
  inter_mem : ∀ {V W : Set (α × α)}, V ∈ Entourage → W ∈ Entourage → V ∩ W ∈ Entourage
  refl : ∀ {V : Set (α × α)}, V ∈ Entourage → ∀ a, (a, a) ∈ V
  symm : ∀ {V : Set (α × α)}, V ∈ Entourage → Set.swapRel V ∈ Entourage
  comp : ∀ {V : Set (α × α)}, V ∈ Entourage → ∃ W, W ∈ Entourage ∧ Set.compRel W W ⊆ V

notation "𝓤 " α:max => @UniformSpace.Entourage α _

namespace UniformSpace

variable {α : Type} [UniformSpace α]

theorem exists_half {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c, (a, b) ∈ W → (b, c) ∈ W → (a, c) ∈ V := by
  have ⟨W, hW, hWV⟩ := comp hV
  refine ⟨W ∩ Set.swapRel W, inter_mem hW (symm hW), ?_, ?_⟩
  · intro a b ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩
  · intro a b c ⟨h₁, _⟩ ⟨h₂, _⟩
    exact hWV _ ⟨b, h₁, h₂⟩

theorem exists_third {V : Set (α × α)} (hV : V ∈ 𝓤 α) :
    ∃ W ∈ 𝓤 α, (∀ a b, (a, b) ∈ W → (b, a) ∈ W) ∧
      ∀ a b c d, (a, b) ∈ W → (b, c) ∈ W → (c, d) ∈ W → (a, d) ∈ V := by
  have ⟨W₁, hW₁, _, h₁⟩ := exists_half hV
  have ⟨W₂, hW₂, hsymm, h₂⟩ := exists_half hW₁
  refine ⟨W₂, hW₂, hsymm, fun a b c d hab hbc hcd => ?_⟩
  exact h₁ a c d (h₂ a b c hab hbc) (h₂ c d d hcd (refl hW₂ d))

instance toTopologicalSpace : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, ∃ V ∈ 𝓤 α, ∀ b, (a, b) ∈ V → b ∈ s
  isOpen_univ := fun _ _ => ⟨Set.univ, univ_mem, fun _ _ => trivial⟩
  isOpen_inter := by
    intro s t hs ht a ⟨has, hat⟩
    have ⟨V, hV, hVs⟩ := hs a has
    have ⟨W, hW, hWt⟩ := ht a hat
    exact ⟨V ∩ W, inter_mem hV hW, fun b ⟨hb₁, hb₂⟩ => ⟨hVs b hb₁, hWt b hb₂⟩⟩
  isOpen_sUnion := by
    intro S hS a ⟨s, hsS, has⟩
    have ⟨V, hV, hVs⟩ := hS s hsS a has
    exact ⟨V, hV, fun b hb => ⟨s, hsS, hVs b hb⟩⟩

theorem exists_open_ball {V : Set (α × α)} (hV : V ∈ 𝓤 α) (a : α) :
    ∃ O : Set α, IsOpen O ∧ a ∈ O ∧ ∀ b ∈ O, (a, b) ∈ V := by
  refine ⟨{y | ∃ W ∈ 𝓤 α, ∀ z, (y, z) ∈ W → (a, z) ∈ V}, ?_, ⟨V, hV, fun _ h => h⟩, ?_⟩
  · intro y ⟨W, hW, hWV⟩
    have ⟨W', hW', hW'W⟩ := comp hW
    exact ⟨W', hW', fun y' hy' => ⟨W', hW', fun z hz => hWV z (hW'W _ ⟨y', hy', hz⟩)⟩⟩
  · intro b ⟨W, hW, hWV⟩
    exact hWV b (refl hW b)

end UniformSpace

open UniformSpace

-- ## Part B: 一様収束と等連続性

section FunctionSpace

variable {X Y : Type} [UniformSpace Y]

def unifRel (V : Set (Y × Y)) : Set ((X → Y) × (X → Y)) := {p | ∀ x, (p.1 x, p.2 x) ∈ V}

instance uniformFun : UniformSpace (X → Y) where
  Entourage := {𝒱 | ∃ V ∈ 𝓤 Y, unifRel V ⊆ 𝒱}
  univ_mem := ⟨Set.univ, univ_mem, fun _ _ => trivial⟩
  mono := fun ⟨V, hV, hV𝒱⟩ h𝒱𝒲 => ⟨V, hV, fun p hp => h𝒱𝒲 p (hV𝒱 p hp)⟩
  inter_mem := fun ⟨V, hV, hV𝒱⟩ ⟨W, hW, hW𝒲⟩ =>
    ⟨V ∩ W, inter_mem hV hW, fun p hp =>
      ⟨hV𝒱 p fun x => (hp x).1, hW𝒲 p fun x => (hp x).2⟩⟩
  refl := fun ⟨_, hV, hV𝒱⟩ f => hV𝒱 (f, f) fun x => refl hV (f x)
  symm := fun ⟨V, hV, hV𝒱⟩ =>
    ⟨Set.swapRel V, symm hV, fun p hp => hV𝒱 (p.2, p.1) fun x => hp x⟩
  comp := fun ⟨_, hV, hV𝒱⟩ =>
    have ⟨W, hW, hWV⟩ := comp hV
    ⟨unifRel W, ⟨W, hW, fun _ h => h⟩, fun _ ⟨g, h₁, h₂⟩ =>
      hV𝒱 _ fun x => hWV _ ⟨g x, h₁ x, h₂ x⟩⟩

variable [TopologicalSpace X]

def EquicontinuousAt (H : Set (X → Y)) (x : X) : Prop :=
  ∀ V ∈ 𝓤 Y, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ V

def Equicontinuous (H : Set (X → Y)) : Prop := ∀ x, EquicontinuousAt H x

theorem Equicontinuous.mono {H H' : Set (X → Y)} (hH : Equicontinuous H) (h : H' ⊆ H) :
    Equicontinuous H' := fun x V hV =>
  have ⟨U, hU, hxU, hUV⟩ := hH x V hV
  ⟨U, hU, hxU, fun f hf => hUV f (h f hf)⟩

theorem equicontinuous_singleton {f : X → Y} (hf : Continuous f) :
    Equicontinuous {g | g = f} := by
  intro x V hV
  have ⟨O, hO, hxO, hOV⟩ := exists_open_ball hV (f x)
  refine ⟨f ⁻¹' O, hf O hO, hxO, ?_⟩
  intro g hg x' hx'
  rw [hg]
  exact hOV (f x') hx'

-- ## Part C: 核心補題

theorem Equicontinuous.finite_control [CompactSpace X] {H : Set (X → Y)}
    (hH : Equicontinuous H) {V : Set (Y × Y)} (hV : V ∈ 𝓤 Y) :
    ∃ W ∈ 𝓤 Y, ∃ P : List X, ∀ f ∈ H, ∀ g ∈ H,
      (∀ p ∈ P, (f p, g p) ∈ W) → ∀ x, (f x, g x) ∈ V := by
  have ⟨W, hW, hsymm, h3⟩ := exists_third hV
  have hU : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ x' ∈ U, (f x, f x') ∈ W :=
    fun x => hH x W hW
  let U := fun x => Classical.choose (hU x)
  have hUspec := fun x => Classical.choose_spec (hU x)
  have ⟨J, hJ, hcov⟩ := CompactSpace.isCompact_univ U (fun x => (hUspec x).1)
    (fun x _ => ⟨x, (hUspec x).2.1⟩)
  have ⟨P, hP⟩ := hJ.exists_list
  refine ⟨W, hW, P, fun f hf g hg hfg x => ?_⟩
  have ⟨y, hyJ, hxy⟩ := hcov x trivial
  have hfy := hsymm _ _ ((hUspec y).2.2 f hf x hxy)
  have hgy := (hUspec y).2.2 g hg x hxy
  exact h3 _ _ _ _ hfy (hfg y (hP y hyJ)) hgy

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
    (h : t ⊆ s) : TotallyBounded t := fun V hV =>
  have ⟨L, hsmall, hcov⟩ := hs V hV
  ⟨L, hsmall, fun a ha => hcov a (h a ha)⟩

variable {X Y : Type} [UniformSpace Y]

theorem finite_points_cover {H : Set (X → Y)}
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) {W : Set (Y × Y)} (hW : W ∈ 𝓤 Y) :
    ∀ P : List X, ∃ C : List (Set (X → Y)),
      (∀ S ∈ C, ∀ f ∈ S, ∀ g ∈ S, ∀ p ∈ P, (f p, g p) ∈ W) ∧ ∀ f ∈ H, ∃ S ∈ C, f ∈ S
  | [] => by
    refine ⟨[Set.univ], ?_, ?_⟩
    · intro _ _ _ _ _ _ p hp
      exact nomatch hp
    · intro f _
      exact ⟨Set.univ, List.mem_cons_self, trivial⟩
  | x :: P => by
    have ⟨C, hCsmall, hCcov⟩ := finite_points_cover hpt hW P
    have ⟨L, hLsmall, hLcov⟩ := hpt x W hW
    refine ⟨List.interCover C (L.map fun A => (fun f => f x) ⁻¹' A), ?_, ?_⟩
    · intro S hS f hf g hg p hp
      have ⟨S', hS', B, hB, hSeq⟩ := List.mem_interCover hS
      have ⟨A, hA, hBeq⟩ := List.mem_map.mp hB
      rw [hSeq, ← hBeq] at hf hg
      cases List.mem_cons.mp hp with
      | inl h => rw [h]; exact hLsmall A hA _ hf.2 _ hg.2
      | inr h => exact hCsmall S' hS' f hf.1 g hg.1 p h
    · refine List.interCover_covers hCcov fun f hf => ?_
      have ⟨A, hA, hfA⟩ := hLcov (f x) ⟨f, hf, rfl⟩
      exact ⟨_, List.mem_map_of_mem hA, hfA⟩

variable [TopologicalSpace X]

theorem ascoli [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, TotallyBounded ((fun f => f x) '' H)) : TotallyBounded H := by
  intro 𝒱 ⟨V, hV, hV𝒱⟩
  have ⟨W, hW, P, hctrl⟩ := hH.finite_control hV
  have ⟨C, hCsmall, hCcov⟩ := finite_points_cover hpt hW P
  refine ⟨C.map fun S => S ∩ H, ?_, ?_⟩
  · intro A hA
    have ⟨S, hS, hSA⟩ := List.mem_map.mp hA
    rw [← hSA]
    intro f ⟨hfS, hfH⟩ g ⟨hgS, hgH⟩
    exact hV𝒱 (f, g) (hctrl f hfH g hgH (hCsmall S hS f hfS g hgS))
  · intro f hf
    have ⟨S, hS, hfS⟩ := hCcov f hf
    exact ⟨S ∩ H, List.mem_map_of_mem hS, hfS, hf⟩

end TotallyBounded

-- ## Part E: 反例 — 等連続性は外せない

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
  isCompact_univ := by
    intro I U hU hcov
    have ⟨i₀, hi₀⟩ := hcov none trivial
    have ⟨N, hN⟩ := hU i₀ hi₀
    let c := fun k : Nat => Classical.choose (hcov (some k) trivial)
    have hc := fun k : Nat => Classical.choose_spec (hcov (some k) trivial)
    let p : Fin (N + 1) → I := fun k =>
      match k with
      | ⟨0, _⟩ => i₀
      | ⟨k + 1, _⟩ => c k
    refine ⟨{i | ∃ k, p k = i}, ⟨N + 1, p, fun _ h => h⟩, ?_⟩
    intro o _
    match o with
    | none => exact ⟨i₀, ⟨⟨0, Nat.succ_pos N⟩, rfl⟩, hi₀⟩
    | some n =>
      by_cases h : N ≤ n
      · exact ⟨i₀, ⟨⟨0, Nat.succ_pos N⟩, rfl⟩, hN n h⟩
      · exact ⟨c n, ⟨⟨n + 1, Nat.succ_lt_succ (Nat.lt_of_not_le h)⟩, rfl⟩, hc n⟩

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

theorem totallyBounded_bool (s : Set Bool) : TotallyBounded s := by
  intro V hV
  refine ⟨[{b | b = true}, {b | b = false}], ?_, ?_⟩
  · intro A hA a ha b hb
    cases List.mem_cons.mp hA with
    | inl h =>
      rw [h] at ha hb
      rw [show a = b from ha.trans hb.symm]
      exact hV b
    | inr h =>
      rw [List.mem_singleton.mp h] at ha hb
      rw [show a = b from ha.trans hb.symm]
      exact hV b
  · intro a _
    cases a with
    | true => exact ⟨_, List.mem_cons_self, rfl⟩
    | false => exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

theorem not_equicontinuousAt : ¬ EquicontinuousAt H none := by
  intro h
  have ⟨U, hU, hnone, hUV⟩ := h (diagonal Bool) (fun _ => rfl)
  have ⟨N, hN⟩ := hU hnone
  have h' : δ N none = δ N (some N) := hUV (δ N) ⟨N, rfl⟩ (some N) (hN N (Nat.le_refl N))
  simp [δ] at h'

theorem exists_avoid (L : List (Set (Option Nat → Bool)))
    (hL : ∀ A ∈ L, Small (unifRel (diagonal Bool)) A) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ A ∈ L, δ n ∉ A := by
  induction L with
  | nil => exact fun N => ⟨N, Nat.le_refl N, fun _ h => nomatch h⟩
  | cons A L ih =>
    intro N
    have ih := ih fun B hB => hL B (List.mem_cons_of_mem _ hB)
    have ⟨n, hn, hnL⟩ := ih N
    have ⟨m, hm, hmL⟩ := ih (n + 1)
    by_cases hnA : δ n ∈ A
    · refine ⟨m, Nat.le_trans hn (Nat.le_trans (Nat.le_succ n) hm), ?_⟩
      intro B hB hmB
      cases List.mem_cons.mp hB with
      | inl h =>
        rw [h] at hmB
        have h' : δ n (some n) = δ m (some n) := hL A List.mem_cons_self _ hnA _ hmB (some n)
        have hne : n ≠ m := Nat.ne_of_lt hm
        simp [δ, hne] at h'
      | inr h => exact hmL B h hmB
    · refine ⟨n, hn, fun B hB hnB => ?_⟩
      cases List.mem_cons.mp hB with
      | inl h => rw [h] at hnB; exact hnA hnB
      | inr h => exact hnL B h hnB

theorem not_totallyBounded : ¬ TotallyBounded H := by
  intro h
  have ⟨L, hsmall, hcov⟩ :=
    h (unifRel (diagonal Bool)) ⟨_, fun _ => rfl, fun _ hp => hp⟩
  have ⟨n, _, hn⟩ := exists_avoid L hsmall 0
  have ⟨A, hA, hnA⟩ := hcov (δ n) ⟨n, rfl⟩
  exact hn A hA hnA

end Counterexample

-- ## Part F: 逆向き — 全有界なら等連続

section Converse

variable {X Y : Type} [UniformSpace Y]

theorem TotallyBounded.eval {H : Set (X → Y)} (hH : TotallyBounded H) (x : X) :
    TotallyBounded ((fun f => f x) '' H) := by
  intro V hV
  have ⟨L, hsmall, hcov⟩ := hH (unifRel V) ⟨V, hV, fun _ h => h⟩
  refine ⟨L.map fun S => (fun f => f x) '' S, ?_, ?_⟩
  · intro A hA
    have ⟨S, hS, hSA⟩ := List.mem_map.mp hA
    rw [← hSA]
    intro a ⟨f, hf, hfa⟩ b ⟨g, hg, hgb⟩
    rw [← hfa, ← hgb]
    exact hsmall S hS f hf g hg x
  · intro a ⟨f, hf, hfa⟩
    have ⟨S, hS, hfS⟩ := hcov f hf
    exact ⟨_, List.mem_map_of_mem hS, f, hfS, hfa⟩

variable [TopologicalSpace X]

theorem TotallyBounded.equicontinuous {H : Set (X → Y)} (hc : ∀ f ∈ H, Continuous f)
    (hH : TotallyBounded H) : Equicontinuous H := by
  intro x V hV
  have ⟨W, hW, _, h3⟩ := exists_third hV
  have ⟨C, hsmall, hcov⟩ := hH (unifRel W) ⟨W, hW, fun _ h => h⟩
  have key : ∀ C : List (Set (X → Y)), (∀ S ∈ C, Small (unifRel W) S) →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ S ∈ C, ∀ f ∈ S, f ∈ H → ∀ x' ∈ U, (f x, f x') ∈ V := by
    intro C
    induction C with
    | nil => exact fun _ => ⟨Set.univ, isOpen_univ, trivial, fun _ h => nomatch h⟩
    | cons S C ih =>
      intro hC
      have ⟨U, hU, hxU, hUV⟩ := ih fun S' hS' => hC S' (List.mem_cons_of_mem _ hS')
      by_cases hS : ∃ g, g ∈ S ∧ g ∈ H
      · have ⟨g, hgS, hgH⟩ := hS
        have ⟨O, hO, hgO, hOW⟩ := exists_open_ball hW (g x)
        refine ⟨U ∩ g ⁻¹' O, isOpen_inter _ _ hU (hc g hgH O hO), ⟨hxU, hgO⟩, ?_⟩
        intro S' hS' f hfS' hfH x' ⟨hx'U, hx'O⟩
        cases List.mem_cons.mp hS' with
        | inl h =>
          rw [h] at hfS'
          have hS := hC S List.mem_cons_self
          exact h3 _ _ _ _ (hS f hfS' g hgS x) (hOW _ hx'O) (hS g hgS f hfS' x')
        | inr h => exact hUV S' h f hfS' hfH x' hx'U
      · refine ⟨U, hU, hxU, fun S' hS' f hfS' hfH => ?_⟩
        cases List.mem_cons.mp hS' with
        | inl h => rw [h] at hfS'; exact absurd ⟨f, hfS', hfH⟩ hS
        | inr h => exact hUV S' h f hfS' hfH
  have ⟨U, hU, hxU, hUV⟩ := key C hsmall
  refine ⟨U, hU, hxU, fun f hf => ?_⟩
  have ⟨S, hS, hfS⟩ := hcov f hf
  exact hUV S hS f hfS hf

end Converse

-- ## Part G: フィルターと Zorn の補題

structure Filter (α : Type) where
  sets : Set (Set α)
  univ_mem : Set.univ ∈ sets
  mono : ∀ {s t : Set α}, s ∈ sets → s ⊆ t → t ∈ sets
  inter_mem : ∀ {s t : Set α}, s ∈ sets → t ∈ sets → s ∩ t ∈ sets

namespace Filter

variable {α β : Type}

instance : Membership (Set α) (Filter α) := ⟨fun F s => s ∈ F.sets⟩

structure IsUltra (F : Filter α) : Prop where
  empty_not_mem : (∅ : Set α) ∉ F
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

theorem IsUltra.map {F : Filter α} (hF : F.IsUltra) (f : α → β) : (F.map f).IsUltra where
  empty_not_mem := hF.empty_not_mem
  mem_or_compl_mem := fun s => hF.mem_or_compl_mem (f ⁻¹' s)

theorem mem_list_inter (F : Filter α) {I : Type} (s : I → Set α) :
    ∀ L : List I, (∀ i ∈ L, s i ∈ F) → {a | ∀ i ∈ L, a ∈ s i} ∈ F
  | [], _ => F.mono F.univ_mem fun _ _ _ h => nomatch h
  | i :: L, h =>
    F.mono (F.inter_mem (h i List.mem_cons_self)
        (mem_list_inter F s L fun j hj => h j (List.mem_cons_of_mem _ hj)))
      fun a ⟨hai, haL⟩ j hj => by
        cases List.mem_cons.mp hj with
        | inl e => rw [e]; exact hai
        | inr e => exact haL j e

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
    (hA : A ∈ 𝔉) {S : Set β} (hS : Tower 𝔉 A S) : S ∈ 𝔉 ∧ A ⊆ S := by
  induction hS with
  | base => exact ⟨hA, Set.subset_refl A⟩
  | next _ ih => exact ⟨next_mem ih.1, fun a ha => subset_next _ a (ih.2 a ha)⟩
  | sup c _ hc hne ih =>
    have ⟨S, hS⟩ := hne
    exact ⟨hchain c (fun T hT => (ih T hT).1) hc hne, fun a ha => ⟨S, hS, (ih S hS).2 a ha⟩⟩

def Extreme (𝔉 : Set (Set β)) (A C : Set β) : Prop :=
  ∀ T, Tower 𝔉 A T → T ⊆ C → T ≠ C → next 𝔉 T ⊆ C

theorem Extreme.dichotomy (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hCT : Tower 𝔉 A C) (hC : Extreme 𝔉 A C) {T : Set β}
    (hT : Tower 𝔉 A T) : T ⊆ C ∨ next 𝔉 C ⊆ T := by
  induction hT with
  | base => exact Or.inl (Tower.mem hchain hA hCT).2
  | @next T hT ih =>
    cases ih with
    | inl h =>
      by_cases he : T = C
      · rw [he]; exact Or.inr (Set.subset_refl _)
      · exact Or.inl (hC T hT h he)
    | inr h => exact Or.inr fun a ha => subset_next T a (h a ha)
  | sup c _ _ _ ih =>
    by_cases h : ∀ S ∈ c, S ⊆ C
    · exact Or.inl fun a ⟨S, hS, haS⟩ => h S hS a haS
    · have ⟨S, hS, hSC⟩ : ∃ S, S ∈ c ∧ ¬ S ⊆ C := Classical.byContradiction fun h' =>
        h fun S hS => Classical.byContradiction fun hSC => h' ⟨S, hS, hSC⟩
      cases ih S hS with
      | inl h => exact absurd h hSC
      | inr h => exact Or.inr fun a ha => ⟨S, hS, h a ha⟩

theorem Tower.extreme (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) {C : Set β} (hC : Tower 𝔉 A C) : Extreme 𝔉 A C := by
  induction hC with
  | base =>
    intro T hT hTA hne
    exact absurd (Set.subset_antisymm hTA (Tower.mem hchain hA hT).2) hne
  | @next C hC ih =>
    intro T hT hTC hne
    cases Extreme.dichotomy hchain hA hC ih hT with
    | inl h =>
      by_cases he : T = C
      · rw [he]; exact Set.subset_refl _
      · exact fun a ha => subset_next C a (ih T hT h he a ha)
    | inr h => exact absurd (Set.subset_antisymm hTC h) hne
  | sup c hc _ _ ih =>
    intro T hT hTc hne
    have ⟨S, hS, hST⟩ : ∃ S, S ∈ c ∧ ¬ S ⊆ T := Classical.byContradiction fun h =>
      hne (Set.subset_antisymm hTc fun a ⟨S, hS, haS⟩ =>
        Classical.byContradiction fun haT => h ⟨S, hS, fun hST => haT (hST a haS)⟩)
    cases Extreme.dichotomy hchain hA (hc S hS) (ih S hS) hT with
    | inl h =>
      have hne' : T ≠ S := fun e => hST (e ▸ Set.subset_refl T)
      exact fun a ha => ⟨S, hS, ih S hS T hT h hne' a ha⟩
    | inr h => exact absurd (fun a ha => h a (subset_next S a ha)) hST

theorem Tower.isChain (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : IsChain {S | Tower 𝔉 A S} := by
  intro S hS T hT
  cases Extreme.dichotomy hchain hA hS (Tower.extreme hchain hA hS) hT with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl fun a ha => h a (subset_next S a ha)

theorem exists_maximal (hchain : ∀ c, c ⊆ 𝔉 → IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ 𝔉)
    (hA : A ∈ 𝔉) : ∃ M, M ∈ 𝔉 ∧ A ⊆ M ∧ ∀ N, N ∈ 𝔉 → M ⊆ N → N = M := by
  let M := ⋃₀ {S | Tower 𝔉 A S}
  have hM : Tower 𝔉 A M :=
    Tower.sup _ (fun _ h => h) (Tower.isChain hchain hA) ⟨A, Tower.base⟩
  have hnext : next 𝔉 M ⊆ M := fun a ha => ⟨_, Tower.next hM, ha⟩
  refine ⟨M, (Tower.mem hchain hA hM).1, (Tower.mem hchain hA hM).2, ?_⟩
  intro N hN hMN
  apply Classical.byContradiction
  intro hne
  have h : ∃ T, T ∈ 𝔉 ∧ M ⊆ T ∧ T ≠ M := ⟨N, hN, hMN, hne⟩
  have hspec := Classical.choose_spec h
  have heq : next 𝔉 M = Classical.choose h := by
    unfold next
    rw [dif_pos h]
  rw [← heq] at hspec
  exact hspec.2.2 (Set.subset_antisymm hnext hspec.2.1)

end Zorn

namespace Filter

variable {α : Type}

theorem exists_ultra (F : Filter α) (hF : (∅ : Set α) ∉ F) :
    ∃ G : Filter α, G.IsUltra ∧ F.sets ⊆ G.sets := by
  let P : Set (Set (Set α)) := {𝒮 | Set.univ ∈ 𝒮 ∧
    (∀ s t, s ∈ 𝒮 → s ⊆ t → t ∈ 𝒮) ∧ (∀ s t, s ∈ 𝒮 → t ∈ 𝒮 → s ∩ t ∈ 𝒮) ∧ ∅ ∉ 𝒮}
  have hchain : ∀ c, c ⊆ P → Zorn.IsChain c → (∃ S, S ∈ c) → ⋃₀ c ∈ P := by
    intro c hcP hc ⟨S, hS⟩
    refine ⟨⟨S, hS, (hcP S hS).1⟩, ?_, ?_, ?_⟩
    · intro s t ⟨T, hT, hsT⟩ hst
      exact ⟨T, hT, (hcP T hT).2.1 s t hsT hst⟩
    · intro s t ⟨T₁, hT₁, hs⟩ ⟨T₂, hT₂, ht⟩
      cases hc T₁ hT₁ T₂ hT₂ with
      | inl h => exact ⟨T₂, hT₂, (hcP T₂ hT₂).2.2.1 s t (h s hs) ht⟩
      | inr h => exact ⟨T₁, hT₁, (hcP T₁ hT₁).2.2.1 s t hs (h t ht)⟩
    · intro ⟨T, hT, he⟩
      exact (hcP T hT).2.2.2 he
  have hFP : F.sets ∈ P :=
    ⟨F.univ_mem, fun _ _ hs h => F.mono hs h, fun _ _ hs ht => F.inter_mem hs ht, hF⟩
  have ⟨M, ⟨huniv, hmono, hinter, hempty⟩, hFM, hmax⟩ := Zorn.exists_maximal hchain hFP
  let G : Filter α :=
    { sets := M, univ_mem := huniv, mono := fun hs h => hmono _ _ hs h,
      inter_mem := fun hs ht => hinter _ _ hs ht }
  refine ⟨G, ⟨hempty, fun s => ?_⟩, hFM⟩
  apply Classical.byContradiction
  intro hs
  have hs₁ : s ∉ M := fun h => hs (Or.inl h)
  have hs₂ : sᶜ ∉ M := fun h => hs (Or.inr h)
  let M' : Set (Set α) := {t | ∃ m, m ∈ M ∧ m ∩ s ⊆ t}
  have hM' : M' ∈ P := by
    refine ⟨⟨Set.univ, huniv, fun _ _ => trivial⟩, ?_, ?_, ?_⟩
    · intro t u ⟨m, hm, hmt⟩ htu
      exact ⟨m, hm, fun a ha => htu a (hmt a ha)⟩
    · intro t u ⟨m₁, hm₁, h₁⟩ ⟨m₂, hm₂, h₂⟩
      exact ⟨m₁ ∩ m₂, hinter _ _ hm₁ hm₂, fun a ⟨⟨ha₁, ha₂⟩, has⟩ =>
        ⟨h₁ a ⟨ha₁, has⟩, h₂ a ⟨ha₂, has⟩⟩⟩
    · intro ⟨m, hm, hms⟩
      exact hs₂ (hmono _ _ hm fun a ham has => hms a ⟨ham, has⟩)
  have hMM' : M ⊆ M' := fun m hm => ⟨m, hm, fun a ha => ha.1⟩
  have heq := hmax M' hM' hMM'
  have : s ∈ M' := ⟨Set.univ, huniv, fun a ha => ha.2⟩
  rw [heq] at this
  exact hs₁ this

end Filter

-- ## Part H: コンパクト版

section Compact

def Filter.ConvergesTo {X : Type} [TopologicalSpace X] (F : Filter X) (a : X) : Prop :=
  ∀ U, IsOpen U → a ∈ U → U ∈ F

variable {X : Type} [TopologicalSpace X]

theorem isCompact_of_ultra {K : Set X}
    (h : ∀ F : Filter X, F.IsUltra → K ∈ F → ∃ a, a ∈ K ∧ F.ConvergesTo a) : IsCompact K := by
  intro I U hU hcov
  apply Classical.byContradiction
  intro hnot
  let F : Filter X :=
    { sets := {s | ∃ L : List I, {a | a ∈ K ∧ ∀ i ∈ L, a ∉ U i} ⊆ s}
      univ_mem := ⟨[], fun _ _ => trivial⟩
      mono := fun ⟨L, hL⟩ hst => ⟨L, fun a ha => hst a (hL a ha)⟩
      inter_mem := fun ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ =>
        ⟨L₁ ++ L₂, fun a ⟨haK, haL⟩ =>
          ⟨h₁ a ⟨haK, fun i hi => haL i (List.mem_append.mpr (Or.inl hi))⟩,
           h₂ a ⟨haK, fun i hi => haL i (List.mem_append.mpr (Or.inr hi))⟩⟩⟩ }
  have hF : (∅ : Set X) ∉ F := by
    intro ⟨L, hL⟩
    apply hnot
    refine ⟨{i | i ∈ L}, Set.finite_of_list L, fun a haK => ?_⟩
    apply Classical.byContradiction
    intro hna
    exact hL a ⟨haK, fun i hi hai => hna ⟨i, hi, hai⟩⟩
  have ⟨G, hG, hFG⟩ := F.exists_ultra hF
  have ⟨a, haK, hconv⟩ := h G hG (hFG _ ⟨[], fun _ ha => ha.1⟩)
  have ⟨i, hai⟩ := hcov a haK
  have h₁ : U i ∈ G := hconv (U i) (hU i) hai
  have h₂ : (U i)ᶜ ∈ G :=
    hFG _ ⟨[i], fun _ ⟨_, hb⟩ => hb i List.mem_cons_self⟩
  exact hG.empty_not_mem (G.mono (G.inter_mem h₁ h₂) fun _ ⟨hb₁, hb₂⟩ => hb₂ hb₁)

theorem IsCompact.ultra_converges {K : Set X} (hK : IsCompact K) {F : Filter X}
    (hF : F.IsUltra) (hKF : K ∈ F) : ∃ a, a ∈ K ∧ F.ConvergesTo a := by
  apply Classical.byContradiction
  intro hno
  have hbad : ∀ a : {a // a ∈ K}, ∃ U, IsOpen U ∧ a.1 ∈ U ∧ U ∉ F := by
    intro ⟨a, haK⟩
    apply Classical.byContradiction
    intro h
    exact hno ⟨a, haK, fun U hU haU =>
      Classical.byContradiction fun hUF => h ⟨U, hU, haU, hUF⟩⟩
  let U := fun a => Classical.choose (hbad a)
  have hUspec := fun a => Classical.choose_spec (hbad a)
  have ⟨J, hJ, hJcov⟩ :=
    hK U (fun a => (hUspec a).1) fun a haK => ⟨⟨a, haK⟩, (hUspec ⟨a, haK⟩).2.1⟩
  have ⟨L, hL⟩ := hJ.exists_list
  have hmem := F.mem_list_inter (fun i => (U i)ᶜ) L fun i _ => hF.compl_mem (hUspec i).2.2
  apply hF.empty_not_mem
  refine F.mono (F.inter_mem hKF hmem) fun a ⟨haK, haL⟩ => ?_
  have ⟨i, hiJ, hai⟩ := hJcov a haK
  exact haL i (hL i hiJ) hai

theorem Filter.IsUltra.mem_of_cover {α : Type} {F : Filter α} (hF : F.IsUltra) :
    ∀ (L : List (Set α)) (s : Set α), s ∈ F → (∀ a ∈ s, ∃ A ∈ L, a ∈ A) → ∃ A ∈ L, A ∈ F
  | [], s, hs, hcov =>
    absurd (F.mono hs fun a ha => nomatch (hcov a ha)) hF.empty_not_mem
  | A :: L, s, hs, hcov => by
    by_cases hA : A ∈ F
    · exact ⟨A, List.mem_cons_self, hA⟩
    · have ⟨B, hB, hBF⟩ := hF.mem_of_cover L (s ∩ Aᶜ) (F.inter_mem hs (hF.compl_mem hA))
        fun a ⟨has, haA⟩ => by
          have ⟨B, hB, haB⟩ := hcov a has
          cases List.mem_cons.mp hB with
          | inl h => rw [h] at haB; exact absurd haB haA
          | inr h => exact ⟨B, h, haB⟩
      exact ⟨B, List.mem_cons_of_mem _ hB, hBF⟩

variable {α : Type} [UniformSpace α]

theorem IsCompact.totallyBounded {K : Set α} (hK : IsCompact K) : TotallyBounded K := by
  intro V hV
  have ⟨W, hW, hsymm, h2⟩ := exists_half hV
  let O := fun a => Classical.choose (exists_open_ball hW a)
  have hO := fun a => Classical.choose_spec (exists_open_ball hW a)
  have ⟨J, hJ, hcov⟩ := hK O (fun a => (hO a).1) fun a _ => ⟨a, (hO a).2.1⟩
  have ⟨P, hP⟩ := hJ.exists_list
  refine ⟨P.map O, ?_, ?_⟩
  · intro A hA
    have ⟨a, _, haA⟩ := List.mem_map.mp hA
    rw [← haA]
    intro b hb c hc
    exact h2 b a c (hsymm _ _ ((hO a).2.2 b hb)) ((hO a).2.2 c hc)
  · intro b hb
    have ⟨a, haJ, hba⟩ := hcov b hb
    exact ⟨O a, List.mem_map_of_mem (hP a haJ), hba⟩

def Filter.Cauchy (F : Filter α) : Prop := ∀ V ∈ 𝓤 α, ∃ A, A ∈ F ∧ Small V A

theorem Filter.IsUltra.cauchy {F : Filter α} (hF : F.IsUltra) {s : Set α}
    (hs : TotallyBounded s) (hsF : s ∈ F) : F.Cauchy := by
  intro V hV
  have ⟨L, hsmall, hcov⟩ := hs V hV
  have ⟨A, hA, hAF⟩ := hF.mem_of_cover L s hsF hcov
  exact ⟨A, hAF, hsmall A hA⟩

end Compact

section AscoliCompact

variable {X Y : Type} [UniformSpace Y]

theorem Filter.Cauchy.convergesTo_of_pointwise {F : Filter (X → Y)} (hF : F.Cauchy)
    (hne : (∅ : Set (X → Y)) ∉ F) (φ : X → Y)
    (hφ : ∀ x, (F.map fun f => f x).ConvergesTo (φ x)) : F.ConvergesTo φ := by
  intro 𝒪 h𝒪 hφ𝒪
  have ⟨𝒱, ⟨V, hV, hV𝒱⟩, h𝒱𝒪⟩ := h𝒪 φ hφ𝒪
  have ⟨W, hW, hWV⟩ := comp hV
  have ⟨A, hAF, hAsmall⟩ := hF (unifRel W) ⟨W, hW, fun _ h => h⟩
  refine F.mono hAF fun f hfA => h𝒱𝒪 f (hV𝒱 (φ, f) fun x => ?_)
  have ⟨O, hO, hφO, hOW⟩ := exists_open_ball hW (φ x)
  have ⟨g, hgO, hgA⟩ := Filter.nonempty_of_mem hne (F.inter_mem (hφ x O hO hφO) hAF)
  exact hWV _ ⟨g x, hOW _ hgO, hAsmall g hgA f hfA x⟩

variable [TopologicalSpace X]

theorem ascoli_compact [CompactSpace X] {H : Set (X → Y)} (hH : Equicontinuous H)
    (hpt : ∀ x, ∃ K : Set Y, IsCompact K ∧ (fun f => f x) '' H ⊆ K) (hcl : IsClosed H) :
    IsCompact H := by
  have hTB : TotallyBounded H := ascoli hH fun x =>
    have ⟨_, hK, hsub⟩ := hpt x
    hK.totallyBounded.subset hsub
  apply isCompact_of_ultra
  intro F hF hHF
  have hlim : ∀ x, ∃ y, (F.map fun f => f x).ConvergesTo y := fun x =>
    have ⟨K, hK, hsub⟩ := hpt x
    have ⟨y, _, hy⟩ := hK.ultra_converges (hF.map _) (F.mono hHF fun f hf => hsub _ ⟨f, hf, rfl⟩)
    ⟨y, hy⟩
  let φ := fun x => Classical.choose (hlim x)
  have hconv := (hF.cauchy hTB hHF).convergesTo_of_pointwise hF.empty_not_mem φ
    fun x => Classical.choose_spec (hlim x)
  refine ⟨φ, Classical.byContradiction fun hφ => ?_, hconv⟩
  exact hF.empty_not_mem
    (F.mono (F.inter_mem hHF (hconv _ hcl hφ)) fun _ ⟨h₁, h₂⟩ => h₂ h₁)

end AscoliCompact

#print axioms ascoli
#print axioms ascoli_compact
