-- 受講者用ファイル（解説は Web 版のテキストで読む）。dev/tools/student.py が自動生成する。
-- このファイルには書き込まず、LeanIntro/MyWork/ の同じ名前のファイルを使うこと。

import LeanIntro.Solutions.«08_Real»
import LeanIntro.Solutions.«09_Ascoli»

-- # 発展演習: 実数版 Arzelà–Ascoli の定理

open CompleteOrderedField UniformSpace

variable {R : Type} [CompleteOrderedField R]

-- ## Part A: 実数の一様構造

instance realUniformSpace : UniformSpace R where
  Entourage := {V | ∃ ε, 0 < ε ∧ ∀ a b : R, abs (a - b) < ε → (a, b) ∈ V}
  univ_mem := sorry
  mono := sorry
  inter_mem := sorry
  refl := sorry
  symm := sorry
  comp := sorry

def distLt (ε : R) : Set (R × R) := {p | abs (p.1 - p.2) < ε}

theorem distLt_mem {ε : R} (hε : 0 < ε) : distLt ε ∈ 𝓤 R := ⟨ε, hε, fun _ _ h => h⟩

-- ## Part B: 2つの位相の一致

theorem TopologicalSpace.ext_iff_isOpen {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : ∀ s, t₁.IsOpen s ↔ t₂.IsOpen s) : t₁ = t₂ := by
  cases t₁
  cases t₂
  congr
  funext s
  exact propext (h s)

theorem uniform_topology_eq :
    (UniformSpace.toTopologicalSpace : TopologicalSpace R) =
      CompleteOrderedField.instTopologicalSpace :=
  sorry

theorem isCompact_Icc' (a b : R) : IsCompact (Icc a b) :=
  sorry

-- ## Part C: 用語の対応

section Dictionary

variable {X : Type} [TopologicalSpace X]

def EquicontinuousR (H : Set (X → R)) : Prop :=
  ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ y ∈ U, abs (f y - f x) < ε

def UniformlyBounded (H : Set (X → R)) : Prop := ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M

theorem equicontinuousR_iff {H : Set (X → R)} : EquicontinuousR H ↔ Equicontinuous H :=
  sorry

theorem mem_Icc_of_abs_le {a M : R} (h : abs a ≤ M) : a ∈ Icc (-M) M :=
  sorry

omit [TopologicalSpace X] in

theorem UniformlyBounded.pointwise {H : Set (X → R)} (h : UniformlyBounded H) (x : X) :
    ∃ K : Set R, IsCompact K ∧ (fun f => f x) '' H ⊆ K :=
  sorry

-- ## Part D: 実数版 Ascoli（閉集合版）

theorem arzela_ascoli_closed [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) (hcl : IsClosed H) : IsCompact H :=
  sorry

-- ## Part E: 逆向き——コンパクトなら一様有界かつ等連続

theorem bounded_of_cover {β : Type} (B : β → R → Prop)
    (hB : ∀ y M M', B y M → M ≤ M' → B y M') {s : Set β} :
    ∀ L : List (Set β), (∀ A ∈ L, ∃ M, ∀ y ∈ A, y ∈ s → B y M) →
      (∀ y ∈ s, ∃ A ∈ L, y ∈ A) → ∃ M, ∀ y ∈ s, B y M :=
  sorry

theorem TotallyBounded.bounded {s : Set R} (hs : TotallyBounded s) :
    ∃ M, ∀ y ∈ s, abs y ≤ M :=
  sorry

theorem bounded_of_continuous [CompactSpace X] {f : X → R} (hf : Continuous f) :
    ∃ M, ∀ x, abs (f x) ≤ M :=
  sorry

theorem arzela_ascoli_converse [CompactSpace X] {H : Set (X → R)}
    (hc : ∀ f ∈ H, Continuous f) (hH : IsCompact H) :
    UniformlyBounded H ∧ EquicontinuousR H :=
  sorry

-- ## Part F: 相対コンパクト版（閉包）

def closure {α : Type} [TopologicalSpace α] (s : Set α) : Set α :=
  {a | ∀ U, IsOpen U → a ∈ U → ∃ b, b ∈ U ∧ b ∈ s}

theorem subset_closure {α : Type} [TopologicalSpace α] (s : Set α) : s ⊆ closure s :=
  sorry

theorem isClosed_closure {α : Type} [TopologicalSpace α] (s : Set α) : IsClosed (closure s) :=
  sorry

theorem exists_near_of_mem_closure {X : Type} {H : Set (X → R)} {f : X → R}
    (hf : f ∈ closure H) {ε : R} (hε : 0 < ε) : ∃ g, g ∈ H ∧ ∀ x, abs (f x - g x) < ε := by
  have hV : unifRel (distLt ε) ∈ 𝓤 (X → R) := ⟨_, distLt_mem hε, fun _ h => h⟩
  have ⟨O, hO, hfO, hOV⟩ := exists_open_ball hV f
  have ⟨g, hgO, hgH⟩ := hf O hO hfO
  exact ⟨g, hgH, hOV g hgO⟩

omit [TopologicalSpace X] in

theorem UniformlyBounded.closure {H : Set (X → R)} (h : UniformlyBounded H) :
    UniformlyBounded (closure H) :=
  sorry

theorem add_three_lt {a b c ε : R} (ha : a < ε / 2 / 2) (hb : b < ε / 2) (hc : c < ε / 2 / 2) :
    a + b + c < ε := by
  have h₁ := add_lt_add ha hc
  rw [add_halves] at h₁
  have h₂ := add_lt_add h₁ hb
  rw [add_halves] at h₂
  have e : a + b + c = a + c + b := by ac_rfl
  rw [e]
  exact h₂

theorem EquicontinuousR.closure {H : Set (X → R)} (h : EquicontinuousR H) :
    EquicontinuousR (closure H) :=
  sorry

theorem arzela_ascoli_closure [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) : IsCompact (closure H) :=
  sorry

-- ## Part G: 点列版（一様収束する部分列）

theorem IsCompact.exists_clusterPt {α : Type} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) {u : Nat → α} (hu : ∀ n, u n ∈ K) :
    ∃ g, g ∈ K ∧ ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U :=
  sorry

theorem lt_of_mul_natCast_lt_one {d ε n : R} (hε : 0 < ε) (hn : ε⁻¹ < n)
    (h : abs d * n < 1) : abs d < ε :=
  sorry

theorem natCast_succ_pos (k : Nat) : (0 : R) < natCast (k + 1) := by
  rw [natCast_succ]
  exact lt_of_le_of_lt (natCast_nonneg k) (lt_add_of_pos_right _ zero_lt_one)

theorem natCast_le_natCast {m n : Nat} (h : m ≤ n) : (natCast m : R) ≤ natCast n := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, natCast_add]
  have := add_le_add_left _ _ (natCast_nonneg k) (natCast m : R)
  rw [add_zero] at this
  exact this

def distInv (k : Nat) : Set (R × R) := {p | abs (p.1 - p.2) * natCast (k + 1) < 1}

theorem distInv_mem (k : Nat) : distInv (R := R) k ∈ 𝓤 R := by
  have hk := natCast_succ_pos (R := R) k
  refine ⟨(natCast (k + 1))⁻¹, inv_pos hk, fun a b h => ?_⟩
  have := mul_lt_mul_of_pos_left h hk
  rw [mul_comm (natCast (k + 1)) (natCast (k + 1))⁻¹, inv_mul_cancel (ne_of_lt hk).symm,
    mul_comm] at this
  exact this

theorem exists_subseq_tendsto {X : Type} {u : Nat → X → R} {g : X → R}
    (hg : ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

theorem arzela_ascoli_seq [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) {u : Nat → X → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : X → R,
      (∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (g y - g x) < ε) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

end Dictionary

-- ## Part H: 閉区間上の関数（古典的な Arzelà–Ascoli の定理）

instance subspaceTopology {α : Type} [TopologicalSpace α] (p : α → Prop) :
    TopologicalSpace (Subtype p) where
  IsOpen s := ∃ U : Set α, IsOpen U ∧ ∀ x : Subtype p, x ∈ s ↔ x.1 ∈ U
  isOpen_univ := ⟨Set.univ, isOpen_univ, fun _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  isOpen_inter := fun _ _ ⟨U, hU, hsU⟩ ⟨V, hV, htV⟩ =>
    ⟨U ∩ V, isOpen_inter _ _ hU hV, fun x =>
      ⟨fun ⟨h₁, h₂⟩ => ⟨(hsU x).mp h₁, (htV x).mp h₂⟩,
       fun ⟨h₁, h₂⟩ => ⟨(hsU x).mpr h₁, (htV x).mpr h₂⟩⟩⟩
  isOpen_sUnion := fun S hS =>
    ⟨⋃₀ {U | IsOpen U ∧ ∀ x : Subtype p, x.1 ∈ U → x ∈ ⋃₀ S},
     isOpen_sUnion _ fun _ hU => hU.1, fun x =>
      ⟨fun ⟨s, hsS, hxs⟩ =>
        have ⟨U, hU, hsU⟩ := hS s hsS
        ⟨U, ⟨hU, fun y hy => ⟨s, hsS, (hsU y).mpr hy⟩⟩, (hsU x).mp hxs⟩,
       fun ⟨_, ⟨_, hU⟩, hxU⟩ => hU x hxU⟩⟩

instance (a b : R) : CompactSpace {x // x ∈ Icc a b} where
  isCompact_univ := sorry

theorem equicontinuousR_of_uniform {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε) :
    EquicontinuousR H :=
  sorry

theorem arzela_ascoli {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (hb : ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M)
    (heq : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε)
    {u : Nat → {x // x ∈ Icc a b} → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : {x // x ∈ Icc a b} → R,
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  sorry

#print axioms arzela_ascoli
