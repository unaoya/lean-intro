import «08_RealSol»
import «09_AscoliSol»

/-! # 発展演習 実数版 Ascoli の解答

`10_AscoliReal.lean` の全問題の解答。問題文と説明はそちらを参照。
-/

open CompleteOrderedField UniformSpace

variable {R : Type} [CompleteOrderedField R]

/-! ## Part A: 実数の一様構造 -/

/-- 問題1: 実数の一様構造が公理を満たすことを示せ。 -/
instance realUniformSpace : UniformSpace R where
  Entourage := {V | ∃ ε, 0 < ε ∧ ∀ a b : R, abs (a - b) < ε → (a, b) ∈ V}
  univ_mem := ⟨1, zero_lt_one, fun _ _ _ => trivial⟩
  mono := fun ⟨ε, hε, hV⟩ hVW => ⟨ε, hε, fun a b h => hVW _ (hV a b h)⟩
  inter_mem := fun ⟨ε, hε, hV⟩ ⟨δ, hδ, hW⟩ =>
    ⟨CompleteOrderedField.min ε δ, lt_min hε hδ, fun a b h =>
      ⟨hV a b (lt_of_lt_of_le h (min_le_left ε δ)),
       hW a b (lt_of_lt_of_le h (min_le_right ε δ))⟩⟩
  refl := fun ⟨ε, hε, hV⟩ a => hV a a (by rw [abs_sub_self]; exact hε)
  symm := fun ⟨ε, hε, hV⟩ => ⟨ε, hε, fun a b h => hV b a (by rw [abs_sub_comm]; exact h)⟩
  comp := fun {V} ⟨ε, hε, hV⟩ => by
    refine ⟨{p | abs (p.1 - p.2) < ε / 2}, ⟨ε / 2, half_pos hε, fun _ _ h => h⟩, ?_⟩
    intro ⟨a, b⟩ ⟨z, (h₁ : abs (a - z) < ε / 2), (h₂ : abs (z - b) < ε / 2)⟩
    apply hV
    have := add_lt_add h₁ h₂
    rw [add_halves] at this
    exact lt_of_le_of_lt (abs_sub_le a z b) this

/-- 近縁 `{(a, b) | |a - b| < ε}`。 -/
def distLt (ε : R) : Set (R × R) := {p | abs (p.1 - p.2) < ε}

theorem distLt_mem {ε : R} (hε : 0 < ε) : distLt ε ∈ 𝓤 R := ⟨ε, hε, fun _ _ h => h⟩

/-! ## Part B: 2つの位相の一致 -/

/-- 開集合が一致する位相は等しい（与える）。 -/
theorem TopologicalSpace.ext_iff_isOpen {X : Type} {t₁ t₂ : TopologicalSpace X}
    (h : ∀ s, t₁.IsOpen s ↔ t₂.IsOpen s) : t₁ = t₂ := by
  cases t₁
  cases t₂
  congr
  funext s
  exact propext (h s)

/-- 問題2: 一様構造から定まる位相は、`08_Real.lean` の `ε`-位相と等しいことを示せ。 -/
theorem uniform_topology_eq :
    (UniformSpace.toTopologicalSpace : TopologicalSpace R) =
      CompleteOrderedField.instTopologicalSpace := by
  apply TopologicalSpace.ext_iff_isOpen
  intro s
  constructor
  · intro h x hx
    have ⟨V, ⟨ε, hε, hV⟩, hVs⟩ := h x hx
    exact ⟨ε, hε, fun y hy => hVs y (hV x y (by rw [abs_sub_comm]; exact hy))⟩
  · intro h x hx
    have ⟨ε, hε, hs⟩ := h x hx
    exact ⟨distLt ε, distLt_mem hε, fun y hy => hs y (by rw [abs_sub_comm]; exact hy)⟩

/-- 問題3: Heine–Borel を、一様構造の位相についての主張に運べ。 -/
theorem isCompact_Icc' (a b : R) : IsCompact (Icc a b) := by
  rw [uniform_topology_eq]
  exact isCompact_Icc a b

/-! ## Part C: 用語の対応 -/

section Dictionary

variable {X : Type} [TopologicalSpace X]

/-- `ε`-論法での等連続性。 -/
def EquicontinuousR (H : Set (X → R)) : Prop :=
  ∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ f ∈ H, ∀ y ∈ U, abs (f y - f x) < ε

/-- 一様有界。 -/
def UniformlyBounded (H : Set (X → R)) : Prop := ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M

/-- 問題4: `ε`-論法の等連続性と、近縁による等連続性（`09_Ascoli.lean`）は同値であることを示せ。 -/
theorem equicontinuousR_iff {H : Set (X → R)} : EquicontinuousR H ↔ Equicontinuous H := by
  constructor
  · intro h x V ⟨ε, hε, hV⟩
    have ⟨U, hU, hxU, hUε⟩ := h x ε hε
    exact ⟨U, hU, hxU, fun f hf y hy =>
      hV _ _ (by rw [abs_sub_comm]; exact hUε f hf y hy)⟩
  · intro h x ε hε
    have ⟨U, hU, hxU, hUV⟩ := h x (distLt ε) (distLt_mem hε)
    exact ⟨U, hU, hxU, fun f hf y hy => by
      rw [abs_sub_comm]; exact hUV f hf y hy⟩

/-- 問題5: `|a| ≤ M` なら `a ∈ [-M, M]` であることを示せ（`neg_abs_le`・`le_abs_self`）。 -/
theorem mem_Icc_of_abs_le {a M : R} (h : abs a ≤ M) : a ∈ Icc (-M) M :=
  ⟨le_trans _ _ _ (neg_le_neg h) (neg_abs_le a), le_trans _ _ _ (le_abs_self a) h⟩

omit [TopologicalSpace X] in
/-- 問題6: 一様有界なら、各点での値の集合はコンパクト集合（`[-M, M]`）に含まれることを示せ。 -/
theorem UniformlyBounded.pointwise {H : Set (X → R)} (h : UniformlyBounded H) (x : X) :
    ∃ K : Set R, IsCompact K ∧ (fun f => f x) '' H ⊆ K :=
  have ⟨M, hM⟩ := h
  ⟨Icc (-M) M, isCompact_Icc' _ _, fun _ ⟨f, hf, hfy⟩ => hfy ▸ mem_Icc_of_abs_le (hM f hf x)⟩

/-! ## Part D: 実数版 Ascoli（閉集合版） -/

/-- 問題7（実数版 Ascoli の定理、閉集合版）: コンパクト空間上の実数値関数の族が -/
theorem arzela_ascoli_closed [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) (hcl : IsClosed H) : IsCompact H :=
  ascoli_compact (equicontinuousR_iff.mp hH) hb.pointwise hcl

/-! ## Part E: 逆向き -/

/-- 問題8: 有限個の有界な集合で覆われる集合は有界であることを示せ。 -/
theorem bounded_of_cover {β : Type} (B : β → R → Prop)
    (hB : ∀ y M M', B y M → M ≤ M' → B y M') {s : Set β} :
    ∀ L : List (Set β), (∀ A ∈ L, ∃ M, ∀ y ∈ A, y ∈ s → B y M) →
      (∀ y ∈ s, ∃ A ∈ L, y ∈ A) → ∃ M, ∀ y ∈ s, B y M
  | [], _, hcov => ⟨0, fun y hy => nomatch hcov y hy⟩
  | A :: L, hL, hcov => by
    have ⟨M₁, hM₁⟩ := hL A List.mem_cons_self
    have ⟨M₂, hM₂⟩ := bounded_of_cover B hB (s := {y | y ∈ s ∧ y ∉ A}) L
      (fun A' hA' => have ⟨M, hM⟩ := hL A' (List.mem_cons_of_mem _ hA')
        ⟨M, fun y hy hys => hM y hy hys.1⟩)
      (fun y ⟨hys, hyA⟩ => by
        have ⟨A', hA', hyA'⟩ := hcov y hys
        cases List.mem_cons.mp hA' with
        | inl e => rw [e] at hyA'; exact absurd hyA' hyA
        | inr e => exact ⟨A', e, hyA'⟩)
    refine ⟨abs M₁ + abs M₂, fun y hy => ?_⟩
    by_cases hyA : y ∈ A
    · refine hB y _ _ (hM₁ y hyA hy) (le_trans _ _ _ (le_abs_self M₁) ?_)
      have := add_le_add_left _ _ (abs_nonneg M₂) (abs M₁)
      rw [add_zero] at this
      exact this
    · refine hB y _ _ (hM₂ y ⟨hy, hyA⟩) (le_trans _ _ _ (le_abs_self M₂) ?_)
      have := add_le_add_right (abs_nonneg M₁) (abs M₂)
      rw [zero_add] at this
      exact this

/-- 問題9: 実数の全有界集合は有界であることを示せ。 -/
theorem TotallyBounded.bounded {s : Set R} (hs : TotallyBounded s) :
    ∃ M, ∀ y ∈ s, abs y ≤ M := by
  have ⟨L, hsmall, hcov⟩ := hs (distLt 1) (distLt_mem zero_lt_one)
  refine bounded_of_cover (fun y M => abs y ≤ M) (fun _ _ _ h h' => le_trans _ _ _ h h') L
    (fun A hA => ?_) hcov
  by_cases h : ∃ a, a ∈ A ∧ a ∈ s
  · have ⟨a, haA, _⟩ := h
    refine ⟨abs a + 1, fun y hy _ => ?_⟩
    have hay : abs (y - a) < 1 := hsmall A hA y hy a haA
    exact le_trans _ _ _ (abs_le_abs_add_abs_sub y a)
      (add_le_add_left _ _ (le_of_lt hay) (abs a))
  · exact ⟨0, fun y hy hys => absurd ⟨y, hy, hys⟩ h⟩

/-- 問題10: コンパクト空間上の連続関数は有界であることを示せ。 -/
theorem bounded_of_continuous [CompactSpace X] {f : X → R} (hf : Continuous f) :
    ∃ M, ∀ x, abs (f x) ≤ M :=
  have ⟨M, hM⟩ := TotallyBounded.bounded
    (IsCompact.totallyBounded (IsCompact.image CompactSpace.isCompact_univ hf))
  ⟨M, fun x => hM (f x) ⟨x, trivial, rfl⟩⟩

/-- 問題11（逆向き）: 連続関数からなる、一様収束の位相でコンパクトな族は、 -/
theorem arzela_ascoli_converse [CompactSpace X] {H : Set (X → R)}
    (hc : ∀ f ∈ H, Continuous f) (hH : IsCompact H) :
    UniformlyBounded H ∧ EquicontinuousR H := by
  have hTB := IsCompact.totallyBounded hH
  refine ⟨?_, equicontinuousR_iff.mpr (hTB.equicontinuous hc)⟩
  have ⟨L, hsmall, hcov⟩ := hTB (unifRel (distLt 1)) ⟨_, distLt_mem zero_lt_one, fun _ h => h⟩
  refine bounded_of_cover (fun f M => ∀ x, abs (f x) ≤ M)
    (fun _ _ _ h h' x => le_trans _ _ _ (h x) h') L (fun S hS => ?_) hcov
  by_cases h : ∃ g, g ∈ S ∧ g ∈ H
  · have ⟨g, hgS, hgH⟩ := h
    have ⟨M, hM⟩ := bounded_of_continuous (hc g hgH)
    refine ⟨M + 1, fun f hfS _ x => ?_⟩
    have hfg : abs (f x - g x) < 1 := hsmall S hS f hfS g hgS x
    exact le_trans _ _ _ (abs_le_abs_add_abs_sub (f x) (g x))
      (add_le_add (hM x) (le_of_lt hfg))
  · exact ⟨0, fun f hfS hfH => absurd ⟨f, hfS, hfH⟩ h⟩

/-! ## Part F: 相対コンパクト版 -/

/-- 閉包。 -/
def closure {α : Type} [TopologicalSpace α] (s : Set α) : Set α :=
  {a | ∀ U, IsOpen U → a ∈ U → ∃ b, b ∈ U ∧ b ∈ s}

/-- 問題12: 集合は閉包に含まれることを示せ。 -/
theorem subset_closure {α : Type} [TopologicalSpace α] (s : Set α) : s ⊆ closure s :=
  fun a ha _ _ haU => ⟨a, haU, ha⟩

/-- 問題13: 閉包は閉集合であることを示せ。 -/
theorem isClosed_closure {α : Type} [TopologicalSpace α] (s : Set α) : IsClosed (closure s) := by
  apply isOpen_of_nhds
  intro a ha
  have ⟨U, hU, haU, hUs⟩ : ∃ U, IsOpen U ∧ a ∈ U ∧ ∀ b, b ∈ U → b ∉ s :=
    Classical.byContradiction fun h => ha fun U hU haU =>
      Classical.byContradiction fun h' => h ⟨U, hU, haU, fun b hbU hbs => h' ⟨b, hbU, hbs⟩⟩
  refine ⟨U, hU, haU, fun b hbU hb => ?_⟩
  have ⟨c, hcU, hcs⟩ := hb U hU hbU
  exact hUs c hcU hcs

/-- 閉包の点の近くには、元の集合の点がある（一様収束の意味で）。 -/
theorem exists_near_of_mem_closure {X : Type} {H : Set (X → R)} {f : X → R}
    (hf : f ∈ closure H) {ε : R} (hε : 0 < ε) : ∃ g, g ∈ H ∧ ∀ x, abs (f x - g x) < ε := by
  have hV : unifRel (distLt ε) ∈ 𝓤 (X → R) := ⟨_, distLt_mem hε, fun _ h => h⟩
  have ⟨O, hO, hfO, hOV⟩ := exists_open_ball hV f
  have ⟨g, hgO, hgH⟩ := hf O hO hfO
  exact ⟨g, hgH, hOV g hgO⟩

omit [TopologicalSpace X] in
/-- 問題14: 一様有界な族の閉包は一様有界であることを示せ（上界は `M + 1` にしてよい）。 -/
theorem UniformlyBounded.closure {H : Set (X → R)} (h : UniformlyBounded H) :
    UniformlyBounded (closure H) := by
  have ⟨M, hM⟩ := h
  refine ⟨M + 1, fun f hf x => ?_⟩
  have ⟨g, hgH, hfg⟩ := exists_near_of_mem_closure hf zero_lt_one
  exact le_trans _ _ _ (abs_le_abs_add_abs_sub (f x) (g x))
    (add_le_add (hM g hgH x) (le_of_lt (hfg x)))

/-- `a < ε/4`・`b < ε/2`・`c < ε/4` なら `a + b + c < ε`（与える）。 -/
theorem add_three_lt {a b c ε : R} (ha : a < ε / 2 / 2) (hb : b < ε / 2) (hc : c < ε / 2 / 2) :
    a + b + c < ε := by
  have h₁ := add_lt_add ha hc
  rw [add_halves] at h₁
  have h₂ := add_lt_add h₁ hb
  rw [add_halves] at h₂
  have e : a + b + c = a + c + b := by ac_rfl
  rw [e]
  exact h₂

/-- 問題15: 等連続な族の閉包は等連続であることを示せ。 -/
theorem EquicontinuousR.closure {H : Set (X → R)} (h : EquicontinuousR H) :
    EquicontinuousR (closure H) := by
  intro x ε hε
  have hε₂ := half_pos hε
  have hε₄ := half_pos hε₂
  have ⟨U, hU, hxU, hUε⟩ := h x (ε / 2) hε₂
  refine ⟨U, hU, hxU, fun f hf y hy => ?_⟩
  have ⟨g, hgH, hfg⟩ := exists_near_of_mem_closure hf hε₄
  have e₁ := abs_sub_le (f y) (g y) (f x)
  have e₂ := abs_sub_le (g y) (g x) (f x)
  have hgx : abs (g x - f x) < ε / 2 / 2 := by rw [abs_sub_comm]; exact hfg x
  exact lt_of_le_of_lt e₁ (lt_of_le_of_lt (add_le_add_left _ _ e₂ _)
    (by rw [← add_assoc]; exact add_three_lt (hfg y) (hUε g hgH y hy) hgx))

/-- 問題16（実数版 Ascoli の定理、相対コンパクト版）: コンパクト空間上の実数値関数の族が -/
theorem arzela_ascoli_closure [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) : IsCompact (closure H) :=
  arzela_ascoli_closed hH.closure hb.closure (isClosed_closure H)

/-! ## Part G: 点列版 -/

/-- 問題17: コンパクト集合の中の点列は集積点を持つことを示せ。 -/
theorem IsCompact.exists_clusterPt {α : Type} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) {u : Nat → α} (hu : ∀ n, u n ∈ K) :
    ∃ g, g ∈ K ∧ ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U := by
  apply Classical.byContradiction
  intro hno
  have hbad : ∀ g : {g // g ∈ K}, ∃ U, IsOpen U ∧ g.1 ∈ U ∧ ∃ N, ∀ n, N ≤ n → u n ∉ U := by
    intro ⟨g, hg⟩
    apply Classical.byContradiction
    intro h
    exact hno ⟨g, hg, fun U hU hgU N => Classical.byContradiction fun h' =>
      h ⟨U, hU, hgU, N, fun n hn hun => h' ⟨n, hn, hun⟩⟩⟩
  let U := fun g => Classical.choose (hbad g)
  have hU := fun g => Classical.choose_spec (hbad g)
  let N := fun g => Classical.choose (hU g).2.2
  have hN := fun g => Classical.choose_spec (hU g).2.2
  have ⟨J, hJ, hcov⟩ := hK U (fun g => (hU g).1) fun g hg => ⟨⟨g, hg⟩, (hU ⟨g, hg⟩).2.1⟩
  have ⟨P, hP⟩ := hJ.exists_list
  have hsum : ∀ P : List {g // g ∈ K}, ∀ g ∈ P, N g ≤ (P.map N).sum := by
    intro P
    induction P with
    | nil => exact fun _ h => nomatch h
    | cons g P ih =>
      intro g' hg'
      rw [List.map_cons, List.sum_cons]
      cases List.mem_cons.mp hg' with
      | inl e => rw [e]; exact Nat.le_add_right _ _
      | inr e => exact Nat.le_trans (ih g' e) (Nat.le_add_left _ _)
  have ⟨g, hgJ, hug⟩ := hcov (u (P.map N).sum) (hu _)
  exact hN g _ (hsum P g (hP g hgJ)) hug

/-- 問題18: `ε⁻¹ < n` かつ `|d| * n < 1` なら `|d| < ε` であることを示せ。 -/
theorem lt_of_mul_natCast_lt_one {d ε n : R} (hε : 0 < ε) (hn : ε⁻¹ < n)
    (h : abs d * n < 1) : abs d < ε := by
  apply Classical.byContradiction
  intro hd
  have hd := not_lt.mp hd
  have hn0 : 0 ≤ n := le_of_lt (lt_trans (inv_pos hε) hn)
  have h₁ : ε * ε⁻¹ < ε * n := mul_lt_mul_of_pos_left hn hε
  rw [mul_inv_cancel ε (ne_of_lt hε).symm] at h₁
  have h₂ : ε * n ≤ abs d * n := mul_le_mul_of_nonneg_right hd hn0
  exact lt_irrefl (1 : R) (lt_trans (lt_of_lt_of_le h₁ h₂) h)

theorem natCast_succ_pos (k : Nat) : (0 : R) < natCast (k + 1) := by
  rw [natCast_succ]
  exact lt_of_le_of_lt (natCast_nonneg k) (lt_add_of_pos_right _ zero_lt_one)

theorem natCast_le_natCast {m n : Nat} (h : m ≤ n) : (natCast m : R) ≤ natCast n := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, natCast_add]
  have := add_le_add_left _ _ (natCast_nonneg k) (natCast m : R)
  rw [add_zero] at this
  exact this

/-- 近縁 `{(a, b) | |a - b| * (k + 1) < 1}`。 -/
def distInv (k : Nat) : Set (R × R) := {p | abs (p.1 - p.2) * natCast (k + 1) < 1}

theorem distInv_mem (k : Nat) : distInv (R := R) k ∈ 𝓤 R := by
  have hk := natCast_succ_pos (R := R) k
  refine ⟨(natCast (k + 1))⁻¹, inv_pos hk, fun a b h => ?_⟩
  have := mul_lt_mul_of_pos_left h hk
  rw [mul_comm (natCast (k + 1)) (natCast (k + 1))⁻¹, inv_mul_cancel (ne_of_lt hk).symm,
    mul_comm] at this
  exact this

/-- 問題19: 点列の集積点 `g` に一様収束する部分列を作れ。 -/
theorem exists_subseq_tendsto {X : Type} {u : Nat → X → R} {g : X → R}
    (hg : ∀ U, IsOpen U → g ∈ U → ∀ N, ∃ n, N ≤ n ∧ u n ∈ U) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε := by
  have hball : ∀ k N, ∃ n, N ≤ n ∧ ∀ x, abs (g x - u n x) * natCast (k + 1) < 1 := by
    intro k N
    have hV : unifRel (distInv (R := R) k) ∈ 𝓤 (X → R) := ⟨_, distInv_mem k, fun _ h => h⟩
    have ⟨O, hO, hgO, hOV⟩ := exists_open_ball hV g
    have ⟨n, hn, hun⟩ := hg O hO hgO N
    exact ⟨n, hn, hOV _ hun⟩
  let c := fun k N => Classical.choose (hball k N)
  have hc := fun k N => Classical.choose_spec (hball k N)
  let φ : Nat → Nat := fun k => Nat.rec (c 0 0) (fun k n => c (k + 1) (n + 1)) k
  refine ⟨φ, fun k => (hc (k + 1) (φ k + 1)).1, fun ε hε => ?_⟩
  have ⟨N, hN⟩ := exists_nat_gt ε⁻¹
  refine ⟨N, fun k hk x => ?_⟩
  have hφ : ∀ x, abs (g x - u (φ k) x) * natCast (k + 1) < 1 := by
    cases k with
    | zero => exact (hc 0 0).2
    | succ k => exact (hc (k + 1) (φ k + 1)).2
  rw [abs_sub_comm]
  exact lt_of_mul_natCast_lt_one hε
    (lt_of_lt_of_le hN (natCast_le_natCast (Nat.le_succ_of_le hk))) (hφ x)

/-- 問題20（実数版 Ascoli の定理、点列版）: コンパクト空間上の等連続・一様有界な関数族の -/
theorem arzela_ascoli_seq [CompactSpace X] {H : Set (X → R)} (hH : EquicontinuousR H)
    (hb : UniformlyBounded H) {u : Nat → X → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : X → R,
      (∀ x ε, 0 < ε → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, abs (g y - g x) < ε) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε := by
  have ⟨g, hgK, hg⟩ := IsCompact.exists_clusterPt (arzela_ascoli_closure hH hb)
    fun n => subset_closure H _ (hu n)
  have ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto hg
  refine ⟨φ, hφ, g, fun x ε hε => ?_, hconv⟩
  have ⟨U, hU, hxU, hUε⟩ := hH.closure x ε hε
  exact ⟨U, hU, hxU, fun y hy => hUε g hgK y hy⟩

end Dictionary

/-! ## Part H: 閉区間上の関数 -/

/-- 部分空間位相（与える）。 -/
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

/-- 問題21: 閉区間（部分空間）はコンパクト空間であることを示せ。 -/
instance (a b : R) : CompactSpace {x // x ∈ Icc a b} where
  isCompact_univ := by
    intro I W hW hcov
    let U := fun i => Classical.choose (hW i)
    have hU := fun i => Classical.choose_spec (hW i)
    have ⟨J, hJ, hJcov⟩ := isCompact_Icc' a b U (fun i => (hU i).1) fun x hx =>
      have ⟨i, hi⟩ := hcov ⟨x, hx⟩ trivial
      ⟨i, ((hU i).2 ⟨x, hx⟩).mp hi⟩
    refine ⟨J, hJ, fun x _ => ?_⟩
    have ⟨i, hiJ, hi⟩ := hJcov x.1 x.2
    exact ⟨i, hiJ, ((hU i).2 x).mpr hi⟩

/-- 問題22: 古典的な**一様等連続性**（`δ` が点によらない）から、等連続性が出ることを示せ。 -/
theorem equicontinuousR_of_uniform {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε) :
    EquicontinuousR H := by
  intro x ε hε
  have ⟨δ, hδ, hH⟩ := h ε hε
  refine ⟨{y | abs (y.1 - x.1) < δ}, ⟨ball x.1 δ, ?_, fun _ => Iff.rfl⟩, ?_, ?_⟩
  · rw [uniform_topology_eq]; exact isOpen_ball x.1 δ
  · show abs (x.1 - x.1) < δ
    rw [abs_sub_self]; exact hδ
  · exact fun f hf y hy => hH f hf x y hy

/-- 問題23（古典的な Arzelà–Ascoli の定理）: 閉区間上の実数値関数の族が一様有界かつ一様等連続なら、 -/
theorem arzela_ascoli {a b : R} {H : Set ({x // x ∈ Icc a b} → R)}
    (hb : ∃ M, ∀ f ∈ H, ∀ x, abs (f x) ≤ M)
    (heq : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ f ∈ H, ∀ x y : {x // x ∈ Icc a b},
      abs (y.1 - x.1) < δ → abs (f y - f x) < ε)
    {u : Nat → {x // x ∈ Icc a b} → R} (hu : ∀ n, u n ∈ H) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : {x // x ∈ Icc a b} → R,
      ∀ ε, 0 < ε → ∃ N, ∀ k, N ≤ k → ∀ x, abs (u (φ k) x - g x) < ε :=
  have ⟨φ, hφ, g, _, hconv⟩ := arzela_ascoli_seq (equicontinuousR_of_uniform heq) hb hu
  ⟨φ, hφ, g, hconv⟩

#print axioms arzela_ascoli
