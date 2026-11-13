import Polyfold.Chapter14.P3W5T9_TransportProof

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5, pp. 676–677:
the sections `s̃ᵇⱼ = Σ_{a ∈ A} s̃ᵃ_{b,j}` of the proof of Theorem 14.1.9 (2017: §14.5).

# The summed transported sections

## The text, paraphrased

After Proposition 14.5.4 the text sums the transported structures over `a ∈ A`:
`s̃ᵇⱼ = Σ_a s̃ᵃ_{b,j}` on `V̂_b`, a locally finite sum (Lemma 14.5.1 (2)); it extends the boundary
sections (Lemma 14.5.1 (3)) and is compatible with `τ̂` (Proposition 14.5.4 (4)).

## What is formalized (namespace `Polyfold.SBLocalization.AssemblyInput`)

* `AssemblyInput A Λ`: the data of §§14.3–14.5 the assembly uses, over B2's `ZSetup`: GL's
  `TransportInput` with Lemma 14.5.1 (1)–(3) for the cut-offs (`suppInSat`, `locFin`, `sum_one`),
  the values of `τ̂` (finitely many, `G`-equivariant: Proposition 14.3.4), non-empty index sets,
  and the boundary multisection `Λ` represented by the `s⁰ᵇ` (Definition 14.1.3 (3)) and a functor
  over `∂X`.
* `C`: the closed saturated set `⋃_a t(s⁻¹(cl{β_a ≠ 0} ∩ …))` off which all transported
  sections vanish (`isClosed_C`, `isSaturated_C`, `tsec_eq_zero_of_not_mem_C`).
* `usec b j = Σᶠ_a s̃ᵃ_{b,j}` and `ssec σ b j = σ·usec b j` (the cut-off `σ` of the size control is
  folded in here): sc⁺ on `V̂_b` (`isScPlusSectionOn_ssec`), `G_b`-equivariant
  (`ssec_equivariant`), compatible with `τ̂` (`ssec_compat`), `usec b j = s⁰ᵇⱼ` on `V̂_b ∩ ∂X`
  (`usec_boundary`), zero off `C` (`ssec_eq_zero_of_not_mem_C`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid EpGroupoid.ZSetup

variable {A : SEP.{u}}

/-- **The data of the assembly** (§§14.3–14.5, the end of the proof of Theorem 14.1.9, p. 677):
the setting `S` of §14.4 with its transport data `T` (Propositions 14.3.8, 14.4.14 and
Lemma 14.5.1), the facts on `τ̂` of Proposition 14.3.4, Lemma 14.5.1 (1)–(3), and the boundary
multisection `Λ` represented by the boundary sections `s⁰ᵇ` on `V̂_b ∩ ∂X`. -/
structure AssemblyInput (A : SEP.{u}) (Λ : A.W → ℚ≥0) where
  /-- The setting of §14.4. -/
  S : A.X.ZSetup
  /-- The transport data of §14.5. -/
  T : TransportInput A S
  /-- Lemma 14.5.1 (1). -/
  suppInSat : T.SuppInSat
  /-- Lemma 14.5.1 (2): locally only finitely many `β_a` are non-zero. -/
  locFin : ∀ y, ∃ Q : Set A.Obj, IsOpen Q ∧ y ∈ Q ∧ A.X.IsSaturated Q ∧
    {a | a ∈ S.A ∧ ∃ z ∈ Q, T.β a z ≠ 0}.Finite
  /-- Lemma 14.5.1 (3). -/
  sum_one : ∀ y ∈ A.X.PObj.boundary, ∑ᶠ a ∈ S.A, T.β a y = 1
  nonempty_I : ∀ b ∈ S.A, Nonempty (S.I b)
  /-- `τ̂_{b,b'}` has finitely many values on `V̂_{b,b'}` (Proposition 14.3.4). -/
  finite_τ : ∀ b ∈ S.A, ∀ b' ∈ S.A, (S.τ b b' '' A.X.morBetween (S.V b) (S.V b')).Finite
  /-- `τ̂_{b,b'}(g' ∗ φ ∗ g) = g' ∗ τ̂_{b,b'}(φ) ∗ g` (Proposition 14.3.4 (3)). -/
  biact_τ : ∀ b ∈ S.A, ∀ b' ∈ S.A, ∀ φ ∈ A.X.morBetween (S.V b) (S.V b'), ∀ g' g,
    S.τ b b' (EpGroupoid.biact (S.nbhd b) (S.nbhd b') g' φ g) =
      IndexCorr.biact g' (S.τ b b' φ) g
  /-- Definition 14.1.3 (3): the `s⁰ᵇ` represent `Λ` over `V̂_b ∩ ∂X`. -/
  rep : ∀ b ∈ S.A, ∀ w, A.P w ∈ S.V b ∩ A.X.PObj.boundary →
    Λ w = (Fintype.card (S.I b) : ℚ≥0)⁻¹ *
      ((Finset.univ.filter fun j => T.s0 b j (A.P w) = w).card : ℚ≥0)
  /-- `Λ` is a functor over `∂X`. -/
  functor : ∀ (φ : A.Mor) (w : A.W), A.P w = A.X.src φ → A.X.src φ ∈ A.X.PObj.boundary →
    Λ (fibAct φ w) = Λ w

namespace AssemblyInput

variable {Λ : A.W → ℚ≥0} (D : AssemblyInput A Λ)

/-! ### The transported sections are sections -/

theorem P_tsec (a b : A.Obj) (j : D.S.I b) (y : A.Obj) : A.P (D.T.tsec a b j y) = y := by
  unfold TransportInput.tsec
  split_ifs with h
  · rw [P_fibAct (D.T.isSection_bsec _ _ _)]
    exact h.choose_spec.2
  · exact proj_fiberZero A.P y

/-! ### The closed set off which the sections vanish -/

/-- `K_a = cl{y ∈ Ũ(a) | β_a(y) ≠ 0} ⊆ V̂_a` (14.53). -/
def K (a : A.Obj) : Set A.Obj := closure {y ∈ (D.S.nbhd a).U | D.T.β a y ≠ 0}

/-- `C = ⋃_a t(s⁻¹(K_a))`. -/
def C : Set A.Obj := ⋃ a : D.S.A, A.X.tgt '' (A.X.src ⁻¹' D.K a)

theorem isClosed_sat_K {a : A.Obj} (ha : a ∈ D.S.A) :
    IsClosed (A.X.tgt '' (A.X.src ⁻¹' D.K a)) :=
  isClosed_image_preimage_of_isProperMap_domRestrict (D.T.proper a ha)
    (closure_mono (sep_subset _ _)) (isClosed_closure.preimage A.X.continuous_src)

theorem locallyFinite_sat_K :
    LocallyFinite fun a : D.S.A => A.X.tgt '' (A.X.src ⁻¹' D.K a) := by
  intro y
  obtain ⟨Q, hQo, hyQ, hQs, hfin⟩ := D.locFin y
  refine ⟨Q, hQo.mem_nhds hyQ, (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
  rintro ⟨a, ha⟩ ⟨z, ⟨φ, hφ, rfl⟩, hzQ⟩
  have hsQ : A.X.src φ ∈ Q := by
    have := A.X.isSaturated_iff.1 hQs (A.X.inv φ) (by rw [A.X.src_inv]; exact hzQ)
    rwa [A.X.tgt_inv] at this
  obtain ⟨z', hz'Q, hz'⟩ := mem_closure_iff.1 hφ Q hQo hsQ
  exact ⟨ha, z', hz'Q, hz'.2⟩

theorem isClosed_C : IsClosed D.C :=
  D.locallyFinite_sat_K.isClosed_iUnion fun a => D.isClosed_sat_K a.2

theorem isSaturated_C : A.X.IsSaturated D.C := by
  refine A.X.isSaturated_iff.2 fun ψ h => ?_
  obtain ⟨_, ⟨a, rfl⟩, φ, hφ, e⟩ := h
  have hc : A.X.src ψ = A.X.tgt φ := e.symm
  refine mem_iUnion.2 ⟨a, A.X.comp ψ φ, ?_, A.X.tgt_comp _ _ hc⟩
  change A.X.src (A.X.comp ψ φ) ∈ D.K a
  rw [A.X.src_comp _ _ hc]; exact hφ

theorem K_subset {a : A.Obj} (ha : a ∈ D.S.A) : D.K a ⊆ D.S.V a := D.T.closure_support_β a ha

/-- Off `C`, every transported section vanishes. -/
theorem tsec_eq_zero_of_not_mem_C {a : A.Obj} (ha : a ∈ D.S.A) {b : A.Obj} (j : D.S.I b)
    {y : A.Obj} (hy : y ∉ D.C) : D.T.tsec a b j y = fiberZero A.P y := by
  by_cases h : ∃ p : D.S.I a × A.Mor, D.S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = y
  · obtain ⟨⟨i, φ⟩, hp, rfl⟩ := h
    have hs := hp.props.2.2.1
    have hβ0 : D.T.β a (A.X.src φ) = 0 := by
      by_contra hne
      exact hy (mem_iUnion.2 ⟨⟨a, ha⟩, φ,
        subset_closure ⟨D.S.V_subset a ha hs, hne⟩, rfl⟩)
    rw [D.T.tsec_of_arc hp, D.T.bsec_of_eq_zero a i hβ0, fibAct_fiberZero rfl rfl]
  · exact D.T.tsec_of_not h

/-! ### Local finiteness -/

/-- Near every point only finitely many `a` contribute. -/
theorem exists_finite_tsec (y₀ : A.Obj) : ∃ Q : Set A.Obj, IsOpen Q ∧ y₀ ∈ Q ∧
    ∃ F : Finset D.S.A, ∀ a : D.S.A, a ∉ F → ∀ b (j : D.S.I b), ∀ y ∈ Q,
      D.T.tsec a b j y = fiberZero A.P y := by
  obtain ⟨Q, hQo, hyQ, hQs, hfin⟩ := D.locFin y₀
  have hfin' : {a : D.S.A | a.1 ∈ D.S.A ∧ ∃ z ∈ Q, D.T.β a z ≠ 0}.Finite :=
    hfin.preimage Subtype.val_injective.injOn
  refine ⟨Q, hQo, hyQ, hfin'.toFinset, fun a ha b j y hy => ?_⟩
  have hnot : ∀ z ∈ Q, D.T.β a z = 0 := fun z hz => by
    by_contra hne
    exact ha (hfin'.mem_toFinset.2 ⟨a.2, z, hz, hne⟩)
  by_cases h : ∃ p : D.S.I a × A.Mor, D.S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = y
  · obtain ⟨⟨i, φ⟩, hp, rfl⟩ := h
    have hsQ : A.X.src φ ∈ Q := by
      have := A.X.isSaturated_iff.1 hQs (A.X.inv φ) (by rw [A.X.src_inv]; exact hy)
      rwa [A.X.tgt_inv] at this
    rw [D.T.tsec_of_arc hp, D.T.bsec_of_eq_zero a i (hnot _ hsQ), fibAct_fiberZero rfl rfl]
  · exact D.T.tsec_of_not h

/-! ### The summed sections -/

/-- The fibre value `Σᶠ_a s̃ᵃ_{b,j}(y)`. -/
def sumFib (b : A.Obj) (j : D.S.I b) (y : A.Obj) : A.P ⁻¹' {y} :=
  ∑ᶠ a : D.S.A, (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y})

/-- **`s̃ᵇⱼ = Σ_a s̃ᵃ_{b,j}`.** -/
def usec (b : A.Obj) (j : D.S.I b) (y : A.Obj) : A.W := (D.sumFib b j y : A.W)

theorem isSection_usec (b : A.Obj) (j : D.S.I b) : IsSection A.P (D.usec b j) :=
  fun y => (D.sumFib b j y).2

theorem support_subset {Q : Set A.Obj} {F : Finset D.S.A}
    (hF : ∀ a : D.S.A, a ∉ F → ∀ b (j : D.S.I b), ∀ y ∈ Q, D.T.tsec a b j y = fiberZero A.P y)
    {b : A.Obj} (j : D.S.I b) {y : A.Obj} (hy : y ∈ Q) :
    (support fun a : D.S.A => (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y})) ⊆ F := by
  intro a ha
  by_contra haF
  exact ha (Subtype.ext (hF a haF b j y hy))

theorem finite_support (b : A.Obj) (j : D.S.I b) (y : A.Obj) :
    (support fun a : D.S.A => (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y})).Finite := by
  obtain ⟨Q, -, hyQ, F, hF⟩ := D.exists_finite_tsec y
  exact F.finite_toSet.subset (D.support_subset hF j hyQ)

theorem usec_eq_sectionSum {Q : Set A.Obj} {F : Finset D.S.A}
    (hF : ∀ a : D.S.A, a ∉ F → ∀ b (j : D.S.I b), ∀ y ∈ Q, D.T.tsec a b j y = fiberZero A.P y)
    {b : A.Obj} (j : D.S.I b) {y : A.Obj} (hy : y ∈ Q) :
    D.usec b j y = sectionSum A.P F (fun a : D.S.A => D.T.tsec a b j) y := by
  rw [sectionSum_apply (s := fun a : D.S.A => D.T.tsec a b j) fun a => D.P_tsec a b j, usec, sumFib,
    finsum_eq_sum_of_support_subset _ (D.support_subset hF j hy)]

theorem isScPlusSectionOn_usec {b : A.Obj} (hb : b ∈ D.S.A) (j : D.S.I b) :
    IsScPlusSectionOn A (D.usec b j) (D.S.V b) := by
  refine IsScPlusSectionOn.of_locally (D.T.isOpen_V b hb) fun y hy => ?_
  obtain ⟨Q, hQo, hyQ, F, hF⟩ := D.exists_finite_tsec y
  have hO := hQo.inter (D.T.isOpen_V b hb)
  refine ⟨Q ∩ D.S.V b, hO, ⟨hyQ, hy⟩, inter_subset_right, ?_⟩
  exact (isScPlusSectionOn_sectionSum F hO
    (fun a => (D.T.isScPlusSectionOn_tsec a.2 hb j).mono hO inter_subset_right)
    fun a => D.P_tsec a b j).congr fun z hz => (D.usec_eq_sectionSum hF j hz.1).symm

/-- `Σᶠ` commutes with `μ(φ, ·)` (the summands being related termwise). -/
theorem usec_fibAct {b b' : A.Obj} {j : D.S.I b} {j' : D.S.I b'} {φ : A.Mor}
    (h : ∀ a : D.S.A, D.T.tsec a b' j' (A.X.tgt φ) = fibAct φ (D.T.tsec a b j (A.X.src φ))) :
    D.usec b' j' (A.X.tgt φ) = fibAct φ (D.usec b j (A.X.src φ)) :=
  (fibAct_finsum rfl rfl (D.finite_support b j _) fun a => h a).symm

/-- **`G_b`-equivariance of `s̃ᵇ`.** -/
theorem usec_equivariant {b : A.Obj} (hb : b ∈ D.S.A) (g : A.X.Isotropy b) (j : D.S.I b)
    {y : A.Obj} (hy : y ∈ D.S.V b) :
    D.usec b (g • j) ((D.S.nbhd b).rep.Φ g y) =
      fibAct ((D.S.nbhd b).rep.Γ g y) (D.usec b j y) := by
  have hyU := D.S.V_subset b hb hy
  have h := D.usec_fibAct (b := b) (b' := b) (j := j) (j' := g • j)
    (φ := (D.S.nbhd b).rep.Γ g y) fun a => by
      rw [(D.S.nbhd b).tgt_Γ g hyU, (D.S.nbhd b).src_Γ g hyU]
      exact D.T.tsec_equivariant hb g j hy
  rwa [(D.S.nbhd b).tgt_Γ g hyU, (D.S.nbhd b).src_Γ g hyU] at h

/-- **Compatibility of `s̃ᵇ` with `τ̂`** (Proposition 14.5.4 (4), summed over `a`). -/
theorem usec_compat {b b' : A.Obj} (hb : b ∈ D.S.A) (hb' : b' ∈ D.S.A) {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (D.S.V b) (D.S.V b')) :
    (D.S.τ b b' φ).Sat fun j j' => D.usec b' j' (A.X.tgt φ) = fibAct φ (D.usec b j (A.X.src φ)) :=
  IndexCorr.sat_of_pairs_t9 _ fun _ _ hp => D.usec_fibAct fun _ =>
    IndexCorr.rel_of_sat_t9 (D.T.tsec_compat hb hb' hφ) hp

/-- **`s̃ᵇⱼ = s⁰ᵇⱼ` on `V̂_b ∩ ∂X`** (Proposition 14.5.4 (3) and `Σ_a β_a = 1` on `∂X`). -/
theorem usec_boundary {b : A.Obj} (hb : b ∈ D.S.A) (j : D.S.I b) {y : A.Obj}
    (hy : y ∈ D.S.V b ∩ A.X.PObj.boundary) : D.usec b j y = D.T.s0 b j y := by
  have hPs0 : A.P (D.T.s0 b j y) = y := by
    rw [← D.T.sh_boundary b hb j y hy]
    exact (D.T.isScPlusSectionOn_sh b hb j).1 y hy.1
  have hterm : ∀ a : D.S.A, (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y}) =
      D.T.β a y • (⟨D.T.s0 b j y, hPs0⟩ : A.P ⁻¹' {y}) := fun a => by
    refine Subtype.ext ?_
    change D.T.tsec a b j y =
      ((D.T.β a y • (⟨D.T.s0 b j y, hPs0⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W)
    rw [D.T.tsec_boundary D.suppInSat a.2 hb j hy]
    unfold Polyfold.sectionSmul
    rw [dif_pos hPs0]
  have hβfin : (support fun a : D.S.A => D.T.β a y).Finite := by
    obtain ⟨Q, -, hyQ, -, hfin⟩ := D.locFin y
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun a ha => ⟨a.2, y, hyQ, ha⟩
  have hsum : ∑ᶠ a : D.S.A, D.T.β a y = 1 := by
    rw [← D.sum_one y hy.2]
    exact finsum_subtype_eq_finsum_cond (f := fun a => D.T.β a y) (· ∈ D.S.A)
  change ((∑ᶠ a : D.S.A, (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y}) :
    A.P ⁻¹' {y}) : A.W) = D.T.s0 b j y
  rw [finsum_congr hterm, ← finsum_smul' hβfin, hsum, one_smul]

/-! ### The cut-off `σ` -/

/-- **`σ·s̃ᵇⱼ`**, with an sc-smooth functor `σ` (the cut-off of the size control). -/
def ssec (σ : A.Obj → ℝ) (b : A.Obj) (j : D.S.I b) : A.Obj → A.W :=
  Polyfold.sectionSmul A.P σ (D.usec b j)

theorem isSection_ssec (σ : A.Obj → ℝ) (b : A.Obj) (j : D.S.I b) :
    IsSection A.P (D.ssec σ b j) := (D.isSection_usec b j).sectionSmul

theorem isScPlusSectionOn_ssec {σ : A.Obj → ℝ} (hσ : A.X.PObj.IsScSmoothMap realPolyfold σ)
    {b : A.Obj} (hb : b ∈ D.S.A) (j : D.S.I b) :
    IsScPlusSectionOn A (D.ssec σ b j) (D.S.V b) :=
  (D.isScPlusSectionOn_usec hb j).sectionSmul (D.T.isOpen_V b hb) (D.isSection_usec b j) hσ

theorem fibAct_ssec {σ : A.Obj → ℝ} (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ))
    {b b' : A.Obj} {j : D.S.I b} {j' : D.S.I b'} {φ : A.Mor}
    (h : D.usec b' j' (A.X.tgt φ) = fibAct φ (D.usec b j (A.X.src φ))) :
    D.ssec σ b' j' (A.X.tgt φ) = fibAct φ (D.ssec σ b j (A.X.src φ)) :=
  (fibAct_sectionSmul (D.isSection_usec b j) (D.isSection_usec b' j') rfl rfl (hσt φ) h).symm

theorem ssec_equivariant {σ : A.Obj → ℝ} (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ))
    {b : A.Obj} (hb : b ∈ D.S.A) (g : A.X.Isotropy b) (j : D.S.I b) {y : A.Obj}
    (hy : y ∈ D.S.V b) :
    D.ssec σ b (g • j) ((D.S.nbhd b).rep.Φ g y) =
      fibAct ((D.S.nbhd b).rep.Γ g y) (D.ssec σ b j y) := by
  have hyU := D.S.V_subset b hb hy
  have h := D.fibAct_ssec hσt (b := b) (b' := b) (j := j) (j' := g • j)
    (φ := (D.S.nbhd b).rep.Γ g y) (by
      rw [(D.S.nbhd b).tgt_Γ g hyU, (D.S.nbhd b).src_Γ g hyU]
      exact D.usec_equivariant hb g j hy)
  rwa [(D.S.nbhd b).tgt_Γ g hyU, (D.S.nbhd b).src_Γ g hyU] at h

theorem ssec_compat {σ : A.Obj → ℝ} (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ))
    {b b' : A.Obj} (hb : b ∈ D.S.A) (hb' : b' ∈ D.S.A) {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (D.S.V b) (D.S.V b')) :
    (D.S.τ b b' φ).Sat fun j j' =>
      D.ssec σ b' j' (A.X.tgt φ) = fibAct φ (D.ssec σ b j (A.X.src φ)) :=
  IndexCorr.sat_of_pairs_t9 _ fun _ _ hp =>
    D.fibAct_ssec hσt (IndexCorr.rel_of_sat_t9 (D.usec_compat hb hb' hφ) hp)

theorem usec_eq_zero_of_not_mem_C {b : A.Obj} (j : D.S.I b) {y : A.Obj} (hy : y ∉ D.C) :
    D.usec b j y = fiberZero A.P y := by
  change ((∑ᶠ a : D.S.A, (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y}) :
    A.P ⁻¹' {y}) : A.W) = fiberZero A.P y
  have h : ∀ a : D.S.A, (⟨D.T.tsec a b j y, D.P_tsec a b j y⟩ : A.P ⁻¹' {y}) = 0 :=
    fun a => Subtype.ext (D.tsec_eq_zero_of_not_mem_C a.2 j hy)
  rw [finsum_congr h, finsum_zero]
  rfl

theorem ssec_eq_zero_of_not_mem_C (σ : A.Obj → ℝ) {b : A.Obj} (j : D.S.I b) {y : A.Obj}
    (hy : y ∉ D.C) : D.ssec σ b j y = fiberZero A.P y := by
  unfold ssec
  rw [sectionSmul_congr_t9 (D.usec_eq_zero_of_not_mem_C j hy)]
  unfold Polyfold.sectionSmul
  rw [dif_pos (proj_fiberZero A.P y)]
  have e : (⟨fiberZero A.P y, proj_fiberZero A.P y⟩ : A.P ⁻¹' {y}) = 0 := rfl
  rw [e, smul_zero]
  rfl

theorem ssec_eq_zero_of_σ {σ : A.Obj → ℝ} {b : A.Obj} (j : D.S.I b) {y : A.Obj}
    (hσ : σ y = 0) : D.ssec σ b j y = fiberZero A.P y :=
  sectionSmul_of_eq_zero_t9 (D.isSection_usec b j y) hσ

end AssemblyInput

end SBLocalization

end Polyfold
