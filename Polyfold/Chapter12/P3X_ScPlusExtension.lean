import Polyfold.Chapter12.P3S_ScPlusSectionFunctor
import Polyfold.Chapter5.P3B_BoundaryExtension2021
import Polyfold.Chapter8.NonVacuityBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §12.3,
pp. 584 and 586–587: **Definition 12.3.6** on ep-groupoids (2017: Definition 12.8) and
**Theorem 12.3.9** (extension of sc⁺-section functors; 2017: Theorem 12.8).

# Extension of sc⁺-section functors from the boundary

## The text, paraphrased

(Definition 12.3.6) For a strong bundle `(P : W → X, μ)` over a tame ep-groupoid, a map
`s : ∂X → W` with `P ∘ s = Id` is an sc⁺-section over the boundary if its restriction to every
local face at every `x ∈ ∂X` is an sc⁺-section.  (Theorem 12.3.9) Let `|X|` be paracompact and let
the ep-groupoid admit sc-smooth partitions of unity.  An sc⁺-section functor `s` of `W|∂X` and a
saturated open neighbourhood `U` of `∂X` give an sc⁺-section functor `s̃` of `P`, supported in
`U`, with `s̃|∂X = s`; if an auxiliary norm `N` and `δ > 0` with `N(s(x)) < δ` on `∂X` are given,
`s̃` can be chosen with `N(s̃(x)) ≤ δ` everywhere.  *Proof*: Corollary 12.3.8 near each `x ∈ ∂X`,
extended to the saturation; an sc-smooth partition of unity for the cover by these saturations and
`X ∖ ∂X`; `s̃ = Σ β_x s̃_x`.  For the bound, a bump function `β = 1` on `∂X` supported where
`N(s̃) < δ`, and `β · s̃`.

## What is formalized (namespace `Polyfold.EpStrongBundle`)

* **Definition 12.3.6** (the ep-groupoid form, gap G.137): `IsBoundaryScPlusSection`, the
  M-polyfold form of Definition 5.4.1 (`StrongBundle.IsBoundaryScPlusSection`) on the object
  M-polyfold; it does not involve `μ`.  The "sc⁺-section functor of `W|∂X`" of Theorem 12.3.9 is
  `IsBoundaryScPlusSectionFunctor`: in addition `s(t φ) = μ(φ, s(s φ))` for every morphism `φ`
  with `s(φ) ∈ ∂X` (then `t(φ) ∈ ∂X` too, `tgt_mem_boundary_iff_p3x`).  **Nonvacuity**:
  `isBoundaryScPlusSectionFunctor_fiberZero`.
* The ep-level bump functions from partitions of unity:
  `admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity` (Definition 7.5.5 ⇒ Definition 12.3.1).
* **The local step** `exists_local_functor_extension`: near `x ∈ ∂X`, Part I's local extension
  (`StrongBundle.exists_local_extension`, which is Proposition 12.3.7 in a tame chart) cut off
  inside an invariant `V(x)`, averaged over `G_x` (`exists_equivariant_average_p3x`, the
  averaging of Corollary 12.3.8 in the natural representation), and extended to the saturation
  (`remark_12_3_5`).  The average still extends `s` because `s` is functorial on `∂X`.
* **The gluing** `glueSection P ρ σ = Σ_i ρ_i σ_i` for a partition of unity, with
  `isScPlusSectionFunctor_glueSection` (functorial if the `ρ_i` are constant along morphisms).
* **Theorem 12.3.9**: `theorem_12_3_9`, both statements; the cores
  `exists_extension_of_tameCharts` and `exists_extension_bounded_of_tameCharts` (any universe,
  with "every point lies in a tame strong bundle chart" in place of `IsTameBundle`).
* **Satisfiability** of all hypotheses of Theorem 12.3.9: `theorem_12_3_9_hypotheses_rn` (the
  trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`, the zero section, `U = X`).

## Reading

* "A strong bundle over the tame ep-groupoid" is `B.IsTameBundle` for the object strong bundle
  (its first component is `X.IsTame = X.PObj.IsTame`), as in Theorem 5.4.2 (`theorem_5_4_2`).
* "The ep-groupoid admits sc-smooth partitions of unity" is Definition 7.5.5,
  `X.HasScPartitionsOfUnity`.  The paracompactness of `|X|` is kept (`_hpara`) but not used: the
  partitions of unity are a hypothesis.
* "Supported in `U`" is `sectionSupport P s̃ ⊆ U` (the closure of `{s̃ ≠ 0}`).
* The local step at `x ∈ ∂X` uses Corollary 12.3.8 in the form of an average of the
  `G_x`-translates in the natural representation (the formula of its proof) rather than the
  chart-level `corollary_12_3_8` with a `LocalBundleAction`; the two are the same construction.
* For the bound the text takes a second neighbourhood `V'` with `cl V' ⊆ V`; the two-set cover
  `{V, X ∖ ∂X}` already gives `β` with `supp β ⊆ V` and `β = 1` on `∂X`, so `V'` is not needed.
-/

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### The boundary of the object space is saturated -/

section Boundary

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace EpGroupoid

/-- `t(φ) ∈ ∂X ⟺ s(φ) ∈ ∂X` (`d_X(t φ) = d_𝐗(φ) = d_X(s φ)`). -/
theorem tgt_mem_boundary_iff_p3x (φ : Mor) :
    X.tgt φ ∈ X.PObj.boundary ↔ X.src φ ∈ X.PObj.boundary := by
  change 1 ≤ X.PObj.degIndex (X.tgt φ) ↔ 1 ≤ X.PObj.degIndex (X.src φ)
  rw [← X.degIndex_tgt φ, X.degIndex_src φ]

/-- `X ∖ ∂X` is saturated. -/
theorem isSaturated_compl_boundary_p3x : X.IsSaturated X.PObj.boundaryᶜ :=
  X.isSaturated_iff.2 fun φ h ht => h ((tgt_mem_boundary_iff_p3x φ).1 ht)

/-- The complement of a saturated set is saturated. -/
theorem isSaturated_compl_p3x {A : Set Obj} (hA : X.IsSaturated A) : X.IsSaturated Aᶜ := by
  refine X.isSaturated_iff.2 fun φ h ht => h ?_
  have := (X.isSaturated_iff.1 hA) (X.inv φ) (by rwa [X.src_inv])
  rwa [X.tgt_inv] at this

/-- Saturation is monotone. -/
theorem saturation_mono_p3x {A A' : Set Obj} (h : A ⊆ A') : X.saturation A ⊆ X.saturation A' :=
  preimage_mono (image_mono h)

omit [T2Space Obj] [ParacompactSpace Obj] in
/-- For a partition of unity indexed by `ULift Bool`, `ρ_true = 1` where `ρ_false = 0`. -/
theorem partitionOfUnity_true_eq_one_p3x {ρ : PartitionOfUnity (ULift.{u} Bool) Obj} {y : Obj}
    (h : ρ ⟨false⟩ y = 0) : ρ ⟨true⟩ y = 1 := by
  have hsum := ρ.sum_eq_one (mem_univ y)
  have hs : ∀ i, i ≠ (⟨true⟩ : ULift.{u} Bool) → ρ i y = 0 := by
    rintro ⟨_ | _⟩ hi
    · exact h
    · exact absurd rfl hi
  rwa [finsum_eq_single _ _ hs] at hsum

/-- **Definition 7.5.5 implies Definition 12.3.1** (pointwise reading): an ep-groupoid admitting
sc-smooth partitions of unity admits sc-smooth bump functions (the function attached to `U` of a
partition of unity for the cover `{U, X ∖ sat(cl V(x))}`). -/
theorem admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity (hpu : X.HasScPartitionsOfUnity) :
    X.AdmitsBumpFunctionsPointwise := by
  classical
  intro x U hU hsat hx
  obtain ⟨R, V, -, hxV, -, hVcl, hRU, hprop⟩ := exists_invariant_nhds_of_isOpen X x hU hx
  set K := X.saturation (closure V)
  have hKc : IsClosed K := X.isClosed_saturation_of_isProperSubset hprop
  have hKU : K ⊆ U := saturation_subset_of_isSaturated hsat (hVcl.trans hRU)
  have hxK : x ∈ K := X.subset_saturation _ (subset_closure hxV)
  let c : ULift.{u} Bool → Set Obj := fun i => bif i.down then U else Kᶜ
  obtain ⟨ρ, hρsub, hρsm, -, hρinv⟩ := hpu _ c
    (fun i => by rcases i with ⟨_ | _⟩; exacts [hKc.isOpen_compl, hU])
    (fun i => by
      rcases i with ⟨_ | _⟩
      exacts [isSaturated_compl_p3x (isSaturated_saturation X _), hsat])
    (iUnion_eq_univ_iff.2 fun y => if hy : y ∈ U then ⟨⟨true⟩, hy⟩ else
      ⟨⟨false⟩, fun hK => hy (hKU hK)⟩)
  refine ⟨ρ ⟨true⟩, hρsm _, ?_, hρsub ⟨true⟩, hρinv _⟩
  have h0 : ρ ⟨false⟩ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hρsub ⟨false⟩ h hxK
  rw [partitionOfUnity_true_eq_one_p3x h0]
  exact one_ne_zero

end EpGroupoid

end Boundary

/-! ### Sections: support lemmas and the glued section -/

section Sections

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
/-- `supp(f · σ) ⊆ supp f`. -/
theorem sectionSupport_sectionSmul_subset_tsupport_p3x {f : Obj → ℝ} {σ : Obj → W}
    (hσ : IsSection P σ) : sectionSupport P (sectionSmul P f σ) ⊆ tsupport f :=
  closure_mono fun y hy h0 => hy (by rw [sectionSmul_apply hσ, h0, zero_smul]; rfl)

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
/-- `supp(f · σ) ⊆ supp σ`. -/
theorem sectionSupport_sectionSmul_subset_p3x {f : Obj → ℝ} {σ : Obj → W}
    (hσ : IsSection P σ) : sectionSupport P (sectionSmul P f σ) ⊆ sectionSupport P σ := by
  refine closure_mono fun y hy h0 => hy ?_
  have h1 : (⟨σ y, hσ y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext h0
  rw [sectionSmul_apply hσ, h1, smul_zero]
  rfl

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The zero section has empty support. -/
theorem sectionSupport_fiberZero_p3x : sectionSupport P (fiberZero P) = ∅ := by
  simp [sectionSupport]

variable {ι : Type*}

open scoped Classical in
variable (P) in
/-- The glued section `Σ_i ρ_i σ_i` of a partition of unity `(ρ_i)` and sections `σ_i` (a
locally finite sum in the fibres; junk if some `σ_i` is not a section at `y`). -/
def glueSection (ρ : PartitionOfUnity ι Obj) (σ : ι → Obj → W) (y : Obj) : W :=
  if h : ∀ i, P (σ i y) = y then ((∑ᶠ i, ρ i y • (⟨σ i y, h i⟩ : P ⁻¹' {y}) : P ⁻¹' {y}) : W)
  else fiberZero P y

variable {ρ : PartitionOfUnity ι Obj} {σ : ι → Obj → W}

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
theorem glueSection_apply (hσ : ∀ i, IsSection P (σ i)) (y : Obj) :
    glueSection P ρ σ y = ((∑ᶠ i, ρ i y • (⟨σ i y, hσ i y⟩ : P ⁻¹' {y}) : P ⁻¹' {y}) : W) := by
  rw [glueSection, dif_pos fun i => hσ i y]

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
theorem isSection_glueSection (hσ : ∀ i, IsSection P (σ i)) :
    IsSection P (glueSection P ρ σ) := fun y => by
  rw [glueSection_apply hσ]
  exact (∑ᶠ i, ρ i y • (⟨σ i y, hσ i y⟩ : P ⁻¹' {y})).2

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
/-- On a finite set containing the support of `(ρ_i(y))_i` the glued sum is a finite sum. -/
theorem glueSection_finsum_eq_sum (hσ : ∀ i, IsSection P (σ i)) (y : Obj) (I : Finset ι)
    (hI : support (ρ · y) ⊆ I) :
    (∑ᶠ i, ρ i y • (⟨σ i y, hσ i y⟩ : P ⁻¹' {y})) =
      ∑ i ∈ I, ρ i y • (⟨σ i y, hσ i y⟩ : P ⁻¹' {y}) :=
  finsum_eq_sum_of_support_subset _ fun i hi => hI fun h => hi (by
    have h' : ρ i y = 0 := h
    simp only [h', zero_smul])

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
/-- The glued section is `w` at `y` if every `σ_i` with `y ∈ supp ρ_i` is `w` at `y`. -/
theorem glueSection_eq_of (hσ : ∀ i, IsSection P (σ i)) {y : Obj} {w : W} (hw : P w = y)
    (h : ∀ i, y ∈ tsupport (ρ i) → σ i y = w) : glueSection P ρ σ y = w := by
  obtain ⟨I, hI⟩ := ρ.exists_finset_nhds y
  obtain ⟨hI1, hIs⟩ := hI.self_of_nhds
  rw [glueSection_apply hσ, glueSection_finsum_eq_sum hσ y I hIs]
  have : ∑ i ∈ I, ρ i y • (⟨σ i y, hσ i y⟩ : P ⁻¹' {y}) =
      ∑ i ∈ I, ρ i y • (⟨w, hw⟩ : P ⁻¹' {y}) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hρ : ρ i y = 0
    · rw [hρ, zero_smul, zero_smul]
    · congr 2
      exact h i (subset_tsupport _ hρ)
  rw [this, ← Finset.sum_smul, hI1, one_smul]

omit [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
/-- The support of the glued section lies in the closed set `⋃_i (supp ρ_i ∩ supp σ_i)`. -/
theorem sectionSupport_glueSection_subset (hσ : ∀ i, IsSection P (σ i)) :
    sectionSupport P (glueSection P ρ σ) ⊆ ⋃ i, tsupport (ρ i) ∩ sectionSupport P (σ i) := by
  have hcl : IsClosed (⋃ i, tsupport (ρ i) ∩ sectionSupport P (σ i)) :=
    (ρ.locallyFinite_tsupport.subset fun i => inter_subset_left).isClosed_iUnion
      fun i => (isClosed_tsupport _).inter isClosed_closure
  refine closure_minimal (fun y hy => ?_) hcl
  by_contra hno
  apply hy
  rw [glueSection_apply hσ]
  have h0 : ∀ i, ρ i y • (⟨σ i y, hσ i y⟩ : P ⁻¹' {y}) = 0 := fun i => by
    by_cases hρ : ρ i y = 0
    · rw [hρ, zero_smul]
    · have hσ0 : σ i y = fiberZero P y := by
        by_contra hne
        exact hno (mem_iUnion.2 ⟨i, subset_tsupport _ hρ, subset_closure hne⟩)
      rw [show (⟨σ i y, hσ i y⟩ : P ⁻¹' {y}) = 0 from Subtype.ext hσ0, smul_zero]
  rw [finsum_eq_zero_of_forall_eq_zero h0]
  rfl

/-- The glued section of sc⁺-sections with an sc-smooth partition of unity is an sc⁺-section. -/
theorem isScPlusSection_glueSection (hρsm : X.PObj.IsScSmoothPartitionOfUnity ρ)
    (hσ : ∀ i, B.IsScPlusSection (σ i)) : B.IsScPlusSection (glueSection P ρ σ) := by
  have hsec : ∀ i, IsSection P (σ i) := fun i => (hσ i).1
  have hloc : ∀ y (I : Finset ι), support (ρ · y) ⊆ I →
      glueSection P ρ σ y = sectionSum P I (fun i => sectionSmul P (ρ i) (σ i)) y :=
    fun y I hI => by
      rw [sectionSum_apply (fun i => (hsec i).sectionSmul), glueSection_apply hsec,
        glueSection_finsum_eq_sum hsec y I hI]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Subtype.ext ?_
      exact (sectionSmul_apply (hsec i) y).symm
  refine StrongBundle.isScPlusSection_of_locally (isSection_glueSection hsec) fun y₀ => ?_
  obtain ⟨I, hI⟩ := ρ.exists_finset_nhds y₀
  obtain ⟨t, ht, hto, hy₀t⟩ := eventually_nhds_iff.1 hI
  have hsum : B.IsScPlusSection (sectionSum P I fun i => sectionSmul P (ρ i) (σ i)) :=
    StrongBundle.isScPlusSection_sectionSum I fun i => (hσ i).smul_left (hρsm i)
  obtain ⟨-, G, hG, hGs⟩ := (B.isScPlusSection_iff _).1 hsum
  exact ⟨t, hto, hy₀t, G, hGs.mono hto (subset_univ _), fun y hy =>
    (congrFun hG y).trans (hloc y I (ht y hy).2).symm⟩

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-! ### Definition 12.3.6 on ep-groupoids -/

/-- **Definition 12.3.6, p. 584** (2017: Definition 12.8), the ep-groupoid form: `s` is an
**sc⁺-section over the boundary** of the strong bundle `(P : W → X, μ)` if it is one of the object
strong bundle (Definition 5.4.1, `StrongBundle.IsBoundaryScPlusSection`: on `∂X` a section with
values in `W_{0,1}`, sc⁺ on every local face germ at every `x ∈ ∂X`, in every tame chart).  The
definition does not involve `μ`. -/
def IsBoundaryScPlusSection (_E : EpStrongBundle X B) (s : Obj → W) : Prop :=
  B.IsBoundaryScPlusSection s

/-- An **sc⁺-section functor of `W|∂X`** (Theorem 12.3.9): an sc⁺-section over the boundary
(Definition 12.3.6) with `s(t φ) = μ(φ, s(s φ))` for every morphism `φ` between boundary points
(`s(φ) ∈ ∂X` forces `t(φ) ∈ ∂X`, `tgt_mem_boundary_iff_p3x`). -/
def IsBoundaryScPlusSectionFunctor (s : Obj → W) : Prop :=
  E.IsBoundaryScPlusSection s ∧ ∀ φ : Mor, X.src φ ∈ X.PObj.boundary →
    ∀ h : P (s (X.src φ)) = X.src φ, s (X.tgt φ) = E.μ ⟨(φ, s (X.src φ)), h⟩

variable {E}

/-- **Nonvacuity of Definition 12.3.6 and of `IsBoundaryScPlusSectionFunctor`**: the zero section
(for every strong bundle over an ep-groupoid). -/
theorem isBoundaryScPlusSectionFunctor_fiberZero :
    E.IsBoundaryScPlusSectionFunctor (fiberZero P) :=
  ⟨StrongBundle.isBoundaryScPlusSection_fiberZero, fun φ _ _ =>
    (secAct_fiberZero (E := E) φ).symm⟩

/-- The zero section is an sc⁺-section functor. -/
theorem isScPlusSectionFunctor_fiberZero_p3x : E.IsScPlusSectionFunctor (fiberZero P) :=
  ⟨⟨StrongBundle.IsScPlusSection.isScSmoothSection' StrongBundle.isScPlusSection_fiberZero,
    fun φ => (secAct_fiberZero (E := E) φ).symm⟩, StrongBundle.isScPlusSection_fiberZero⟩

/-! ### Functoriality of products and glued sums -/

/-- `f · σ` is functorial for `f` constant along morphisms and `σ` functorial. -/
theorem isFunctorialSection_sectionSmul_p3x {f : Obj → ℝ}
    (hf : ∀ φ : Mor, f (X.src φ) = f (X.tgt φ))
    {σ : Obj → W} (hσ : IsSection P σ) (hfun : E.IsFunctorialSection hσ) :
    E.IsFunctorialSection (hσ.sectionSmul (f := f)) := by
  intro φ
  have h1 : (⟨σ (X.tgt φ), hσ _⟩ : P ⁻¹' {X.tgt φ}) = E.fiberMor φ ⟨σ (X.src φ), hσ _⟩ :=
    Subtype.ext (by rw [fiberMor_apply]; exact hfun φ)
  rw [sectionSmul_apply hσ (X.tgt φ), h1, ← hf φ, ← map_smul, fiberMor_apply]
  exact E.μ_pair_congr rfl (sectionSmul_apply hσ (X.src φ)).symm _ _

/-- The glued section of functorial sections with a partition of unity constant along morphisms
is functorial. -/
theorem isFunctorialSection_glueSection (hρinv : ∀ i (φ : Mor), ρ i (X.src φ) = ρ i (X.tgt φ))
    (hσ : ∀ i, IsSection P (σ i)) (hfun : ∀ i, E.IsFunctorialSection (hσ i)) :
    E.IsFunctorialSection (isSection_glueSection (ρ := ρ) hσ) := by
  intro φ
  obtain ⟨I, hI⟩ := ρ.exists_finset_nhds (X.src φ)
  have hIs : support (ρ · (X.src φ)) ⊆ I := hI.self_of_nhds.2
  have hIt : support (ρ · (X.tgt φ)) ⊆ I := fun i hi => hIs (by
    change ρ i (X.src φ) ≠ 0
    rw [hρinv]
    exact hi)
  have e1 : ∀ i, (⟨σ i (X.tgt φ), hσ i _⟩ : P ⁻¹' {X.tgt φ}) =
      E.fiberMor φ ⟨σ i (X.src φ), hσ i _⟩ :=
    fun i => Subtype.ext (by rw [fiberMor_apply]; exact hfun i φ)
  have e2 : ∑ i ∈ I, ρ i (X.tgt φ) • (⟨σ i (X.tgt φ), hσ i _⟩ : P ⁻¹' {X.tgt φ}) =
      E.fiberMor φ (∑ i ∈ I, ρ i (X.src φ) • (⟨σ i (X.src φ), hσ i _⟩ : P ⁻¹' {X.src φ})) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← e1 i, hρinv i φ]
  rw [glueSection_apply hσ (X.tgt φ), glueSection_finsum_eq_sum hσ _ I hIt, e2, fiberMor_apply]
  refine E.μ_pair_congr rfl ?_ _ _
  rw [glueSection_apply hσ (X.src φ), glueSection_finsum_eq_sum hσ _ I hIs]

/-- **The glued sc⁺-section functor**: for an sc-smooth partition of unity constant along
morphisms, `Σ_i ρ_i σ_i` of sc⁺-section functors is an sc⁺-section functor. -/
theorem isScPlusSectionFunctor_glueSection (hρsm : X.PObj.IsScSmoothPartitionOfUnity ρ)
    (hρinv : ∀ i (φ : Mor), ρ i (X.src φ) = ρ i (X.tgt φ))
    (hσ : ∀ i, E.IsScPlusSectionFunctor (σ i)) : E.IsScPlusSectionFunctor (glueSection P ρ σ) := by
  have hplus : ∀ i, B.IsScPlusSection (σ i) := fun i => (hσ i).2
  have hsec : ∀ i, IsSection P (σ i) := fun i => (hplus i).1
  have hfun : ∀ i, E.IsFunctorialSection (hsec i) := fun i => by
    obtain ⟨_, h⟩ := (hσ i).1
    exact h
  have hg := isScPlusSection_glueSection hρsm hplus
  exact ⟨⟨StrongBundle.IsScPlusSection.isScSmoothSection' hg,
    isFunctorialSection_glueSection hρinv hsec hfun⟩, hg⟩

end EpStrongBundle

end Sections

/-! ### The local step and Theorem 12.3.9 -/

section Extension

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable {E : EpStrongBundle X B}

/-- **The average of Corollary 12.3.8 in the natural representation** (as
`exists_equivariant_average`, with the value statement at every point): from an sc⁺-section `s`
supported in an open invariant `V`, `cl V ⊆ U(x)`, the average `σ = |G_x|⁻¹ Σ_k h_k` of its
translates `h_k` is an sc⁺-section, `G_x`-equivariant on `U(x)`, supported in `cl V`, and
`σ(y) = w` wherever all translates `h_k(y)` equal `w`. -/
theorem exists_equivariant_average_p3x {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVinv : ∀ k, MapsTo (R.Φ k) V V) (hVcl : closure V ⊆ R.U) {s : Obj → W}
    (hs : B.IsScPlusSection s) (hsV : sectionSupport P s ⊆ V) :
    ∃ σ : Obj → W, ∃ hσ : B.IsScPlusSection σ,
      (∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ.1 ψ) ∧ sectionSupport P σ ⊆ closure V ∧
      ∀ y (w : W) (_hw : P w = y), (∀ k, natTerm E R hs.1 k y = w) → σ y = w := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  set c : ℝ := (Fintype.card (X.Isotropy x) : ℝ)⁻¹ with hc
  have hcard : (0 : ℝ) < Fintype.card (X.Isotropy x) := Nat.cast_pos.2 Fintype.card_pos
  set h := natTerm E R hs.1 with hh
  have hsec : ∀ k, IsSection P (h k) := isSection_natTerm R hs.1
  have hplus : ∀ k, B.IsScPlusSection (h k) := isScPlusSection_natTerm R hVinv hVcl hs hsV
  set S := sectionSum P Finset.univ h with hS
  have hSsec : IsSection P S := isSection_sectionSum hsec
  set σ := sectionSmul P (fun _ => c) S with hσdef
  have hσ : B.IsScPlusSection σ :=
    (StrongBundle.isScPlusSection_sectionSum Finset.univ hplus).smul_left
      (isScSmoothMap_real_const c)
  refine ⟨σ, hσ, fun ψ hψ => ?_, ?_, fun y w hw hk => ?_⟩
  · have h1 : S (X.tgt ψ) = E.secAct hSsec ψ :=
      sectionSum_tgt hsec ψ (Equiv.mulLeft (R.index ψ)) fun k => natTerm_tgt R hs.1 hψ k
    exact (sectionSmul_tgt hSsec c ψ h1).trans rfl
  · refine closure_minimal (fun y hy => ?_) isClosed_closure
    by_contra hyV
    have hyV' : y ∉ V := fun h' => hyV (subset_closure h')
    apply hy
    have hS0 : S y = fiberZero P y := by
      rw [hS, sectionSum_apply hsec]
      have h0 : (∑ k, (⟨h k y, hsec k y⟩ : P ⁻¹' {y})) = 0 := Finset.sum_eq_zero fun k _ =>
        Subtype.ext (natTerm_eq_zero R hs.1 (subset_closure.trans hVcl) hVinv hsV k hyV')
      rw [h0]
      rfl
    have hv0 : (⟨S y, hSsec y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext hS0
    rw [hσdef, sectionSmul_apply hSsec, hv0, smul_zero]
    rfl
  · have hk' : ∀ k, (⟨h k y, hsec k y⟩ : P ⁻¹' {y}) = ⟨w, hw⟩ := fun k => Subtype.ext (hk k)
    have hSy : (⟨S y, hSsec y⟩ : P ⁻¹' {y}) =
        (Fintype.card (X.Isotropy x) : ℝ) • (⟨w, hw⟩ : P ⁻¹' {y}) := by
      apply Subtype.ext
      change S y = _
      rw [hS, sectionSum_apply hsec]
      simp only [hk', Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
    rw [hσdef, sectionSmul_apply hSsec, hSy, smul_smul, hc, inv_mul_cancel₀ hcard.ne', one_smul]

/-- **The local step of Theorem 12.3.9** (Corollary 12.3.8 near `x ∈ ∂X`, extended to the
saturation): for `x ∈ ∂X` in a saturated open `U` there are a saturated open `U' ∋ x` and an
sc⁺-section functor `σ` supported in `U` with `σ = s` on `U' ∩ ∂X`. -/
theorem exists_local_functor_extension
    (hB : ∀ x : Obj, ∃ c : StrongBundleChart X.PObj P, B.IsTameChart c ∧ x ∈ c.φ.source)
    (hbump : X.PObj.AdmitsBumpFunctions) {s : Obj → W} (hs : E.IsBoundaryScPlusSectionFunctor s)
    {U : Set Obj} (hU : IsOpen U) (hUsat : X.IsSaturated U) {x : Obj} (hxU : x ∈ U)
    (hxb : x ∈ X.PObj.boundary) :
    ∃ U' : Set Obj, IsOpen U' ∧ X.IsSaturated U' ∧ x ∈ U' ∧ ∃ σ : Obj → W,
      E.IsScPlusSectionFunctor σ ∧ sectionSupport P σ ⊆ U ∧
      ∀ y ∈ U' ∩ X.PObj.boundary, σ y = s y := by
  classical
  obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, hprop⟩ :=
    EpGroupoid.exists_invariant_nhds_of_isOpen X x hU hxU
  -- Part I's local extension (Proposition 12.3.7 in a tame chart), cut off inside `V`
  obtain ⟨c, hc, hxc⟩ := hB x
  obtain ⟨U₁, hU₁, hxU₁, σ₀, hσ₀, hagree₀⟩ :=
    StrongBundle.exists_local_extension hbump hc hxc hxb hs.1
  obtain ⟨β, hβ, -, -, hβS, hβev⟩ := proposition_5_5_3 hbump (hVo.inter hU₁) ⟨hxV, hxU₁⟩
  set σ₁ := sectionSmul P β σ₀ with hσ₁def
  have hσ₁ : B.IsScPlusSection σ₁ := hσ₀.smul_left hβ
  have hσ₁V : sectionSupport P σ₁ ⊆ V :=
    (sectionSupport_sectionSmul_subset_tsupport_p3x hσ₀.1).trans (hβS.trans inter_subset_left)
  set W₁ := interior {y | β y = 1} ∩ U₁ with hW₁def
  have hW₁o : IsOpen W₁ := isOpen_interior.inter hU₁
  have hxW₁ : x ∈ W₁ := ⟨mem_interior_iff_mem_nhds.2 hβev, hxU₁⟩
  have hσ₁s : ∀ y ∈ W₁ ∩ X.PObj.boundary, σ₁ y = s y := by
    rintro y ⟨⟨hy1, hyU₁⟩, hyb⟩
    have hβy : β y = 1 := interior_subset (s := {y | β y = 1}) hy1
    rw [hσ₁def, sectionSmul_apply hσ₀.1, hβy, one_smul]
    exact hagree₀ y ⟨hyU₁, hyb⟩
  -- the average over `G_x`
  obtain ⟨σ₂, hσ₂, hequiv, hσ₂V, hσ₂agree⟩ :=
    exists_equivariant_average_p3x (E := E) R hVinv hVcl hσ₁ hσ₁V
  set W₂ := ⋂ k : X.Isotropy x, R.U ∩ R.Φ k ⁻¹' W₁ with hW₂def
  have hW₂o : IsOpen W₂ := isOpen_iInter_of_finite fun k =>
    (R.continuousOn_Φ k).isOpen_inter_preimage R.isOpen_U hW₁o
  have hxW₂ : x ∈ W₂ := mem_iInter.2 fun k =>
    ⟨R.mem_U, by rw [mem_preimage, R.Φ_self]; exact hxW₁⟩
  have hW₂U : W₂ ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  -- the average still extends `s` on `W₂ ∩ ∂X` (`s` is functorial on `∂X`)
  have hσ₂s : ∀ y ∈ W₂ ∩ X.PObj.boundary, σ₂ y = s y := by
    rintro y ⟨hyW, hyb⟩
    have hyU : y ∈ R.U := hW₂U hyW
    refine hσ₂agree y (s y) (hs.1.1 y hyb).1 fun k => ?_
    rw [natTerm_of_mem R hσ₁.1 k hyU]
    have hz : R.Φ k⁻¹ y ∈ R.U := R.mapsTo_Φ k⁻¹ hyU
    have hψs : X.src (R.Γ k (R.Φ k⁻¹ y)) = R.Φ k⁻¹ y := R.src_Γ k _ hz
    have hψt : X.tgt (R.Γ k (R.Φ k⁻¹ y)) = y := tgt_Γ_Φ_inv R k hyU
    have hψb : X.src (R.Γ k (R.Φ k⁻¹ y)) ∈ X.PObj.boundary :=
      (EpGroupoid.tgt_mem_boundary_iff_p3x _).1 (by rw [hψt]; exact hyb)
    have hzW : X.src (R.Γ k (R.Φ k⁻¹ y)) ∈ W₁ := by
      rw [hψs]
      exact (mem_iInter.1 hyW k⁻¹).2
    have h1 : σ₁ (X.src (R.Γ k (R.Φ k⁻¹ y))) = s (X.src (R.Γ k (R.Φ k⁻¹ y))) :=
      hσ₁s _ ⟨hzW, hψb⟩
    exact (E.μ_pair_congr rfl h1 _ ((hs.1.1 _ hψb).1)).trans
      ((hs.2 _ hψb _).symm.trans (congrArg s hψt))
  -- the extension to the saturation (Remark 12.3.5)
  obtain ⟨hfun, -, hsupp, -⟩ := remark_12_3_5 (E := E) R hVcl hprop hσ₂ hequiv hσ₂V
  refine ⟨X.saturation W₂, EpGroupoid.isOpen_saturation_of_isOpen X hW₂o,
    EpGroupoid.isSaturated_saturation X W₂, X.subset_saturation W₂ hxW₂,
    natExtension E R hσ₂.1, hfun, ?_, ?_⟩
  · exact hsupp.trans ((EpGroupoid.saturation_mono_p3x hσ₂V).trans
      (EpGroupoid.saturation_subset_of_isSaturated hUsat (hVcl.trans hRU)))
  · rintro y ⟨⟨z, hz, hzy⟩, hyb⟩
    obtain ⟨φ, hφs, hφt⟩ := X.π_eq_π_iff.1 hzy
    subst hφs hφt
    have hzb : X.src φ ∈ X.PObj.boundary := (EpGroupoid.tgt_mem_boundary_iff_p3x φ).1 hyb
    rw [natExtension_eq R hσ₂.1 hequiv (hW₂U hz)]
    have h2 : σ₂ (X.src φ) = s (X.src φ) := hσ₂s _ ⟨hz, hzb⟩
    exact (E.μ_pair_congr rfl h2 _ ((hs.1.1 _ hzb).1)).trans (hs.2 φ hzb _).symm

/-- **Theorem 12.3.9, first statement** (core, any universes; "every point lies in a tame strong
bundle chart" for the tame bundle): the local extensions glued by an sc-smooth partition of unity
of the ep-groupoid. -/
theorem exists_extension_of_tameCharts
    (hB : ∀ x : Obj, ∃ c : StrongBundleChart X.PObj P, B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : X.HasScPartitionsOfUnity) {s : Obj → W} (hs : E.IsBoundaryScPlusSectionFunctor s)
    {U : Set Obj} (hU : IsOpen U) (hUsat : X.IsSaturated U) (hbU : X.PObj.boundary ⊆ U) :
    ∃ s' : Obj → W, E.IsScPlusSectionFunctor s' ∧ sectionSupport P s' ⊆ U ∧
      ∀ x ∈ X.PObj.boundary, s' x = s x := by
  classical
  have hbump : X.PObj.AdmitsBumpFunctions := EpGroupoid.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hpu)
  have hloc : ∀ x : Obj, ∃ U' : Set Obj, IsOpen U' ∧ X.IsSaturated U' ∧ x ∈ U' ∧
      ∃ σ : Obj → W, E.IsScPlusSectionFunctor σ ∧ sectionSupport P σ ⊆ U ∧
        ∀ y ∈ U' ∩ X.PObj.boundary, σ y = s y := by
    intro x
    by_cases hxb : x ∈ X.PObj.boundary
    · exact exists_local_functor_extension hB hbump hs hU hUsat (hbU hxb) hxb
    · refine ⟨X.PObj.boundaryᶜ, X.PObj.isClosed_boundary.isOpen_compl,
        EpGroupoid.isSaturated_compl_boundary_p3x, hxb, fiberZero P,
        isScPlusSectionFunctor_fiberZero_p3x, ?_, fun y hy => absurd hy.2 hy.1⟩
      rw [sectionSupport_fiberZero_p3x]
      exact empty_subset _
  choose U' hU'o hU'sat hxU' σ hσ hσU hσs using hloc
  obtain ⟨ρ, hρsub, hρsm, -, hρinv⟩ :=
    hpu Obj U' hU'o hU'sat (iUnion_eq_univ_iff.2 fun x => ⟨x, hxU' x⟩)
  have hsec : ∀ i, IsSection P (σ i) := fun i => (hσ i).2.1
  refine ⟨glueSection P ρ σ, isScPlusSectionFunctor_glueSection hρsm hρinv hσ, ?_, ?_⟩
  · exact (sectionSupport_glueSection_subset hsec).trans
      (iUnion_subset fun i => inter_subset_right.trans (hσU i))
  · intro y hyb
    exact glueSection_eq_of hsec (hs.1.1 y hyb).1 fun i hi => hσs i y ⟨hρsub i hi, hyb⟩

/-- **Theorem 12.3.9, second statement** (core): with an auxiliary norm `N` and `δ > 0` such that
`N(s(x)) < δ` on `∂X`, the extension can be taken with `N(s̃(x)) ≤ δ` for all `x` (the extension of
`exists_extension_of_tameCharts` times a bump function `β = 1` on `∂X`, supported where
`N(s̃) < δ`). -/
theorem exists_extension_bounded_of_tameCharts
    (hB : ∀ x : Obj, ∃ c : StrongBundleChart X.PObj P, B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : X.HasScPartitionsOfUnity) {s : Obj → W} (hs : E.IsBoundaryScPlusSectionFunctor s)
    {U : Set Obj} (hU : IsOpen U) (hUsat : X.IsSaturated U) (hbU : X.PObj.boundary ⊆ U)
    {N : B.One → ℝ} (hN : E.IsAuxNorm N) {δ : ℝ} (hδ : 0 < δ)
    (hNs : ∀ x ∈ X.PObj.boundary, ∀ h : s x ∈ B.oneSet, N (B.oneMk (s x) h) < δ) :
    ∃ s' : Obj → W, E.IsScPlusSectionFunctor s' ∧ sectionSupport P s' ⊆ U ∧
      (∀ x ∈ X.PObj.boundary, s' x = s x) ∧
      ∀ x (h : s' x ∈ B.oneSet), N (B.oneMk (s' x) h) ≤ δ := by
  classical
  obtain ⟨s₁, hs₁, hs₁U, hs₁s⟩ := exists_extension_of_tameCharts hB hpu hs hU hUsat hbU
  have hplus : B.IsScPlusSection s₁ := hs₁.2
  have hsec : IsSection P s₁ := hplus.1
  have hfun : E.IsFunctorialSection hsec := by
    obtain ⟨_, h⟩ := hs₁.1
    exact h
  obtain ⟨-, g, hg, hgs⟩ := (B.isScPlusSection_iff s₁).1 hplus
  have hgc : Continuous g := continuousOn_univ.1 hgs.continuousOn
  have hgv : ∀ y, B.oneVal (g y) = s₁ y := fun y => congrFun hg y
  -- `V = {N(s̃) < δ}` is open, saturated and contains `∂X`
  set V := {y | N (g y) < δ} with hVdef
  have hVo : IsOpen V := isOpen_lt (hN.isAuxNorm.continuous.comp hgc) continuous_const
  have hVsat : X.IsSaturated V := by
    refine X.isSaturated_iff.2 fun φ hφ => ?_
    change N (g (X.tgt φ)) < δ
    have hk : P (B.oneVal (g (X.src φ))) = X.src φ := by rw [hgv]; exact hsec _
    have he : N (g (X.tgt φ)) = N (g (X.src φ)) :=
      hN.map_μ (g (X.tgt φ)) (g (X.src φ)) φ hk (by
        rw [hgv (X.tgt φ), hfun φ]
        exact E.μ_pair_congr rfl (hgv _).symm _ _)
    rw [he]
    exact hφ
  have hbV : X.PObj.boundary ⊆ V := fun y hyb => by
    change N (g y) < δ
    have h1 := (hs.1.1 y hyb).2
    have : g y = B.oneMk (s y) h1 :=
      B.oneVal_injective (by rw [hgv, B.oneVal_oneMk, hs₁s y hyb])
    rw [this]
    exact hNs y hyb h1
  -- the bump function `β = 1` on `∂X` with `supp β ⊆ V`
  let c : ULift.{u} Bool → Set Obj := fun i => bif i.down then V else X.PObj.boundaryᶜ
  obtain ⟨ρ, hρsub, hρsm, -, hρinv⟩ := hpu _ c
    (fun i => by rcases i with ⟨_ | _⟩; exacts [X.PObj.isClosed_boundary.isOpen_compl, hVo])
    (fun i => by
      rcases i with ⟨_ | _⟩
      exacts [EpGroupoid.isSaturated_compl_boundary_p3x, hVsat])
    (iUnion_eq_univ_iff.2 fun y => if hy : y ∈ X.PObj.boundary then ⟨⟨true⟩, hbV hy⟩ else
      ⟨⟨false⟩, hy⟩)
  set β := ρ ⟨true⟩ with hβdef
  have hβ1 : ∀ y ∈ X.PObj.boundary, β y = 1 := fun y hy =>
    EpGroupoid.partitionOfUnity_true_eq_one_p3x
      (image_eq_zero_of_notMem_tsupport fun h => hρsub ⟨false⟩ h hy)
  have hplus' : B.IsScPlusSection (sectionSmul P β s₁) := hplus.smul_left (hρsm _)
  refine ⟨sectionSmul P β s₁, ⟨⟨StrongBundle.IsScPlusSection.isScSmoothSection' hplus',
    isFunctorialSection_sectionSmul_p3x (hρinv _) hsec hfun⟩, hplus'⟩,
    (sectionSupport_sectionSmul_subset_p3x hsec).trans hs₁U, fun y hy => ?_, fun y h => ?_⟩
  · rw [sectionSmul_apply hsec, hβ1 y hy, one_smul]
    exact hs₁s y hy
  · have hmem : s₁ y ∈ B.oneSet := hplus.mem_oneSet y
    let w : B.oneFiber y := ⟨⟨s₁ y, hsec y⟩, hmem⟩
    have hrep : B.oneMk (sectionSmul P β s₁ y) h = B.toOne (β y • w) := by
      apply B.oneVal_injective
      rw [B.oneVal_oneMk, B.oneVal_toOne, sectionSmul_apply hsec]
      rfl
    have hw : B.toOne w = g y := B.oneVal_injective (by rw [B.oneVal_toOne, hgv])
    rw [hrep, hN.isAuxNorm.smul, abs_of_nonneg (ρ.nonneg _ y), hw]
    by_cases hβ0 : β y = 0
    · rw [hβ0, zero_mul]
      exact hδ.le
    · have hyV : y ∈ V := hρsub ⟨true⟩ (subset_tsupport _ hβ0)
      calc β y * N (g y) ≤ 1 * δ :=
            mul_le_mul (ρ.le_one _ y) hyV.le (hN.isAuxNorm.nonneg _) zero_le_one
        _ = δ := one_mul δ

end EpStrongBundle

end Extension

/-! ### Theorem 12.3.9 -/

section Theorem

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **Theorem 12.3.9, p. 586** (extension of sc⁺-section functors; 2017: Theorem 12.8).  Let
`(P : W → X, μ)` be a strong bundle over a tame ep-groupoid (`B.IsTameBundle`: `X` tame and a tame
strong bundle chart around every object), `|X|` paracompact, and let the ep-groupoid admit
sc-smooth partitions of unity (Definition 7.5.5).  For an sc⁺-section functor `s` of `W|∂X`
(Definition 12.3.6 plus functoriality) and a saturated open neighbourhood `U` of `∂X`:
(1) there is an sc⁺-section functor `s̃` of `P` supported in `U` with `s̃|∂X = s`;
(2) given an auxiliary norm `N` and `δ > 0` with `N(s(x)) < δ` on `∂X`, `s̃` can moreover be
chosen with `N(s̃(x)) ≤ δ` for all `x`. -/
theorem theorem_12_3_9 (E : EpStrongBundle X B) (hB : B.IsTameBundle)
    (_hpara : X.HasParacompactOrbitSpace) (hpu : X.HasScPartitionsOfUnity) {s : Obj → W}
    (hs : E.IsBoundaryScPlusSectionFunctor s) {U : Set Obj} (hU : IsOpen U)
    (hUsat : X.IsSaturated U) (hbU : X.PObj.boundary ⊆ U) :
    (∃ s' : Obj → W, E.IsScPlusSectionFunctor s' ∧ sectionSupport P s' ⊆ U ∧
      ∀ x ∈ X.PObj.boundary, s' x = s x) ∧
    ∀ {N : B.One → ℝ}, E.IsAuxNorm N → ∀ {δ : ℝ}, 0 < δ →
      (∀ x ∈ X.PObj.boundary, ∀ h : s x ∈ B.oneSet, N (B.oneMk (s x) h) < δ) →
      ∃ s' : Obj → W, E.IsScPlusSectionFunctor s' ∧ sectionSupport P s' ⊆ U ∧
        (∀ x ∈ X.PObj.boundary, s' x = s x) ∧
        ∀ x (h : s' x ∈ B.oneSet), N (B.oneMk (s' x) h) ≤ δ :=
  ⟨exists_extension_of_tameCharts hB.2 hpu hs hU hUsat hbU, fun hN _ hδ hNs =>
    exists_extension_bounded_of_tameCharts hB.2 hpu hs hU hUsat hbU hN hδ hNs⟩

/-- **The hypotheses of Theorem 12.3.9 are satisfiable**: the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` over
the trivial ep-groupoid of `ℝⁿ` is a tame strong bundle, `|X|` is paracompact, the ep-groupoid
admits sc-smooth partitions of unity, the zero section is an sc⁺-section functor of `W|∂X`, and
`U = X` is a saturated open neighbourhood of `∂X`. -/
theorem theorem_12_3_9_hypotheses_rn (n k : ℕ) :
    (TrivialBundle.bundle n k).IsTameBundle ∧
      (EpGroupoid.trivial (rnPolyfold n)).HasParacompactOrbitSpace ∧
      (EpGroupoid.trivial (rnPolyfold n)).HasScPartitionsOfUnity ∧
      (TrivialBundle.epBundle n k).IsBoundaryScPlusSectionFunctor
        (fiberZero (TrivialBundle.proj n k)) ∧
      (EpGroupoid.trivial (rnPolyfold n)).IsSaturated univ ∧
      (EpGroupoid.trivial (rnPolyfold n)).PObj.boundary ⊆ univ :=
  ⟨⟨rnPolyfold_isTame, fun x => ⟨TrivialBundle.chart x, TrivialBundle.isTameChart_chart x,
    by simp [TrivialBundle.chart, rnChart_source]⟩⟩,
    (EpGroupoid.theorem_7_5_7_hypotheses_rn n).1,
    EpGroupoid.hasScPartitionsOfUnity_trivial_rn_of_theorem_7_5_7 n,
    isBoundaryScPlusSectionFunctor_fiberZero, GroupoidStr.isSaturated_univ _, subset_univ _⟩

end EpStrongBundle

end Theorem

end Polyfold
