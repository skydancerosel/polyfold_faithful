import Polyfold.Chapter16.CanonicalIntegralInvariance
import Polyfold.Chapter16.CircleSectionCobordism
import Polyfold.Chapter16.IndexZeroIsotropyWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8) and Definition 16.6.5 on two examples.

# Oriented sc-Fredholm sections over polyfolds for Theorem 16.6.6

## What is formalized

Namespace `Polyfold.TrivialBundle`, the circle section `f(x) = (x, x₀² + x₁² − 1)` of
`ℝ² × ℝ → ℝ²` (`epSEP 2 1`, Fredholm index `1`, solution set the unit circle):
* `circleBundleStructure`, `circlePolyfoldBundle`, `circleGraphRep`, `circleFredholmSection`: the
  strong polyfold bundle `|ℝ² × ℝ| → |ℝ²|` and the sc-Fredholm section `|x| ↦ |f(x)|`
  (Definitions 16.3.1, 16.3.18, 16.6.1).
* `definition_12_5_4_circleSectionOrientation`, **`circleOrientationRep`**: an orientation of
  the section in the sense of Definition 16.6.5.
* **`theorem_16_6_6_canonical_hypotheses_circle`**: every hypothesis of
  `StrongPolyfoldBundle.theorem_16_6_6_canonical` holds (`Z` has sc-smooth partitions of unity,
  `∂Z = ∅`, compact solution set), non-zero fibres, `CanonicalInput` with index `1`, and the
  predicate "orientation inherited from `(f, o)`" is satisfied by a perturbed solution set whose
  support is the unit circle (sheets of dimension `1`).

Namespace `Polyfold.StrongBundleLocalizationExamples`, the section `|x| ↦ |(x, x² − 1)|` over
`|ℤ/3 × ℝ ⇉ ℝ|` (morphisms which are not units, Fredholm index `0`):
* `canonicalInput_z3OrientationRep`, **`theorem_16_6_6_index_zero_hypotheses_z3`**: the
  predicate of `theorem_16_6_6_index_zero_canonical_input` is satisfied for this orientation by a
  canonically oriented regular perturbation of dimension `0` whose support contains `±1`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid SEP
  StrongBundleEquivalenceExamples StrongBundleLocalizationExamples
  StrongPolyfoldBundle StrongPolyfoldBundleStructure PolyfoldClass

/-! ### The strong polyfold bundle and the section -/

/-- **The strong polyfold bundle structure `((P : W → X, μ), id, id)`** for
`|P| : |ℝ² × ℝ| → |ℝ²|` over the trivial ep-groupoid of `ℝ²` (Definition 16.3.1). -/
def circleBundleStructure : StrongPolyfoldBundleStructure (epSEP 2 1).E.projFunctor.orbitMap where
  A := epSEP 2 1
  isZhou := isZhou_trivial _
  paracompact := hasParacompactOrbitSpace_trivial _
  isLRLocal := EpStrongBundle.isLRLocal_trivial _
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- The strong polyfold bundle of `circleBundleStructure` (Definition 16.3.4). -/
def circlePolyfoldBundle : StrongPolyfoldBundle (epSEP 2 1).E.projFunctor.orbitMap :=
  ⟦circleBundleStructure⟧

/-- **The representative `(circleBundleStructure, f)`** of the section `|x| ↦ |(x, x₀² + x₁² − 1)|`
(Definition 16.3.18). -/
def circleGraphRep : SectionRep circlePolyfoldBundle where
  S := circleBundleStructure
  hS := rfl
  F := circleSection
  hF := isScFredholmSectionFunctor_circleSection.1
  f := Quotient.lift
    (fun x : (epSEP 2 1).Obj => (epSEP 2 1).E.toEpGroupoid.π (circleSection x))
    fun x y h => by
      have e : x = y := injective_π_trivial_rn (Quotient.sound h)
      rw [e]
  continuous_f := Continuous.quotient_lift ((epSEP 2 1).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk contDiff_circleMap.continuous)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

/-- **The sc-Fredholm section `|x| ↦ |(x, x₀² + x₁² − 1)|`** (Definition 16.6.1). -/
def circleFredholmSection : FredholmSection circlePolyfoldBundle :=
  ⟨⟦circleGraphRep⟧, circleGraphRep, rfl, isScFredholmSectionFunctor_circleSection⟩

/-! ### The orientation (Definition 16.6.5) -/

/-- Part I's topology on `O_f` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_circleSection :
    haveI := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 2 1).B
    haveI := paracompactSpace_rn_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP 2 1).B
    IsOrientationTopology (B := (epSEP 2 1).B) circleSection
      isScFredholmSectionFunctor_circleSection.2
      (orTopology (orLocalTransport (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
        (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
        (hasScPlusSectionsThrough_epSEP 2 1))) := by
  have := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
  have := paracompactSpace_rn_pullback (epSEP 2 1).B
  have := paracompactSpace_rn_rn_prod (epSEP 2 1).X.PObj
  have := paracompactSpace_rn_rn_pullback (epSEP 2 1).B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
    (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)).exists
  exact eq_orTopology_of (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
    (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
    (hasScPlusSectionsThrough_epSEP 2 1) ht₀.isLocalHomeomorph ht₀.propagation ▸ ht₀

/-- **`circleSectionOrientation` is an orientation in the sense of Definition 12.5.4** for Part
I's topology on `O_f`: continuous (`isSectionOrientation_iff_continuous`) and invariant under the
morphisms (units). -/
theorem definition_12_5_4_circleSectionOrientation :
    haveI := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 2 1).B
    haveI := paracompactSpace_rn_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP 2 1).B
    (epSEP 2 1).E.definition_12_5_4 isScFredholmSectionFunctor_circleSection
      (hasScPlusSectionsThrough_epSEP 2 1)
      (orTopology (orLocalTransport (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
        (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
        (hasScPlusSectionsThrough_epSEP 2 1))) circleSectionOrientation := by
  have := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
  have := paracompactSpace_rn_pullback (epSEP 2 1).B
  have := paracompactSpace_rn_rn_prod (epSEP 2 1).X.PObj
  have := paracompactSpace_rn_rn_pullback (epSEP 2 1).B
  exact ⟨(isSectionOrientation_iff_continuous (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
      (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
      (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation).1
      isSectionOrientation_circleSectionOrientation,
    isOrInvariant_circleSectionOrientation⟩

/-- **An orientation of the circle section over the polyfold `|ℝ²|`** (Definition 16.6.5): the
representative `(circleBundleStructure, f)` with Part I's topology on `O_f` and the orientation
`circleSectionOrientation`. -/
def circleOrientationRep : OrientationRep circleFredholmSection where
  a := circleGraphRep
  ha := rfl
  hF := isScFredholmSectionFunctor_circleSection
  hsec := hasScPlusSectionsThrough_epSEP 2 1
  t := haveI := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 2 1).B
    haveI := paracompactSpace_rn_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP 2 1).B
    orTopology (orLocalTransport (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
      (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
      (hasScPlusSectionsThrough_epSEP 2 1))
  isOrientationTopology := isOrientationTopology_circleSection
  o := circleSectionOrientation
  isOrientation := definition_12_5_4_circleSectionOrientation

/-! ### The hypotheses of Theorem 16.6.6 -/

/-- **The polyfold `|ℝ²|` has no boundary.** -/
theorem circlePolyfoldBundle_boundary_eq_empty : circlePolyfoldBundle.polyfold.boundary = ∅ := by
  obtain ⟨-, -, hd, -⟩ := corollary_15_4_4_hypotheses_circleSection
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := circleBundleStructure.surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := circlePolyfoldBundle) rfl x).1 hz
  have h : (0 : ℕ) < (epSEP 2 1).X.PObj.degIndex x := hx
  have h0 : (epSEP 2 1).X.PObj.degIndex x = 0 := hd x
  omega

/-- **The polyfold `|ℝ²|` admits sc-smooth partitions of unity** (Definition 16.1.5 (2)). -/
theorem circlePolyfoldBundle_admitsScPartitionsOfUnity :
    circlePolyfoldBundle.polyfold.AdmitsScPartitionsOfUnity :=
  ⟨circleBundleStructure.toPolyfoldStructure, rfl,
    hasScPartitionsOfUnity_trivial_rn_of_theorem_7_5_7 2⟩

/-- **The standing hypotheses in the model of `circleOrientationRep`** (index `1`). -/
theorem canonicalInput_circleOrientationRep : CanonicalInput circleOrientationRep (0 + 1) := by
  obtain ⟨-, -, -, -, -, hPUC, -, hft, -, -, -, hidx⟩ := corollary_15_4_4_hypotheses_circleSection
  exact ⟨hPUC, hft, hidx⟩

/-- **Every hypothesis of `theorem_16_6_6_canonical` holds for the circle section over `|ℝ²|`,
and its predicate is satisfied**: `Z` admits sc-smooth partitions of unity, `∂Z = ∅`, the
solution set is compact, every fibre is non-zero, the standing hypotheses hold in the model of
`circleOrientationRep` (index `1`), and a perturbed solution set `θ̂ = λ ∘ f` with the
orientation inherited from `(f, o)` exists whose model support (the unit circle) is non-empty. -/
theorem theorem_16_6_6_canonical_hypotheses_circle :
    circlePolyfoldBundle.polyfold.AdmitsScPartitionsOfUnity ∧
    circlePolyfoldBundle.polyfold.boundary = ∅ ∧
    circleFredholmSection.1.HasCompactSolutionSet ∧
    (∀ y : (epSEP 2 1).Obj, Nontrivial ((epSEP 2 1).P ⁻¹' {y})) ∧
    ∃ (P : OrientedRegularPerturbation (epSEP 2 1) circleSection 0)
      (Q : OrientedPerturbation circleFredholmSection.1 0),
      (EpGroupoid.supp (fun z => (P.Λ (circleSection z) : ℚ))).Nonempty ∧
      (CanonicalInput circleOrientationRep (0 + 1) ∧
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P)
          circleOrientationRep Q) := by
  obtain ⟨hne, -, -, -, -, -, -, -, hS, -, -, -⟩ := corollary_15_4_4_hypotheses_circleSection
  obtain ⟨P, -, hcan, hsupp⟩ := exists_isCanonicalPerturbation_circleSection
  refine ⟨circlePolyfoldBundle_admitsScPartitionsOfUnity, circlePolyfoldBundle_boundary_eq_empty,
    circleGraphRep.hasCompactSolutionSet_iff.2 hS, hne, P,
    (ModelPerturbation.ofRegular P).toOrientedPerturbation circleOrientationRep.ha, hsupp,
    canonicalInput_circleOrientationRep, P, hcan, rfl⟩

end TrivialBundle

namespace StrongBundleLocalizationExamples

open SBLocalization StrongPolyfoldBundle PolyfoldClass TrivialBundle

/-- **The standing hypotheses in the model of `z3OrientationRep`** (index `0`). -/
theorem canonicalInput_z3OrientationRep :
    CanonicalInput (z3OrientationRep (k := 1) contDiff_twoPointMap) 0 := by
  obtain ⟨hPUC, hft, -, hidx⟩ := indexZeroInput_z3OrientationRep
  exact ⟨hPUC, hft, fun x hx => by exact_mod_cast hidx x hx⟩

/-- **The predicate of `theorem_16_6_6_index_zero_canonical_input` for one orientation with
isotropy**: on the section `|x| ↦ |(x, x² − 1)|` over `|ℤ/3 × ℝ ⇉ ℝ|` (a morphism which is not a
unit, every fibre non-zero) the standing hypotheses hold in the model of `z3OrientationRep`, and
a regular perturbation of dimension `0` with the canonical orientation exists whose support
contains the two points `±1`. -/
theorem theorem_16_6_6_index_zero_hypotheses_z3 :
    (∃ σ : (z3SEP 1).Mor, σ ≠ (z3SEP 1).X.unit ((z3SEP 1).X.src σ)) ∧
    (∀ y : (z3SEP 1).Obj, Nontrivial ((z3SEP 1).P ⁻¹' {y})) ∧
    CanonicalInput (z3OrientationRep (k := 1) contDiff_twoPointMap) 0 ∧
    ∃ P : PointPerturbation (z3SEP 1) (graphSection twoPointMap),
      P.IsCanonical (z3OrientationRep (k := 1) contDiff_twoPointMap).hF.2
        (z3OrientationRep (k := 1) contDiff_twoPointMap).hsec
        (z3OrientationRep (k := 1) contDiff_twoPointMap).o ∧
      (fun _ => (1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (graphSection twoPointMap z) : ℚ)) ∧
      (fun _ => (-1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (graphSection twoPointMap z) : ℚ)) := by
  obtain ⟨hne, hnu, -⟩ := corollary_15_4_4_index_zero_hypotheses_z3
  obtain ⟨P, -, hP, h1, h2⟩ := exists_isCanonical_z3
  exact ⟨hnu, hne, canonicalInput_z3OrientationRep, P, hP, h1, h2⟩

end StrongBundleLocalizationExamples

end Polyfold
