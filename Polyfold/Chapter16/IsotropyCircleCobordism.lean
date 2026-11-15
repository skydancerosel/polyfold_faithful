import Polyfold.Chapter16.TrivialIsotropyBundle
import Polyfold.Chapter16.CircleSectionCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) on an example with isotropy and sheets of positive
dimension.

# Corollary 15.4.4 for the circle section over `ℤ/3 × ℝ² ⇉ ℝ²`

The strong bundle `ℝ² × ℝ → ℝ²` over the translation groupoid of the trivial action of `ℤ/3`
on `ℝ²` (`planeZ3SEP`), with the section `f(x) = (x, x₀² + x₁² − 1)`.  Every isotropy group is
`ℤ/3`, the base is not effective, the fibres are not zero, `f` has Fredholm index `1`, and the
solution set is the unit circle.

## What is formalized (namespace `Polyfold.TrivialIsotropy`)

* `isTransversal_graphSection_rnZ3`: the graph section of a `C^∞` map `ℝⁿ → ℝᵏ` with `0` a
  regular value is transversal to the zero section over `ℤ/3 × ℝⁿ ⇉ ℝⁿ` (Definition 15.2.1).
* **`corollary_15_4_4_hypotheses_planeZ3`**: all hypotheses of `corollary_15_4_4_oriented` hold
  with `m = 0`, together with non-zero fibres, a morphism that is not a unit, a base which is not
  effective, and `S_f ≠ ∅`; the orientation is `circleSectionOrientation`, invariant under
  the morphisms by `isOrInvariant_z3SEPOf`.
* **`corollary_15_4_4_planeZ3`**: the conclusion of Corollary 15.4.4 there (weights `1/3`).
* **`exists_isCanonicalPerturbation_planeZ3`**: a canonically oriented regular perturbation of
  dimension `1` whose support is the unit circle, so the corollary does not quantify over an
  empty set.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialIsotropy

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15 SEP
  StrongBundleEquivalenceExamples StrongBundleLocalizationExamples TrivialBundle

/-- `ℝⁿ × ℝᵏ → ℝⁿ` over `ℤ/3 × ℝⁿ ⇉ ℝⁿ` (the trivial action of `ℤ/3`). -/
abbrev rnZ3SEP (n k : ℕ) : SEP.{0} := z3SEPOf (rnPolyfold n) (TrivialBundle.bundle n k)

/-- `ℝ² × ℝ → ℝ²` over `ℤ/3 × ℝ² ⇉ ℝ²`. -/
abbrev planeZ3SEP : SEP.{0} := rnZ3SEP 2 1

section Transversal

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

theorem isScFredholmSectionFunctor_graphSection_rnZ3 (hφ : ContDiff ℝ ∞ φ) :
    (rnZ3SEP n k).E.IsScFredholmSectionFunctor (graphSection φ) := by
  obtain ⟨⟨hs, -⟩, hfred⟩ := graphSection_mem_fredholmSectionFunctors_epBundle (n := n) (k := k) hφ
  exact isScFredholmSectionFunctor_z3SEPOf _ hs hfred

/-- `Λ₀(f(x)) > 0` iff `φ(x) = 0`, for the multisection `Λ₀` of the zero section. -/
theorem zeroMultisection_graphSection_rnZ3_pos_iff (x : Fin n → ℝ) :
    0 < zeroMultisection (rnZ3SEP n k) (graphSection φ x) ↔ φ x = 0 := by
  classical
  have aux : ∀ w : (rnZ3SEP n k).W, w = graphSection φ x →
      (0 < zeroMultisection (rnZ3SEP n k) w ↔ φ x = 0) := by
    intro w hw
    have key : w = fiberZero (rnZ3SEP n k).P ((rnZ3SEP n k).P w) ↔ φ x = 0 := by
      subst hw
      exact isZeroAt_graphSection_iff (n := n) (k := k) (φ := φ) (x := x)
    unfold zeroMultisection
    by_cases h : w = fiberZero (rnZ3SEP n k).P ((rnZ3SEP n k).P w)
    · rw [if_pos h]
      exact iff_of_true one_pos (key.1 h)
    · rw [if_neg h]
      exact iff_of_false (lt_irrefl _) fun h' => h (key.2 h')
  exact aux _ rfl

/-- **The graph section of a `C^∞` map with `0` a regular value is transversal to the zero
section over `ℤ/3 × ℝⁿ ⇉ ℝⁿ`** (Definition 15.2.1 for `Λ₀`): at a zero `x₀`, in the chart
centred at `x₀`, `(f − 0)'(x₀) = Dφ(x₀)` is onto `ℝᵏ`. -/
theorem isTransversal_graphSection_rnZ3 (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x, φ x = 0 → Surjective (fderiv ℝ φ x)) :
    IsTransversal (A := rnZ3SEP n k) (graphSection φ) (zeroMultisection (rnZ3SEP n k)) := by
  classical
  have hf : (rnZ3SEP n k).E.IsScFredholmSectionFunctor (graphSection φ) :=
    isScFredholmSectionFunctor_graphSection_rnZ3 hφ
  intro x₀ hpos
  have h0 : φ x₀ = 0 := (zeroMultisection_graphSection_rnZ3_pos_iff x₀).1 hpos
  have hx1 : x₀ ∈ (rnZ3SEP n k).X.PObj.levelSet 1 := by
    have h : (x₀ : Fin n → ℝ) ∈ (rnPolyfold n).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hpos, hx1, ?_⟩
  set x := (rnZ3SEP n k).X.PObj.levelMk 1 x₀ hx1 with hxdef
  intro L hL
  have hxv : (rnZ3SEP n k).X.PObj.levelVal 1 x = x₀ := (rnZ3SEP n k).X.PObj.levelVal_levelMk _ _ _
  let c : StrongBundleChart (rnZ3SEP n k).X.PObj (rnZ3SEP n k).P := chart (k := k) x₀
  have hc : (rnZ3SEP n k).B.IsChart c := isChart_chart x₀
  have hx : (rnZ3SEP n k).X.PObj.levelVal 1 x ∈ c.φ.source := mem_univ _
  have hx0 : graphSection φ ((rnZ3SEP n k).X.PObj.levelVal 1 x) =
      fiberZero (rnZ3SEP n k).P ((rnZ3SEP n k).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (n := n) (k := k) (φ := φ) (x := x₀)).2 h0
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (isScPlusSectionOn_fiberZero isOpen_univ) hc
    (subset_univ _) hx hx0).2 ?_
  set z := levelLift c.φ 1 ((rnZ3SEP n k).X.PObj.levelVal 1 x) with hzdef
  have hz : z = 0 := by
    have h1 : c.φ.model.E.toBase 1 z = c.φ ((rnZ3SEP n k).X.PObj.levelVal 1 x) :=
      (rnZ3SEP n k).X.PObj.toBase_levelLift c.isChart hx ((rnZ3SEP n k).X.PObj.levelVal_mem x)
    rw [hxv] at h1
    have h2 : c.φ x₀ = (0 : Fin n → ℝ) := sub_self (show Fin n → ℝ from x₀)
    exact h1.trans h2
  have he : ((fun y => c.principal (graphSection φ) y -
      c.principal (fiberZero (rnZ3SEP n k).P) y) ∘ r c.R) = loc φ x₀ := by
    funext u
    have h2 : c.principal (fiberZero (rnZ3SEP n k).P) u = 0 :=
      c.snd_fiberZero (x := c.φ.symm u) (mem_univ _)
    change c.principal (graphSection φ) u - c.principal (fiberZero (rnZ3SEP n k).P) u = _
    rw [h2, sub_zero]
    rfl
  intro w _
  obtain ⟨v, hv⟩ := hreg x₀ h0 w
  refine ⟨v, ⟨v, ?_⟩, ?_⟩
  · rw [hz]
    exact congrArg (fun T : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => T v) (scDeriv_r (k := k) x₀)
  · change scDeriv c.U ((fun y => c.principal (graphSection φ) y -
      c.principal (fiberZero (rnZ3SEP n k).P) y) ∘ r c.R) z v = w
    rw [he, hz]
    exact (congrArg (fun T : (rnSc n) 0 →L[ℝ] (rnSc k) 0 => T v) (scDeriv_loc hφ x₀)).trans hv

end Transversal

/-! ### The circle section over `ℤ/3 × ℝ² ⇉ ℝ²` -/

theorem isScFredholmSectionFunctor_circle_planeZ3 :
    planeZ3SEP.E.IsScFredholmSectionFunctor circleSection :=
  isScFredholmSectionFunctor_graphSection_rnZ3 contDiff_circleMap

theorem hasParacompactOrbitSpace_planeZ3 : planeZ3SEP.X.HasParacompactOrbitSpace :=
  hasParacompactOrbitSpace_z3SEPOf _

/-- **`|S_f|` is compact** (Definition 12.4.1 (1)): `S_f` is the unit circle. -/
theorem hasCompactSolutionSetEp_circle_planeZ3 :
    planeZ3SEP.E.HasCompactSolutionSetEp circleSection := by
  have hK : IsCompact (solutionSet planeZ3SEP.P circleSection) := by
    have h : solutionSet planeZ3SEP.P circleSection = TrivialBundle.circleMap ⁻¹' {0} := by
      ext x
      exact isZeroAt_graphSection_iff (n := 2) (k := 1) (φ := TrivialBundle.circleMap) (x := x)
    rw [h]
    exact isCompact_circleMap_zero
  exact hK.image planeZ3SEP.X.continuous_π

theorem hasScPlusSectionsThrough_cube_planeZ3 :
    (planeZ3SEP.cubeSEP 1).B.HasScPlusSectionsThrough := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) planeZ3SEP.X.PObj
  have hb : (planeZ3SEP.cubeSEP 1).X.PObj.AdmitsBumpFunctions :=
    admitsBumpFunctions_prod_cube (admitsBumpFunctions_epSEP 2 1)
  exact MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hb

/-- **All hypotheses of Corollary 15.4.4 (`corollary_15_4_4_oriented`, `m = 0`) hold for the
circle section over `ℤ/3 × ℝ² ⇉ ℝ²`**, with non-zero fibres, a morphism that is not a unit, a
base which is not effective and a non-empty solution set: `d_X ≡ 0`, `|X|` is paracompact, `X`
and `[0, 1] × X` have sc-smooth partitions of unity, `f` is an sc-Fredholm section functor with
tame germ data, `|S_f|` is compact, `circleSectionOrientation` is an orientation of `f`
(Definition 6.6.16) invariant under the morphisms (Definition 12.5.4), and `f` has index `1` at
every point. -/
theorem corollary_15_4_4_hypotheses_planeZ3 :
    (∀ y : planeZ3SEP.Obj, Nontrivial (planeZ3SEP.P ⁻¹' {y})) ∧
    (∃ σ : planeZ3SEP.Mor, σ ≠ planeZ3SEP.X.unit (planeZ3SEP.X.src σ)) ∧
    ¬ planeZ3SEP.X.IsEffective ∧
    (solutionSet planeZ3SEP.P circleSection).Nonempty ∧
    (∀ x, planeZ3SEP.X.PObj.degIndex x = 0) ∧
    planeZ3SEP.X.HasParacompactOrbitSpace ∧ planeZ3SEP.X.HasScPartitionsOfUnity ∧
    (planeZ3SEP.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    planeZ3SEP.E.IsScFredholmSectionFunctor circleSection ∧
    planeZ3SEP.B.IsScFredholmSectionTame circleSection ∧
    planeZ3SEP.E.HasCompactSolutionSetEp circleSection ∧
    (haveI := paracompactSpace_rn_prod planeZ3SEP.X.PObj
     haveI := paracompactSpace_rn_pullback planeZ3SEP.B
     IsSectionOrientation (B := planeZ3SEP.B) circleSection
       isScFredholmSectionFunctor_circle_planeZ3.2 circleSectionOrientation) ∧
    planeZ3SEP.E.IsOrInvariant isScFredholmSectionFunctor_circle_planeZ3
      (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation ∧
    ∀ x ∈ planeZ3SEP.X.PObj.smoothSet,
      planeZ3SEP.B.IsIndexAt circleSection x ((0 + 1 : ℕ) : ℤ) := by
  have hpara := hasParacompactOrbitSpace_planeZ3
  have hPUobj : planeZ3SEP.X.PObj.AdmitsScPartitionsOfUnity :=
    rnPolyfold_admitsScPartitionsOfUnity 2
  exact ⟨fun y => (fibEquiv (n := 2) (k := 1) y).nontrivial, ne_unit_z3SEPOf _ 0,
    not_isEffective_z3SEPOf _ 0,
    ⟨fun i => if i = 0 then 1 else 0,
      (isZeroAt_graphSection_iff (n := 2) (k := 1) (φ := TrivialBundle.circleMap)).2
        ((circleMap_eq_zero_iff _).2 (by norm_num))⟩,
    fun x => MPolyfold.degIndex_rn x, hpara, planeZ3SEP.X.theorem_7_5_7 hpara hPUobj,
    admitsScPartitionsOfUnity_cubeSEP 1 hPUobj, isScFredholmSectionFunctor_circle_planeZ3,
    isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap,
    hasCompactSolutionSetEp_circle_planeZ3, isSectionOrientation_circleSectionOrientation,
    isOrInvariant_z3SEPOf _ _ _ _, fun x _ => isIndexAt_circleSection x⟩

/-- **Corollary 15.4.4 (2021 p. 703) for the circle section over `ℤ/3 × ℝ² ⇉ ℝ²`**
(`corollary_15_4_4_oriented` applied to `corollary_15_4_4_hypotheses_planeZ3`): exact
`1`-forms integrate to `0` over every regular perturbation of `f` with the canonical orientation
of `(f, o)`, and a closed `1`-form has the same integral over any two of them; the weights of the
branched integrals are `1/♯G_x = 1/3`. -/
theorem corollary_15_4_4_planeZ3 :
    corollary_15_4_4_statement planeZ3SEP circleSection 0
      (IsCanonicalPerturbation isScFredholmSectionFunctor_circle_planeZ3.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation) := by
  obtain ⟨-, -, -, -, hd, hpara, hPU, hPUC, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_planeZ3
  exact corollary_15_4_4_oriented hd hF hft (hasScPlusSectionsThrough_epSEP 2 1)
    hasScPlusSectionsThrough_cube_planeZ3 circleSectionOrientation ho hinv hidx hpara hPU hPUC hS

/-- **`Λ₀` is a regular perturbation of the circle section over `ℤ/3 × ℝ² ⇉ ℝ²`**
(Corollary 15.3.10). -/
theorem exists_isRegularPerturbation_planeZ3 :
    ∃ (N : planeZ3SEP.B.One → ℝ) (U : Set planeZ3SEP.Obj),
      IsRegularPerturbation planeZ3SEP circleSection N U (zeroMultisection planeZ3SEP) := by
  have hpara := hasParacompactOrbitSpace_planeZ3
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 planeZ3SEP.E hpara
  obtain ⟨U, hcc⟩ := exists_controlsCompactness isScFredholmSectionFunctor_circle_planeZ3
    hasCompactSolutionSetEp_circle_planeZ3 hN
  have hN0 := pointwiseNorm_zeroMultisection (A := planeZ3SEP) hcc.1.isAuxNorm
  exact ⟨N, U, hcc, isStructurable_zeroMultisection hpara,
    by rw [domSupp_zeroMultisection]; exact empty_subset _,
    fun x => by rw [hN0]; exact one_pos,
    isTransversal_graphSection_rnZ3 contDiff_circleMap fun _ h => surjective_fderiv_circleMap h⟩

/-- **A canonically oriented regular perturbation over `ℤ/3 × ℝ² ⇉ ℝ²`** (Definition 15.4.2,
Corollary 15.4.4): an oriented regular perturbation `P` of the circle section of dimension
`0 + 1` with `P.Λ = Λ₀` and the canonical orientation of `(f, circleSectionOrientation)`; the
support of `Λ₀ ∘ f` (the unit circle) is not empty. -/
theorem exists_isCanonicalPerturbation_planeZ3 :
    ∃ P : OrientedRegularPerturbation planeZ3SEP circleSection 0,
      P.Λ = zeroMultisection planeZ3SEP ∧
      IsCanonicalPerturbation isScFredholmSectionFunctor_circle_planeZ3.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation P ∧
      (EpGroupoid.supp (fun z => (P.Λ (circleSection z) : ℚ))).Nonempty := by
  obtain ⟨-, -, -, -, hd, -, -, -, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_planeZ3
  obtain ⟨N, U, hreg⟩ := exists_isRegularPerturbation_planeZ3
  have hbd : ∀ x : planeZ3SEP.Obj, x ∉ planeZ3SEP.X.PObj.boundary := fun x hx => by
    have h : (0 : ℕ) < planeZ3SEP.X.PObj.degIndex x := hx
    rw [hd x] at h
    exact lt_irrefl _ h
  have hgood : ∀ x ∈ planeZ3SEP.X.PObj.boundary,
      0 < zeroMultisection planeZ3SEP (circleSection x) →
      SBLocalization.IsGoodPositionAt (A := planeZ3SEP) circleSection
        (zeroMultisection planeZ3SEP) x :=
    fun x hx _ => absurd hx (hbd x)
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => (zeroMultisection planeZ3SEP (circleSection z) : ℚ)),
      planeZ3SEP.B.IsIndexAt circleSection x ((0 + 1 : ℕ) : ℤ) := fun x _ =>
    isIndexAt_circleSection x
  refine ⟨OrientedRegularPerturbation.canonical (A := planeZ3SEP) (m := 0) (isTame_epSEP 2 1)
      (admitsBumpFunctions_epSEP 2 1) hF hft (hasScPlusSectionsThrough_epSEP 2 1) _ hinv ho hreg
      hgood hidx', rfl,
    isCanonicalPerturbation_canonical (A := planeZ3SEP) (m := 0) (isTame_epSEP 2 1)
      (admitsBumpFunctions_epSEP 2 1)
      hF hft (hasScPlusSectionsThrough_epSEP 2 1) _ hinv ho hreg hgood hidx',
    ⟨fun i => if i = 0 then 1 else 0, ?_⟩⟩
  change (0 : ℚ) < _
  exact_mod_cast (zeroMultisection_graphSection_rnZ3_pos_iff (φ := TrivialBundle.circleMap) _).2
    ((circleMap_eq_zero_iff _).2 (by norm_num))

end TrivialIsotropy

end Polyfold
