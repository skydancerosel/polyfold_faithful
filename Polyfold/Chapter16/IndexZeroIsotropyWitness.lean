import Polyfold.Chapter16.IndexZeroCylinderWitness
import Polyfold.Chapter16.CylinderInvarianceNonEffective

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) for Fredholm index `0`, on an example with
isotropy.

# Two signed points with isotropy `ℤ/3`

The strong bundle `ℝ × ℝ → ℝ` over the ep-groupoid `ℤ/3 × ℝ ⇉ ℝ` (trivial action), with the
section `f(x) = (x, x² − 1)`: the fibres are not zero, the morphisms are not all units (every
isotropy group is `ℤ/3`, the ep-groupoid is not effective), `f` has Fredholm index `0`, and the
solution set is `{−1, 1}`.

## What is formalized (namespace `Polyfold.StrongBundleLocalizationExamples`)

* `zeroMultisection_graphSection_z3_pos_iff`, `isTransversal_graphSection_z3`: the graph
  section of a `C^∞` map with `0` a regular value is transversal to the zero section over
  `ℤ/3 × ℝ ⇉ ℝ`.
* **`corollary_15_4_4_index_zero_hypotheses_z3`**: all hypotheses of
  `corollary_15_4_4_index_zero_oriented` hold, with non-zero fibres, a morphism that is not a
  unit, and `S_f = {−1, 1}`.
* **`exists_isCanonical_z3`**: a canonically oriented regular perturbation of dimension `0`
  with support `{−1, 1}`.
* **`corollary_15_4_4_index_zero_z3`**, `hasOrientedCobordism_z3`: the conclusion of the
  corollary and the cobordism of the cylinder.
* `indexZeroInput_z3OrientationRep`: the standing hypotheses of Theorem 16.6.6 for index `0`
  in the model of the orientation `z3OrientationRep`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15 SEP
  StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle

section Transversal

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

/-- `Λ₀(f(x)) > 0` iff `φ(x) = 0`, for the multisection `Λ₀` of the zero section over
`ℤ/3 × ℝ ⇉ ℝ`. -/
theorem zeroMultisection_graphSection_z3_pos_iff (x : Fin 1 → ℝ) :
    0 < zeroMultisection (z3SEP k) (graphSection φ x) ↔ φ x = 0 := by
  classical
  have aux : ∀ w : (z3SEP k).W, w = graphSection φ x →
      (0 < zeroMultisection (z3SEP k) w ↔ φ x = 0) := by
    intro w hw
    have key : w = fiberZero (z3SEP k).P ((z3SEP k).P w) ↔ φ x = 0 := by
      subst hw
      exact isZeroAt_graphSection_iff (n := 1) (k := k) (φ := φ) (x := x)
    unfold zeroMultisection
    by_cases h : w = fiberZero (z3SEP k).P ((z3SEP k).P w)
    · rw [if_pos h]
      exact iff_of_true one_pos (key.1 h)
    · rw [if_neg h]
      exact iff_of_false (lt_irrefl _) fun h' => h (key.2 h')
  exact aux _ rfl

/-- **The graph section of a `C^∞` map with `0` a regular value is transversal to the zero
section over `ℤ/3 × ℝ ⇉ ℝ`** (Definition 15.2.1 for `Λ₀`): at a zero `x₀`, in the chart
centred at `x₀`, `(f − 0)'(x₀) = Dφ(x₀)` is onto `ℝᵏ`. -/
theorem isTransversal_graphSection_z3 (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x, φ x = 0 → Surjective (fderiv ℝ φ x)) :
    IsTransversal (A := z3SEP k) (graphSection φ) (zeroMultisection (z3SEP k)) := by
  classical
  have hf : (z3SEP k).E.IsScFredholmSectionFunctor (graphSection φ) :=
    isScFredholmSectionFunctor_graphSection_z3 hφ
  intro x₀ hpos
  have h0 : φ x₀ = 0 := (zeroMultisection_graphSection_z3_pos_iff x₀).1 hpos
  have hx1 : x₀ ∈ (z3SEP k).X.PObj.levelSet 1 := by
    have h : (x₀ : Fin 1 → ℝ) ∈ (rnPolyfold 1).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hpos, hx1, ?_⟩
  set x := (z3SEP k).X.PObj.levelMk 1 x₀ hx1 with hxdef
  intro L hL
  have hxv : (z3SEP k).X.PObj.levelVal 1 x = x₀ := (z3SEP k).X.PObj.levelVal_levelMk _ _ _
  let c : StrongBundleChart (z3SEP k).X.PObj (z3SEP k).P := chart (k := k) x₀
  have hc : (z3SEP k).B.IsChart c := isChart_chart x₀
  have hx : (z3SEP k).X.PObj.levelVal 1 x ∈ c.φ.source := mem_univ _
  have hx0 : graphSection φ ((z3SEP k).X.PObj.levelVal 1 x) =
      fiberZero (z3SEP k).P ((z3SEP k).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (n := 1) (k := k) (φ := φ) (x := x₀)).2 h0
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (isScPlusSectionOn_fiberZero isOpen_univ) hc
    (subset_univ _) hx hx0).2 ?_
  set z := levelLift c.φ 1 ((z3SEP k).X.PObj.levelVal 1 x) with hzdef
  have hz : z = 0 := by
    have h1 : c.φ.model.E.toBase 1 z = c.φ ((z3SEP k).X.PObj.levelVal 1 x) :=
      (z3SEP k).X.PObj.toBase_levelLift c.isChart hx ((z3SEP k).X.PObj.levelVal_mem x)
    rw [hxv] at h1
    have h2 : c.φ x₀ = (0 : Fin 1 → ℝ) := sub_self (show Fin 1 → ℝ from x₀)
    exact h1.trans h2
  have he : ((fun y => c.principal (graphSection φ) y -
      c.principal (fiberZero (z3SEP k).P) y) ∘ r c.R) = loc φ x₀ := by
    funext u
    have h2 : c.principal (fiberZero (z3SEP k).P) u = 0 :=
      c.snd_fiberZero (x := c.φ.symm u) (mem_univ _)
    change c.principal (graphSection φ) u - c.principal (fiberZero (z3SEP k).P) u = _
    rw [h2, sub_zero]
    rfl
  intro w _
  obtain ⟨v, hv⟩ := hreg x₀ h0 w
  refine ⟨v, ⟨v, ?_⟩, ?_⟩
  · rw [hz]
    exact congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T v) (scDeriv_r (k := k) x₀)
  · change scDeriv c.U ((fun y => c.principal (graphSection φ) y -
      c.principal (fiberZero (z3SEP k).P) y) ∘ r c.R) z v = w
    rw [he, hz]
    exact (congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc k) 0 => T v) (scDeriv_loc hφ x₀)).trans hv

end Transversal

/-! ### The section `x ↦ (x, x² − 1)` over `ℤ/3 × ℝ ⇉ ℝ` -/

/-- **`|S_f|` is compact** (Definition 12.4.1 (1)): `S_f = {−1, 1}`. -/
theorem hasCompactSolutionSetEp_twoPoint_z3 :
    (z3SEP 1).E.HasCompactSolutionSetEp (graphSection twoPointMap) := by
  have hK : IsCompact (solutionSet (z3SEP 1).P (graphSection twoPointMap)) := by
    have h : solutionSet (z3SEP 1).P (graphSection twoPointMap) = twoPointMap ⁻¹' {0} := by
      ext x
      exact isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := twoPointMap) (x := x)
    rw [h]
    exact isCompact_twoPointMap_zero
  exact hK.image (z3SEP 1).X.continuous_π

/-- **The index of `f` is `0`** at every point. -/
theorem isIndexAt_twoPoint_z3 (x : (z3SEP 1).Obj) :
    (z3SEP 1).B.IsIndexAt (graphSection twoPointMap) x 0 :=
  isIndexAt_twoPointSection x

/-- **All hypotheses of Corollary 15.4.4 for index `0`
(`corollary_15_4_4_index_zero_oriented`) hold for `f(x) = (x, x² − 1)` over `ℤ/3 × ℝ ⇉ ℝ`**,
with non-zero fibres, a morphism that is not a unit, and the solution set `{−1, 1}`: `d_X ≡ 0`,
`|X|` is paracompact, `X` and `[0, 1] × X` have sc-smooth partitions of unity, `f` is an
sc-Fredholm section functor with tame germ data, `|S_f|` is compact, `z3Orientation` is an
orientation of `f` (Definition 6.6.16) invariant under the morphisms (Definition 12.5.4), and
`f` has index `0` at every point. -/
theorem corollary_15_4_4_index_zero_hypotheses_z3 :
    (∀ y : (z3SEP 1).Obj, Nontrivial ((z3SEP 1).P ⁻¹' {y})) ∧
    (∃ σ : (z3SEP 1).Mor, σ ≠ (z3SEP 1).X.unit ((z3SEP 1).X.src σ)) ∧
    (fun _ => (1 : ℝ)) ∈ solutionSet (z3SEP 1).P (graphSection twoPointMap) ∧
    (fun _ => (-1 : ℝ)) ∈ solutionSet (z3SEP 1).P (graphSection twoPointMap) ∧
    (∀ x, (z3SEP 1).X.PObj.degIndex x = 0) ∧
    (z3SEP 1).X.HasParacompactOrbitSpace ∧ (z3SEP 1).X.HasScPartitionsOfUnity ∧
    ((z3SEP 1).cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    (z3SEP 1).E.IsScFredholmSectionFunctor (graphSection twoPointMap) ∧
    (z3SEP 1).B.IsScFredholmSectionTame (graphSection twoPointMap) ∧
    (z3SEP 1).E.HasCompactSolutionSetEp (graphSection twoPointMap) ∧
    (haveI := paracompactSpace_rn_prod (z3SEP 1).X.PObj
     haveI := paracompactSpace_rn_pullback (z3SEP 1).B
     IsSectionOrientation (B := (z3SEP 1).B) (graphSection twoPointMap)
       (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap).2
       (z3Orientation contDiff_twoPointMap)) ∧
    (z3SEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap)
      (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap) ∧
    ∀ x ∈ (z3SEP 1).X.PObj.smoothSet,
      (z3SEP 1).B.IsIndexAt (graphSection twoPointMap) x 0 := by
  have := paracompactSpace_rn_prod (z3SEP 1).X.PObj
  have := paracompactSpace_rn_pullback (z3SEP 1).B
  have := paracompactSpace_rn_rn_prod (z3SEP 1).X.PObj
  have := paracompactSpace_rn_rn_pullback (z3SEP 1).B
  have hpara : (z3SEP 1).X.HasParacompactOrbitSpace :=
    EpGroupoid.Examples.hasParacompactOrbitSpace_trivialZ3
  have hPUobj : (z3SEP 1).X.PObj.AdmitsScPartitionsOfUnity :=
    rnPolyfold_admitsScPartitionsOfUnity 1
  have hdef := definition_12_5_4_z3Orientation (k := 1) contDiff_twoPointMap
  exact ⟨fun y => (TrivialBundle.fibEquiv (n := 1) (k := 1) y).nontrivial, ne_unit_z3SEP 1,
    (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := twoPointMap)).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num)),
    (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := twoPointMap)).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num)),
    fun x => MPolyfold.degIndex_rn x, hpara, (z3SEP 1).X.theorem_7_5_7 hpara hPUobj,
    admitsScPartitionsOfUnity_cubeSEP 1 hPUobj,
    isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap,
    isScFredholmSectionTame_graphSection_z3 contDiff_twoPointMap,
    hasCompactSolutionSetEp_twoPoint_z3,
    (isSectionOrientation_iff_continuous (isTame_z3SEP 1) (admitsBumpFunctions_z3SEP 1)
      (isScFredholmSectionTame_graphSection_z3 contDiff_twoPointMap)
      (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap)).2 hdef.1,
    hdef.2, fun x _ => isIndexAt_twoPoint_z3 x⟩

/-- **`Λ₀` is a regular perturbation of `f`** over `ℤ/3 × ℝ ⇉ ℝ` (Corollary 15.3.10). -/
theorem exists_isRegularPerturbation_twoPoint_z3 :
    ∃ (N : (z3SEP 1).B.One → ℝ) (U : Set (z3SEP 1).Obj),
      IsRegularPerturbation (z3SEP 1) (graphSection twoPointMap) N U
        (zeroMultisection (z3SEP 1)) := by
  have hpara : (z3SEP 1).X.HasParacompactOrbitSpace :=
    EpGroupoid.Examples.hasParacompactOrbitSpace_trivialZ3
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (z3SEP 1).E hpara
  obtain ⟨U, hcc⟩ := exists_controlsCompactness
    (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap)
    hasCompactSolutionSetEp_twoPoint_z3 hN
  have hN0 := pointwiseNorm_zeroMultisection (A := z3SEP 1) hcc.1.isAuxNorm
  exact ⟨N, U, hcc, isStructurable_zeroMultisection hpara,
    by rw [domSupp_zeroMultisection]; exact empty_subset _,
    fun x => by rw [hN0]; exact one_pos,
    isTransversal_graphSection_z3 contDiff_twoPointMap fun _ h => surjective_fderiv_twoPointMap h⟩

/-- **A canonically oriented regular perturbation of dimension `0` over `ℤ/3 × ℝ ⇉ ℝ`**
(Definition 15.4.2, Corollary 15.4.4 for index `0`): a regular perturbation `P` of
`f(x) = (x, x² − 1)` of dimension `0` with `P.Λ = Λ₀` and the canonical orientation of `(f, o)`;
both points `±1` lie in the support of `Λ₀ ∘ f`. -/
theorem exists_isCanonical_z3 :
    ∃ P : PointPerturbation (z3SEP 1) (graphSection twoPointMap),
      P.Λ = zeroMultisection (z3SEP 1) ∧
      P.IsCanonical (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap).2
        (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap) ∧
      (fun _ => (1 : ℝ)) ∈
        EpGroupoid.supp (fun z => (P.Λ (graphSection twoPointMap z) : ℚ)) ∧
      (fun _ => (-1 : ℝ)) ∈
        EpGroupoid.supp (fun z => (P.Λ (graphSection twoPointMap z) : ℚ)) := by
  obtain ⟨-, -, -, -, hd, -, -, -, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_z3
  obtain ⟨N, U, hreg⟩ := exists_isRegularPerturbation_twoPoint_z3
  have hbd : ∀ x : (z3SEP 1).Obj, x ∉ (z3SEP 1).X.PObj.boundary := fun x hx => by
    have h : (0 : ℕ) < (z3SEP 1).X.PObj.degIndex x := hx
    rw [hd x] at h
    exact lt_irrefl _ h
  have hgood : ∀ x ∈ (z3SEP 1).X.PObj.boundary,
      0 < zeroMultisection (z3SEP 1) (graphSection twoPointMap x) →
      SBLocalization.IsGoodPositionAt (graphSection twoPointMap) (zeroMultisection (z3SEP 1)) x :=
    fun x hx _ => absurd hx (hbd x)
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => (zeroMultisection (z3SEP 1) (graphSection twoPointMap z) : ℚ)),
      (z3SEP 1).B.IsIndexAt (graphSection twoPointMap) x (0 : ℕ) := fun x _ => by
    exact_mod_cast isIndexAt_twoPoint_z3 x
  refine ⟨PointPerturbation.canonical (isTame_z3SEP 1) (admitsBumpFunctions_z3SEP 1) hF hft
      (hasScPlusSectionsThrough_z3SEP 1) _ hinv ho hreg hgood hidx', rfl,
    PointPerturbation.isCanonical_canonical (isTame_z3SEP 1) (admitsBumpFunctions_z3SEP 1)
      hF hft (hasScPlusSectionsThrough_z3SEP 1) _ hinv ho hreg hgood hidx', ?_, ?_⟩
  · change (0 : ℚ) < _
    exact_mod_cast (zeroMultisection_graphSection_z3_pos_iff (φ := twoPointMap) _).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num))
  · change (0 : ℚ) < _
    exact_mod_cast (zeroMultisection_graphSection_z3_pos_iff (φ := twoPointMap) _).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num))

/-- **Corollary 15.4.4 (2021 p. 703) for Fredholm index `0`, for `f(x) = (x, x² − 1)` over
`ℤ/3 × ℝ ⇉ ℝ`** (`corollary_15_4_4_index_zero_oriented` applied to the instance of
`corollary_15_4_4_index_zero_hypotheses_z3`): a closed `0`-form has the same weighted signed
count `∫` (weights `1/3`) and the same effective count `∮` over any two regular perturbations
of dimension `0` with the canonical orientation of `(f, o)`. -/
theorem corollary_15_4_4_index_zero_z3
    (P₀ P₁ : PointPerturbation (z3SEP 1) (graphSection twoPointMap))
    (h₀ : P₀.IsCanonical (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap).2
      (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap))
    (h₁ : P₁.IsCanonical (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap).2
      (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap))
    (τ : (z3SEP 1).baseEP.epFormsInfty 0) (hτ : (z3SEP 1).baseEP.epFormsInftyD 0 τ = 0) :
    P₀.count τ = P₁.count τ ∧
      ∀ hLUC : (z3SEP 1).X.IsLUC, P₀.countEff hLUC τ = P₁.countEff hLUC τ := by
  obtain ⟨-, -, -, -, hd, hpara, hPU, hPUC, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_z3
  exact corollary_15_4_4_index_zero_oriented hd hF hft (hasScPlusSectionsThrough_z3SEP 1)
    (z3Orientation contDiff_twoPointMap) ho hidx hinv hpara hPU hPUC hS P₀ P₁ h₀ h₁ τ hτ

/-- **The cobordism of the cylinder over `ℤ/3 × ℝ ⇉ ℝ`**: any two canonically oriented regular
perturbations of dimension `0` of `f(x) = (x, x² − 1)` are joined by an oriented compact
cobordism of dimension `1` over `[0, 1] × (ℤ/3 × ℝ ⇉ ℝ)`. -/
theorem hasOrientedCobordism_z3
    (P₀ P₁ : PointPerturbation (z3SEP 1) (graphSection twoPointMap))
    (h₀ : P₀.IsCanonical (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap).2
      (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap))
    (h₁ : P₁.IsCanonical (isScFredholmSectionFunctor_graphSection_z3 contDiff_twoPointMap).2
      (hasScPlusSectionsThrough_z3SEP 1) (z3Orientation contDiff_twoPointMap)) :
    P₀.HasOrientedCobordism P₁ := by
  obtain ⟨-, -, -, -, hd, hpara, hPU, hPUC, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_z3
  exact (hasOrientedCobordism_of_isCanonical hd hF hft (hasScPlusSectionsThrough_z3SEP 1)
    (z3Orientation contDiff_twoPointMap) ho hidx hinv hpara hPU hPUC hS P₀ P₁ h₀ h₁).1

/-- **The standing hypotheses of Theorem 16.6.6 for index `0` hold in a model with isotropy**:
`StrongPolyfoldBundle.IndexZeroInput` for the orientation `z3OrientationRep` of the sc-Fredholm
section `|x| ↦ |(x, x² − 1)|` of the strong polyfold bundle over `|ℤ/3 × ℝ ⇉ ℝ|`. -/
theorem indexZeroInput_z3OrientationRep :
    StrongPolyfoldBundle.IndexZeroInput (z3OrientationRep (k := 1) contDiff_twoPointMap) := by
  obtain ⟨-, -, -, -, -, -, -, hPUC, -, hft, -, ho, -, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_z3
  exact ⟨hPUC, hft, ho, hidx⟩

end StrongBundleLocalizationExamples

end Polyfold
