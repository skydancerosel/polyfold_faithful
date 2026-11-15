import Polyfold.Chapter15.CanonicalOrientationStokes
import Polyfold.Chapter15.TransversalExtensionWitness
import Polyfold.Chapter16.HalfSpaceOrientedSection
import Polyfold.Chapter6.UntamedIndexJump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–703: **an instance with boundary and non-zero fibres** of all hypotheses of
**Theorem 15.4.1** (the canonical orientation of `Θ = Λ ∘ f`) and of the canonically oriented
regular perturbation of **Definition 15.4.2** and **Corollary 15.4.4**.

# The canonical orientation on the half-disc example

## The example

The base is the half-plane `H = [0, ∞) × ℝ` with the trivial ep-groupoid, the bundle is
`H × ℝ → H` (`HalfSpaceBundle.halfSEP 1 1`), the section is the graph section
`f(a, y) = ((a, y), a² + y² − 1)` of `φ(a, y) = a² + y² − 1`, and `Λ` is the multisection of the
zero section.  The support of `Θ = Λ ∘ f` is the half circle `{a² + y² = 1, a ≥ 0}`, which
meets `∂H = {0} × ℝ` in the two points `(0, ±1)`.  At every point of the half circle
`Dφ(a, y) = (2a, 2y) ≠ 0` is onto `ℝ`, and at `(0, ±1)` it is onto on `T^R H = {0} × ℝ`: the pair
`(f, Λ)` is in general position, hence in good position, at every point of the support.  The
linearization `Dφ(a, y) : ℝ ⊕ ℝ → ℝ` has index `2 − 1 = 1`, and every sc-Fredholm section over
the convex set `H` is orientable.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

* `chartPointAt`, `finrank_T_chartPointAt`, `finrank_K_chartPointAt`,
  **`isIndexAt_graphSection_halfSEP`**: on `H × ℝᵏ → H = [0, ∞) × ℝᵐ`, the graph section of a
  `C^∞` map has index `(m + 1) − k` at every point (Definition 6.2.1), read in the chart
  centred at the point, where `T_0O = ℝ ⊕ ℝᵐ` and `K_0 = ℝᵏ`.
* `isInGeneralPositionAt_graphSection_of_presentation`,
  `isInGeneralPositionAt_graphSection_interior`: general position (Definition 15.3.5) of the
  graph section and the zero multisection at an interior zero `x₀` with `Dφ(x₀)` onto.
* `isInGeneralPositionAt_halfDisc`, `isGoodPositionAt_halfDisc`, `isTransversal_halfDisc`,
  `isIndexAt_halfDisc`: general position, good position (Definition 15.2.4), transversality
  (Definition 15.2.1) and index `1` on the half circle.
* `isSectionOrientation_halfOrientation`: `halfOrientation` is an orientation in the sense of
  Definition 6.6.16.
* **`theorem_15_4_1_hypotheses_halfSEP`**: `∂X ≠ ∅`, every fibre non-zero, `supp(Λ ∘ f) ∩ ∂X`
  non-empty, and every hypothesis of `theorem_15_4_1` with `n = 1`;
  **`theorem_15_4_1_halfSEP`**: the conclusion of Theorem 15.4.1 there.
* `exists_isRegularPerturbation_halfDisc`, **`exists_isCanonicalPerturbation_halfSEP`**: `Λ` is
  a regular perturbation of `f` for an auxiliary norm `N` and a saturated open `U`, and with its
  canonical orientation it is an oriented regular perturbation of dimension `0 + 1` satisfying
  the predicate `IsCanonicalPerturbation` of Corollary 15.4.4, with support meeting `∂X`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-! ### The index of the graph section -/

/-- The chart point of the chart centred at `x₀`: the level-`1` point over `φ(x₀) = 0` is `0`. -/
def chartPointAt (x₀ : H m) : ChartPoint (bundle m k) x₀ where
  c := chartAt x₀
  isChart := isChart_chartAt x₀
  mem_source := mem_source_chartAt x₀
  z := 0
  toBase_z := by rw [map_zero]; exact (chartAt_self x₀).symm

/-- `T_0O = ℝ ⊕ ℝᵐ` in the chart centred at `x₀`. -/
theorem T_chartPointAt (x₀ : H m) : (chartPointAt (k := k) x₀).T = ⊤ := by
  change rangeS (scDeriv (chartAt (k := k) x₀).U (r (chartAt (k := k) x₀).R) 0) = ⊤
  rw [rangeS, scDeriv_r_chartAt]
  exact LinearMap.range_id

/-- `K_0 = ℝᵏ` in the chart centred at `x₀`. -/
theorem K_chartPointAt (x₀ : H m) : (chartPointAt (k := k) x₀).K = ⊤ :=
  eq_top_iff.2 fun h _ => ⟨h, rfl⟩

instance (x₀ : H m) : FiniteDimensional ℝ ↥(chartPointAt (k := k) x₀).T :=
  haveI : FiniteDimensional ℝ ((chartPointAt (k := k) x₀).c.φ.model.E 0) :=
    (inferInstance : FiniteDimensional ℝ (Pm m))
  inferInstance

instance (x₀ : H m) : FiniteDimensional ℝ ↥(chartPointAt (k := k) x₀).K :=
  haveI : FiniteDimensional ℝ ((chartPointAt (k := k) x₀).c.F 0) :=
    (inferInstance : FiniteDimensional ℝ (Fin k → ℝ))
  inferInstance

theorem finrank_T_chartPointAt (x₀ : H m) :
    finrank ℝ ↥(chartPointAt (k := k) x₀).T = m + 1 := by
  rw [T_chartPointAt]
  have h : finrank ℝ (Pm m) = m + 1 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, add_comm]
  exact (finrank_top ℝ _).trans h

theorem finrank_K_chartPointAt (x₀ : H m) :
    finrank ℝ ↥(chartPointAt (k := k) x₀).K = k := by
  rw [K_chartPointAt]
  have h : finrank ℝ (Fin k → ℝ) = k := Module.finrank_fin_fun ℝ
  exact (finrank_top ℝ _).trans h

/-- **The index of the graph section** (Definition 6.2.1): on `H × ℝᵏ → H = [0, ∞) × ℝᵐ`, the
graph section of a `C^∞` map `φ` has index `(m + 1) − k` at every point `x₀`: a member of
`Lin(f, x₀)` is an operator `ℝ ⊕ ℝᵐ → ℝᵏ` in the chart centred at `x₀`. -/
theorem isIndexAt_graphSection_halfSEP (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) :
    (halfSEP m k).B.IsIndexAt (graphSection φ) x₀ (((m + 1 : ℕ) : ℤ) - (k : ℕ)) := by
  have hf : (bundle m k).IsScFredholmSection (graphSection φ) :=
    (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2
  obtain ⟨L, hL⟩ := (chartPointAt (k := k) x₀).linSet_nonempty hf
    (by rw [smoothSet_eq_univ]; exact mem_univ x₀) (hasScPlusSectionsThrough_halfSEP m k)
  have h := ((chartPointAt (k := k) x₀).isFredholm_isIndexAt_of_mem_linSet hf hL).2
  rwa [fredholmIndex_of_finiteDimensional, finrank_T_chartPointAt, finrank_K_chartPointAt] at h

/-! ### General position at an interior zero -/

/-- **General position at a zero, for a presentation of the partial quadrant of the centred
chart** (Definition 15.3.5 at one point): if `φ(x₀) = 0` and `Dφ(x₀)` maps the reduced tangent
space of the presentation `T` at `0` onto `ℝᵏ`, the graph section of `φ` and the multisection of
the zero section are in general position at `x₀`. -/
theorem isInGeneralPositionAt_graphSection_of_presentation (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso (halfSpaceSc m) ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : (chartAt (k := k) x₀).φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (honto : ∀ w : Fin k → ℝ, ∃ v : Pm m, v ∈ minimalSubspaceWith T 0 ∧
      fderiv ℝ φ (x₀ : Pm m) v = w) :
    IsInGeneralPositionAt (A := halfSEP m k) (graphSection φ) (zeroMultisection (halfSEP m k))
      x₀ := by
  classical
  have hf := isScFredholmSectionFunctor_graphSection_halfSEP (k := k) hφ
  have hft := isScFredholmSectionTame_graphSection_halfSEP (k := k) hφ
  have hx1 : (show (halfSEP m k).Obj from x₀) ∈ (halfSEP m k).X.PObj.levelSet 1 := by
    change x₀ ∈ (basePoly m).levelSet 1
    rw [levelSet_eq_univ]; exact mem_univ _
  refine ⟨hx1, ?_⟩
  set x := (halfSEP m k).X.PObj.levelMk 1 x₀ hx1 with hxdef
  have hxv : (halfSEP m k).X.PObj.levelVal 1 x = x₀ := (halfSEP m k).X.PObj.levelVal_levelMk _ _ _
  set c : StrongBundleChart (halfSEP m k).X.PObj (halfSEP m k).P := chartAt (k := k) x₀ with hcdef
  have hc : (halfSEP m k).B.IsChart c := isChart_chartAt x₀
  have hx : (halfSEP m k).X.PObj.levelVal 1 x ∈ c.φ.source := by
    rw [hxv]; exact mem_source_chartAt x₀
  have hφ0 : c.φ ((halfSEP m k).X.PObj.levelVal 1 x) = 0 := by
    rw [hxv]; exact chartAt_self x₀
  have hx0 : graphSection φ ((halfSEP m k).X.PObj.levelVal 1 x) =
      fiberZero (halfSEP m k).P ((halfSEP m k).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (k := k) (φ := φ) (x := x₀)).2 h0
  intro L hL ψ hψ hxψ n' V T' hT'
  rw [← reducedTangentFiber_eq (hφ := c.isChart) (hx := hx) (T := T)
    (hψ := hψ) (hx' := hxψ) (T' := T') hT hT']
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  have key := (onto_chart_iff (A := halfSEP m k) (ℓ := 0) (s := fun j => j.elim0) (hft := hft)
    (hsec := fun j => j.elim0) (hc := hc) (hx := hx) (hφ0 := hφ0) (hx0 := hx0)
    (T := T)).2 ?_
  · intro w
    obtain ⟨v, hv, τ, he⟩ := key w
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he
    exact he
  · intro q _
    obtain ⟨v, hv0, hvq⟩ := honto q
    have htop : rangeS (scDeriv c.U (r c.R) 0) = ⊤ := by
      rw [rangeS, hcdef, scDeriv_r_chartAt]; exact LinearMap.range_id
    refine ⟨⟨v, by rw [htop]; exact Submodule.mem_top⟩, hv0, fun j => j.elim0, ?_⟩
    rw [linAt_apply, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change scDeriv (chartAt (k := k) x₀).U ((chartAt (k := k) x₀).principal (graphSection φ) ∘
      r (chartAt (k := k) x₀).R) 0 v = q
    rw [scDeriv_principal_comp_r_chartAt hφ x₀]
    exact hvq

/-- The presentation of `ℝ ⊕ ℝᵐ` as a partial quadrant without corner coordinates. -/
def interiorPresentation (m : ℕ) :
    ScIso (halfSpaceSc m) ((ScBanach.const (Fin 0 → ℝ)).prod (halfSpaceSc m)) where
  lvl := fun j => (ContinuousLinearEquiv.uniqueProd ℝ ((halfSpaceSc m) j) (Fin 0 → ℝ)).symm
  incl_comm := fun _ _ => Prod.ext (funext fun i => i.elim0) rfl

/-- **General position at an interior zero** (Definition 15.3.5 at one point): if `x₀ ∉ ∂H`,
`φ(x₀) = 0` and `Dφ(x₀)` is onto `ℝᵏ`, then the graph section of `φ` and the multisection of
the zero section are in general position at `x₀` (`T^R_{x₀}H = T_{x₀}H`). -/
theorem isInGeneralPositionAt_graphSection_interior (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) (hb : (x₀ : Pm m).1 0 ≠ 0)
    (honto : Surjective (fderiv ℝ φ (x₀ : Pm m))) :
    IsInGeneralPositionAt (A := halfSEP m k) (graphSection φ) (zeroMultisection (halfSEP m k))
      x₀ := by
  refine isInGeneralPositionAt_graphSection_of_presentation hφ h0 (interiorPresentation m) ?_
    fun w => ?_
  · refine (C_chartAt x₀).trans ?_
    rw [if_neg hb]
    exact (eq_univ_of_forall fun v i => i.elim0).symm
  · obtain ⟨v, hv⟩ := honto w
    exact ⟨v, (mem_minimalSubspaceWith (interiorPresentation m)).2 fun i _ => i.elim0, hv⟩

/-! ### The half-disc example -/

/-- `Dφ(a, y)` is onto `ℝ` at a zero with `a ≠ 0`: `Dφ(a, y)(α, 0) = 2 a α`. -/
theorem surjective_fderiv_halfDiscMap {x : Pm 1} (ha : x.1 0 ≠ 0) :
    Surjective (fderiv ℝ halfDiscMap x) := fun w => by
  refine ⟨(fun _ => w 0 / (2 * x.1 0), 0), ?_⟩
  rw [(hasFDerivAt_halfDiscMap x).fderiv]
  funext i
  rw [Subsingleton.elim i 0]
  simp [coordA, coordY]
  field_simp

/-- **General position on the half circle** (Definition 15.3.5): at every point of
`supp(Λ ∘ f)`, interior or on `∂H`. -/
theorem isInGeneralPositionAt_halfDisc {x : (halfSEP 1 1).Obj}
    (hpos : 0 < zeroMultisection (halfSEP 1 1) (halfDiscSection x)) :
    IsInGeneralPositionAt halfDiscSection (zeroMultisection (halfSEP 1 1)) x := by
  have h0 := (zeroMultisection_graphSection_pos_iff (k := 1) (φ := halfDiscMap) x).1 hpos
  by_cases hb : ((show H 1 from x) : Pm 1).1 0 = 0
  · exact isInGeneralPositionAt_graphSection contDiff_halfDiscMap h0 hb
      (halfDiscMap_onto_hyperplane h0 hb)
  · exact isInGeneralPositionAt_graphSection_interior contDiff_halfDiscMap h0 hb
      (surjective_fderiv_halfDiscMap hb)

/-- **Good position at every point of `supp(Λ ∘ f)`** (Definition 15.2.4). -/
theorem isGoodPositionAt_halfDisc (x : (halfSEP 1 1).Obj)
    (hx : x ∈ EpGroupoid.supp
      (fun z => (zeroMultisection (halfSEP 1 1) (halfDiscSection z) : ℚ))) :
    SBLocalization.IsGoodPositionAt halfDiscSection (zeroMultisection (halfSEP 1 1)) x := by
  have hpos : 0 < zeroMultisection (halfSEP 1 1) (halfDiscSection x) := by exact_mod_cast hx
  exact isGoodPositionAt_of_isInGeneralPositionAt
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _) hpos (isInGeneralPositionAt_halfDisc hpos)

/-- **`(f, Λ)` is transversal** (Definition 15.2.1). -/
theorem isTransversal_halfDisc :
    IsTransversal halfDiscSection (zeroMultisection (halfSEP 1 1)) :=
  ((isInGeneralPosition_iff_forall_at
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _)).2 fun _ hpos =>
      isInGeneralPositionAt_halfDisc hpos).isTransversal
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _)

/-- **The index of `f` is `1 = 2 − 1`** at every point of `H`. -/
theorem isIndexAt_halfDisc (x : (halfSEP 1 1).Obj) :
    (halfSEP 1 1).B.IsIndexAt halfDiscSection x ((1 : ℕ) : ℤ) := by
  have h := isIndexAt_graphSection_halfSEP contDiff_halfDiscMap x
  norm_num at h
  exact_mod_cast h

/-- **`halfOrientation` is an orientation of the graph section** (Definition 6.6.16): it is a
continuous section of `σ : O_F → H`. -/
theorem isSectionOrientation_halfOrientation (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    IsSectionOrientation (B := (halfSEP m k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2 (halfOrientation hφ) := by
  have := paracompactSpace_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_pullback (halfSEP m k).B
  have := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_rn_pullback (halfSEP m k).B
  exact (isSectionOrientation_iff_continuous (B := (halfSEP m k).B) (isTame_halfSEP m k)
    (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (hasScPlusSectionsThrough_halfSEP m k) (halfOrientation hφ)).2
    (definition_12_5_4_halfOrientation hφ).1

/-! ### Theorem 15.4.1 -/

/-- **All hypotheses of Theorem 15.4.1, with `∂X ≠ ∅` and non-zero fibres** (on `H × ℝ → H`,
`f(a, y) = ((a, y), a² + y² − 1)`, `Λ` the multisection of the zero section, `n = 1`): the
boundary is non-empty, every fibre is a non-zero vector space, `supp(Λ ∘ f)` meets `∂X` (at
`(0, 1)`), `X` is tame with sc-smooth bump functions, `f` is an sc-Fredholm section functor with
tame germ data, `Λ` is an sc⁺-multisection, there are sc⁺-sections through every smooth point,
`halfOrientation` is an orientation of `f` (Definition 6.6.16) invariant under the morphisms
(Definition 12.5.4), `(f, Λ)` is in good position at every point of `supp(Λ ∘ f)`, and `f` has
index `1` there. -/
theorem theorem_15_4_1_hypotheses_halfSEP :
    (halfSEP 1 1).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    (∃ x ∈ (halfSEP 1 1).X.PObj.boundary, x ∈ EpGroupoid.supp
      (fun z => (zeroMultisection (halfSEP 1 1) (halfDiscSection z) : ℚ))) ∧
    (halfSEP 1 1).X.PObj.IsTame ∧ (halfSEP 1 1).X.PObj.AdmitsBumpFunctions ∧
    (halfSEP 1 1).E.IsScFredholmSectionFunctor halfDiscSection ∧
    (halfSEP 1 1).B.IsScFredholmSectionTame halfDiscSection ∧
    IsScPlusMultisection (halfSEP 1 1) (zeroMultisection (halfSEP 1 1)) ∧
    (halfSEP 1 1).B.HasScPlusSectionsThrough ∧
    (halfSEP 1 1).E.IsOrInvariant
      (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
      (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) ∧
    (haveI := paracompactSpace_rn_prod (halfSEP 1 1).X.PObj
     haveI := paracompactSpace_rn_pullback (halfSEP 1 1).B
     IsSectionOrientation halfDiscSection
       (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap).2
       (halfOrientation contDiff_halfDiscMap)) ∧
    (∀ x ∈ EpGroupoid.supp (fun z => (zeroMultisection (halfSEP 1 1) (halfDiscSection z) : ℚ)),
      SBLocalization.IsGoodPositionAt halfDiscSection (zeroMultisection (halfSEP 1 1)) x) ∧
    ∀ x ∈ EpGroupoid.supp (fun z => (zeroMultisection (halfSEP 1 1) (halfDiscSection z) : ℚ)),
      (halfSEP 1 1).B.IsIndexAt halfDiscSection x ((1 : ℕ) : ℤ) :=
  ⟨⟨_, zero_mem_boundary_halfSEP 1 1⟩, nontrivial_fibre_halfSEP 1 1,
    ⟨_, topPoint_mem_boundary, by
      change (0 : ℚ) < _
      exact_mod_cast zeroMultisection_halfDisc_topPoint⟩,
    isTame_halfSEP 1 1, admitsBumpFunctions_halfSEP 1 1,
    isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap,
    isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap,
    isScPlusMultisection_zeroMultisection _, hasScPlusSectionsThrough_halfSEP 1 1,
    (definition_12_5_4_halfOrientation contDiff_halfDiscMap).2,
    isSectionOrientation_halfOrientation contDiff_halfDiscMap, isGoodPositionAt_halfDisc,
    fun x _ => isIndexAt_halfDisc x⟩

/-- **Theorem 15.4.1 on the half-disc example** (`theorem_15_4_1` applied to the instance of
`theorem_15_4_1_hypotheses_halfSEP`): `canonicalOrientation` is the canonical orientation of
`Θ = Λ ∘ f`, whose support is the half circle, a `1`-dimensional branched ep⁺-subgroupoid with
boundary. -/
theorem theorem_15_4_1_halfSEP :
    IsCanonicalFor (zeroMultisection (halfSEP 1 1))
      (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
      (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) 1
      (canonicalOrientation (zeroMultisection (halfSEP 1 1))
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap)) := by
  obtain ⟨-, -, -, hX, hbump, hF, hft, hΛ, hsec, hinv, ho, hgp, hidx⟩ :=
    theorem_15_4_1_hypotheses_halfSEP
  exact theorem_15_4_1 hX hbump hF hft hΛ hsec _ hinv ho hgp hidx

/-! ### The canonically oriented regular perturbation -/

/-- **`Λ` is a regular perturbation of `f`** (Corollary 15.3.10): for an auxiliary norm `N` and
a saturated open `U` with `(N, U)` controlling compactness, `Λ` is structurable,
`dom-supp(Λ) = ∅ ⊆ U`, `N(Λ) ≡ 0 < 1` and `(f, Λ)` is transversal. -/
theorem exists_isRegularPerturbation_halfDisc :
    ∃ (N : (halfSEP 1 1).B.One → ℝ) (U : Set (halfSEP 1 1).Obj),
      IsRegularPerturbation (halfSEP 1 1) halfDiscSection N U
        (zeroMultisection (halfSEP 1 1)) := by
  obtain ⟨-, -, -, -, hpara, -, -, -, -, N, U, hcc, -⟩ := theorem_15_3_9_hypotheses_halfSEP
  have hN0 := pointwiseNorm_zeroMultisection (A := halfSEP 1 1) hcc.1.isAuxNorm
  exact ⟨N, U, hcc, isStructurable_zeroMultisection hpara,
    by rw [domSupp_zeroMultisection]; exact empty_subset _,
    fun x => by rw [hN0]; exact one_pos, isTransversal_halfDisc⟩

/-- **A canonically oriented regular perturbation with boundary** (Definition 15.4.2, Corollary
15.4.4): on the half-disc example there is an oriented regular perturbation `P` of `f` of
dimension `0 + 1` with `P.Λ = Λ`, obtained by `OrientedRegularPerturbation.canonical`, which
satisfies `IsCanonicalPerturbation` for the orientation `halfOrientation` of `f`, and whose
support meets `∂X`. -/
theorem exists_isCanonicalPerturbation_halfSEP :
    ∃ P : OrientedRegularPerturbation (halfSEP 1 1) halfDiscSection 0,
      P.Λ = zeroMultisection (halfSEP 1 1) ∧
      IsCanonicalPerturbation
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) P ∧
      ∃ x ∈ (halfSEP 1 1).X.PObj.boundary,
        x ∈ EpGroupoid.supp (fun z => (P.Λ (halfDiscSection z) : ℚ)) := by
  obtain ⟨-, -, hsupp, hX, hbump, hF, hft, -, hsec, hinv, ho, hgp, hidx⟩ :=
    theorem_15_4_1_hypotheses_halfSEP
  obtain ⟨N, U, hreg⟩ := exists_isRegularPerturbation_halfDisc
  have hgood : ∀ x ∈ (halfSEP 1 1).X.PObj.boundary,
      0 < zeroMultisection (halfSEP 1 1) (halfDiscSection x) →
      SBLocalization.IsGoodPositionAt halfDiscSection (zeroMultisection (halfSEP 1 1)) x :=
    fun x _ hpos => hgp x (by change (0 : ℚ) < _; exact_mod_cast hpos)
  exact ⟨OrientedRegularPerturbation.canonical (m := 0) hX hbump hF hft hsec _ hinv ho hreg
      hgood hidx, rfl,
    isCanonicalPerturbation_canonical (m := 0) hX hbump hF hft hsec _ hinv ho hreg hgood hidx,
    hsupp⟩

end HalfSpaceBundle

end Polyfold
