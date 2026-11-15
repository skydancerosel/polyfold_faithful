import Polyfold.Chapter15.BoundaryExtensionIndependence
import Polyfold.Chapter15.HalfSpaceBoundaryWeightWitness
import Polyfold.Chapter15.InteriorPerturbationWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3: **instances with
boundary and non-zero fibres** of all hypotheses of Theorem 15.3.9 (Transversal Extension
Theorem, p. 694) and of its relative step (steps (c)–(d) of the proof, pp. 698–699), and an
instance with non-zero fibres of Corollary 15.3.10 (1) (p. 699).

# The half-disc example

## The example

The base is the half-plane `H = [0, ∞) × ℝ` with the trivial ep-groupoid, the bundle is
`H × ℝ → H` (`HalfSpaceBundle.halfSEP 1 1`), and the section is the graph section
`f(a, y) = ((a, y), a² + y² − 1)` of `φ(a, y) = a² + y² − 1`.  Its solution set is the half
circle `{a² + y² = 1, a ≥ 0}`, compact, and it meets `∂H = {0} × ℝ` in the two points `(0, ±1)`.
At these points `Dφ(0, ±1)(0, η) = ±2η`, so `Dφ` is onto `ℝ` on the hyperplane `{0} × ℝ = T^R H`:
the pair `(f, Λ)`, with `Λ` the multisection of the zero section, is in general position at the
boundary points of `supp(Λ ∘ f)`, which is the boundary hypothesis of Theorem 15.3.9.  The
boundary datum is `Λ` over `∂H`; `dom-supp(Λ) = ∅`, `N(Λ) ≡ 0` and `h ≡ 1`.

For Corollary 15.3.10 (1) the text asks `∂X = ∅` (`d_X ≡ 0`); there the example is
`ℝ × ℝ → ℝ` (`epSEP 1 1`) with the graph section of `φ = id`, `S_f = {0}`.

## What is formalized

Namespace `Polyfold.HalfSpaceBundle`:
* `halfDiscMap`, `contDiff_halfDiscMap`, `hasFDerivAt_halfDiscMap`;
* `halfDiscMap_onto_hyperplane`: at the boundary zeros `Dφ` is onto on `{0} × ℝ`;
* `hasCompactSolutionSetEp_halfDisc`: `|S_f|` is compact;
* `isBoundaryFaceOnto_halfDisc`: the boundary hypothesis `IsBoundaryFaceOnto f Λ` (through
  `SBLocalization.isBoundaryFaceOnto_iff` with the extension `Λ` itself and
  `isInGeneralPositionAt_graphSection`);
* **`theorem_15_3_9_hypotheses_halfSEP`**: `∂X ≠ ∅`, every fibre non-zero, `supp(Λ ∘ f) ∩ ∂X`
  non-empty, and every hypothesis of `theorem_15_3_9_statement (halfSEP 1 1)` for `f`, an
  auxiliary norm `N`, a saturated open `U`, `Λ` and `h ≡ 1`;
  **`theorem_15_3_9_halfSEP`**: the conclusion of Theorem 15.3.9 there (`theorem_15_3_9`);
* **`theorem_15_3_7_relative_hypotheses_halfSEP`**, **`theorem_15_3_7_relative_halfSEP`**: the
  same for `theorem_15_3_7_relative_statement` with `Λ₀ = Λ`, whose boundary hypothesis is
  general position at the two boundary zeros;
* `not_isBoundaryFaceOnto_tangentDisc`: for `ψ(a, y) = (a − 1)² + y² − 1`, whose zero set
  touches `∂H` tangentially at `0`, the boundary hypothesis fails, so it is a restriction.

Namespace `Polyfold.TrivialBundle`:
* **`corollary_15_3_10_1_hypotheses_epSEP`**, **`corollary_15_3_10_1_epSEP`**: on `ℝ × ℝ → ℝ`,
  `f(x) = (x, x)`, every hypothesis of `corollary_15_3_10_1` holds, the fibres are non-zero and
  `S_f = {0}` is non-empty; hence a structurable regular perturbation in general position.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15

/-! ### The map `φ(a, y) = a² + y² − 1` -/

/-- `φ : ℝ ⊕ ℝ → ℝ`, `φ(a, y) = a² + y² − 1`. -/
def halfDiscMap (p : Pm 1) : Fin 1 → ℝ := fun _ => p.1 0 ^ 2 + p.2 0 ^ 2 - 1

theorem contDiff_halfDiscMap : ContDiff ℝ ∞ halfDiscMap := by
  unfold halfDiscMap
  fun_prop

/-- The coordinate `a` of `(a, y) ∈ ℝ ⊕ ℝ`. -/
def coordA : Pm 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
    (ContinuousLinearMap.fst ℝ _ _)

/-- The coordinate `y` of `(a, y) ∈ ℝ ⊕ ℝ`. -/
def coordY : Pm 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
    (ContinuousLinearMap.snd ℝ _ _)

/-- The derivative of `φ` at `x = (a, y)`: `(α, η) ↦ 2 a α + 2 y η`. -/
theorem hasFDerivAt_halfDiscMap (x : Pm 1) :
    HasFDerivAt halfDiscMap (ContinuousLinearMap.pi fun _ : Fin 1 =>
      (2 * x.1 0) • coordA + (2 * x.2 0) • coordY) x := by
  rw [hasFDerivAt_pi]
  intro i
  have h1 : HasFDerivAt (fun p : Pm 1 => p.1 0) coordA x := coordA.hasFDerivAt
  have h2 : HasFDerivAt (fun p : Pm 1 => p.2 0) coordY x := coordY.hasFDerivAt
  have h := ((h1.mul h1).add (h2.mul h2)).sub_const 1
  convert h using 1
  · funext p
    simp only [halfDiscMap, Pi.add_apply, Pi.mul_apply]
    ring
  · ext v <;> simp [coordA, coordY] <;> ring

/-- `φ(x) = 0` iff `a² + y² = 1`. -/
theorem halfDiscMap_eq_zero_iff (x : Pm 1) :
    halfDiscMap x = 0 ↔ x.1 0 ^ 2 + x.2 0 ^ 2 = 1 := by
  constructor
  · intro h
    have := congrFun h 0
    simp only [halfDiscMap, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [halfDiscMap, Pi.zero_apply]
    linarith

/-- **At a boundary zero, `Dφ` is onto on `{0} × ℝ`**: at `(0, y)` with `y² = 1`,
`Dφ(0, y)(0, η) = 2 y η`. -/
theorem halfDiscMap_onto_hyperplane {x : Pm 1} (h0 : halfDiscMap x = 0) (hb : x.1 0 = 0)
    (w : Fin 1 → ℝ) : ∃ v : Pm 1, v.1 0 = 0 ∧ fderiv ℝ halfDiscMap x v = w := by
  have hy : x.2 0 ^ 2 = 1 := by
    have := (halfDiscMap_eq_zero_iff x).1 h0
    rw [hb] at this
    linarith
  have hy0 : x.2 0 ≠ 0 := by
    intro h
    rw [h] at hy
    norm_num at hy
  refine ⟨(0, fun _ => w 0 / (2 * x.2 0)), rfl, ?_⟩
  rw [(hasFDerivAt_halfDiscMap x).fderiv]
  funext i
  rw [Subsingleton.elim i 0]
  simp [coordA, coordY]
  field_simp

/-! ### The graph section of `φ` on `H × ℝ → H` -/

/-- The section `f(a, y) = ((a, y), a² + y² − 1)` of `H × ℝ → H`. -/
abbrev halfDiscSection : (halfSEP 1 1).Obj → (halfSEP 1 1).W := graphSection halfDiscMap

/-- The zero set of `φ` in `ℝ ⊕ ℝ` (the unit circle) is compact. -/
theorem isCompact_halfDiscMap_zero : IsCompact (halfDiscMap ⁻¹' {0}) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_singleton.preimage contDiff_halfDiscMap.continuous) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Pm 1)) (r := 1)).subset fun p hp => ?_
  have h := (halfDiscMap_eq_zero_iff p).1 hp
  have ha : |p.1 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg (p.2 0)]
  have hy : |p.2 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg (p.1 0)]
  rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
  refine ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_,
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact ha
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact hy

/-- `S_f` is the half circle `{a² + y² = 1, a ≥ 0}`. -/
theorem solutionSet_halfDisc :
    solutionSet (halfSEP 1 1).P halfDiscSection =
      ((↑) : H 1 → (halfSpaceSc 1) 0) ⁻¹' (halfDiscMap ⁻¹' {0}) := by
  ext x
  exact isZeroAt_graphSection_iff (k := 1) (φ := halfDiscMap) (x := x)

/-- **`|S_f|` is compact** (Definition 12.4.1 (1)). -/
theorem hasCompactSolutionSetEp_halfDisc :
    (halfSEP 1 1).E.HasCompactSolutionSetEp halfDiscSection := by
  have hK : IsCompact (solutionSet (halfSEP 1 1).P halfDiscSection) := by
    rw [solutionSet_halfDisc]
    exact (quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_halfDiscMap_zero
  exact hK.image (halfSEP 1 1).X.continuous_π

/-- The boundary point `(0, 1)` of `H`. -/
def topPoint : H 1 := ⟨(0, fun _ => 1), fun _ => le_rfl⟩

theorem topPoint_mem_boundary :
    (show (halfSEP 1 1).Obj from topPoint) ∈ (halfSEP 1 1).X.PObj.boundary :=
  (mem_boundary_halfSEP_iff 1 1 topPoint).2 rfl

theorem halfDiscMap_topPoint : halfDiscMap (topPoint : Pm 1) = 0 :=
  (halfDiscMap_eq_zero_iff _).2 (by simp [topPoint]; rfl)

/-- **`supp(Λ ∘ f)` meets `∂H`**: `Λ(f(0, 1)) = 1`. -/
theorem zeroMultisection_halfDisc_topPoint :
    0 < zeroMultisection (halfSEP 1 1) (halfDiscSection topPoint) :=
  (zeroMultisection_graphSection_pos_iff (k := 1) (φ := halfDiscMap) topPoint).2
    halfDiscMap_topPoint

/-- **General position at the boundary points of the support**: at every `x ∈ ∂H` with
`Λ(f(x)) > 0`, every operator of `T(f, Λ)(x)` is onto on `T^R_xH` (Definition 15.3.5). -/
theorem isReducedOntoAtPt_halfDisc (x : (halfSEP 1 1).X.PObj.Level 1)
    (hxb : (halfSEP 1 1).X.PObj.levelVal 1 x ∈ (halfSEP 1 1).X.PObj.boundary)
    (hpos : 0 < zeroMultisection (halfSEP 1 1)
      (halfDiscSection ((halfSEP 1 1).X.PObj.levelVal 1 x))) :
    IsReducedOntoAtPt halfDiscSection (zeroMultisection (halfSEP 1 1)) x := by
  have h0 := (zeroMultisection_graphSection_pos_iff (k := 1) (φ := halfDiscMap) _).1 hpos
  have hb := (mem_boundary_halfSEP_iff 1 1 _).1 hxb
  obtain ⟨_, hred⟩ := isInGeneralPositionAt_graphSection contDiff_halfDiscMap h0 hb
    (halfDiscMap_onto_hyperplane h0 hb)
  exact hred

/-- **The boundary hypothesis of Theorem 15.3.9 holds** for `f` and `Λ`: for every sc⁺
extension of `Λ|∂H` (`isBoundaryFaceOnto_iff`, with the extension `Λ` itself). -/
theorem isBoundaryFaceOnto_halfDisc :
    IsBoundaryFaceOnto halfDiscSection (zeroMultisection (halfSEP 1 1)) :=
  (isBoundaryFaceOnto_iff (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _) fun _ _ => rfl).2
    fun x hxb _ hpos => isReducedOntoAtPt_halfDisc x hxb hpos

/-! ### Theorem 15.3.9 -/

/-- **All hypotheses of Theorem 15.3.9, with `∂X ≠ ∅` and non-zero fibres** (on `H × ℝ → H`,
`f(a, y) = ((a, y), a² + y² − 1)`, `Λ` the multisection of the zero section, `h ≡ 1`): the
boundary is non-empty, every fibre is a non-zero vector space, `supp(Λ ∘ f)` meets `∂X` (at
`(0, 1)`, so the boundary hypothesis is not empty), and for an auxiliary norm `N` and a
saturated open `U` every hypothesis of `theorem_15_3_9_statement (halfSEP 1 1)` holds. -/
theorem theorem_15_3_9_hypotheses_halfSEP :
    (halfSEP 1 1).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    (∃ x ∈ (halfSEP 1 1).X.PObj.boundary,
      0 < zeroMultisection (halfSEP 1 1) (halfDiscSection x)) ∧
    (halfSEP 1 1).X.IsTame ∧ (halfSEP 1 1).X.HasParacompactOrbitSpace ∧
    (halfSEP 1 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    (halfSEP 1 1).E.IsScFredholmSectionFunctor halfDiscSection ∧
    (halfSEP 1 1).B.IsScFredholmSectionTame halfDiscSection ∧
    (halfSEP 1 1).E.HasCompactSolutionSetEp halfDiscSection ∧
    ∃ (N : (halfSEP 1 1).B.One → ℝ) (U : Set (halfSEP 1 1).Obj),
      ControlsCompactness (halfSEP 1 1) halfDiscSection N U ∧
      IsBoundaryStructurable (halfSEP 1 1) (zeroMultisection (halfSEP 1 1)) ∧
      boundaryDomSupp (zeroMultisection (halfSEP 1 1)) ⊆ U ∧
      (∀ x ∈ (halfSEP 1 1).X.PObj.boundary,
        pointwiseNorm N (zeroMultisection (halfSEP 1 1)) x ≤ 1) ∧
      Continuous (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ∧
      (∀ φ : (halfSEP 1 1).Mor, (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ((halfSEP 1 1).X.src φ) =
        (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ((halfSEP 1 1).X.tgt φ)) ∧
      (∀ _ : (halfSEP 1 1).Obj, (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1) ∧
      (∀ x ∈ (halfSEP 1 1).X.PObj.boundary,
        pointwiseNorm N (zeroMultisection (halfSEP 1 1)) x < 1) ∧
      IsBoundaryFaceOnto halfDiscSection (zeroMultisection (halfSEP 1 1)) := by
  have hX := isTame_halfSEP 1 1
  have hpara := hasParacompactOrbitSpace_halfSEP 1 1
  have hf := isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap
  have hS := hasCompactSolutionSetEp_halfDisc
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (halfSEP 1 1).E hpara
  obtain ⟨U, hU⟩ := exists_controlsCompactness hf hS hN
  have hN0 := pointwiseNorm_zeroMultisection (A := halfSEP 1 1) hN.isAuxNorm
  refine ⟨⟨_, zero_mem_boundary_halfSEP 1 1⟩, nontrivial_fibre_halfSEP 1 1,
    ⟨_, topPoint_mem_boundary, zeroMultisection_halfDisc_topPoint⟩, hX, hpara,
    admitsScPartitionsOfUnity_halfSEP 1 1, hf,
    isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap, hS, N, U, hU,
    isBoundaryStructurable_zero hX hpara, by rw [boundaryDomSupp_zero]; exact empty_subset _,
    fun x _ => by rw [hN0]; exact zero_le_one, continuous_const, fun _ => rfl,
    fun _ => ⟨one_pos, le_rfl⟩, fun x _ => by rw [hN0]; exact one_pos,
    isBoundaryFaceOnto_halfDisc⟩

/-- **Theorem 15.3.9 on the half-plane example** (`theorem_15_3_9` applied to the instance of
`theorem_15_3_9_hypotheses_halfSEP`): there is a structurable `Λ'` on `H × ℝ → H`, equal to `Λ`
over `∂H`, with dom-supp in `U`, `N(Λ') < 1`, `(N, U)`-admissible and transversal, and
`Λ' ∘ f` is a compact branched ep⁺-subgroupoid. -/
theorem theorem_15_3_9_halfSEP :
    ∃ (N : (halfSEP 1 1).B.One → ℝ) (U : Set (halfSEP 1 1).Obj),
      ControlsCompactness (halfSEP 1 1) halfDiscSection N U ∧
      ∃ Λ' : (halfSEP 1 1).W → ℚ≥0, IsStructurable (halfSEP 1 1) Λ' ∧
        (∀ w, (halfSEP 1 1).P w ∈ (halfSEP 1 1).X.PObj.boundary →
          Λ' w = zeroMultisection (halfSEP 1 1) w) ∧
        domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < 1) ∧
        IsAdmissible (halfSEP 1 1) halfDiscSection N U Λ' ∧
        IsTransversal halfDiscSection Λ' ∧
        (halfSEP 1 1).X.IsBranchedEpSubgroupoid (fun z => (Λ' (halfDiscSection z) : ℚ)) ∧
        (halfSEP 1 1).X.IsCompactBranched (fun z => (Λ' (halfDiscSection z) : ℚ)) := by
  obtain ⟨-, -, -, hX, hpara, hPU, hf, hft, hS, N, U, hcc, hΛ, hdom, hN1, hc, hfun, hh, hNh,
    honto⟩ := theorem_15_3_9_hypotheses_halfSEP
  exact ⟨N, U, hcc, theorem_15_3_9 hX hpara hPU _ hf hft hS N U hcc _ hΛ hdom hN1 _ hc hfun hh
    hNh honto⟩

/-! ### Steps (c)–(d): the relative form of Theorem 15.3.7 -/

/-- **All hypotheses of the relative step of Theorem 15.3.9 (`theorem_15_3_7_relative_statement`),
with `∂X ≠ ∅` and non-zero fibres**, on the same example with `Λ₀ = Λ` and `h ≡ 1`: `Λ₀` is
structurable, its dom-supp (empty) lies in `U`, `N(Λ₀) ≡ 0 < 1`, and `(f, Λ₀)` is in general
position at the points of `supp(Λ₀ ∘ f) ∩ ∂X`, which is non-empty (it contains `(0, 1)`). -/
theorem theorem_15_3_7_relative_hypotheses_halfSEP :
    (halfSEP 1 1).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    (∃ x ∈ (halfSEP 1 1).X.PObj.boundary,
      0 < zeroMultisection (halfSEP 1 1) (halfDiscSection x)) ∧
    (halfSEP 1 1).X.IsTame ∧ (halfSEP 1 1).X.HasParacompactOrbitSpace ∧
    (halfSEP 1 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    (halfSEP 1 1).E.IsScFredholmSectionFunctor halfDiscSection ∧
    (halfSEP 1 1).B.IsScFredholmSectionTame halfDiscSection ∧
    (halfSEP 1 1).E.HasCompactSolutionSetEp halfDiscSection ∧
    ∃ (N : (halfSEP 1 1).B.One → ℝ) (U : Set (halfSEP 1 1).Obj),
      ControlsCompactness (halfSEP 1 1) halfDiscSection N U ∧
      Continuous (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ∧
      (∀ φ : (halfSEP 1 1).Mor, (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ((halfSEP 1 1).X.src φ) =
        (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ((halfSEP 1 1).X.tgt φ)) ∧
      (∀ _ : (halfSEP 1 1).Obj, (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1) ∧
      IsStructurable (halfSEP 1 1) (zeroMultisection (halfSEP 1 1)) ∧
      domSupp (zeroMultisection (halfSEP 1 1)) ⊆ U ∧
      (∀ x, pointwiseNorm N (zeroMultisection (halfSEP 1 1)) x < 1) ∧
      ∀ x : (halfSEP 1 1).X.PObj.Level 1,
        (halfSEP 1 1).X.PObj.levelVal 1 x ∈ (halfSEP 1 1).X.PObj.boundary →
        0 < zeroMultisection (halfSEP 1 1) (halfDiscSection ((halfSEP 1 1).X.PObj.levelVal 1 x)) →
        IsReducedOntoAtPt halfDiscSection (zeroMultisection (halfSEP 1 1)) x := by
  obtain ⟨hne, hfib, hsupp, hX, hpara, hPU, hf, hft, hS, N, U, hcc, -, -, -, hc, hfun, hh, -,
    -⟩ := theorem_15_3_9_hypotheses_halfSEP
  have hN0 := pointwiseNorm_zeroMultisection (A := halfSEP 1 1) hcc.1.isAuxNorm
  exact ⟨hne, hfib, hsupp, hX, hpara, hPU, hf, hft, hS, N, U, hcc, hc, hfun, hh,
    isStructurable_zeroMultisection hpara,
    by rw [domSupp_zeroMultisection]; exact empty_subset _, fun x => by rw [hN0]; exact one_pos,
    isReducedOntoAtPt_halfDisc⟩

/-- **The relative step of Theorem 15.3.9 on the half-plane example**
(`theorem_15_3_7_relative` applied to `theorem_15_3_7_relative_hypotheses_halfSEP`): there is a
structurable `Λ'` equal to `Λ₀` over `∂H`, with dom-supp in `U`, `N(Λ') < 1`, and `(f, Λ')`
transversal and in general position. -/
theorem theorem_15_3_7_relative_halfSEP :
    ∃ (N : (halfSEP 1 1).B.One → ℝ) (U : Set (halfSEP 1 1).Obj),
      ControlsCompactness (halfSEP 1 1) halfDiscSection N U ∧
      ∃ Λ' : (halfSEP 1 1).W → ℚ≥0, IsStructurable (halfSEP 1 1) Λ' ∧
        (∀ w, (halfSEP 1 1).P w ∈ (halfSEP 1 1).X.PObj.boundary →
          Λ' w = zeroMultisection (halfSEP 1 1) w) ∧
        domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < 1) ∧
        IsTransversal halfDiscSection Λ' ∧
        IsInGeneralPosition (halfSEP 1 1) halfDiscSection Λ' := by
  obtain ⟨-, -, -, hX, hpara, hPU, hf, hft, hS, N, U, hcc, hc, hfun, hh, hΛ, hdom, hN, hgp⟩ :=
    theorem_15_3_7_relative_hypotheses_halfSEP
  exact ⟨N, U, hcc, theorem_15_3_7_relative hX hpara hPU _ hf hft hS N U hcc _ hc hfun hh _ hΛ
    hdom hN hgp⟩

/-! ### The boundary hypothesis is a restriction -/

/-- `ψ(a, y) = (a − 1)² + y² − 1 = a² − 2a + y²`: its zero set, the circle of radius `1` about
`(1, 0)`, touches `∂H` at `0` only, tangentially. -/
def tangentDiscMap (p : Pm 1) : Fin 1 → ℝ := fun _ => p.1 0 ^ 2 - 2 * p.1 0 + p.2 0 ^ 2

theorem contDiff_tangentDiscMap : ContDiff ℝ ∞ tangentDiscMap := by
  unfold tangentDiscMap
  fun_prop

/-- The derivative of `ψ` at `x = (a, y)`: `(α, η) ↦ (2a − 2) α + 2 y η`. -/
theorem hasFDerivAt_tangentDiscMap (x : Pm 1) :
    HasFDerivAt tangentDiscMap (ContinuousLinearMap.pi fun _ : Fin 1 =>
      (2 * x.1 0 - 2) • coordA + (2 * x.2 0) • coordY) x := by
  rw [hasFDerivAt_pi]
  intro i
  have h1 : HasFDerivAt (fun p : Pm 1 => p.1 0) coordA x := coordA.hasFDerivAt
  have h2 : HasFDerivAt (fun p : Pm 1 => p.2 0) coordY x := coordY.hasFDerivAt
  have h := ((h1.mul h1).sub (h1.const_mul 2)).add (h2.mul h2)
  convert h using 1
  · funext p
    simp only [tangentDiscMap, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · ext v <;> simp [coordA, coordY] <;> ring

/-- **The boundary hypothesis of Theorem 15.3.9 fails for `ψ`**: at the tangency point `0 ∈ ∂H`
the operator of `T(f_ψ, Λ)(0)` is `Dψ(0)(α, η) = −2α`, which vanishes on `T^R_0H = {0} × ℝ`
and so is not onto the fibre `ℝ`.  Hence the boundary hypothesis is not automatic on
`H × ℝ → H`: `isBoundaryFaceOnto_halfDisc` uses that `φ⁻¹(0)` meets `∂H` transversally. -/
theorem not_isBoundaryFaceOnto_tangentDisc :
    ¬ IsBoundaryFaceOnto (A := halfSEP 1 1) (graphSection tangentDiscMap)
      (zeroMultisection (halfSEP 1 1)) := by
  classical
  intro hBF
  have hψ := contDiff_tangentDiscMap
  have hf := isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) hψ
  have hft := isScFredholmSectionTame_graphSection_halfSEP (k := 1) hψ
  have hΛ := isScPlusMultisection_zeroMultisection (halfSEP 1 1)
  set x₀ : H 1 := ⟨0, fun _ => le_rfl⟩ with hx₀
  have h0 : tangentDiscMap (x₀ : Pm 1) = 0 := by
    funext i
    simp [tangentDiscMap, hx₀]
  have hx1 : (show (halfSEP 1 1).Obj from x₀) ∈ (halfSEP 1 1).X.PObj.levelSet 1 := by
    change x₀ ∈ (basePoly 1).levelSet 1
    rw [levelSet_eq_univ]; exact mem_univ _
  set x := (halfSEP 1 1).X.PObj.levelMk 1 x₀ hx1 with hxdef
  have hxv : (halfSEP 1 1).X.PObj.levelVal 1 x = x₀ := (halfSEP 1 1).X.PObj.levelVal_levelMk _ _ _
  have hpos : 0 < zeroMultisection (halfSEP 1 1)
      (graphSection tangentDiscMap ((halfSEP 1 1).X.PObj.levelVal 1 x)) := by
    rw [hxv]; exact (zeroMultisection_graphSection_pos_iff (k := 1) x₀).2 h0
  have hxb : (halfSEP 1 1).X.PObj.levelVal 1 x ∈ (halfSEP 1 1).X.PObj.boundary := by
    rw [hxv]; exact zero_mem_boundary_halfSEP 1 1
  have hred := hBF _ hΛ (fun _ _ => rfl) x hxb (mem_smoothSet_of_pos hft hΛ hpos) hpos
  set c : StrongBundleChart (halfSEP 1 1).X.PObj (halfSEP 1 1).P := chartAt (k := 1) x₀ with hcdef
  have hc : (halfSEP 1 1).B.IsChart c := isChart_chartAt x₀
  have hx : (halfSEP 1 1).X.PObj.levelVal 1 x ∈ c.φ.source := by
    rw [hxv]; exact mem_source_chartAt x₀
  have hφ0 : c.φ ((halfSEP 1 1).X.PObj.levelVal 1 x) = 0 := by
    rw [hxv]; exact chartAt_self x₀
  have hx0 : graphSection tangentDiscMap ((halfSEP 1 1).X.PObj.levelVal 1 x) =
      fiberZero (halfSEP 1 1).P ((halfSEP 1 1).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (k := 1) (φ := tangentDiscMap) (x := x₀)).2 h0
  have hb : (x₀ : Pm 1).1 0 = 0 := rfl
  have hT : c.φ.model.C = (ScIso.refl (halfSpaceSc 1)) 0 ⁻¹' quadrant 1 (rnSc 1) 0 :=
    (C_chartAt x₀).trans (by rw [if_pos hb]; ext; rfl)
  have hsurj := hred _ ((mem_support_linearization_zero_iff hf hc hx hx0 _).2 rfl) c.φ
    c.isChart hx 1 (rnSc 1) (ScIso.refl _) hT
  have key := (onto_chart_iff (A := halfSEP 1 1) (ℓ := 0) (s := fun j => j.elim0) (hft := hft)
    (hsec := fun j => j.elim0) (hc := hc) (hx := hx) (hφ0 := hφ0) (hx0 := hx0)
    (T := ScIso.refl (halfSpaceSc 1))).1 fun w => by
      obtain ⟨⟨v, hv⟩, he⟩ := hsurj w
      refine ⟨v, hv, fun j => j.elim0, ?_⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact he
  have hnt := nontrivial_fibre_halfSEP 1 1 ((halfSEP 1 1).X.PObj.levelVal 1 x)
  obtain ⟨w, hw⟩ := exists_ne (0 : (halfSEP 1 1).P ⁻¹' {(halfSEP 1 1).X.PObj.levelVal 1 x})
  have hk : ((0 : c.φ.model.E 0), c.fiberLin hx w) ∈ c.K := by
    rw [← hφ0, ← c.apply_fiberLin hx w, ← c.image_source]
    exact ⟨_, c.fiberLin_src hx w, rfl⟩
  obtain ⟨u, hu, τ, he⟩ := key _ hk
  rw [linAt_apply, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he
  change scDeriv (chartAt (k := 1) x₀).U ((chartAt (k := 1) x₀).principal
    (graphSection tangentDiscMap) ∘ r (chartAt (k := 1) x₀).R) 0 u = _ at he
  rw [scDeriv_principal_comp_r_chartAt hψ x₀, (hasFDerivAt_tangentDiscMap _).fderiv] at he
  have hu0 : coordA (show Pm 1 from (u : c.φ.model.E 0)) = 0 :=
    (mem_minimalSubspaceWith (ScIso.refl (halfSpaceSc 1))).1 hu 0 rfl
  have hY : (x₀ : Pm 1).2 0 = 0 := rfl
  have hz : c.fiberLin hx w = c.fiberLin hx 0 := by
    rw [← he, map_zero]
    funext i
    change (2 * (x₀ : Pm 1).1 0 - 2) * coordA (show Pm 1 from (u : c.φ.model.E 0)) +
      (2 * (x₀ : Pm 1).2 0) * coordY (show Pm 1 from (u : c.φ.model.E 0)) = 0
    rw [hu0, hY]
    ring
  exact hw (c.fiberLin_injective hx hz)

end HalfSpaceBundle

namespace TrivialBundle

open SBLocalization StrongBundle MPolyfold EpGroupoid StrongBundleEquivalenceExamples

/-! ### Corollary 15.3.10 (1) with non-zero fibres -/

/-- The section `f(x) = (x, x)` of `ℝ × ℝ → ℝ` (the graph of the identity). -/
abbrev diagSection : (epSEP 1 1).Obj → (epSEP 1 1).W := graphSection (id : (Fin 1 → ℝ) → _)

/-- `S_f = {0}`. -/
theorem solutionSet_diagSection :
    solutionSet (epSEP 1 1).P diagSection = {show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)} := by
  ext x
  exact isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := id) (x := x)

/-- **All hypotheses of Corollary 15.3.10 (1), with non-zero fibres and `S_f ≠ ∅`**: on
`ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ` (`d_X ≡ 0`, as the corollary asks), with
`f(x) = (x, x)`: `|X|` paracompact, sc-smooth bump functions, `f` sc-Fredholm with tame germ
data, `|S_f| = {0}` compact, and `(N, U)` controlling compactness for an auxiliary norm `N`. -/
theorem corollary_15_3_10_1_hypotheses_epSEP :
    (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
    (solutionSet (epSEP 1 1).P diagSection).Nonempty ∧
    (∀ x, (epSEP 1 1).X.PObj.degIndex x = 0) ∧ (epSEP 1 1).X.HasParacompactOrbitSpace ∧
    (epSEP 1 1).X.AdmitsBumpFunctionsPointwise ∧
    (epSEP 1 1).E.IsScFredholmSectionFunctor diagSection ∧
    (epSEP 1 1).B.IsScFredholmSectionTame diagSection ∧
    (epSEP 1 1).E.HasCompactSolutionSetEp diagSection ∧
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj),
      ControlsCompactness (epSEP 1 1) diagSection N U := by
  have hφ : ContDiff ℝ ∞ (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) := contDiff_id
  have hpara := (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn 1).2
  have hf : (epSEP 1 1).E.IsScFredholmSectionFunctor diagSection :=
    graphSection_mem_fredholmSectionFunctors_epBundle hφ
  have hS : (epSEP 1 1).E.HasCompactSolutionSetEp diagSection := by
    change IsCompact ((epSEP 1 1).X.π '' solutionSet (epSEP 1 1).P diagSection)
    rw [solutionSet_diagSection]
    exact isCompact_singleton.image (epSEP 1 1).X.continuous_π
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (epSEP 1 1).E hpara
  refine ⟨fun y => (fibEquiv (n := 1) (k := 1) y).nontrivial,
    ⟨_, by rw [solutionSet_diagSection]; exact mem_singleton _⟩, rnPolyfold_degIndex 1, hpara,
    (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn 1).1, hf,
    isScFredholmSectionTame_graphSection hφ, hS, N, exists_controlsCompactness hf hS hN⟩

/-- **Corollary 15.3.10 (1) on `ℝ × ℝ → ℝ`** (`corollary_15_3_10_1` applied to
`corollary_15_3_10_1_hypotheses_epSEP`): there is a structurable regular perturbation
`(N, U, Λ)` of `f(x) = (x, x)`, in general position, with `Λ ∘ f` a compact branched
ep⁺-subgroupoid. -/
theorem corollary_15_3_10_1_epSEP :
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj) (Λ : (epSEP 1 1).W → ℚ≥0),
      IsRegularPerturbation (epSEP 1 1) diagSection N U Λ ∧
      IsInGeneralPosition (epSEP 1 1) diagSection Λ ∧
      (epSEP 1 1).X.IsBranchedEpSubgroupoid (fun z => (Λ (diagSection z) : ℚ)) ∧
      (epSEP 1 1).X.IsCompactBranched (fun z => (Λ (diagSection z) : ℚ)) := by
  obtain ⟨-, -, hd, hpara, hbump, hf, hft, hS, N, U, hcc⟩ := corollary_15_3_10_1_hypotheses_epSEP
  obtain ⟨Λ, h⟩ := corollary_15_3_10_1 hd hpara hbump hf hft hS hcc
  exact ⟨N, U, Λ, h⟩

end TrivialBundle

end Polyfold
