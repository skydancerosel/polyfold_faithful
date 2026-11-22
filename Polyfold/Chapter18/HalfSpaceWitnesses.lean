import Polyfold.Chapter18.HalfSpaceBundleConstruction
import Polyfold.Chapter18.PerturbationModelIndependence
import Polyfold.Chapter18.ImplicitFunctionTheorem
import Polyfold.Chapter18.CompactnessExamples
import Polyfold.Chapter15.TransversalExtensionWitness
import Polyfold.Chapter4.NonVacuityHalfSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18:
**witnesses with non-empty boundary and non-trivial isotropy** for Theorem 18.6.1 (pp. 860–861),
Theorem 18.4.4 (p. 855), Theorem 15.3.9 in the polyfold context (§18.6) and Theorem 18.2.6
(p. 851), on the strong polyfold bundle construction `ℤ/2 ⋉ (H × ℝ) → ℤ/2 ⋉ H` of
`HalfSpaceBundleConstruction.lean`.  Numbers and pages are the 2021 text's.

# The half circle on `ℤ/2 ⋉ [0, ∞) × ℝ`

`C = ℤ/2 ⋉ H`, `H = [0, ∞) × ℝ`, `−1` acting by `(a, y) ↦ (a, −y)` on objects and trivially on
the fibres `μ(x) = ℝ`.  `∂C = {(0, y)}`; the corner `(0, 0) ∈ ∂C` and every `(a, 0)` have
isotropy `ℤ/2`.  The section functor `f(a, y) = ((a, y), a² + y² − 1)` (`halfF`, equivariant
since `φ(a, y) = a² + y² − 1` is even in `y`) has the half circle `{a² + y² = 1, a ≥ 0}` as
solution set (`halfF_zeroSet`), compact, meeting `∂C` in `(0, ±1)` and containing the point
`(1, 0)` with isotropy `ℤ/2`.

* **`theorem_18_6_1_witness_boundary`**, **`theorem_18_6_1_modelFree_witness_boundary`**: every
  hypothesis of `theorem_18_6_1` (in the covering model `halfSingle`) and of
  `theorem_18_6_1_modelFree` holds (tame, model bump functions
  `halfS_admitsModelBumpFunctions`, sc-Fredholm in both forms, compact `|S_f|`, an auxiliary norm
  `N` and `U` controlling compactness, `h = 1`), with `∂C ≠ ∅`, non-trivial isotropy on `∂C`
  and `S_f ∩ ∂C ≠ ∅`; hence their conclusions.
* `Λ₀ = halfV.zeroFunctor`, the multisection functor of the zero section: structurable over
  `∂C` (`isBoundaryStructurableFunctor_zeroFunctor`), positive on every `(α, 0)`, with
  `|dom-supp(Λ₀|∂C)| = ∅` and `N(Λ₀) = 0` (`pointwiseNormFunctor_zeroFunctor_eq_zero`).
* **`theorem_18_4_4_modelFree_witness_boundary`**: every hypothesis of
  `theorem_18_4_4_modelFree` for `Λ₀` over the non-empty `∂C`, `U = |C|`, `β = 1`; the theorem
  gives a structurable `Λ'` with `N(Λ') ≤ 1` and `Λ' = Λ₀` over `∂C`.
* `isBoundaryFaceOnto_model`, `isBoundaryFaceOntoFunctor_halfF`: the boundary hypothesis of
  Theorem 15.3.9 for `(f, Λ₀)`.  In the model `⊔_{Unit} (H × ℝ)` the inclusion of the piece is a
  local strong bundle isomorphism (`StrongBundle.sigmaMkLocalIso`), along which general position
  at a point is carried (`isReducedOntoAtLevel_localIso_iff`) to the half-disc example of
  Chapter 15 (`isReducedOntoAtPt_halfDisc`: at `(0, ±1)`, `Dφ(0, ±1)(0, η) = ±2η` is onto on
  `T^R H = {0} × ℝ`).
* **`theorem_15_3_9_categorical_witness_boundary`**: every hypothesis of
  `theorem_15_3_9_categorical` for `f`, `Λ₀` and `h = 1`, with `Λ₀ ∘ f > 0` at the boundary
  zero `(0, 1)`; hence a structurable transversal `Λ'` agreeing with `Λ₀` over `∂C`.
* **`theorem_18_2_6_witness_boundary`**: every hypothesis of `theorem_18_2_6` with
  `U_∂ = |{‖x‖ < 2}| ∩ |∂C|` (`halfUb`), a non-empty open subset of `|∂C|` containing
  `|S_f ∩ ∂C|`, a reflexive auxiliary norm and reflexive local compactness (`H` is locally
  compact); hence an open `U ⊇ |S_f|` with `U ∩ |∂C| = U_∂` and `(N, U)` controlling
  compactness.

## Readings

* The multisection functor over `∂C` is `Λ₀`, the functor of the zero section (Remark 18.1.6):
  it is non-zero on every boundary object and structurable over `∂C`; its domain support on
  `∂C` is empty, so the admissibility conditions `|dom-supp(Λ|∂C)| ⊆ U`, `N(Λ) ≤ 1` and
  `N(Λ) < h` on `∂C` hold with `N(Λ₀) = 0`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.HalfSpaceReflection

open GroupoidalCategory GroupoidalCategory.BanachFunctor HalfSpaceBundle StrongBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction
  PolyfoldConstruction SBLocalization

/-! ### The section functor `f(a, y) = ((a, y), a² + y² − 1)` -/

/-- `φ(a, y) = a² + y² − 1` is even in `y`. -/
theorem halfDiscMap_reflPm (g : ℤˣ) (p : Pm 1) : halfDiscMap (reflPm g p) = halfDiscMap p := by
  rcases Int.units_eq_one_or g with rfl | rfl
  · simp [reflPm]
  · funext i
    simp [halfDiscMap, reflPm]

/-- **The section functor `f(a, y) = ((a, y), a² + y² − 1)`** of `P : E → ℤ/2 ⋉ H`
(`ℤ/2`-equivariant: `φ` is even in `y` and `ℤ/2` acts trivially on the fibres). -/
def halfF : halfV.SectionFunctor where
  toFun x := halfMu.objMk x (halfDiscMap (x : Pm 1))
  base_toFun _ := rfl
  toFun_tgt φ := by
    obtain ⟨g, x⟩ := φ
    change halfMu.objMk (g • x) (halfDiscMap (reflPm g x)) = halfMu.objMk (g • x) (halfDiscMap x)
    rw [halfDiscMap_reflPm]

/-- The representative of `f` in `Ψ̄` is the graph section of `φ`. -/
theorem localRep_halfF : halfUnifData.localRep halfF = graphSection halfDiscMap := by
  funext q
  exact (halfUnifData.localRep_eq_iff halfF q _).2 rfl

/-- **Definition 18.1.1 holds for `f`** (`f_Ψ̄` is the graph section of `φ`, sc-Fredholm on the
half-space bundle by Chapter 4). -/
theorem isScFredholmSectionFunctor_halfF : halfQ.IsScFredholmSectionFunctor halfF := by
  intro α Ψ hΨ
  obtain rfl : Ψ = halfUnif := hΨ
  change halfUnifData.B.IsScFredholmSection (halfUnifData.localRep halfF)
  rw [localRep_halfF]
  exact (HalfSpaceBundle.isScFredholmSection_graphSection_wholeChart
    contDiff_halfDiscMap).isScFredholmSection

/-- The tame form of Definition 18.1.1 holds for `f`. -/
theorem isScFredholmSectionFunctorTame_halfF : halfQ.IsScFredholmSectionFunctorTame halfF := by
  intro α Ψ hΨ
  obtain rfl : Ψ = halfUnif := hΨ
  change halfUnifData.B.IsScFredholmSectionTame (halfUnifData.localRep halfF)
  rw [localRep_halfF]
  exact (HalfSpaceBundle.isScFredholmSectionTame_graphSection_wholeChart
    contDiff_halfDiscMap).isScFredholmSectionTame

/-- `F̄(x) ≠ ∅` for every `x`. -/
theorem halfQ_hasStrongBundleUniformizers : halfQ.HasStrongBundleUniformizers :=
  fun _ => ⟨halfUnif, rfl⟩

/-- **`S_f` is the half circle** `{a² + y² = 1, a ≥ 0}`. -/
theorem halfF_zeroSet : halfF.zeroSet = {x : H 1 | halfDiscMap (x : Pm 1) = 0} := by
  ext x
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · intro h
    change halfMu.objMk x (halfDiscMap (x : Pm 1)) = halfMu.objMk x 0
    rw [show halfDiscMap (x : Pm 1) = 0 from h]
    rfl

/-- **Definition 18.2.1 (1) for `f`**: `|S_f|` is compact. -/
theorem halfF_hasCompactModuliSpace : halfF.HasCompactModuliSpace := by
  unfold SectionFunctor.HasCompactModuliSpace
  rw [halfF_zeroSet]
  exact ((quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.isCompact_preimage
    isCompact_halfDiscMap_zero).image continuous_quot_mk

/-- **`S_f` meets `∂C`**: the boundary point `(0, 1)` is a zero of `f`. -/
theorem topPoint_mem_zeroSet_boundarySet : topPoint ∈ halfF.zeroSet ∩ halfS.boundarySet := by
  refine ⟨?_, (mem_boundarySet_iff topPoint).2 rfl⟩
  rw [halfF_zeroSet]
  exact halfDiscMap_topPoint

/-- **Definition 18.2.1 (3) for `f`**: `f` is proper`<∞` (Theorem 18.2.2). -/
theorem halfF_isProperLtInfty : halfQ.IsProperLtInfty halfF :=
  ((halfQ.theorem_18_2_2 halfF halfQ_hasStrongBundleUniformizers
    isScFredholmSectionFunctor_halfF).out 0 2).1 halfF_hasCompactModuliSpace

/-- **Definition 18.2.3 for `f`**: an auxiliary norm exists, and for each one an open
`U ⊇ |S_f|` such that `(N, U)` strongly controls compactness. -/
theorem halfF_stronglyControlsCompactness :
    (∃ N : halfV.EObj → ℝ≥0∞, halfQ.IsAuxNormFunctor N) ∧
      ∀ N : halfV.EObj → ℝ≥0∞, halfQ.IsAuxNormFunctor N →
        ∃ U, halfF.StronglyControlsCompactness N U := by
  refine ⟨halfQ.exists_isAuxNormFunctor halfQ_hasStrongBundleUniformizers, fun N hN => ?_⟩
  obtain ⟨U, hUo, hSU, hC⟩ := halfF_isProperLtInfty.2 N hN
  exact ⟨U, hUo, hSU, hC⟩

/-! ### Partitions of unity and bump functions in the model -/

/-- **The model `⊔_{Unit} H` admits sc-smooth partitions of unity** (Theorem 5.5.10: its chart
has the finite-dimensional model `ℝ ⊕ ℝ`, Proposition 5.5.11). -/
theorem halfModel_admitsScPartitionsOfUnity :
    (halfQ.modelSEP halfSingle.Ψ).X.PObj.AdmitsScPartitionsOfUnity := by
  refine theorem_5_5_10.2 ⟨{MPolyfold.sigmaChart () (baseChart 1)}, ?_, ?_, ?_⟩
  · rintro _ rfl
    exact (MPolyfold.isChart_sigmaChart_iff (P := fun _ : Unit => basePoly 1)).2
      ((basePoly 1).isChart_of_mem (mem_singleton _))
  · rintro ⟨⟨⟩, q⟩
    exact ⟨_, rfl, q, mem_univ q, rfl⟩
  · rintro _ rfl
    change (baseChart 1).model.HasApproxProperty
    have : FiniteDimensional ℝ ((baseChart 1).model.E 0) := by
      change FiniteDimensional ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ))
      infer_instance
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional _)

theorem halfQ_hasModelMPolyfoldPartitionsOfUnity : halfQ.HasModelMPolyfoldPartitionsOfUnity :=
  ⟨halfSingle, halfModel_admitsScPartitionsOfUnity⟩

/-- **Definition 18.4.1 holds for `ℤ/2 ⋉ H` (bump functions)**. -/
theorem halfS_admitsModelBumpFunctions : halfS.AdmitsModelBumpFunctions :=
  ⟨halfQ.baseCoveringFamily halfSingle,
    EpGroupoid.theorem_12_3_2_1.2 halfModel_admitsScPartitionsOfUnity.admitsBumpFunctions⟩

/-- The constant functor `h = 1` is a continuous functor `C → (0, 1]`. -/
theorem halfS_isContinuousFunctionFunctor_one :
    halfS.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) :=
  ⟨fun _ => rfl, fun _ => continuous_const⟩

/-! ### Theorem 18.6.1 -/

/-- **The hypotheses and conclusions of Theorem 18.6.1 for `f(a, y) = ((a, y), a² + y² − 1)` on
`ℤ/2 ⋉ H`**, in the covering model `halfSingle`, with `h = 1`.  Not degenerate: `∂C ≠ ∅`, the
corner `(0, 0) ∈ ∂C` has the non-trivial automorphism `(−1, (0, 0))`, and `S_f` (the half circle)
meets `∂C` at `(0, 1)`, so the general position (4) to `∂C` is a condition at boundary points. -/
theorem theorem_18_6_1_witness_boundary :
    halfS.IsTame ∧ halfS.AdmitsModelBumpFunctions ∧
      halfQ.IsScFredholmSectionFunctor halfF ∧ halfQ.IsScFredholmSectionFunctorTame halfF ∧
      halfF.HasCompactModuliSpace ∧
      halfS.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) ∧
      corner ∈ halfS.boundarySet ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      topPoint ∈ halfF.zeroSet ∩ halfS.boundarySet ∧
      ∃ (N : halfV.EObj → ℝ≥0∞) (U : Set halfC.toGroupoidStr.OrbitSpace),
        halfQ.IsAuxNormFunctor N ∧ halfF.ControlsCompactness N U ∧
        ∃ Λ : halfV.EObj → ℚ≥0, halfQ.IsStructurableFunctor Λ ∧
          (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal 1) ∧ orbitDomSupp Λ ⊆ U ∧
          halfQ.IsTransversalIn halfSingle.Ψ halfF Λ ∧
          halfQ.IsInGeneralPositionIn halfSingle.Ψ halfF Λ ∧
          halfS.IsBranchedSubcategory (fun α => (Λ (halfF.toFun α) : ℚ)) ∧
          halfC.IsCompactBranched (fun α => (Λ (halfF.toFun α) : ℚ)) ∧
          halfS.IsTameModel (fun α => (Λ (halfF.toFun α) : ℚ)) := by
  obtain ⟨⟨N, hN⟩, hU⟩ := halfF_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  exact ⟨halfS_isTame, halfS_admitsModelBumpFunctions, isScFredholmSectionFunctor_halfF,
    isScFredholmSectionFunctorTame_halfF, halfF_hasCompactModuliSpace,
    halfS_isContinuousFunctionFunctor_one, corner_mem_boundarySet, exists_ne_unit_corner,
    topPoint_mem_zeroSet_boundarySet, N, U, hN, hU.controlsCompactness,
    theorem_18_6_1 halfSingle halfS_isTame halfS_admitsModelBumpFunctions
      isScFredholmSectionFunctor_halfF isScFredholmSectionFunctorTame_halfF
      halfF_hasCompactModuliSpace hN hU.controlsCompactness halfS_isContinuousFunctionFunctor_one
      (fun _ => ⟨one_pos, le_rfl⟩)⟩

/-- **The model-free Theorem 18.6.1 for `f` on `ℤ/2 ⋉ H`**, with `h = 1`: its hypotheses hold
(with `∂C ≠ ∅` and `S_f ∩ ∂C ≠ ∅`), and the perturbation `Λ` it gives has (3) and (4) in every
covering model. -/
theorem theorem_18_6_1_modelFree_witness_boundary :
    halfQ.HasStrongBundleUniformizers ∧
      topPoint ∈ halfF.zeroSet ∩ halfS.boundarySet ∧
      ∃ (N : halfV.EObj → ℝ≥0∞) (U : Set halfC.toGroupoidStr.OrbitSpace),
        halfQ.IsAuxNormFunctor N ∧ halfF.ControlsCompactness N U ∧
        ∃ Λ : halfV.EObj → ℚ≥0, halfQ.IsStructurableFunctor Λ ∧
          (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal 1) ∧ orbitDomSupp Λ ⊆ U ∧
          (∀ c : halfQ.BundleCoveringFamily, halfQ.IsTransversalIn c.Ψ halfF Λ ∧
            halfQ.IsInGeneralPositionIn c.Ψ halfF Λ) ∧
          halfS.IsBranchedSubcategory (fun α => (Λ (halfF.toFun α) : ℚ)) ∧
          halfC.IsCompactBranched (fun α => (Λ (halfF.toFun α) : ℚ)) ∧
          halfS.IsTameModel (fun α => (Λ (halfF.toFun α) : ℚ)) := by
  obtain ⟨⟨N, hN⟩, hU⟩ := halfF_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  have hf := isScFredholmSectionFunctor_halfF
  obtain ⟨Λ, hΛ, h1, h2, h3, h4, h5⟩ := theorem_18_6_1_modelFree
    halfQ_hasStrongBundleUniformizers halfS_isTame halfS_admitsModelBumpFunctions hf
    isScFredholmSectionFunctorTame_halfF halfF_hasCompactModuliSpace hN hU.controlsCompactness
    halfS_isContinuousFunctionFunctor_one (fun _ => ⟨one_pos, le_rfl⟩)
  have hms := hΛ.isScPlusMultisectionFunctor
  exact ⟨halfQ_hasStrongBundleUniformizers, topPoint_mem_zeroSet_boundarySet, N, U, hN,
    hU.controlsCompactness, Λ, hΛ, h1, h2, fun c =>
    ⟨(isTransversalFunctor_iff_forall hf hms).1 h3 c,
      (isInGeneralPositionFunctor_iff_forall hf hms).1 h4 c⟩, h5⟩

/-! ### The multisection functor `Λ₀` of the zero section -/

theorem objMk_eq_objMk_zero_iff (α : H 1) (v : Fin 1 → ℝ) :
    halfV.objMk α v = halfV.objMk α 0 ↔ v = 0 :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by rw [h]; rfl⟩

/-- `Λ₀(α, v) > 0` iff `v = 0`. -/
theorem zeroFunctor_pos_iff (α : H 1) (v : Fin 1 → ℝ) :
    0 < halfV.zeroFunctor (halfV.objMk α v) ↔ v = 0 := by
  classical
  unfold zeroFunctor
  rw [← objMk_eq_objMk_zero_iff α v]
  change 0 < (if halfV.objMk α v = halfV.objMk α 0 then 1 else 0 : ℚ≥0) ↔ _
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_pos⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl 0), fun h' => absurd h' h⟩

/-- **`Λ₀` charges every boundary object**: `Λ₀(α, 0) = 1 > 0`, in particular over the corner
`(0, 0) ∈ ∂C`. -/
theorem zeroFunctor_objMk_zero_pos (α : H 1) : 0 < halfV.zeroFunctor (halfV.objMk α 0) :=
  (zeroFunctor_pos_iff α 0).2 rfl

/-- `|dom-supp(Λ₀|∂C)| = ∅`: `Λ₀` charges no non-zero vector. -/
theorem orbitBoundaryDomSupp_zeroFunctor : orbitBoundaryDomSupp halfS halfV.zeroFunctor = ∅ := by
  unfold orbitBoundaryDomSupp
  have : {α : H 1 | α ∈ halfS.boundarySet ∧ ∃ v : halfV.V α, v ≠ 0 ∧
      0 < halfV.zeroFunctor (halfV.objMk α v)} = ∅ :=
    eq_empty_of_forall_notMem fun α ⟨_, v, hv, hpos⟩ => hv ((zeroFunctor_pos_iff α v).1 hpos)
  rw [this, image_empty, closure_empty]

/-- `N(Λ₀)(α) = N(α, 0)`. -/
theorem pointwiseNormFunctor_zeroFunctor (N : halfV.EObj → ℝ≥0∞) (α : H 1) :
    pointwiseNormFunctor N halfV.zeroFunctor α = N (halfV.objMk α 0) := by
  unfold pointwiseNormFunctor
  have : {v : halfV.V α | 0 < halfV.zeroFunctor (halfV.objMk α v)} = {0} := by
    ext v
    exact zeroFunctor_pos_iff α v
  rw [this, image_singleton, sSup_singleton]

/-- Every point of the half-space bundle lies in `W_{0,1}`. -/
theorem mem_oneSet_bundle (y : K) : y ∈ (bundle 1 1).oneSet := by
  rintro c hc -
  rw [mem_singleton_iff.1 hc]
  exact (bijective_toBase_const _ 1).2 _

/-- **`N(Λ₀) = 0`** for an auxiliary norm `N`: `N(α, 0) = 0`. -/
theorem pointwiseNormFunctor_zeroFunctor_eq_zero {N : halfV.EObj → ℝ≥0∞}
    (hN : halfQ.IsAuxNormFunctor N) (α : H 1) :
    pointwiseNormFunctor N halfV.zeroFunctor α = 0 := by
  have hNc := hN halfSingle
  have hw : (⟨(), (α, 0)⟩ : halfQ.ModelW halfSingle.Ψ) ∈ (halfQ.modelSEP halfSingle.Ψ).B.oneSet :=
    (mem_oneSet_sigma_iff (B := fun _ : Unit => bundle 1 1) (i := ()) (α, 0)).2
      (mem_oneSet_bundle _)
  have hne : pointwiseNormFunctor N halfV.zeroFunctor α ≠ ⊤ := by
    rw [pointwiseNormFunctor_zeroFunctor]
    exact hNc.ne_top _ hw
  have h := halfQ.pointwiseNorm_bundlePull_of_ne_top hNc halfV.zeroFunctor ⟨(), α⟩ hne
  rw [halfQ.bundlePull_zeroFunctor] at h
  have h' : (pointwiseNormFunctor N halfV.zeroFunctor α).toReal = 0 :=
    h.trans (pointwiseNorm_zeroMultisection (A := halfQ.modelSEP halfSingle.Ψ)
      hNc.isAuxNorm.isAuxNorm ⟨(), α⟩)
  exact ((ENNReal.toReal_eq_zero_iff _).1 h').resolve_right hne

/-- **`Λ₀` is structurable over `∂C`** (Definition 14.1.7 in the model, by
`isBoundaryStructurable_zero`; its pull-back to the model is the trivial multisection). -/
theorem isBoundaryStructurableFunctor_zeroFunctor :
    halfQ.IsBoundaryStructurableFunctor halfV.zeroFunctor := by
  refine ⟨isMorInvariant_zeroFunctor, halfSingle, ?_⟩
  change IsBoundaryStructurable (halfQ.modelSEP halfSingle.Ψ)
    (halfQ.bundlePull halfSingle.Ψ halfV.zeroFunctor)
  rw [halfQ.bundlePull_zeroFunctor]
  exact isBoundaryStructurable_zero
    (halfS.isTame_modelEpGroupoid (Ψ := halfQ.modelBase halfSingle.Ψ) halfS_isTame)
    (halfQ.hasParacompactOrbitSpace_model halfSingle)

/-! ### Theorem 18.4.4 -/

/-- **The model-free Theorem 18.4.4 on `ℤ/2 ⋉ H` with `∂C ≠ ∅`**: for an auxiliary norm `N`,
the multisection functor `Λ₀` of the zero section over `∂C` (structurable over `∂C`, charging
every boundary object, the corner with isotropy `ℤ/2` among them), `U = |C|` and `β = 1`, every
hypothesis holds, and the theorem gives a structurable `Λ'` with `N(Λ') ≤ 1` which agrees with
`Λ₀` over `∂C`. -/
theorem theorem_18_4_4_modelFree_witness_boundary :
    halfQ.HasModelMPolyfoldPartitionsOfUnity ∧
      corner ∈ halfS.boundarySet ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      ∃ N : halfV.EObj → ℝ≥0∞, halfQ.IsAuxNormFunctor N ∧
        halfQ.IsBoundaryStructurableFunctor halfV.zeroFunctor ∧
        (∀ α ∈ halfS.boundarySet, 0 < halfV.zeroFunctor (halfV.objMk α 0)) ∧
        halfS.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) ∧
        ∃ Λ' : halfV.EObj → ℚ≥0, halfQ.IsStructurableFunctor Λ' ∧
          (∀ α, pointwiseNormFunctor N Λ' α ≤ ENNReal.ofReal 1) ∧ orbitDomSupp Λ' ⊆ univ ∧
          ∀ e : halfV.EObj, halfV.base e ∈ halfS.boundarySet → Λ' e = halfV.zeroFunctor e := by
  obtain ⟨N, hN⟩ := halfQ.exists_isAuxNormFunctor halfQ_hasStrongBundleUniformizers
  refine ⟨halfQ_hasModelMPolyfoldPartitionsOfUnity, corner_mem_boundarySet, exists_ne_unit_corner,
    N, hN, isBoundaryStructurableFunctor_zeroFunctor, fun α _ => zeroFunctor_objMk_zero_pos α,
    halfS_isContinuousFunctionFunctor_one, ?_⟩
  refine theorem_18_4_4_modelFree halfS_isTame halfQ_hasModelMPolyfoldPartitionsOfUnity hN
    isBoundaryStructurableFunctor_zeroFunctor isOpen_univ (subset_univ _)
    halfS_isContinuousFunctionFunctor_one (fun _ => zero_le_one) (subset_univ _) ?_
  intro α hα
  rw [orbitBoundaryDomSupp_zeroFunctor] at hα
  exact hα.elim

/-! ### The boundary hypothesis of Theorem 15.3.9 in the model -/

/-- `y = 0_{p(y)}` in `H × ℝ → H` iff `y₂ = 0`. -/
theorem eq_fiberZero_iff (y : K) : y = fiberZero (proj 1 1) (proj 1 1 y) ↔ y.2 = 0 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Prod.ext ((0 : proj 1 1 ⁻¹' {proj 1 1 y}).2).symm (h.trans rfl)

/-- In the model `⊔_{Unit} (H × ℝ)`, the trivial multisection is that of `H × ℝ → H`. -/
theorem zeroMultisection_model_mk (y : K) :
    zeroMultisection (halfQ.modelSEP halfSingle.Ψ) ⟨(), y⟩ = zeroMultisection (halfSEP 1 1) y := by
  classical
  rw [← halfQ.bundlePull_zeroFunctor]
  change halfV.zeroFunctor (halfV.objMk y.1 y.2) = _
  unfold zeroMultisection zeroFunctor
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((eq_fiberZero_iff y).2 ((objMk_eq_objMk_zero_iff y.1 y.2).1 h1)) h2
  · exact absurd ((objMk_eq_objMk_zero_iff y.1 y.2).2 ((eq_fiberZero_iff y).1 h2)) h1
  · rfl

/-- The section of the model is the family `{graphSection φ}`. -/
theorem modelSection_halfF :
    halfQ.modelSection halfSingle.Ψ halfF =
      sigmaSection (fun _ : Unit => graphSection halfDiscMap) := by
  funext x
  obtain ⟨i, q⟩ := x
  change (⟨i, halfUnifData.localRep halfF q⟩ : Σ _ : Unit, K) = ⟨i, graphSection halfDiscMap q⟩
  rw [localRep_halfF]

/-- **The boundary hypothesis of Theorem 15.3.9 in the model**: `(f^Ψ̄, Γ̄^*Λ₀)` satisfies
`IsBoundaryFaceOnto`.  At a boundary point of the support, `q = (0, ±1)`, the reduced
linearization in the model is carried by the local strong bundle isomorphism
`⊔_{Unit} (H × ℝ) ⊇ range(mk ()) ≅ H × ℝ` (`isReducedOntoAtLevel_localIso_iff`) to that of the
graph section of `φ` on `H × ℝ → H`, onto by `isReducedOntoAtPt_halfDisc` (Chapter 15). -/
theorem isBoundaryFaceOnto_model :
    IsBoundaryFaceOnto (A := halfQ.modelSEP halfSingle.Ψ) (halfQ.modelSection halfSingle.Ψ halfF)
      (halfQ.bundlePull halfSingle.Ψ halfV.zeroFunctor) := by
  classical
  set A := halfQ.modelSEP halfSingle.Ψ with hA
  have hf : A.E.IsScFredholmSectionFunctor (halfQ.modelSection halfSingle.Ψ halfF) :=
    (halfQ.remark_18_1_2_a_model halfF halfSingle).2 isScFredholmSectionFunctor_halfF
  have hft : A.B.IsScFredholmSectionTame (halfQ.modelSection halfSingle.Ψ halfF) :=
    (halfQ.remark_18_1_2_a_model_tame halfF halfSingle).2 isScFredholmSectionFunctorTame_halfF
  rw [halfQ.bundlePull_zeroFunctor]
  refine (isBoundaryFaceOnto_iff hf hft (isScPlusMultisection_zeroMultisection A)
    fun _ _ => rfl).2 ?_
  intro x hxb _ hpos
  rcases hyq : A.X.PObj.levelVal 1 x with ⟨u, q⟩
  cases u
  have hq1 : (show (halfSEP 1 1).Obj from q) ∈ (halfSEP 1 1).X.PObj.levelSet 1 := by
    change q ∈ (basePoly 1).levelSet 1
    rw [levelSet_eq_univ]; exact mem_univ _
  set x' := (halfSEP 1 1).X.PObj.levelMk 1 q hq1 with hx'
  have hx'v : (halfSEP 1 1).X.PObj.levelVal 1 x' = q :=
    (halfSEP 1 1).X.PObj.levelVal_levelMk _ _ _
  set L := (sigmaMkLocalIso (fun _ : Unit => bundle 1 1) () q).symm with hL
  have hfL : EqOn (halfQ.modelSection halfSingle.Ψ halfF) (L.Ψ ∘ graphSection halfDiscMap ∘ L.ϕ)
      (range (Sigma.mk ())) := by
    rw [modelSection_halfF]
    exact eqOn_sigmaSection (fun _ : Unit => bundle 1 1) (fun _ => graphSection halfDiscMap) () q
  have hΛL : ∀ w : A.W, A.P w ∈ range (Sigma.mk ()) →
      zeroMultisection A w = zeroMultisection (halfSEP 1 1) (L.Φ w) := by
    rintro ⟨⟨⟩, y⟩ -
    exact (zeroMultisection_model_mk y).trans (congrArg (zeroMultisection (halfSEP 1 1))
      (sigmaMkLocalIso_Ψ_mk (fun _ : Unit => bundle 1 1) () q y).symm)
  have hxU : A.X.PObj.levelVal 1 x ∈ range (Sigma.mk ()) := ⟨q, hyq.symm⟩
  have hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = (halfSEP 1 1).X.PObj.levelVal 1 x' := by
    rw [hyq, hx'v]
    exact sigmaMkLocalIso_g_mk (fun _ : Unit => bundle 1 1) () q q
  have key := isReducedOntoAtLevel_localIso_iff (A := A) (A' := halfSEP 1 1) L hf
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _) hfL hΛL hxU hϕ
  have hqb : ((show H 1 from q) : Pm 1).1 0 = 0 := by
    have h := (halfQ.mem_boundary_model_iff_obj halfSingle (A.X.PObj.levelVal 1 x)).1 hxb
    rw [hyq] at h
    exact (mem_boundarySet_iff q).1 h
  have hxb' : (halfSEP 1 1).X.PObj.levelVal 1 x' ∈ (halfSEP 1 1).X.PObj.boundary := by
    rw [hx'v]; exact (mem_boundary_halfSEP_iff 1 1 q).2 hqb
  have hpos' : 0 < zeroMultisection (halfSEP 1 1)
      (halfDiscSection ((halfSEP 1 1).X.PObj.levelVal 1 x')) := by
    rw [hx'v]
    rw [hyq, modelSection_halfF] at hpos
    exact (zeroMultisection_model_mk _).symm.trans_gt hpos
  exact key.2 (isReducedOntoAtPt_halfDisc x' hxb' hpos')

/-- **The boundary hypothesis of Theorem 15.3.9 holds model-free** for `f` and `Λ₀`. -/
theorem isBoundaryFaceOntoFunctor_halfF : halfQ.IsBoundaryFaceOntoFunctor halfF halfV.zeroFunctor :=
  ⟨halfSingle, isBoundaryFaceOnto_model⟩

/-- `supp(Λ₀ ∘ f)` meets `∂C`: `Λ₀(f(0, 1)) = 1`, so the boundary hypothesis is a condition at
the two boundary zeros `(0, ±1)`. -/
theorem zeroFunctor_halfF_topPoint_pos : 0 < halfV.zeroFunctor (halfF.toFun topPoint) :=
  (zeroFunctor_pos_iff topPoint _).2 halfDiscMap_topPoint

/-! ### Theorem 15.3.9 in the polyfold context -/

/-- **Theorem 15.3.9 in the polyfold context on `ℤ/2 ⋉ H` with `∂C ≠ ∅`**, for
`f(a, y) = ((a, y), a² + y² − 1)`, the multisection functor `Λ₀` of the zero section over `∂C`
and `h = 1`: every hypothesis holds (the boundary hypothesis `IsBoundaryFaceOntoFunctor` at the
boundary zeros `(0, ±1)` of `f`, where `Λ₀ ∘ f > 0`), and the theorem gives a structurable,
transversal `Λ'` agreeing with `Λ₀` over `∂C`, with `Λ' ∘ f` a compact branched
ep⁺-subcategory. -/
theorem theorem_15_3_9_categorical_witness_boundary :
    corner ∈ halfS.boundarySet ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      topPoint ∈ halfF.zeroSet ∩ halfS.boundarySet ∧
      0 < halfV.zeroFunctor (halfF.toFun topPoint) ∧
      ∃ (N : halfV.EObj → ℝ≥0∞) (U : Set halfC.toGroupoidStr.OrbitSpace),
        halfQ.IsAuxNormFunctor N ∧ halfF.ControlsCompactness N U ∧
        halfQ.IsBoundaryStructurableFunctor halfV.zeroFunctor ∧
        halfQ.IsBoundaryFaceOntoFunctor halfF halfV.zeroFunctor ∧
        ∃ Λ' : halfV.EObj → ℚ≥0, halfQ.IsStructurableFunctor Λ' ∧
          (∀ e : halfV.EObj, halfV.base e ∈ halfS.boundarySet → Λ' e = halfV.zeroFunctor e) ∧
          orbitDomSupp Λ' ⊆ U ∧
          (∀ α, pointwiseNormFunctor N Λ' α < ENNReal.ofReal 1) ∧
          halfQ.IsTransversalFunctor halfF Λ' ∧
          halfS.IsBranchedSubcategory (fun α => (Λ' (halfF.toFun α) : ℚ)) ∧
          halfC.IsCompactBranched (fun α => (Λ' (halfF.toFun α) : ℚ)) := by
  obtain ⟨⟨N, hN⟩, hU⟩ := halfF_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  have h0 := pointwiseNormFunctor_zeroFunctor_eq_zero hN
  refine ⟨corner_mem_boundarySet, exists_ne_unit_corner, topPoint_mem_zeroSet_boundarySet,
    zeroFunctor_halfF_topPoint_pos, N, U, hN, hU.controlsCompactness,
    isBoundaryStructurableFunctor_zeroFunctor, isBoundaryFaceOntoFunctor_halfF, ?_⟩
  exact theorem_15_3_9_categorical halfS_isTame halfQ_hasModelMPolyfoldPartitionsOfUnity
    isScFredholmSectionFunctor_halfF isScFredholmSectionFunctorTame_halfF
    halfF_hasCompactModuliSpace hN hU.controlsCompactness isBoundaryStructurableFunctor_zeroFunctor
    (by rw [orbitBoundaryDomSupp_zeroFunctor]; exact empty_subset _)
    (fun α _ => by rw [h0]; exact zero_le_one) halfS_isContinuousFunctionFunctor_one
    (fun _ => ⟨one_pos, le_rfl⟩) (fun α _ => by rw [h0, ENNReal.ofReal_one]; exact one_pos)
    isBoundaryFaceOntoFunctor_halfF

/-! ### Theorem 18.2.6 -/

/-- `|ℤ/2 ⋉ H|` is metrizable. -/
instance metrizableSpace_orbitSpace_halfC : MetrizableSpace halfC.toGroupoidStr.OrbitSpace :=
  metrizableSpace_translation_orbitSpace isScSmoothMap_halfSmul

/-- `H = [0, ∞) × ℝ` is locally compact (closed in `ℝ ⊕ ℝ`). -/
instance locallyCompactSpace_H : LocallyCompactSpace (H 1) :=
  (quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The model `⊔_{Unit} (H × ℝ)` has reflexive `(0, 1)`-fibres (fibre model `ℝ`). -/
theorem halfSingle_hasReflexiveFibersIn : halfQ.HasReflexiveFibersIn halfSingle.Ψ :=
  StrongBundle.hasReflexiveFibers_of_atlas fun c ⟨_, c', hc', hcc⟩ => by
    subst hcc
    rw [mem_singleton_iff.1 hc']
    exact isReflexive_of_finiteDimensional (F := Fin 1 → ℝ)

theorem halfQ_hasReflexiveFibers : halfQ.HasReflexiveFibers :=
  (halfQ.hasReflexiveFibers_iff_model halfSingle).2 halfSingle_hasReflexiveFibersIn

/-- **Definition 18.2.4 for `f`**: the reflexive local compactness property (`H` is locally
compact). -/
theorem halfF_hasReflexiveLocalCompactness : halfQ.HasReflexiveLocalCompactness halfF :=
  have : ∀ i, WeaklyLocallyCompactSpace (halfQ.modelBase halfSingle.Ψ i).1.O := fun _ =>
    inferInstanceAs (WeaklyLocallyCompactSpace (H 1))
  hasReflexiveLocalCompactness_of_locallyCompact halfSingle halfF

/-- The points of `H` of norm `< r`. -/
def ballH (r : ℝ) : Set (H 1) := {x | ‖(x : Pm 1)‖ < r}

/-- `W' = |{‖x‖ < 2}|`, an open neighbourhood of the boundary zeros `(0, ±1)`. -/
def halfW' : Set halfC.toGroupoidStr.OrbitSpace := halfC.toGroupoidStr.π '' ballH 2

theorem isOpen_halfW' : IsOpen halfW' :=
  GroupoidStr.isOpenMap_π_translation continuous_halfSmul _
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)

/-- `U_∂ = W' ∩ |∂C|`. -/
def halfUb : Set halfC.toGroupoidStr.OrbitSpace :=
  halfW' ∩ halfC.toGroupoidStr.π '' halfS.boundarySet

/-- The zeros of `φ` have norm `≤ 1`. -/
theorem norm_le_one_of_halfDiscMap_eq_zero {p : Pm 1} (hp : halfDiscMap p = 0) : ‖p‖ ≤ 1 := by
  have h := (halfDiscMap_eq_zero_iff _).1 hp
  have ha : |p.1 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg (p.2 0)]
  have hy : |p.2 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg (p.1 0)]
  rw [norm_prod_le_iff]
  refine ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_,
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact ha
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact hy

/-- The zeros of `f` have norm `≤ 1`. -/
theorem norm_le_one_of_mem_zeroSet {x : H 1} (hx : x ∈ halfF.zeroSet) : ‖(x : Pm 1)‖ ≤ 1 := by
  rw [halfF_zeroSet] at hx
  exact norm_le_one_of_halfDiscMap_eq_zero hx

/-- `|S_f ∩ ∂C| ⊆ U_∂`. -/
theorem zeroSet_boundary_subset_halfUb :
    halfC.toGroupoidStr.π '' (halfF.zeroSet ∩ halfS.boundarySet) ⊆ halfUb := by
  rintro _ ⟨x, ⟨hx, hb⟩, rfl⟩
  exact ⟨⟨x, lt_of_le_of_lt (norm_le_one_of_mem_zeroSet hx) one_lt_two, rfl⟩, ⟨x, hb, rfl⟩⟩

/-- `U_∂ ≠ ∅`: it contains `|(0, 1)|`. -/
theorem topPoint_mem_halfUb : halfC.toGroupoidStr.π topPoint ∈ halfUb :=
  zeroSet_boundary_subset_halfUb ⟨topPoint, topPoint_mem_zeroSet_boundarySet, rfl⟩

/-- `|{‖x‖ ≤ 2}|` is compact. -/
theorem isCompact_closedBallH :
    IsCompact (halfC.toGroupoidStr.π '' {x : H 1 | ‖(x : Pm 1)‖ ≤ 2}) := by
  refine IsCompact.image ?_ continuous_quot_mk
  have e : {x : H 1 | ‖(x : Pm 1)‖ ≤ 2} = (↑) ⁻¹' Metric.closedBall (0 : Pm 1) 2 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [e]
  exact (quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_closedBall (0 : Pm 1) 2)

/-- **The hypotheses of Theorem 18.2.6 hold for `f` on `ℤ/2 ⋉ H` with `∂C ≠ ∅`** (`C` tame,
reflexive fibres, a reflexive auxiliary norm `N`, compact moduli space, reflexive local
compactness, and `U_∂ = |{‖x‖ < 2}| ∩ |∂C|`, a non-empty open subset of `|∂C|` containing
`|S_f ∩ ∂C| = {|(0, ±1)|}`, with `cl(U_∂ ∩ {|N| ∘ |f| ≤ 1})` compact), and its conclusion: an
open `U ⊇ |S_f|` with `U ∩ |∂C| = U_∂` such that `(N, U)` controls compactness. -/
theorem theorem_18_2_6_witness_boundary :
    ∃ N : halfV.EObj → ℝ≥0∞, halfQ.IsReflexiveAuxNormFunctor N ∧
      halfS.IsTame ∧ halfQ.HasReflexiveFibers ∧
      halfQ.IsScFredholmSectionFunctor halfF ∧ halfF.HasCompactModuliSpace ∧
      halfQ.HasReflexiveLocalCompactness halfF ∧
      halfC.toGroupoidStr.π topPoint ∈ halfUb ∧
      ∃ U, U ∩ halfC.toGroupoidStr.π '' halfS.boundarySet = halfUb ∧
        halfF.ControlsCompactness N U := by
  obtain ⟨N, hN⟩ := halfQ.exists_isReflexiveAuxNormFunctor halfQ_hasStrongBundleUniformizers
    halfQ_hasReflexiveFibers
  refine ⟨N, hN, halfS_isTame, halfQ_hasReflexiveFibers, isScFredholmSectionFunctor_halfF,
    halfF_hasCompactModuliSpace, halfF_hasReflexiveLocalCompactness, topPoint_mem_halfUb, ?_⟩
  refine halfQ.theorem_18_2_6 halfF halfQ_hasStrongBundleUniformizers halfS_isTame
    halfQ_hasReflexiveFibers hN isScFredholmSectionFunctor_halfF halfF_hasCompactModuliSpace
    halfF_hasReflexiveLocalCompactness ⟨halfW', isOpen_halfW', rfl⟩
    zeroSet_boundary_subset_halfUb ?_
  refine isCompact_closedBallH.closure_of_subset (inter_subset_left.trans
    (inter_subset_left.trans (image_mono fun x hx =>
      show ‖(x : Pm 1)‖ ≤ 2 from le_of_lt hx)))

end GCT.VectorBundle.HalfSpaceReflection

end Polyfold
