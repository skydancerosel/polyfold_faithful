import Polyfold.Chapter17.TameOrientedTransfer
import Polyfold.Chapter17.ModelPropertiesExamples
import Polyfold.Chapter9.HalfCircleWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 (pp. 820–824): a polyfold-level oriented branched ep⁺-subcategory with non-empty support
which is tame, oriented, compact, of dimension `1`, with non-empty boundary — a witness for the
hypotheses of Theorems 17.6.4–17.6.10.  Numbers and pages are the 2021 text's.

# The closed half-circle in the half-plane polyfold

`C = {1} ⋉ ([0, ∞) × ℝ)` is the translation GCT of the trivial group on the half-plane `Q2`
(Chapter 9's `Pa`, `HalfCircleSheet`) with its tautological polyfold structure
(`halfPlaneConstruction`, covering family `halfPlaneFamily = {Ψ₀}`).  The ep-groupoid
`AA = trivial Pa` of Chapter 9 carries the oriented closed half-circle `Θ̂ = (1_{arc}, T̂)`
(`HalfCircle.thetaA`, `HalfCircle.TA`), with oriented tame structures of dimension `1` at every
point (`HalfCircle.arc_hloc`).

* `halfPlaneTrivialFunctor : trivial Pa → {1} ⋉ Q2` (`y ↦ y`, `y ↦ (1, y)`) is an equivalence,
  and so is `halfPlaneModelFunctor : trivial Pa → X_Ψ` (followed by `tautModelFunctor`).
* `halfPlaneTheta = Γ_*(E_*Θ)` (`E = halfPlaneModelFunctor`) is a branched ep⁺-subcategory of `C`
  (Proposition 17.5.2 (1)) with `Γ^*halfPlaneTheta = E_*Θ`; `halfPlaneArc` is the oriented
  subcategory with orientation `E_*T̂` on the model (`ofModel`).
* `halfPlaneArc_isTameOrientedVia`, `halfPlaneArc_isTameOriented` (moved from
  `HalfCircle.arc_hloc` along `E`), `isCompactBranched_halfPlaneTheta`,
  `halfPlaneArc_boundaryVia_eq_one` (`∂Θ = 1` at an end point, on every covering family),
  `halfPlane_isLUC`, `halfPlaneModel_hasScPartitionsOfUnity`.
* **`halfPlaneArc_properties`**: `supp Θ ≠ ∅`, `|supp Θ|` compact, `Θ̂` tame and oriented of
  dimension `1` on every covering family, `∂Θ ≠ 0` (Definition 17.6.5), (LUC), sc-smooth
  partitions of unity on the model.
* **`halfPlaneArc_stokes`**, **`halfPlaneArc_stokes_eff`**: Theorems 17.6.7 and 17.6.10 for `n = 1`
  for this `Θ̂` (`theorem_17_6_7_dim1_book`, `theorem_17_6_10_dim1_book`).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

open EpGroupoid MPolyfold EPLocalization EPLocalization.EPLoc HalfCircle

namespace GCT.PolyfoldConstruction

/-- The trivial group `{1}` (as `Multiplicative (ZMod 1)`) acting on the half-plane `Q2`. -/
scoped instance instMulActionZ1HalfPlane : MulAction (Multiplicative (ZMod 1)) Q2 where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isScSmoothMap_z1_smul_halfPlane (k : Multiplicative (ZMod 1)) :
    Pa.IsScSmoothMap Pa fun y : Q2 => k • y :=
  MPolyfold.isScSmoothMap_id

/-- **The polyfold `{1} ⋉ ([0, ∞) × ℝ)`** with its tautological polyfold structure. -/
abbrev halfPlaneConstruction :
    (GCT.translation (Multiplicative (ZMod 1)) Q2
      isScSmoothMap_z1_smul_halfPlane).PolyfoldConstruction :=
  tautConstruction isScSmoothMap_z1_smul_halfPlane

/-- The covering family `{Ψ₀}` of the half-plane polyfold. -/
abbrev halfPlaneFamily : halfPlaneConstruction.CoveringFamily :=
  tautSingleFamily isScSmoothMap_z1_smul_halfPlane HalfCircle.pt1

/-- **`trivial Pa → {1} ⋉ Q2`**: `y ↦ y`, `y ↦ (1, y)`. -/
def halfPlaneTrivialFunctor :
    EpFunctor (trivial Pa) (EpGroupoid.Examples.actionEpGroupoid isScSmoothMap_z1_smul_halfPlane)
    where
  obj y := y
  mor y := (1, y)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    have h' : φ = ψ := h
    subst h'
    rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor :=
    (EpGroupoid.Examples.actionEpGroupoid isScSmoothMap_z1_smul_halfPlane).isScSmoothMap_unit

theorem isEquivalence_halfPlaneTrivialFunctor : halfPlaneTrivialFunctor.IsEquivalence := by
  refine EpFunctor.lemma_10_1_2 _ ?_ MPolyfold.isLocalScDiffeo_id
  refine { full := ?_, faithful := ?_, essSurj := ?_ }
  · exact (GroupoidFunctor.faithful_iff _).2 fun _ _ hs _ _ => hs
  · refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
    obtain ⟨k, y⟩ := ψ
    have hy : y = x := hs
    have hk : k = 1 := Subsingleton.elim _ _
    subst hy hk
    exact ⟨y, rfl, ht, rfl⟩
  · exact (GroupoidFunctor.essSurj_iff _).2 fun y => ⟨y, (1, y), rfl, rfl⟩

/-- **The equivalence `trivial Pa → X_Ψ`** (`halfPlaneTrivialFunctor` followed by
`tautModelFunctor`). -/
def halfPlaneModelFunctor :
    EpFunctor (trivial Pa) (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X :=
  (tautModelFunctor isScSmoothMap_z1_smul_halfPlane HalfCircle.pt1).comp halfPlaneTrivialFunctor

theorem isEquivalence_halfPlaneModelFunctor : halfPlaneModelFunctor.IsEquivalence :=
  (isEquivalence_tautModelFunctor _ _).comp isEquivalence_halfPlaneTrivialFunctor

/-- `E_*Θ` on the model, `Θ = 1_{arc}`. -/
def halfPlaneModelTheta : (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).Obj → ℚ :=
  halfPlaneModelFunctor.pushforwardTheta thetaA

/-- `E_*T̂` on the model. -/
def halfPlaneModelT :
    (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).Obj →
      (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.PObj.OrTangent →₀ ℚ :=
  halfPlaneModelFunctor.pushSection TA

theorem isBranchedEpSubgroupoid_halfPlaneModelTheta :
    (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.IsBranchedEpSubgroupoid
      halfPlaneModelTheta :=
  EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta isEquivalence_halfPlaneModelFunctor
    isBranchedEpSubgroupoid_thetaA

/-- **The branched ep⁺-subcategory `Γ_*(E_*Θ)` of the half-plane polyfold.** -/
def halfPlaneTheta : Q2 → ℚ := halfPlaneConstruction.modelPush halfPlaneFamily.Ψ halfPlaneModelTheta

theorem isBranchedSubcategory_halfPlaneTheta :
    halfPlaneConstruction.IsBranchedSubcategory halfPlaneTheta :=
  proposition_17_5_2_one halfPlaneFamily.cover isBranchedEpSubgroupoid_halfPlaneModelTheta

theorem modelPull_halfPlaneTheta :
    halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta = halfPlaneModelTheta :=
  modelPull_modelPush isBranchedEpSubgroupoid_halfPlaneModelTheta.isFunctorial

theorem isOrientation_halfPlaneModelT :
    (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.IsOrientation
      (halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta) halfPlaneModelT := by
  rw [modelPull_halfPlaneTheta]
  exact EpFunctor.isOrientation_pushSection isEquivalence_halfPlaneModelFunctor
    isBranchedEpSubgroupoid_thetaA hasIndependentTangentSums_thetaA isOrientation_thetaA

/-- **The oriented closed half-circle in the half-plane polyfold**: `Θ = Γ_*(E_*1_{arc})` with the
orientation `E_*T̂` on the model of `{Ψ₀}` (`ofModel`). -/
def halfPlaneArc : halfPlaneConstruction.OrientedSubcategory :=
  OrientedSubcategory.ofModel halfPlaneConstruction halfPlaneFamily halfPlaneTheta
    isBranchedSubcategory_halfPlaneTheta halfPlaneModelT isOrientation_halfPlaneModelT

/-- Oriented tame structures of dimension `1` describing `E_*T̂` at every point of `supp E_*Θ`
(moved from `HalfCircle.arc_hloc` along the equivalence `E`, the structures of Theorem
11.4.1). -/
theorem halfPlaneModel_hloc :
    ∀ x ∈ supp (halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta),
      ∃ D : (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.OrientedTameStructure (0 + 1)
        (halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta) x,
        D.Represents halfPlaneModelT := by
  rw [modelPull_halfPlaneTheta]
  intro x hx
  obtain ⟨D, -, hD⟩ := EpFunctor.hcov_push isEquivalence_halfPlaneModelFunctor
    (EP.epFormsInftyEval_isPullback (A := AA) isEquivalence_halfPlaneModelFunctor (0 + 1))
    isBranchedEpSubgroupoid_thetaA.isFunctorial
    (EpFunctor.isTransported_push isEquivalence_halfPlaneModelFunctor
      isOrientation_thetaA.isGrHatSection)
    (FormEval.hcov_of_tameOpen (FormEval.tameOpen AA.X) arc_hloc) x hx
  exact ⟨D, hD⟩

theorem supp_halfPlaneModelTheta_nonempty : (supp halfPlaneModelTheta).Nonempty := by
  refine ⟨halfPlaneModelFunctor.obj HalfCircle.pt1, ?_⟩
  change 0 < halfPlaneModelFunctor.pullbackTheta halfPlaneModelTheta HalfCircle.pt1
  rw [halfPlaneModelTheta,
    EpFunctor.pullbackTheta_pushforwardTheta isEquivalence_halfPlaneModelFunctor.full
    isBranchedEpSubgroupoid_thetaA.isFunctorial]
  have := HalfCircle.pt1_mem_arc
  simp [thetaA, this]

theorem isCompactBranched_halfPlaneTheta :
    (GCT.translation (Multiplicative (ZMod 1)) Q2
      isScSmoothMap_z1_smul_halfPlane).IsCompactBranched halfPlaneArc.Θ := by
  refine (isCompactBranched_iff_model halfPlaneFamily
    isBranchedSubcategory_halfPlaneTheta.isFunctorial).2 ?_
  rw [modelPull_halfPlaneTheta]
  exact halfPlaneModelFunctor.isCompactBranched_pushforwardTheta
    isEquivalence_halfPlaneModelFunctor.full isBranchedEpSubgroupoid_thetaA.isFunctorial
    isCompactBranched_thetaA

/-- **`halfPlaneArc` is tame and oriented of dimension `1` on every covering family.** -/
theorem halfPlaneArc_isTameOrientedVia (c : halfPlaneConstruction.CoveringFamily) :
    halfPlaneArc.IsTameOrientedVia c (0 + 1) :=
  OrientedSubcategory.ofModel_isTameOrientedVia halfPlaneFamily halfPlaneTheta
    isBranchedSubcategory_halfPlaneTheta halfPlaneModelT isOrientation_halfPlaneModelT
    halfPlaneModel_hloc c

theorem halfPlaneArc_isTameOriented : halfPlaneArc.IsTameOriented (0 + 1) :=
  ⟨halfPlaneFamily, halfPlaneArc_isTameOrientedVia halfPlaneFamily⟩

/-- **`∂Θ ≠ 0`** (Definition 17.6.5): on every covering family, `∂Θ = Γ_*(∂Γ^*Θ)` takes the value
`1` at the object `Γ(E(pt1))`, `pt1 = (0, 1)` an end point of the half-circle. -/
theorem halfPlaneArc_boundaryVia_eq_one (c : halfPlaneConstruction.CoveringFamily) :
    halfPlaneArc.boundaryVia c ((halfPlaneConstruction.modelFunctor halfPlaneFamily.Ψ).obj
      (halfPlaneModelFunctor.obj HalfCircle.pt1)) = 1 := by
  rw [← halfPlaneArc.definition_17_6_5 halfPlaneFamily c]
  have h := congrFun (halfPlaneArc.modelPull_boundaryVia halfPlaneFamily)
    (halfPlaneModelFunctor.obj HalfCircle.pt1)
  refine h.trans ?_
  change (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.boundaryTheta
      (halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta)
      (halfPlaneModelFunctor.obj HalfCircle.pt1) = 1
  rw [modelPull_halfPlaneTheta, halfPlaneModelTheta,
    ← EpFunctor.boundaryTheta_pushforwardTheta isEquivalence_halfPlaneModelFunctor
      isBranchedEpSubgroupoid_thetaA hasIndependentTangentSums_thetaA]
  change halfPlaneModelFunctor.pullbackTheta
      (halfPlaneModelFunctor.pushforwardTheta (AA.X.boundaryTheta thetaA)) HalfCircle.pt1 = 1
  rw [EpFunctor.pullbackTheta_pushforwardTheta isEquivalence_halfPlaneModelFunctor.full
    (AA.X.isFunctorial_boundaryTheta isBranchedEpSubgroupoid_thetaA
      hasIndependentTangentSums_thetaA)]
  exact boundaryTheta_pt1

/-- The half-plane polyfold has (LUC) (Definition 17.1.22): its model is equivalent to
`trivial Pa`, which has (LUC). -/
theorem halfPlane_isLUC : halfPlaneConstruction.IsLUC := by
  have : IsIso (localizationFunctor.map (X := AA)
      (Y := halfPlaneConstruction.modelEP halfPlaneFamily.Ψ) halfPlaneModelFunctor) :=
    isInvertedBy_localizationFunctor _ isEquivalence_halfPlaneModelFunctor
  exact ⟨halfPlaneFamily,
    (isGenIsoInvariant_isLUC ((isGeneralizedIso_iff_isIso _).2 this)).1 arc_isLUC⟩

/-- **The model of the half-plane polyfold admits sc-smooth partitions of unity** (Theorem 7.5.7:
`|X_Ψ|` is metrizable and `Σ_{PUnit} Pa` has the chart `id` of `[0, ∞) × ℝ`, Theorem 5.5.10,
Proposition 5.5.11). -/
theorem halfPlaneModel_hasScPartitionsOfUnity :
    (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.HasScPartitionsOfUnity := by
  refine EpGroupoid.theorem_7_5_7 _ ?_ ?_
  · have := metrizableSpace_modelOrbitSpace_of_family (S := halfPlaneConstruction)
      (Ψ := halfPlaneFamily.Ψ)
    let _ := TopologicalSpace.metrizableSpaceMetric
      (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.OrbitSpace
    exact (inferInstance :
      ParacompactSpace (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.OrbitSpace)
  · refine theorem_5_5_10.2 ⟨{MPolyfold.sigmaChart PUnit.unit chartA}, fun φ hφ => ?_,
      fun x => ⟨_, mem_singleton _, ?_⟩, fun φ hφ => ?_⟩
    · rw [mem_singleton_iff.1 hφ]; exact MPolyfold.IsChart.sigmaChart isChart_chartA
    · obtain ⟨i, y⟩ := x
      exact ⟨y, mem_univ y, rfl⟩
    · rw [mem_singleton_iff.1 hφ]
      exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional V2)

/-- **The hypotheses of Theorems 17.6.4–17.6.10 hold jointly in a non-degenerate case**: for the
oriented closed half-circle `halfPlaneArc` in the half-plane polyfold, `supp Θ ≠ ∅`, `|supp Θ|`
is compact, `Θ̂` is tame and oriented of dimension `1` on every covering family,
`∂Θ ≠ 0` on every covering family, `C` has (LUC), and the model of `{Ψ₀}` admits sc-smooth
partitions of unity. -/
theorem halfPlaneArc_properties :
    (∃ α, 0 < halfPlaneArc.Θ α) ∧
      (GCT.translation (Multiplicative (ZMod 1)) Q2
        isScSmoothMap_z1_smul_halfPlane).IsCompactBranched halfPlaneArc.Θ ∧
      (∀ c, halfPlaneArc.IsTameOrientedVia c (0 + 1)) ∧
      (∀ c, ∃ α, halfPlaneArc.boundaryVia c α = 1) ∧
      halfPlaneConstruction.IsLUC ∧
      (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.HasScPartitionsOfUnity := by
  refine ⟨?_, isCompactBranched_halfPlaneTheta, halfPlaneArc_isTameOrientedVia,
    fun c => ⟨_, halfPlaneArc_boundaryVia_eq_one c⟩, halfPlane_isLUC,
    halfPlaneModel_hasScPartitionsOfUnity⟩
  obtain ⟨x, hx⟩ := supp_halfPlaneModelTheta_nonempty
  refine ⟨(halfPlaneConstruction.modelFunctor halfPlaneFamily.Ψ).obj x, ?_⟩
  have h := congrFun modelPull_halfPlaneTheta x
  change 0 < halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta x
  rw [h]
  exact hx

/-- **Theorem 17.6.7 (Stokes, `n = 1`) for the oriented closed half-circle in the half-plane
polyfold**: `∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]` for every `[ω] ∈ Ω∞⁰(C)`, both sides computed on `C`
(`theorem_17_6_7_dim1_book`; here `∂Θ ≠ 0`). -/
theorem halfPlaneArc_stokes (ω : halfPlaneConstruction.catFormsInfty 0) :
    halfPlaneArc.integral (Nat.succ_pos 0) isCompactBranched_halfPlaneTheta
        halfPlaneArc_isTameOriented (halfPlaneConstruction.catFormsInftyD 0 ω) =
      halfPlaneArc.boundaryIntegralDim1 isCompactBranched_halfPlaneTheta
        halfPlaneArc_isTameOriented ω :=
  halfPlaneArc.theorem_17_6_7_dim1_book halfPlaneFamily
    (EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity _
      halfPlaneModel_hasScPartitionsOfUnity) _ _ ω

/-- **Theorem 17.6.10 (effective Stokes, `n = 1`) for the oriented closed half-circle in the
half-plane polyfold** (`C` has (LUC)). -/
theorem halfPlaneArc_stokes_eff (ω : halfPlaneConstruction.catFormsInfty 0) :
    halfPlaneArc.integralEff halfPlane_isLUC (Nat.succ_pos 0) isCompactBranched_halfPlaneTheta
        halfPlaneArc_isTameOriented (halfPlaneConstruction.catFormsInftyD 0 ω) =
      halfPlaneArc.boundaryIntegralEffDim1 halfPlane_isLUC isCompactBranched_halfPlaneTheta
        halfPlaneArc_isTameOriented ω :=
  halfPlaneArc.theorem_17_6_10_dim1_book halfPlane_isLUC halfPlaneFamily
    (EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity _
      halfPlaneModel_hasScPartitionsOfUnity) _ _ ω

end GCT.PolyfoldConstruction

end Polyfold
