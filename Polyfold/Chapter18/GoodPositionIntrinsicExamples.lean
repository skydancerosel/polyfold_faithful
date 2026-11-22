import Polyfold.Chapter18.GoodPositionIntrinsic
import Polyfold.Chapter18.HalfSpaceWitnesses
import Polyfold.Chapter18.TangentPartialConeExamples
import Polyfold.Chapter4.NonVacuityG
import Polyfold.Chapter4.Characterization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV: Theorem 18.1.5
(p. 846) and Remark 17.2.18 (p. 784), with Definition 3.1.24: **non-degenerate witnesses for
"`ker f'(α)` is in good position to `C_αC`"** on `C = ℤ/2 ⋉ H`, `H = [0, ∞) × ℝ`
(`HalfSpaceBundleConstruction.lean`), with the section `f(a, y) = a² + y² − 1`
(`HalfSpaceWitnesses.lean`), whose zero set meets `∂C` at `(0, ±1)`.

* `halfCoord p : T_pC ≅ ℝ ⊕ ℝ`; on `∂C`, `C_pC = {α ≥ 0}` and `T^R_pC = {α = 0}`
  (`partialCone_halfS_eq`, `mem_reducedTangent_halfS_iff`).
* `isInGoodPositionToPartialCone_halfS_iff`: at a boundary object, a non-zero `N ⊆ T_pC` is in
  good position to `C_pC` iff `N ⊄ T^R_pC`.
* `isInGoodPositionToPartialCone_corner`: at the corner `(0, 0)`, which has the non-trivial
  automorphism `(−1, (0, 0))`, the line `ℝ·(1, 0)` is in good position to `C_αC`, and the
  non-zero `T^R_αC` is not.
* `theorem_18_1_5_intrinsic_hyp_witness`: at the boundary zero `(0, 1)` of `f`, `C_αC ≠ T_αC`,
  `f'(α)` is onto and `ker f'(α) ≠ 0` is in good position to `C_αC`;
  `theorem_18_1_5_intrinsic_hyp_applies`: the conclusions of `theorem_18_1_5`
  there.

The zeros `(0, ±1)` of `f` have trivial isotropy.  At the corner every `ℤ/2`-invariant section of
this bundle (the fibre action is trivial) has `Dφ(0, 0) = (∂_aφ, 0)`, so a kernel of a surjective
`Dφ(0, 0)` is `T^R_αC`, which is not in good position; the corner witness is therefore stated for
subspaces of `T_αC`, not for a zero of a section.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.HalfSpaceReflection

open PolyfoldConstruction HalfSpaceBundle MPolyfold StrongPolyfoldBundleConstruction

/-- Every object of `ℤ/2 ⋉ H` is smooth. -/
theorem isSmoothObj_halfS (p : H 1) : halfS.IsSmoothObj p :=
  (isSmoothObj_obj_iff (tautUnif _ _ p) p).2 (smoothSet_eq_univ (m := 1) ▸ mem_univ p)

/-- `T_αC` is defined at every object of `ℤ/2 ⋉ H`, as an instance. -/
instance fact_tangentObj_halfS (p : H 1) : Fact (halfS.TangentObj p) :=
  ⟨tangentObj_of_isSmoothObj halfS_hasUniformizers (isSmoothObj_halfS p)⟩

/-- The base M-polyfold `H` of `Ψ̄`. -/
abbrev halfP := (halfUC.baseUnif halfΨ).1.P

/-- A point `p ∈ H` on level `1`. -/
def halfPt (p : H 1) : halfP.Level 1 :=
  halfP.levelMk 1 p (by have h := levelSet_eq_univ (m := 1) 1; exact h ▸ mem_univ _)

/-- `Ψ(p) = p`. -/
theorem obj_halfPt (p : H 1) :
    (halfUC.baseUnif halfΨ).1.obj (halfP.levelVal 1 (halfPt p)) = p := rfl

/-- The inclusion `H → ℝ ⊕ ℝ` is a chart of the base of `Ψ̄`. -/
theorem isChart_baseChart_halfP : halfP.IsChart (baseChart 1) :=
  (basePoly 1).isChart_of_mem (mem_singleton _)

/-- Every point lies in the chart. -/
theorem mem_baseChart_source_halfPt (p : H 1) : halfP.levelVal 1 (halfPt p) ∈ (baseChart 1).source :=
  mem_univ _

/-- `T_pH = ℝ ⊕ ℝ` in the chart of `H`. -/
theorem tangentFiberModel_halfPt (p : H 1) :
    tangentFiberModel isChart_baseChart_halfP (mem_baseChart_source_halfPt p) = ⊤ := by
  refine (Submodule.eq_top_iff'.2 fun v => ?_)
  have h : tangentSpace (baseChart 1).model.E (baseChart 1).model.C (baseChart 1).model.O
      (levelLift (baseChart 1) 1 (halfP.levelVal 1 (halfPt p))) = univ :=
    tangentSpace_relOpen (relOpen_H 1)
      (levelLift_mem_lvlSet_one isChart_baseChart_halfP (mem_baseChart_source_halfPt p))
  exact (Set.ext_iff.1 h v).2 (mem_univ v)

/-- **The coordinates `T_pC ≅ ℝ ⊕ ℝ`** at `p ∈ H` (`S_Ψ` followed by the chart of `H`). -/
def halfCoord (p : H 1) : halfS.TangentSpaceAt p ≃L[ℝ] (halfSpaceSc 1) 0 :=
  ((halfS.tangentChartCLE p (halfUC.baseUnif halfΨ) (halfPt p) (obj_halfPt p)).trans
    (tangentFiberContinuousLinearEquiv isChart_baseChart_halfP (mem_baseChart_source_halfPt p))).trans
    { LinearEquiv.ofTop _ (tangentFiberModel_halfPt p) with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }

/-- `halfCoord p` is the chart coordinate of `S_Ψ`. -/
theorem halfCoord_apply (p : H 1) (e : halfS.TangentSpaceAt p) :
    halfCoord p e = fiberCoord isChart_baseChart_halfP (mem_baseChart_source_halfPt p)
      (halfS.tangentChartCLE p (halfUC.baseUnif halfΨ) (halfPt p) (obj_halfPt p) e) := rfl

/-- **`C_pC` in coordinates**: `{(α, η) | α ≥ 0}` if `p ∈ ∂H`, everything otherwise. -/
theorem mem_partialCone_halfS_iff (p : H 1) (e : halfS.TangentSpaceAt p) :
    e ∈ halfS.partialCone p ↔ ((p : Pm 1).1 0 = 0 → 0 ≤ (halfCoord p e).1 0) := by
  rw [halfS.partialCone_eq p (halfUC.baseUnif halfΨ) (halfPt p) (obj_halfPt p) isChart_baseChart_halfP
    (mem_baseChart_source_halfPt p) (ScIso.refl _) rfl]
  show fiberCoord isChart_baseChart_halfP (mem_baseChart_source_halfPt p)
      (halfS.tangentChartCLE p (halfUC.baseUnif halfΨ) (halfPt p) (obj_halfPt p) e) ∈
      partialQuadrantAtWith (ScIso.refl _) ((baseChart 1) (halfP.levelVal 1 (halfPt p))) ↔ _
  rw [← halfCoord_apply]
  constructor
  · intro h hp
    exact h 0 hp
  · intro h i hi
    rw [Subsingleton.elim i 0] at hi ⊢
    exact h hi

/-- On `∂H`, `C_pC = {α ≥ 0}` in coordinates. -/
theorem mem_partialCone_halfS_iff_of_boundary {p : H 1} (hp : p ∈ halfS.boundarySet)
    (e : halfS.TangentSpaceAt p) : e ∈ halfS.partialCone p ↔ 0 ≤ (halfCoord p e).1 0 := by
  rw [mem_partialCone_halfS_iff, (mem_boundarySet_iff p).1 hp]
  exact ⟨fun h => h rfl, fun h _ => h⟩

/-- On `∂H`, `T^R_pC = {α = 0}` in coordinates. -/
theorem mem_reducedTangent_halfS_iff {p : H 1} (hp : p ∈ halfS.boundarySet)
    (e : halfS.TangentSpaceAt p) : e ∈ halfS.reducedTangent p ↔ (halfCoord p e).1 0 = 0 := by
  rw [mem_reducedTangent_iff_lineality, mem_partialCone_halfS_iff_of_boundary hp,
    mem_partialCone_halfS_iff_of_boundary hp, map_neg]
  change (0 ≤ (halfCoord p e).1 0 ∧ 0 ≤ -(halfCoord p e).1 0) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    linarith
  · intro h
    rw [h]
    simp

/-- `C_pC = (halfCoord p)⁻¹(H)` on `∂H`. -/
theorem partialCone_halfS_eq {p : H 1} (hp : p ∈ halfS.boundarySet) :
    halfS.partialCone p = halfCoord p ⁻¹' quadrant 1 (rnSc 1) 0 := by
  ext e
  rw [mem_partialCone_halfS_iff_of_boundary hp]
  exact mem_quadrant_one_iff.symm

/-- **Good position to `C_pC` on `∂C`**: a non-zero subspace `N ⊆ T_pC` at a boundary object of
`ℤ/2 ⋉ H` is in good position to `C_pC` iff `N ⊄ T^R_pC`. -/
theorem isInGoodPositionToPartialCone_halfS_iff {p : H 1} (hp : p ∈ halfS.boundarySet)
    {N : Submodule ℝ (halfS.TangentSpaceAt p)} (hN : N ≠ ⊥) :
    halfS.IsInGoodPositionToPartialCone p N ↔ ¬ N ≤ halfS.reducedTangent p := by
  constructor
  · intro h hle
    exact not_isInGoodPositionToPartialCone_of_le_reducedTangent (S := halfS) p halfS_isTame
      (isSmoothObj_halfS p) hp hle hN h
  · intro hle
    obtain ⟨e, he, heR⟩ := SetLike.not_le_iff_exists.1 hle
    rw [mem_reducedTangent_halfS_iff hp] at heR
    rw [IsInGoodPositionToPartialCone, partialCone_halfS_eq hp, isInGoodPositionTop_preimage_iff,
      isInGoodPositionTop_iff_norm]
    obtain ⟨-, hi, P, -, h1, h2, ε, hε, hg⟩ := isInGoodPositionIn_halfSpace (m := 1)
      (N.map (halfCoord p : halfS.TangentSpaceAt p →ₗ[ℝ] (halfSpaceSc 1) 0))
      ⟨halfCoord p e, ⟨e, he, rfl⟩, heR⟩
    exact ⟨hi, P, IsCompl.of_eq h1 h2, ε, hε, hg⟩

/-- `T_pC` has dimension `2`. -/
theorem finrank_tangentSpaceAt_halfS (p : H 1) :
    Module.finrank ℝ (halfS.TangentSpaceAt p) = 2 := by
  rw [(halfCoord p).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ)) = 2
  simp

/-- The tangent vector with coordinates `(1, 0)`. -/
def tangentA (p : H 1) : halfS.TangentSpaceAt p := (halfCoord p).symm ((fun _ => 1, 0))

/-- The tangent vector with coordinates `(0, 1)`. -/
def tangentY (p : H 1) : halfS.TangentSpaceAt p := (halfCoord p).symm ((0, fun _ => 1))

/-- The coordinates of `tangentA p`. -/
theorem halfCoord_tangentA (p : H 1) : halfCoord p (tangentA p) = ((fun _ => 1, 0)) := by
  simp [tangentA]

/-- The coordinates of `tangentY p`. -/
theorem halfCoord_tangentY (p : H 1) : halfCoord p (tangentY p) = ((0, fun _ => 1)) := by
  simp [tangentY]

/-- **A non-zero proper subspace in good position at the corner, and the reduced tangent space
not in good position** (Remark 17.2.18 with Definition 3.1.24): at the corner `α = (0, 0)` of
`ℤ/2 ⋉ H`, a boundary object with the non-trivial automorphism `(−1, (0, 0))`, the line
`N = ℝ·(1, 0)` (`N ≠ 0`, `N ≠ T_αC`) is in good position to `C_αC`, while `T^R_αC ≠ 0` is not. -/
theorem isInGoodPositionToPartialCone_corner :
    corner ∈ halfS.boundarySet ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      Submodule.span ℝ {tangentA corner} ≠ ⊥ ∧ Submodule.span ℝ {tangentA corner} ≠ ⊤ ∧
      halfS.IsInGoodPositionToPartialCone corner (Submodule.span ℝ {tangentA corner}) ∧
      halfS.reducedTangent corner ≠ ⊥ ∧
      ¬ halfS.IsInGoodPositionToPartialCone corner (halfS.reducedTangent corner) := by
  have hA := halfCoord_tangentA corner
  have hY := halfCoord_tangentY corner
  have hA0 : tangentA corner ≠ 0 := fun h => by
    rw [h, map_zero] at hA
    have := congrArg (fun v : (halfSpaceSc 1) 0 => v.1 0) hA
    simp at this
  have hY0 : tangentY corner ≠ 0 := fun h => by
    rw [h, map_zero] at hY
    have := congrArg (fun v : (halfSpaceSc 1) 0 => v.2 0) hY
    simp at this
  have hYR : tangentY corner ∈ halfS.reducedTangent corner := by
    rw [mem_reducedTangent_halfS_iff corner_mem_boundarySet, hY]
    rfl
  have hR0 : halfS.reducedTangent corner ≠ ⊥ := fun h => hY0 (by
    rw [h] at hYR; exact (Submodule.mem_bot ℝ).1 hYR)
  have hN0 : Submodule.span ℝ {tangentA corner} ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]; exact hA0
  refine ⟨corner_mem_boundarySet, exists_ne_unit_corner, hN0, ?_, ?_, hR0, ?_⟩
  · intro h
    have hY' : tangentY corner ∈ Submodule.span ℝ {tangentA corner} := by
      rw [h]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hY'
    have := congrArg (fun v => (halfCoord corner v).2 0) ha
    simp only [map_smul, hA, hY] at this
    simp at this
  · rw [isInGoodPositionToPartialCone_halfS_iff corner_mem_boundarySet hN0]
    intro hle
    have := (mem_reducedTangent_halfS_iff corner_mem_boundarySet _).1
      (hle (Submodule.mem_span_singleton_self _))
    rw [hA] at this
    simp at this
  · rw [isInGoodPositionToPartialCone_halfS_iff corner_mem_boundarySet hR0]
    exact fun h => h le_rfl

/-- `f(0, 1) = 0`. -/
theorem halfF_zero_topPoint : halfF.toFun topPoint = halfV.objMk topPoint 0 :=
  topPoint_mem_zeroSet_boundarySet.1

/-- `F̄(p) ≠ ∅`. -/
theorem halfQ_F_nonempty (p : H 1) : (halfQ.F p).Nonempty := ⟨halfUnif, rfl⟩

/-- The point `(0, 1)` on level `1` of the base of `Ψ̄`, in the covering family `halfSingle`. -/
def topPt : (halfSingle.Ψ ()).1.base.P.Level 1 :=
  (halfSingle.Ψ ()).1.base.P.levelMk 1 topPoint
    (by have h := levelSet_eq_univ (m := 1) 1; exact h ▸ mem_univ _)

/-- **Part I's good position of `f_Ψ̄` at `(0, 1)`** (Definition 3.6.6): `Dφ(0, 1)` is onto and
its kernel contains `(1, 0)`. -/
theorem isGoodPositionGermTame_halfF_topPoint :
    (halfSingle.Ψ ()).1.B.IsGoodPositionGermTame ((halfSingle.Ψ ()).1.localRep halfF)
      ((halfSingle.Ψ ()).1.base.P.levelVal 1 topPt) := by
  change halfUnifData.B.IsGoodPositionGermTame (halfUnifData.localRep halfF) topPoint
  rw [localRep_halfF]
  refine HalfSpaceBundle.isGoodPositionGermTame_graphSection contDiff_halfDiscMap
    (fun w => ?_) (fun _ => ?_)
  · obtain ⟨v, -, hv⟩ := halfDiscMap_onto_hyperplane halfDiscMap_topPoint rfl w
    exact ⟨v, hv⟩
  · refine ⟨(fun _ => 1, 0), ?_, one_ne_zero⟩
    rw [(hasFDerivAt_halfDiscMap _).fderiv]
    funext i
    simp [coordA, coordY, topPoint]
    rfl

/-- The linearization `f'(0, 1) : T_{(0,1)}C → E_{(0,1)}` (Definition 18.1.3). -/
abbrev halfFLin : halfS.TangentSpaceAt topPoint →ₗ[ℝ] halfV.V topPoint :=
  halfQ.linearization halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor topPoint
    halfF_zero_topPoint (halfQ_F_nonempty topPoint)

/-- **The intrinsic hypothesis of Theorem 18.1.5 holds at a boundary zero**: at `(0, 1) ∈ ∂C ∩ S_f`,
`C_αC ≠ T_αC`, `f'(α)` is onto, and `ker f'(α)` is in good position to `C_αC`; the kernel is
non-zero and not contained in `T^R_αC`. -/
theorem theorem_18_1_5_intrinsic_hyp_witness :
    topPoint ∈ halfF.zeroSet ∩ halfS.boundarySet ∧ halfS.partialCone topPoint ≠ univ ∧
      Surjective halfFLin ∧
      halfQ.IsKernelInGoodPosition halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor
        topPoint halfF_zero_topPoint (halfQ_F_nonempty topPoint) ∧
      LinearMap.ker halfFLin ≠ ⊥ ∧ ¬ LinearMap.ker halfFLin ≤ halfS.reducedTangent topPoint := by
  have hb := topPoint_mem_zeroSet_boundarySet.2
  obtain ⟨hsurj, hker⟩ := (halfQ.isGoodPositionGermTame_localRep_iff
    isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor isScFredholmSectionFunctorTame_halfF
    topPoint halfF_zero_topPoint (halfQ_F_nonempty topPoint) (Ψ := halfSingle.Ψ ())
    (mem_singleton _) topPt rfl).1 isGoodPositionGermTame_halfF_topPoint
  have hk0 : LinearMap.ker halfFLin ≠ ⊥ := by
    intro h
    have hinj := LinearMap.ker_eq_bot.1 h
    have : FiniteDimensional ℝ (halfV.V topPoint) :=
      inferInstanceAs (FiniteDimensional ℝ (Fin 1 → ℝ))
    have hle := LinearMap.finrank_le_finrank_of_injective (f := halfFLin) hinj
    rw [finrank_tangentSpaceAt_halfS] at hle
    change 2 ≤ Module.finrank ℝ (Fin 1 → ℝ) at hle
    simp at hle
  refine ⟨topPoint_mem_zeroSet_boundarySet,
    partialCone_ne_univ (S := halfS) topPoint halfS_isTame (isSmoothObj_halfS _) hb, hsurj, hker,
    hk0, ?_⟩
  exact (isInGoodPositionToPartialCone_halfS_iff hb hk0).1 hker

/-- **Theorem 18.1.5 with the intrinsic hypothesis applies** at `(0, 1)`: there is a natural
representation `U(x₀)` in the model of `halfSingle` whose image is an open neighbourhood of
`|(0, 1)|`, on which `Θ ∘ Γ` has tame local branching structures at the zeros of `f`, `(f^Ψ̄, Λ₀)`
is in good position there, and the zero set is a smooth submanifold. -/
theorem theorem_18_1_5_intrinsic_hyp_applies :
    ∃ R : (halfQ.modelSEP halfSingle.Ψ).X.NaturalRep
        ⟨(), (halfSingle.Ψ ()).1.base.P.levelVal 1 topPt⟩,
      IsOpen ((halfS.modelFunctor (halfQ.modelBase halfSingle.Ψ)).orbitMap ''
        ((halfS.modelEP (halfQ.modelBase halfSingle.Ψ)).X.π '' R.U)) ∧
      halfC.toGroupoidStr.π topPoint ∈
        (halfS.modelFunctor (halfQ.modelBase halfSingle.Ψ)).orbitMap ''
          ((halfS.modelEP (halfQ.modelBase halfSingle.Ψ)).X.π '' R.U) ∧
      (∀ y ∈ R.U, (halfS.modelFunctor (halfQ.modelBase halfSingle.Ψ)).obj y ∈ halfF.zeroSet →
        Nonempty ((halfQ.modelSEP halfSingle.Ψ).X.TameBranchingStructure (fun z =>
          halfF.zeroIndicator ((halfS.modelFunctor (halfQ.modelBase halfSingle.Ψ)).obj z)) y) ∧
        SBLocalization.IsGoodPositionAt (A := halfQ.modelSEP halfSingle.Ψ)
          (halfQ.modelSection halfSingle.Ψ halfF)
          (SBLocalization.zeroMultisection (halfQ.modelSEP halfSingle.Ψ)) y) ∧
      (halfQ.modelSEP halfSingle.Ψ).X.PObj.IsSmoothSubmanifold
        {y ∈ R.U | (halfS.modelFunctor (halfQ.modelBase halfSingle.Ψ)).obj y ∈ halfF.zeroSet} := by
  obtain ⟨-, -, hsurj, hker, -⟩ := theorem_18_1_5_intrinsic_hyp_witness
  obtain ⟨R, hU, hπ, -, -, h1, h2, hS, -⟩ := halfQ.theorem_18_1_5 halfSingle.Ψ
    isScFredholmSectionFunctor_halfF isScFredholmSectionFunctorTame_halfF halfF_zero_topPoint
    (halfQ_F_nonempty topPoint) hsurj hker (i := ()) (mem_singleton _) topPt rfl
  exact ⟨R, hU, hπ, fun y hy hz => ⟨h1 y hy hz, h2 y hy hz⟩, hS⟩

end GCT.VectorBundle.HalfSpaceReflection

end Polyfold
