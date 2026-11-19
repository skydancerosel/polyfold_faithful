import Polyfold.Chapter16.HalfDiscBoundaryIntegral
import Polyfold.Chapter9.IntervalCobordismFaceStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 2.5.10,
Theorem 6.6.18, Remark 6.6.19 and the proof of Theorem 6.7.1 (pp. 275–278), on the half-disc
example of `HalfDiscIntervalCobordism.lean`.

# The half-disc cobordism as an instance of the general statements

`H = [0, ∞) × ℝ` (`∂H ≠ ∅`), the bundle `H × ℝ → H` (fibres `ℝ`),
`f(a, y) = ((a, y), a² + y² − 1)` with the orientation `halfDiscOrientation` (index `1`).

* `isFaceStructured_basePoly_one`: `H` is face-structured (`d_H ≤ 1`).
* **`isFaceStructured_halfDisc_interval_cobordism`**: for EVERY sc⁺-section `S` over
  `[0, 1] × H` with `F = f̃ + S` proper and in general position, `S_F` is face-structured
  (`isFaceStructured_interval_cobordism`; no assumption on the shape of `S_F`).
* **`theorem_6_6_18_boundaryIntegral_interval_halfDisc`**:
  `theorem_6_6_18_boundaryIntegral_interval` for `S = 0`: the corner structures, the
  orientations of Theorem 6.6.18 and the signed formula
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + Σ_{lateral faces} ∫ …`, with every
  hypothesis discharged.  `S_F = [0, 1] × S_f`, both ends contain the boundary point `(0, 1)`
  (`topPoint_mem_ends_halfDisc`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Manifold
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr UnitCube MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local instance instParacompactIvHF : ParacompactSpace ((Fin 1 → unitInterval) × H 1) :=
  MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)

local instance instParacompactIvPullbackF :
    ParacompactSpace (pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1)) :=
  paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
    ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)

/-- `H = [0, ∞) × ℝ` is tame. -/
theorem isTame_basePoly_one : (basePoly 1).IsTame := isTame_halfSEP 1 1

/-- `H = [0, ∞) × ℝ` admits sc-smooth bump functions. -/
theorem admitsBumpFunctions_basePoly_one : (basePoly 1).AdmitsBumpFunctions :=
  admitsBumpFunctions_halfSEP 1 1

/-- **`H = [0, ∞) × ℝ` is face-structured**: `d_H ≤ 1`, with the one face `\{0\} × ℝ`. -/
theorem isFaceStructured_basePoly_one : (basePoly 1).IsFaceStructured :=
  isFaceStructured_of_degIndex_le_one isTame_basePoly_one fun x => by
    rw [degIndex_basePoly_one]; split_ifs <;> norm_num

/-- **Point A on the half-disc, from the general statement**: for every sc⁺-section `S` over
`[0, 1] × H` with `F = f̃ + S` proper and in general position, `S_F` is face-structured. -/
theorem isFaceStructured_halfDisc_interval_cobordism
    {S : (Fin 1 → unitInterval) × H 1 →
      pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1)}
    (hS : (ivBundle (bundle 1 1)).IsScPlusSection S)
    (hP : (ivBundle (bundle 1 1)).IsProper (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
      (cubeLift (n := 1) (graphSection halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1)
      S))
    (hgp : ∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd) (sectionAdd (pullbackProj (proj 1 1)
        Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
          isScFredholmSectionTame_halfDisc.isScSmooth.1) S) z →
      (ivBundle (bundle 1 1)).IsGeneralPositionGerm (sectionAdd (pullbackProj (proj 1 1)
        Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
          isScFredholmSectionTame_halfDisc.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSmoothSubmanifold
      (solutionSet (pullbackProj (proj 1 1) Prod.snd) (sectionAdd (pullbackProj (proj 1 1)
        Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
          isScFredholmSectionTame_halfDisc.isScSmooth.1) S)))
    [ParacompactSpace (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd) (cubeLift (n := 1) (graphSection
        halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1) S))] :
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured :=
  isFaceStructured_interval_cobordism isTame_basePoly_one isFaceStructured_basePoly_one
    isScFredholmSectionTame_halfDisc hS hP hgp hSm

set_option quotPrecheck false in
local notation "SFg" => solutionSet (pullbackProj (proj 1 1) Prod.snd)
  (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
    (cubeLift (n := 1) (graphSection halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1)
    halfDiscZeroLift)

set_option quotPrecheck false in
local notation "SEg" b => solutionSet (proj 1 1)
  (sectionAdd (proj 1 1) (graphSection halfDiscMap) (prodSlice halfDiscZeroLift (ivEnd b)))

local instance instParacompactSFg : ParacompactSpace SFg :=
  ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype _

local instance instParacompactSEg (b : Bool) : ParacompactSpace (SEg b) :=
  (basePoly 1).paracompactSpace_subtype _

/-- **The ends of the half-disc cobordism meet `∂H`**: `(0, 1) ∈ S_{F_b}` for `b ∈ \{0, 1\}`. -/
theorem topPoint_mem_ends_halfDisc (b : Bool) : topPoint ∈ SEg b :=
  isZeroAt_slice_of_isZeroAt isScFredholmSectionTame_halfDisc halfDiscZeroLift_spec.1
    (halfDiscZeroLift_spec.2.2.2.2.2 (ivEnd b))

/-- **`theorem_6_6_18_boundaryIntegral_interval` on the half-disc** (`S = 0`, index `1`): every
hypothesis is discharged; the face-structuredness of `S_F` comes from the general statement. -/
theorem theorem_6_6_18_boundaryIntegral_interval_halfDisc :
    ∃ (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSmoothSubmanifold SFg)
      (hSt : ∀ b, (basePoly 1).IsSmoothSubmanifold (SEg b))
      (hcs : ∀ b, (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).HasCornerStructureOfDim 1)
      (hcs' : (MPolyfold.subPolyfold hSm.isSubMPolyfold).HasCornerStructureOfDim (1 + 1)),
      letI : ∀ b, ChartedSpace (EuclideanQuadrant 1) (SEg b) := fun b =>
        (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b)
      letI : ChartedSpace (EuclideanQuadrant (1 + 1)) SFg :=
        (MPolyfold.subPolyfold hSm.isSubMPolyfold).cornerChartedSpace hcs'
      ∃ (oS : TangentOrientation (𝓠 (1 + 1)) SFg (1 + 1))
        (o₀ : TangentOrientation (𝓠 1) (SEg false) 1)
        (o₁ : TangentOrientation (𝓠 1) (SEg true) 1),
        oS.IsContinuous (𝓠 (1 + 1)) ∞ ∧
        IsIntervalCobordismOrientation isTame_basePoly_one admitsBumpFunctions_basePoly_one
          isScFredholmSectionTame_halfDisc halfDiscOrientation halfDiscZeroLift_spec.1
          halfDiscZeroLift_spec.2.2.1 oS ∧
        o₀.IsContinuous (𝓠 1) ∞ ∧
        IsIntervalEndOrientation isScFredholmSectionTame_halfDisc halfDiscOrientation
          halfDiscZeroLift_spec.1 (ivEnd false)
          (ivEndLinSurj isScFredholmSectionTame_halfDisc halfDiscZeroLift_spec.1
            halfDiscZeroLift_spec.2.2.1 false) o₀ ∧
        o₁.IsContinuous (𝓠 1) ∞ ∧
        IsIntervalEndOrientation isScFredholmSectionTame_halfDisc halfDiscOrientation
          halfDiscZeroLift_spec.1 (ivEnd true)
          (ivEndLinSurj isScFredholmSectionTame_halfDisc halfDiscZeroLift_spec.1
            halfDiscZeroLift_spec.2.2.1 true) o₁ ∧
        ∀ α : (BundledMPolyfold.of (basePoly 1)).formsInfty 1,
          haveI := isManifold_of_eq hcs' rfl
          haveI : CompactSpace SFg := isCompact_iff_compactSpace.1 halfDiscZeroLift_spec.2.1.1
          haveI : Finite (Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold)) := finite_faces hcs'
          letI : Fintype (LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            fun b => sliceInclusion isScFredholmSectionTame_halfDisc.isScSmooth.1
              halfDiscZeroLift_spec.1.1 (ivEnd b)) := Fintype.ofFinite _
          letI : ∀ a : Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold),
            ChartedSpace (EuclideanQuadrant 1) a.1 := fun a =>
              faceChartedSpace hcs' (isFaceStructured_halfDisc_interval_cobordism
                halfDiscZeroLift_spec.1 halfDiscZeroLift_spec.2.1 halfDiscZeroLift_spec.2.2.1
                hSm) a.2
          ManifoldForm.boundaryIntegral oS (formsInftyRestrict 1 hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap (basePoly 1)) 1 α)) =
            ManifoldForm.integral o₁ (formsInftyRestrict 1 (hcs true) α) -
              ManifoldForm.integral o₀ (formsInftyRestrict 1 (hcs false) α) +
              ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
                  (fun b => sliceInclusion isScFredholmSectionTame_halfDisc.isScSmooth.1
                    halfDiscZeroLift_spec.1.1 (ivEnd b)),
                ManifoldForm.integral (faceOrientation hcs'
                    (isFaceStructured_halfDisc_interval_cobordism halfDiscZeroLift_spec.1
                      halfDiscZeroLift_spec.2.1 halfDiscZeroLift_spec.2.2.1 hSm) oS rfl a.1)
                  (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict 1 hcs'
                    (BundledMPolyfold.formsInftyPullback (ivPrScMap (basePoly 1)) 1 α))) :=
  theorem_6_6_18_boundaryIntegral_interval isTame_basePoly_one isFaceStructured_basePoly_one
    admitsBumpFunctions_basePoly_one isScFredholmSectionTame_halfDisc halfDiscOrientation
    halfDiscZeroLift_spec.1 halfDiscZeroLift_spec.2.1 halfDiscZeroLift_spec.2.2.1
    (k := 1) (fun x _ => isIndexAt_halfDisc x)

end HalfSpaceBundle

end Polyfold
