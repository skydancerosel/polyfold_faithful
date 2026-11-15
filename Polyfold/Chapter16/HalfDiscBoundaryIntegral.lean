import Polyfold.Chapter16.HalfDiscCobordismFaces
import Polyfold.Chapter9.IntervalEndSigns

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
Remark 6.6.19 and the proof of **Theorem 6.7.1**, on the half-disc example of
`HalfDiscIntervalCobordism.lean`.

# Stokes' theorem on the cobordism `[0, 1] × S_f` over `[0, 1] × H`

## The text, paraphrased

(Proof of Theorem 6.7.1, p. 278) For the oriented cobordism `S_F ⊆ [0, 1] × X` and
`α ∈ Ω^k_∞(X)`, Stokes' theorem gives
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + (the integral over the part of ∂S_F
over [0, 1] × ∂X)`, the end `t = 1` with the sign `+` and the end `t = 0` with the sign `−`.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

`H = [0, ∞) × ℝ` (`∂H ≠ ∅`), the bundle `H × ℝ → H` (fibres `ℝ`),
`f(a, y) = ((a, y), a² + y² − 1)` with the orientation `halfDiscOrientation`, and the
sc⁺-section `halfDiscZeroLift = 0` over `[0, 1] × H`, so that `S_F = [0, 1] × S_f`.

* `halfDiscZeroLift_spec`: `F = f̃ + 0` is sc⁺-perturbed, proper, in general position, of index
  `2`, with `S_F = [0, 1] × S_f`.
* **`boundaryIntegral_interval_cobordism_halfDisc`**: an instance of
  `boundaryIntegral_interval_cobordism_ends` with every hypothesis discharged: `S_F` and the
  ends `S_{F_0}`, `S_{F_1}` are smooth submanifolds with corner structures of dimensions `2` and
  `1`; the boundary point `(0, 1)` of `H` lies on both ends; `S_F` is face-structured with the
  four faces `\{0\} × S_f`, `\{1\} × S_f`, `[0, 1] × \{(0, ∓1)\}`; the orientations of
  `theorem_6_6_18_oriented_interval` and `theorem_6_6_18_oriented_end` exist, and for every
  `α ∈ Ω¹_∞(H)`,
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + Σ_{lateral faces} ∫ …`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Manifold
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open StrongBundle StrongRetr UnitCube MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local instance instParacompactIvH' : ParacompactSpace ((Fin 1 → unitInterval) × H 1) :=
  MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)

local instance instParacompactIvPullback' :
    ParacompactSpace (pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1)) :=
  paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
    ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)

/-- `f(a, y) = ((a, y), a² + y² − 1)` is a tame sc-Fredholm section. -/
theorem isScFredholmSectionTame_halfDisc :
    (bundle 1 1).IsScFredholmSectionTame (graphSection halfDiscMap) :=
  isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap

/-- **The sc⁺-section `S = 0` over `[0, 1] × H`**: the constant lift of the zero section. -/
def halfDiscZeroLift : (Fin 1 → unitInterval) × H 1 →
    pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1) :=
  cubeLift (n := 1) (fiberZero (proj 1 1))
    (isScPlusSection_fiberZero : (bundle 1 1).IsScPlusSection (fiberZero (proj 1 1))).1

set_option quotPrecheck false in
local notation "SFh" => solutionSet (pullbackProj (proj 1 1) Prod.snd)
  (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
    (cubeLift (n := 1) (graphSection halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1)
    halfDiscZeroLift)

set_option quotPrecheck false in
local notation "SEh" b => solutionSet (proj 1 1)
  (sectionAdd (proj 1 1) (graphSection halfDiscMap) (prodSlice halfDiscZeroLift (ivEnd b)))

local instance instParacompactSFh : ParacompactSpace SFh :=
  ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype _

local instance instParacompactSEh (b : Bool) : ParacompactSpace (SEh b) :=
  (basePoly 1).paracompactSpace_subtype _

/-- **`F = f̃ + 0` over `[0, 1] × H`** (`constant_cobordism`): `0` is sc⁺, `F` is proper, in
general position at every zero, of index `2`, and `S_F = [0, 1] × S_f`; the corner points
`(t, (0, 1))` are zeros of `F`. -/
theorem halfDiscZeroLift_spec :
    (ivBundle (bundle 1 1)).IsScPlusSection halfDiscZeroLift ∧
      (ivBundle (bundle 1 1)).IsProper (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1)
        halfDiscZeroLift) ∧
      (∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd) (sectionAdd (pullbackProj (proj 1 1)
          Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
            isScFredholmSectionTame_halfDisc.isScSmooth.1) halfDiscZeroLift) z →
        (ivBundle (bundle 1 1)).IsGeneralPositionGerm (sectionAdd (pullbackProj (proj 1 1)
          Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
            isScFredholmSectionTame_halfDisc.isScSmooth.1) halfDiscZeroLift) z) ∧
      (∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd) (sectionAdd (pullbackProj (proj 1 1)
          Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
            isScFredholmSectionTame_halfDisc.isScSmooth.1) halfDiscZeroLift) z →
        (ivBundle (bundle 1 1)).IsLinOfIndex (sectionAdd (pullbackProj (proj 1 1)
          Prod.snd) (cubeLift (n := 1) (graphSection halfDiscMap)
            isScFredholmSectionTame_halfDisc.isScSmooth.1) halfDiscZeroLift) z (1 + 1 : ℕ)) ∧
      SFh = univ ×ˢ solutionSet (proj 1 1) (graphSection halfDiscMap) ∧
      ∀ t : Fin 1 → unitInterval, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
        (sectionAdd (pullbackProj (proj 1 1) Prod.snd) (cubeLift (n := 1) (graphSection
          halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1) halfDiscZeroLift)
        (t, topPoint) := by
  have hbump : (basePoly 1).AdmitsBumpFunctions := admitsBumpFunctions_halfSEP 1 1
  have hf := isScFredholmSectionTame_halfDisc
  have hsec : IsSection (proj 1 1) (graphSection halfDiscMap) := hf.isScSmooth.1
  have hadd : sectionAdd (proj 1 1) (graphSection halfDiscMap) (fiberZero (proj 1 1)) =
      graphSection halfDiscMap := sectionAdd_fiberZero hsec
  have hk : ∀ x ∈ (basePoly 1).smoothSet,
      (bundle 1 1).IsIndexAt (graphSection halfDiscMap) x (1 : ℕ) := fun x _ =>
    isIndexAt_halfDisc x
  have hs0 : (bundle 1 1).IsScPlusSection (fiberZero (proj 1 1)) := isScPlusSection_fiberZero
  obtain ⟨hSp, hP, hgp, hidx, hsol⟩ := constant_cobordism hbump hf hs0
    (by rw [hadd]; exact isCompact_solutionSet_halfDisc)
    (fun x hx => by
      rw [hadd] at hx ⊢
      exact isGeneralPositionGerm_halfDisc hx) hk
  have htop : IsZeroAt (proj 1 1) (sectionAdd (proj 1 1) (graphSection halfDiscMap)
      (fiberZero (proj 1 1))) topPoint := by
    rw [hadd]
    exact isZeroAt_graphSection_iff.2 halfDiscMap_topPoint
  refine ⟨hSp, hP, hgp, hidx, ?_, fun t => constant_cobordism_mem_ends hsec hs0.1 htop t⟩
  exact hsol.trans (by rw [hadd])

set_option maxHeartbeats 800000 in
-- the solution sets carry the structures of `theorem_6_6_18_solutionSet`, unfolded three times
/-- **Stokes' theorem on the cobordism `[0, 1] × S_f` with both ends** (an instance of
`boundaryIntegral_interval_cobordism_ends` with `∂X ≠ ∅` and non-zero fibres; not in the text):
for `H = [0, ∞) × ℝ`, `f(a, y) = ((a, y), a² + y² − 1)` with the orientation
`halfDiscOrientation` and `S = 0`, `F = f̃ + S`:
* `S_F ⊆ [0, 1] × H` and the ends `S_{F_b} ⊆ H`, `b ∈ \{0, 1\}`, are smooth submanifolds with
  corner structures of dimensions `2` and `1`, and the boundary point `(0, 1)` of `H` lies on
  both ends;
* `S_F` is face-structured, with the faces `\{0\} × S_f`, `\{1\} × S_f`, `[0, 1] × \{(0, −1)\}`
  and `[0, 1] × \{(0, 1)\}`;
* there are continuous orientations `oS` of `S_F` and `o_b` of `S_{F_b}` which are the
  orientations of `theorem_6_6_18_oriented_interval` and `theorem_6_6_18_oriented_end`;
* for every `α ∈ Ω¹_∞(H)`,
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + Σ_a ∫_a (pr₂^*α)|_{S_F}`, the sum over
  the faces of `S_F` other than the two ends. -/
theorem boundaryIntegral_interval_cobordism_halfDisc :
    ∃ (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSmoothSubmanifold SFh)
      (hSt : ∀ b, (basePoly 1).IsSmoothSubmanifold (SEh b))
      (hcs : ∀ b, (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).HasCornerStructureOfDim 1)
      (hcs' : (MPolyfold.subPolyfold hSm.isSubMPolyfold).HasCornerStructureOfDim (1 + 1))
      (hfs : (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured),
      (∀ b, topPoint ∈ SEh b) ∧
      (∀ F, (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFace F ↔
        F = {z | (z.1.1 0 : ℝ) = 0} ∨ F = {z | (z.1.1 0 : ℝ) = 1} ∨
          F = {z | (z.1.2 : Pm 1).2 0 = -1} ∨ F = {z | (z.1.2 : Pm 1).2 0 = 1}) ∧
      letI : ∀ b, ChartedSpace (EuclideanQuadrant 1) (SEh b) := fun b =>
        (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b)
      letI : ChartedSpace (EuclideanQuadrant (1 + 1)) SFh :=
        (MPolyfold.subPolyfold hSm.isSubMPolyfold).cornerChartedSpace hcs'
      ∃ (oS : TangentOrientation (𝓠 (1 + 1)) SFh (1 + 1))
        (o₀ : TangentOrientation (𝓠 1) (SEh false) 1)
        (o₁ : TangentOrientation (𝓠 1) (SEh true) 1),
        oS.IsContinuous (𝓠 (1 + 1)) ∞ ∧
        IsIntervalCobordismOrientation (show (basePoly 1).IsTame from isTame_halfSEP 1 1)
          (show (basePoly 1).AdmitsBumpFunctions from admitsBumpFunctions_halfSEP 1 1)
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
          haveI : CompactSpace SFh := isCompact_iff_compactSpace.1 halfDiscZeroLift_spec.2.1.1
          haveI : Finite (Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold)) := finite_faces hcs'
          letI : Fintype (LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            fun b => sliceInclusion isScFredholmSectionTame_halfDisc.isScSmooth.1
              halfDiscZeroLift_spec.1.1 (ivEnd b)) := Fintype.ofFinite _
          letI : ∀ a : Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold),
            ChartedSpace (EuclideanQuadrant 1) a.1 := fun a => faceChartedSpace hcs' hfs a.2
          ManifoldForm.boundaryIntegral oS (formsInftyRestrict 1 hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap (basePoly 1)) 1 α)) =
            ManifoldForm.integral o₁ (formsInftyRestrict 1 (hcs true) α) -
              ManifoldForm.integral o₀ (formsInftyRestrict 1 (hcs false) α) +
              ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
                  (fun b => sliceInclusion isScFredholmSectionTame_halfDisc.isScSmooth.1
                    halfDiscZeroLift_spec.1.1 (ivEnd b)),
                ManifoldForm.integral (faceOrientation hcs' hfs oS rfl a.1)
                  (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict 1 hcs'
                    (BundledMPolyfold.formsInftyPullback (ivPrScMap (basePoly 1)) 1 α))) := by
  have hX : (basePoly 1).IsTame := isTame_halfSEP 1 1
  have hbump : (basePoly 1).AdmitsBumpFunctions := admitsBumpFunctions_halfSEP 1 1
  have hf := isScFredholmSectionTame_halfDisc
  obtain ⟨hS, hP, hgp, hidx, hsol, hz⟩ := halfDiscZeroLift_spec
  have hk : ∀ x ∈ (basePoly 1).smoothSet,
      (bundle 1 1).IsIndexAt (graphSection halfDiscMap) x (1 : ℕ) := fun x _ =>
    isIndexAt_halfDisc x
  have hD := (theorem_6_6_18_solutionSet (prod_cube_isTame hX)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx
  have hcs' := hD.hasCornerStructureOfDim_of_tame (prod_cube_isTame hX)
    ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
      (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
      (prod_cube_isTame hX))
  have hEnd : ∀ b, ∃ hSt : (basePoly 1).IsSmoothSubmanifold (SEh b),
      (MPolyfold.subPolyfold hSt.isSubMPolyfold).HasCornerStructureOfDim 1 := fun b => by
    obtain ⟨hPt, hgpt, hidxt, -⟩ := theorem_6_6_18_oriented_end hX hbump hf halfDiscOrientation
      hS hP hgp hk (t := ivEnd b) (ivEnd_zero_or_one b)
    have hDt := (theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b)))
      hPt hgpt).isSubmanifoldOfDim (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b))) hidxt
    exact ⟨hDt.1, hDt.hasCornerStructureOfDim_of_tame hX
      ((theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b))) hPt
        hgpt).isGoodPositionAt hX)⟩
  choose hSt hcs using hEnd
  have hfs := isFaceStructured_halfDisc_cobordism hf hS hP hgp hD.1 hsol
  have hI := (theorem_6_6_18_oriented_interval hX hbump hf halfDiscOrientation hS hP hgp
    hidx).2.2
  have hOr : ∀ b, letI := (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b)
      ∃ oE : TangentOrientation (𝓠 1) (SEh b) 1, oE.IsContinuous (𝓠 1) ∞ ∧
        IsIntervalEndOrientation hf halfDiscOrientation hS (ivEnd b) (ivEndLinSurj hf hS hgp b)
          oE := fun b => by
    obtain ⟨hPt, hgpt, hidxt, -, -, oE, hoE, hoEs⟩ := theorem_6_6_18_oriented_end hX hbump hf
      halfDiscOrientation hS hP hgp hk (t := ivEnd b) (ivEnd_zero_or_one b)
    exact ⟨oE, hoE, hoEs⟩
  have h₀ := hOr false
  have h₁ := hOr true
  refine ⟨hD.1, hSt, hcs, hcs', hfs, fun b => isZeroAt_slice_of_isZeroAt hf hS (hz (ivEnd b)),
    isFace_halfDisc_cobordism_iff hf hS hP hgp hD.1 hsol, hI.choose, h₀.choose, h₁.choose,
    hI.choose_spec.1, hI.choose_spec.2,
    h₀.choose_spec.1, h₀.choose_spec.2, h₁.choose_spec.1, h₁.choose_spec.2, fun α => ?_⟩
  exact boundaryIntegral_interval_cobordism_ends
    (inst := fun b => (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b))
    (inst' := (MPolyfold.subPolyfold hD.1.isSubMPolyfold).cornerChartedSpace hcs')
    hX hbump hf halfDiscOrientation hS hP hgp hD.1 hSt hcs (fun b => rfl) hcs' rfl hfs hI.choose
    hI.choose_spec.1 hI.choose_spec.2 h₀.choose h₁.choose h₀.choose_spec.1
    h₁.choose_spec.1 h₀.choose_spec.2 h₁.choose_spec.2 α

end HalfSpaceBundle

end Polyfold
