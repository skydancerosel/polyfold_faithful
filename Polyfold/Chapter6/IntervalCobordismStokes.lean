import Polyfold.Chapter6.IntervalEndManifolds

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.4, p. 199
(**Theorem 4.4.7**; preprint Theorem 4.28) and the proof of **Theorem 6.7.1**, p. 278: Stokes'
theorem on the cobordism `S_F ⊆ [0, 1] × X`, `F = f̃ + S`.

# Stokes' theorem on the cobordism over `[0, 1] × X`

## What is formalized

* `MPolyfold.boundaryIntegral_formsInftyRestrict_of_closed`: on a compact sub-M-polyfold `S`
  with a corner structure of dimension `n + 1` and a continuous orientation, `∫_{∂S} ω|_S = 0`
  for a closed `ω ∈ Ωⁿ_∞(X)`.
* `MPolyfold.boundaryIntegral_formsInftyRestrict_pullback_of_closed`: the same for the pull-back
  `g^*ω` of a closed form along an sc-smooth map `g`.
* `ivPrScMap`: the projection `pr₂ : [0, 1] × X → X` as an sc-smooth map.
* **`stokes_interval_cobordism`**: for `F = f̃ + S` over `[0, 1] × X` proper, in general position
  at every zero and of index `k + 1`, with the manifold structure of
  `theorem_6_6_18_oriented_interval` and any continuous tangent orientation `oS` of `S_F`:
  `∫_{S_F} (dω)|_{S_F} = ∫_{∂S_F} ω|_{S_F}` for `ω ∈ Ωᵏ_∞([0, 1] × X)`, and
  `∫_{∂S_F} (pr₂^*ω)|_{S_F} = 0` for a closed `ω ∈ Ωᵏ_∞(X)`.

## Not formalized

The boundary integral `∫_{∂S_F}` is that of the Mathlib manifold with corners `S_F`.  Its
decomposition into the integrals over `\{1\} × S_{F_1}`, `\{0\} × S_{F_0}` and over
`S_F ∩ ([0, 1] × ∂X)` is not proved here.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

universe u v w

open StrongRetr StrongBundle UnitCube MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace MPolyfold

section ClosedForms

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] {hY : PX.IsSubMPolyfold S} {n : ℕ}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1)}
  [inst : ChartedSpace (EuclideanQuadrant (n + 1)) S]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **The boundary integral of a closed form vanishes** (2021 Theorem 4.4.7, p. 199): for a
compact `S ⊆ X` with a corner structure of dimension `n + 1`, a continuous tangent orientation
`o` and `ω ∈ Ωⁿ_∞(X)` with `dω = 0`, `∫_{∂S} ω|_S = 0`. -/
theorem boundaryIntegral_formsInftyRestrict_of_closed [CompactSpace S]
    {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)} (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (ω : (BundledMPolyfold.of PX).formsInfty n)
    (hω : (BundledMPolyfold.of PX).formsInftyD n ω = 0) :
    haveI := isManifold_of_eq hcs hch
    ManifoldForm.boundaryIntegral o (formsInftyRestrict n hcs ω) = 0 := by
  have := isManifold_of_eq hcs hch
  rw [← stokes_formsInftyRestrict hch ho ω, hω, map_zero]
  have h0 : IsCompact (ManifoldForm.tsupport (0 : ManifoldForm (𝓠 (n + 1)) S (n + 1))) := by
    have : ManifoldForm.tsupport (0 : ManifoldForm (𝓠 (n + 1)) S (n + 1)) = ∅ := by
      simp [ManifoldForm.tsupport, ManifoldForm.support]
    rw [this]; exact isCompact_empty
  have h := ManifoldForm.integral_add ho (ManifoldForm.contMDiffForm_zero_form 0)
    (ManifoldForm.contMDiffForm_zero_form 0) h0 h0 (o := o)
  rw [add_zero] at h
  linarith

/-- **The boundary integral of the pull-back of a closed form vanishes**: for an sc-smooth map
`g : X → Z` and `ω ∈ Ωⁿ_∞(Z)` with `dω = 0`, `∫_{∂S} (g^*ω)|_S = 0`
(`d g^* = g^* d`, `formsInftyD_comp_formsInftyPullback`). -/
theorem boundaryIntegral_formsInftyRestrict_pullback_of_closed [CompactSpace S]
    {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)} (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {Bd : BundledMPolyfold.{w}} (g : ScMap (BundledMPolyfold.of PX).P Bd.P)
    (ω : Bd.formsInfty n) (hω : Bd.formsInftyD n ω = 0) :
    haveI := isManifold_of_eq hcs hch
    ManifoldForm.boundaryIntegral o
      (formsInftyRestrict n hcs (BundledMPolyfold.formsInftyPullback g n ω)) = 0 := by
  refine boundaryIntegral_formsInftyRestrict_of_closed hch ho _ ?_
  have h := LinearMap.congr_fun
    (BundledMPolyfold.formsInftyD_comp_formsInftyPullback (A := BundledMPolyfold.of PX) g
      (k := n)) ω
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hω, map_zero] at h
  exact h

end ClosedForms

end MPolyfold

section IvStokes

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

variable (PX) in
/-- The projection `pr₂ : [0, 1] × X → X`, `(t, x) ↦ x`, as an `ScMap`. -/
abbrev ivPrScMap :
    ScMap (BundledMPolyfold.of ((cubePolyfold 1).prod PX)).P (BundledMPolyfold.of PX).P :=
  ⟨Prod.snd, MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX⟩

/-- **Stokes' theorem on the cobordism over `[0, 1] × X`** (2021 Theorem 4.4.7, p. 199, and the
proof of Theorem 6.7.1, p. 278): let `X` be tame, `f` a tame sc-Fredholm section and `S` an
sc⁺-section over `[0, 1] × X` such that `F = f̃ + S` is proper, in general position at every zero
and of index `k + 1`.  With the structure of a compact manifold with boundary and corners on
`S_F` of `theorem_6_6_18_oriented_interval` and any continuous tangent orientation `oS` (for
instance the one given by `e ∧ o`):
* `∫_{S_F} (dω)|_{S_F} = ∫_{∂S_F} ω|_{S_F}` for every `ω ∈ Ωᵏ_∞([0, 1] × X)`;
* `∫_{∂S_F} (pr₂^*ω)|_{S_F} = 0` for every closed `ω ∈ Ωᵏ_∞(X)`. -/
theorem stokes_interval_cobordism (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    {k : ℕ}
    (hidx : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsLinOfIndex
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z
        (k + 1 : ℕ)) :
    letI := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
      (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    letI := (MPolyfold.subPolyfold ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
      (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
      (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx).1.isSubMPolyfold).cornerChartedSpace
      (((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
        (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
        (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx).hasCornerStructureOfDim_of_tame
        (prod_cube_isTame hX) ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
          (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
          (prod_cube_isTame hX)))
    haveI := isManifold_of_eq (((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
        (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
        (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx).hasCornerStructureOfDim_of_tame
        (prod_cube_isTame hX) ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
          (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
          (prod_cube_isTame hX))) rfl
    ∀ oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1),
      oS.IsContinuous (𝓠 (k + 1)) ∞ →
      (∀ ω : (BundledMPolyfold.of ((cubePolyfold 1).prod PX)).formsInfty k,
        ManifoldForm.integral oS (formsInftyRestrict (k + 1)
            (((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
              (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
              (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS)
              hidx).hasCornerStructureOfDim_of_tame
              (prod_cube_isTame hX) ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
                (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
                (prod_cube_isTame hX)))
            ((BundledMPolyfold.of ((cubePolyfold 1).prod PX)).formsInftyD k ω)) =
          ManifoldForm.boundaryIntegral oS (formsInftyRestrict k
            (((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
              (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
              (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS)
              hidx).hasCornerStructureOfDim_of_tame
              (prod_cube_isTame hX) ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
                (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
                (prod_cube_isTame hX))) ω)) ∧
      ∀ ω : (BundledMPolyfold.of PX).formsInfty k,
        (BundledMPolyfold.of PX).formsInftyD k ω = 0 →
          ManifoldForm.boundaryIntegral oS (formsInftyRestrict k
            (((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
              (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
              (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS)
              hidx).hasCornerStructureOfDim_of_tame
              (prod_cube_isTame hX) ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
                (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
                (prod_cube_isTame hX)))
            (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k ω)) = 0 := by
  let := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
    (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
  have h := theorem_6_6_18_solutionSet (prod_cube_isTame hX)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp
  have hcs := (h.isSubmanifoldOfDim (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS)
    hidx).hasCornerStructureOfDim_of_tame (prod_cube_isTame hX)
    (h.isGoodPositionAt (prod_cube_isTame hX))
  let := (MPolyfold.subPolyfold (h.isSubmanifoldOfDim
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx).1.isSubMPolyfold).cornerChartedSpace
    hcs
  have : CompactSpace ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    isCompact_iff_compactSpace.1 hP.1
  intro oS hoS
  exact ⟨fun ω => stokes_formsInftyRestrict (hcs := hcs) rfl hoS ω, fun ω hω =>
    boundaryIntegral_formsInftyRestrict_pullback_of_closed (hcs := hcs) rfl hoS
      (ivPrScMap PX) ω hω⟩

end IvStokes

end Polyfold
