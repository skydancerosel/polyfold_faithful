import Polyfold.Chapter9.EndFaceChartPairs
import Polyfold.Chapter9.IntervalEndSigns
import Polyfold.Chapter6.IntervalCobordismExistence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Remark 6.6.19 and the
proof of Theorem 6.7.1 (pp. 276–278), with Theorem 4.4.7 (p. 199).

# The signed boundary formula of the cobordism without faces

For `F = f̃ + S` proper and in general position over `[0, 1] × X`, `X` tame (not necessarily
face-structured), the proof of Theorem 6.7.1 decomposes `∂S_F = S_0 ∪ S_1 ∪ S̃` with
`S̃ ⊆ ∂X × (0, 1)` and reads
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + ∫_{S̃} (pr₂^*α)|_{S̃}`.
The last term is the integral over the part of `∂S_F` with `0 < t < 1`; it is the limit of
`∫_{∂S_F} (χₘ ∘ t) (pr₂^*α)|_{S_F}` for cut-offs `χₘ` of `[0, 1]` vanishing at `0` and `1` and
tending to `1` on `(0, 1)` (`tendsto_boundaryIntegral_levels`).  No face structure of `S_F` or of
`X` is used.

## What is formalized

* `exists_localInverse_sliceInclusion`: near every point of `range j_t`, `j_t : S_{F_t} → S_F`
  has the `C^∞` left inverse `(t, x) ↦ r(x)`, `r` a retraction onto `S_{F_t}`
  (Proposition 2.3.19 (2)).
* **`boundaryIntegral_interval_cobordism_lateral`**: for the orientations of Theorem 6.6.18 and
  Remark 6.6.19, `∫_{∂S_F} (χₘ ∘ t) ω → ∫_{∂S_F} ω − (∫_{S_{F_1}} α − ∫_{S_{F_0}} α)`, i.e.
  `∫_{∂S_F} ω = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + lim_m ∫_{∂S_F} (χₘ ∘ t) ω`, for
  `ω = (pr₂^*α)|_{S_F}`.
* **`theorem_6_6_18_boundaryIntegral_interval_lateral`**: the same with the corner structures and
  orientations of Theorem 6.6.18 produced, for `X` tame with sc-smooth bump functions.
-/

open Set Filter Topology Manifold Module Function
open scoped ContDiff

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

section Lateral

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

omit [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **Local left inverses of `j_t`** (Proposition 2.3.19 (2)): near `j_t(p)`, the map
`(t', x) ↦ r(x)`, `r` a retraction of a neighbourhood of `p` in `X` onto `S_{F_t}`, is a `C^∞`
left inverse of `j_t` (sc-smooth, `contMDiffOn_of_isScSmoothOn`). -/
theorem exists_localInverse_sliceInclusion (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)))
    (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S t))))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))]
    [ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S t)))] {k : ℕ}
    (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim k)
    [inst : ChartedSpace (EuclideanQuadrant k) (solutionSet P (sectionAdd P f (prodSlice S t)))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (k + 1))
    [inst' : ChartedSpace (EuclideanQuadrant (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs')
    (p : solutionSet P (sectionAdd P f (prodSlice S t))) :
    ∃ (U : Set (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)))
      (g : solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) →
          solutionSet P (sectionAdd P f (prodSlice S t))),
      IsOpen U ∧ sliceInclusion hf hS t p ∈ U ∧ ContMDiffOn (𝓠 (k + 1)) (𝓠 k) ∞ g U ∧
        ∀ q, sliceInclusion hf hS t q ∈ U → g (sliceInclusion hf hS t q) = q := by
  set d := hSt.data p.2
  have hsnd : (MPolyfold.subPolyfold hSm).IsScSmoothMap PX
      (fun z : solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) => z.1.2) :=
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX).comp (subPolyfold_inclusion_isScSmooth hSm)
  have hUo : IsOpen ((fun z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) => z.1.2) ⁻¹' d.V) :=
    d.isOpen.preimage (continuous_snd.comp continuous_subtype_val)
  refine ⟨_, fun z => d.retractInto p z.1.2, hUo, hSt.mem_data_V p.2, ?_,
    fun q hq => Subtype.ext ?_⟩
  · exact contMDiffOn_of_isScSmoothOn hcs' hch' hcs hch
      ((subPolyfold_retraction_isScSmooth hSt d p).comp
        (IsScSmoothOn.mono hsnd hUo (subset_univ _)) fun _ hw => hw)
  · have hq' : q.1 ∈ d.V := hq
    change (d.retractInto p q.1).1 = q.1
    rw [SubData.retractInto_val d p hq']
    exact d.apply_eq_self ⟨q.2, hq'⟩

/-- **The signed boundary formula of the cobordism `S_F`, without faces** (2021, Remark 6.6.19
and the proof of Theorem 6.7.1, p. 278): for `F = f̃ + S` proper and in general position over
`[0, 1] × X`, `X` tame, `S_F` and its ends carrying corner structures of dimensions `k + 1` and
`k`, the orientation `oS = e ∧ o` of `S_F` (Remark 6.6.19), the orientations `o_0`, `o_1` of the
ends (Theorem 6.6.18), `α ∈ Ωᵏ_∞(X)`, `ω = (pr₂^*α)|_{S_F}` and cut-offs `χₘ` of `[0, 1]`
(`|χₘ| ≤ 1`, `χₘ(0) = χₘ(1) = 0`, `χₘ → 1` on `(0, 1)`):
`∫_{∂S_F} (χₘ ∘ t) ω → ∫_{∂S_F} ω − (∫_{S_{F_1}} α − ∫_{S_{F_0}} α)`.  The limit is the integral
of `ω` over the part of `∂S_F` with `0 < t < 1`, the lateral term of the book; no face structure
of `S_F` or of `X` is assumed. -/
theorem boundaryIntegral_interval_cobordism_lateral (hX : PX.IsTame)
    (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSmoothSubmanifold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hSt : ∀ b, PX.IsSmoothSubmanifold
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))))
    [∀ b, ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))))] {k : ℕ}
    (hcs : ∀ b, (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).HasCornerStructureOfDim k)
    [inst : ∀ b, ChartedSpace (EuclideanQuadrant k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))))]
    (hch : ∀ b, inst b = (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b))
    (hcs' : (MPolyfold.subPolyfold hSm.isSubMPolyfold).HasCornerStructureOfDim (k + 1))
    [inst' : ChartedSpace (EuclideanQuadrant (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm.isSubMPolyfold).cornerChartedSpace hcs')
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : oS.IsContinuous (𝓠 (k + 1)) ∞)
    (hoSs : IsIntervalCobordismOrientation hX hbump hf o hS hgp oS)
    (o₀ : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false)))) k)
    (o₁ : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true)))) k)
    (ho₀ : o₀.IsContinuous (𝓠 k) ∞) (ho₁ : o₁.IsContinuous (𝓠 k) ∞)
    (ho₀s : IsIntervalEndOrientation hf o hS (ivEnd false) (ivEndLinSurj hf hS hgp false) o₀)
    (ho₁s : IsIntervalEndOrientation hf o hS (ivEnd true) (ivEndLinSurj hf hS hgp true) o₁)
    (α : (BundledMPolyfold.of PX).formsInfty k) {χ : ℕ → ℝ → ℝ}
    (hχs : ∀ m, ContDiff ℝ ∞ (χ m)) (hχ1 : ∀ m t, |χ m t| ≤ 1) (hχ0 : ∀ m, χ m 0 = 0)
    (hχ1' : ∀ m, χ m 1 = 0) (hχ : ∀ t ∈ Ioo (0 : ℝ) 1, Tendsto (fun m => χ m t) atTop (𝓝 1)) :
    haveI := isManifold_of_eq hcs' hch'
    Tendsto (fun m => ManifoldForm.boundaryIntegral oS (ManifoldForm.smulFun
        (fun z => χ m ((z.1.1 0 : unitInterval) : ℝ)) (formsInftyRestrict k hcs'
          (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)))) atTop
      (𝓝 (ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
          (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) -
        (ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
          ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α)))) := by
  have : IsManifold (𝓠 (k + 1)) ∞ (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    isManifold_of_eq hcs' hch'
  have : ∀ b, IsManifold (𝓠 k) ∞ (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) :=
    fun b => isManifold_of_eq (hcs b) (hch b)
  have : CompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    isCompact_iff_compactSpace.1 hP.1
  have : ∀ b, CompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) := fun b =>
    isCompact_iff_compactSpace.1 (isCompact_solutionSet_slice hf.isScSmooth.1 hS.1 hP.1 (ivEnd b))
  let oN : ∀ b, TangentOrientation (𝓠 k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) k := fun b =>
    match b with
    | false => -o₀
    | true => o₁
  have hoN : ∀ b, IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) oS
      (oN b) := by
    intro b
    cases b
    · exact isInducedOrientation_interval_end_zero hX hbump hf o hS hgp hSm.isSubMPolyfold
        (hSt false).isSubMPolyfold (hcs false) (hch false) hcs' hch' oS hoSs o₀ ho₀s
    · exact isInducedOrientation_interval_end_one hX hbump hf o hS hgp hSm.isSubMPolyfold
        (hSt true).isSubMPolyfold (hcs true) (hch true) hcs' hch' oS hoSs o₁ ho₁s
  have hoNc : ∀ b, (oN b).IsContinuous (𝓠 k) ∞ := by
    intro b
    cases b
    exacts [ho₀.neg, ho₁]
  have hτ : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ (fun z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
        ((z.1.1 0 : unitInterval) : ℝ)) :=
    contMDiff_of_isScSmoothMap_real hcs' hch'
      (((isScSmoothMap_cube_real_of_contDiff (n := 1) (g := fun y => y 0)
        (contDiff_apply ℝ ℝ 0)).comp (MPolyfold.isScSmoothMap_fst (cubePolyfold 1) PX)).comp
        (subPolyfold_inclusion_isScSmooth hSm.isSubMPolyfold))
  have hrange : ∀ b, range (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) =
      (fun z : solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
          ((z.1.1 0 : unitInterval) : ℝ)) ⁻¹' {endLevel b} := by
    intro b
    rw [range_sliceInclusion]
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      rw [h]
      cases b <;> simp [ivEnd, endLevel]
    · intro h
      funext i
      rw [Subsingleton.elim i 0]
      apply Subtype.ext
      rw [h]
      cases b <;> simp [ivEnd, endLevel]
  have hadapt : ∀ b, IsAdaptedEnd k (fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) b :=
    fun b => isAdaptedEnd_of_localInverse
      (PN := fun b => MPolyfold.subPolyfold (hSt b).isSubMPolyfold) hcs' hch' b (hcs b)
      (isEmbedding_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b))
      (by
        rw [range_sliceInclusion]
        exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const)
      (contMDiff_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
        (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hch')
      (fun x => degIndex_interval_cobordism_end hX hf hS hP hgp hSm (ivEnd_zero_or_one b)
        (hSt b) x)
      (degIndex_eq_one_ends hX hf hS hP hgp hSm b)
      (exists_localInverse_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
        (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hch')
  have h := tendsto_boundaryIntegral_levels (o := oS)
    (j := fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) hoS
    (fun b => (isEmbedding_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)).continuous) hoN hoNc hτ
    (fun z => (z.1.1 0).2) hrange hadapt hχs hχ1 hχ0 hχ1' hχ
    ((contMDiffForm_formsInftyRestrict hch'
      (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)).of_le (by exact_mod_cast le_top))
  have hsum : ∑ b, ManifoldForm.integral (oN b) (restrictForm
      (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) (formsInftyRestrict k hcs'
        (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α))) =
      ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
        ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α) := by
    rw [Fintype.sum_bool]
    change ManifoldForm.integral o₁ _ + ManifoldForm.integral (-o₀) _ = _
    rw [restrictForm_sliceInclusion_pullback hf.isScSmooth.1 hS.1 (ivEnd true) hSm.isSubMPolyfold
        (hSt true).isSubMPolyfold (hcs true) (hch true) hcs' hch' α,
      restrictForm_sliceInclusion_pullback hf.isScSmooth.1 hS.1 (ivEnd false) hSm.isSubMPolyfold
        (hSt false).isSubMPolyfold (hcs false) (hch false) hcs' hch' α,
      ManifoldForm.integral_neg_orientation ho₀
        ((contMDiffForm_formsInftyRestrict (hch false) α).of_le zero_le)
        isClosed_closure.isCompact]
    ring
  rw [hsum] at h
  exact h

/-- **Stokes' theorem on the cobordism `S_F` with the orientations of Theorem 6.6.18, without
faces** (2021, Remark 6.6.19 and the proof of Theorem 6.7.1, pp. 276–278), for a tame `X` with
sc-smooth bump functions (not necessarily face-structured), a tame sc-Fredholm section `f` of
index `k` with orientation `o`, and `F = f̃ + S` proper and in general position over `[0, 1] × X`:
`S_F` and the ends `S_{F_b}` are smooth submanifolds with corner structures of dimensions `k + 1`
and `k`, with the continuous orientations `oS`, `o_b` of `theorem_6_6_18_oriented_interval` and
`theorem_6_6_18_oriented_end`, and for every `α ∈ Ωᵏ_∞(X)` and all cut-offs `χₘ` of `[0, 1]`,
`∫_{∂S_F} (χₘ ∘ t) ω → ∫_{∂S_F} ω − (∫_{S_{F_1}} α − ∫_{S_{F_0}} α)`, `ω = (pr₂^*α)|_{S_F}`
(`boundaryIntegral_interval_cobordism_lateral`). -/
theorem theorem_6_6_18_boundaryIntegral_interval_lateral (hX : PX.IsTame)
    (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    {k : ℕ} (hk : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x k)
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    [∀ b, ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))))] :
    ∃ (hSm : ((cubePolyfold 1).prod PX).IsSmoothSubmanifold (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
      (hSt : ∀ b, PX.IsSmoothSubmanifold
        (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))))
      (hcs : ∀ b, (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).HasCornerStructureOfDim k)
      (hcs' : (MPolyfold.subPolyfold hSm.isSubMPolyfold).HasCornerStructureOfDim (k + 1)),
      letI : ∀ b, ChartedSpace (EuclideanQuadrant k)
          (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) := fun b =>
        (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b)
      letI : ChartedSpace (EuclideanQuadrant (k + 1)) (solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
        (MPolyfold.subPolyfold hSm.isSubMPolyfold).cornerChartedSpace hcs'
      ∃ (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
        (o₀ : TangentOrientation (𝓠 k)
          (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false)))) k)
        (o₁ : TangentOrientation (𝓠 k)
          (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true)))) k),
        oS.IsContinuous (𝓠 (k + 1)) ∞ ∧ IsIntervalCobordismOrientation hX hbump hf o hS hgp oS ∧
        o₀.IsContinuous (𝓠 k) ∞ ∧
        IsIntervalEndOrientation hf o hS (ivEnd false) (ivEndLinSurj hf hS hgp false) o₀ ∧
        o₁.IsContinuous (𝓠 k) ∞ ∧
        IsIntervalEndOrientation hf o hS (ivEnd true) (ivEndLinSurj hf hS hgp true) o₁ ∧
        ∀ (α : (BundledMPolyfold.of PX).formsInfty k) (χ : ℕ → ℝ → ℝ),
          (∀ m, ContDiff ℝ ∞ (χ m)) → (∀ m t, |χ m t| ≤ 1) → (∀ m, χ m 0 = 0) →
          (∀ m, χ m 1 = 0) → (∀ t ∈ Ioo (0 : ℝ) 1, Tendsto (fun m => χ m t) atTop (𝓝 1)) →
          haveI := isManifold_of_eq hcs' rfl
          Tendsto (fun m => ManifoldForm.boundaryIntegral oS (ManifoldForm.smulFun
              (fun z => χ m ((z.1.1 0 : unitInterval) : ℝ)) (formsInftyRestrict k hcs'
                (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)))) atTop
            (𝓝 (ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
                (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) -
              (ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
                ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α)))) := by
  have hidx : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsLinOfIndex
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z
        (k + 1 : ℕ) := fun z hz => by
    obtain ⟨t, x⟩ := z
    have hzs := (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection
      hS).mem_smoothSet_of_isZeroAt hz
    have h := isLinOfIndex_interval_of_isIndexAt hbump hf hS hz
      (hk x (prod_cube_mem_smoothSet_iff.1 hzs))
    have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [hc]
    exact h
  have hD := (theorem_6_6_18_solutionSet (prod_cube_isTame hX)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx
  have hcs' := hD.hasCornerStructureOfDim_of_tame (prod_cube_isTame hX)
    ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
      (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
      (prod_cube_isTame hX))
  have hEnd : ∀ b, ∃ hSt : PX.IsSmoothSubmanifold
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))),
      (MPolyfold.subPolyfold hSt.isSubMPolyfold).HasCornerStructureOfDim k := fun b => by
    obtain ⟨hPt, hgpt, hidxt, -⟩ := theorem_6_6_18_oriented_end hX hbump hf o hS hP hgp hk
      (t := ivEnd b) (ivEnd_zero_or_one b)
    have hDt := (theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b)))
      hPt hgpt).isSubmanifoldOfDim (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b))) hidxt
    exact ⟨hDt.1, hDt.hasCornerStructureOfDim_of_tame hX
      ((theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b))) hPt
        hgpt).isGoodPositionAt hX)⟩
  choose hSt hcs using hEnd
  have hI := (theorem_6_6_18_oriented_interval hX hbump hf o hS hP hgp hidx).2.2
  have hOr : ∀ b, letI := (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b)
      ∃ oE : TangentOrientation (𝓠 k)
        (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) k, oE.IsContinuous (𝓠 k) ∞ ∧
        IsIntervalEndOrientation hf o hS (ivEnd b) (ivEndLinSurj hf hS hgp b) oE := fun b => by
    obtain ⟨hPt, hgpt, hidxt, -, -, oE, hoE, hoEs⟩ := theorem_6_6_18_oriented_end hX hbump hf
      o hS hP hgp hk (t := ivEnd b) (ivEnd_zero_or_one b)
    exact ⟨oE, hoE, hoEs⟩
  have h₀ := hOr false
  have h₁ := hOr true
  refine ⟨hD.1, hSt, hcs, hcs', hI.choose, h₀.choose, h₁.choose,
    hI.choose_spec.1, hI.choose_spec.2,
    h₀.choose_spec.1, h₀.choose_spec.2, h₁.choose_spec.1, h₁.choose_spec.2,
    fun α χ hχs hχ1 hχ0 hχ1' hχ => ?_⟩
  exact boundaryIntegral_interval_cobordism_lateral
    (inst := fun b => (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b))
    (inst' := (MPolyfold.subPolyfold hD.1.isSubMPolyfold).cornerChartedSpace hcs')
    hX hbump hf o hS hP hgp hD.1 hSt hcs (fun b => rfl) hcs' rfl hI.choose
    hI.choose_spec.1 hI.choose_spec.2 h₀.choose h₁.choose h₀.choose_spec.1
    h₁.choose_spec.1 h₀.choose_spec.2 h₁.choose_spec.2 α hχs hχ1 hχ0 hχ1' hχ

end Lateral

end Polyfold
