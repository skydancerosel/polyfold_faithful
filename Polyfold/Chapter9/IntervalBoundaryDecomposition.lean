import Polyfold.Chapter9.BoundaryEndFaces
import Polyfold.Chapter4.SubmanifoldNearBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Remark 6.6.19** and the proof of **Theorem 6.7.1**: the boundary of the cobordism
`S_F ⊆ [0, 1] × X` and the boundary integral over it.

# The boundary integral of the cobordism over `[0, 1] × X`

## The text, paraphrased

(p. 278) For `F = f̃ + S` over `[0, 1] × X` proper and in general position, `S_F` is a compact
manifold with boundary and corners whose boundary consists of the ends `\{0\} × S_{F_0}`,
`\{1\} × S_{F_1}` and of the part over `[0, 1] × ∂X`; Stokes' theorem on `S_F` gives
`∫_{∂S_F} pr₂^*ω = ∫_{S_{F_1}} ω − ∫_{S_{F_0}} ω + ∫_{S_F ∩ [0,1] × ∂X} pr₂^*ω`.

## What is formalized

`F = f̃ + S` with `X` tame, `f` tame sc-Fredholm, `S` sc⁺, `F` proper and in general position;
`S_F` and the ends `S_{F_t}`, `t ∈ \{0, 1\}` (`ivEnd`), with the structures of smooth
submanifolds and corner structures of dimensions `k + 1` and `k` (as given by
`theorem_6_6_18_oriented_interval`, `theorem_6_6_18_oriented_end`), `S_F` face-structured (the
reading of Theorem 4.4.7's "boundary a union of smooth faces", as in `theorem_4_4_7_hyp`).

* `degIndex_eq_one_ends`: a point of `S_F` of degeneracy index `1` near an end point of
  degeneracy index `1` lies on the same end.
* `face_end_inverse`: on a face of `S_F` inside `\{t\} × X`, `(t, x) ↦ x` is a `C^∞` map into
  `S_{F_t}`, inverse to the inclusion `j_t` (`MPolyfold.contMDiff_of_isScSmoothMap`).
* **`boundaryIntegral_interval_cobordism`**: for `α ∈ Ωᵏ_∞(X)` and any continuous orientation of
  `S_F`,
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∑_{t ∈ \{0,1\}} ∫_{S_{F_t}} α|_{S_{F_t}} + ∑_F ∫_F (pr₂^*α)|_F`,
  the ends with the orientations induced by `j_t` (outward vector first) and the second sum over
  the faces of `S_F` lying in neither end (in the text, the part over `[0, 1] × ∂X`), with their
  induced orientations; `exists_isInducedOrientation_interval_end`: these orientations of the
  ends exist.
* `boundaryIntegral_interval_cobordism_sub`: if the orientation induced by `j_1` is `o_1` and the
  one induced by `j_0` is `-o_0`, the end terms are `∫_{S_{F_1}} α - ∫_{S_{F_0}} α`.

Not formalized here: that the orientations `o_0`, `o_1` of `theorem_6_6_18_oriented_end` satisfy
these two identities (outward vector first: `+` at `t = 1`, `-` at `t = 0`), and the
face-structuredness of `S_F`, which is a hypothesis.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

/-- The end points of `[0, 1]`: `0` for `false`, `1` for `true`. -/
def ivEnd : Bool → Fin 1 → unitInterval
  | false => fun _ => 0
  | true => fun _ => 1

theorem ivEnd_zero_or_one (b : Bool) : ((ivEnd b 0 : unitInterval) : ℝ) = 0 ∨
    ((ivEnd b 0 : unitInterval) : ℝ) = 1 := by
  cases b <;> simp [ivEnd]

theorem ivEnd_injective : Function.Injective ivEnd := by
  intro b b' h
  have h0 := congrArg (fun g : Fin 1 → unitInterval => ((g 0 : unitInterval) : ℝ)) h
  cases b <;> cases b' <;> simp_all [ivEnd]

section Decomposition

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

/-- **Points of degeneracy index `1` near an end lie on the end**: if `(t, x) ∈ S_F` with
`t ∈ \{0, 1\}` has `d_{S_F}(t, x) = 1`, then `d_X(x) = 0`, and every `(t', x') ∈ S_F` close to
it with `d_{S_F}(t', x') = 1` has `d_X(x') = 0` (upper semicontinuity), so `d_{[0,1]}(t') = 1`
and `t' = t`. -/
theorem degIndex_eq_one_ends (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
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
    (b : Bool) :
    ∀ p ∈ range (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)),
      (MPolyfold.subPolyfold hSm.isSubMPolyfold).degIndex p = 1 →
      ∀ᶠ z in 𝓝 p, (MPolyfold.subPolyfold hSm.isSubMPolyfold).degIndex z = 1 →
        z ∈ range (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) := by
  have hdeg := degIndex_interval_cobordism hX hf hS hP hgp hSm
  have hend : (cubePolyfold 1).degIndex (ivEnd b) = 1 := by
    rw [UnitCube.cubePolyfold_one_degIndex, if_pos (ivEnd_zero_or_one b)]
  rintro p ⟨x, rfl⟩ hp1
  have hx0 : PX.degIndex x.1 = 0 := by
    have h := hdeg (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) x)
    rw [hp1] at h
    change 1 = (cubePolyfold 1).degIndex (ivEnd b) + PX.degIndex x.1 at h
    rw [hend] at h
    omega
  have hc : Continuous fun z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
      ((z.1.1 0 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply 0).comp
      (continuous_fst.comp continuous_subtype_val))
  have hN1 : IsOpen {z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) |
      PX.degIndex z.1.2 ≤ 0} :=
    (isOpen_degIndex_le PX 0).preimage (continuous_snd.comp continuous_subtype_val)
  have hN2 : IsOpen {z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) |
      dist ((z.1.1 0 : unitInterval) : ℝ) ((ivEnd b 0 : unitInterval) : ℝ) < 1 / 2} :=
    isOpen_lt (hc.dist continuous_const) continuous_const
  filter_upwards [hN1.mem_nhds (show PX.degIndex x.1 ≤ 0 from hx0.le),
    hN2.mem_nhds (show dist ((ivEnd b 0 : unitInterval) : ℝ) ((ivEnd b 0 : unitInterval) : ℝ) <
      1 / 2 by simp)] with z hz1 hz2 hz
  have h := hdeg z
  rw [hz, Nat.le_zero.1 hz1, add_zero, UnitCube.cubePolyfold_one_degIndex] at h
  have ht : ((z.1.1 0 : unitInterval) : ℝ) = 0 ∨ ((z.1.1 0 : unitInterval) : ℝ) = 1 := by
    by_contra hne
    rw [if_neg hne] at h
    exact one_ne_zero h
  have heq : z.1.1 = ivEnd b := by
    funext i
    rw [Subsingleton.elim i 0]
    refine Subtype.ext ?_
    have hd2 : dist ((z.1.1 0 : unitInterval) : ℝ) ((ivEnd b 0 : unitInterval) : ℝ) < 1 / 2 := hz2
    rw [Real.dist_eq] at hd2
    rcases ht with h1 | h1 <;> rcases ivEnd_zero_or_one b with h2 | h2 <;>
      rw [h1, h2] at hd2 <;> rw [h1, h2] <;> norm_num at hd2
  rw [range_sliceInclusion]
  exact heq

omit [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **The inverse of an end inclusion on a face**: on a face `a` of `S_F` contained in
`\{t\} × X = range j_t`, the map `(t, x) ↦ x` into `S_{F_t}` is inverse to `j_t` and `C^∞` for the
face charts of `a` (`faceChartedSpace`) and the corner charts of `S_{F_t}`: it is sc-smooth
(`pr₂` restricted, Proposition 2.3.19 (2)), and sc-smooth maps between M-polyfolds with corner
structures are `C^∞` (`MPolyfold.contMDiff_of_isScSmoothMap`). -/
theorem face_end_inverse (hf : IsSection P f)
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
    [inst : ChartedSpace (EuclideanQuadrant k)
      (solutionSet P (sectionAdd P f (prodSlice S t)))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (k + 1))
    (hfs : (MPolyfold.subPolyfold hSm).IsFaceStructured)
    (a : Faces (MPolyfold.subPolyfold hSm)) (ha : a.1 ⊆ range (sliceInclusion hf hS t)) :
    ∃ g : a.1 → solutionSet P (sectionAdd P f (prodSlice S t)),
      (letI := faceChartedSpace hcs' hfs a.2; ContMDiff (𝓠 k) (𝓠 k) ∞ g) ∧
        ∀ p, sliceInclusion hf hS t (g p) = p := by
  have := paracompactSpace_face a.2
  set g : a.1 → solutionSet P (sectionAdd P f (prodSlice S t)) := fun p => (ha p.2).choose
  have hjg : ∀ p, sliceInclusion hf hS t (g p) = p := fun p => (ha p.2).choose_spec
  have hgval : (fun p => (g p : X)) = fun p : a.1 => (p : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)).1.2 := by
    funext p
    rw [← hjg p]
    rfl
  have hsm : (MPolyfold.subPolyfold (theorem_2_5_17_isSubMPolyfold_face
      (MPolyfold.subPolyfold hSm) hcs'.isTame hfs a.2)).IsScSmoothMap
      (MPolyfold.subPolyfold hSt) g := by
    refine MPolyfold.isScSmoothMap_into_subPolyfold hSt ?_
    rw [hgval]
    exact (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX).comp
      ((subPolyfold_inclusion_isScSmooth hSm).comp (subPolyfold_inclusion_isScSmooth _))
  refine ⟨g, ?_, hjg⟩
  exact MPolyfold.contMDiff_of_isScSmoothMap (hasCornerStructureOfDim_face hcs' hfs a.2)
    (inst := faceChartedSpace hcs' hfs a.2) rfl hcs hch hsm

/-- **The boundary integral of the cobordism `S_F`** (2021, proof of Theorem 6.7.1, p. 278, with
Theorem 4.4.7, p. 199): for `F = f̃ + S` proper and in general position over `[0, 1] × X`, `S_F`
and its ends `S_{F_0}`, `S_{F_1}` carrying corner structures of dimensions `k + 1` and `k`,
`S_F` face-structured, a continuous orientation `oS` of `S_F`, orientations `oN b` of the ends
induced by `j_t` (`exists_isInducedOrientation_interval_end`) and `α ∈ Ωᵏ_∞(X)`:
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∑_{t ∈ \{0, 1\}} ∫_{S_{F_t}} α|_{S_{F_t}} + ∑_F ∫_F (pr₂^*α)|_F`, the
second sum over the faces `F` of `S_F` contained in neither end. -/
theorem boundaryIntegral_interval_cobordism (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
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
    (hfs : (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured)
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : oS.IsContinuous (𝓠 (k + 1)) ∞)
    (oN : ∀ b, TangentOrientation (𝓠 k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) k)
    (hoN : ∀ b, IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) oS (oN b))
    (hoNc : ∀ b, (oN b).IsContinuous (𝓠 k) ∞) (α : (BundledMPolyfold.of PX).formsInfty k) :
    haveI := isManifold_of_eq hcs' hch'
    haveI : CompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
      isCompact_iff_compactSpace.1 hP.1
    haveI : Finite (Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold)) := finite_faces hcs'
    letI : Fintype (LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
      fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) := Fintype.ofFinite _
    letI : ∀ a : Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold),
      ChartedSpace (EuclideanQuadrant k) a.1 := fun a => faceChartedSpace hcs' hfs a.2
    ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
        (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) =
      ∑ b, ManifoldForm.integral (oN b) (formsInftyRestrict k (hcs b) α) +
        ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            (fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)),
          ManifoldForm.integral (faceOrientation hcs' hfs oS hch' a.1)
            (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict k hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α))) := by
  have : ∀ b, IsManifold (𝓠 k) ∞ (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) :=
    fun b => isManifold_of_eq (hcs b) (hch b)
  have : CompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    isCompact_iff_compactSpace.1 hP.1
  have : ∀ b, CompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) := fun b =>
    isCompact_iff_compactSpace.1 (isCompact_solutionSet_slice hf.isScSmooth.1 hS.1 hP.1 (ivEnd b))
  have h := boundaryIntegral_eq_sum_ends_add_lateral
    (J := fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) hcs' hfs oS hch' hoS
    (PY := fun b => MPolyfold.subPolyfold (hSt b).isSubMPolyfold) hcs
    (fun b => isEmbedding_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b))
    (fun b => by
      rw [range_sliceInclusion]
      exact isClosed_eq ((continuous_fst.comp continuous_subtype_val)) continuous_const)
    (fun b => contMDiff_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
      (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hch')
    (fun b x => degIndex_interval_cobordism_end hX hf hS hP hgp hSm (ivEnd_zero_or_one b)
      (hSt b) x)
    (fun b => degIndex_eq_one_ends hX hf hS hP hgp hSm b)
    (fun b b' hne => by
      change Disjoint (range _) (range _)
      rw [range_sliceInclusion, range_sliceInclusion]
      exact Set.disjoint_left.2 fun z hz hz' => hne (ivEnd_injective (hz.symm.trans hz')))
    (fun b a ha => face_end_inverse hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
      (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hfs a ha)
    oN hoN hoNc ((contMDiffForm_formsInftyRestrict hch'
      (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)).of_le (by exact_mod_cast le_top))
  refine h.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [restrictForm_sliceInclusion_pullback hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
    (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hch' α]

/-- **The orientations of the ends induced by `j_t`** exist and are continuous
(`exists_isInducedOrientation_end`). -/
theorem exists_isInducedOrientation_interval_end (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f)
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
    (hfs : (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured)
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : oS.IsContinuous (𝓠 (k + 1)) ∞) (b : Bool) :
    ∃ oN : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) k,
      IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) oS oN ∧
        oN.IsContinuous (𝓠 k) ∞ := by
  have : ∀ b, IsManifold (𝓠 k) ∞ (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) :=
    fun b => isManifold_of_eq (hcs b) (hch b)
  exact exists_isInducedOrientation_end
    (J := fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) hcs' hfs oS hch' hoS
    (PY := fun b => MPolyfold.subPolyfold (hSt b).isSubMPolyfold) hcs
    (fun b => isEmbedding_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b))
    (fun b => by
      rw [range_sliceInclusion]
      exact isClosed_eq ((continuous_fst.comp continuous_subtype_val)) continuous_const)
    (fun b => contMDiff_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
      (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hch')
    (fun b x => degIndex_interval_cobordism_end hX hf hS hP hgp hSm (ivEnd_zero_or_one b)
      (hSt b) x)
    (fun b => degIndex_eq_one_ends hX hf hS hP hgp hSm b)
    (fun b b' hne => by
      change Disjoint (range _) (range _)
      rw [range_sliceInclusion, range_sliceInclusion]
      exact Set.disjoint_left.2 fun z hz hz' => hne (ivEnd_injective (hz.symm.trans hz')))
    (fun b a ha => face_end_inverse hf.isScSmooth.1 hS.1 (ivEnd b) hSm.isSubMPolyfold
      (hSt b).isSubMPolyfold (hcs b) (hch b) hcs' hfs a ha) b

/-- **The boundary integral of `S_F` with the signs of the ends** (2021, proof of Theorem 6.7.1,
p. 278): if the orientation induced by `j_1` (outward vector first) is `o_1` and the one induced
by `j_0` is `-o_0`, then
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α - ∫_{S_{F_0}} α + ∑_F ∫_F (pr₂^*α)|_F`, the sum over the
faces of `S_F` contained in neither end. -/
theorem boundaryIntegral_interval_cobordism_sub (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f)
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
    (hfs : (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured)
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : oS.IsContinuous (𝓠 (k + 1)) ∞)
    (o₀ : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false)))) k)
    (o₁ : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true)))) k)
    (ho₀ : o₀.IsContinuous (𝓠 k) ∞) (ho₁ : o₁.IsContinuous (𝓠 k) ∞)
    (hi₀ : IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd false)) oS (-o₀))
    (hi₁ : IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd true)) oS o₁)
    (α : (BundledMPolyfold.of PX).formsInfty k) :
    haveI := isManifold_of_eq hcs' hch'
    haveI : CompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
      isCompact_iff_compactSpace.1 hP.1
    haveI : Finite (Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold)) := finite_faces hcs'
    letI : Fintype (LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
      fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) := Fintype.ofFinite _
    letI : ∀ a : Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold),
      ChartedSpace (EuclideanQuadrant k) a.1 := fun a => faceChartedSpace hcs' hfs a.2
    ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
        (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) =
      ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
        ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α) +
        ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            (fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)),
          ManifoldForm.integral (faceOrientation hcs' hfs oS hch' a.1)
            (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict k hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α))) := by
  have : ∀ b, IsManifold (𝓠 k) ∞ (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) :=
    fun b => isManifold_of_eq (hcs b) (hch b)
  have : CompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false)))) :=
    isCompact_iff_compactSpace.1
      (isCompact_solutionSet_slice hf.isScSmooth.1 hS.1 hP.1 (ivEnd false))
  let oN : ∀ b, TangentOrientation (𝓠 k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) k := fun b => match b with
    | false => -o₀
    | true => o₁
  have h := boundaryIntegral_interval_cobordism hX hf hS hP hgp hSm hSt hcs hch hcs' hch' hfs oS
    hoS oN (fun b => match b with | false => hi₀ | true => hi₁)
    (fun b => match b with | false => ho₀.neg | true => ho₁) α
  have e₀ : ManifoldForm.integral (oN false) (formsInftyRestrict k (hcs false) α) =
      -ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α) :=
    ManifoldForm.integral_neg_orientation ho₀
      ((contMDiffForm_formsInftyRestrict (hch false) α).of_le (by exact_mod_cast le_top))
      isClosed_closure.isCompact
  have e₁ : ManifoldForm.integral (oN true) (formsInftyRestrict k (hcs true) α) =
      ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) := rfl
  rw [h, Fintype.sum_bool]
  exact congrArg (· + _) ((congrArg₂ (· + ·) e₁ e₀).trans (sub_eq_add_neg _ _).symm)

end Decomposition

end Polyfold
