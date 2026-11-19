import Polyfold.Chapter9.IntervalEndSigns
import Polyfold.Chapter6.IntervalCobordismExistence
import Polyfold.Chapter4.GeneralPositionFaceStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Theorem 6.6.18**, **Remark 6.6.19** and the proof of **Theorem 6.7.1**, with Definition 2.5.10
and Theorem 4.2.11.

# The cobordism `S_F ⊆ [0, 1] × X` is face-structured

## The text, paraphrased

(Proof of Theorem 6.7.1, p. 278) For `F = f̃ + S` proper and in general position over
`[0, 1] × X`, Stokes' theorem on the oriented cobordism `S_F` gives
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + (the part of ∂S_F over [0, 1] × ∂X)`.
Stokes' theorem (Theorem 4.4.7) is stated for manifolds whose boundary is a union of faces.

## What is formalized

* `MPolyfold.theorem_4_2_11_isFaceStructured_of_tame`: a smooth submanifold in general position
  at every point of a tame face-structured `X` is face-structured (the tameness of the induced
  structure from Theorem 4.2.7 and Lemma 4.2.8).
* `UnitCube.cubePolyfold_one_isFaceStructured`: `[0, 1]` is face-structured (faces `\{0\}`,
  `\{1\}`); **`isFaceStructured_cubeProd`**: `[0, 1] × X` is face-structured when `X` is tame
  and face-structured (`MPolyfold.isFaceStructured_prod`).
* **`isFaceStructured_interval_cobordism`**: for `X` tame and face-structured and `F` proper and
  in general position over `[0, 1] × X`, the sub-M-polyfold `S_F` is face-structured.
* **`boundaryIntegral_interval_cobordism_faceStructured`**:
  `boundaryIntegral_interval_cobordism_ends` with the hypothesis that `S_F` is face-structured
  replaced by that of `X`.
* **`theorem_6_6_18_boundaryIntegral_interval`**: for `X` tame, face-structured, with sc-smooth
  bump functions, `f` tame sc-Fredholm of index `k` with orientation `o`, and `F = f̃ + S` proper
  and in general position: `S_F` and the ends are smooth submanifolds with corner structures of
  dimensions `k + 1` and `k`, the orientations `oS`, `o_0`, `o_1` of Theorem 6.6.18 / Remark
  6.6.19 exist, and for every `α ∈ Ωᵏ_∞(X)`
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + Σ_{lateral faces} ∫ (pr₂^*α)|_{S_F}`.

## Reading

"`X` face-structured" is the hypothesis under which the faces of `S_F` are faces in the sense of
Definition 2.5.10; the text's Theorem 6.7.1 is stated for tame `X` and its boundary term is
read on the local faces of `X` (Chapter 9's `SolutionFaces`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Manifold Module Function
open scoped ContDiff

noncomputable section

local notation "𝓠" => modelWithCornersEuclideanQuadrant

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold TameBoundary

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **2021 Theorem 4.2.11, the faces of a submanifold in general position**, without the
tameness hypothesis: Theorem 4.2.7 with Lemma 4.2.8 (general position implies good position)
gives a tame induced structure. -/
theorem theorem_4_2_11_isFaceStructured_of_tame (hP : P.IsTame) (hfs : P.IsFaceStructured)
    {A : Set X} (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    (hgp : ∀ a ∈ A, P.IsGeneralPositionAt A a) :
    (subPolyfold hA.isSubMPolyfold).IsFaceStructured := by
  obtain ⟨-, hA', htame⟩ := theorem_4_2_7 hP hA fun a ha => (hgp a ha).isGoodPositionAt hP hA
  exact theorem_4_2_11_isFaceStructured hP hfs hA htame hgp

end MPolyfold

/-- **`[0, 1]` is face-structured**: its faces are `\{0\}` and `\{1\}` (the identity label). -/
theorem UnitCube.cubePolyfold_one_isFaceStructured : (cubePolyfold 1).IsFaceStructured := by
  classical
  refine isFaceStructured_of_label (cubePolyfold_isTame 1) (Λ := id) ?_ ?_
  · intro S hS hSc p hp q hq
    have h01 : ∀ t ∈ S, (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 := fun t ht => by
      have := hS ht
      rw [mem_ofPred_eq, cubePolyfold_one_degIndex] at this
      by_contra hn
      rw [if_neg hn] at this
      exact zero_ne_one this
    have hc : Continuous fun t : Fin 1 → unitInterval => (t 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hI := hSc.image _ hc.continuousOn
    have key : ∀ a ∈ S, ∀ b ∈ S, (a 0 : ℝ) ≤ (b 0 : ℝ) → (a 0 : ℝ) = (b 0 : ℝ) := by
      intro a ha b hb hab
      by_contra hne
      have hlt := lt_of_le_of_ne hab hne
      have ha0 : (a 0 : ℝ) = 0 := by
        rcases h01 a ha with h | h
        · exact h
        · rcases h01 b hb with h' | h' <;> linarith [(b 0).2.2]
      have hb1 : (b 0 : ℝ) = 1 := by
        rcases h01 b hb with h | h
        · linarith
        · exact h
      have hmid := hI.Icc_subset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
        (show (1 / 2 : ℝ) ∈ Icc (a 0 : ℝ) (b 0 : ℝ) by rw [ha0, hb1]; norm_num)
      obtain ⟨t, ht, ht2⟩ := hmid
      have ht2' : (t 0 : ℝ) = 1 / 2 := ht2
      rcases h01 t ht with h | h
      · rw [h] at ht2'; norm_num at ht2'
      · rw [h] at ht2'; norm_num at ht2'
    have hpq : (p 0 : ℝ) = (q 0 : ℝ) := by
      rcases le_total (p 0 : ℝ) (q 0 : ℝ) with h | h
      · exact key p hp q hq h
      · exact (key q hq p hp h).symm
    funext i
    rw [Subsingleton.elim i 0]
    exact Subtype.ext hpq
  · intro t
    by_cases h : (cubePolyfold 1).degIndex t = 1
    · exact ⟨{t}, by rw [h]; rfl, fun a ha N hN => by
        rw [Finset.mem_singleton] at ha
        exact ⟨t, mem_of_mem_nhds hN, h, ha.symm⟩⟩
    · have h0 : (cubePolyfold 1).degIndex t = 0 := by
        rw [cubePolyfold_one_degIndex] at h ⊢
        split_ifs at h ⊢
        · exact absurd rfl h
        · rfl
      exact ⟨∅, by rw [h0]; rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩

section FaceStructure

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

omit [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **`[0, 1] × X` is face-structured** when `X` is tame and face-structured: its faces are
`\{0\} × X`, `\{1\} × X` and `[0, 1] × F` for the faces `F` of `X`. -/
theorem isFaceStructured_cubeProd (hX : PX.IsTame) (hXfs : PX.IsFaceStructured) :
    ((cubePolyfold 1).prod PX).IsFaceStructured :=
  isFaceStructured_prod (cubePolyfold_isTame 1) hX cubePolyfold_one_isFaceStructured hXfs

/-- **Point A: the cobordism `S_F` is face-structured** (Definition 2.5.10): for `X` tame and
face-structured and `F = f̃ + S` proper and in general position over `[0, 1] × X`, every point
of `S_F` lies in exactly `d_{S_F}` faces of `S_F` (Theorem 4.2.11 for the solution set of
Theorem 6.6.18 in the face-structured `[0, 1] × X`). -/
theorem isFaceStructured_interval_cobordism (hX : PX.IsTame) (hXfs : PX.IsFaceStructured)
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
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))] :
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured := by
  obtain ⟨-, -, -, -, hgpS, -, -, -⟩ := theorem_6_6_18_solutionSet (prod_cube_isTame hX)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp
  exact theorem_4_2_11_isFaceStructured_of_tame (prod_cube_isTame hX)
    (isFaceStructured_cubeProd hX hXfs) hSm hgpS

/-- **The boundary integral of `S_F` with the orientations of Theorem 6.6.18 and Remark 6.6.19,
for a face-structured `X`** (2021, proof of Theorem 6.7.1, p. 278):
`boundaryIntegral_interval_cobordism_ends` with `S_F` face-structured derived
(`isFaceStructured_interval_cobordism`):
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + ∑_F ∫_F (pr₂^*α)|_F`, the sum over the
faces of `S_F` contained in neither end. -/
theorem boundaryIntegral_interval_cobordism_faceStructured (hX : PX.IsTame)
    (hXfs : PX.IsFaceStructured) (hbump : PX.AdmitsBumpFunctions)
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
    (α : (BundledMPolyfold.of PX).formsInfty k) :
    haveI := isManifold_of_eq hcs' hch'
    haveI : CompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
      isCompact_iff_compactSpace.1 hP.1
    haveI : Finite (Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold)) := finite_faces hcs'
    letI : Fintype (LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
      fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) := Fintype.ofFinite _
    letI : ∀ a : Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold),
      ChartedSpace (EuclideanQuadrant k) a.1 := fun a =>
        faceChartedSpace hcs' (isFaceStructured_interval_cobordism hX hXfs hf hS hP hgp hSm) a.2
    ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
        (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) =
      ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
        ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α) +
        ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            (fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)),
          ManifoldForm.integral (faceOrientation hcs'
              (isFaceStructured_interval_cobordism hX hXfs hf hS hP hgp hSm) oS hch' a.1)
            (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict k hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α))) :=
  boundaryIntegral_interval_cobordism_ends hX hbump hf o hS hP hgp hSm hSt hcs hch hcs' hch'
    (isFaceStructured_interval_cobordism hX hXfs hf hS hP hgp hSm) oS hoS hoSs o₀ o₁ ho₀ ho₁
    ho₀s ho₁s α

/-- **Stokes' theorem on the cobordism `S_F` with the orientations of Theorem 6.6.18** (2021,
Remark 6.6.19 and the proof of Theorem 6.7.1, pp. 276–278), for a tame face-structured `X` with
sc-smooth bump functions, a tame sc-Fredholm section `f` of index `k` with orientation `o`, and
`F = f̃ + S` proper and in general position over `[0, 1] × X`:
* `S_F ⊆ [0, 1] × X` and the ends `S_{F_b} ⊆ X` are smooth submanifolds with corner structures
  of dimensions `k + 1` and `k`;
* there are continuous orientations `oS` of `S_F` and `o_b` of `S_{F_b}`, those of
  `theorem_6_6_18_oriented_interval` and `theorem_6_6_18_oriented_end`;
* for every `α ∈ Ωᵏ_∞(X)`,
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + Σ_a ∫_a (pr₂^*α)|_{S_F}`, the sum over
  the faces of `S_F` other than the two ends, `S_F` being face-structured
  (`isFaceStructured_interval_cobordism`). -/
theorem theorem_6_6_18_boundaryIntegral_interval (hX : PX.IsTame) (hXfs : PX.IsFaceStructured)
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
        ∀ α : (BundledMPolyfold.of PX).formsInfty k,
          haveI := isManifold_of_eq hcs' rfl
          haveI : CompactSpace (solutionSet (pullbackProj P Prod.snd)
            (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
            isCompact_iff_compactSpace.1 hP.1
          haveI : Finite (Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold)) := finite_faces hcs'
          letI : Fintype (LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) := Fintype.ofFinite _
          letI : ∀ a : Faces (MPolyfold.subPolyfold hSm.isSubMPolyfold),
            ChartedSpace (EuclideanQuadrant k) a.1 := fun a =>
              faceChartedSpace hcs' (isFaceStructured_interval_cobordism hX hXfs hf hS hP hgp hSm)
                a.2
          ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) =
            ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
              ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α) +
              ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
                  (fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)),
                ManifoldForm.integral (faceOrientation hcs'
                    (isFaceStructured_interval_cobordism hX hXfs hf hS hP hgp hSm) oS rfl a.1)
                  (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict k hcs'
                    (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α))) := by
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
    h₀.choose_spec.1, h₀.choose_spec.2, h₁.choose_spec.1, h₁.choose_spec.2, fun α => ?_⟩
  exact boundaryIntegral_interval_cobordism_faceStructured
    (inst := fun b => (MPolyfold.subPolyfold (hSt b).isSubMPolyfold).cornerChartedSpace (hcs b))
    (inst' := (MPolyfold.subPolyfold hD.1.isSubMPolyfold).cornerChartedSpace hcs')
    hX hXfs hbump hf o hS hP hgp hD.1 hSt hcs (fun b => rfl) hcs' rfl hI.choose
    hI.choose_spec.1 hI.choose_spec.2 h₀.choose h₁.choose h₀.choose_spec.1
    h₁.choose_spec.1 h₀.choose_spec.2 h₁.choose_spec.2 α

end FaceStructure

end Polyfold
