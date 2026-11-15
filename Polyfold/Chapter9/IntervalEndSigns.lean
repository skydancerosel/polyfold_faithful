import Polyfold.Chapter9.IntervalBoundaryDecomposition
import Polyfold.Chapter6.IntervalEndManifolds
import Polyfold.Chapter6.IntervalEndOrientation
import Polyfold.Chapter6.InducedOrientationFrames

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Remark 6.6.19** and the proof of **Theorem 6.7.1**: the boundary orientation of the cobordism
`S_F ⊆ [0, 1] × X` on its ends, `∂S_F ⊇ \{1\} × S_{F_1} ⊔ −\{0\} × S_{F_0}`.

# The signs of the ends of the cobordism over `[0, 1] × X`

## The text, paraphrased

(p. 278) The orientation of `S_F` is `e ∧ o` (Remark 6.6.19, `e` the direction of increasing
`t`), and the ends carry the orientations of `S_{F_0}`, `S_{F_1}` given by `o`.  With the outward
normal first, `e` points out of `S_F` at `t = 1` and into it at `t = 0`, so
`∫_{∂S_F} pr₂^*ω = ∫_{S_{F_1}} ω − ∫_{S_{F_0}} ω + (the part over [0, 1] × ∂X)`.

## What is formalized

* `IsIntervalCobordismOrientation`, `IsIntervalEndOrientation`: the defining properties of the
  tangent orientations of `S_F` and of `S_{F_t}` given by `theorem_6_6_18_oriented_interval` and
  `theorem_6_6_18_oriented_end`: in every chart, a basis is positive iff its image under the
  tangent map spans `e ∧ o`, resp. `o`.
* `endHeight`: the function `±t` on `S_F`, with a maximum along the end `\{t\} × S_{F_t}`.
* **`exists_end_frame`**: at every point `p` of an end there are bases `b` of `ℝ^k` and
  `b' = (w, Tj_t b₁, …, Tj_t b_k)` of `ℝ^{k+1}`, `w` of `t`-derivative `1`, with `b'` positive for
  the orientation of `S_F` iff `b` is positive for the orientation of `S_{F_t}`: the end identity
  `tangentOr_ivFirst_eq_ray_iff_of_end` read in the charts of the two manifolds
  (`derivIn_comp_mfderiv`).
* **`isInducedOrientation_interval_end_one`**: at `t = 1` the orientation of `S_{F_1}` is the one
  induced by `j_1 : S_{F_1} → S_F` (outward vector first);
  **`isInducedOrientation_interval_end_zero`**: at `t = 0` the induced one is `−o_{S_{F_0}}`.
* **`boundaryIntegral_interval_cobordism_ends`**: so, for `S_F` face-structured,
  `∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + ∑_F ∫_F (pr₂^*α)|_F`, the sum over the
  faces of `S_F` in neither end, with the orientations of Theorem 6.6.18 and Remark 6.6.19.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

/-! ### Derivatives from coordinates -/

section Coords

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map whose derivative is injective on a non-zero space is differentiable. -/
theorem differentiableWithinAt_of_coords {m : ℕ} {φ : EuclideanSpace ℝ (Fin (m + 1)) → F}
    {s : Set (EuclideanSpace ℝ (Fin (m + 1)))} {x : EuclideanSpace ℝ (Fin (m + 1))}
    {N : Submodule ℝ F} (ι : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗ[ℝ] N)
    (hι : ∀ v, (ι v : F) = fderivWithin ℝ φ s x v) : DifferentiableWithinAt ℝ φ s x := by
  by_contra h
  have h0 : ∀ v, ι v = 0 := fun v => Subtype.ext (by
    rw [hι v, fderivWithin_zero_of_not_differentiableWithinAt h]; rfl)
  have h1 : EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ) = 0 :=
    ι.injective ((h0 _).trans (map_zero ι).symm)
  have := congrArg (fun w : EuclideanSpace ℝ (Fin (m + 1)) => w 0) h1
  simp at this

variable {m : ℕ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanQuadrant m) Q]

/-- The tangent map of `y ↦ (c₀, φ y)` is `v ↦ (0, Tφ v)`, when `Tφ` is the coordinate map of a
subspace. -/
theorem derivIn_prodMk_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : OpenPartialHomeomorph Q (EuclideanQuadrant m)) (φ : Q → F) (c₀ : V) (x : Q)
    {N : Submodule ℝ F} (ι : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] N)
    (hι : ∀ v, (ι v : F) = derivIn (𝓠 m) e φ x v) (v : EuclideanSpace ℝ (Fin m)) :
    derivIn (𝓠 m) e (fun y => (c₀, φ y)) x v = (0, derivIn (𝓠 m) e φ x v) := by
  rcases m with _ | m
  · have hv : v = 0 := by ext i; exact i.elim0
    rw [hv, map_zero, map_zero]
    rfl
  · have hd := differentiableWithinAt_of_coords ι hι
    have hx : e.extend (𝓠 (m + 1)) x ∈ range (𝓠 (m + 1)) := by
      rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
    have h := ((hasFDerivWithinAt_const c₀ (e.extend (𝓠 (m + 1)) x)
      (range (𝓠 (m + 1)))).prodMk hd.hasFDerivWithinAt).fderivWithin
      ((𝓠 (m + 1)).uniqueDiffOn _ hx)
    have h' := congrArg (fun L : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] V × F => L v) h
    refine h'.trans ?_
    rw [ContinuousLinearMap.prod_apply]
    rfl

end Coords

/-! ### The orientations of `S_F` and of its ends -/

section EndSigns

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

/-- **The orientation `e ∧ o` of `S_F`** (Remark 6.6.19 with Theorem 6.6.18; the conclusion of
`theorem_6_6_18_oriented_interval`): in every chart `c` of `[0, 1] × X` at `z ∈ S_F`, a basis of
`ℝ^d` is positive for `oS` iff its image under the tangent map of `S_F → [0, 1] × X` (read in
`c`) spans the orientation `e ∧ o` of `ker F'(z)`. -/
def IsIntervalCobordismOrientation (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    {d : ℕ} [ChartedSpace (EuclideanQuadrant d) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (oS : TangentOrientation (𝓠 d) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) d) :
    Prop :=
  ∀ (z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (c : StrongBundleChart ((cubePolyfold 1).prod PX) (pullbackProj P Prod.snd))
    (hc : (ivBundle B).IsChart c) (hzc : z.1 ∈ c.φ.source),
    ∃ ι : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] c.linKer
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
        (chartPtOf c hc hzc ((theorem_3_1_18_tame (hf.paramCube (n := 1))
          hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2)).z,
      (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 d) (chartAt (EuclideanQuadrant d) z)
        (fun y : solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
          c.φ y.1) z v) ∧
      ∀ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
        b.orientation = tangentOrToModel (oS z) ↔
          (chartPtOf c hc hzc ((theorem_3_1_18_tame (hf.paramCube (n := 1))
              hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2)).tangentOr
            (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS).toIsScFredholmSection z.2
            (hgp z.1 z.2).isLinSurjAt
            (toChartOr (theorem_3_1_18_tame (hf.paramCube (n := 1))
                hS).toIsScFredholmSection
              ((theorem_3_1_18_tame (hf.paramCube (n := 1))
                hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2) c hc hzc
              ((SectionOrientation.ivFirst hX hbump hf o hS).1 z.1
                ((theorem_3_1_18_tame (hf.paramCube (n := 1))
                  hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2))) =
            rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b)

/-- **The orientation `o` of an end `S_{F_t}`** (Theorem 6.6.18 for `F_t`; the conclusion of
`theorem_6_6_18_oriented_end`): in every chart `c` of `X` at `x ∈ S_{F_t}`, a basis of `ℝ^k` is
positive for `oE` iff its image under the tangent map of `S_{F_t} → X` spans the orientation `o`
of `ker F_t'(x)`. -/
def IsIntervalEndOrientation (hf : B.IsScFredholmSectionTame f)
    (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) (t : Fin 1 → unitInterval)
    (hLt : ∀ x : solutionSet P (sectionAdd P f (prodSlice S t)),
      B.IsLinSurjAt (sectionAdd P f (prodSlice S t)) x.1)
    {k : ℕ} [ChartedSpace (EuclideanQuadrant k) (solutionSet P (sectionAdd P f (prodSlice S t)))]
    (oE : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S t))) k) : Prop :=
  ∀ (x : solutionSet P (sectionAdd P f (prodSlice S t))) (c : StrongBundleChart PX P)
    (hc : B.IsChart c) (hxc : x.1 ∈ c.φ.source),
    ∃ ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] c.linKer (sectionAdd P f (prodSlice S t))
        (chartPtOf c hc hxc ((theorem_3_1_18_tame hf
          (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).z,
      (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 k) (chartAt (EuclideanQuadrant k) x)
        (fun y : solutionSet P (sectionAdd P f (prodSlice S t)) => c.φ y.1) x v) ∧
      ∀ b : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
        b.orientation = tangentOrToModel (oE x) ↔
          (chartPtOf c hc hxc ((theorem_3_1_18_tame hf
              (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).tangentOr
            (theorem_3_1_18_tame hf (hS.cubeSlice t)).toIsScFredholmSection x.2 (hLt x)
            (toChartOr (theorem_3_1_18_tame hf (hS.cubeSlice t)).toIsScFredholmSection
              ((theorem_3_1_18_tame hf
                (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)
              c hc hxc
              ((o.sectionAdd (hS.cubeSlice t)).1 x.1 ((theorem_3_1_18_tame hf
                (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2))) =
            rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b)

/-- **The height of the end `t = b`**: `t` for `b = true` (the end `t = 1`), `−t` for
`b = false` (the end `t = 0`); it is maximal along the end. -/
def endHeight (b : Bool) {Z : Set ((Fin 1 → unitInterval) × X)} (z : Z) : ℝ :=
  orSign b * ((z.1.1 0 : unitInterval) : ℝ)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
theorem endHeight_le (b : Bool) {Z : Set ((Fin 1 → unitInterval) × X)} (z z' : Z)
    (hz' : z'.1.1 = ivEnd b) : endHeight b z ≤ endHeight b z' := by
  unfold endHeight
  rw [hz']
  have h1 := (z.1.1 0).2.1
  have h2 := (z.1.1 0).2.2
  cases b <;> simp [ivEnd, orSign] <;> linarith

/-- The chart of `[0, 1]` at the end `b`: `t ↦ 1 − t` at `t = 1`, `t ↦ t` at `t = 0`. -/
def endChartIndex (b : Bool) : Fin 1 → Bool := fun _ => !b

theorem ivEnd_mem_chart_source (b : Bool) : ivEnd b ∈ (chart (endChartIndex b)).source := by
  intro i
  cases b <;> simp [ivEnd, endChartIndex, fl]

theorem orSign_mul_ivSign_mul_ivSign (b : Bool) :
    orSign b * ivSign (endChartIndex b) * ivSign (endChartIndex b) = orSign b := by
  rw [mul_assoc, ivSign_mul_self, mul_one]

/-- **A frame at a point of an end, outward vector first up to the sign of `b`**: at every
`p ∈ S_{F_t}`, `t ∈ \{0, 1\}`, there are bases `bb` of `ℝ^k` and
`bb' = (w, Tj_t bb₁, …, Tj_t bb_k)` of `ℝ^{k+1}` (read in the charts at `p` and `j_t p`) with
`d(±t)(w) = ±1` and `bb'` positive for `oS` iff `bb` is positive for `oE`; `±t` is
`endHeight b`, and it is differentiable in the chart at `j_t p`. -/
theorem exists_end_frame (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (b : Bool) (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))))
    [ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))))] {k : ℕ}
    (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim k)
    [inst : ChartedSpace (EuclideanQuadrant k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (k + 1))
    [inst' : ChartedSpace (EuclideanQuadrant (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs')
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : IsIntervalCobordismOrientation hX hbump hf o hS hgp oS)
    (hLt : ∀ x : solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))),
      B.IsLinSurjAt (sectionAdd P f (prodSlice S (ivEnd b))) x.1)
    (oE : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) k)
    (hoE : IsIntervalEndOrientation hf o hS (ivEnd b) hLt oE)
    (p : solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) :
    DifferentiableWithinAt ℝ (endHeight b ∘
        ((chartAt (EuclideanQuadrant (k + 1))
          (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)).extend (𝓠 (k + 1))).symm)
        (range (𝓠 (k + 1)))
        ((chartAt (EuclideanQuadrant (k + 1))
          (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)).extend
          (𝓠 (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)) ∧
    ∃ (bb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)))
      (bb' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1)))),
      (∀ l, bb' l.succ = mfderiv (𝓠 k) (𝓠 (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b))
        p (bb l)) ∧
      derivIn (𝓠 (k + 1)) (chartAt (EuclideanQuadrant (k + 1))
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)) (endHeight b)
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p) (bb' 0) = orSign b ∧
      (bb'.orientation = tangentOrToModel (oS (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)) ↔
        bb.orientation = tangentOrToModel (oE p)) := by
  have := isManifold_of_eq hcs hch
  have := isManifold_of_eq hcs' hch'
  have ht : ((ivEnd b 0 : unitInterval) : ℝ) = 0 ∨ ((ivEnd b 0 : unitInterval) : ℝ) = 1 :=
    ivEnd_zero_or_one b
  have hjd : MDifferentiableAt (𝓠 k) (𝓠 (k + 1))
      (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) p :=
    (contMDiff_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) hSm hSt hcs hch hcs'
      hch').mdifferentiableAt (by simp)
  have hFred := (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS).toIsScFredholmSection
  have hFt := (theorem_3_1_18_tame hf (hS.cubeSlice (ivEnd b))).toIsScFredholmSection
  have hxs : p.1 ∈ PX.smoothSet := hFt.mem_smoothSet_of_isZeroAt p.2
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
      (ivEnd b, p.1) :=
    (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p).2
  obtain ⟨c, hcm, hxc⟩ := exists_chart_mem B p.1
  have hc := B.isChart_of_mem hcm
  have hb' : ivEnd b ∈ (chart (endChartIndex b)).source := ivEnd_mem_chart_source b
  obtain ⟨ι, hι, hE⟩ := hoE p c hc hxc
  obtain ⟨ι', hι', hF⟩ := hoS (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)
    (ivChart (endChartIndex b) c (S (ivEnd b, p.1)))
    (isChart_ivChart (endChartIndex b) hc (S (ivEnd b, p.1)))
    (mem_ivChart_source (S (ivEnd b, p.1)) hxc hb')
  -- the kernel of `F'(t, x)` meets `\{0\} × E` in `\{0\} × ker F_t'(x)`
  have hiff : ∀ w : (Fin 1 → ℝ) × c.φ.model.E 0, w.1 = 0 →
      (w ∈ (ivChart (endChartIndex b) c (S (ivEnd b, p.1))).linKer
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
        (chartPtOf (ivChart (endChartIndex b) c (S (ivEnd b, p.1)))
          (isChart_ivChart (endChartIndex b) hc (S (ivEnd b, p.1)))
          (mem_ivChart_source (S (ivEnd b, p.1)) hxc hb')
          (hFred.mem_smoothSet_of_isZeroAt hz0)).z ↔
        w.2 ∈ c.linKer (sectionAdd P f (prodSlice S (ivEnd b)))
          (chartPtOf c hc hxc hxs).z) := by
    intro w hw
    have hzz : (chartPtOf (ivChart (endChartIndex b) c (S (ivEnd b, p.1)))
        (isChart_ivChart (endChartIndex b) hc (S (ivEnd b, p.1)))
        (mem_ivChart_source (S (ivEnd b, p.1)) hxc hb') (hFred.mem_smoothSet_of_isZeroAt hz0)).z =
        ((chartPtOf c hc hxc hxs).ivPt (endChartIndex b) hb' (S (ivEnd b, p.1))).z :=
      ivChart_lift_eq (endChartIndex b) (chartPtOf c hc hxc hxs).z
        (chartPtOf c hc hxc hxs).toBase_z (ivEnd b) (S (ivEnd b, p.1)) _
        (chartPtOf (ivChart (endChartIndex b) c (S (ivEnd b, p.1)))
          (isChart_ivChart (endChartIndex b) hc (S (ivEnd b, p.1)))
          (mem_ivChart_source (S (ivEnd b, p.1)) hxc hb')
          (hFred.mem_smoothSet_of_isZeroAt hz0)).toBase_z
    have hsl := prodSlice_sectionAdd_cubeLift hf.isScSmooth.1 hS.1 (ivEnd b)
    have hg : B.IsScFredholmSection (prodSlice (sectionAdd (pullbackProj P Prod.snd)
        (cubeLift (n := 1) f hf.isScSmooth.1) S) (ivEnd b)) := by rw [hsl]; exact hFt
    have hx0 : IsZeroAt P (prodSlice (sectionAdd (pullbackProj P Prod.snd)
        (cubeLift (n := 1) f hf.isScSmooth.1) S) (ivEnd b)) p.1 := by rw [hsl]; exact p.2
    have key := (chartPtOf c hc hxc hxs).mem_linKer_ivPt_iff_of_fst_eq_zero (endChartIndex b)
      hb' (S (ivEnd b, p.1)) hFred hg hz0 hx0 w hw
    rw [hzz]
    refine key.trans ?_
    rw [hsl]
    exact Iff.rfl
  obtain ⟨bb', h₀, h₁⟩ := exists_timeFirst_basis ι ι' hiff (ivSign_ne_zero (endChartIndex b))
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  -- the tangent map of `j_t` in coordinates: `ι' ∘ Tj = (0, ι)`
  have hh'd : DifferentiableWithinAt ℝ ((fun y : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
        (ivChart (endChartIndex b) c (S (ivEnd b, p.1))).φ y.1) ∘
      ((chartAt (EuclideanQuadrant (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)
        p)).extend (𝓠 (k + 1))).symm) (range (𝓠 (k + 1)))
      ((chartAt (EuclideanQuadrant (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)
        p)).extend (𝓠 (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)) :=
    differentiableWithinAt_of_coords ι' fun v => hι' v
  have hTj : ∀ w, ((ι' (mfderiv (𝓠 k) (𝓠 (k + 1))
      (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) p w)).1 :
        (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (ι w : c.φ.model.E 0)) := by
    intro w
    refine (hι' _).trans ?_
    rw [← derivIn_comp_mfderiv hjd hh'd w]
    have hcomp : ((fun y : solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
          (ivChart (endChartIndex b) c (S (ivEnd b, p.1))).φ y.1) ∘
          sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) =
        fun y : solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))) =>
          ((chart (endChartIndex b) (ivEnd b) : Fin 1 → ℝ), (c.φ y.1 : c.φ.model.E 0)) := rfl
    rw [hcomp]
    have hpr := derivIn_prodMk_const (chartAt (EuclideanQuadrant k) p)
      (fun y : solutionSet P (sectionAdd P f (prodSlice S (ivEnd b))) =>
        (c.φ y.1 : c.φ.model.E 0)) ((chart (endChartIndex b) (ivEnd b) : Fin 1 → ℝ)) p ι
      (fun v => hι v) w
    exact hpr.trans (Prod.ext rfl (hι w).symm)
  have hsucc : ∀ l, bb' l.succ = mfderiv (𝓠 k) (𝓠 (k + 1))
      (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)) p
        ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis l) := by
    intro l
    refine ι'.injective (Subtype.ext ?_)
    exact (h₀ l).trans (hTj _).symm
  -- the height `±t` in the chart: `±t = ψ ∘ φ`, `ψ` affine
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (Fin 1 → ℝ) × c.φ.model.E 0 →L[ℝ] ℝ,
      ℓ = (orSign b * ivSign (endChartIndex b)) • ((ContinuousLinearMap.proj (0 : Fin 1)).comp
        (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (c.φ.model.E 0))) := ⟨_, rfl⟩
  have hℓv : ∀ w, ℓ w = orSign b * ivSign (endChartIndex b) * w.1 0 := fun w => by
    rw [hℓ]; rfl
  have hψ : endHeight b = (fun w : (Fin 1 → ℝ) × c.φ.model.E 0 =>
      ℓ w + orSign b * (if b then 1 else 0)) ∘
      (fun y : solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
          ((ivChart (endChartIndex b) c (S (ivEnd b, p.1))).φ y.1 :
            (Fin 1 → ℝ) × c.φ.model.E 0)) := by
    funext y
    simp only [endHeight, hℓv]
    change orSign b * ((y.1.1 0 : unitInterval) : ℝ) =
      orSign b * ivSign (endChartIndex b) * fl (endChartIndex b 0) ((y.1.1 0 : unitInterval) : ℝ) +
        orSign b * (if b then 1 else 0)
    cases b <;> simp [endChartIndex, ivSign, fl]
  refine ⟨?_, (EuclideanSpace.basisFun (Fin k) ℝ).toBasis, bb', hsucc, ?_, ?_⟩
  · rw [hψ]
    exact (ℓ.differentiable.add_const _).differentiableAt.comp_differentiableWithinAt _ hh'd
  · have hz' : (chartAt (EuclideanQuadrant (k + 1))
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)).extend (𝓠 (k + 1))
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p) ∈ range (𝓠 (k + 1)) := by
      rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
    have hd := ((ℓ.hasFDerivAt.add_const (orSign b * (if b then 1 else 0))).comp_hasFDerivWithinAt
      _ hh'd.hasFDerivWithinAt).fderivWithin ((𝓠 (k + 1)).uniqueDiffOn _ hz')
    have h1 : (derivIn (𝓠 (k + 1)) (chartAt (EuclideanQuadrant (k + 1))
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p))
        (fun y : solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
          (ivChart (endChartIndex b) c (S (ivEnd b, p.1))).φ y.1)
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p) (bb' 0)).1 =
        fun _ => ivSign (endChartIndex b) :=
      (congrArg Prod.fst (hι' (bb' 0))).symm.trans h₁
    have hv : ℓ (derivIn (𝓠 (k + 1)) (chartAt (EuclideanQuadrant (k + 1))
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p))
        (fun y : solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
          (ivChart (endChartIndex b) c (S (ivEnd b, p.1))).φ y.1)
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p) (bb' 0)) = orSign b :=
      (hℓv _).trans ((congrArg (fun v : Fin 1 → ℝ => orSign b * ivSign (endChartIndex b) * v 0)
        h1).trans (orSign_mul_ivSign_mul_ivSign b))
    have e : endHeight b ∘ ((chartAt (EuclideanQuadrant (k + 1))
        (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)).extend (𝓠 (k + 1))).symm =
        (fun w : (Fin 1 → ℝ) × c.φ.model.E 0 => ℓ w + orSign b * (if b then 1 else 0)) ∘
          ((fun y : solutionSet (pullbackProj P Prod.snd)
            (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
            ((ivChart (endChartIndex b) c (S (ivEnd b, p.1))).φ y.1 :
              (Fin 1 → ℝ) × c.φ.model.E 0)) ∘
          ((chartAt (EuclideanQuadrant (k + 1))
            (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)).extend (𝓠 (k + 1))).symm) := by
      rw [hψ]; rfl
    exact (congrArg (fun F => fderivWithin ℝ F (range (𝓠 (k + 1)))
      ((chartAt (EuclideanQuadrant (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)
        p)).extend (𝓠 (k + 1)) (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b) p)) (bb' 0)) e).trans
      ((congrArg (fun L => L (bb' 0)) hd).trans hv)
  · have hend := tangentOr_ivFirst_eq_ray_iff_of_end hX hbump hf o hS ht hxs (endChartIndex b)
      hb' hc hxc (S (ivEnd b, p.1)) hz0 (hgp _ hz0) ι ι'
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bb' h₀ h₁
    exact orientation_end_iff_of_specs ι ι' hF hE _ bb' hend

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- `F_t'(x)` is onto at every zero `x` of an end `F_t`, `t ∈ \{0, 1\}`
(`isLinSurjAt_slice_of_end`). -/
theorem ivEndLinSurj (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (b : Bool) (x : solutionSet P (sectionAdd P f (prodSlice S (ivEnd b)))) :
    B.IsLinSurjAt (sectionAdd P f (prodSlice S (ivEnd b))) x.1 :=
  isLinSurjAt_slice_of_end hf hS (ivEnd_zero_or_one b)
    (isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 x.2)
    (hgp _ (isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 x.2))

/-- **The end `t = 1` with the induced orientation** (2021, proof of Theorem 6.7.1, p. 278): for
the orientation `e ∧ o` of `S_F` (Remark 6.6.19) and the orientation `o` of `S_{F_1}`
(Theorem 6.6.18), the orientation induced on `S_{F_1}` by `j_1 : S_{F_1} → S_F` (outward vector
first) is that of `S_{F_1}`: `e` points out of `S_F` at `t = 1`. -/
theorem isInducedOrientation_interval_end_one (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true)))))
    [ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true))))] {k : ℕ}
    (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim k)
    [inst : ChartedSpace (EuclideanQuadrant k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true))))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (k + 1))
    [inst' : ChartedSpace (EuclideanQuadrant (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs')
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : IsIntervalCobordismOrientation hX hbump hf o hS hgp oS)
    (oE : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd true)))) k)
    (hoE : IsIntervalEndOrientation hf o hS (ivEnd true) (ivEndLinSurj hf hS hgp true) oE) :
    IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd true)) oS oE := by
  have := isManifold_of_eq hcs hch
  have := isManifold_of_eq hcs' hch'
  refine isInducedOrientation_of_outward_frames oS oE (g := endHeight true)
    (fun p => (contMDiff_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd true) hSm hSt hcs hch hcs'
      hch').mdifferentiableAt (by simp))
    (fun p => Filter.Eventually.of_forall fun y => endHeight_le true y _ rfl)
    (fun p => Filter.Eventually.of_forall fun q => rfl)
    (fun p => (exists_end_frame hX hbump hf o hS hgp hSm true hSt hcs hch hcs' hch' oS hoS
      (ivEndLinSurj hf hS hgp true) oE hoE p).1) fun p => ?_
  obtain ⟨-, bb, bb', h1, h2, h3⟩ := exists_end_frame hX hbump hf o hS hgp hSm true hSt hcs hch
    hcs' hch' oS hoS (ivEndLinSurj hf hS hgp true) oE hoE p
  exact ⟨bb, bb', h1, lt_of_lt_of_eq (by norm_num [orSign]) h2.symm, h3⟩

/-- **The end `t = 0` with the induced orientation** (2021, proof of Theorem 6.7.1, p. 278): the
orientation induced on `S_{F_0}` by `j_0` (outward vector first) is the opposite of the
orientation `o` of `S_{F_0}`: `e` points into `S_F` at `t = 0`. -/
theorem isInducedOrientation_interval_end_zero (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false)))))
    [ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false))))] {k : ℕ}
    (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim k)
    [inst : ChartedSpace (EuclideanQuadrant k)
      (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false))))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (k + 1))
    [inst' : ChartedSpace (EuclideanQuadrant (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs')
    (oS : TangentOrientation (𝓠 (k + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) (k + 1))
    (hoS : IsIntervalCobordismOrientation hX hbump hf o hS hgp oS)
    (oE : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S (ivEnd false)))) k)
    (hoE : IsIntervalEndOrientation hf o hS (ivEnd false) (ivEndLinSurj hf hS hgp false) oE) :
    IsInducedOrientation (sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd false)) oS (-oE) := by
  have := isManifold_of_eq hcs hch
  have := isManifold_of_eq hcs' hch'
  refine isInducedOrientation_neg_of_inward_frames oS oE (g := endHeight false)
    (fun p => (contMDiff_sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd false) hSm hSt hcs hch hcs'
      hch').mdifferentiableAt (by simp))
    (fun p => Filter.Eventually.of_forall fun y => endHeight_le false y _ rfl)
    (fun p => Filter.Eventually.of_forall fun q => rfl)
    (fun p => (exists_end_frame hX hbump hf o hS hgp hSm false hSt hcs hch hcs' hch' oS hoS
      (ivEndLinSurj hf hS hgp false) oE hoE p).1) fun p => ?_
  obtain ⟨-, bb, bb', h1, h2, h3⟩ := exists_end_frame hX hbump hf o hS hgp hSm false hSt hcs hch
    hcs' hch' oS hoS (ivEndLinSurj hf hS hgp false) oE hoE p
  exact ⟨bb, bb', h1, lt_of_eq_of_lt h2 (by norm_num [orSign]), h3⟩

/-- **The boundary integral of `S_F` with the orientations of Theorem 6.6.18 and Remark 6.6.19**
(2021, proof of Theorem 6.7.1, p. 278): for `F = f̃ + S` proper and in general position over
`[0, 1] × X`, `S_F` face-structured, `oS` the orientation `e ∧ o` of `S_F` and `o_0`, `o_1` the
orientations `o` of the ends, and `α ∈ Ωᵏ_∞(X)`:
`∫_{∂S_F} (pr₂^*α)|_{S_F} = ∫_{S_{F_1}} α − ∫_{S_{F_0}} α + ∑_F ∫_F (pr₂^*α)|_F`, the sum over the
faces of `S_F` contained in neither end. -/
theorem boundaryIntegral_interval_cobordism_ends (hX : PX.IsTame)
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
    (hfs : (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured)
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
      ChartedSpace (EuclideanQuadrant k) a.1 := fun a => faceChartedSpace hcs' hfs a.2
    ManifoldForm.boundaryIntegral oS (formsInftyRestrict k hcs'
        (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α)) =
      ManifoldForm.integral o₁ (formsInftyRestrict k (hcs true) α) -
        ManifoldForm.integral o₀ (formsInftyRestrict k (hcs false) α) +
        ∑ a : LateralFace (MPolyfold.subPolyfold hSm.isSubMPolyfold)
            (fun b => sliceInclusion hf.isScSmooth.1 hS.1 (ivEnd b)),
          ManifoldForm.integral (faceOrientation hcs' hfs oS hch' a.1)
            (restrictForm (Subtype.val : a.1.1 → _) (formsInftyRestrict k hcs'
              (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α))) :=
  boundaryIntegral_interval_cobordism_sub hX hf hS hP hgp hSm hSt hcs hch hcs' hch' hfs oS hoS
    o₀ o₁ ho₀ ho₁
    (isInducedOrientation_interval_end_zero hX hbump hf o hS hgp hSm.isSubMPolyfold
      (hSt false).isSubMPolyfold (hcs false) (hch false) hcs' hch' oS hoSs o₀ ho₀s)
    (isInducedOrientation_interval_end_one hX hbump hf o hS hgp hSm.isSubMPolyfold
      (hSt true).isSubMPolyfold (hcs true) (hch true) hcs' hch' oS hoSs o₁ ho₁s) α

end EndSigns

end Polyfold
