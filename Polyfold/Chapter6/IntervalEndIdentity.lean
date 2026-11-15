import Polyfold.Chapter6.IntervalSliceOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Remark 6.6.19** (preprint Remark 6.42) and the proof of Theorem 6.7.1: the orientation of the
cobordism `S_F ⊆ [0, 1] × X`, `F = f̃ + S`, at a point `(t, x)` and the orientation of the
solution set `S_{F_t} ⊆ X` of the slice `F_t = f + S(t, ·)`.

# The end identity for `F = f̃ + S` over `[0, 1] × X`

## What is formalized

* `pullOr_tangentOrOf_ivOrLift_iff_of_slice`:
  `ChartPoint.pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice` for chart points with given level-`1`
  lifts.
* `pullOr_tangentOr_ivFirst_iff_slice`: for an orientation `o` of `f`, an sc⁺-section `S` over
  `[0, 1] × X`, `F = f̃ + S` and a zero `(t, x)` of `F` with `F'(t, x)` and `F_t'(x)` onto: in
  coordinates `ι` of `ker F_t'(x) = T_xS_{F_t}` and `ι̂` of `ker F'(t, x) = T_{(t,x)}S_F` with
  `ι̂(0, w) = (0, ι w)` and `ι̂(1, 0)` of `t`-component `± 1` (the direction of increasing `t`),
  the tangent orientation of `S_F` given by `e ∧ o` (`SectionOrientation.ivFirst`) is the
  standard orientation of `ℝ^{k+1}` iff the tangent orientation of `S_{F_t}` given by `o`
  (`SectionOrientation.sectionAdd`) is the standard orientation of `ℝ^k`.

At `t = 1` the vector `ι̂(1, 0)` points out of `[0, 1] × X` and at `t = 0` into it.  So, with the
outward normal first (Definition 9.3.8), the boundary orientation of `S_F` at a point of
`\{1\} × S_{F_1}` is the orientation of `S_{F_1}` given by `o`, and at a point of
`\{0\} × S_{F_0}` it is the opposite of the orientation of `S_{F_0}` given by `o`:
`∂S_F = \{1\} × S_{F_1} ⊔ −\{0\} × S_{F_0}` at the level of tangent spaces.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube MPolyfold

universe u v

section IvEndIdentity

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **The orientation `e ∧ o` and the slice, for chart points with given lifts**
(`ChartPoint.pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice` for `ivOrLift`), with the slice
`G(t, ·)` written as a section `g`. -/
theorem pullOr_tangentOrOf_ivOrLift_iff_of_slice (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty) (o : (chartPt c hc hx z hz).Or f hf)
    {G : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) {g : X → Y} (hslice : prodSlice G t = g)
    (hg : B.IsScFredholmSection g)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P g x)
    (hgL : B.IsLinSurjAt g x) (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem : (chartPt c hc hx z hz).linZero hg hx0 ∈ (chartPt c hc hx z hz).linSet f)
    (hmem' : (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linZero hG hz0 ∈
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] c.linKer g z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (ivChart b c q₀).linKer G z')
    (hι₀ : ∀ w, ((ι' (consE 0 w)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      (0, (ι w : c.φ.model.E 0)))
    (hι₁ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k)))).1 :
      (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) :
    pullOr finrank_euclideanSpace_fin ι'
        ((chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').tangentOrOf hfc hG hz0 hGL hmem'
          (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o)) =
        stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι
        ((chartPt c hc hx z hz).tangentOrOf hf hg hx0 hgL hmem o) = stdOrientation k := by
  subst hzz
  subst hslice
  exact (chartPt c hc hx z hz).pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice b ht q₀ hf hfc hxs hne o
    hG hg hz0 hx0 hgL hGL hmem hmem' ι ι' hι₀ hι₁

/-- **The end identity for `F = f̃ + S` over `[0, 1] × X`** (2021 Remark 6.6.19, p. 276, and the
proof of Theorem 6.7.1, p. 278): let `o` be an orientation of the tame sc-Fredholm section `f`
over a tame `X` with sc-smooth bump functions, `S` an sc⁺-section over `[0, 1] × X`,
`F = f̃ + S`, and `(t, x)` a zero of `F` (so `x` is a zero of `F_t = f + S(t, ·)`) at which
`F'(t, x)` and `F_t'(x)` are onto.  Let `ι : ℝ^k ≅ ker F_t'(x)` and `ι̂ : ℝ^{k+1} ≅ ker F'(t, x)`
be coordinates in the charts `c` and `χ_b × φ_c` with `ι̂(0, w) = (0, ι w)` and `ι̂(1, 0)` of
`t`-component `± 1`, the sign that of `χ_b` (the direction of increasing `t`).  Then the tangent
orientation of `S_F` at `(t, x)` given by `e ∧ o` (`SectionOrientation.ivFirst`) is the standard
orientation of `ℝ^{k+1}` iff the tangent orientation of `S_{F_t}` at `x` given by `o`
(`SectionOrientation.sectionAdd`) is the standard orientation of `ℝ^k`.  `t = 0` and `t = 1` are
included; there `ι̂(1, 0)` points into, resp. out of, `[0, 1] × X`. -/
theorem pullOr_tangentOr_ivFirst_iff_slice (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval} {x : X}
    (hxs : x ∈ PX.smoothSet) (b : Fin 1 → Bool) (hb : t ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hL : (ivBundle B).IsLinSurjAt (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hx0 : IsZeroAt P (sectionAdd P f (prodSlice S t)) x)
    (hLt : B.IsLinSurjAt (sectionAdd P f (prodSlice S t)) x)
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ]
      c.linKer (sectionAdd P f (prodSlice S t)) (chartPtOf c hc hxc hxs).z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (ivChart b c q₀).linKer
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
      (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).z)
    (hι₀ : ∀ w, ((ι' (consE 0 w)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      (0, (ι w : c.φ.model.E 0)))
    (hι₁ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k)))).1 :
      (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) :
    pullOr finrank_euclideanSpace_fin ι'
        ((chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).tangentOr
          (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS) hz0 hL
          (toChartOr (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS)
            (prod_cube_mem_smoothSet_iff.2 hxs) (ivChart b c q₀) (isChart_ivChart b hc q₀)
            (mem_ivChart_source q₀ hxc hb)
            ((SectionOrientation.ivFirst hX hbump hf o hS).1 (t, x)
              (prod_cube_mem_smoothSet_iff.2 hxs)))) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι
        ((chartPtOf c hc hxc hxs).tangentOr
          (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t)) hx0 hLt
          (toChartOr (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t)) hxs c
            hc hxc ((o.sectionAdd (hS.cubeSlice t)).1 x hxs))) = stdOrientation k := by
  have hf' := hf.toIsScFredholmSection
  have hfc := (hf.paramCube (n := 1)).toIsScFredholmSection
  have hs := hS.cubeSlice t
  have hne := ChartPoint.linSet_nonempty (chartPtOf c hc hxc hxs) hf' hxs
    (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)
  have e1 := tangentOr_toChartOr_ivFirst hX hbump hf o hS hxs b hb hc hxc q₀ hz0 hL
  have e2 : (chartPtOf c hc hxc hxs).tangentOr (theorem_3_1_18_preprint hf' hs) hx0 hLt
      (toChartOr (theorem_3_1_18_preprint hf' hs) hxs c hc hxc
        ((o.sectionAdd hs).1 x hxs)) =
      (chartPtOf c hc hxc hxs).pertTangentOr hf' hs hx0 hLt
        (toChartOr hf' hxs c hc hxc (o.1 x hxs)) :=
    (congrArg _ (toChartOr_orSectionAdd hf' hs hxs (o.1 x hxs) c hc hxc)).trans
      (ChartPoint.tangentOr_orSectionAdd _ hf' hs hx0 hLt _)
  refine (iff_of_eq (congrArg (fun r => pullOr finrank_euclideanSpace_fin ι' r =
    stdOrientation (k + 1)) e1)).trans (Iff.trans ?_ (iff_of_eq (congrArg (fun r =>
      pullOr finrank_euclideanSpace_fin ι r = stdOrientation k) e2)).symm)
  exact pullOr_tangentOrOf_ivOrLift_iff_of_slice b hc hxc _
    (exists_lift_of_smooth c hxc hxs).choose_spec hb q₀ (mem_ivChart_source q₀ hxc hb) _
    (exists_lift_of_smooth (ivChart b c q₀) (mem_ivChart_source q₀ hxc hb)
      (prod_cube_mem_smoothSet_iff.2 hxs)).choose_spec
    (ivChart_lift_eq b _ (exists_lift_of_smooth c hxc hxs).choose_spec t q₀ _
      (exists_lift_of_smooth (ivChart b c q₀) (mem_ivChart_source q₀ hxc hb)
        (prod_cube_mem_smoothSet_iff.2 hxs)).choose_spec) hf' hfc hxs hne
    (toChartOr hf' hxs c hc hxc (o.1 x hxs)) (theorem_3_1_18_preprint hfc hS)
    (prodSlice_sectionAdd_cubeLift hf'.isScSmooth.1 hS.1 t) (theorem_3_1_18_preprint hf' hs)
    hz0 hx0 hLt hL
    ((chartPtOf c hc hxc hxs).linZero_mem_linSet_of_sectionAdd hf' hs hx0)
    ((chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
      (mem_ivChart_source q₀ hxc hb)
      (prod_cube_mem_smoothSet_iff.2 hxs)).linZero_mem_linSet_of_sectionAdd hfc hS hz0)
    ι ι' hι₀ hι₁

end IvEndIdentity

end Polyfold
