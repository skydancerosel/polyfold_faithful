import Polyfold.Chapter6.IntervalCobordismDegeneracy
import Polyfold.Chapter6.IntervalCobordismStokes

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.3, p. 43
(**Proposition 2.3.19**; preprint Proposition 2.21) and the proof of **Theorem 6.7.1**, p. 278:
the inclusions `S_{F_t} → S_F`, `x ↦ (t, x)`, of the slices of the cobordism
`S_F ⊆ [0, 1] × X`.

# The inclusions of the ends into the cobordism

## What is formalized

* `MPolyfold.isScSmoothMap_const`: the constant map at a smooth point is sc-smooth.
* `MPolyfold.isScSmoothMap_into_subPolyfold`: a map into a sub-M-polyfold `A ⊆ X` is sc-smooth
  as soon as it is sc-smooth as a map into `X` (Proposition 2.3.19 (2)).
* `isScSmoothMap_cube_mk`: `x ↦ (t, x)` is an sc-smooth map `X → [0, 1]ⁿ × X`.
* `sliceInclusion`, `sliceInclusion_val`, `sliceInclusion_injective`,
  `range_sliceInclusion`: the map `j_t : S_{F_t} → S_F`, `x ↦ (t, x)`, a bijection onto
  `S_F ∩ (\{t\} × X)`.
* **`isScSmoothMap_sliceInclusion`**: `j_t` is an sc-smooth map between the sub-M-polyfolds
  `S_{F_t} ⊆ X` and `S_F ⊆ [0, 1] × X`, for every `t` for which both are sub-M-polyfolds (for
  `t ∈ \{0, 1\}` and `F` proper and in general position: `theorem_6_6_18_oriented_end`).
* `isEmbedding_sliceInclusion`: `j_t` is a topological embedding.
* `sliceIntoCube`, **`formsInftyAlong_sliceIntoCube_pullback`**: for a sub-M-polyfold `A ⊆ X`
  with a corner structure and `ι_t : A → [0, 1] × X`, `x ↦ (t, x)`: the pull-back along `ι_t`
  of `pr₂^*α`, `α ∈ Ωᵏ_∞(X)`, is the restriction `α|_A`.  For `A = S_{F_t}` this is the
  integrand of `∫_{S_{F_t}} α` read on the end `\{t\} × S_{F_t}` of the cobordism.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

namespace MPolyfold

section General

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The constant map at a smooth point is sc-smooth.** -/
theorem isScSmoothMap_const {x : X} (hx : x ∈ P.smoothSet) :
    Q.IsScSmoothMap P fun _ : Z => x := by
  obtain ⟨ψ, hψ, hxψ⟩ := P.exists_isChart_mem_source x
  have hsm : ψ x ∈ ψ.model.E.smooth := ψ.model.E.mem_smooth_iff.2 fun k =>
    (P.mem_levelSet_iff hψ hxψ).1 (mem_iInter.1 hx k)
  refine MPolyfold.isScSmoothMap_of_local fun z => ?_
  obtain ⟨φ, hφ, hz⟩ := Q.exists_isChart_mem_source z
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hz, subset_rfl, fun _ _ => hxψ, ?_⟩
  rw [φ.image_source]
  refine ⟨fun _ _ => ψ.mapsTo_model x hxψ, fun R _ => ?_⟩
  exact isScSmooth_const_of_mem_smooth R.isScDomain hsm

/-- **Maps into a sub-M-polyfold** (2021 Proposition 2.3.19 (2), p. 43): a map `g : Z → A` into
a sub-M-polyfold `A ⊆ X` whose composition with the inclusion `A → X` is sc-smooth is sc-smooth
(near `g(z)` it is `i⁻¹ ∘ r ∘ (i ∘ g)` for a retraction `r` onto `A`). -/
theorem isScSmoothMap_into_subPolyfold {A : Set X} (hA : P.IsSubMPolyfold A)
    [ParacompactSpace A] {g : Z → A} (hg : Q.IsScSmoothMap P fun z => (g z : X)) :
    Q.IsScSmoothMap (subPolyfold hA) g := by
  have hgc : Continuous fun z => (g z : X) := continuousOn_univ.1 hg.continuousOn
  refine IsScSmoothOn.of_locally isOpen_univ fun z _ => ?_
  set d := hA.data (g z).2 with hd
  have hU' : IsOpen ((fun z => (g z : X)) ⁻¹' d.V) := d.isOpen.preimage hgc
  have h1 : Q.IsScSmoothOn P (fun z => (g z : X)) ((fun z => (g z : X)) ⁻¹' d.V) :=
    IsScSmoothOn.mono hg hU' (subset_univ _)
  have h2 := (subPolyfold_retraction_isScSmooth hA d (g z)).comp h1 fun _ hw => hw
  refine ⟨_, hU', hA.mem_data_V (g z).2, subset_univ _, h2.congr fun w hw => ?_⟩
  refine Subtype.ext ?_
  change (d.retractInto (g z) (g w : X)).1 = (g w : X)
  rw [SubData.retractInto_val d (g z) hw]
  exact d.apply_eq_self ⟨(g w).2, hw⟩

end General

end MPolyfold

section Inclusion

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **`x ↦ (t, x)` is an sc-smooth map `X → [0, 1]ⁿ × X`**, for every `t ∈ [0, 1]ⁿ` (every point
of `[0, 1]ⁿ` is smooth). -/
theorem isScSmoothMap_cube_mk {n : ℕ} [ParacompactSpace ((Fin n → unitInterval) × X)]
    (t : Fin n → unitInterval) :
    PX.IsScSmoothMap ((cubePolyfold n).prod PX)
      fun x : X => ((t, x) : (Fin n → unitInterval) × X) := by
  have ht : t ∈ (cubePolyfold n).smoothSet :=
    ((cubePolyfold n).mem_smoothSet_iff (isChart_cChart t) (mem_cChart t)).2 (mem_smooth_rnSc _)
  exact IsScSmoothOn.prodMk (MPolyfold.isScSmoothMap_const ht) MPolyfold.isScSmoothMap_id

variable [ParacompactSpace ((Fin 1 → unitInterval) × X)]

/-- **The inclusion `j_t : S_{F_t} → S_F`**, `x ↦ (t, x)`, of the slice at `t` of the solution
set of `F = f̃ + S` over `[0, 1] × X`. -/
def sliceInclusion (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval)
    (x : solutionSet P (sectionAdd P f (prodSlice S t))) :
    solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) :=
  ⟨(t, x.1), isZeroAt_of_isZeroAt_slice hf hS x.2⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
@[simp] theorem sliceInclusion_val (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval)
    (x : solutionSet P (sectionAdd P f (prodSlice S t))) :
    (sliceInclusion hf hS t x : (Fin 1 → unitInterval) × X) = (t, x.1) :=
  rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- `j_t` is injective. -/
theorem sliceInclusion_injective (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval) :
    Function.Injective (sliceInclusion hf hS t) := fun _ _ h =>
  Subtype.ext (congrArg (fun z : solutionSet (pullbackProj P Prod.snd)
    (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) => z.1.2) h)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **The image of `j_t` is `S_F ∩ (\{t\} × X)`.** -/
theorem range_sliceInclusion (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval) :
    range (sliceInclusion hf hS t) = {z | z.1.1 = t} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hz
    obtain ⟨⟨t', x⟩, hzero⟩ := z
    obtain rfl : t' = t := hz
    have hx : x ∈ solutionSet P (sectionAdd P f (prodSlice S t')) := by
      rw [solutionSet_slice_eq_preimage hf hS t']
      exact hzero
    exact ⟨⟨x, hx⟩, rfl⟩

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **`j_t` is a topological embedding** of `S_{F_t}` into `S_F`. -/
theorem isEmbedding_sliceInclusion (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval) :
    Topology.IsEmbedding (sliceInclusion hf hS t) := by
  have h1 : Topology.IsEmbedding (fun x : X => ((t, x) : (Fin 1 → unitInterval) × X)) :=
    isEmbedding_prodMkRight t
  have h2 : Topology.IsEmbedding (fun x : solutionSet P (sectionAdd P f (prodSlice S t)) =>
      ((t, x.1) : (Fin 1 → unitInterval) × X)) := h1.comp Topology.IsEmbedding.subtypeVal
  exact Topology.IsEmbedding.of_comp
    (continuous_induced_rng.2 h2.continuous) continuous_subtype_val h2

omit [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- **The inclusion `S_{F_t} → S_F` is sc-smooth** (the proof of 2021 Theorem 6.7.1, p. 278):
for sub-M-polyfolds `S_{F_t} ⊆ X` and `S_F ⊆ [0, 1] × X`, the map `j_t(x) = (t, x)` is an
sc-smooth map between them. -/
theorem isScSmoothMap_sliceInclusion (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)))
    (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S t)))) :
    haveI := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
      (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))
    haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f (prodSlice S t)))
    (MPolyfold.subPolyfold hSt).IsScSmoothMap (MPolyfold.subPolyfold hSm)
      (sliceInclusion hf hS t) := by
  have := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
    (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))
  have := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f (prodSlice S t)))
  refine MPolyfold.isScSmoothMap_into_subPolyfold hSm ?_
  exact (isScSmoothMap_cube_mk (n := 1) t).comp (subPolyfold_inclusion_isScSmooth hSt)

end Inclusion

/-! ### The forms `pr₂^*α` on a slice -/

section SliceForms

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)] {A : Set X} [ParacompactSpace A]

/-- The map `ι_t : A → [0, 1] × X`, `x ↦ (t, x)`, on a sub-M-polyfold `A ⊆ X`, as an `ScMap`. -/
def sliceIntoCube (hA : PX.IsSubMPolyfold A) (t : Fin 1 → unitInterval) :
    ScMap (subPolyfold hA) (BundledMPolyfold.of ((cubePolyfold 1).prod PX)).P :=
  ⟨fun x => (t, x.1),
    (isScSmoothMap_cube_mk (n := 1) t).comp (subPolyfold_inclusion_isScSmooth hA)⟩

/-- **`ι_t^*(pr₂^*α) = α|_A`** (the proof of 2021 Theorem 6.7.1, p. 278: the form `pr₂^*α` on
the end `\{t\} × A` of a cobordism is `α` on `A`): for a sub-M-polyfold `A ⊆ X` with a corner
structure of dimension `n`, `t ∈ [0, 1]` and `α ∈ Ωᵏ_∞(X)`, the pull-back along
`ι_t(x) = (t, x)` of `pr₂^*α ∈ Ωᵏ_∞([0, 1] × X)` is the restriction of `α` to `A`
(`pr₂ ∘ ι_t` is the inclusion of `A`). -/
theorem formsInftyAlong_sliceIntoCube_pullback {hA : PX.IsSubMPolyfold A} {n k : ℕ}
    (hcs : (subPolyfold hA).HasCornerStructureOfDim n)
    [inst : ChartedSpace (EuclideanQuadrant n) A] (t : Fin 1 → unitInterval)
    (α : (BundledMPolyfold.of PX).formsInfty k) :
    formsInftyAlong k hcs (A := BundledMPolyfold.of ((cubePolyfold 1).prod PX))
        (sliceIntoCube hA t) (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) k α) =
      formsInftyRestrict k hcs α := by
  have h := LinearMap.congr_fun (formsInftyAlong_comp_formsInftyPullback (k := k) hcs
    (A := BundledMPolyfold.of ((cubePolyfold 1).prod PX)) (sliceIntoCube hA t)
    (B := BundledMPolyfold.of PX) (ivPrScMap PX)) α
  rw [LinearMap.comp_apply] at h
  exact h

end SliceForms

end Polyfold
