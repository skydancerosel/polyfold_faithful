import Polyfold.Chapter6.IntervalEndManifolds
import Polyfold.Chapter6.IntervalCobordismExistence
import Polyfold.Chapter6.Theorem671_2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Remark 6.6.19** (preprint Remark 6.42) and the proof of **Theorem 6.7.1**: cobordisms
`S_F ⊆ [0, 1] × X` which meet the two ends `\{0\} × X` and `\{1\} × X`.

# The `t`-constant cobordism, and an instance on the point

## What is formalized

* `prodSlice_cubeLift`: the slices of the `t`-constant lift `s̃` are `s`.
* **`constant_cobordism`**: let `s` be an sc⁺-section of `P` such that `f + s` has a compact
  solution set and is in general position at every zero, and let `f` have index `k` at every
  smooth point.  Then `S = s̃` is an sc⁺-section over `[0, 1] × X` for which `F = f̃ + S` is
  proper, in general position at every zero (zeros on `\{0, 1\} × X` included) and of index
  `k + 1` at every zero, and `S_F = [0, 1] × S_{f+s}`.  These are all hypotheses of
  `theorem_6_6_18_oriented_interval`, `theorem_6_6_18_oriented_end` and
  `tangentOr_ivFirst_eq_ray_iff_of_end` on `S`.
* `constant_cobordism_mem_ends`: every zero `x` of `f + s` gives the zeros `(0, x)` and `(1, x)`
  of `F`: the cobordism meets both ends when `S_{f+s} ≠ ∅`.
* `isIndexAt_ptSection`: the section `f = 0` of the zero bundle over the point has index `0`.
* **`interval_cobordism_witness`**: on the point `X = ℝ⁰` with the zero bundle and `f = 0`
  there is an sc⁺-section `S` over `[0, 1] × X` with `F = f̃ + S` proper, in general position
  at every zero and of index `1`, whose solution set contains `(t, 0)` for every `t ∈ [0, 1]`,
  in particular the end points `(0, 0)` and `(1, 0)`; the sections `F_0`, `F_1` are in general
  position at `0`.

## Reading

The instance on the point has fibres `0`; it is the example used for Theorem 6.7.1 itself
(`theorem_6_7_1_witness`).  For a general `f` the section `S = s̃` of `constant_cobordism` exists
for every admissible `s` (`exists_isAdmissible`), and `S_F` meets the ends exactly when
`S_{f+s}` is not empty.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

section Constant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slices of the `t`-constant lift `s̃` of `s` are `s`. -/
theorem prodSlice_cubeLift {n : ℕ} {s : X → Y} (hs : IsSection P s)
    (t : Fin n → unitInterval) : prodSlice (cubeLift (n := n) s hs) t = s :=
  rfl

variable [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]

/-- **The `t`-constant cobordism** (2021 Remark 6.6.19, p. 276): let `f` be a tame sc-Fredholm
section of index `k` at every smooth point over an `X` with sc-smooth bump functions, and `s` an
sc⁺-section such that `f + s` has a compact solution set and is in general position at every
zero.  Then `S = s̃`, the `t`-constant lift of `s` to `[0, 1] × X`, is an sc⁺-section, and
`F = f̃ + S` is proper, in general position at every zero (the zeros on `\{0, 1\} × X` included)
and of index `k + 1` at every zero, with `S_F = [0, 1] × S_{f+s}`. -/
theorem constant_cobordism (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
    {s : X → Y} (hs : B.IsScPlusSection s)
    (hc : IsCompact (solutionSet P (sectionAdd P f s)))
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x →
      B.IsGeneralPositionGerm (sectionAdd P f s) x)
    {k : ℕ} (hk : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x k) :
    (ivBundle B).IsScPlusSection (cubeLift (n := 1) s hs.1) ∧
      (ivBundle B).IsProper (sectionAdd (pullbackProj P Prod.snd)
        (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) ∧
      (∀ z, IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
          (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) z →
        (ivBundle B).IsGeneralPositionGerm (sectionAdd (pullbackProj P Prod.snd)
          (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) z) ∧
      (∀ z, IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
          (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) z →
        (ivBundle B).IsLinOfIndex (sectionAdd (pullbackProj P Prod.snd)
          (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) z (k + 1 : ℕ)) ∧
      solutionSet (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
          (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) =
        univ ×ˢ solutionSet P (sectionAdd P f s) := by
  have hSp : (ivBundle B).IsScPlusSection (cubeLift (n := 1) s hs.1) :=
    isScPlusSection_cubeLift hs
  have hfc := (hf.paramCube (n := 1)).toIsScFredholmSection
  have hsol : solutionSet (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) =
      univ ×ˢ solutionSet P (sectionAdd P f s) := by
    rw [sectionAdd_cubeLift hf.isScSmooth.1 hs.1]
    exact solutionSet_cubeLift _
  have hzero : ∀ z : (Fin 1 → unitInterval) × X, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1)
        (cubeLift (n := 1) s hs.1)) z → IsZeroAt P (sectionAdd P f s) z.2 := fun z hz => by
    have h : z ∈ solutionSet (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) s hs.1)) := hz
    rw [hsol] at h
    exact h.2
  refine ⟨hSp, ?_, fun z hz => ?_, fun z hz => ?_, hsol⟩
  · refine theorem_5_2_2_preprint (theorem_3_1_18_preprint hfc hSp) ?_
    rw [hsol]
    exact isCompact_univ.prod hc
  · obtain ⟨t, x⟩ := z
    exact isGeneralPositionGerm_cubeLift_add_of_slice hf hSp hz (hgp x (hzero _ hz))
  · obtain ⟨t, x⟩ := z
    have hzs := (theorem_3_1_18_preprint hfc hSp).mem_smoothSet_of_isZeroAt hz
    have h := isLinOfIndex_interval_of_isIndexAt hbump hf hSp hz
      (hk x (prod_cube_mem_smoothSet_iff.1 hzs))
    have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [hcast]
    exact h

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **The `t`-constant cobordism meets both ends**: a zero `x` of `f + s` gives the zeros
`(t, x)` of `F = f̃ + s̃` for every `t ∈ [0, 1]`, in particular `(0, x)` and `(1, x)`. -/
theorem constant_cobordism_mem_ends (hf : IsSection P f) {s : X → Y} (hs : IsSection P s)
    {x : X} (hx : IsZeroAt P (sectionAdd P f s) x) (t : Fin 1 → unitInterval) :
    IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf) (cubeLift (n := 1) s hs)) (t, x) := by
  have h : ((t, x) : (Fin 1 → unitInterval) × X) ∈ solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf)
        (cubeLift (n := 1) s hs)) := by
    rw [sectionAdd_cubeLift hf hs, solutionSet_cubeLift]
    exact ⟨mem_univ _, hx⟩
  exact h

end Constant

/-! ### An instance on the point -/

section Point

open TrivialBundle

/-- **The section `f = 0` of the zero bundle over the point has index `0`** (Definition 6.2.1):
for an admissible `s` the point is a zero of `f + s`, it lies in one of the parts `S_k`, and
`S_k` is a `k`-dimensional manifold with one point, so `k = 0`. -/
theorem isIndexAt_ptSection (x : Fin 0 → ℝ) : (bundle 0 0).IsIndexAt ptSection x (0 : ℕ) := by
  have hf := isScFredholmSectionTame_ptSection
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := bundle 0 0)
  obtain ⟨s, hs⟩ := exists_isAdmissible (U := univ) rnPolyfold_isTame
    rnPolyfold_zero_admitsBumpFunctions hf (Set.toFinite _).isCompact hN isOpen_univ
    (subset_univ _)
  have hz : x ∈ solutionSet (proj 0 0) (sectionAdd (proj 0 0) ptSection s) :=
    Subsingleton.elim (α := (Fin 0 → ℝ) × (Fin 0 → ℝ)) _ _
  rw [solutionSet_eq_iUnion_solPart hf hs.isScPlusSection hs.gp] at hz
  obtain ⟨k, hk⟩ := mem_iUnion.1 hz
  let := solPartChartedSpace rnPolyfold_isTame hf hs k
  obtain rfl : k = 0 := eq_zero_of_subsingleton_chartedSpace
    (⟨_, hk⟩ : ↥((bundle 0 0).solPart ptSection s k))
  rw [solPart_eq] at hk
  exact hk.2

/-- **A cobordism over `[0, 1] × X` meeting both ends** (non-vacuity of the hypotheses of
`theorem_6_6_18_oriented_interval`, `theorem_6_6_18_oriented_end` and
`tangentOr_ivFirst_eq_ray_iff_of_end`; not in the text): on the point `X = ℝ⁰` with the zero
bundle and `f = 0` there is an sc⁺-section `S` over `[0, 1] × X` such that `F = f̃ + S` is proper,
in general position at every zero and of index `1` at every zero, `(t, 0)` is a zero of `F` for
every `t ∈ [0, 1]` (so `S_F` contains points of `\{0\} × X` and of `\{1\} × X`), and for
`t ∈ \{0, 1\}` the section `F_t` is in general position at its zero `0`. -/
theorem interval_cobordism_witness :
    haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (rnPolyfold 0)
    haveI := paracompactSpace_pullbackSpace
      (f := (Prod.snd : (Fin 1 → unitInterval) × (Fin 0 → ℝ) → (Fin 0 → ℝ)))
      ((cubePolyfold 1).prod (rnPolyfold 0)) (bundle 0 0)
    ∃ S : (Fin 1 → unitInterval) × (Fin 0 → ℝ) →
        pullbackSpace (proj 0 0) (Prod.snd : (Fin 1 → unitInterval) × (Fin 0 → ℝ) → _),
      (ivBundle (bundle 0 0)).IsScPlusSection S ∧
      (ivBundle (bundle 0 0)).IsProper (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
        (cubeLift (n := 1) ptSection isScFredholmSectionTame_ptSection.isScSmooth.1) S) ∧
      (∀ z, IsZeroAt (pullbackProj (proj 0 0) Prod.snd)
          (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
            (cubeLift (n := 1) ptSection isScFredholmSectionTame_ptSection.isScSmooth.1) S) z →
        (ivBundle (bundle 0 0)).IsGeneralPositionGerm
          (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
            (cubeLift (n := 1) ptSection isScFredholmSectionTame_ptSection.isScSmooth.1) S) z) ∧
      (∀ z, IsZeroAt (pullbackProj (proj 0 0) Prod.snd)
          (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
            (cubeLift (n := 1) ptSection isScFredholmSectionTame_ptSection.isScSmooth.1) S) z →
        (ivBundle (bundle 0 0)).IsLinOfIndex
          (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
            (cubeLift (n := 1) ptSection isScFredholmSectionTame_ptSection.isScSmooth.1) S) z
          (0 + 1 : ℕ)) ∧
      (∀ t : Fin 1 → unitInterval, IsZeroAt (pullbackProj (proj 0 0) Prod.snd)
          (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
            (cubeLift (n := 1) ptSection isScFredholmSectionTame_ptSection.isScSmooth.1) S)
          (t, 0)) ∧
      ∀ t : Fin 1 → unitInterval, (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 →
        (bundle 0 0).IsGeneralPositionGerm (sectionAdd (proj 0 0) ptSection (prodSlice S t))
          0 := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (rnPolyfold 0)
  have := paracompactSpace_pullbackSpace
    (f := (Prod.snd : (Fin 1 → unitInterval) × (Fin 0 → ℝ) → (Fin 0 → ℝ)))
    ((cubePolyfold 1).prod (rnPolyfold 0)) (bundle 0 0)
  have hf := isScFredholmSectionTame_ptSection
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := bundle 0 0)
  obtain ⟨s, hs⟩ := exists_isAdmissible (U := univ) rnPolyfold_isTame
    rnPolyfold_zero_admitsBumpFunctions hf (Set.toFinite _).isCompact hN isOpen_univ
    (subset_univ _)
  obtain ⟨hSp, hP, hgp, hidx, -⟩ := constant_cobordism rnPolyfold_zero_admitsBumpFunctions hf
    hs.isScPlusSection (Set.toFinite _).isCompact hs.gp (k := 0)
    fun x _ => isIndexAt_ptSection x
  have hx0 : IsZeroAt (proj 0 0) (sectionAdd (proj 0 0) ptSection s) (0 : Fin 0 → ℝ) :=
    Subsingleton.elim (α := (Fin 0 → ℝ) × (Fin 0 → ℝ)) _ _
  have hz : ∀ t : Fin 1 → unitInterval, IsZeroAt (pullbackProj (proj 0 0) Prod.snd)
      (sectionAdd (pullbackProj (proj 0 0) Prod.snd)
        (cubeLift (n := 1) ptSection hf.isScSmooth.1)
        (cubeLift (n := 1) s hs.isScPlusSection.1)) (t, 0) := fun t =>
    constant_cobordism_mem_ends hf.isScSmooth.1 hs.isScPlusSection.1 hx0 t
  exact ⟨cubeLift (n := 1) s hs.isScPlusSection.1, hSp, hP, hgp, hidx, hz, fun t ht =>
    isGeneralPositionGerm_slice_of_end hf hSp ht (hz t) (hgp _ (hz t))⟩

end Point

end Polyfold
