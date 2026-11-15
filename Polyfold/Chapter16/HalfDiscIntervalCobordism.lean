import Polyfold.Chapter16.CanonicalOrientationWitness
import Polyfold.Chapter6.IntervalConstantCobordism
import Polyfold.Chapter6.CornerSmoothMaps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Remark 6.6.19** and the proof of **Theorem 6.7.1**, on an example with boundary and non-zero
fibres.

# A cobordism over `[0, 1] × H` with non-zero fibres

## The text, paraphrased

(Remark 6.6.19, p. 276) For an oriented sc-Fredholm section `(f, o)` over a tame `X` and an
sc⁺-section `S` over `[0, 1] × X` with `F = f̃ + S` proper and in general position, the solution
set `S_F` is a compact oriented manifold with boundary and corners.  The text gives no example.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

`X = H = [0, ∞) × ℝ` (so `∂X ≠ ∅`), the bundle is `H × ℝ → H` (fibres `ℝ`), and
`f(a, y) = ((a, y), a² + y² − 1)`, whose solution set is the half circle; it meets `∂H` in
`(0, ±1)`.

* `isGeneralPositionGerm_graphSection_of_presentation`: Part I's general position (Definition
  5.3.9) for the graph section of a `C^∞` map `φ` at a zero `x₀`: `Dφ(x₀)` onto on the minimal
  subspace of a presentation of the partial quadrant of the centred chart.
  `isGeneralPositionGerm_graphSection_boundary`, `isGeneralPositionGerm_graphSection_interior`:
  the two cases `x₀ ∈ ∂H` (`Dφ(x₀)` onto on `\{0\} × ℝᵐ`) and `x₀ ∉ ∂H` (`Dφ(x₀)` onto).
* `isGeneralPositionGerm_halfDisc`: `f` is in general position at every zero.
* `halfDiscOrientation`: an orientation of `f` (Definition 6.6.16).
* **`interval_cobordism_halfDisc`**: for `S = 0` the section `F = f̃ + S` over `[0, 1] × H`
  satisfies every hypothesis of `theorem_6_6_18_oriented_interval`,
  `theorem_6_6_18_oriented_end` and `stokes_interval_cobordism` with the orientation
  `halfDiscOrientation` and the index `1` of `f` (index `2` of `F`): `H` is tame with sc-smooth
  bump functions, `f` has tame germ data and index `1` at every point, `S` is sc⁺, `F` is proper,
  in general position at every zero and of index `2`; `∂H ≠ ∅`, the fibres are non-zero,
  `S_F = [0, 1] × S_f`, and the corner point `(0, (0, 1))` of `[0, 1] × H` is a zero of `F`.
* **`restrictForm_sliceInclusion_halfDisc`**: for this instance and `t = 0`, the solution sets
  `S_{F_0}` (non-empty, of dimension `1`) and `S_F` (of dimension `2`) are sub-M-polyfolds with
  corner structures, the inclusion `j_0 : S_{F_0} → S_F` is `C^∞` between the Mathlib manifolds
  with corners, and `j_0^*((pr₂^*α)|_{S_F}) = α|_{S_{F_0}}` for every `α ∈ Ω¹_∞(H)`
  (`contMDiff_sliceInclusion`, `restrictForm_sliceInclusion_pullback`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold UnitCube

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-! ### General position of a graph section (Definition 5.3.9) -/

/-- **General position of the graph section at a zero** (Definition 5.3.9, p. 220): if
`φ(x₀) = 0` and `Dφ(x₀)` maps the minimal subspace at `0` of a presentation `T` of the partial
quadrant of the chart centred at `x₀` onto `ℝᵏ`, then the graph section of `φ` is in general
position at `x₀`: `Dφ(x₀)` is onto and `ker Dφ(x₀) + T^R = ℝ ⊕ ℝᵐ`. -/
theorem isGeneralPositionGerm_graphSection_of_presentation (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso (halfSpaceSc m) ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : (chartAt (k := k) x₀).φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (honto : ∀ w : Fin k → ℝ, ∃ v : Pm m, v ∈ minimalSubspaceWith T 0 ∧
      fderiv ℝ φ (x₀ : Pm m) v = w) :
    (bundle m k).IsGeneralPositionGerm (graphSection φ) x₀ := by
  have hft : (bundle m k).IsScFredholmSectionTame (graphSection φ) :=
    isScFredholmSectionTame_graphSection_halfSEP hφ
  have htop : rangeS (scDeriv (chartAt (k := k) x₀).U (r (chartAt (k := k) x₀).R) 0) = ⊤ := by
    rw [rangeS, scDeriv_r_chartAt]
    exact LinearMap.range_id
  have hmem : ∀ v : (halfSpaceSc m) 0,
      v ∈ rangeS (scDeriv (chartAt (k := k) x₀).U (r (chartAt (k := k) x₀).R) 0) := fun v => by
    rw [htop]
    trivial
  have hlin : ∀ v : Pm m, linAt (chartAt (k := k) x₀).U (chartAt (k := k) x₀).R
      ((chartAt (k := k) x₀).principal (graphSection φ)) 0 ⟨v, hmem v⟩ =
        (fderiv ℝ φ (x₀ : Pm m) v : Fin k → ℝ) := fun v => by
    rw [linAt_apply]
    exact congrFun (congrArg DFunLike.coe (scDeriv_principal_comp_r_chartAt hφ x₀)) v
  refine isGeneralPositionGerm_of_sup_eq hft (isZeroAt_graphSection_iff.2 h0)
    (isTameChart_chartAt x₀) (mem_source_chartAt x₀) (chartAt_self x₀) T hT (fun q _ => ?_) ?_
  · obtain ⟨v, -, hv⟩ := honto q
    exact ⟨⟨v, hmem v⟩, (hlin v).trans hv⟩
  · refine le_antisymm (sup_le ((chartAt (k := k) x₀).linKer_le _ 0) inf_le_left) fun v _ => ?_
    obtain ⟨e, he, hev⟩ := honto (fderiv ℝ φ (x₀ : Pm m) v)
    have hk : (show Pm m from v) - e ∈ (chartAt (k := k) x₀).linKer (graphSection φ) 0 :=
      ((chartAt (k := k) x₀).mem_linKer_iff _ 0 _).2 ⟨hmem _, by
        exact (hlin _).trans (by rw [map_sub, hev, sub_self]; rfl)⟩
    have hred : e ∈ reducedTangentSpaceWith
        ((chartAt (k := k) x₀).isRetraction.baseRetraction (chartAt (k := k) x₀).relOpen) T 0 := by
      refine ⟨hmem e, ?_⟩
      have hb0 : (halfSpaceSc m).toBase 1 (0 : (halfSpaceSc m) 1) = 0 := map_zero _
      change e ∈ minimalSubspaceWith T ((halfSpaceSc m).toBase 1 (0 : (halfSpaceSc m) 1))
      rw [hb0]
      exact he
    have e' : v = ((show Pm m from v) - e) + e := (sub_add_cancel _ _).symm
    rw [e']
    exact Submodule.add_mem_sup hk hred

/-- **General position at a boundary zero**: if `x₀ ∈ ∂H`, `φ(x₀) = 0` and `Dφ(x₀)` maps the
hyperplane `\{0\} × ℝᵐ = T^R_{x₀}H` onto `ℝᵏ`, the graph section is in general position at
`x₀`. -/
theorem isGeneralPositionGerm_graphSection_boundary (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) (hb : (x₀ : Pm m).1 0 = 0)
    (honto : ∀ w : Fin k → ℝ, ∃ v : Pm m, v.1 0 = 0 ∧ fderiv ℝ φ (x₀ : Pm m) v = w) :
    (bundle m k).IsGeneralPositionGerm (graphSection φ) x₀ := by
  refine isGeneralPositionGerm_graphSection_of_presentation hφ h0 (ScIso.refl (halfSpaceSc m))
    ((C_chartAt x₀).trans (by rw [if_pos hb]; ext; rfl)) fun w => ?_
  obtain ⟨v, hv0, hv⟩ := honto w
  exact ⟨v, (mem_minimalSubspaceWith (ScIso.refl (halfSpaceSc m))).2 fun i _ => by
    rw [Subsingleton.elim i 0]; exact hv0, hv⟩

/-- **General position at an interior zero**: if `x₀ ∉ ∂H`, `φ(x₀) = 0` and `Dφ(x₀)` is onto
`ℝᵏ`, the graph section is in general position at `x₀`. -/
theorem isGeneralPositionGerm_graphSection_interior (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) (hb : (x₀ : Pm m).1 0 ≠ 0)
    (honto : Surjective (fderiv ℝ φ (x₀ : Pm m))) :
    (bundle m k).IsGeneralPositionGerm (graphSection φ) x₀ := by
  refine isGeneralPositionGerm_graphSection_of_presentation hφ h0 (interiorPresentation m) ?_
    fun w => ?_
  · refine (C_chartAt x₀).trans ?_
    rw [if_neg hb]
    exact (eq_univ_of_forall fun v i => i.elim0).symm
  · obtain ⟨v, hv⟩ := honto w
    exact ⟨v, (mem_minimalSubspaceWith (interiorPresentation m)).2 fun i _ => i.elim0, hv⟩

/-! ### The half-disc section -/

/-- **`f(a, y) = ((a, y), a² + y² − 1)` is in general position at every zero** (Definition
5.3.9), the two zeros `(0, ±1)` on `∂H` included. -/
theorem isGeneralPositionGerm_halfDisc {x : H 1}
    (hx : IsZeroAt (proj 1 1) (graphSection halfDiscMap) x) :
    (bundle 1 1).IsGeneralPositionGerm (graphSection halfDiscMap) x := by
  have h0 : halfDiscMap (x : Pm 1) = 0 := isZeroAt_graphSection_iff.1 hx
  by_cases hb : (x : Pm 1).1 0 = 0
  · exact isGeneralPositionGerm_graphSection_boundary contDiff_halfDiscMap h0 hb
      (halfDiscMap_onto_hyperplane h0 hb)
  · exact isGeneralPositionGerm_graphSection_interior contDiff_halfDiscMap h0 hb
      (surjective_fderiv_halfDiscMap hb)

/-- **An orientation of `f(a, y) = ((a, y), a² + y² − 1)`** (Definition 6.6.16): the continuous
section `halfOrientation` of `σ : O_f → H`. -/
def halfDiscOrientation : SectionOrientation (B := bundle 1 1) (graphSection halfDiscMap)
    (isScFredholmSectionTame_graphSection_halfSEP
      (k := 1) contDiff_halfDiscMap).toIsScFredholmSection :=
  ⟨halfOrientation contDiff_halfDiscMap, isSectionOrientation_halfOrientation contDiff_halfDiscMap⟩

/-- `S_f` is compact: the half circle. -/
theorem isCompact_solutionSet_halfDisc :
    IsCompact (solutionSet (proj 1 1) (graphSection halfDiscMap)) := by
  have h : solutionSet (proj 1 1) (graphSection halfDiscMap) =
      ((↑) : H 1 → (halfSpaceSc 1) 0) ⁻¹' (halfDiscMap ⁻¹' {0}) := solutionSet_halfDisc
  rw [h]
  exact (quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.isCompact_preimage
    isCompact_halfDiscMap_zero

/-- **A cobordism over `[0, 1] × H` with `∂H ≠ ∅` and fibres `ℝ`** (non-vacuity of the
hypotheses of `theorem_6_6_18_oriented_interval`, `theorem_6_6_18_oriented_end` and
`stokes_interval_cobordism`; not in the text).  For `H = [0, ∞) × ℝ`, the bundle `H × ℝ → H`,
`f(a, y) = ((a, y), a² + y² − 1)` with the orientation `halfDiscOrientation`, and the
sc⁺-section `S = 0` over `[0, 1] × H`: `H` is tame with sc-smooth bump functions and non-empty
boundary, the fibres are non-zero, `f` has tame germ data and index `1` at every point, and
`F = f̃ + S` is proper, in general position at every zero (those over `\{0, 1\} × H` and over
`[0, 1] × ∂H` included) and of index `2` at every zero; `S_F = [0, 1] × S_f`, and the corner
point `(0, (0, 1))` is a zero of `F`. -/
theorem interval_cobordism_halfDisc :
    haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)
    haveI := paracompactSpace_pullbackSpace
      (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
      ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)
    (basePoly 1).IsTame ∧ (basePoly 1).AdmitsBumpFunctions ∧
    (basePoly 1).boundary.Nonempty ∧ (∀ y : H 1, Nontrivial (proj 1 1 ⁻¹' {y})) ∧
    ∃ hf : (bundle 1 1).IsScFredholmSectionTame (graphSection halfDiscMap),
      Nonempty (SectionOrientation (B := bundle 1 1) (graphSection halfDiscMap)
        hf.toIsScFredholmSection) ∧
      (∀ x ∈ (basePoly 1).smoothSet, (bundle 1 1).IsIndexAt (graphSection halfDiscMap) x (1 : ℕ)) ∧
      ∃ S : (Fin 1 → unitInterval) × H 1 →
          pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → _),
        (ivBundle (bundle 1 1)).IsScPlusSection S ∧
        (ivBundle (bundle 1 1)).IsProper (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
          (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) ∧
        (∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
            (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
              (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z →
          (ivBundle (bundle 1 1)).IsGeneralPositionGerm
            (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
              (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z) ∧
        (∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
            (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
              (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z →
          (ivBundle (bundle 1 1)).IsLinOfIndex
            (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
              (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z
            (1 + 1 : ℕ)) ∧
        solutionSet (pullbackProj (proj 1 1) Prod.snd)
            (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
              (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) =
          univ ×ˢ solutionSet (proj 1 1) (graphSection halfDiscMap) ∧
        topPoint ∈ (basePoly 1).boundary ∧
        ∀ t : Fin 1 → unitInterval, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
          (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
            (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) (t, topPoint) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)
  have := paracompactSpace_pullbackSpace
    (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
    ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)
  have hX : (basePoly 1).IsTame := isTame_halfSEP 1 1
  have hbump : (basePoly 1).AdmitsBumpFunctions := admitsBumpFunctions_halfSEP 1 1
  have hf : (bundle 1 1).IsScFredholmSectionTame (graphSection halfDiscMap) :=
    isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap
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
  refine ⟨hX, hbump, ⟨_, zero_mem_boundary_halfSEP 1 1⟩, nontrivial_fibre_halfSEP 1 1, hf,
    ⟨halfDiscOrientation⟩, hk, cubeLift (n := 1) (fiberZero (proj 1 1)) hs0.1, hSp, hP, hgp,
    hidx, ?_, topPoint_mem_boundary, fun t => constant_cobordism_mem_ends hsec hs0.1 htop t⟩
  rw [hsol, hadd]

local notation "𝓠" => modelWithCornersEuclideanQuadrant

set_option maxHeartbeats 1600000 in
-- the solution sets carry the structures of `theorem_6_6_18_solutionSet`, unfolded twice
/-- **The inclusion of the end `\{0\} × S_{F_0}` on the half-disc example** (an instance of
`contMDiff_sliceInclusion` and `restrictForm_sliceInclusion_pullback` with `∂X ≠ ∅` and
non-zero fibres; not in the text): for `H = [0, ∞) × ℝ`, `f(a, y) = ((a, y), a² + y² − 1)` and
an sc⁺-section `S` over `[0, 1] × H` with `F = f̃ + S` proper and in general position, at `t = 0`:
`S_{F_0} ⊆ H` and `S_F ⊆ [0, 1] × H` are sub-M-polyfolds with corner structures of dimensions
`1` and `2`, `S_{F_0}` contains the boundary point `(0, 1)` of `H`, the inclusion
`j_0 : S_{F_0} → S_F` is `C^∞`, and `j_0^*((pr₂^*α)|_{S_F}) = α|_{S_{F_0}}` for every
`α ∈ Ω¹_∞(H)`. -/
theorem restrictForm_sliceInclusion_halfDisc :
    haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)
    haveI := paracompactSpace_pullbackSpace
      (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
      ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)
    ∃ (hf : (bundle 1 1).IsScFredholmSectionTame (graphSection halfDiscMap))
      (S : (Fin 1 → unitInterval) × H 1 →
        pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → _))
      (hS : IsSection (pullbackProj (proj 1 1) Prod.snd) S)
      (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSubMPolyfold
        (solutionSet (pullbackProj (proj 1 1) Prod.snd)
          (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
            (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S)))
      (t : Fin 1 → unitInterval)
      (hSt : (basePoly 1).IsSubMPolyfold
        (solutionSet (proj 1 1) (sectionAdd (proj 1 1) (graphSection halfDiscMap)
          (prodSlice S t)))),
      (t 0 : ℝ) = 0 ∧
      IsZeroAt (proj 1 1) (sectionAdd (proj 1 1) (graphSection halfDiscMap) (prodSlice S t))
        topPoint ∧
      letI := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
        (solutionSet (pullbackProj (proj 1 1) Prod.snd)
          (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
            (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
      letI := (basePoly 1).paracompactSpace_subtype
        (solutionSet (proj 1 1) (sectionAdd (proj 1 1) (graphSection halfDiscMap)
          (prodSlice S t)))
      ∃ (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim 1)
        (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (1 + 1)),
        letI := (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs
        letI := (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs'
        ContMDiff (𝓠 1) (𝓠 (1 + 1)) ∞ (sliceInclusion hf.isScSmooth.1 hS t) ∧
        ∀ α : (BundledMPolyfold.of (basePoly 1)).formsInfty 1,
          restrictForm (sliceInclusion hf.isScSmooth.1 hS t)
              (formsInftyRestrict 1 hcs'
                (BundledMPolyfold.formsInftyPullback (ivPrScMap (basePoly 1)) 1 α)) =
            formsInftyRestrict 1 hcs α := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)
  have := paracompactSpace_pullbackSpace
    (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
    ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)
  have h := interval_cobordism_halfDisc
  obtain ⟨hX, hbump, -, -, hf, ho, hk, S, hSp, hP, hgp, hidx, -, -, hz⟩ := h
  obtain ⟨o⟩ := ho
  obtain ⟨t, ht0⟩ : ∃ t : Fin 1 → unitInterval, (t 0 : ℝ) = 0 := ⟨fun _ => 0, rfl⟩
  obtain ⟨hPt, hgpt, hidxt, -⟩ := theorem_6_6_18_oriented_end hX hbump hf o hSp hP hgp hk
    (t := t) (Or.inl ht0)
  have hD := (theorem_6_6_18_solutionSet (prod_cube_isTame hX)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hSp) hP hgp).isSubmanifoldOfDim
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hSp) hidx
  have hDt := (theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hSp.cubeSlice t)) hPt
    hgpt).isSubmanifoldOfDim (theorem_3_1_18_tame hf (hSp.cubeSlice t)) hidxt
  let _ := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
    (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
  let _ := (basePoly 1).paracompactSpace_subtype
    (solutionSet (proj 1 1) (sectionAdd (proj 1 1) (graphSection halfDiscMap)
      (prodSlice S t)))
  have hcs' := hD.hasCornerStructureOfDim_of_tame (prod_cube_isTame hX)
    ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
      (theorem_3_1_18_tame (hf.paramCube (n := 1)) hSp) hP hgp).isGoodPositionAt
      (prod_cube_isTame hX))
  have hcs := hDt.hasCornerStructureOfDim_of_tame hX
    ((theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hSp.cubeSlice t)) hPt
      hgpt).isGoodPositionAt hX)
  refine ⟨hf, S, hSp.1, ?_⟩
  refine ⟨hD.1.isSubMPolyfold, t, ?_⟩
  refine ⟨hDt.1.isSubMPolyfold, ht0, ?_, ?_⟩
  · exact isZeroAt_slice_of_isZeroAt hf hSp (hz t)
  refine ⟨hcs, hcs', ?_, fun α => ?_⟩
  · exact contMDiff_sliceInclusion
      (inst := (MPolyfold.subPolyfold hDt.1.isSubMPolyfold).cornerChartedSpace hcs)
      (inst' := (MPolyfold.subPolyfold hD.1.isSubMPolyfold).cornerChartedSpace hcs')
      hf.isScSmooth.1 hSp.1 t hD.1.isSubMPolyfold hDt.1.isSubMPolyfold hcs rfl hcs' rfl
  · exact restrictForm_sliceInclusion_pullback
      (inst := (MPolyfold.subPolyfold hDt.1.isSubMPolyfold).cornerChartedSpace hcs)
      (inst' := (MPolyfold.subPolyfold hD.1.isSubMPolyfold).cornerChartedSpace hcs')
      hf.isScSmooth.1 hSp.1 t hD.1.isSubMPolyfold hDt.1.isSubMPolyfold hcs rfl hcs' rfl α

end HalfSpaceBundle

end Polyfold
