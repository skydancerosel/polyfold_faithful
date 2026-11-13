import Polyfold.Chapter9.Measure
import Polyfold.Chapter9.GapP1_Stokes2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5, the paragraph
before **Definition 9.5.14** (p. 448; 2017: before Definition 9.17, p. 327): `(n-1)`-dimensional
measure zero in the boundary faces (gap G.108).

# Measure zero in the boundary faces, and a witness for `L(∂S)`

## The text, paraphrased

(p. 448) For `K ⊆ |∂M_U|` the preimages lie in the `∂Mᵢ`; `Mᵢ`, being tame, is a manifold with
boundary with corners, and one takes the intersection of the set with every boundary face, where
`(n-1)`-dimensional Lebesgue measure zero makes sense.

## What is formalized

* `MPolyfold.IsFaceNull`: for a face-structured `Q` with a corner structure of dimension `n + 1`
  (a tame sheet), `K` has **measure zero face by face** if for every face `F` of `Q`, a manifold
  modelled on `[0,∞)ⁿ` (`faceChartedSpace`), `K ∩ F` has measure zero in `F` (Definition 9.4.5,
  `IsMeasureZero`).  `isFaceNull_empty`, `IsFaceNull.mono`, `isFaceNull_iUnion`,
  `isFaceNull_of_forall_disjoint` (a set meeting no face), `not_isFaceNull_face` (a face is not
  null): the face-by-face notion is a proper σ-ideal.  `not_isMeasureZero_univ_quadrant`: a
  nonempty manifold modelled on `[0,∞)ⁿ` is not a null set.
* `SheetNullSets.point`: the `0`-dimensional null sets (counting measure: only `∅ ∩ N`), a
  null-set system on every class of sets, with no hypothesis; the boundary faces of a
  `1`-dimensional sheet are points.
* `EpGroupoid.isMeasureZeroBoundary_point_iff`: for these null sets, `K` has measure zero in
  `∂S = |supp(∂Θ)|` iff `K ∩ ∂S = ∅`; `lebesgueSigmaBoundary_point`: `L(∂S)` is then the Borel
  σ-algebra of `∂S`.
* **The witness with `∂S ≠ ∅`**: `Θ = 1` on the half-line `[0, ∞)`, a tame branched
  ep⁺-subgroupoid of dimension `1` (`halfLineTame`): `halfLine_orbitSupp_boundary_nonempty`
  (`|0| ∈ ∂S`), `halfLine_isMeasureZeroBoundary_iff`, `halfLine_not_isMeasureZeroBoundary`
  (`∂S` is not null) and `halfLine_lebesgueSigmaBoundary` (`L(∂S) = B(∂S)`).

## Not formalized

For `n ≥ 2`, the face-by-face null sets as a `SheetNullSets` on the class of the boundaries `∂Mᵢ`
of the sheets of a general M-polyfold: its field `isNull_transfer` (two boundaries induce the
same null sets on their intersection) needs the smooth retractions between sheets, as for
Lemma 9.5.2 (gap G.106), and sheets need not be face-structured globally.  (2026-11-12) With
the intrinsic null sets `MPolyfold.IsHNull P (n - 1)` of `GapP2_DSheetNull.lean` and
`MPolyfold.hNullSets` (`GapP2_DSheetMeasure.lean`) the transfer field is automatic; what remains
is that a nonempty `∂M` of a tame `n`-dimensional sheet is not `(n - 1)`-null.  (2026-11-13) Proved
(`not_isHNull_submanifoldBoundary`, `GapP2_E5_BoundaryNull.lean`); the boundary null-set system
for every `n` is `boundaryNullSets` (`GapP2_E5_BoundaryNullSigma.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-! ### A nonempty manifold modelled on `[0,∞)ⁿ` is not null -/

section Quadrant

variable {n : ℕ}

/-- The open quadrant `(0,∞)ⁿ` is open. -/
theorem isOpen_setOf_forall_pos :
    IsOpen {z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (EuclideanSpace.proj i).continuous

/-- A neighbourhood in `ℝⁿ` of a point of `[0,∞)ⁿ` meets `(0,∞)ⁿ`. -/
theorem exists_forall_pos_mem {y : EuclideanSpace ℝ (Fin n)} (hy : ∀ i, 0 ≤ y i)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : W ∈ 𝓝 y) : ∃ z ∈ W, ∀ i, 0 < z i := by
  set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun _ => 1
  set f : ℝ → EuclideanSpace ℝ (Fin n) := fun t => y + t • v with hf
  have hc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have h0 : f 0 = y := by simp [hf]
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ W :=
    ((h0 ▸ hc.tendsto 0).eventually hW).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htW, ht⟩ := (h1.and self_mem_nhdsWithin).exists
  refine ⟨f t, htW, fun i => ?_⟩
  have hi := hy i
  have ht' : (0 : ℝ) < t := ht
  simp only [hf, v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (𝓠 n) ∞ M]

/-- **A nonempty manifold modelled on `[0,∞)ⁿ` does not have measure zero** (Definition 9.4.5 is
not vacuous on manifolds with corners): the image of a chart contains a nonempty open subset of
`(0,∞)ⁿ`. -/
theorem not_isMeasureZero_univ_quadrant [Nonempty M] :
    ¬ IsMeasureZero (𝓠 n) (univ : Set M) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  set e := chartAt (EuclideanQuadrant n) x with he
  have hx : x ∈ e.source := mem_chart_source _ x
  have h0 := h e (IsManifold.chart_mem_maximalAtlas (I := 𝓠 n) (n := ∞) x)
  rw [chartImage, inter_univ, ← e.extend_source (I := 𝓠 n),
    (e.extend (𝓠 n)).image_source_eq_target] at h0
  obtain ⟨W, hW, hWt⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1
    (e.extend_target_mem_nhdsWithin (I := 𝓠 n) hx)
  obtain ⟨W', hW'W, hW'o, hyW'⟩ := mem_nhds_iff.1 hW
  have hy : ∀ i, 0 ≤ (e.extend (𝓠 n) x) i := fun i => by
    have := (e.extend (𝓠 n)).map_source (by rwa [e.extend_source])
    rw [e.extend_target] at this
    have h2 := this.2
    rw [range_modelWithCornersEuclideanQuadrant] at h2
    exact h2 i (mem_univ i)
  obtain ⟨z, hzW', hz⟩ := exists_forall_pos_mem hy (hW'o.mem_nhds hyW')
  have hsub : W' ∩ {z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} ⊆ (e.extend (𝓠 n)).target :=
    fun w hw => hWt ⟨hW'W hw.1, by
      rw [range_modelWithCornersEuclideanQuadrant]; exact fun i _ => (hw.2 i).le⟩
  exact ((hW'o.inter isOpen_setOf_forall_pos).measure_pos volume ⟨z, hzW', hz⟩).ne'
    (measure_mono_null hsub h0)

end Quadrant

/-! ### Measure zero face by face -/

namespace MPolyfold

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} (hcs : Q.HasCornerStructureOfDim (n + 1)) (hfs : Q.IsFaceStructured)

/-- **`(n-1)`-dimensional measure zero in the boundary faces** (2021 p. 448, before
Definition 9.5.14): for a face-structured `Q` with a corner structure of dimension `n + 1` (a tame
`(n+1)`-dimensional sheet with its induced structure), `K` has measure zero **face by face** if
for every face `F` of `Q` (a manifold modelled on `[0,∞)ⁿ`, `faceChartedSpace`) the set `K ∩ F`
has measure zero in `F` (Definition 9.4.5). -/
def IsFaceNull (K : Set Z) : Prop :=
  ∀ (F : Set Z) (hF : Q.IsFace F),
    letI := faceChartedSpace hcs hfs hF
    IsMeasureZero (𝓠 n) ((↑) ⁻¹' K : Set F)

theorem isFaceNull_empty : IsFaceNull hcs hfs (∅ : Set Z) := fun F hF => by
  let _ := faceChartedSpace hcs hfs hF
  rw [preimage_empty]
  exact isMeasureZero_empty (I := 𝓠 n)

variable {hcs hfs} in
theorem IsFaceNull.mono {K K' : Set Z} (h : IsFaceNull hcs hfs K') (hK : K ⊆ K') :
    IsFaceNull hcs hfs K := fun F hF => by
  let _ := faceChartedSpace hcs hfs hF
  exact (h F hF).mono (preimage_mono hK)

theorem isFaceNull_iUnion {ι : Type*} [Countable ι] {K : ι → Set Z}
    (h : ∀ i, IsFaceNull hcs hfs (K i)) : IsFaceNull hcs hfs (⋃ i, K i) := fun F hF => by
  let _ := faceChartedSpace hcs hfs hF
  rw [preimage_iUnion]
  exact isMeasureZero_iUnion (I := 𝓠 n) fun i => h i F hF

/-- A set meeting no face (a set of interior points) has measure zero face by face. -/
theorem isFaceNull_of_forall_disjoint {K : Set Z} (h : ∀ F, Q.IsFace F → Disjoint K F) :
    IsFaceNull hcs hfs K := fun F hF => by
  let _ := faceChartedSpace hcs hfs hF
  have : ((↑) ⁻¹' K : Set F) = ∅ :=
    eq_empty_of_forall_notMem fun a ha => disjoint_left.1 (h F hF) ha a.2
  rw [this]
  exact isMeasureZero_empty (I := 𝓠 n)

/-- **A face is not a null set**: the face-by-face null sets do not contain a face (each face is
nonempty). -/
theorem not_isFaceNull_face {F : Set Z} (hF : Q.IsFace F) : ¬ IsFaceNull hcs hfs F := fun h => by
  let _ := faceChartedSpace hcs hfs hF
  have := isManifold_faceChartedSpace hcs hfs hF
  obtain ⟨x, hx, hFeq⟩ := id hF
  have : Nonempty F := ⟨⟨x, hFeq ▸ subset_closure (mem_connectedComponentIn hx)⟩⟩
  have h1 := h F hF
  rw [Subtype.coe_preimage_self] at h1
  exact not_isMeasureZero_univ_quadrant h1

end MPolyfold

/-! ### The `0`-dimensional null sets -/

section Point

variable {X : Type u} [TopologicalSpace X]

/-- **`0`-dimensional measure zero** (the counting measure): `A` is null in `N` iff `A ∩ N = ∅`.
A null-set system on every class `S` of sets, with no hypothesis: the boundary faces of a
`1`-dimensional sheet are points (2021 p. 448 for `n = 1`). -/
def SheetNullSets.point (S : Set (Set X)) : SheetNullSets S where
  IsNull N A := Disjoint A N
  isNull_empty _ := disjoint_bot_left
  isNull_mono h hA := h.mono_left hA
  isNull_iUnion h := disjoint_iUnion_left.2 h
  isNull_of_local N _ A h := disjoint_left.2 fun z hzA hzN => by
    obtain ⟨V, -, hzV, hd⟩ := h z hzA
    exact disjoint_left.1 hd ⟨hzA, hzV⟩ hzN
  isNull_transfer N _ N' _ C hC h := by
    have : C = ∅ := h.eq_bot_of_le (hC.trans inter_subset_left)
    rw [this]
    exact disjoint_bot_left
  not_isNull_self N _ hne h := hne.ne_empty (disjoint_self.1 h)

theorem SheetNullSets.point_isNull_iff {S : Set (Set X)} {N A : Set X} :
    (SheetNullSets.point S).IsNull N A ↔ Disjoint A N := Iff.rfl

end Point

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {S' : Set (Set Obj)}

/-- **`0`-dimensional measure zero in `∂S`**: for the counting null sets on the boundaries (a
`1`-dimensional `Θ`), `K` has measure zero in `∂S = |supp(∂Θ)|` iff `K ∩ ∂S = ∅`.  The hypothesis
`hS'` is the standing one of Definition 9.5.14: tame structures with boundaries in the class. -/
theorem isMeasureZeroBoundary_point_iff (hind : X.HasIndependentTangentSums Θ)
    (hS' : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ B : X.TameBranchingStructure Θ x,
      ∀ i, X.PObj.submanifoldBoundary (B.M i) ∈ S') {K : Set X.OrbitSpace} :
    X.IsMeasureZeroBoundary (SheetNullSets.point S') Θ K ↔
      Disjoint K (X.orbitSupp (X.boundaryTheta Θ)) := by
  classical
  constructor
  · intro h
    refine disjoint_left.2 ?_
    rintro _ hK ⟨y, hy, rfl⟩
    obtain ⟨B, -, hnull⟩ := h y hy
    have h1 : 0 < X.boundaryTheta Θ y := hy
    rw [X.boundaryTheta_eq hind B.toLocalBranchingStructure B.mem_U] at h1
    obtain ⟨i, hi⟩ := exists_mem_of_sum_pos h1
    exact disjoint_left.1 (hnull i) ⟨hi, hK⟩ hi
  · intro h x hx
    obtain ⟨B, hB⟩ := hS' x hx
    refine ⟨B, hB, fun i => disjoint_left.2 fun y hy _ => ?_⟩
    have hyM : y ∈ B.M i := by obtain ⟨-, hy', -⟩ := hy.1; exact hy'
    refine disjoint_left.1 h hy.2 ⟨y, ?_, rfl⟩
    change 0 < X.boundaryTheta Θ y
    rw [X.boundaryTheta_eq hind B.toLocalBranchingStructure (B.subset_U i hyM)]
    exact Finset.sum_pos' (fun j _ => (B.σ_pos j).le) ⟨i, by simp [hy.1], B.σ_pos i⟩

/-- For the counting null sets the only subset of `∂S` of measure zero is `∅`. -/
theorem boundaryMeasureZeroSets_point (hind : X.HasIndependentTangentSums Θ)
    (hS' : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ B : X.TameBranchingStructure Θ x,
      ∀ i, X.PObj.submanifoldBoundary (B.M i) ∈ S') :
    X.boundaryMeasureZeroSets (SheetNullSets.point S') Θ = {∅} := by
  ext K
  change X.IsMeasureZeroBoundary (SheetNullSets.point S') Θ (Subtype.val '' K) ↔ K = ∅
  rw [isMeasureZeroBoundary_point_iff hind hS']
  constructor
  · intro h
    refine eq_empty_of_forall_notMem fun a ha => ?_
    exact disjoint_left.1 h ⟨a, ha, rfl⟩ a.2
  · rintro rfl
    rw [image_empty]
    exact disjoint_bot_left

/-- **`L(∂S)` for a `1`-dimensional `Θ`** (Definition 9.5.14 with the counting null sets): the
Borel σ-algebra of `∂S`. -/
theorem lebesgueSigmaBoundary_point (hind : X.HasIndependentTangentSums Θ)
    (hS' : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ B : X.TameBranchingStructure Θ x,
      ∀ i, X.PObj.submanifoldBoundary (B.M i) ∈ S') :
    X.lebesgueSigmaBoundary (SheetNullSets.point S') Θ =
      borel (X.orbitSupp (X.boundaryTheta Θ)) := by
  refine le_antisymm ?_ (borel_le_borelNullSigma _)
  change MeasurableSpace.generateFrom _ ≤ _
  rw [boundaryMeasureZeroSets_point hind hS']
  refine MeasurableSpace.generateFrom_le fun A hA => ?_
  rcases hA with hA | hA
  · exact hA
  · rw [mem_singleton_iff.1 hA]
    exact @MeasurableSet.empty _ (borel _)

end EpGroupoid

/-! ### The witness: `Θ = 1` on the half-line -/

section HalfLine

open EpGroupoid MPolyfold

local notation "Wq" => ScBanach.const (Fin 0 → ℝ)

local notation "Ph" => MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))

/-- The half-line `[0, ∞)` is connected. -/
instance connectedSpace_halfLine : ConnectedSpace (quadrant 1 Wq 0) :=
  Subtype.connectedSpace ((quadrant_convex 1 Wq 0).isConnected (quadrant_nonempty 1 Wq))

/-- **`Θ = 1` on the half-line is tame** (Definition 9.3.6): `U = M = [0, ∞)`, the natural
representation of the trivial ep-groupoid, the tame structure of the quadrant. -/
def halfLineTame (x : quadrant 1 Wq 0) :
    (trivial Ph).TameBranchingStructure (fun _ => 1) x where
  toLocalBranchingStructure := localBranchingStructure_one Ph halfLine_hasCornerStructure x
  rep := trivialNaturalRep Ph x
  U_eq := rfl
  hasPropernessProperty := hasPropernessProperty_trivial Ph isOpen_univ
  hasTameInducedStructure _ := hasTameInducedStructure_univ Ph (quadrantPolyfold_isTame 1 Wq)

/-- The class of the boundaries: `∂[0, ∞) = {0}`. -/
def halfLineBoundaries : Set (Set (quadrant 1 Wq 0)) := {MPolyfold.submanifoldBoundary Ph univ}

theorem halfLine_boundaries_mem :
    ∀ x ∈ supp ((trivial Ph).boundaryTheta fun _ => 1),
      ∃ B : (trivial Ph).TameBranchingStructure (fun _ => 1) x,
        ∀ i, MPolyfold.submanifoldBoundary Ph (B.M i) ∈ halfLineBoundaries :=
  fun x _ => ⟨halfLineTame x, fun _ => rfl⟩

/-- **`∂S ≠ ∅`**: the class of the corner `0` lies in `∂S = |supp(∂Θ)|` for `Θ = 1` on
`[0, ∞)`. -/
theorem halfLine_orbitSupp_boundary_nonempty :
    ((trivial Ph).orbitSupp ((trivial Ph).boundaryTheta fun _ => 1)).Nonempty := by
  refine ⟨(trivial Ph).π halfLineCorner, halfLineCorner, ?_, rfl⟩
  change 0 < (trivial Ph).boundaryTheta (fun _ => 1) halfLineCorner
  rw [boundaryTheta_one Ph halfLine_hasCornerStructure halfLineCorner_mem_submanifoldBoundary]
  exact one_pos

/-- **Measure zero in `∂S` for the half-line** (`0`-dimensional, in the boundary face `{0}`):
`K` has measure zero iff it does not meet `∂S`. -/
theorem halfLine_isMeasureZeroBoundary_iff {K : Set (trivial Ph).OrbitSpace} :
    (trivial Ph).IsMeasureZeroBoundary (SheetNullSets.point halfLineBoundaries) (fun _ => 1) K ↔
      Disjoint K ((trivial Ph).orbitSupp ((trivial Ph).boundaryTheta fun _ => 1)) :=
  isMeasureZeroBoundary_point_iff (hasIndependentTangentSums_one Ph halfLine_hasCornerStructure)
    halfLine_boundaries_mem

/-- `∂S` is not a null set. -/
theorem halfLine_not_isMeasureZeroBoundary :
    ¬ (trivial Ph).IsMeasureZeroBoundary (SheetNullSets.point halfLineBoundaries) (fun _ => 1)
      ((trivial Ph).orbitSupp ((trivial Ph).boundaryTheta fun _ => 1)) := fun h =>
  halfLine_orbitSupp_boundary_nonempty.ne_empty
    (disjoint_self.1 (halfLine_isMeasureZeroBoundary_iff.1 h))

/-- **A witness for Definition 9.5.14 with `∂S ≠ ∅`**: for `Θ = 1` on the half-line, `L(∂S)` is
the Borel σ-algebra of the nonempty `∂S`. -/
theorem halfLine_lebesgueSigmaBoundary :
    (trivial Ph).lebesgueSigmaBoundary (SheetNullSets.point halfLineBoundaries) (fun _ => 1) =
      borel ((trivial Ph).orbitSupp ((trivial Ph).boundaryTheta fun _ => 1)) :=
  lebesgueSigmaBoundary_point (hasIndependentTangentSums_one Ph halfLine_hasCornerStructure)
    halfLine_boundaries_mem

end HalfLine

end Polyfold
