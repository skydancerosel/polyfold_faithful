import Polyfold.Chapter9.BoundaryNotNull
import Polyfold.Chapter9.SolutionFaces2021
import Polyfold.Chapter9.BoundaryOrientationContinuity2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, Definition 9.3.8, p. 427 (2017: Definition 9.9), and §9.5, Theorem 9.5.15, p. 448.

# The stratum `{d_M = 1}` of a tame sheet is a smooth submanifold

For an `n`-dimensional submanifold `M` of an M-polyfold `X` with tame induced structure, the
boundary orientation `o_{∂M}` of Definition 9.3.8 lives on the points with `d_M = 1`, and the
boundary measures of Theorem 9.5.15 integrate over `∂M`.  Here the set
`∂₁M = {y ∈ M | d_M(y) = 1}` is shown to be a smooth finite-dimensional submanifold of `X` in the
sense of Definition 4.2.1 (an sc⁺-retraction on an open subset of `X`).

## What is formalized

* `MPolyfold.CornerCoords.facePiece`, `faceRet`: in corner coordinates `κ` of an M-polyfold `Q`,
  the open piece on which all coordinates but the `i`-th are positive, and the map
  `κ⁻¹ ∘ (yᵢ ↦ 0) ∘ κ`; it is an sc-smooth retraction of the piece onto its points with
  `d_Q = 1` (`isScSmoothOn_faceRet`, `degIndex_eq_one_iff`).
* `MPolyfold.stratumOne P M`: the set `{y ∈ M | d_M(y) = 1}`; for tame `M` it is
  `boundaryStratum M` (`stratumOne_eq_boundaryStratum`).
* `MPolyfold.exists_stratum_coords`: corner coordinates of `M` at a point of the stratum with
  exactly one vanishing coordinate.
* `MPolyfold.exists_isScPlusRetractionOn_stratumOne`,
  **`MPolyfold.isSmoothSubmanifold_stratumOne`**:
  the retraction `ι ∘ faceRet ∘ s` (`s` the sc⁺-retraction of `M`) is an sc⁺-retraction of an
  open subset of `X` onto the stratum.

## What the text leaves implicit

The text speaks of "the boundary `∂M`" as of a manifold; the smooth structure of the stratum as a
subset of the ambient M-polyfold is not discussed.  The sc⁺-property of the new retraction `r`
comes from `r = s ∘ r`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

namespace CornerCoords

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} (κ : CornerCoords Q n) (i : Fin n)

/-- The open piece of the coordinate domain on which all coordinates but the `i`-th are positive
(and the projection to `{yᵢ = 0}` stays in the coordinate image). -/
def facePiece : Set Z :=
  {z | z ∈ κ.s ∧ (∀ l, l ≠ i → 0 < κ.coord z l) ∧ Function.update (κ.coord z) i 0 ∈ κ.W}

/-- The map `κ⁻¹ ∘ (yᵢ ↦ 0) ∘ κ`. -/
def faceRet (z : Z) : Z := κ.coordInv (Function.update (κ.coord z) i 0)

theorem continuous_update_zero : Continuous fun v : Fin n → ℝ => Function.update v i 0 :=
  continuous_id.update i continuous_const

theorem isOpen_facePiece : IsOpen (κ.facePiece i) := by
  have hO : IsOpen ({v : Fin n → ℝ | ∀ l, l ≠ i → 0 < v l} ∩
      (fun v : Fin n → ℝ => Function.update v i 0) ⁻¹' κ.W) :=
    (isOpen_setOf_forall_ne_pos i).inter (κ.isOpen_W.preimage (continuous_update_zero i))
  exact κ.continuousOn_coord.isOpen_inter_preimage κ.isOpen_s hO

variable {κ i}

theorem facePiece_subset_s : κ.facePiece i ⊆ κ.s := fun _ h => h.1

theorem update_nonneg {z : Z} (hz : z ∈ κ.facePiece i) (l : Fin n) :
    0 ≤ Function.update (κ.coord z) i 0 l := by
  by_cases hl : l = i
  · rw [hl, Function.update_self]
  · rw [Function.update_of_ne hl]; exact (hz.2.1 l hl).le

theorem coord_faceRet {z : Z} (hz : z ∈ κ.facePiece i) :
    κ.coord (κ.faceRet i z) = Function.update (κ.coord z) i 0 :=
  κ.coord_coordInv hz.2.2 (update_nonneg hz)

theorem faceRet_mem_s {z : Z} (hz : z ∈ κ.facePiece i) : κ.faceRet i z ∈ κ.s :=
  κ.coordInv_mem hz.2.2 (update_nonneg hz)

theorem coord_faceRet_self {z : Z} (hz : z ∈ κ.facePiece i) : κ.coord (κ.faceRet i z) i = 0 := by
  rw [coord_faceRet hz, Function.update_self]

theorem faceRet_mem_facePiece {z : Z} (hz : z ∈ κ.facePiece i) :
    κ.faceRet i z ∈ κ.facePiece i := by
  refine ⟨faceRet_mem_s hz, fun l hl => ?_, ?_⟩
  · rw [coord_faceRet hz, Function.update_of_ne hl]; exact hz.2.1 l hl
  · rw [coord_faceRet hz, Function.update_idem]; exact hz.2.2

theorem faceRet_eq_self {z : Z} (hz : z ∈ κ.facePiece i) (h : κ.coord z i = 0) :
    κ.faceRet i z = z := by
  unfold faceRet
  rw [← h, Function.update_eq_self]
  exact κ.coordInv_coord hz.1

/-- On the piece, `d_Q = 1` exactly on `{yᵢ = 0}`. -/
theorem degIndex_eq_one_iff {z : Z} (hz : z ∈ κ.facePiece i) :
    Q.degIndex z = 1 ↔ κ.coord z i = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [κ.degIndex_eq_card hz.1] at h
    have : (Finset.univ.filter fun j => κ.coord z j = 0) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun l _ => ?_
      by_cases hl : l = i
      · rw [hl]; exact hne
      · exact (hz.2.1 l hl).ne'
    rw [this, Finset.card_empty] at h
    exact zero_ne_one h
  · intro h
    exact κ.degIndex_eq_one hz.1 h fun j hj => (hz.2.1 j hj).ne'

theorem continuousOn_faceRet : ContinuousOn (κ.faceRet i) (κ.facePiece i) :=
  κ.continuousOn_coordInv.comp
    ((continuous_update_zero i).comp_continuousOn (κ.continuousOn_coord.mono facePiece_subset_s))
    fun _ hz => ⟨hz.2.2, update_nonneg hz⟩

theorem contDiff_update_zero : ContDiff ℝ ∞ fun v : Fin n → ℝ => Function.update v i 0 := by
  refine contDiff_pi.2 fun l => ?_
  by_cases hl : l = i
  · subst hl
    simp only [Function.update_self]
    exact contDiff_const
  · simp only [Function.update_of_ne hl]
    exact contDiff_apply ℝ ℝ l

variable (κ i) in
/-- **The projection to the face `{yᵢ = 0}` is sc-smooth** on the piece (in the corner chart it
is an affine map of a finite-dimensional space). -/
theorem isScSmoothOn_faceRet : Q.IsScSmoothOn Q (κ.faceRet i) (κ.facePiece i) := by
  refine IsScSmoothOn.of_exists_charts (κ.isOpen_facePiece i) continuousOn_faceRet fun x hx => ?_
  have hsub : κ.facePiece i ⊆ κ.χ.source := fun z hz => κ.s_subset hz.1
  refine ⟨κ.χ, κ.χ, κ.facePiece i, κ.isChart, κ.isChart, κ.isOpen_facePiece i, hx,
    fun z hz => ⟨hz, hsub hz⟩, fun z hz => κ.s_subset (faceRet_mem_s hz), ?_⟩
  have hrel : IsRelOpenInQuadrant κ.χ.model.E κ.χ.model.C (κ.χ '' κ.facePiece i) := by
    obtain ⟨W₀, hW₀, h⟩ := κ.χ.exists_isOpen_image_eq hsub (κ.isOpen_facePiece i)
    rw [h]
    exact κ.isCornerChart.isRelOpenInQuadrant.inter_isOpen hW₀
  have hV1 : IsScDomain (ScBanach.const (Fin n → ℝ)) (κ.W ∩ {y | ∀ i, 0 ≤ y i}) :=
    (isRelOpenInQuadrant_stdQuadrant κ.isOpen_W).isScDomain
  have hf1 : IsScSmooth (E := κ.χ.model.E) (F := ScBanach.const (Fin n → ℝ))
      (κ.χ '' κ.facePiece i) (fun v => κ.Ψ v + κ.c) :=
    κ.isScSmooth_coordAff.of_subset hrel.isScDomain (image_mono facePiece_subset_s)
  have hf1m : MapsTo (fun v => κ.Ψ v + κ.c) (κ.χ '' κ.facePiece i)
      (κ.W ∩ {y | ∀ i, 0 ≤ y i}) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨κ.coord_mem_W hz.1, κ.coord_nonneg hz.1⟩
  have hupd : IsScSmooth (E := ScBanach.const (Fin n → ℝ)) (F := ScBanach.const (Fin n → ℝ))
      (κ.W ∩ {y | ∀ i, 0 ≤ y i}) (fun v : Fin n → ℝ => Function.update v i 0) :=
    IsScSmooth.of_contDiffOn_finiteDimensional hV1 contDiff_update_zero.contDiffOn
  have h2 := IsScSmooth.comp hrel.isScDomain hV1 hupd hf1 hf1m
  have h2m : MapsTo ((fun v : Fin n → ℝ => Function.update v i 0) ∘ fun v => κ.Ψ v + κ.c)
      (κ.χ '' κ.facePiece i) (κ.W ∩ {y | ∀ i, 0 ≤ y i}) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hz.2.2, update_nonneg hz⟩
  have h3 := IsScSmooth.comp hrel.isScDomain hV1 κ.isScSmooth_coordAffInv h2 h2m
  refine (isScSmoothRetractMap_iff_exists hrel.isScRetract).2 ⟨?_, ScRetraction.id hrel,
    image_id _, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change κ.χ (κ.faceRet i (κ.χ.symm (κ.χ z))) ∈ κ.χ.model.O
    rw [κ.χ.symm_apply_apply (hsub hz)]
    exact κ.χ.mapsTo_model _ (κ.s_subset (faceRet_mem_s hz))
  · refine IsScSmooth.congr hrel.isScDomain ?_ h3
    rintro _ ⟨z, hz, rfl⟩
    change κ.Ψ.symm (Function.update (κ.Ψ (κ.χ z) + κ.c) i 0 - κ.c) =
      κ.χ (κ.faceRet i (κ.χ.symm (κ.χ z)))
    rw [κ.χ.symm_apply_apply (hsub hz)]
    exact (κ.apply_coordInv hz.2.2 (update_nonneg hz)).symm

end CornerCoords

/-! ### The stratum of a tame sheet -/

section Sheet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {n : ℕ}

variable (P) in
/-- **The stratum `∂₁M = {y ∈ M | d_M(y) = 1}`** of a smooth submanifold `M` (the points at which
Definition 9.3.8, 2021 p. 427, is stated; `∅` unless `M` is a smooth submanifold). -/
def stratumOne (M : Set X) : Set X :=
  {y | ∃ (hM : P.IsSmoothSubmanifold M) (hy : y ∈ M), P.subDegIndex hM.isSubMPolyfold ⟨y, hy⟩ = 1}

theorem stratumOne_subset (M : Set X) : P.stratumOne M ⊆ M := fun _ ⟨_, hy, _⟩ => hy

theorem mem_stratumOne_iff (hM : P.IsSmoothSubmanifold M) {y : X} (hy : y ∈ M) :
    y ∈ P.stratumOne M ↔ P.subDegIndex hM.isSubMPolyfold ⟨y, hy⟩ = 1 :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hM, hy, h⟩⟩

/-- For `M` with tame induced structure the stratum is the stratum of reduced codimension `1`
of `BoundaryOrientationContinuity2021`. -/
theorem stratumOne_eq_boundaryStratum (hM : P.IsSmoothSubmanifold M)
    (ht : P.HasTameInducedStructure M) : P.stratumOne M = P.boundaryStratum M := by
  rw [boundaryStratum_eq_of_tame hM ht]
  ext y
  exact ⟨fun ⟨_, hy, h⟩ => ⟨hy, h⟩, fun ⟨hy, h⟩ => ⟨hM, hy, h⟩⟩

theorem stratumOne_subset_submanifoldBoundary (M : Set X) :
    P.stratumOne M ⊆ P.submanifoldBoundary M := fun _ ⟨hM, hy, h⟩ => ⟨hM, hy, h.ge⟩

/-- **Corner coordinates at a point of the stratum**: exactly one coordinate vanishes. -/
theorem exists_stratum_coords [ParacompactSpace M] (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) {y : X} (hy : y ∈ M)
    (h1 : P.subDegIndex hM.1.isSubMPolyfold ⟨y, hy⟩ = 1) :
    ∃ (κ : CornerCoords (subPolyfold hM.1.isSubMPolyfold) n) (i : Fin n),
      (⟨y, hy⟩ : M) ∈ κ.facePiece i ∧ κ.coord ⟨y, hy⟩ i = 0 := by
  have hcs := hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  obtain ⟨κ, hyκ⟩ := hcs.exists_cornerCoords ⟨y, hy⟩
  have hcard : (Finset.univ.filter fun j => κ.coord ⟨y, hy⟩ j = 0).card = 1 := by
    rw [← κ.degIndex_eq_card hyκ]; exact h1
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hcard
  have hi0 : κ.coord ⟨y, hy⟩ i = 0 :=
    (Finset.mem_filter.1 (hi ▸ Finset.mem_singleton_self i :
      i ∈ Finset.univ.filter fun j => κ.coord ⟨y, hy⟩ j = 0)).2
  refine ⟨κ, i, ⟨hyκ, fun l hl => ?_, ?_⟩, hi0⟩
  · refine lt_of_le_of_ne (κ.coord_nonneg hyκ l) fun h0 => hl ?_
    have : l ∈ Finset.univ.filter fun j => κ.coord ⟨y, hy⟩ j = 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h0.symm⟩
    rw [hi] at this
    exact Finset.mem_singleton.1 this
  · rw [← hi0, Function.update_eq_self]
    exact κ.coord_mem_W hyκ

/-- **The stratum `{d_M = 1}` of a tame sheet is the image of an sc⁺-retraction near each of its
points** (Definition 4.2.1 for the stratum; used for Definition 9.3.8 and Theorem 9.5.15): for an
`n`-dimensional submanifold `M` with tame induced structure and `y` with `d_M(y) = 1` there are an
open `V ∋ y` in `X` and an sc⁺-retraction `r : V → V` with `r(V) = ∂₁M ∩ V`
(`r = ι ∘ κ⁻¹ ∘ (yᵢ ↦ 0) ∘ κ ∘ s`). -/
theorem exists_isScPlusRetractionOn_stratumOne (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) {y : X} (hy : y ∈ P.stratumOne M) :
    ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ ∃ r : X → X, P.IsScPlusRetractionOn r V ∧
      r '' V = P.stratumOne M ∩ V := by
  have := P.paracompactSpace_subtype M
  obtain ⟨_, hyM, h1⟩ := hy
  obtain ⟨κ, i, hyp, hyi⟩ := exists_stratum_coords hM ht hyM h1
  set d := hM.1.data hyM with hd
  have hyV : y ∈ d.V := hM.1.mem_data_V hyM
  set st : X → M := d.toSubData.retractInto ⟨y, hyM⟩ with hst_def
  have hst : P.IsScSmoothOn (subPolyfold hM.1.isSubMPolyfold) st d.V :=
    subPolyfold_retraction_isScSmooth hM.1.isSubMPolyfold d.toSubData ⟨y, hyM⟩
  have hfix : ∀ z (hz : z ∈ M), z ∈ d.V → st z = ⟨z, hz⟩ := fun z hz hzV =>
    Subtype.ext ((d.toSubData.retractInto_val ⟨y, hyM⟩ hzV).trans
      (d.toSubData.apply_eq_self ⟨hz, hzV⟩))
  set r : X → X := fun x => (κ.faceRet i (st x)).1 with hr
  set V₁ : Set X := d.V ∩ st ⁻¹' κ.facePiece i with hV₁
  have hV₁o : IsOpen V₁ := hst.continuousOn.isOpen_inter_preimage d.isOpen (κ.isOpen_facePiece i)
  have hmem : ∀ x ∈ V₁, st x ∈ κ.facePiece i := fun x hx => hx.2
  have hr₀ : P.IsScSmoothOn (subPolyfold hM.1.isSubMPolyfold) (κ.faceRet i ∘ st) V₁ :=
    IsScSmoothOn.comp (g := κ.faceRet i) (f := st) (κ.isScSmoothOn_faceRet i)
      (hst.mono hV₁o inter_subset_left) hmem
  have hr₁ : P.IsScSmoothOn P r V₁ :=
    IsScSmoothOn.comp (g := Subtype.val) (f := κ.faceRet i ∘ st)
      (subPolyfold_inclusion_isScSmooth hM.1.isSubMPolyfold) hr₀ (mapsTo_univ _ _)
  set V : Set X := V₁ ∩ r ⁻¹' d.V with hV
  have hVo : IsOpen V := hr₁.continuousOn.isOpen_inter_preimage hV₁o d.isOpen
  have hpiece : ∀ x ∈ V₁, κ.faceRet i (st x) ∈ κ.facePiece i := fun x hx =>
    CornerCoords.faceRet_mem_facePiece (hmem x hx)
  have hstr : ∀ x ∈ V, st (r x) = κ.faceRet i (st x) := fun x hx =>
    hfix (r x) (κ.faceRet i (st x)).2 hx.2
  have hrr : ∀ x ∈ V, r (r x) = r x := fun x hx => by
    change (κ.faceRet i (st (r x))).1 = (κ.faceRet i (st x)).1
    rw [hstr x hx, CornerCoords.faceRet_eq_self (hpiece x hx.1)
      (CornerCoords.coord_faceRet_self (hmem x hx.1))]
  have hmaps : MapsTo r V V := fun x hx =>
    ⟨⟨hx.2, by change st (r x) ∈ κ.facePiece i; rw [hstr x hx]; exact hpiece x hx.1⟩,
      by change r (r x) ∈ d.V; rw [hrr x hx]; exact hx.2⟩
  have hyst : st y = ⟨y, hyM⟩ := hfix y hyM hyV
  have hry : r y = y := by
    change (κ.faceRet i (st y)).1 = y
    rw [hyst, CornerCoords.faceRet_eq_self hyp hyi]
  have hyV' : y ∈ V := ⟨⟨hyV, by change st y ∈ κ.facePiece i; rw [hyst]; exact hyp⟩,
    by change r y ∈ d.V; rw [hry]; exact hyV⟩
  refine ⟨V, hVo, hyV', r, ⟨hr₁.mono hVo inter_subset_left, hmaps, hrr, fun x _ =>
    hM.1.mem_levelSet_one (κ.faceRet i (st x)).2, fun x₀ => ?_⟩, ?_⟩
  · refine (IsScSmoothOn.comp (d.isScPlusRetractionOn.isScSmoothOn_one x₀)
      (hr₁.mono hVo inter_subset_left) fun x hx => hx.2).congr fun x hx => ?_
    change P.toLevelOne x₀ (d.s (r x)) = P.toLevelOne x₀ (r x)
    exact congrArg _ (d.toSubData.apply_eq_self (x := r x) ⟨(κ.faceRet i (st x)).2, hx.2⟩)
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨hM.1, (κ.faceRet i (st x)).2, ?_⟩, hmaps hx⟩
      exact (CornerCoords.degIndex_eq_one_iff (hpiece x hx.1)).2
        (CornerCoords.coord_faceRet_self (hmem x hx.1))
    · rintro ⟨⟨_, hzM, hz1⟩, hzV⟩
      have hstz : st z = ⟨z, hzM⟩ := hfix z hzM hzV.1.1
      have hzp : (⟨z, hzM⟩ : M) ∈ κ.facePiece i := by rw [← hstz]; exact hzV.1.2
      refine ⟨z, hzV, ?_⟩
      change (κ.faceRet i (st z)).1 = z
      rw [hstz, CornerCoords.faceRet_eq_self hzp ((CornerCoords.degIndex_eq_one_iff hzp).1 hz1)]

/-- **The stratum `∂₁M = {d_M = 1}` of a tame `n`-dimensional sheet is a smooth
finite-dimensional submanifold of `X`** (Definition 4.2.1; for Definition 9.3.8, 2021 p. 427, and
Theorem 9.5.15, p. 448). -/
theorem isSmoothSubmanifold_stratumOne (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) : P.IsSmoothSubmanifold (P.stratumOne M) :=
  fun _ hy => exists_isScPlusRetractionOn_stratumOne hM ht hy

end Sheet

end MPolyfold

end Polyfold
