import Polyfold.Chapter9.BoundaryOperation
import Polyfold.Chapter9.GeneralLevelZero

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3: **Definition 9.3.8** (2021 p. 427; 2017: Definition 9.9, p. 313), the
sentence after it ("orientations of `T_y∂M` with `d_M(y) = 1`, which fit continuously together"),
and **Definition 9.3.10** (2021 p. 428; 2017: Definition 9.11, p. 314).  Numbers and pages are the
2021 text's, the 2017 ones in parentheses.

# The boundary orientation `o_{∂M}` is continuous along `∂M`

## The text, paraphrased

(Before Definition 9.3.8) For tame `M`, the points with `d_M(y) = 1` form an open dense part of
`∂M` with a manifold structure.  (Definition 9.3.8) For an oriented `(M, o)` of dimension `n` and
`y ∈ ∂M` with `d_M(y) = 1`, `(a₁, …, a_{n-1})` is a positive basis of `T_y∂M` iff
`(e, a₁, …, a_{n-1})` is positive for `o_y`, `e` outward; `o_{∂M}` assigns this orientation to
every such `y`.  (After it) These orientations "fit continuously together".

## What is formalized

* `MPolyfold.boundaryStratum A`: the points `y ∈ A` at which `T_yA` has reduced codimension `1`
  (`dim T_yA / (T_yA ∩ T^R_yX) = 1`, read in every presented chart); for `A` with tame induced
  structure this is `{y ∈ A | d_A(y) = 1}` (`mem_boundaryStratum_iff_subDegIndex`, through
  Lemma 9.3.7's `subDegIndex_eq_quotDim_span`).
* `MPolyfold.OrientationAlong S L n`: an orientation of the tangent sets `L y`, `y ∈ S`, with the
  continuity clause of `SubmanifoldOrientation` (positive frame fields with continuous chart
  vectors near every point of `S`); `OrientationAlong.toSubmanifoldOrientation`: on a smooth
  submanifold `B ⊆ S` with `T_yB = L y` it is an orientation of `B`.
* **The continuity of `o_{∂M}`** (`SubmanifoldOrientation.exists_continuous_boundaryFrames`):
  for every oriented smooth submanifold `(A, o)` of dimension `m + 1` (tame or not) and every
  `y₀` of the boundary stratum, there are a chart `φ`, an open `V ∋ y₀` and a frame field
  `a` along the stratum, positive for Definition 9.3.8's orientation at every point of the stratum
  in `V`, whose chart vectors are continuous.  Hence **`o_{∂M}` is an orientation along the
  stratum** (`SubmanifoldOrientation.boundaryOrientation`), of the sets
  `T_y∂M = T^R_yA` (`boundaryCarrier`, `chartVec_image_boundaryCarrier`); the tame form
  `boundaryOrientation_tame` is along `{d_A = 1}`.
* The tools: in a chart with a presentation `T`, the derivative `Dr(z)` of an sc⁺-retraction maps
  the partial quadrant `C_{x₀}` at a nearby point `x₀` into `C_{ι z}` and the minimal subspace
  `E_{x₀}` into `E_{ι z}` (`ScRetraction.scDeriv_mem_partialQuadrantAtWith`,
  `ScRetraction.scDeriv_mem_minimalSubspaceWith`, from `nonneg_scDeriv`); near `φ(y₀)` the
  vanishing coordinates are among those of `φ(y₀)` (`eventually_coord_eq_zero_imp`).

## The proof, and what the text leaves implicit

The text says the orientations fit together "by definition".  The proof here: let `r` be the
chart sc⁺-retraction of `A` at `y₀`, `K₀ = T_{y₀}∂A` with a positive frame `w` of `o_{∂A}`, and
`s ∈ C_{y₀}A ∖ K₀`.  For `z` in the stratum near `y₀`, `Dr(z)w` lies in `T_zA ∩ E_{φ(z)}`
(`E_{φ(y₀)} ⊆ E_{φ(z)}` and `Dr(z)E_{φ(z)} ⊆ E_{φ(z)}`) and is independent near `y₀`, hence a
basis of `T_z∂A` (dimension count, reduced codimension `1`); `Dr(z)s` lies in `C_{φ(z)}` but not
in `T_z∂A`, so `−Dr(z)s` is outward; the sign of `(−Dr(z)s, Dr(z)w)` against the continuous
positive frame of `o` is locally constant (`frameDet`).  Tameness is not used: the reduced
codimension `1` suffices, and for tame `A` it is `d_A(y) = 1`.

## Not formalized, and why

* That the stratum `{d_M = 1}` is open and dense in `∂M` and a smooth manifold whose tangent space
  is `T^R_yM`: the stratum is not built as a submanifold; `T_y∂M` is read as `T^R_yM`
  (`boundaryCarrier`), and `toSubmanifoldOrientation` turns the result into a
  `SubmanifoldOrientation` of any submanifold with these tangent spaces lying in the stratum.
  (2026-11-12) For a sheet with tame induced structure the stratum is open and dense in `∂M`
  (`exists_isOpen_boundaryStratum_eq`, `submanifoldBoundary_subset_closure_boundaryStratum`,
  `GapP2_DBoundaryStratum.lean`); it is not built as a submanifold.  (2026-11-13) It is built
  as one in `GapP2_E6_StratumRetraction.lean`, `GapP2_E6_StratumTangent.lean`
  (`isSubmanifoldOfDim_stratumOne`, `submanifoldTangent_stratumOne`: dimension `n - 1`, tangent
  spaces `T^R_yM`), oriented by `o_{∂M}` in the sense of Definition 9.3.3
  (`stratumOrientation`, `GapP2_E6_BoundaryOrientation.lean`).
* The extension to the closed faces (Figure 9.1).  Remark 9.3.11 is a comment, with nothing to
  formalize.  (2026-11-13) For face-structured sheets: `figure_9_1_existsUnique_faceOrientation`
  (`GapP2_D3FaceOrientation.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology

noncomputable section

namespace Polyfold

universe u

/-! ### The derivative of an sc⁺-retraction on partial quadrants at nearby points -/

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}

/-- **`Dr(z)` maps `C_{x₀}` into `C_{ι z}`** for a point `x₀` whose vanishing coordinates include
those of `ι z` (in a presentation `T` of `C`), on level-`1` vectors.  For a vanishing coordinate
`ℓ` of `ι z`, `ι z + τ v ∈ C` for small `τ > 0`, and `nonneg_scDeriv` gives `ℓ(Dr(z)v) ≥ 0`. -/
theorem scDeriv_mem_partialQuadrantAtWith (hR : R.IsScPlus) {n : ℕ} {W : ScBanach}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    {z : E 1} (hz : E.toBase 1 z ∈ R.retract) {x₀ : E 0}
    (hsub : ∀ i, (T 0 (E.toBase 1 z)).1 i = 0 → (T 0 x₀).1 i = 0)
    {v : E 0} (hv : v ∈ partialQuadrantAtWith T x₀) (hv1 : v ∈ range (E.toBase 1)) :
    scDeriv R.U R z v ∈ partialQuadrantAtWith T (E.toBase 1 z) := by
  intro i hi
  obtain ⟨p, rfl⟩ := hv1
  set x := E.toBase 1 z with hxdef
  let ℓ : Fin n → E 0 →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T 0 : E 0 →L[ℝ] _))
  have hℓapp : ∀ j e, ℓ j e = (T 0 e).1 j := fun _ _ => rfl
  have hmemC : ∀ e, e ∈ C ↔ ∀ j, 0 ≤ ℓ j e := fun e => by rw [hT]; exact Iff.rfl
  have hxC : x ∈ C := by
    obtain ⟨O, -, hUO⟩ := R.relOpen.relOpen
    exact (hUO ▸ R.retract_subset hz).2
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ j, 0 ≤ ℓ j (x + τ • E.toBase 1 p) := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ℓ j x = 0
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [map_add, map_smul, hj, zero_add, smul_eq_mul]
      exact mul_nonneg (le_of_lt hτ) (hv j (hsub j hj))
    · have hpos : 0 < ℓ j x := lt_of_le_of_ne ((hmemC x).1 hxC j) (Ne.symm hj)
      have hcont : Continuous fun τ : ℝ => ℓ j (x + τ • E.toBase 1 p) := by fun_prop
      have h0 : ℓ j (x + (0 : ℝ) • E.toBase 1 p) = ℓ j x := by rw [zero_smul, add_zero]
      have := (hcont.tendsto 0).eventually (lt_mem_nhds (h0 ▸ hpos))
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
  obtain ⟨τ, hτC, hτ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hτ0 : (0 : ℝ) < τ := hτ
  have hc : x + E.toBase 1 (τ • p) ∈ C := by
    rw [hmemC, map_smul]; exact hτC
  have h := nonneg_scDeriv hR hz (ℓ i) (fun e he => (hmemC e).1 he i) hi hc
  rw [map_smul, map_smul] at h
  rw [ContinuousLinearMap.map_smul, smul_eq_mul] at h
  exact (mul_nonneg_iff_of_pos_left hτ0).1 h

/-- **`Dr(z)` maps `E_{x₀}` into `E_{ι z}`** (two-sided form of
`scDeriv_mem_partialQuadrantAtWith`). -/
theorem scDeriv_mem_minimalSubspaceWith (hR : R.IsScPlus) {n : ℕ} {W : ScBanach}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    {z : E 1} (hz : E.toBase 1 z ∈ R.retract) {x₀ : E 0}
    (hsub : ∀ i, (T 0 (E.toBase 1 z)).1 i = 0 → (T 0 x₀).1 i = 0)
    {v : E 0} (hv : v ∈ minimalSubspaceWith T x₀) (hv1 : v ∈ range (E.toBase 1)) :
    scDeriv R.U R z v ∈ minimalSubspaceWith T (E.toBase 1 z) := by
  have hpos := scDeriv_mem_partialQuadrantAtWith hR hT hz hsub
    (minimalSubspaceWith_subset_partialQuadrantAtWith T x₀ hv) hv1
  have hneg := scDeriv_mem_partialQuadrantAtWith hR hT hz hsub
    (minimalSubspaceWith_subset_partialQuadrantAtWith T x₀ (neg_mem hv))
    (by obtain ⟨p, rfl⟩ := hv1; exact ⟨-p, map_neg _ _⟩)
  refine (mem_minimalSubspaceWith T).2 fun i hi => ?_
  have h1 := hpos i hi
  have h2 := hneg i hi
  rw [map_neg, map_neg, Prod.fst_neg, Pi.neg_apply, neg_nonneg] at h2
  exact le_antisymm h2 h1

end ScRetraction

/-! ### Frames and determinants -/

section FrameDetTools

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- A frame with `frameDet Λ w ≠ 0` is linearly independent. -/
theorem linearIndependent_of_frameDet_ne_zero (Λ : E →L[ℝ] (Fin n → ℝ)) {w : Fin n → E}
    (h : frameDet Λ w ≠ 0) : LinearIndependent ℝ w := by
  rw [frameDet_eq] at h
  have hli : LinearIndependent ℝ (fun i => Λ (w i)) :=
    ((Pi.basisFun ℝ (Fin n)).is_basis_iff_det.2 (isUnit_iff_ne_zero.2 h)).1
  exact LinearIndependent.of_comp (Λ : E →ₗ[ℝ] (Fin n → ℝ)) hli

/-- `frameDet Λ w = 0` if the vectors of `w` lie in a subspace of dimension `< n`. -/
theorem frameDet_eq_zero_of_mem {K : Submodule ℝ E} [FiniteDimensional ℝ K]
    (Λ : E →L[ℝ] (Fin n → ℝ)) {w : Fin n → E} (hw : ∀ i, w i ∈ K) (hK : finrank ℝ K < n) :
    frameDet Λ w = 0 := by
  by_contra h
  have hli := linearIndependent_of_frameDet_ne_zero Λ h
  let w' : Fin n → K := fun i => ⟨w i, hw i⟩
  have hli' : LinearIndependent ℝ w' := LinearIndependent.of_comp K.subtype hli
  have := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  omega

end FrameDetTools

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **An oriented tangent set of positive dimension has a positive frame** (`Orientation.someBasis`,
lifted to `TX`). -/
theorem IsOrientedAt.exists_mem_frames {y : X} {d : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin d → P.TangentSpace)} (h : P.IsOrientedAt y ⟨d, L, O⟩) (hd : 0 < d) :
    ∃ v, v ∈ O := by
  obtain ⟨-, φ, hφ, -, N, hN, hfin, hrank, ω, hO⟩ := h
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have := hfin
  have hcard : Fintype.card (Fin d) = finrank ℝ N := by rw [Fintype.card_fin]; exact hrank.symm
  set b : Basis (Fin d) ℝ N := ω.someBasis hcard
  have hb : ∀ i, ∃ α ∈ L, chartVec hφ α = b i := fun i => by
    have : (b i : φ.model.E 0) ∈ (N : Set (φ.model.E 0)) := (b i).2
    rw [hN] at this
    exact this
  choose v hvL hv using hb
  refine ⟨v, ?_⟩
  have hO' : O = chartFrames hφ L N ω := hO
  rw [hO']
  exact ⟨hvL, b, fun i => (hv i).symm, ω.someBasis_orientation hcard⟩

/-- **A frame is positive if its determinant has the sign of a positive frame's**: for an
oriented tangent set `(L, O)` over `y`, a chart `φ` at `y`, `v₁ ∈ O` and a frame `v₂` of `L`, both
with `frameDet Λ ≠ 0`, `v₂ ∈ O` as soon as the two determinants have the same sign. -/
theorem mem_frames_of_frameDet {y : X} {d : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin d → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨d, L, O⟩) {φ : MChart X}
    (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) (Λ : φ.model.E 0 →L[ℝ] (Fin d → ℝ))
    {v₁ v₂ : Fin d → P.TangentSpace} (hv₁ : v₁ ∈ O) (hv₂ : ∀ i, v₂ i ∈ L)
    (h₁ : frameDet Λ (fun i => chartVec hφ (v₁ i)) ≠ 0)
    (h₂ : frameDet Λ (fun i => chartVec hφ (v₂ i)) ≠ 0)
    (hs : 0 < frameDet Λ (fun i => chartVec hφ (v₁ i)) ↔
      0 < frameDet Λ (fun i => chartVec hφ (v₂ i))) : v₂ ∈ O := by
  obtain ⟨N, hN, hfin, hrank, ω, hOeq⟩ := hO.isChartOrientation hφ hyφ
  have := hfin
  change O = chartFrames hφ L N ω at hOeq
  have hv₁' := hv₁
  rw [hOeq] at hv₁'
  obtain ⟨-, b₁, hb₁, hbo₁⟩ := hv₁'
  have hmem : ∀ i, chartVec hφ (v₂ i) ∈ N := fun i => by
    rw [← SetLike.mem_coe, hN]; exact ⟨v₂ i, hv₂ i, rfl⟩
  have hli := linearIndependent_of_frameDet_ne_zero Λ h₂
  let w : Fin d → N := fun i => ⟨chartVec hφ (v₂ i), hmem i⟩
  have hliw : LinearIndependent ℝ w := LinearIndependent.of_comp N.subtype hli
  have hcard : Fintype.card (Fin d) = finrank ℝ N := by rw [Fintype.card_fin]; exact hrank.symm
  set b₂ := basisOfLinearIndependentOfCardEqFinrank' w hliw hcard
  have hb₂ : ∀ i, (b₂ i : φ.model.E 0) = chartVec hφ (v₂ i) := fun i => by
    simp only [b₂, coe_basisOfLinearIndependentOfCardEqFinrank', w]
  have hf₁ : (fun i => chartVec hφ (v₁ i)) = fun i => (b₁ i : φ.model.E 0) :=
    funext fun i => (hb₁ i).symm
  have hf₂ : (fun i => chartVec hφ (v₂ i)) = fun i => (b₂ i : φ.model.E 0) :=
    funext fun i => (hb₂ i).symm
  rw [hf₁] at h₁ hs
  rw [hf₂] at hs
  rw [hOeq]
  refine ⟨hv₂, b₂, hb₂, ?_⟩
  rw [← hbo₁]
  exact ((orientation_eq_iff_frameDet Λ b₁ b₂ h₁).2 hs).symm

omit [T2Space X] [ParacompactSpace X] in
/-- **Near `y₀` the vanishing coordinates are among those of `φ(y₀)`** (in a presentation `T` of
the partial quadrant of the chart `φ`): the others stay nonzero by continuity. -/
theorem eventually_coord_eq_zero_imp {φ : MChart X} {y₀ : X} (hy₀ : y₀ ∈ φ.source) {n : ℕ}
    {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    ∀ᶠ z in 𝓝 y₀, ∀ i, (T 0 (φ z)).1 i = 0 → (T 0 (φ y₀)).1 i = 0 := by
  rw [Filter.eventually_all]
  intro i
  by_cases h : (T 0 (φ y₀)).1 i = 0
  · exact Eventually.of_forall fun _ _ => h
  · have hφc : ContinuousAt φ y₀ :=
      φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hy₀)
    let ℓ : φ.model.E 0 →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T 0 : φ.model.E 0 →L[ℝ] _))
    have hc : ContinuousAt (fun z => ℓ (φ z)) y₀ := ℓ.continuous.continuousAt.comp hφc
    exact (hc.eventually (isOpen_ne.mem_nhds h)).mono fun z hz hz0 => (hz hz0).elim

/-! ### The boundary stratum and orientations along a set -/

variable (P) in
/-- **The boundary stratum** `∂₁A`: the points `y ∈ A` at which `T_yA` has reduced codimension
`1`, `dim(T_yA / T_yA ∩ T^R_yX) = 1`, read in every presented chart (for `A` with tame induced
structure, `d_A(y) = 1`: `mem_boundaryStratum_iff_subDegIndex`). -/
def boundaryStratum (A : Set X) : Set X :=
  {y | y ∈ A ∧ ∀ c : P.PresentedChart y,
    quotDim (span ℝ (c.vec '' P.submanifoldTangent A y)) c.red = 1}

/-- For tame `A`, the boundary stratum is `{y ∈ A | d_A(y) = 1}` (Lemma 9.3.7's proof). -/
theorem mem_boundaryStratum_iff_subDegIndex {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) {y : X} (hy : y ∈ A) :
    y ∈ P.boundaryStratum A ↔ P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = 1 := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  refine ⟨fun h => ?_, fun h => ⟨hy, fun c' => ?_⟩⟩
  · rw [subDegIndex_eq_quotDim_span hA ht hy c]; exact h.2 c
  · rw [← subDegIndex_eq_quotDim_span hA ht hy c', h]

/-- The oriented tangent space `T_y(M, o)` has reduced codimension `1` exactly on the stratum. -/
theorem SubmanifoldOrientation.hasReducedCodim_iff_mem_boundaryStratum {A : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation A n) {y : X} (hy : y ∈ A) :
    P.HasReducedCodim y 1 (o.tangent y) ↔ y ∈ P.boundaryStratum A :=
  ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩

variable (P) in
/-- **An orientation along a set `S`** of the tangent sets `L y`, `y ∈ S`: an orientation of `L y`
at every `y ∈ S` (given by its positive frames), continuous as in `SubmanifoldOrientation`: near
every point of `S` there are a chart `φ` and a frame field, positive along `S`, whose chart vectors
depend continuously on the point of `S`.  For `n = 0` there is no continuity condition. -/
structure OrientationAlong (S : Set X) (L : X → Set P.TangentSpace) (n : ℕ) where
  /-- The positive frames of `L y`. -/
  frames : X → Set (Fin n → P.TangentSpace)
  isOrientedAt : ∀ y ∈ S, P.IsOrientedAt y ⟨n, L y, frames y⟩
  continuous : 0 < n → ∀ y ∈ S, ∃ (φ : MChart X) (hφ : P.IsChart φ) (V : Set X), IsOpen V ∧
    y ∈ V ∧ V ⊆ φ.source ∧ ∃ e : X → Fin n → P.TangentSpace, (∀ z ∈ S ∩ V, e z ∈ frames z) ∧
      ContinuousOn (fun z i => chartVec hφ (e z i)) (S ∩ V)

/-- **On a submanifold lying in `S` with tangent spaces `L y`, an orientation along `S` is an
orientation of the submanifold** (`SubmanifoldOrientation`). -/
def OrientationAlong.toSubmanifoldOrientation {S : Set X} {L : X → Set P.TangentSpace} {n : ℕ}
    (o : P.OrientationAlong S L n) {B : Set X} (hBS : B ⊆ S)
    (hBL : ∀ y ∈ B, P.submanifoldTangent B y = L y) : P.SubmanifoldOrientation B n where
  frames := o.frames
  isOrientedAt y hy := by rw [hBL y hy]; exact o.isOrientedAt y (hBS hy)
  continuous hn y hy := by
    obtain ⟨φ, hφ, V, hV, hyV, hVφ, e, he, hc⟩ := o.continuous hn y (hBS hy)
    exact ⟨φ, hφ, V, hV, hyV, hVφ, e, fun z hz => he z ⟨hBS hz.1, hz.2⟩,
      hc.mono fun z hz => ⟨hBS hz.1, hz.2⟩⟩

/-- **The frames of Definition 9.3.8 at `y`**: the frames `a` of `T_y∂A = T^R_yA` such that
`(e, a)` is positive for `o_y` for every outward `e ∈ T_yA`; this is the boundary operation
`boundaryOp` applied to `T_y(A, o)` (`boundaryOp_tangent_eq`). -/
def SubmanifoldOrientation.boundaryFramesAt {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (y : X) : Set (Fin m → P.TangentSpace) :=
  {a | (∀ i, a i ∈ P.boundaryCarrier (P.submanifoldTangent A y)) ∧
    ∀ e ∈ P.submanifoldTangent A y, P.IsOutwardTangent e →
      (Fin.cons e a : Fin (m + 1) → P.TangentSpace) ∈ o.frames y}

theorem SubmanifoldOrientation.boundaryOp_tangent_eq {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (y : X) :
    P.boundaryOp (o.tangent y) =
      ⟨m, P.boundaryCarrier (P.submanifoldTangent A y), o.boundaryFramesAt y⟩ := rfl

/-! ### The continuity of `o_{∂M}` -/

/-- **Definition 9.3.8: the boundary orientations "fit continuously together"** (2021 p. 427):
for an oriented smooth submanifold `(A, o)` of dimension `m + 1`, `m > 0`, and a point `y₀` of
the boundary stratum, there are a chart `φ`, an open `V ∋ y₀` and a frame field `a` which is
positive for Definition 9.3.8's orientation `o_{∂A, z}` of `T_z∂A = T^R_zA` at every point `z`
of the stratum in `V`, and whose chart vectors depend continuously on `z`.  (The frame is
`Dr(z)w`, `r` the chart sc⁺-retraction of `A`, `w` a positive boundary frame at `y₀`.) -/
theorem SubmanifoldOrientation.exists_continuous_boundaryFrames {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (hA : P.IsSmoothSubmanifold A) (hm : 0 < m)
    {y₀ : X} (hy₀ : y₀ ∈ P.boundaryStratum A) :
    ∃ (φ : MChart X) (hφ : P.IsChart φ) (V : Set X), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ φ.source ∧
      ∃ a : X → Fin m → P.TangentSpace,
        (∀ z ∈ P.boundaryStratum A ∩ V, a z ∈ o.boundaryFramesAt z) ∧
        ContinuousOn (fun z i => chartVec hφ (a z i)) (P.boundaryStratum A ∩ V) := by
  obtain ⟨hy₀A, hcod₀⟩ := hy₀
  -- the continuity chart of `o`, presented
  obtain ⟨φ, hφ, V₁, hV₁, hy₀V₁, hV₁φ, e, he, hec⟩ := o.continuous (Nat.succ_pos m) y₀ hy₀A
  have hy₀φ : y₀ ∈ φ.source := hV₁φ hy₀V₁
  obtain ⟨k, Wk, T, hT⟩ := φ.model.isPartialQuadrant
  let pc : ∀ z, z ∈ φ.source → P.PresentedChart z := fun z hz => ⟨φ, hφ, hz, k, Wk, T, hT⟩
  -- the chart sc⁺-retraction of `A`
  set d := hA.data hy₀A
  have hy₀V : y₀ ∈ d.V := hA.mem_data_V hy₀A
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hy₀A hy₀V
  set W₀ := d.toSubData.shrink φ with hW₀def
  have hW₀ : IsOpen W₀ := d.toSubData.isOpen_shrink φ
  have hy₀W₀ : y₀ ∈ W₀ := d.toSubData.mem_shrink φ hy₀A hy₀V hy₀φ
  have hW₀V : W₀ ⊆ d.V := fun q hq => d.toSubData.shrink_subset_V φ hq
  have hW₀φ : W₀ ⊆ φ.source := d.toSubData.shrink_subset_source φ
  set ι := φ.model.E.toBase 1 with hιdef
  set D : X → φ.model.E 0 →L[ℝ] φ.model.E 0 := fun z => scDeriv t.U t (levelLift φ 1 z)
    with hDdef
  have hrange : ∀ z ∈ A ∩ W₀, ι (levelLift φ 1 z) = φ z ∧ φ z ∈ t.retract ∧
      P.chartTangent hφ A z = range (D z) := fun z hz =>
    chartTangent_eq_range hφ d ht hz.1 (hW₀V hz.2) (hW₀φ hz.2)
  have hret : ∀ z ∈ A ∩ W₀, ι (levelLift φ 1 z) ∈ t.retract := fun z hz => by
    rw [(hrange z hz).1]; exact (hrange z hz).2.1
  obtain ⟨hz₀, -, hT₀⟩ := hrange y₀ ⟨hy₀A, hy₀W₀⟩
  have hret₀ := hret y₀ ⟨hy₀A, hy₀W₀⟩
  -- `D z` along `A`, on vectors of `T_{y₀}A`
  have hrangeι : ∀ v ∈ range (D y₀), v ∈ range ι := fun v hv =>
    ⟨_, ScRetraction.toBase_plusDeriv_of_mem_range htp hret₀ hv⟩
  have hfix : ∀ v ∈ range (D y₀), D y₀ v = v := by
    rintro _ ⟨u, rfl⟩
    exact congrArg (fun L : φ.model.E 0 →L[ℝ] φ.model.E 0 => L u) (t.scDeriv_comp_self hret₀)
  have hmaps : MapsTo (levelLift φ 1) (A ∩ W₀) (φ.model.E.lvlSet t.U 1) := fun z hz =>
    t.retract_subset (hret z hz)
  have hcontD : ∀ v ∈ range (D y₀), ContinuousOn (fun z => D z v) (A ∩ W₀) := by
    intro v hv
    set p := t.plusDeriv (levelLift φ 1 y₀) v
    have hιp : ι p = v := ScRetraction.toBase_plusDeriv_of_mem_range htp hret₀ hv
    have hlz : ContinuousOn (levelLift φ 1) (A ∩ W₀) :=
      (hasContinuousLevelOneOn hA φ hφ).mono fun z hz => ⟨hz.1, hW₀φ hz.2⟩
    have h1 := (ScRetraction.continuousOn_plusDeriv htp).comp hlz hmaps
    have h2 : ContinuousOn (fun z => ι (((t.plusDeriv (levelLift φ 1 z)).comp ι) p)) (A ∩ W₀) :=
      ι.continuous.comp_continuousOn
        ((ContinuousLinearMap.apply ℝ _ p).continuous.comp_continuousOn h1)
    refine h2.congr fun z hz => ?_
    change D z v = ι (t.plusDeriv (levelLift φ 1 z) (ι p))
    rw [ScRetraction.toBase_plusDeriv htp (hmaps hz), hιp]
  -- the data at `y₀`: an inward `s` off `T^R`, the outward `u₀`, a positive boundary frame `w`
  have hO₀ := o.isOrientedAt y₀ hy₀A
  have hadm₀ := isBoundaryAdmissible_of_submanifold hA hy₀A hO₀ rfl hcod₀
  obtain ⟨s, hs, hsin, hsred⟩ := hadm₀.2
  set c₀ := pc y₀ hy₀φ
  have hsC : chartVec hφ s ∈ partialQuadrantAtWith T (φ y₀) :=
    (isInwardVec_iff c₀ (hO₀.1 s hs)).1 hsin
  have hsR : chartVec hφ s ∈ range (D y₀) := by
    rw [← hT₀]; exact ⟨s, hs, rfl⟩
  obtain ⟨u₀, hu₀, hu₀v⟩ : ∃ u₀ ∈ P.submanifoldTangent A y₀, chartVec hφ u₀ = -chartVec hφ s := by
    have : -chartVec hφ s ∈ range (D y₀) := by
      obtain ⟨q, hq⟩ := hsR; exact ⟨-q, by rw [map_neg, hq]⟩
    rw [← hT₀] at this
    exact this
  have hu₀out : P.IsOutwardTangent u₀ := by
    rw [isOutwardTangent_iff (hO₀.1 u₀ hu₀)]
    intro hin
    have h1 := (isInwardVec_iff c₀ (hO₀.1 u₀ hu₀)).1 hin
    change chartVec hφ u₀ ∈ c₀.cone at h1
    rw [hu₀v] at h1
    exact hsred ((isReducedVec_iff c₀ (hO₀.1 s hs)).2 (c₀.mem_red_of_mem_cone hsC h1))
  have hbO₀ := isOrientedAt_boundaryOp hO₀ hadm₀
  change P.IsOrientedAt y₀
    ⟨m, P.boundaryCarrier (P.submanifoldTangent A y₀), o.boundaryFramesAt y₀⟩ at hbO₀
  obtain ⟨w, hwbc, hwcons⟩ := hbO₀.exists_mem_frames hm
  have hcons₀ := hwcons u₀ hu₀ hu₀out
  have hwT : ∀ i, w i ∈ P.submanifoldTangent A y₀ := fun i => (hwbc i).1
  have hwred : ∀ i, chartVec hφ (w i) ∈ minimalSubspaceWith T (φ y₀) := fun i =>
    (isReducedVec_iff c₀ (hO₀.1 _ (hwT i))).1 (by
      have h := (hwbc i).2
      unfold IsReducedTangent at h
      rwa [(hO₀.1 _ (hwT i))] at h)
  have hwR : ∀ i, chartVec hφ (w i) ∈ range (D y₀) := fun i => by
    rw [← hT₀]; exact ⟨w i, hwT i, rfl⟩
  -- the fields
  set Sf : X → φ.model.E 0 := fun z => D z (chartVec hφ s) with hSfdef
  set Af : X → Fin m → φ.model.E 0 := fun z i => D z (chartVec hφ (w i)) with hAfdef
  have hSfc : ContinuousOn Sf (A ∩ W₀) := hcontD _ hsR
  have hAfc : ContinuousOn Af (A ∩ W₀) := continuousOn_pi.2 fun i => hcontD _ (hwR i)
  set F : X → Fin (m + 1) → φ.model.E 0 := fun z => Fin.cons (-Sf z) (Af z) with hFdef
  have hFc : ContinuousOn F (A ∩ W₀) := by
    refine continuousOn_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [hFdef, Fin.cons_zero]; exact hSfc.neg
    · simp only [hFdef, Fin.cons_succ]; exact (continuousOn_pi.1 hAfc) j
  -- the determinant map
  obtain ⟨N, hN, hfin, hrank, -, -⟩ := hO₀.isChartOrientation hφ hy₀φ
  have := hfin
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional N
  let b₀ : Basis (Fin (m + 1)) ℝ N := Module.finBasisOfFinrankEq ℝ N hrank
  let Λ : φ.model.E 0 →L[ℝ] (Fin (m + 1) → ℝ) :=
    (b₀.equivFunL : N →L[ℝ] (Fin (m + 1) → ℝ)).comp Q'
  have hΛN : ∀ v : N, Λ v = b₀.equivFun v := fun v => by
    change b₀.equivFunL (Q' v) = _
    rw [hQ' v]; rfl
  have hne : ∀ v ∈ o.frames y₀, frameDet Λ (fun i => chartVec hφ (v i)) ≠ 0 := by
    intro v hv
    obtain ⟨N', hN', -, -, ω, hOeq⟩ := hO₀.isChartOrientation hφ hy₀φ
    have hNN : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
    subst hNN
    have hv' : v ∈ chartFrames hφ (P.submanifoldTangent A y₀) N' ω := hOeq ▸ hv
    obtain ⟨-, b, hb, -⟩ := hv'
    have : (fun i => chartVec hφ (v i)) = fun i => (b i : φ.model.E 0) :=
      funext fun i => (hb i).symm
    rw [this]
    exact frameDet_ne_zero_of_basis b₀ Λ hΛN b
  set De : X → ℝ := fun z => frameDet Λ (fun i => chartVec hφ (e z i)) with hDedef
  set Db : X → ℝ := fun z => frameDet Λ (F z) with hDbdef
  have hDec : ContinuousOn De (A ∩ V₁) := ContinuousOn.frameDet Λ hec
  have hDbc : ContinuousOn Db (A ∩ W₀) := ContinuousOn.frameDet Λ hFc
  have he₀ := he y₀ ⟨hy₀A, hy₀V₁⟩
  have hDe₀ : De y₀ ≠ 0 := hne _ he₀
  have hF₀ : F y₀ = fun i => chartVec hφ ((Fin.cons u₀ w : Fin (m + 1) → P.TangentSpace) i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [hFdef, Fin.cons_zero, hSfdef, hfix _ hsR, hu₀v]
    · simp only [hFdef, Fin.cons_succ, hAfdef, hfix _ (hwR j)]
  have hDb₀ : Db y₀ ≠ 0 := by
    change frameDet Λ (F y₀) ≠ 0
    rw [hF₀]; exact hne _ hcons₀
  have hsign₀ : 0 < De y₀ ↔ 0 < Db y₀ := by
    have h := (frames_eq_iff_frameDet hO₀ hO₀ hφ hy₀φ Λ he₀ hcons₀ hDe₀).1 rfl
    change _ ↔ 0 < frameDet Λ (F y₀)
    rw [hF₀]; exact h
  obtain ⟨U₁, hU₁, hy₀U₁, hU₁s⟩ := exists_isOpen_sign_eq hDec ⟨hy₀A, hy₀V₁⟩ hDe₀
  obtain ⟨U₂, hU₂, hy₀U₂, hU₂s⟩ := exists_isOpen_sign_eq hDbc ⟨hy₀A, hy₀W₀⟩ hDb₀
  obtain ⟨U₃, hU₃sub, hU₃, hy₀U₃⟩ := mem_nhds_iff.1 (eventually_coord_eq_zero_imp hy₀φ T)
  -- the lifts to `TX`
  have : Nonempty P.TangentSpace := ⟨s⟩
  let lift : X → φ.model.E 0 → P.TangentSpace := fun z v =>
    Function.invFunOn (chartVec hφ) (P.submanifoldTangent A z) v
  have hlift : ∀ z ∈ A ∩ W₀, ∀ v ∈ range (D z),
      lift z v ∈ P.submanifoldTangent A z ∧ chartVec hφ (lift z v) = v := by
    intro z hz v hv
    rw [← (hrange z hz).2.2] at hv
    exact ⟨Function.invFunOn_mem hv, Function.invFunOn_eq hv⟩
  let a : X → Fin m → P.TangentSpace := fun z i => lift z (Af z i)
  let u : X → P.TangentSpace := fun z => lift z (-Sf z)
  have hAfR : ∀ z i, Af z i ∈ range (D z) := fun z i => ⟨_, rfl⟩
  have hSfR : ∀ z, -Sf z ∈ range (D z) := fun z => ⟨-chartVec hφ s, map_neg _ _⟩
  refine ⟨φ, hφ, V₁ ∩ W₀ ∩ U₁ ∩ U₂ ∩ U₃, (((hV₁.inter hW₀).inter hU₁).inter hU₂).inter hU₃,
    ⟨⟨⟨⟨hy₀V₁, hy₀W₀⟩, hy₀U₁⟩, hy₀U₂⟩, hy₀U₃⟩, fun z hz => hV₁φ hz.1.1.1.1, a, ?_, ?_⟩
  · rintro z ⟨⟨hzA, hcodz⟩, ⟨⟨⟨⟨hzV₁, hzW₀⟩, hzU₁⟩, hzU₂⟩, hzU₃⟩⟩
    have hzAW : z ∈ A ∩ W₀ := ⟨hzA, hzW₀⟩
    have hzφ : z ∈ φ.source := hW₀φ hzW₀
    set cz := pc z hzφ
    have hOz := o.isOrientedAt z hzA
    obtain ⟨hιz, hzret, hTz⟩ := hrange z hzAW
    have hsubz : ∀ i, (T 0 (ι (levelLift φ 1 z))).1 i = 0 → (T 0 (φ y₀)).1 i = 0 := by
      rw [hιz]; exact hU₃sub hzU₃
    -- the fields lie in `E_{φ(z)}`, resp. `C_{φ(z)}`
    have hAfred : ∀ i, Af z i ∈ cz.red := fun i => by
      have h := ScRetraction.scDeriv_mem_minimalSubspaceWith htp hT (hret z hzAW) hsubz
        (hwred i) (hrangeι _ (hwR i))
      rw [hιz] at h; exact h
    have hSfC : Sf z ∈ cz.cone := by
      have h := ScRetraction.scDeriv_mem_partialQuadrantAtWith htp hT (hret z hzAW) hsubz
        hsC (hrangeι _ hsR)
      rw [hιz] at h; exact h
    -- `T_z∂A` has dimension `m`
    obtain ⟨Nz, hNz, hspanz, hfinz, hrankz, hKz⟩ := hOz.chartData cz
    have := hfinz
    have hrankz' : finrank ℝ Nz = m + 1 := hrankz
    have hcodz' : quotDim Nz cz.red = 1 := hspanz ▸ hcodz cz
    have hrankK : finrank ℝ ↥(Nz ⊓ cz.red) = m := by
      have := finrank_inf_eq_of_quotDim_eq_one hcodz'
      omega
    have hNzR : ∀ v ∈ range (D z), v ∈ Nz := fun v hv => by
      rw [← SetLike.mem_coe, hNz]
      rw [← hTz] at hv
      exact hv
    -- the determinant does not vanish at `z`
    obtain ⟨hDbz, hsDbz⟩ := hU₂s z ⟨hzAW, hzU₂⟩
    obtain ⟨hDez, hsDez⟩ := hU₁s z ⟨⟨hzA, hzV₁⟩, hzU₁⟩
    -- `u z` points outward
    obtain ⟨huT, huv⟩ := hlift z hzAW _ (hSfR z)
    have hbase : ∀ α ∈ P.submanifoldTangent A z, P.levelVal 1 (P.tangentProj α) = z :=
      fun α hα => hα.1
    have huout : ¬ P.IsInwardVec z (u z) := by
      intro hin
      have h1 := (isInwardVec_iff cz (hbase _ huT)).1 hin
      change chartVec hφ (u z) ∈ cz.cone at h1
      rw [huv] at h1
      have hSred : Sf z ∈ cz.red := cz.mem_red_of_mem_cone hSfC h1
      have hmemK : ∀ i, F z i ∈ Nz ⊓ cz.red := fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [hFdef, Fin.cons_zero]
          exact neg_mem (Submodule.mem_inf.2 ⟨hNzR _ ⟨_, rfl⟩, hSred⟩)
        · simp only [hFdef, Fin.cons_succ]
          exact Submodule.mem_inf.2 ⟨hNzR _ (hAfR z j), hAfred j⟩
      exact hDbz (frameDet_eq_zero_of_mem Λ hmemK
        (show finrank ℝ ↥(Nz ⊓ cz.red) < m + 1 by omega))
    -- the boundary frames at `z` are those with first vector `u z`
    have hadmz := isBoundaryAdmissible_of_submanifold hA hzA hOz rfl hcodz
    have heq := boundaryOp_eq hOz hadmz huT huout
    rw [show (⟨m + 1, P.submanifoldTangent A z, o.frames z⟩ : OrTangent P) = o.tangent z from rfl,
      o.boundaryOp_tangent_eq z] at heq
    simp only [OrTangent.mk.injEq, true_and, heq_eq_eq] at heq
    rw [heq]
    -- `a z` is a positive boundary frame
    have haT : ∀ i, a z i ∈ P.submanifoldTangent A z ∧ chartVec hφ (a z i) = Af z i :=
      fun i => hlift z hzAW _ (hAfR z i)
    refine ⟨fun i => ⟨(haT i).1, ?_⟩, ?_⟩
    · unfold IsReducedTangent
      rw [hbase _ (haT i).1, isReducedVec_iff cz (hbase _ (haT i).1)]
      change chartVec hφ (a z i) ∈ cz.red
      rw [(haT i).2]; exact hAfred i
    · have hFz : (fun i => chartVec hφ ((Fin.cons (u z) (a z) : Fin (m + 1) → P.TangentSpace) i))
          = F z := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero, hFdef]; exact huv
        · simp only [Fin.cons_succ, hFdef]; exact (haT j).2
      have hcT : ∀ i, (Fin.cons (u z) (a z) : Fin (m + 1) → P.TangentSpace) i ∈
          P.submanifoldTangent A z := fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using huT
        · simpa using (haT j).1
      refine mem_frames_of_frameDet hOz hφ hzφ Λ (he z ⟨hzA, hzV₁⟩) hcT hDez
        (by rw [hFz]; exact hDbz) ?_
      rw [hFz]
      change 0 < De z ↔ 0 < Db z
      rw [hsDez, hsDbz]; exact hsign₀
  · refine (continuousOn_pi.2 fun i => (continuousOn_pi.1 hAfc i).mono ?_).congr ?_
    · rintro z ⟨⟨hzA, -⟩, ⟨⟨⟨⟨-, hzW₀⟩, -⟩, -⟩, -⟩⟩
      exact ⟨hzA, hzW₀⟩
    · rintro z ⟨⟨hzA, -⟩, ⟨⟨⟨⟨-, hzW₀⟩, -⟩, -⟩, -⟩⟩
      funext i
      exact (hlift z ⟨hzA, hzW₀⟩ _ (hAfR z i)).2

/-- **Definition 9.3.8: `o_{∂M}` is an orientation along the boundary stratum** (2021 p. 427;
2017: Definition 9.9): for an oriented smooth submanifold `(A, o)` of dimension `m + 1`, the
frames of Definition 9.3.8 (`boundaryFramesAt`, i.e. `boundaryOp (T_y(A, o))`) orient
`T_y∂A = T^R_yA` at every point of the stratum (`SubmanifoldOrientation.boundaryOp_tangent`) and
fit continuously together (`exists_continuous_boundaryFrames`). -/
def SubmanifoldOrientation.boundaryOrientation {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (hA : P.IsSmoothSubmanifold A) :
    P.OrientationAlong (P.boundaryStratum A)
      (fun y => P.boundaryCarrier (P.submanifoldTangent A y)) m where
  frames := o.boundaryFramesAt
  isOrientedAt y hy := by
    have h := (o.boundaryOp_tangent hA hy.1
      ((o.hasReducedCodim_iff_mem_boundaryStratum hy.1).2 hy)).1
    exact h
  continuous hm _ hy := o.exists_continuous_boundaryFrames hA hm hy

/-- The frames of `boundaryOrientation` are those of the boundary operation `boundaryOp`. -/
theorem SubmanifoldOrientation.boundaryOp_tangent_eq_boundaryOrientation {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (hA : P.IsSmoothSubmanifold A) (y : X) :
    P.boundaryOp (o.tangent y) = ⟨m, P.boundaryCarrier (P.submanifoldTangent A y),
      (o.boundaryOrientation hA).frames y⟩ := rfl

/-- **The tame form**: for `A` with tame induced structure the stratum is `{y ∈ A | d_A(y) = 1}`,
the set of points at which Definition 9.3.8 is stated. -/
theorem boundaryStratum_eq_of_tame {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) :
    P.boundaryStratum A = {y | ∃ hy : y ∈ A, P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = 1} := by
  ext y
  constructor
  · intro h; exact ⟨h.1, (mem_boundaryStratum_iff_subDegIndex hA ht h.1).1 h⟩
  · rintro ⟨hy, h⟩; exact (mem_boundaryStratum_iff_subDegIndex hA ht hy).2 h

/-- **Definition 9.3.8 for tame `M`, continuity included**: for an oriented smooth submanifold
`(A, o)` of dimension `m + 1` with tame induced structure, `o_{∂A}` is an orientation of the sets
`T_y∂A = T^R_yA` along `{y ∈ A | d_A(y) = 1}`. -/
def SubmanifoldOrientation.boundaryOrientation_tame {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) :
    P.OrientationAlong {y | ∃ hy : y ∈ A, P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = 1}
      (fun y => P.boundaryCarrier (P.submanifoldTangent A y)) m where
  frames := o.boundaryFramesAt
  isOrientedAt y hy :=
    (o.boundaryOrientation hA).isOrientedAt y (by rw [boundaryStratum_eq_of_tame hA ht]; exact hy)
  continuous hm y hy := by
    rw [← boundaryStratum_eq_of_tame hA ht] at hy ⊢
    exact (o.boundaryOrientation hA).continuous hm y hy

end MPolyfold

/-! ### Definition 9.3.10: the terms of (9.12) -/

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- **The terms `T_y(∂Mᵢ, o_{∂Mᵢ})` of (9.12) come from orientations along `∂Mᵢ`** (Definition
9.3.10, 2021 p. 428; 2017: Definition 9.11): for a sheet `Mᵢ` of dimension `m + 1` of an oriented
branching structure, the boundary operation `boundaryOp` used in `boundaryLift` (9.12) is, along
the boundary stratum of `Mᵢ`, the orientation `o_{∂Mᵢ}` of `T^R_yMᵢ`, continuous along the
stratum (`SubmanifoldOrientation.boundaryOrientation`). -/
theorem OrientedBranchingStructure.exists_boundaryOrientation
    (B : X.OrientedBranchingStructure Θ x) (i : B.ι) {m : ℕ} (hm : B.dim i = m + 1) :
    ∃ ob : X.PObj.OrientationAlong (X.PObj.boundaryStratum (B.M i))
        (fun y => X.PObj.boundaryCarrier (X.PObj.submanifoldTangent (B.M i) y)) m,
      ∀ y, X.PObj.boundaryOp ((B.orient i).tangent y) =
        ⟨m, X.PObj.boundaryCarrier (X.PObj.submanifoldTangent (B.M i) y), ob.frames y⟩ := by
  have hA := (B.isSubmanifoldOfDim i).1
  generalize B.orient i = o
  generalize B.dim i = d at o hm
  subst hm
  exact ⟨o.boundaryOrientation hA, fun y => rfl⟩

end EpGroupoid

end Polyfold
