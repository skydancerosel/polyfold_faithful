import Polyfold.Chapter9.BranchingGeometryMeasure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.4 "The Geometry of Local Branching Structures" (2021 pp. 429–436; 2017
pp. 316–321): **Definition 9.4.1** (p. 429; 2017: Definition 9.12), **Lemma 9.4.2** (p. 430;
2017: Lemma 9.11), **Definition 9.4.5** (p. 431; 2017: Definition 9.13) and **Lemma 9.4.6**
(p. 431; 2017: Lemma 9.14), for a smooth finite-dimensional manifold with boundary and corners.
Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# Essential points and sets of measure zero in a finite-dimensional manifold

## The text, paraphrased

(Definition 9.4.1, after [57]) `M` a smooth `n`-dimensional manifold with boundary and corners,
`K ⊆ M`.  (1) For `z ∈ K` and a chart `ϕ : (V(z), z) → ([0,∞)ᵏ × ℝⁿ⁻ᵏ, 0)`, the linear subspace
`Tϕ(z)(T^K_z M)` of `ℝⁿ` is the linear hull of the unit vectors `e = lim ϕ(zₖ)/|ϕ(zₖ)|`,
`zₖ ∈ K ∖ {z}`, `zₖ → z`; it does not depend on `ϕ`.  (2) `z ∈ K` is essential if some sequence
`zₖ ∈ K` with `zₖ → z` has `T^K_{zₖ} M = T_{zₖ} M`; `K^e` is the set of essential points,
`K^{ne} = K ∖ K^e`.  (Lemma 9.4.2) `K^e` is closed in `K`, `K ∖ K^e` open in `K` ("obvious").
(Definition 9.4.5) `K ⊆ M` has measure zero if `ϕ(U ∩ K)` has Lebesgue measure zero for every
smooth chart `ϕ : U → [0, ∞)ᵏ × ℝⁿ⁻ᵏ`.  (Lemma 9.4.6) The sets `K(i, i')^{ne}` have measure zero
(proof: every point of `K^{ne}` is a point of Lebesgue density `0`).

## What is formalized

The manifold is Mathlib's: a charted space `M` on a model `H` with corners `I : H → E`, `E` a
finite-dimensional real normed space, smooth (`IsManifold I ∞ M`); charts are the elements of
the maximal smooth atlas, read in `E` through `e.extend I`.  `T_zM` is `E` (Mathlib's
`TangentSpace I z`).

* `chartImage I e K = ϕ(V ∩ K)`; `relTangent I K z` (**Definition 9.4.1 (1)**: the span of the
  tangent cone of `ϕ(V ∩ K)` at `ϕ(z)` in the chart at `z`; by `span_unitDirections` this is the
  text's linear hull of unit directions).  Chart independence:
  `span_tangentConeAt_chartImage_eq_map` (the subspaces of two charts correspond under the
  derivative of the chart change), `relTangent_eq_map`, `relTangent_eq_top_iff`
  (`T^K_zM = T_zM` read in any chart).
* `essentialSet I K` (**Definition 9.4.1 (2)**, sequences as in the text), `fullSet`;
  `essentialSet_eq` (`K^e = K ∩ closure{T^K_zM = T_zM}`), **`lemma_9_4_2`** (`K^e` closed in
  `K`), `lemma_9_4_2_open`.
* `IsMeasureZero I K` (**Definition 9.4.5**, Lebesgue measure `volume` on `E`), with `mono`,
  `union`, `iUnion` (countable), and the chart criterion `isMeasureZero_of_forall_mem`
  (one chart around each point suffices; chart changes preserve null sets,
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`).
* **`lemma_9_4_6`**: `K ∖ K^e` has measure zero for every `K ⊆ M`; in fact the points where
  `T^K_zM ≠ T_zM` do (`isMeasureZero_setOf_relTangent_ne_top`).
* Witness (`ℝ²`, the model space itself): the two coordinate lines `K = (ℝ × 0) ∪ (0 × ℝ)`
  (`crossLines`) have `T^K_0 = ℝ²` and `T^K_z = ℝ × 0` or `0 × ℝ` at their other points;
  `essentialSet_crossLines` (`K^e = {0}`), `nonEssential_crossLines` (`K^{ne} = K ∖ {0}`, of
  measure zero), and `not_isMeasureZero_univ` (Definition 9.4.5 is not vacuous).

## The choices made

* "The chart `ϕ` with `ϕ(z) = 0`" is any chart of the maximal atlas, the limits are taken at
  `ϕ(z)`; the tangent cone (Mathlib's `tangentConeAt`) replaces the unit vectors (same span,
  `span_unitDirections`).  `T_zM` is identified with `E` through the chart at `z`, so
  `T^K_zM = T_zM` is `relTangent I K z = ⊤`.
* Lemma 9.4.6 is proved for every subset `K` of `M` (the text: `K = K(i, i') = Mᵢ ∩ Mᵢ'`); its
  proof needs no measurability.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Definition 9.4.1 (1) -/

/-- The image `ϕ(V ∩ K)` of `K` in the chart `ϕ = e.extend I` (`V` the chart domain). -/
def chartImage (e : OpenPartialHomeomorph M H) (K : Set M) : Set E :=
  e.extend I '' (e.source ∩ K)

/-- **Definition 9.4.1 (1), 2021 p. 429 (2017: Definition 9.12) (`T^K_z M`)**: the linear
subspace of `T_zM = E` spanned by the limit directions of `ϕ(K)` at `ϕ(z)`, read in the chart
`ϕ` at `z` (the tangent cone of `ϕ(V ∩ K)` at `ϕ(z)`; its span is the text's linear hull of unit
vectors, `span_unitDirections`). -/
def relTangent (K : Set M) (z : M) : Submodule ℝ E :=
  Submodule.span ℝ (tangentConeAt ℝ (chartImage I (chartAt H z) K) (extChartAt I z z))

variable {I}

omit [ChartedSpace H M] in
theorem chartImage_subset_range (e : OpenPartialHomeomorph M H) (K : Set M) :
    chartImage I e K ⊆ range I := by
  rintro _ ⟨w, hw, rfl⟩
  exact e.extend_target_subset_range ((e.extend I).map_source (by rw [e.extend_source]; exact hw.1))

omit [ChartedSpace H M] in
theorem extendCoordChange_apply_of_mem {e e' : OpenPartialHomeomorph M H} {z : M}
    (hze : z ∈ e.source) : I.extendCoordChange e e' (e.extend I z) = e'.extend I z := by
  change (e'.extend I) ((e.extend I).symm (e.extend I z)) = _
  rw [e.extend_left_inv hze]

omit [ChartedSpace H M] in
theorem extend_mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H} {z : M}
    (hze : z ∈ e.source) (hze' : z ∈ e'.source) :
    e.extend I z ∈ (I.extendCoordChange e e').source := by
  rw [← e.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hze, hze'⟩

omit [ChartedSpace H M] in
/-- The chart change maps the part of `ϕ(K)` in its domain into `ϕ'(K)`. -/
theorem image_chartImage_inter_subset (e e' : OpenPartialHomeomorph M H) (K : Set M) :
    I.extendCoordChange e e' '' (chartImage I e K ∩ (I.extendCoordChange e e').source) ⊆
      chartImage I e' K := by
  rintro _ ⟨_, ⟨⟨w, hw, rfl⟩, hsrc⟩, rfl⟩
  have hsrc' := hsrc
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
    PartialEquiv.symm_source, mem_inter_iff, mem_preimage] at hsrc'
  rw [e.extend_left_inv hw.1, e'.extend_source] at hsrc'
  exact ⟨w, ⟨hsrc'.2, hw.2⟩, (extendCoordChange_apply_of_mem hw.1).symm⟩

variable {n : WithTop ℕ∞}

/-- **One half of the chart independence in Definition 9.4.1 (1)**: the derivative of the chart
change `ϕ' ∘ ϕ⁻¹` maps the span of the tangent cone of `ϕ(K)` into that of `ϕ'(K)`. -/
theorem map_span_tangentConeAt_chartImage_le [IsManifold I n M] (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) {z : M} (hze : z ∈ e.source)
    (hze' : z ∈ e'.source) (K : Set M) :
    (Submodule.span ℝ (tangentConeAt ℝ (chartImage I e K) (e.extend I z))).map
        (fderivWithin ℝ (I.extendCoordChange e e') (I.extendCoordChange e e').source
          (e.extend I z) : E →ₗ[ℝ] E) ≤
      Submodule.span ℝ (tangentConeAt ℝ (chartImage I e' K) (e'.extend I z)) := by
  set φ := I.extendCoordChange e e' with hφdef
  have hp : e.extend I z ∈ φ.source := extend_mem_extendCoordChange_source hze hze'
  have hdiff : HasFDerivWithinAt φ (fderivWithin ℝ φ φ.source (e.extend I z)) φ.source
      (e.extend I z) :=
    ((I.contDiffOn_extendCoordChange he he' _ hp).differentiableWithinAt hn).hasFDerivWithinAt
  have hTC : tangentConeAt ℝ (chartImage I e K ∩ φ.source) (e.extend I z) =
      tangentConeAt ℝ (chartImage I e K) (e.extend I z) := by
    refine tangentConeAt_congr (nhdsWithin_inter_of_mem' ?_)
    exact nhdsWithin_mono _ (chartImage_subset_range e K)
      (I.extendCoordChange_source_mem_nhdsWithin hp)
  have hmaps := (hdiff.mono (inter_subset_right (s := chartImage I e K))).mapsTo_tangent_cone
  rw [Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [← hTC] at hv
  have h1 := hmaps hv
  rw [extendCoordChange_apply_of_mem hze] at h1
  exact tangentConeAt_mono (image_chartImage_inter_subset e e' K) h1

/-- The derivatives of the two chart changes `ϕ' ∘ ϕ⁻¹`, `ϕ ∘ ϕ'⁻¹` are inverse. -/
theorem fderivWithin_extendCoordChange_comp [IsManifold I n M] (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) {z : M} (hze : z ∈ e.source)
    (hze' : z ∈ e'.source) :
    (fderivWithin ℝ (I.extendCoordChange e e') (I.extendCoordChange e e').source
        (e.extend I z)).comp
      (fderivWithin ℝ (I.extendCoordChange e' e) (I.extendCoordChange e' e).source
        (e'.extend I z)) = ContinuousLinearMap.id ℝ E := by
  set φ := I.extendCoordChange e e' with hφdef
  have hsymm : I.extendCoordChange e' e = φ.symm := rfl
  have hq : e'.extend I z ∈ φ.target := by
    rw [← PartialEquiv.symm_source, ← hsymm]
    exact extend_mem_extendCoordChange_source hze' hze
  have hsq : φ.symm (e'.extend I z) = e.extend I z := by
    rw [← hsymm]; exact extendCoordChange_apply_of_mem hze'
  have hφ : ContDiffOn ℝ n φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφ' : ContDiffOn ℝ n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
  have hU : UniqueDiffWithinAt ℝ φ.target (e'.extend I z) :=
    I.uniqueDiffOn_extendCoordChange_target _ hq
  rw [hsymm, PartialEquiv.symm_source]
  have h1 := fderivWithin_comp (g := φ) (t := φ.source) (f := φ.symm) (s := φ.target)
    (x := e'.extend I z)
    (by rw [hsq]; exact (hφ _ (hsq ▸ φ.map_target hq)).differentiableWithinAt hn)
    ((hφ' _ hq).differentiableWithinAt hn) φ.mapsTo_symm hU
  rw [hsq] at h1
  rw [← h1, fderivWithin_congr' φ.rightInvOn.eqOn hq, fderivWithin_id hU]

/-- **Chart independence in Definition 9.4.1 (1)**: for two charts `ϕ, ϕ'` of the maximal
smooth atlas around `z`, the span of the tangent cone of `ϕ'(K)` at `ϕ'(z)` is the image of that
of `ϕ(K)` at `ϕ(z)` under the (invertible) derivative of the chart change `ϕ' ∘ ϕ⁻¹`. -/
theorem span_tangentConeAt_chartImage_eq_map [IsManifold I n M] (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) {z : M} (hze : z ∈ e.source)
    (hze' : z ∈ e'.source) (K : Set M) :
    Submodule.span ℝ (tangentConeAt ℝ (chartImage I e' K) (e'.extend I z)) =
      (Submodule.span ℝ (tangentConeAt ℝ (chartImage I e K) (e.extend I z))).map
        (fderivWithin ℝ (I.extendCoordChange e e') (I.extendCoordChange e e').source
          (e.extend I z) : E →ₗ[ℝ] E) := by
  refine le_antisymm ?_ (map_span_tangentConeAt_chartImage_le hn he he' hze hze' K)
  set D := fderivWithin ℝ (I.extendCoordChange e e') (I.extendCoordChange e e').source
    (e.extend I z)
  set D' := fderivWithin ℝ (I.extendCoordChange e' e) (I.extendCoordChange e' e).source
    (e'.extend I z)
  have hcomp : D.comp D' = ContinuousLinearMap.id ℝ E :=
    fderivWithin_extendCoordChange_comp hn he he' hze hze'
  have h2 := Submodule.map_mono (f := (D : E →ₗ[ℝ] E))
    (map_span_tangentConeAt_chartImage_le hn he' he hze' hze K)
  refine le_trans (le_of_eq ?_) h2
  have hid : (D : E →ₗ[ℝ] E).comp (D' : E →ₗ[ℝ] E) = LinearMap.id := by
    ext v
    exact congrArg (fun L : E →L[ℝ] E => L v) hcomp
  rw [← Submodule.map_comp, hid, Submodule.map_id]

/-- `T^K_zM` read in another chart `ϕ'` of the maximal atlas: the image of `relTangent` under the
derivative of the chart change. -/
theorem relTangent_eq_map [IsManifold I n M] (hn : n ≠ 0) {e' : OpenPartialHomeomorph M H}
    (he' : e' ∈ IsManifold.maximalAtlas I n M) {z : M} (hze' : z ∈ e'.source) (K : Set M) :
    Submodule.span ℝ (tangentConeAt ℝ (chartImage I e' K) (e'.extend I z)) =
      (relTangent I K z).map
        (fderivWithin ℝ (I.extendCoordChange (chartAt H z) e')
          (I.extendCoordChange (chartAt H z) e').source (extChartAt I z z) : E →ₗ[ℝ] E) :=
  span_tangentConeAt_chartImage_eq_map hn (IsManifold.chart_mem_maximalAtlas z) he'
    (mem_chart_source H z) hze' K

/-- **`T^K_zM = T_zM` does not depend on the chart**: it holds in the chart at `z` iff the
tangent cone of `ϕ'(K)` spans `E` for any chart `ϕ'` of the maximal atlas around `z`. -/
theorem relTangent_eq_top_iff [IsManifold I n M] (hn : n ≠ 0) {e' : OpenPartialHomeomorph M H}
    (he' : e' ∈ IsManifold.maximalAtlas I n M) {z : M} (hze' : z ∈ e'.source) (K : Set M) :
    relTangent I K z = ⊤ ↔
      Submodule.span ℝ (tangentConeAt ℝ (chartImage I e' K) (e'.extend I z)) = ⊤ := by
  have he : chartAt H z ∈ IsManifold.maximalAtlas I n M := IsManifold.chart_mem_maximalAtlas z
  have hz : z ∈ (chartAt H z).source := mem_chart_source H z
  have hsurj : ∀ {e₁ e₂ : OpenPartialHomeomorph M H}, e₁ ∈ IsManifold.maximalAtlas I n M →
      e₂ ∈ IsManifold.maximalAtlas I n M → z ∈ e₁.source → z ∈ e₂.source →
      LinearMap.range (fderivWithin ℝ (I.extendCoordChange e₁ e₂)
        (I.extendCoordChange e₁ e₂).source (e₁.extend I z) : E →ₗ[ℝ] E) = ⊤ := by
    intro e₁ e₂ h₁ h₂ hz₁ hz₂
    refine LinearMap.range_eq_top.2 fun v => ⟨fderivWithin ℝ (I.extendCoordChange e₂ e₁)
      (I.extendCoordChange e₂ e₁).source (e₂.extend I z) v, ?_⟩
    exact congrArg (fun L : E →L[ℝ] E => L v)
      (fderivWithin_extendCoordChange_comp hn h₁ h₂ hz₁ hz₂)
  constructor
  · intro h
    rw [relTangent_eq_map hn he' hze' K, h, Submodule.map_top]
    exact hsurj he he' hz hze'
  · intro h
    have h2 := span_tangentConeAt_chartImage_eq_map hn he' he hze' hz K
    unfold relTangent
    change Submodule.span ℝ (tangentConeAt ℝ (chartImage I (chartAt H z) K)
      ((chartAt H z).extend I z)) = ⊤
    rw [h2, h, Submodule.map_top]
    exact hsurj he' he hze' hz

/-! ### Definition 9.4.1 (2) and Lemma 9.4.2 -/

variable (I) in
/-- The points `z ∈ K` with `T^K_zM = T_zM`. -/
def fullSet (K : Set M) : Set M := {z | z ∈ K ∧ relTangent I K z = ⊤}

variable (I) in
/-- **Definition 9.4.1 (2), 2021 p. 429 (2017: Definition 9.12 (2)) (essential points)**: `z ∈ K`
is essential if there is a sequence `zₖ ∈ K` with `zₖ → z` and `T^K_{zₖ}M = T_{zₖ}M`; `K^e` is
the set of essential points, `K^{ne} = K ∖ K^e` that of the non-essential ones. -/
def essentialSet (K : Set M) : Set M :=
  {z | z ∈ K ∧ ∃ u : ℕ → M, (∀ k, u k ∈ K ∧ relTangent I K (u k) = ⊤) ∧ Tendsto u atTop (𝓝 z)}

variable (I) in
include I in
/-- A manifold is first countable (its charts are homeomorphisms onto subsets of `H ⊆ E`). -/
theorem firstCountableTopology_of_chartedSpace : FirstCountableTopology M := by
  have : FirstCountableTopology H := I.isClosedEmbedding.isEmbedding.firstCountableTopology
  refine ⟨fun z => ?_⟩
  have h := (chartAt H z).symm.map_nhds_eq ((chartAt H z).map_source (mem_chart_source H z))
  rw [(chartAt H z).left_inv (mem_chart_source H z)] at h
  rw [← h]
  infer_instance

/-- `K^e = K ∩ closure{z ∈ K | T^K_zM = T_zM}` (sequences suffice in a manifold). -/
theorem essentialSet_eq (K : Set M) : essentialSet I K = K ∩ closure (fullSet I K) := by
  have := firstCountableTopology_of_chartedSpace I (M := M)
  ext z
  constructor
  · rintro ⟨hz, u, hu, hlim⟩
    exact ⟨hz, mem_closure_of_tendsto hlim (Eventually.of_forall fun k => hu k)⟩
  · rintro ⟨hz, hcl⟩
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
    exact ⟨hz, u, hu, hlim⟩

/-- **Lemma 9.4.2, 2021 p. 430 (2017: Lemma 9.11)**: `K^e` is closed in `K`. -/
theorem lemma_9_4_2 (K : Set M) : IsClosed (((↑) : K → M) ⁻¹' essentialSet I K) := by
  rw [essentialSet_eq]
  have : ((↑) : K → M) ⁻¹' (K ∩ closure (fullSet I K)) =
      ((↑) : K → M) ⁻¹' closure (fullSet I K) := by
    ext ⟨z, hz⟩; simp
  rw [this]
  exact isClosed_closure.preimage continuous_subtype_val

/-- **Lemma 9.4.2 (second half)**: `K ∖ K^e` is open in `K`. -/
theorem lemma_9_4_2_open (K : Set M) : IsOpen (((↑) : K → M) ⁻¹' (K \ essentialSet I K)) := by
  have : ((↑) : K → M) ⁻¹' (K \ essentialSet I K) = (((↑) : K → M) ⁻¹' essentialSet I K)ᶜ := by
    ext ⟨z, hz⟩; simp
  rw [this]
  exact (lemma_9_4_2 K).isOpen_compl

theorem diff_essentialSet_subset (K : Set M) :
    K \ essentialSet I K ⊆ {z | z ∈ K ∧ relTangent I K z ≠ ⊤} := by
  rintro z ⟨hz, hne⟩
  refine ⟨hz, fun h => hne ⟨hz, fun _ => z, fun _ => ⟨hz, h⟩, tendsto_const_nhds⟩⟩

/-! ### Definition 9.4.5 -/

variable [MeasureSpace E]

variable (I) in
/-- **Definition 9.4.5, 2021 p. 431 (2017: Definition 9.13) (measure zero)**: `K ⊆ M` has measure
zero if `ϕ(U ∩ K)` has Lebesgue measure zero for every smooth chart `ϕ : U → E` (every chart of
the maximal smooth atlas, read in `E`). -/
def IsMeasureZero (K : Set M) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas I ∞ M, volume (chartImage I e K) = 0

theorem IsMeasureZero.mono {K K' : Set M} (h : IsMeasureZero I K') (hK : K ⊆ K') :
    IsMeasureZero I K := fun e he =>
  measure_mono_null (image_mono (inter_subset_inter_right _ hK)) (h e he)

theorem isMeasureZero_empty : IsMeasureZero I (∅ : Set M) := fun e _ => by
  simp [chartImage]

theorem IsMeasureZero.union {K K' : Set M} (h : IsMeasureZero I K) (h' : IsMeasureZero I K') :
    IsMeasureZero I (K ∪ K') := fun e he => by
  rw [chartImage, inter_union_distrib_left, image_union]
  exact measure_union_null (h e he) (h' e he)

theorem isMeasureZero_iUnion {ι : Type*} [Countable ι] {K : ι → Set M}
    (h : ∀ i, IsMeasureZero I (K i)) : IsMeasureZero I (⋃ i, K i) := fun e he => by
  rw [chartImage, inter_iUnion, image_iUnion]
  exact measure_iUnion_null fun i => h i e he

/-- **Chart independence of Definition 9.4.5**: if every point of `K` lies in a chart of the
maximal atlas in which (the whole of) `K` has measure-zero image, then `K` has measure zero in
every chart.  (Chart changes are `C¹` on `range I`, and `C¹` maps send null sets to null sets;
a countable subcover exists since `E` is second countable.) -/
theorem isMeasureZero_of_forall_mem [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [IsManifold I ∞ M] {K : Set M}
    (h : ∀ z ∈ K, ∃ e ∈ IsManifold.maximalAtlas I ∞ M, z ∈ e.source ∧
      volume (chartImage I e K) = 0) :
    IsMeasureZero I K := by
  intro e' he'
  set S' := chartImage I e' K with hS'
  choose c hc hzc hc0 using h
  -- the open cover of `S'` (as a subspace) by the chart domains of the `c z`
  let W : ↥(e'.source ∩ K) → Set S' := fun z =>
    ((↑) : S' → E) ⁻¹' ((e'.extend I).symm ⁻¹' (c z.1 z.2.2).source)
  have hS'sub : S' ⊆ (e'.extend I).target := by
    rintro _ ⟨w, hw, rfl⟩
    exact (e'.extend I).map_source (by rw [e'.extend_source]; exact hw.1)
  have hW : ∀ z, IsOpen (W z) := by
    intro z
    have hcont : Continuous fun q : S' => (e'.extend I).symm q :=
      (e'.continuousOn_extend_symm (I := I)).comp_continuous continuous_subtype_val
        fun q => hS'sub q.2
    exact (c z.1 z.2.2).open_source.preimage hcont
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hcover : S' ⊆ ⋃ z ∈ T, I.extendCoordChange (c z.1 z.2.2) e' ''
      (chartImage I (c z.1 z.2.2) K ∩ (I.extendCoordChange (c z.1 z.2.2) e').source) := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := hq
    have hmem : (⟨e'.extend I w, ⟨w, hw, rfl⟩⟩ : S') ∈ ⋃ z, W z := by
      refine mem_iUnion.2 ⟨⟨w, hw⟩, ?_⟩
      change (e'.extend I).symm (e'.extend I w) ∈ (c w hw.2).source
      rw [e'.extend_left_inv hw.1]
      exact hzc w hw.2
    rw [← hTU] at hmem
    obtain ⟨z, hzT, hz⟩ := mem_iUnion₂.1 hmem
    change (e'.extend I).symm (e'.extend I w) ∈ (c z.1 z.2.2).source at hz
    rw [e'.extend_left_inv hw.1] at hz
    exact mem_iUnion₂.2 ⟨z, hzT, (c z.1 z.2.2).extend I w, ⟨⟨w, ⟨hz, hw.2⟩, rfl⟩,
      extend_mem_extendCoordChange_source hz hw.1⟩, extendCoordChange_apply_of_mem hz⟩
  refine measure_mono_null hcover ((measure_biUnion_null_iff hT).2 fun z _ => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null inter_subset_left (hc0 z.1 z.2.2))
  exact ((I.contDiffOn_extendCoordChange (hc z.1 z.2.2) he').differentiableOn
    (by simp)).mono inter_subset_right

/-! ### Lemma 9.4.6 -/

/-- **The points with `T^K_zM ≠ T_zM` form a set of measure zero** (the core of Lemma 9.4.6):
in every chart they are among the points of `ϕ(K)` at which the tangent cone of `ϕ(K)` does not
span `E`, a Lebesgue null set (`addHaar_setOf_span_tangentConeAt_ne_top`). -/
theorem isMeasureZero_setOf_relTangent_ne_top [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [IsManifold I ∞ M] (K : Set M) :
    IsMeasureZero I {z | z ∈ K ∧ relTangent I K z ≠ ⊤} := by
  intro e he
  refine measure_mono_null ?_
    (addHaar_setOf_span_tangentConeAt_ne_top volume (chartImage I e K))
  rintro _ ⟨w, ⟨hwe, hwK, hw⟩, rfl⟩
  refine ⟨⟨w, ⟨hwe, hwK⟩, rfl⟩, fun h => hw ?_⟩
  exact (relTangent_eq_top_iff (n := ∞) (by simp) he hwe K).2 h

/-- **Lemma 9.4.6, 2021 p. 431 (2017: Lemma 9.14)**: the non-essential points `K^{ne} = K ∖ K^e`
of any subset `K` of a smooth finite-dimensional manifold with boundary and corners form a set of
measure zero (Definition 9.4.5).  (The text states it for `K = K(i, i') = Mᵢ ∩ Mᵢ'`.) -/
theorem lemma_9_4_6 [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [IsManifold I ∞ M] (K : Set M) :
    IsMeasureZero I (K \ essentialSet I K) :=
  (isMeasureZero_setOf_relTangent_ne_top K).mono (diff_essentialSet_subset K)

/-! ### Witnesses in the model space `ℝ²` -/

section Witness

/-- The image of `K` in the chart at `z` of the model space is `K`. -/
theorem chartImage_chartAt_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set F) (z : F) : chartImage 𝓘(ℝ, F) (chartAt F z) K = K := by
  simp [chartImage, chartAt_self_eq, OpenPartialHomeomorph.extend]

theorem relTangent_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set F) (z : F) :
    relTangent 𝓘(ℝ, F) K z = Submodule.span ℝ (tangentConeAt ℝ K z) := by
  rw [relTangent, chartImage_chartAt_self, extChartAt_model_space_eq_id]
  rfl

/-- The tangent cone of a closed subspace `L` at a point of `L` lies in `L`. -/
theorem tangentConeAt_subset_submodule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : Submodule ℝ F} (hL : IsClosed (L : Set F)) {z : F} (hz : z ∈ L) :
    tangentConeAt ℝ (L : Set F) z ⊆ L := by
  intro v hv
  obtain ⟨c, d, -, hds, hcd⟩ := (mem_tangentConeAt_iff_exists_seq).1 hv
  refine hL.mem_of_tendsto hcd (hds.mono fun k hk => ?_)
  have : d k ∈ L := by simpa using L.sub_mem hk hz
  exact L.smul_mem _ this

/-- The horizontal line `ℝ × 0` of `ℝ²`. -/
def lineH : Submodule ℝ (Fin 2 → ℝ) := LinearMap.ker (LinearMap.proj 1)

/-- The vertical line `0 × ℝ` of `ℝ²`. -/
def lineV : Submodule ℝ (Fin 2 → ℝ) := LinearMap.ker (LinearMap.proj 0)

theorem mem_lineH {v : Fin 2 → ℝ} : v ∈ lineH ↔ v 1 = 0 := Iff.rfl

theorem mem_lineV {v : Fin 2 → ℝ} : v ∈ lineV ↔ v 0 = 0 := Iff.rfl

theorem isClosed_lineH : IsClosed (lineH : Set (Fin 2 → ℝ)) :=
  isClosed_eq (continuous_apply 1) continuous_const

theorem isClosed_lineV : IsClosed (lineV : Set (Fin 2 → ℝ)) :=
  isClosed_eq (continuous_apply 0) continuous_const

/-- **The two crossing lines** `K = (ℝ × 0) ∪ (0 × ℝ) ⊆ ℝ²`. -/
def crossLines : Set (Fin 2 → ℝ) := (lineH : Set (Fin 2 → ℝ)) ∪ lineV

theorem lineH_ne_top : lineH ≠ ⊤ := by
  intro h
  have : (Pi.single 1 1 : Fin 2 → ℝ) ∈ lineH := by rw [h]; exact Submodule.mem_top
  simp [mem_lineH] at this

theorem lineV_ne_top : lineV ≠ ⊤ := by
  intro h
  have : (Pi.single 0 1 : Fin 2 → ℝ) ∈ lineV := by rw [h]; exact Submodule.mem_top
  simp [mem_lineV] at this

theorem mem_tangentConeAt_of_mem_submodule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : Submodule ℝ F} {A : Set F} (hLA : (L : Set F) ⊆ A) {v : F} (hv : v ∈ L) :
    v ∈ tangentConeAt ℝ A 0 := by
  have := mem_tangentConeAt_of_segment_subset (x := (0 : F)) (y := v)
    (((L.convex).segment_subset L.zero_mem hv).trans hLA)
  simpa using this

/-- At the crossing point, `T^K_0 = ℝ²`. -/
theorem relTangent_crossLines_zero : relTangent 𝓘(ℝ, Fin 2 → ℝ) crossLines 0 = ⊤ := by
  rw [relTangent_self, eq_top_iff]
  intro v _
  have h0 : (Pi.single 0 1 : Fin 2 → ℝ) ∈ tangentConeAt ℝ crossLines 0 :=
    mem_tangentConeAt_of_mem_submodule (L := lineH) subset_union_left (by simp [mem_lineH])
  have h1 : (Pi.single 1 1 : Fin 2 → ℝ) ∈ tangentConeAt ℝ crossLines 0 :=
    mem_tangentConeAt_of_mem_submodule (L := lineV) subset_union_right (by simp [mem_lineV])
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ℝ) + v 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    funext j; fin_cases j <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span h0))
    (Submodule.smul_mem _ _ (Submodule.subset_span h1))

/-- Away from the crossing point, `T^K_z` is the line through `z`. -/
theorem relTangent_crossLines_ne_top {z : Fin 2 → ℝ} (hz : z ∈ crossLines) (hz0 : z ≠ 0) :
    relTangent 𝓘(ℝ, Fin 2 → ℝ) crossLines z ≠ ⊤ := by
  rw [relTangent_self]
  rcases hz with hzH | hzV
  · have hz1 : z 1 = 0 := hzH
    have hz0' : z 0 ≠ 0 := fun h => hz0 (by funext j; fin_cases j <;> simp [h, hz1])
    have hball : Metric.ball z |z 0| ∈ 𝓝 z := Metric.ball_mem_nhds z (abs_pos.2 hz0')
    have hsub : crossLines ∩ Metric.ball z |z 0| ⊆ lineH := by
      rintro v ⟨hvH | hvV, hvb⟩
      · exact hvH
      · exfalso
        have h1 : dist (v 0) (z 0) ≤ dist v z := dist_le_pi_dist v z 0
        have hv0 : v 0 = 0 := hvV
        rw [hv0, Real.dist_eq, zero_sub, abs_neg] at h1
        exact absurd (lt_of_le_of_lt h1 hvb) (lt_irrefl _)
    intro htop
    apply lineH_ne_top
    rw [eq_top_iff, ← htop, ← tangentConeAt_inter_nhds hball]
    refine Submodule.span_le.2 ((tangentConeAt_mono hsub).trans ?_)
    exact tangentConeAt_subset_submodule isClosed_lineH hzH
  · have hz1 : z 0 = 0 := hzV
    have hz0' : z 1 ≠ 0 := fun h => hz0 (by funext j; fin_cases j <;> simp [h, hz1])
    have hball : Metric.ball z |z 1| ∈ 𝓝 z := Metric.ball_mem_nhds z (abs_pos.2 hz0')
    have hsub : crossLines ∩ Metric.ball z |z 1| ⊆ lineV := by
      rintro v ⟨hvH | hvV, hvb⟩
      · exfalso
        have h1 : dist (v 1) (z 1) ≤ dist v z := dist_le_pi_dist v z 1
        have hv0 : v 1 = 0 := hvH
        rw [hv0, Real.dist_eq, zero_sub, abs_neg] at h1
        exact absurd (lt_of_le_of_lt h1 hvb) (lt_irrefl _)
      · exact hvV
    intro htop
    apply lineV_ne_top
    rw [eq_top_iff, ← htop, ← tangentConeAt_inter_nhds hball]
    refine Submodule.span_le.2 ((tangentConeAt_mono hsub).trans ?_)
    exact tangentConeAt_subset_submodule isClosed_lineV hzV

/-- **The essential points of the crossing lines**: `K^e = {0}`. -/
theorem essentialSet_crossLines : essentialSet 𝓘(ℝ, Fin 2 → ℝ) crossLines = {0} := by
  have h0 : (0 : Fin 2 → ℝ) ∈ crossLines := Or.inl lineH.zero_mem
  ext z
  constructor
  · rintro ⟨hz, u, hu, hlim⟩
    have hu0 : ∀ k, u k = 0 := fun k => by
      by_contra hne
      exact relTangent_crossLines_ne_top (hu k).1 hne (hu k).2
    have : Tendsto u atTop (𝓝 0) := by
      rw [show u = fun _ => 0 from funext hu0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim this
  · rintro rfl
    exact ⟨h0, fun _ => 0, fun _ => ⟨h0, relTangent_crossLines_zero⟩, tendsto_const_nhds⟩

/-- **Lemma 9.4.6 for the crossing lines**: `K^{ne} = K ∖ {0}` (nonempty) has measure zero. -/
theorem nonEssential_crossLines :
    crossLines \ essentialSet 𝓘(ℝ, Fin 2 → ℝ) crossLines = crossLines \ {0} ∧
      (crossLines \ {0}).Nonempty ∧ IsMeasureZero 𝓘(ℝ, Fin 2 → ℝ) (crossLines \ {0}) := by
  refine ⟨by rw [essentialSet_crossLines], ⟨Pi.single 0 1, Or.inl (by simp [mem_lineH]), ?_⟩, ?_⟩
  · intro h
    have := congrFun (mem_singleton_iff.1 h) 0
    simp at this
  · rw [← essentialSet_crossLines]
    exact lemma_9_4_6 crossLines

/-- **Definition 9.4.5 is not vacuous**: `ℝ²` itself does not have measure zero. -/
theorem not_isMeasureZero_univ : ¬ IsMeasureZero 𝓘(ℝ, Fin 2 → ℝ) (univ : Set (Fin 2 → ℝ)) := by
  intro h
  have h0 := h (chartAt (Fin 2 → ℝ) (0 : Fin 2 → ℝ))
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin 2 → ℝ)) (n := ∞) 0)
  rw [chartImage_chartAt_self] at h0
  exact (Metric.measure_closedBall_pos volume (0 : Fin 2 → ℝ) one_pos).ne'
    (measure_mono_null (subset_univ _) h0)

end Witness

end Polyfold
