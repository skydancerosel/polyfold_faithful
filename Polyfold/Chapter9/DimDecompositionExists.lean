import Polyfold.Chapter9.DimDecompositionUnique

/-!
# Proposition 9.1.11: existence of the local dimensional decomposition (gap G.96)

2021 Proposition 9.1.11, pp. 407–408 (2017: Proposition 9.2, p. 297), says that a branched
ep⁺-subgroupoid `Θ` is `Θ_0 + Θ_1 + ⋯` with `Θ_k` a `k`-dimensional branched ep⁺-subgroupoid,
the sum being locally finite.  `DimDecompositionUnique.lean` proves that a *local* decomposition
(`IsLocalDimDecomposition`: near every point of `supp(Θ)`, the decomposition of a local branching
structure) is unique; among all decompositions the uniqueness does not hold as we read it
(`not_proposition_9_1_11_rn`).  This file proves the existence: the local `Θ_k` of the proof glue
into functors on all of `X`.

## The construction

The proof of the text puts `Θ_k(y) = ∑_{i ∈ I_k, y ∈ Mᵢ} σᵢ` on `U(x)`, where `I_k` indexes the
`k`-dimensional `Mᵢ` of a local branching structure at `x`.  Here `Θ_k(y) = ∑_{i ∈ I_k} σᵢ` for
a chosen *labelled* local branching structure at `y` (one whose `Mᵢ` have constant dimensions
`dim i`, `HasLabelledBranchingAt`), and `Θ_k(y) = 0` if there is none (`dimComponent`).  Every
`Mᵢ` passes through the base point, so this is the value at `y` of the local `Θ_k` at `y`.

## What is formalized

* `dimComponent_eq_self`: by Proposition 9.1.12 (2021, p. 408), `Θ_k(x)` is the same for every
  labelled structure at `x`; `dimComponent_eq_of_mem`: on all of `U(x)`, `Θ_k` is the
  `k`-dimensional part of any labelled structure at `x` (restrict it to `y ∈ U(x)`,
  `restrictAt`, `dimPart_restrictAt`).
* `isFunctorial_dimComponent`: `Θ_k(s φ) = Θ_k(t φ)` for every morphism `φ`.  A labelled structure
  at `s φ` is transported along `φ̂` (`LocalBranchingStructure.transport`,
  `isSubmanifoldOfDim_transport`); if there is none at `s φ` but one at `t φ`, it is transported
  along `φ⁻¹`.
* `isClosed_orbitSupp_dimComponent`: `|supp(Θ_k)|` is closed in `|supp(Θ)|`, hence paracompact
  (`paracompactSpace_orbitSupp_dimComponent`, Definition 9.1.2 (1)).
* `dimComponentStructure` (the `k`-dimensional sheets of a labelled structure at `x`, on `U(x)`),
  `isBranchedEpSubgroupoid_dimComponent`, `isNDimensional_dimComponent`,
  `isDimDecomposition_dimComponent`, `isLocalDimDecomposition_dimComponent`;
  `dimComponent_locallyFinite_of_mem` (local finiteness at the points of `supp(Θ)`) and
  `isLocallyFiniteFamily_dimComponent` (at every point, when the dimensions of submanifolds are
  bounded).
* **Proposition 9.1.11 in the reading of its proof**, `Proposition_9_1_11_local`: a unique local
  dimensional decomposition, and it is locally finite.  `existsUnique_localDimDecomposition` and
  `proposition_9_1_11_local_of` (any ep-groupoid, under the hypotheses below);
  `proposition_9_1_11_local_rn` (every ep-groupoid with `X.PObj = rnPolyfold m`, any morphisms,
  no hypothesis), `proposition_9_1_11_local_trivial_rn`, `isDimDecomposition_dimComponent_rn`.
* `MPolyfold.rn_hasDimAt_le`: a submanifold of `ℝᵐ` has dimension at most `m`.
* Witness: `dimComponent_axis2`: for the indicator of the line `L` of `not_proposition_9_1_11_rn`
  the construction gives `Θ_0 = 0`, `Θ_1 = 1_L` (`decompB`).

## The hypotheses of the general case, and why they can be met

* `X.Proposition_9_1_12`: proved over `ℝᵐ` (`proposition_9_1_12_rn`) and under the graph
  representation (`proposition_9_1_12_of_hasGraphChartAt`).
* `HasLocallyConstantDimAt` on `supp(Θ)` (2021 Remark 9.1.1, p. 402; 2017: Remark 9.1, p. 291):
  it gives the labels (`exists_restrict_labelled`); proved in `ℝᵐ` (`hasLocallyConstantDimAt_rn`).
* For `IsLocallyFiniteFamily` only, a bound `N` on the dimensions of submanifolds of `X`;
  `N = m` in `ℝᵐ` (`rn_hasDimAt_le`).

## What the text leaves implicit, and the choices made

* The text takes a symmetric structure (Lemma 9.1.7) so that `Θ_k` is `G_x`-invariant on `U(x)`.
  Here `Θ_k` is defined pointwise and its functoriality is checked along every morphism, between
  different objects too, by transport and Proposition 9.1.12 at the target; no symmetric
  structure is used.
* The paracompactness of `|supp(Θ_k)|` (Definition 9.1.2 (1), new in 2021) is not discussed in
  the proof; it follows from the closedness of `|supp(Θ_k)|` in `|supp(Θ)|`.
* "The sum is locally finite" is `IsLocallyFiniteFamily`: every object, also off `supp(Θ)`, has a
  neighbourhood on which only finitely many `Θ_k` are not identically zero.  At the points of
  `supp(Θ)` the construction gives it; at points of the closure of `supp(Θ)` outside `supp(Θ)` it
  is derived here from a bound on the dimensions.

## What remains of gap G.96

For ep-groupoids whose object space is `ℝᵐ`: nothing (`proposition_9_1_11_local_rn`).  In
general the gluing is done (`existsUnique_localDimDecomposition`) up to its inputs: Proposition
9.1.12 beyond the graph representation, the local constancy of the dimension (Remark 9.1.1)
beyond `ℝᵐ`, and, for local finiteness off `supp(Θ)` without a dimension bound, an argument not
given here.
-/

open Set Filter Topology

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj} (B : X.LocalBranchingStructure Θ x)

/-- The dimensional parts are nonnegative. -/
theorem dimPart_nonneg (dim : B.ι → ℕ) (k : ℕ) (y : Obj) : 0 ≤ B.dimPart dim k y := by
  unfold dimPart
  exact Finset.sum_nonneg fun i _ => (B.σ_pos i).le

/-- The dimensional parts vanish on `U(x) ∖ supp(Θ)`. -/
theorem dimPart_eq_zero_of_not_mem_supp (dim : B.ι → ℕ) (k : ℕ) {y : Obj} (hy : y ∈ B.U)
    (hys : y ∉ supp Θ) : B.dimPart dim k y = 0 := by
  unfold dimPart
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_filter] at hi
  exact (hys ((B.mem_supp_iff hy).2 ⟨i, hi.2.2⟩)).elim

open scoped Classical in
/-- At the base point every `Mᵢ` passes through `x`, so `Θ_k(x) = ∑_{i ∈ I_k} σᵢ`. -/
theorem dimPart_self (dim : B.ι → ℕ) (k : ℕ) :
    B.dimPart dim k x = ∑ i with dim i = k, B.σ i := by
  unfold dimPart
  exact Finset.sum_congr (Finset.filter_congr fun i _ => by simp [B.mem_M i]) fun _ _ => rfl

/-- The restriction to a point `y ∈ U(x)` (`restrictAt`) keeps the dimension labels. -/
theorem isSubmanifoldOfDim_restrictAt {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) {y : Obj} (hy : y ∈ B.U)
    (i : (B.restrictAt hy).ι) :
    X.PObj.IsSubmanifoldOfDim ((B.restrictAt hy).M i) (dim i.1) :=
  (hdim i.1).inter_isOpen (B.isOpen_nbhdAt y)

open scoped Classical in
/-- The restriction to `y ∈ U(x)` has, at `y`, the dimensional parts of the structure at `x`. -/
theorem dimPart_restrictAt (dim : B.ι → ℕ) {y : Obj} (hy : y ∈ B.U) (k : ℕ) :
    (B.restrictAt hy).dimPart (fun i => dim i.1) k y = B.dimPart dim k y := by
  unfold dimPart
  refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun i hi => ?_) (fun _ _ => rfl)
  · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ha
    have h2' : y ∈ B.M a.1 ∩ B.nbhdAt y := h2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2'.1⟩
  · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hi
    refine ⟨⟨i, h2⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, ?_⟩, rfl⟩
    exact (⟨h2, B.mem_nbhdAt_self hy⟩ : y ∈ B.M i ∩ B.nbhdAt y)

/-- Transport along a morphism keeps the dimension labels (`φ̂` is an sc-diffeomorphism). -/
theorem isSubmanifoldOfDim_transport (hΘ : X.IsFunctorial Θ) {φ : Mor}
    (B : X.LocalBranchingStructure Θ (X.src φ)) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) :
    ∀ i, X.PObj.IsSubmanifoldOfDim ((B.transport hΘ φ).M i) (dim i) := fun i =>
  ((hdim i).inter_isOpen (X.isScDiffeoOn_hat' φ).isScSmoothOn.isOpen).image_of_isScDiffeoOn
    (X.isScDiffeoOn_hat' φ) inter_subset_right

end LocalBranchingStructure

/-! ### The global `Θ_k` -/

variable (X) in
/-- A **labelled** local branching structure of `Θ` at `x` exists: one whose submanifolds have
constant dimensions `dim i` (the splitting `I = I_0 ⊔ ⋯ ⊔ I_n` of the proof of Proposition
9.1.11). -/
def HasLabelledBranchingAt (Θ : Obj → ℚ) (x : Obj) : Prop :=
  ∃ (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ),
    ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)

open scoped Classical in
variable (X) in
/-- **The `k`-dimensional part `Θ_k` of `Θ`** (the proof of Proposition 9.1.11, 2021 p. 408):
`Θ_k(y) = ∑_{i ∈ I_k} σᵢ` for a chosen labelled local branching structure at `y`, and `0` if
there is none (in particular off `supp(Θ)`).  By Proposition 9.1.12 the value does not depend on
the structure (`dimComponent_eq_self`), and near `x` it is the `k`-dimensional part of any
labelled structure at `x` (`dimComponent_eq_of_mem`). -/
def dimComponent (Θ : Obj → ℚ) (k : ℕ) (y : Obj) : ℚ :=
  if h : X.HasLabelledBranchingAt Θ y then h.choose.dimPart h.choose_spec.choose k y else 0

/-- Off `supp(Θ)`, `Θ_k = 0`. -/
theorem dimComponent_eq_zero {k : ℕ} {y : Obj} (hy : y ∉ supp Θ) : X.dimComponent Θ k y = 0 := by
  unfold dimComponent
  split_ifs with h
  · exact h.choose.dimPart_eq_zero_of_not_mem_supp _ k h.choose.mem_U hy
  · rfl

theorem dimComponent_nonneg (k : ℕ) (y : Obj) : 0 ≤ X.dimComponent Θ k y := by
  unfold dimComponent
  split_ifs with h
  · exact h.choose.dimPart_nonneg _ k y
  · exact le_rfl

/-- `supp(Θ_k) ⊆ supp(Θ)`. -/
theorem supp_dimComponent_subset (k : ℕ) : supp (X.dimComponent Θ k) ⊆ supp Θ := fun y hy => by
  by_contra h
  simp [supp, dimComponent_eq_zero h] at hy

/-- **`Θ_k(x)` does not depend on the structure** (Proposition 9.1.12): for every labelled local
branching structure `B` at `x`, `Θ_k(x) = B_k(x)`. -/
theorem dimComponent_eq_self (h912 : X.Proposition_9_1_12) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {x : Obj} (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (k : ℕ) :
    X.dimComponent Θ k x = B.dimPart dim k x := by
  have hex : X.HasLabelledBranchingAt Θ x := ⟨B, dim, hdim⟩
  rw [dimComponent, dif_pos hex]
  obtain ⟨V, -, hxV, -, hagree⟩ := h912 Θ hΘ x hex.choose B hex.choose_spec.choose dim
    hex.choose_spec.choose_spec hdim
  exact hagree k x hxV

/-- **Near `x`, `Θ_k` is the `k`-dimensional part of any labelled structure at `x`**: on all of
`U(x)` (restrict the structure to `y ∈ U(x)` and apply `dimComponent_eq_self` at `y`). -/
theorem dimComponent_eq_of_mem (h912 : X.Proposition_9_1_12) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {x : Obj} (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (k : ℕ) {y : Obj} (hy : y ∈ B.U) :
    X.dimComponent Θ k y = B.dimPart dim k y := by
  rw [dimComponent_eq_self h912 hΘ (B.restrictAt hy) (B.isSubmanifoldOfDim_restrictAt hdim hy) k,
    B.dimPart_restrictAt dim hy k]

/-- Under the local constancy of the dimension at `x ∈ supp(Θ)` (2021 Remark 9.1.1, p. 402), a
labelled structure exists at `x`. -/
theorem hasLabelledBranchingAt (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj}
    (hLC : X.PObj.HasLocallyConstantDimAt x) (hx : x ∈ supp Θ) : X.HasLabelledBranchingAt Θ x := by
  obtain ⟨B⟩ := hΘ.localBranching x hx
  obtain ⟨V, hV, hxV, hVU, dim, hdim⟩ := B.exists_restrict_labelled hLC
  exact ⟨B.restrict hV hxV hVU, dim, hdim⟩

/-- `Θ_k(s φ) = Θ_k(t φ)` when there is a labelled structure at `s φ` (transport it along `φ`). -/
theorem dimComponent_eq_of_isomorphic (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {x y : Obj} (hxy : ∃ φ : Mor, X.src φ = x ∧ X.tgt φ = y)
    (hx : X.HasLabelledBranchingAt Θ x) (k : ℕ) : X.dimComponent Θ k x = X.dimComponent Θ k y := by
  obtain ⟨φ, rfl, rfl⟩ := hxy
  obtain ⟨B, dim, hdim⟩ := hx
  rw [dimComponent_eq_self h912 hΘ B hdim,
    dimComponent_eq_self h912 hΘ (B.transport hΘ.isFunctorial φ)
      (B.isSubmanifoldOfDim_transport hΘ.isFunctorial hdim),
    B.dimPart_self]
  exact ((B.transport hΘ.isFunctorial φ).dimPart_self dim k).symm

/-- **`Θ_k` is a functor** (compatibility across morphisms between different objects). -/
theorem isFunctorial_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (k : ℕ) : X.IsFunctorial (X.dimComponent Θ k) := by
  intro φ
  by_cases h1 : X.HasLabelledBranchingAt Θ (X.src φ)
  · exact dimComponent_eq_of_isomorphic h912 hΘ ⟨φ, rfl, rfl⟩ h1 k
  by_cases h2 : X.HasLabelledBranchingAt Θ (X.tgt φ)
  · exact (dimComponent_eq_of_isomorphic h912 hΘ ⟨X.inv φ, X.src_inv φ, X.tgt_inv φ⟩ h2 k).symm
  · rw [dimComponent, dif_neg h1, dimComponent, dif_neg h2]

/-- If the labelled structure at `x` has no `k`-dimensional sheet (equivalently `x ∉ supp(Θ_k)`),
then `Θ_k = 0` on `U(x)`. -/
theorem dimComponent_eq_zero_of_not_mem (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj} (B : X.LocalBranchingStructure Θ x)
    {dim : B.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) {k : ℕ}
    (hx : x ∉ supp (X.dimComponent Θ k)) {y : Obj} (hy : y ∈ B.U) :
    X.dimComponent Θ k y = 0 := by
  rw [dimComponent_eq_of_mem h912 hΘ B hdim k hy]
  refine B.dimPart_eq_zero (fun i hi => hx ?_) y
  change 0 < X.dimComponent Θ k x
  rw [dimComponent_eq_self h912 hΘ B hdim k, B.dimPart_self]
  exact Finset.sum_pos' (fun j _ => (B.σ_pos j).le) ⟨i, by simp [hi], B.σ_pos i⟩

theorem orbitSupp_dimComponent_subset (k : ℕ) :
    X.orbitSupp (X.dimComponent Θ k) ⊆ X.orbitSupp Θ :=
  image_mono (supp_dimComponent_subset k)

/-- **`|supp(Θ_k)|` is closed in `|supp(Θ)|`**: near a point `x ∈ supp(Θ) ∖ supp(Θ_k)`,
`Θ_k = 0` on `U(x)`, and `π(U(x))` is open (Proposition 7.1) and misses `|supp(Θ_k)|` (`Θ_k` is
a functor, so `supp(Θ_k)` is saturated). -/
theorem isClosed_orbitSupp_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x)
    (k : ℕ) :
    IsClosed {p : X.orbitSupp Θ | (p : X.OrbitSpace) ∈ X.orbitSupp (X.dimComponent Θ k)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨p, hp⟩ hpk
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC z hz) hz
  have hzk : z ∉ supp (X.dimComponent Θ k) := fun h => hpk ⟨z, h, rfl⟩
  refine ⟨((↑) : X.orbitSupp Θ → X.OrbitSpace) ⁻¹' (X.π '' B.U), fun q hq hqk => ?_,
    (X.proposition_7_1_8 _ B.isOpen_U).preimage continuous_subtype_val, ⟨z, B.mem_U, rfl⟩⟩
  obtain ⟨u, hu, hqu⟩ := hq
  have hu' : u ∈ supp (X.dimComponent Θ k) := by
    rw [← preimage_π_orbitSupp (isFunctorial_dimComponent h912 hΘ k)]
    change X.π u ∈ X.orbitSupp (X.dimComponent Θ k)
    rw [hqu]
    exact hqk
  have h0 := dimComponent_eq_zero_of_not_mem h912 hΘ B hdim hzk hu
  change 0 < X.dimComponent Θ k u at hu'
  rw [h0] at hu'
  exact lt_irrefl _ hu'

/-- **`|supp(Θ_k)|` is paracompact** (Definition 9.1.2 (1)): it is closed in the paracompact
`|supp(Θ)|`. -/
theorem paracompactSpace_orbitSupp_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x)
    (k : ℕ) : ParacompactSpace (X.orbitSupp (X.dimComponent Θ k)) := by
  have := hΘ.paracompactSpace_orbitSupp
  have hsub := orbitSupp_dimComponent_subset (X := X) (Θ := Θ) k
  refine Topology.IsClosedEmbedding.paracompactSpace (e := inclusion hsub)
    ⟨Topology.IsEmbedding.inclusion hsub, ?_⟩
  rw [range_inclusion]
  exact isClosed_orbitSupp_dimComponent h912 hΘ hLC k

open scoped Classical in
/-- **The local branching structure of `Θ_k` at `x`**: the `k`-dimensional sheets
`(Mᵢ)_{i ∈ I_k}` of a labelled structure of `Θ` at `x`, on all of `U(x)`. -/
def dimComponentStructure (h912 : X.Proposition_9_1_12) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {x : Obj} (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (k : ℕ) :
    X.LocalBranchingStructure (X.dimComponent Θ k) x :=
  B.subOn (fun i => dim i = k) B.isOpen_U B.mem_U subset_rfl (X.dimComponent Θ k) fun y hy => by
    rw [dimComponent_eq_of_mem h912 hΘ B hdim k hy]
    unfold LocalBranchingStructure.dimPart
    exact Finset.sum_congr (Finset.filter_congr fun _ _ => Iff.rfl) fun _ _ => rfl

/-- The structure of `Θ_k` is `k`-dimensional. -/
theorem dimComponentStructure_isOfDim (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj} (B : X.LocalBranchingStructure Θ x)
    {dim : B.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (k : ℕ) :
    (dimComponentStructure h912 hΘ B hdim k).IsOfDim k := fun i => by
  obtain ⟨i, hi⟩ := i
  change X.PObj.IsSubmanifoldOfDim (B.M i ∩ B.U) k
  rw [← hi]
  exact (hdim i).inter_isOpen B.isOpen_U

/-- **Each `Θ_k` is a branched ep⁺-subgroupoid** (Proposition 9.1.11 (1)). -/
theorem isBranchedEpSubgroupoid_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x)
    (k : ℕ) : X.IsBranchedEpSubgroupoid (X.dimComponent Θ k) where
  nonneg := dimComponent_nonneg k
  isFunctorial := isFunctorial_dimComponent h912 hΘ k
  support_subset := (supp_dimComponent_subset k).trans hΘ.support_subset
  paracompactSpace_orbitSupp := paracompactSpace_orbitSupp_dimComponent h912 hΘ hLC k
  localBranching x hx := by
    have hx' := supp_dimComponent_subset k hx
    obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC x hx') hx'
    exact ⟨dimComponentStructure h912 hΘ B hdim k⟩

/-- **Each `Θ_k` is `k`-dimensional** (Proposition 9.1.11 (1)). -/
theorem isNDimensional_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x)
    (k : ℕ) : X.IsNDimensional (X.dimComponent Θ k) k := fun x hx => by
  have hx' := supp_dimComponent_subset k hx
  obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC x hx') hx'
  exact ⟨_, dimComponentStructure_isOfDim h912 hΘ B hdim k⟩

/-- On `U(x)` only the dimensions of the sheets of a labelled structure at `x` occur. -/
theorem support_dimComponent_subset (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj} (B : X.LocalBranchingStructure Θ x)
    {dim : B.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) {y : Obj}
    (hy : y ∈ B.U) :
    (Function.support fun k => X.dimComponent Θ k y) ⊆ ↑(Finset.univ.image dim) := by
  intro k hk
  by_contra hkd
  apply hk
  show X.dimComponent Θ k y = 0
  rw [dimComponent_eq_of_mem h912 hΘ B hdim k hy]
  exact B.dimPart_eq_zero (fun i hi => hkd (Finset.mem_coe.2
    (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩))) y

/-- **`(Θ_k)` is a dimensional decomposition of `Θ`** (Proposition 9.1.11 (1), (2)). -/
theorem isDimDecomposition_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x) :
    X.IsDimDecomposition Θ (X.dimComponent Θ) where
  isBranched := isBranchedEpSubgroupoid_dimComponent h912 hΘ hLC
  isNDimensional := isNDimensional_dimComponent h912 hΘ hLC
  finite_support y := by
    by_cases hy : y ∈ supp Θ
    · obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC y hy) hy
      exact (Finset.finite_toSet _).subset (support_dimComponent_subset h912 hΘ B hdim B.mem_U)
    · simp [dimComponent_eq_zero hy]
  eq_finsum y := by
    by_cases hy : y ∈ supp Θ
    · obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC y hy) hy
      rw [finsum_eq_sum_of_support_subset _ (support_dimComponent_subset h912 hΘ B hdim B.mem_U),
        B.eq_sum_dimPart dim B.mem_U]
      exact Finset.sum_congr rfl fun k _ => (dimComponent_eq_of_mem h912 hΘ B hdim k B.mem_U).symm
    · have h0 : Θ y = 0 := le_antisymm (not_lt.1 hy) (hΘ.nonneg y)
      simp [dimComponent_eq_zero hy, h0]

/-- **`(Θ_k)` is a local dimensional decomposition**: near `x ∈ supp(Θ)` it is the
decomposition of a labelled local branching structure at `x`. -/
theorem isLocalDimDecomposition_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x) :
    X.IsLocalDimDecomposition Θ (X.dimComponent Θ) := fun x hx => by
  obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC x hx) hx
  exact ⟨B, dim, hdim, eventually_of_mem (B.isOpen_U.mem_nhds B.mem_U) fun y hy k =>
    dimComponent_eq_of_mem h912 hΘ B hdim k hy⟩

/-- **Local finiteness at the points of `supp(Θ)`**: on `U(x)` only finitely many `Θ_k` are
nonzero. -/
theorem dimComponent_locallyFinite_of_mem (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x)
    {y : Obj} (hy : y ∈ supp Θ) :
    ∃ W ∈ 𝓝 y, {k | ∃ z ∈ W, X.dimComponent Θ k z ≠ 0}.Finite := by
  obtain ⟨B, dim, hdim⟩ := hasLabelledBranchingAt hΘ (hLC y hy) hy
  refine ⟨B.U, B.isOpen_U.mem_nhds B.mem_U, (Finset.finite_toSet (Finset.univ.image dim)).subset ?_⟩
  rintro k ⟨z, hz, hk⟩
  exact support_dimComponent_subset h912 hΘ B hdim hz hk

/-- **Local finiteness everywhere** when the dimensions of the submanifolds of `X` are bounded
by some `N` (in `ℝᵐ`, `N = m`): then `Θ_k = 0` for `k > N`. -/
theorem isLocallyFiniteFamily_dimComponent (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {N : ℕ}
    (hN : ∀ (A : Set Obj) (a : Obj) (n : ℕ), X.PObj.IsSmoothSubmanifold A →
      X.PObj.HasDimAt A a n → n ≤ N) :
    IsLocallyFiniteFamily (X.dimComponent Θ) := fun y => by
  refine ⟨univ, univ_mem, (Set.finite_Iic N).subset ?_⟩
  rintro k ⟨z, -, hk⟩
  by_cases hz : X.HasLabelledBranchingAt Θ z
  · obtain ⟨B, dim, hdim⟩ := hz
    rw [dimComponent_eq_self h912 hΘ B hdim k] at hk
    by_contra hkN
    refine hk (B.dimPart_eq_zero (fun i hi => hkN ?_) z)
    rw [← hi]
    exact hN (B.M i) z (dim i) (hdim i).1 ((hdim i).2 z (B.mem_M i))
  · exact (hk (by rw [dimComponent, dif_neg hz])).elim

/-! ### Proposition 9.1.11, in the reading of its proof -/

variable (X) in
/-- **Proposition 9.1.11 (2021 pp. 407–408; 2017 Proposition 9.2, p. 297), in the reading of its
proof**: every branched ep⁺-subgroupoid `Θ` has exactly one *local* dimensional decomposition
(`IsDimDecomposition` and `IsLocalDimDecomposition`), and it is locally finite.  As stated, with
uniqueness among all dimensional decompositions, it does not hold as we read it
(`not_proposition_9_1_11_rn`). -/
def Proposition_9_1_11_local : Prop :=
  ∀ Θ, X.IsBranchedEpSubgroupoid Θ →
    (∃! Θk, X.IsDimDecomposition Θ Θk ∧ X.IsLocalDimDecomposition Θ Θk) ∧
      ∀ Θk, X.IsDimDecomposition Θ Θk → X.IsLocalDimDecomposition Θ Θk →
        IsLocallyFiniteFamily Θk

/-- **Existence and uniqueness of the local dimensional decomposition**, given Proposition
9.1.12 and the local constancy of the dimension (2021 Remark 9.1.1) on `supp(Θ)`. -/
theorem existsUnique_localDimDecomposition (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x) :
    ∃! Θk, X.IsDimDecomposition Θ Θk ∧ X.IsLocalDimDecomposition Θ Θk :=
  ⟨X.dimComponent Θ, ⟨isDimDecomposition_dimComponent h912 hΘ hLC,
      isLocalDimDecomposition_dimComponent h912 hΘ hLC⟩,
    fun _ h => isDimDecomposition_unique h912 hΘ h.1 (isDimDecomposition_dimComponent h912 hΘ hLC)
      h.2 (isLocalDimDecomposition_dimComponent h912 hΘ hLC)⟩

/-- **Proposition 9.1.11 in the reading of its proof**, for any ep-groupoid, given Proposition
9.1.12, the local constancy of the dimension (Remark 9.1.1) and a bound on the dimensions of
submanifolds (used only for the local finiteness off `supp(Θ)`). -/
theorem proposition_9_1_11_local_of (h912 : X.Proposition_9_1_12)
    (hLC : ∀ x, X.PObj.HasLocallyConstantDimAt x) {N : ℕ}
    (hN : ∀ (A : Set Obj) (a : Obj) (n : ℕ), X.PObj.IsSmoothSubmanifold A →
      X.PObj.HasDimAt A a n → n ≤ N) :
    X.Proposition_9_1_11_local := fun Θ hΘ =>
  ⟨existsUnique_localDimDecomposition h912 hΘ fun x _ => hLC x, fun Θk h hl => by
    rw [isDimDecomposition_unique h912 hΘ h (isDimDecomposition_dimComponent h912 hΘ
      fun x _ => hLC x) hl (isLocalDimDecomposition_dimComponent h912 hΘ fun x _ => hLC x)]
    exact isLocallyFiniteFamily_dimComponent h912 hΘ hN⟩

end EpGroupoid

namespace MPolyfold

variable {m : ℕ}

/-- **In `ℝᵐ` a submanifold has dimension at most `m`**: `T_aA` is the range of `Ds(a)` for a
retraction `s` onto `A` near `a` (`rn_exists_retraction_forall`). -/
theorem rn_hasDimAt_le {A : Set (Fin m → ℝ)} (hA : (rnPolyfold m).IsSmoothSubmanifold A)
    {a : Fin m → ℝ} {n : ℕ} (h : (rnPolyfold m).HasDimAt A a n) : n ≤ m := by
  obtain ⟨W, -, haW, s, -, -, -, -, hT⟩ := rn_exists_retraction_forall hA h.1
  have hfr := finrank_chartTangent (isChart_rnChart 0) h hA (mem_univ a)
    (N := LinearMap.range (fderiv ℝ s a : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))
    (by rw [hT a ⟨haW, h.1⟩]; rfl)
  have hle := LinearMap.finrank_range_le (fderiv ℝ s a : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
  rw [Module.finrank_fin_fun] at hle
  have hn : Module.finrank ℝ
      (LinearMap.range (fderiv ℝ s a : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) = n := hfr
  omega

end MPolyfold

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor} {Θ : (Fin m → ℝ) → ℚ}

/-- **Proposition 9.1.11 over `ℝᵐ`, in the reading of its proof**, with no further hypothesis:
for every ep-groupoid whose object M-polyfold is `ℝᵐ` (any morphisms), every branched
ep⁺-subgroupoid has a unique local dimensional decomposition, and it is locally finite. -/
theorem proposition_9_1_11_local_rn (hX : X.PObj = rnPolyfold m) : X.Proposition_9_1_11_local :=
  proposition_9_1_11_local_of (proposition_9_1_12_rn hX)
    (fun x => hX ▸ MPolyfold.hasLocallyConstantDimAt_rn x) (N := m) fun A a n hA h => by
      rw [hX] at hA h
      exact MPolyfold.rn_hasDimAt_le hA h

/-- **Proposition 9.1.11 for the trivial ep-groupoid of `ℝᵐ`**, in the reading of its proof. -/
theorem proposition_9_1_11_local_trivial_rn :
    (trivial (rnPolyfold m)).Proposition_9_1_11_local :=
  proposition_9_1_11_local_rn rfl

/-- The global decomposition `Θ_k` over `ℝᵐ` is a local dimensional decomposition of `Θ`. -/
theorem isDimDecomposition_dimComponent_rn (hX : X.PObj = rnPolyfold m)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.IsDimDecomposition Θ (X.dimComponent Θ) ∧ X.IsLocalDimDecomposition Θ (X.dimComponent Θ) ∧
      IsLocallyFiniteFamily (X.dimComponent Θ) :=
  have hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x := fun x _ =>
    hX ▸ MPolyfold.hasLocallyConstantDimAt_rn x
  ⟨isDimDecomposition_dimComponent (proposition_9_1_12_rn hX) hΘ hLC,
    isLocalDimDecomposition_dimComponent (proposition_9_1_12_rn hX) hΘ hLC,
    isLocallyFiniteFamily_dimComponent (proposition_9_1_12_rn hX) hΘ (N := m)
      fun A a n hA h => by
        rw [hX] at hA h
        exact MPolyfold.rn_hasDimAt_le hA h⟩

/-- **A witness**: for the indicator of the `x`-axis `L` of `ℝ²` (the example of
`not_proposition_9_1_11_rn`), the constructed decomposition is `Θ_0 = 0`, `Θ_1 = 1_L`
(`decompB`), not `Θ_0 = 1_{0}`, `Θ_1 = 1_{L ∖ 0}`. -/
theorem dimComponent_axis2 :
    (trivial (rnPolyfold 2)).dimComponent (axis2.indicator 1) = decompB := by
  obtain ⟨hD, hL, -⟩ := isDimDecomposition_dimComponent_rn rfl indicator_axis2_branched.1
  exact proposition_9_1_11_unique_rn rfl indicator_axis2_branched.1 hD
    decompB_isDimDecomposition hL decompB_isLocalDimDecomposition

end EpGroupoid

end Polyfold
