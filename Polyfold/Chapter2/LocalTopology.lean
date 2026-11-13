import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter7.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part I, Chapter 2: the local topology of sc-smooth retracts and M-polyfolds added in the 2021
edition.  §2.1: **Proposition 2.1.4** (p. 22), **Definition 2.1.5**, **Remark 2.1.6**,
**Corollary 2.1.7** (p. 23), **Proposition 2.1.8** (p. 24), **Lemma 2.1.9**, **Proposition 2.1.10**
(p. 25); §2.2: **Lemma 2.2.1** (p. 30), **Lemma 2.2.2** (p. 31), **Definition 2.2.3**,
**Theorem 2.2.4** (p. 32), **Definition 2.2.5**, **Proposition 2.2.6** (p. 33); §2.3: the footnote
to **Definition 2.3.4** (p. 35; 2017: Definition 2.8, p. 21), **Lemma 2.3.5** (p. 35),
**Propositions 2.3.6, 2.3.7** (p. 36); Appendix 2.7.2: **Lemma 2.7.2** (p. 72).  All are new in
the 2021 edition except Definition 2.3.4; Remark 2.1.17 (p. 30) only fixes the words "tangent" and
"tangent bundle" of a retract and has no further content.

# Local completeness and local path-connectedness

## The text, paraphrased

(Proposition 2.1.4) Equip an sc-smooth retract `(O, C, E)` with `d_O(x, y) = |x − y|₀`.  Every
`x ∈ O` has open neighbourhoods `W(x)`, `V(x)` with `cl_O(V(x)) ⊆ W(x)` and `d_O` complete on
`cl_O(V(x))`.  *Proof*: with `cl_C(V') ⊆ U` and `r(V') ⊆ V'`, a limit `v ∈ C` of `vₖ ∈ O ∩ V'` lies
in `U`, so `vₖ = r(vₖ) → r(v)` gives `v ∈ O`; hence `cl_O(V) = cl_C(V)` is closed in `E₀`.
(Definition 2.1.5) A Hausdorff space `X` is locally complete if every `x` has open neighbourhoods
`W(x)`, `V(x)` such that (1) `W(x)` carries a metric `d` inducing its topology, (2) `V(x) ⊆ W(x)`,
`cl_X(V(x)) ⊆ W(x)` and `cl_X(V(x))` is `d`-complete.  (Remark 2.1.6) The condition
`cl_X(V) ⊆ W` is a global one; replacing `cl_X(V)` by `cl_W(V)` gives a weaker notion, since
`cl_X(V) ⊆ W` implies `cl_W(V) = cl_X(V)`.  (Corollary 2.1.7) A retract is locally complete.
(Proposition 2.1.8) For a locally complete Hausdorff `X`: (1) locally closed subspaces, (2)
homeomorphic spaces, (3) open subsets are locally complete; and a Hausdorff `Y` with an open cover
`(Yᵢ)` by locally complete subspaces such that (b) every `z ∈ Yᵢ` has an open neighbourhood in
`Yᵢ` whose closure in `Y` lies in `Yᵢ` is locally complete.  (Lemma 2.1.9) Points of a locally
complete space have countable neighbourhood bases.  (Proposition 2.1.10) A Hausdorff locally
complete space is completely regular (a bump function in the complete metric space
`cl_X(V(x))`, extended by `0`, continuity checked with sequences).

(Lemma 2.2.1) If `U ⊆ C` is relatively open and connected, then for every `k ∈ ℕ ∪ {∞}` the level
`U_k = E_k ∩ U` with the `E_k`-topology is path-connected.  *Proof*: `U` is locally
path-connected, hence path-connected; a path in `U₀` is replaced by a polygon through smooth points
in overlapping convex sets `B_ε(σ(tᵢ)) ∩ C`, and points of `U_k` are joined to nearby smooth points.
(Lemma 2.2.2) For a retraction `r : U → U` onto `O`, `x ∈ O` and an open neighbourhood `V(x)` in
`U`, `W(x) = V(x) ∩ r⁻¹(V(x))` is a relatively open neighbourhood of `x` in `C` with
`W(x) ∩ O = V(x) ∩ O`, `r(W(x)) ⊆ W(x)` and `r(W(x)) = O ∩ V(x)`.  (Definition 2.2.3) Locally
path-connected: every open neighbourhood contains a path-connected open neighbourhood.
(Theorem 2.2.4) A retract is locally path-connected (via the component of `W(x)` containing `x`).
(Definition 2.2.5) `Z` is almost locally contractible if every `z` and open `V(z)` admit an open
`W(z) ⊆ V(z)` and a continuous `Φ : [0, 1] × W(z) → V(z)` with `Φ(0, ·) = id`, `Φ(t, z) = z`,
`Φ(1, W(z)) = {z}`.  (Proposition 2.2.6) A retract is almost locally contractible:
`Φ(t, y) = r((1 − t)y + tx)` on `W(x) = B_ε(x) ∩ O`.

(Definition 2.3.4) An M-polyfold is a Hausdorff paracompact* space with an equivalence class of
sc-smooth atlases; the footnote: paracompactness does not include the Hausdorff property, it only
asks that every open covering has a locally finite open covering refining it.  (Lemma 2.3.5) In an
M-polyfold every open `W(x)` contains an arbitrarily small open `V(x)` with `cl_X(V(x)) ⊆ W(x)`
(proof from Hausdorff and paracompact).  (Proposition 2.3.6) An M-polyfold is locally complete,
with `W(x)` arbitrarily small (Proposition 2.1.4 in a chart and Lemma 2.3.5).
(Proposition 2.3.7) An M-polyfold is locally path-connected (corollary of Theorem 2.2.4).
(Appendix 2.7.2, p. 72) Paracompactness means that every open covering has a locally finite
open subcovering; (Lemma 2.7.2) in a regular Hausdorff space every open `U(x)` contains an open
`V(x)` with `V(x) ⊆ cl_X(V(x)) ⊆ U(x)`; it is used for Lemma 2.7.3.

## What is formalized

* `AdmitsCompleteMetricOn T K` (`T` carries a metric defining its topology for which `K` is
  complete), with the transport lemma `AdmitsCompleteMetricOn.of_isEmbedding`.
* `IsLocallyComplete X` (**Definition 2.1.5**); `IsLocallyComplete.exists_subset` (`W(x)` inside
  any neighbourhood), `IsLocallyComplete.regularSpace`, `.t1Space`, `.t2Space` (the Hausdorff
  assumption is automatic).  Witnesses: `isLocallyComplete_of_completeSpace`,
  `isLocallyComplete_real`, `isLocallyComplete_univ_retract`.
* `remark_2_1_6` (the closure identity), `IsLocallyCompleteRel` (the modified definition) and
  `IsLocallyComplete.isLocallyCompleteRel` (**Remark 2.1.6**: it is weaker).
* `ScRetraction.exists_isClosed_retract_inter_closedBall`, `IsScRetract.exists_isComplete_closure`
  (with `W(x)` arbitrarily small), `proposition_2_1_4` (**Proposition 2.1.4**),
  `isLocallyComplete_of_metric`, `corollary_2_1_7` (**Corollary 2.1.7**).
* `IsLocallyComplete.of_isEmbedding`, `proposition_2_1_8_1`, `proposition_2_1_8_2`,
  `proposition_2_1_8_3`, `proposition_2_1_8_4` (**Proposition 2.1.8**, the last part
  being the open-cover statement).
* `lemma_2_1_9` (**Lemma 2.1.9**, `FirstCountableTopology`),
  `IsLocallyComplete.completelyRegularSpace` and `proposition_2_1_10` (**Proposition 2.1.10**,
  `T35Space`).
* `ScBanach.lvlSetInfty E U` (`U_∞` in `∏_m E_m`, with `ScBanach.image_lvlSetInfty`),
  `ScBanach.smoothSeq`,
  `ScBanach.joinedIn_lvlSetInfty_of_segment`, `IsPartialQuadrant.exists_smooth_near` (smooth points
  are dense in `C_m`), `IsRelOpenInQuadrant.exists_ball_inter_subset`, `lemma_2_2_1`
  (**Lemma 2.2.1**, `k ∈ ℕ`) and `lemma_2_2_1_infty` (`k = ∞`).
* `lemma_2_2_2` (**Lemma 2.2.2**); `definition_2_2_3` (**Definition 2.2.3** is Mathlib's
  `LocallyPathConnectedSpace`); `theorem_2_2_4` (**Theorem 2.2.4**).
* `IsAlmostLocallyContractible` (**Definition 2.2.5**), `proposition_2_2_6`
  (**Proposition 2.2.6**), witness `isAlmostLocallyContractible_univ`.
* `IsLocallyFiniteSetFamily`, `IsParacompactStar` (the footnote to **Definition 2.3.4**),
  `isParacompactStar_iff` (it is Mathlib's `ParacompactSpace`), `definition_2_3_4`,
  `isParacompactStar_real`;
  `IsParacompactBySubcover` and `not_isParacompactBySubcover_real`.
* `lemma_2_7_2` (**Lemma 2.7.2**), `exists_isOpen_closure_subset_of_paracompact`,
  `lemma_2_3_5` (**Lemma 2.3.5**); `MChart.isLocallyComplete_source`,
  `MPolyfold.isLocallyComplete`, `proposition_2_3_6` (**Proposition 2.3.6**);
  `proposition_2_3_7` (**Proposition 2.3.7**).

## What the text leaves implicit, and the choices made

* **Definition 2.1.5.**  "`W(x)` admits a metric `d` defining the topology" is a `MetricSpace`
  structure on the subtype `W(x)` whose topology is the subspace topology; "`cl_X(V(x))` is
  complete with respect to `d`" is `IsComplete` of the preimage of `cl_X(V(x))` in `W(x)`.
  `V(x) ⊆ W(x)` follows from `cl_X(V(x)) ⊆ W(x)` and is not a separate field.  The text assumes
  `X` Hausdorff; this is not part of `IsLocallyComplete` because it follows
  (`IsLocallyComplete.t2Space`: `T₁` from the metrizable `W(x)`, regular from the global
  condition `cl_X(V(x)) ⊆ W(x)`).  Accordingly no Hausdorff hypothesis is needed in
  Propositions 2.1.8, 2.1.10 (except for the `T35Space` conclusion) and Lemma 2.1.9.
* **Proposition 2.1.4** is stated for the subtype `O ⊆ E₀` with its subspace metric, which is
  `d_O`; the proof uses `O ∩ B̄_ε(x)` instead of the text's `V'`.  Corollary 2.1.7 restricts `d_O`
  to `W(x)`.
* **Remark 2.1.6**: "weaker" is formalized as the implication; that it is strictly weaker is
  `remark_2_1_6_strict` in `Chapter2/LocalTopologyExample.lean` (ℝ with the K-topology).
* **Proposition 2.1.8 (1)**: "locally closed" is Mathlib's `IsLocallyClosed` (open ∩ closed),
  equivalent to the text's use ("`U ∩ A` closed in `U` for an open `U ∋ a`",
  `isLocallyClosed_tfae`).  The proof goes through the general `IsLocallyComplete.of_isEmbedding`,
  which also gives (2) and (3); the open-cover part is proved by transporting the metric of
  `W ⊆ Yᵢ` to `W ⊆ X`.
* **Lemma 2.1.9 and Proposition 2.1.10** are proved without sequences: the neighbourhood filter
  of `x` is the image of that of the metrizable open `W(x)`, and the bump function is built in the
  metrizable `W(x)` and extended by the constant on `X \ cl_X(V(x))`.  Mathlib's
  `CompletelyRegularSpace` separates by maps to `[0, 1]` with `f(x) = 0`, `f = 1` on the closed
  set (the text's `β` is `1 − f`).
* **Lemma 2.2.1.**  `U_k` is `E.lvlSet U k ⊆ E_k` with the topology of `E_k`.  For `k = ∞`,
  `U_∞` is represented by the compatible sequences `(v_m) ∈ ∏_m E_m` with `v₀ ∈ U`
  (`ScBanach.lvlSetInfty`), i.e. `E_∞` carries the inverse-limit topology of the `E_m` (the topology
  of all the norms `|·|_m`); a path in it is a path continuous into every level.  The proof replaces
  the compactness argument (polygon along a path `σ` in `U₀`) by a clopen argument in the
  connected `U`: the set of points near which every point of `U_∞` is joined to a fixed one is
  open and closed in `U`.  The density of smooth points in `C_m`
  (`IsPartialQuadrant.exists_smooth_near`) is the text's "`U_∞` is dense in every `U_k`".
* **Lemma 2.2.2**: the open neighbourhood `V(x)` of `x` in `U` is `V' ∩ U` with `V'` open in `E₀`.
* **Theorem 2.2.4 and Proposition 2.3.7** were already formalized (Chapter 7 needed them, 2017
  p. 183 recalls them without proof): `IsScRetract.locallyPathConnectedSpace` and
  `MPolyfold.locallyPathConnectedSpace` in `Chapter7/LocConnected.lean`, whose proof joins nearby
  points by `τ ↦ r(o + τ(p − o))` rather than through Lemma 2.2.2 and components.  Definition
  2.2.3 is Mathlib's `LocallyPathConnectedSpace` (`definition_2_2_3`).
* **Definition 2.2.5**: `[0, 1]` is `unitInterval`; `Φ` is a continuous map `I × W(z) → Z` with
  values in `V(z)`; (3) `Φ(1, W(z)) = {z}` is `Φ(1, y) = z` for all `y` (`W(z) ∋ z` is nonempty).
* **Definition 2.3.4.**  The footnote's paracompactness (`IsParacompactStar`, coverings as sets of
  open sets) is equivalent to Mathlib's `ParacompactSpace` (`isParacompactStar_iff`), which does not
  include the Hausdorff property either.  So "Hausdorff paracompact*" is exactly the hypothesis
  `[T2Space X] [ParacompactSpace X]` of `MPolyfold` (`definition_2_3_4`): the footnote changes
  nothing for M-polyfolds, whose Hausdorff property is required separately (it matters for spaces
  not assumed Hausdorff, such as the orbit spaces of later chapters).  The wording of the
  convention in Appendix 2.7.2 (and 2017 Appendix 2.6.2, p. 51), a locally finite open
  *subcovering*, does not hold as we read it for `ℝ` (`not_isParacompactBySubcover_real`); we read
  it as "refinement" (possible misprint), as in the footnote.
* **Lemma 2.3.5** holds in every Hausdorff paracompact space (Mathlib: such spaces are normal);
  "arbitrarily small" is `V(x) ⊆ N` for a given neighbourhood `N`.  **Lemma 2.7.2** only needs
  regularity.
* **Proposition 2.3.6** is derived from the open-cover part of Proposition 2.1.8, with the cover by
  chart domains (`V ≅ O`, Corollary 2.1.7, Proposition 2.1.8 (2)) and condition (b) from
  Lemma 2.3.5; "(3) the topology on level `0`" is the topology of `X`.
* Not formalized here: Lemma 2.7.3 and Proposition 2.7.4 of the appendix (2017 Lemma 2.7,
  Proposition 2.17), which `Metrizable.lean` bypasses; they are formalized in `GapP1_Michael.lean`
  (`lemma_2_7_3`, `proposition_2_7_4`).
-/

open Set Filter Topology TopologicalSpace Function
open scoped unitInterval

noncomputable section

namespace Polyfold

/-! ### Complete metrics on a subspace -/

section CompleteMetric

/-- A closed subset of a complete set is complete. -/
theorem isComplete_inter_of_isClosed {α : Type*} [UniformSpace α] {s t : Set α}
    (hs : IsComplete s) (ht : IsClosed t) : IsComplete (s ∩ t) := by
  intro f hf hfst
  obtain ⟨x, hxs, hx⟩ := hs f hf (hfst.trans (principal_mono.2 inter_subset_left))
  refine ⟨x, ⟨hxs, ht.closure_subset ?_⟩, hx⟩
  have := hf.1
  exact mem_closure_iff_clusterPt.2
    (neBot_of_le (le_inf hx (hfst.trans (principal_mono.2 inter_subset_right))))

/-- `AdmitsCompleteMetricOn T K`: the space `T` admits a metric `d` defining its topology such
that the restriction of `d` to `K ⊆ T` is complete (Definition 2.1.5 (1), (2), with `T = W(x)` and
`K = cl_X(V(x))`). -/
def AdmitsCompleteMetricOn (T : Type*) [t : TopologicalSpace T] (K : Set T) : Prop :=
  ∃ m : MetricSpace T, m.toUniformSpace.toTopologicalSpace = t ∧ @IsComplete T m.toUniformSpace K

/-- A metric space admits its own metric. -/
theorem admitsCompleteMetricOn_of_isComplete {T : Type*} [MetricSpace T] {K : Set T}
    (hK : IsComplete K) : AdmitsCompleteMetricOn T K :=
  ⟨inferInstance, rfl, hK⟩

/-- A space admitting a compatible metric is metrizable. -/
theorem AdmitsCompleteMetricOn.metrizableSpace {T : Type*} [TopologicalSpace T] {K : Set T}
    (h : AdmitsCompleteMetricOn T K) : MetrizableSpace T := by
  obtain ⟨m, rfl, -⟩ := h
  let := m
  infer_instance

/-- **Transport along embeddings**: if `T` admits a metric for which `K` is complete, `j : T' → T`
is an embedding and `j(K') = K ∩ F` with `F` closed, then `T'` admits a metric (the pull-back
`d(j ·, j ·)`) for which `K'` is complete. -/
theorem AdmitsCompleteMetricOn.of_isEmbedding {T T' : Type*} [TopologicalSpace T]
    [t' : TopologicalSpace T'] {K : Set T} (h : AdmitsCompleteMetricOn T K) {j : T' → T}
    (hj : IsEmbedding j) {K' : Set T'} {F : Set T} (hF : IsClosed F) (hK' : j '' K' = K ∩ F) :
    AdmitsCompleteMetricOn T' K' := by
  obtain ⟨m, rfl, hK⟩ := h
  let := m
  let m' : MetricSpace T' := MetricSpace.induced j hj.injective m
  refine ⟨m', ?_, ?_⟩
  · exact hj.eq_induced.symm
  · have hu : @IsUniformInducing T' T m'.toUniformSpace _ j :=
      @isUniformInducing_iff_uniformSpace T' T m'.toUniformSpace _ j |>.2 rfl
    rw [← @IsUniformInducing.isComplete_iff T' T m'.toUniformSpace _ j K' hu, hK']
    exact isComplete_inter_of_isClosed hK hF

/-- A closed subset of a complete set stays complete for the same metric. -/
theorem AdmitsCompleteMetricOn.mono {T : Type*} [TopologicalSpace T] {K K' : Set T}
    (h : AdmitsCompleteMetricOn T K) (hK' : K' ⊆ K) (hc : IsClosed K') :
    AdmitsCompleteMetricOn T K' :=
  h.of_isEmbedding IsEmbedding.id hc (by rw [image_id, inter_eq_right.2 hK'])

end CompleteMetric

/-! ### Locally complete spaces (Definition 2.1.5) -/

section LocallyComplete

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Definition 2.1.5 (2021)**: `X` is **locally complete** if every `x ∈ X` has open
neighbourhoods `W(x)` and `V(x)` such that (1) `W(x)` admits a metric `d` defining the subspace
topology of `W(x)`, and (2) the closure `cl_X(V(x))` of `V(x)` in `X` lies in `W(x)` and is complete
for `d`.  (`V(x) ⊆ W(x)` follows from `cl_X(V(x)) ⊆ W(x)`; the text assumes `X` Hausdorff, which
is a consequence: `IsLocallyComplete.t2Space`.) -/
def IsLocallyComplete (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ W V : Set X, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
    AdmitsCompleteMetricOn W (Subtype.val ⁻¹' closure V)

/-- **`W(x)` can be chosen inside any given neighbourhood `N` of `x`.** -/
theorem IsLocallyComplete.exists_subset (h : IsLocallyComplete X) {x : X} {N : Set X}
    (hN : N ∈ 𝓝 x) : ∃ W V : Set X, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ W ⊆ N ∧ closure V ⊆ W ∧
      AdmitsCompleteMetricOn W (Subtype.val ⁻¹' closure V) := by
  obtain ⟨W₀, V₀, hW₀, hV₀, hxV₀, hclV₀, hm⟩ := h x
  have := hm.metrizableSpace
  have hxW₀ : x ∈ W₀ := hclV₀ (subset_closure hxV₀)
  set N' := interior N ∩ W₀ with hN'
  have hN'o : IsOpen N' := isOpen_interior.inter hW₀
  have hxN' : x ∈ N' := ⟨mem_interior_iff_mem_nhds.2 hN, hxW₀⟩
  -- a closed neighbourhood `B` of `x` in the metrizable `W₀`, inside `N' ∩ V₀`
  have hnhds : (Subtype.val ⁻¹' (N' ∩ V₀) : Set W₀) ∈ 𝓝 (⟨x, hxW₀⟩ : W₀) :=
    ((hN'o.inter hV₀).preimage continuous_subtype_val).mem_nhds ⟨hxN', hxV₀⟩
  obtain ⟨B, hB, hBc, hBsub⟩ := exists_mem_nhds_isClosed_subset hnhds
  set V : Set X := Subtype.val '' interior B with hV
  have hVo : IsOpen V := hW₀.isOpenMap_subtype_val _ isOpen_interior
  have hxV : x ∈ V := ⟨⟨x, hxW₀⟩, mem_interior_iff_mem_nhds.2 hB, rfl⟩
  have hVV₀ : V ⊆ V₀ := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hBsub (interior_subset hw)).2
  have hclV : closure V ⊆ N' := by
    intro z hz
    have hzW₀ : z ∈ W₀ := hclV₀ (closure_mono hVV₀ hz)
    have : (⟨z, hzW₀⟩ : W₀) ∈ closure (interior B) := closure_subtype.2 hz
    exact (hBsub (hBc.closure_subset (closure_mono interior_subset this))).1
  refine ⟨N', V, hN'o, hVo, hxV, fun y hy => interior_subset hy.1, hclV, ?_⟩
  refine hm.of_isEmbedding (IsEmbedding.inclusion inter_subset_right)
    (F := Subtype.val ⁻¹' closure V) (isClosed_closure.preimage continuous_subtype_val) ?_
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨closure_mono hVV₀ hw', hw'⟩
  · rintro ⟨-, hw⟩
    exact ⟨⟨w, hclV hw⟩, hw, rfl⟩

/-- A locally complete space is regular (closed neighbourhoods form a basis). -/
theorem IsLocallyComplete.regularSpace (h : IsLocallyComplete X) : RegularSpace X :=
  RegularSpace.of_exists_mem_nhds_isClosed_subset fun _ _ hN => by
    obtain ⟨W, V, -, hV, hxV, hWN, hVW, -⟩ := h.exists_subset hN
    exact ⟨closure V, mem_of_superset (hV.mem_nhds hxV) subset_closure, isClosed_closure,
      hVW.trans hWN⟩

/-- A locally complete space is `T₁`. -/
theorem IsLocallyComplete.t1Space (h : IsLocallyComplete X) : T1Space X := by
  refine t1Space_iff_exists_open.2 fun x y hxy => ?_
  obtain ⟨W, V, hW, -, hxV, hVW, hm⟩ := h x
  have hxW : x ∈ W := hVW (subset_closure hxV)
  by_cases hyW : y ∈ W
  · have := hm.metrizableSpace
    obtain ⟨U, hU, hxU, hyU⟩ := t1Space_iff_exists_open.1 (inferInstance : T1Space W)
      (fun h' => hxy (congrArg Subtype.val h' : _) : (⟨x, hxW⟩ : W) ≠ ⟨y, hyW⟩)
    exact ⟨Subtype.val '' U, hW.isOpenMap_subtype_val _ hU, ⟨_, hxU, rfl⟩, by
      rintro ⟨w, hw, hwy⟩
      exact hyU (by rwa [show (⟨y, hyW⟩ : W) = w from Subtype.ext hwy.symm])⟩
  · exact ⟨W, hW, hxW, hyW⟩

/-- **The Hausdorff assumption of Definition 2.1.5 is automatic**: a locally complete space is
Hausdorff (it is `T₁` and regular). -/
theorem IsLocallyComplete.t2Space (h : IsLocallyComplete X) : T2Space X := by
  have := h.t1Space
  have := h.regularSpace
  infer_instance

/-- A complete metric space is locally complete (`W = V = X`). -/
theorem isLocallyComplete_of_completeSpace (M : Type*) [MetricSpace M] [CompleteSpace M] :
    IsLocallyComplete M := fun _ =>
  ⟨univ, univ, isOpen_univ, isOpen_univ, mem_univ _, subset_univ _,
    (admitsCompleteMetricOn_of_isComplete isComplete_univ).of_isEmbedding IsEmbedding.subtypeVal
      isClosed_univ (by simp)⟩

/-- **Non-vacuity of Definition 2.1.5**: `ℝ` is locally complete. -/
theorem isLocallyComplete_real : IsLocallyComplete ℝ := isLocallyComplete_of_completeSpace ℝ

/-- In a metric space, if every point has open `V ⊆ W` with `cl(V) ⊆ W` and `cl(V)` complete for
the given metric, the space is locally complete (the restricted metric on `W`). -/
theorem isLocallyComplete_of_metric {M : Type*} [MetricSpace M]
    (h : ∀ x : M, ∃ W V : Set M, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      IsComplete (closure V)) : IsLocallyComplete M := fun x => by
  obtain ⟨W, V, hW, hV, hxV, hVW, hc⟩ := h x
  refine ⟨W, V, hW, hV, hxV, hVW, ?_⟩
  refine (admitsCompleteMetricOn_of_isComplete hc).of_isEmbedding IsEmbedding.subtypeVal
    isClosed_univ ?_
  rw [Subtype.image_preimage_coe, inter_eq_right.2 hVW, inter_univ]

end LocallyComplete

/-! ### Remark 2.1.6, Lemma 2.1.9, Proposition 2.1.10 -/

section LocallyCompleteProps

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Remark 2.1.6 (2021)**, the identity: if `cl_X(V) ⊆ W`, the closure of `V` in `W` is
`cl_X(V)`. -/
theorem remark_2_1_6 {W V : Set X} (h : closure V ⊆ W) :
    Subtype.val '' closure (Subtype.val ⁻¹' V : Set W) = closure V := by
  have hVW : V ⊆ W := subset_closure.trans h
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have := closure_subtype.1 hw
    rwa [Subtype.image_preimage_coe, inter_eq_right.2 hVW] at this
  · intro hz
    refine ⟨⟨z, h hz⟩, closure_subtype.2 ?_, rfl⟩
    rwa [Subtype.image_preimage_coe, inter_eq_right.2 hVW]

/-- The **modified definition of Remark 2.1.6**: `cl_X(V(x))` replaced by the closure
`cl_{W(x)}(V(x))` of `V(x)` in `W(x)`. -/
def IsLocallyCompleteRel (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ W V : Set X, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
    AdmitsCompleteMetricOn W (closure (Subtype.val ⁻¹' V : Set W))

/-- **Remark 2.1.6 (2021)**: the modified definition is weaker. -/
theorem IsLocallyComplete.isLocallyCompleteRel (h : IsLocallyComplete X) :
    IsLocallyCompleteRel X := fun x => by
  obtain ⟨W, V, hW, hV, hxV, hVW, hm⟩ := h x
  refine ⟨W, V, hW, hV, hxV, subset_closure.trans hVW, ?_⟩
  have : closure (Subtype.val ⁻¹' V : Set W) = Subtype.val ⁻¹' closure V := by
    rw [← remark_2_1_6 hVW, preimage_image_eq _ Subtype.val_injective]
  rwa [this]

/-- **Lemma 2.1.9 (2021)**: every point of a locally complete space has a countable neighbourhood
basis. -/
theorem lemma_2_1_9 (h : IsLocallyComplete X) : FirstCountableTopology X := by
  refine ⟨fun x => ?_⟩
  obtain ⟨W, V, hW, -, hxV, hVW, hm⟩ := h x
  have := hm.metrizableSpace
  rw [← hW.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hVW (subset_closure hxV)⟩]
  infer_instance

/-- A locally complete space is completely regular (the proof of Proposition 2.1.10; the Hausdorff
property is not used). -/
theorem IsLocallyComplete.completelyRegularSpace (h : IsLocallyComplete X) :
    CompletelyRegularSpace X := by
  refine ⟨fun x K hK hxK => ?_⟩
  obtain ⟨W, V, hW, hV, hxV, hVW, hm⟩ := h x
  have := hm.metrizableSpace
  have hxW : x ∈ W := hVW (subset_closure hxV)
  -- in the metrizable `W`, separate `x` from the complement of `V \ K`
  have hopen : IsOpen (Subtype.val ⁻¹' (V ∩ Kᶜ) : Set W) :=
    (hV.inter hK.isOpen_compl).preimage continuous_subtype_val
  obtain ⟨f, hfc, hfx, hf1⟩ :=
    CompletelyRegularSpace.completely_regular_isOpen (⟨x, hxW⟩ : W) _ hopen ⟨hxV, hxK⟩
  classical
  -- extend by `1` outside `W`
  let g : X → I := fun y => if hy : y ∈ W then f ⟨y, hy⟩ else 1
  have hg1 : ∀ y, y ∉ V ∩ Kᶜ → g y = 1 := by
    intro y hy
    by_cases hyW : y ∈ W
    · simp only [g, dif_pos hyW]
      exact hf1 (show (⟨y, hyW⟩ : W) ∉ Subtype.val ⁻¹' (V ∩ Kᶜ) from hy)
    · simp only [g, dif_neg hyW]
  refine ⟨g, ?_, by simp [g, hxW, hfx], fun y hy => hg1 y fun h' => h'.2 hy⟩
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hyW : y ∈ W
  · have hcont : ContinuousOn g W := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hfc using 1
      funext w
      simp [g, w.2]
    exact hcont.continuousAt (hW.mem_nhds hyW)
  · have hy : y ∉ closure V := fun h' => hyW (hVW h')
    refine (continuousAt_const : ContinuousAt (fun _ : X => (1 : I)) y).congr ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
    exact (hg1 z fun h' => hz (subset_closure h'.1)).symm

/-- **Proposition 2.1.10 (2021)**: a Hausdorff locally complete space is completely regular
(Tychonoff). -/
theorem proposition_2_1_10 [T2Space X] (h : IsLocallyComplete X) : T35Space X :=
  @T35Space.mk X _ inferInstance h.completelyRegularSpace

/-! ### Proposition 2.1.8 -/

/-- **Local completeness passes to embedded subspaces with locally closed image**: if
`f : Y → X` is an embedding and `f(Y)` is locally closed in the locally complete `X`, then `Y` is
locally complete.  This is the proof of Proposition 2.1.8 (1). -/
theorem IsLocallyComplete.of_isEmbedding (h : IsLocallyComplete X) {f : Y → X}
    (hf : IsEmbedding f) (hr : IsLocallyClosed (range f)) : IsLocallyComplete Y := by
  intro y
  obtain ⟨U, Z, hU, hZ, hUZ⟩ := hr
  have hfyU : f y ∈ U := (hUZ ▸ mem_range_self y : f y ∈ U ∩ Z).1
  obtain ⟨W, V, hW, hV, hxV, hWU, hVW, hm⟩ := h.exists_subset (hU.mem_nhds hfyU)
  refine ⟨f ⁻¹' W, f ⁻¹' V, hW.preimage hf.continuous, hV.preimage hf.continuous, hxV,
    (hf.continuous.closure_preimage_subset V).trans (preimage_mono hVW), ?_⟩
  have hcl : ∀ y' : Y, y' ∈ closure (f ⁻¹' V) ↔ f y' ∈ closure (f '' (f ⁻¹' V)) := fun y' => by
    rw [hf.isInducing.closure_eq_preimage_closure_image (f ⁻¹' V), mem_preimage]
  refine hm.of_isEmbedding (hf.restrictPreimage W)
    (F := Subtype.val ⁻¹' (closure (f '' (f ⁻¹' V)) ∩ Z))
    ((isClosed_closure.inter hZ).preimage continuous_subtype_val) ?_
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    have h1 : f w' ∈ closure (f '' (f ⁻¹' V)) := (hcl w').1 hw'
    have h2 : f w' ∈ U ∩ Z := hUZ ▸ mem_range_self _
    exact ⟨closure_mono (image_preimage_subset f V) h1, h1, h2.2⟩
  · rintro ⟨-, h1, hZw⟩
    have : (w : X) ∈ range f := by rw [hUZ]; exact ⟨hWU w.2, hZw⟩
    obtain ⟨y', hy'⟩ := this
    have hy'W : y' ∈ f ⁻¹' W := by rw [mem_preimage, hy']; exact w.2
    refine ⟨⟨y', hy'W⟩, (hcl y').2 (by rw [hy']; exact h1), Subtype.ext hy'⟩

/-- **Proposition 2.1.8 (1) (2021)**: a locally closed subspace of a locally complete space is
locally complete. -/
theorem proposition_2_1_8_1 (h : IsLocallyComplete X) {A : Set X}
    (hA : IsLocallyClosed A) : IsLocallyComplete A :=
  h.of_isEmbedding IsEmbedding.subtypeVal (by rwa [Subtype.range_coe])

/-- **Proposition 2.1.8 (2) (2021)**: a space homeomorphic to a locally complete space is locally
complete. -/
theorem proposition_2_1_8_2 (h : IsLocallyComplete X) (e : X ≃ₜ Y) : IsLocallyComplete Y :=
  h.of_isEmbedding e.symm.isEmbedding (by
    rw [e.symm.range_coe]; exact isClosed_univ.isLocallyClosed)

/-- **Proposition 2.1.8 (3) (2021)**: an open subset of a locally complete space is locally
complete. -/
theorem proposition_2_1_8_3 (h : IsLocallyComplete X) {A : Set X} (hA : IsOpen A) :
    IsLocallyComplete A :=
  proposition_2_1_8_1 h hA.isLocallyClosed

/-- **Proposition 2.1.8, last part (2021)**: if `X` has an open covering `(Yᵢ)` such that (a) every
`Yᵢ` is locally complete, and (b) every `z ∈ Yᵢ` has an open neighbourhood in `Yᵢ` whose closure in
`X` lies in `Yᵢ`, then `X` is locally complete.  (The Hausdorff property of `X` is not used.) -/
theorem proposition_2_1_8_4 {ι : Type*} (Yᵢ : ι → Set X) (hYo : ∀ i, IsOpen (Yᵢ i))
    (hcov : ∀ y, ∃ i, y ∈ Yᵢ i) (ha : ∀ i, IsLocallyComplete (Yᵢ i))
    (hb : ∀ i, ∀ z ∈ Yᵢ i, ∃ U, IsOpen U ∧ z ∈ U ∧ U ⊆ Yᵢ i ∧ closure U ⊆ Yᵢ i) :
    IsLocallyComplete X := by
  intro y
  obtain ⟨i, hyi⟩ := hcov y
  obtain ⟨U, hUo, hyU, -, hclU⟩ := hb i y hyi
  obtain ⟨W', V', hW', hV', hyV', hV'W', hm⟩ := ha i ⟨y, hyi⟩
  set V'' : Set (Yᵢ i) := V' ∩ Subtype.val ⁻¹' U with hV''
  set W : Set X := Subtype.val '' W' with hW
  set V : Set X := Subtype.val '' V'' with hV
  have hWo : IsOpen W := (hYo i).isOpenMap_subtype_val _ hW'
  have hVo : IsOpen V :=
    (hYo i).isOpenMap_subtype_val _ (hV'.inter (hUo.preimage continuous_subtype_val))
  have hyV : y ∈ V := ⟨⟨y, hyi⟩, ⟨hyV', hyU⟩, rfl⟩
  have hVU : V ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  -- `cl_X(V) ⊆ Yᵢ`, where it is the closure of `V''` in `Yᵢ`
  have hclVY : closure V ⊆ Yᵢ i := (closure_mono hVU).trans hclU
  have hcl : ∀ z : Yᵢ i, z ∈ closure V'' ↔ (z : X) ∈ closure V := fun z => closure_subtype
  have hclVW : closure V ⊆ W := by
    intro z hz
    have hz' : (⟨z, hclVY hz⟩ : Yᵢ i) ∈ closure V'' := (hcl _).2 hz
    exact ⟨_, hV'W' (closure_mono inter_subset_left hz'), rfl⟩
  refine ⟨W, V, hWo, hVo, hyV, hclVW, ?_⟩
  -- transport the metric of `W' ⊆ Yᵢ` to `W ⊆ X`
  have hWY : W ⊆ Yᵢ i := Subtype.coe_image_subset _ _
  have hmemW' : ∀ w : W, (⟨w, hWY w.2⟩ : Yᵢ i) ∈ W' := fun w => by
    obtain ⟨z, hz, hzw⟩ := w.2
    have : z = ⟨w, hWY w.2⟩ := Subtype.ext hzw
    rwa [← this]
  let j : W → W' := fun w => ⟨⟨w, hWY w.2⟩, hmemW' w⟩
  have hjc : Continuous j := (continuous_subtype_val.subtype_mk _).subtype_mk _
  have hjind : IsInducing (Subtype.val ∘ Subtype.val ∘ j) := IsInducing.subtypeVal
  have hj : IsEmbedding j :=
    ⟨IsInducing.of_comp hjc (continuous_subtype_val.comp continuous_subtype_val) hjind,
      fun a b hab => Subtype.ext (congrArg (fun w : W' => ((w : Yᵢ i) : X)) hab)⟩
  refine hm.of_isEmbedding hj (F := Subtype.val ⁻¹' closure V'')
    (isClosed_closure.preimage continuous_subtype_val) ?_
  ext w'
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : (⟨w, hWY w.2⟩ : Yᵢ i) ∈ closure V'' := (hcl _).2 hw
    exact ⟨closure_mono inter_subset_left h1, h1⟩
  · rintro ⟨-, h1⟩
    refine ⟨⟨(w' : Yᵢ i), ⟨w', w'.2, rfl⟩⟩, (hcl _).1 h1, rfl⟩

end LocallyCompleteProps

/-! ### Sc-smooth retracts: Proposition 2.1.4 and Corollary 2.1.7 -/

section Retracts

variable {E : ScBanach} {C : Set (E 0)}

/-- Near a point `x` of `O = r(U)` the sets `O ∩ B̄_ε(x)`, `ε` small, are closed in `E₀` (the
core of the proof of Proposition 2.1.4: a limit `v` of points `vₖ = r(vₖ)` of `O` near `x` lies
in `C`, hence in `U`, and `r(v) = v`). -/
theorem ScRetraction.exists_isClosed_retract_inter_closedBall (R : ScRetraction E C) {x : E 0}
    (hx : x ∈ R.retract) :
    ∃ δ > 0, ∀ ε ≤ δ, IsClosed (R.retract ∩ Metric.closedBall x ε) := by
  obtain ⟨O', hO'o, hUO'⟩ := R.relOpen.relOpen
  have hxO' : x ∈ O' := by
    have := R.retract_subset hx
    rw [hUO'] at this
    exact this.1
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hO'o x hxO'
  refine ⟨δ₀ / 2, half_pos hδ₀, fun ε hε => ?_⟩
  have hKU : C ∩ Metric.closedBall x ε ⊆ R.U := by
    intro z hz
    rw [hUO']
    exact ⟨hball (Metric.closedBall_subset_ball (by linarith) hz.2), hz.1⟩
  have hKc : IsClosed (C ∩ Metric.closedBall x ε) :=
    R.relOpen.isPartialQuadrant.isClosed.inter Metric.isClosed_closedBall
  have hcont : ContinuousOn (fun z => (R z, z)) (C ∩ Metric.closedBall x ε) :=
    ((R.isSc1.isSc0.continuousOn_base).mono hKU).prodMk continuousOn_id
  have := hcont.preimage_isClosed_of_isClosed hKc isClosed_diagonal
  convert this using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_diagonal_iff, R.mem_retract_iff]
  constructor
  · rintro ⟨⟨hzU, hRz⟩, hzB⟩
    refine ⟨⟨?_, hzB⟩, hRz⟩
    rw [hUO'] at hzU
    exact hzU.2
  · rintro ⟨hzK, hRz⟩
    exact ⟨⟨hKU hzK, hRz⟩, hzK.2⟩

/-- **Proposition 2.1.4 (2021)**, with `W(x)` arbitrarily small: in an sc-smooth retract
`(O, C, E)`, with the metric `d_O(x, y) = |x − y|₀`, every `x ∈ O` and every neighbourhood `N` of
`x` admit open `V ⊆ W ⊆ N` with `cl_O(V) ⊆ W` and `cl_O(V)` complete for `d_O`. -/
theorem IsScRetract.exists_isComplete_closure {O : Set (E 0)} (hO : IsScRetract E C O) (x : O)
    {N : Set O} (hN : N ∈ 𝓝 x) : ∃ W V : Set O, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ W ⊆ N ∧
      closure V ⊆ W ∧ IsComplete (closure V) := by
  obtain ⟨R, rfl⟩ := hO
  obtain ⟨δ, hδ, hcl⟩ := R.exists_isClosed_retract_inter_closedBall x.2
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.1 hN
  set ε := min δ ρ / 2 with hε
  have hm : 0 < min δ ρ := lt_min hδ hρ
  have hε0 : 0 < ε := half_pos hm
  have hεδ : ε ≤ δ := by have := min_le_left δ ρ; linarith
  have hερ : 2 * ε ≤ ρ := by have := min_le_right δ ρ; linarith
  refine ⟨Metric.ball x (2 * ε), Metric.ball x ε, Metric.isOpen_ball, Metric.isOpen_ball,
    Metric.mem_ball_self hε0, (Metric.ball_subset_ball hερ).trans hρN,
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith)), ?_⟩
  -- `B̄_ε(x) ⊆ O` is complete: its image `O ∩ B̄_ε(x)` is closed in the Banach space `E₀`
  have hB : IsComplete (Metric.closedBall x ε) := by
    rw [← isUniformEmbedding_subtype_val.isUniformInducing.isComplete_iff]
    have : Subtype.val '' Metric.closedBall x ε =
        R.retract ∩ Metric.closedBall (x : E 0) ε := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw⟩
      · rintro ⟨hz, hzb⟩
        exact ⟨⟨z, hz⟩, hzb, rfl⟩
    rw [this]
    exact (hcl ε hεδ).isComplete
  have := isComplete_inter_of_isClosed hB (isClosed_closure (s := Metric.ball x ε))
  rwa [inter_eq_right.2 Metric.closure_ball_subset_closedBall] at this

/-- **Proposition 2.1.4 (2021)**: for an sc-smooth retract `(O, C, E)`, every `x ∈ O` has open
neighbourhoods `V(x)`, `W(x)` in `O` with `cl_O(V(x)) ⊆ W(x)` such that the restriction of
`d_O(x, y) = |x − y|₀` to `cl_O(V(x))` is complete. -/
theorem proposition_2_1_4 {O : Set (E 0)} (hO : IsScRetract E C O) (x : O) :
    ∃ W V : Set O, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧ IsComplete (closure V) := by
  obtain ⟨W, V, hW, hV, hxV, -, hVW, hc⟩ := hO.exists_isComplete_closure x univ_mem
  exact ⟨W, V, hW, hV, hxV, hVW, hc⟩

/-- **Corollary 2.1.7 (2021)**: an sc-smooth retract `(O, C, E)` (level-`0` topology) is locally
complete. -/
theorem corollary_2_1_7 {O : Set (E 0)} (hO : IsScRetract E C O) : IsLocallyComplete O :=
  isLocallyComplete_of_metric (proposition_2_1_4 hO)

/-- **Non-vacuity**: the retract `(E₀, E, E)` (the whole sc-Banach space, `r = id`) is locally
complete, by Corollary 2.1.7. -/
theorem isLocallyComplete_univ_retract (E : ScBanach) : IsLocallyComplete (univ : Set (E 0)) :=
  corollary_2_1_7 (C := univ)
    (⟨isPartialQuadrant_univ E, univ, isOpen_univ, (univ_inter _).symm⟩ :
      IsRelOpenInQuadrant E univ univ).isScRetract

end Retracts

/-! ### Paracompactness in Definition 2.3.4, Lemma 2.7.2 -/

section Paracompact

universe v

variable {X : Type v} [TopologicalSpace X]

/-- A family `𝒱` of subsets of `X` (a set of sets) is **locally finite**: every point has a
neighbourhood meeting only finitely many members of `𝒱`. -/
def IsLocallyFiniteSetFamily (𝒱 : Set (Set X)) : Prop :=
  ∀ x : X, ∃ N ∈ 𝓝 x, {V ∈ 𝒱 | (V ∩ N).Nonempty}.Finite

/-- **Paracompactness in the sense of the footnote to Definition 2.3.4 (2021)** ("paracompact*"):
every open covering admits a locally finite open covering refining it; no separation axiom is
included. -/
def IsParacompactStar (X : Type v) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = univ →
    ∃ 𝒱 : Set (Set X), (∀ V ∈ 𝒱, IsOpen V) ∧ ⋃₀ 𝒱 = univ ∧ IsLocallyFiniteSetFamily 𝒱 ∧
      ∀ V ∈ 𝒱, ∃ U ∈ 𝒰, V ⊆ U

/-- **The footnote's paracompactness is Mathlib's `ParacompactSpace`**, the notion used by
`MPolyfold` (which, like the footnote, does not include the Hausdorff property). -/
theorem isParacompactStar_iff : IsParacompactStar X ↔ ParacompactSpace X := by
  constructor
  · intro h
    refine ⟨fun α s hso hcov => ?_⟩
    obtain ⟨𝒱, hVo, hVcov, hVlf, hVref⟩ :=
      h (range s) (forall_mem_range.2 hso) (by rwa [sUnion_range])
    refine ⟨𝒱, Subtype.val, fun V => hVo V V.2, by rwa [← sUnion_eq_iUnion], fun x => ?_,
      fun V => ?_⟩
    · obtain ⟨N, hN, hfin⟩ := hVlf x
      refine ⟨N, hN, ?_⟩
      have := hfin.preimage ((Subtype.val_injective (p := (· ∈ 𝒱))).injOn
        (s := Subtype.val ⁻¹' {V | V ∈ 𝒱 ∧ (V ∩ N).Nonempty}))
      convert this using 1
      ext b
      simp
    · obtain ⟨U, ⟨a, rfl⟩, hVU⟩ := hVref V V.2
      exact ⟨a, hVU⟩
  · intro h 𝒰 hUo hcov
    obtain ⟨β, t, hto, htcov, htlf, htref⟩ := ParacompactSpace.locallyFinite_refinement 𝒰
      Subtype.val (fun U => hUo U U.2) (by rwa [← sUnion_eq_iUnion])
    refine ⟨range t, forall_mem_range.2 hto, by rwa [sUnion_range], fun x => ?_,
      forall_mem_range.2 fun b => ?_⟩
    · obtain ⟨N, hN, hfin⟩ := htlf x
      refine ⟨N, hN, (hfin.image t).subset ?_⟩
      rintro _ ⟨⟨b, rfl⟩, hb⟩
      exact ⟨b, hb, rfl⟩
    · obtain ⟨a, ha⟩ := htref b
      exact ⟨a, a.2, ha⟩

/-- **Definition 2.3.4 (2021)**: "Hausdorff paracompact*" is exactly the hypothesis
`[T2Space X] [ParacompactSpace X]` of `MPolyfold` (2017 Definition 2.8, "Hausdorff
paracompact"): the footnote changes nothing for M-polyfolds. -/
theorem definition_2_3_4 :
    (T2Space X ∧ IsParacompactStar X) ↔ (T2Space X ∧ ParacompactSpace X) := by
  rw [isParacompactStar_iff]

/-- **Non-vacuity**: `ℝ` is paracompact* (metric spaces are paracompact). -/
theorem isParacompactStar_real : IsParacompactStar ℝ :=
  isParacompactStar_iff.2 inferInstance

/-- The reading "every open covering has a locally finite open **sub**covering" (the wording of
the convention in Appendix 2.7.2, p. 72; 2017 Appendix 2.6.2: "locally finite subcovering"). -/
def IsParacompactBySubcover (X : Type v) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = univ →
    ∃ 𝒱 ⊆ 𝒰, ⋃₀ 𝒱 = univ ∧ IsLocallyFiniteSetFamily 𝒱

/-- **The subcovering reading does not hold for `ℝ`** (possible misprint for "refinement", which
is the footnote's wording): the covering of `ℝ` by the intervals `(−n−1, n+1)` has no locally
finite subcovering, although `ℝ` is paracompact. -/
theorem not_isParacompactBySubcover_real : ¬ IsParacompactBySubcover ℝ := by
  intro h
  obtain ⟨𝒱, hsub, hcov, hlf⟩ := h (range fun n : ℕ => Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))
    (forall_mem_range.2 fun _ => isOpen_Ioo) (by
      refine eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      refine ⟨_, ⟨n, rfl⟩, ?_⟩
      constructor
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x])
  obtain ⟨N, hN, hfin⟩ := hlf 0
  -- every member contains `0 ∈ N`, so `𝒱` is finite
  have h𝒱 : 𝒱.Finite := hfin.subset fun V hV => ⟨hV, by
    obtain ⟨n, rfl⟩ := hsub hV
    have := Nat.cast_nonneg (α := ℝ) n
    exact ⟨0, ⟨by linarith, by linarith⟩, mem_of_mem_nhds hN⟩⟩
  have hbdd : Bornology.IsBounded (⋃₀ 𝒱) := (Bornology.isBounded_sUnion h𝒱).2 fun V hV => by
    obtain ⟨n, rfl⟩ := hsub hV
    exact Metric.isBounded_Ioo _ _
  rw [hcov] at hbdd
  exact NormedSpace.unbounded_univ ℝ ℝ hbdd

/-- **Lemma 2.7.2 (2021)**: in a regular space, every open neighbourhood `U(x)` contains an open
`V(x)` with `V(x) ⊆ cl_X(V(x)) ⊆ U(x)` (the Hausdorff property is not used). -/
theorem lemma_2_7_2 [RegularSpace X] {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ closure V ∧ closure V ⊆ U := by
  obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hx)
  exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, subset_closure,
    (closure_minimal interior_subset htc).trans htU⟩

/-- The proof of Lemma 2.3.5: in a Hausdorff paracompact space, every open `W ∋ x` contains an
open `V ∋ x`, inside any given neighbourhood `N` of `x`, with `cl_X(V) ⊆ W`.  (Mathlib:
paracompact Hausdorff spaces are normal, Dieudonné.) -/
theorem exists_isOpen_closure_subset_of_paracompact [T2Space X] [ParacompactSpace X] {x : X}
    {W N : Set X} (hW : IsOpen W) (hx : x ∈ W) (hN : N ∈ 𝓝 x) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ closure V ⊆ W := by
  obtain ⟨V, hVo, hxV, -, hVW⟩ := lemma_2_7_2 (hW.inter isOpen_interior)
    ⟨hx, mem_interior_iff_mem_nhds.2 hN⟩
  exact ⟨V, hVo, hxV, fun y hy => interior_subset (hVW (subset_closure hy)).2,
    hVW.trans inter_subset_left⟩

end Paracompact

/-! ### M-polyfolds: Lemma 2.3.5, Propositions 2.3.6, 2.3.7 -/

/-- A chart domain `V` of an M-polyfold is locally complete (`V ≅ O` and Corollary 2.1.7,
Proposition 2.1.8 (2)). -/
theorem MChart.isLocallyComplete_source {X : Type*} [TopologicalSpace X] (φ : MChart X) :
    IsLocallyComplete φ.source :=
  proposition_2_1_8_2 (corollary_2_1_7 φ.model.isScRetract) φ.sourceHomeomorph.symm

section MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

include P

set_option linter.unusedSectionVars false in
/-- **Lemma 2.3.5 (2021)**: for an M-polyfold `X`, `x ∈ X` and an open neighbourhood `W(x)`, there
is an open neighbourhood `V(x)` with `cl_X(V(x)) ⊆ W(x)`, which can be chosen inside any given
neighbourhood `N` of `x` ("arbitrarily small"). -/
theorem lemma_2_3_5 {x : X} {W N : Set X} (hW : IsOpen W) (hx : x ∈ W) (hN : N ∈ 𝓝 x) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ closure V ⊆ W :=
  exists_isOpen_closure_subset_of_paracompact hW hx hN

/-- An M-polyfold is locally complete (Definition 2.1.5). -/
theorem MPolyfold.isLocallyComplete : IsLocallyComplete X := by
  refine proposition_2_1_8_4 (ι := {φ : MChart X // P.IsChart φ}) (fun φ => φ.1.source)
    (fun φ => φ.1.isOpen_source) (fun y => ?_) (fun φ => φ.1.isLocallyComplete_source)
    (fun φ z hz => ?_)
  · obtain ⟨φ, hφ, hy⟩ := P.exists_isChart_mem_source y
    exact ⟨⟨φ, hφ⟩, hy⟩
  · obtain ⟨V, hVo, hzV, -, hVW⟩ :=
      exists_isOpen_closure_subset_of_paracompact φ.1.isOpen_source hz univ_mem
    exact ⟨V, hVo, hzV, subset_closure.trans hVW, hVW⟩

/-- **Proposition 2.3.6 (2021)**: an M-polyfold `X` is locally complete; namely every `x ∈ X` has
open neighbourhoods `V(x) ⊆ W(x)` with (1) `W(x)` inside any given neighbourhood `N` of `x`,
(2) `cl_X(V(x)) ⊆ W(x)`, (3) `W(x)` admits a metric `d` defining its (level-`0`) topology whose
restriction to `cl_X(V(x))` is complete. -/
theorem proposition_2_3_6 {x : X} {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ W V : Set X, IsOpen W ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ W ⊆ N ∧ closure V ⊆ W ∧
      AdmitsCompleteMetricOn W (Subtype.val ⁻¹' closure V) := by
  obtain ⟨W, V, hW, hV, hxV, hWN, hVW, hm⟩ := P.isLocallyComplete.exists_subset hN
  exact ⟨W, V, hW, hV, hxV, subset_closure.trans hVW, hWN, hVW, hm⟩

/-- **Proposition 2.3.7 (2021)**: every M-polyfold is locally path-connected.  This is
`MPolyfold.locallyPathConnectedSpace` (`Chapter7/LocConnected.lean`). -/
theorem proposition_2_3_7 : LocallyPathConnectedSpace X :=
  P.locallyPathConnectedSpace

end MPolyfold

/-! ### Lemma 2.2.1: the levels of a connected relatively open set are path-connected -/

section Levels

variable {E : ScBanach} {C U : Set (E 0)}

/-- `U_∞ = E_∞ ∩ U` with the topology of `E_∞`: the compatible sequences `(v_m)_m ∈ ∏_m E_m`
(`v_m ↦ v_0` under the inclusion `E_m → E_0`) with `v_0 ∈ U`.  The topology of `E_∞ = ⋂_m E_m`
(the inverse limit of the `E_m`) is the one induced by the product `∏_m E_m`. -/
def ScBanach.lvlSetInfty (E : ScBanach) (U : Set (E 0)) : Set (∀ m, E m) :=
  {v | (∀ m, E.toBase m (v m) = v 0) ∧ v 0 ∈ U}

/-- A smooth point `x ∈ E_∞` as a compatible sequence `(x_m)_m`. -/
def ScBanach.smoothSeq (E : ScBanach) {x : E 0} (hx : x ∈ E.smooth) : ∀ m, E m :=
  fun m => ((ScScale.mem_smooth_iff _).1 hx m).choose

lemma ScBanach.toBase_smoothSeq {x : E 0} (hx : x ∈ E.smooth) (m : ℕ) :
    E.toBase m (E.smoothSeq hx m) = x :=
  ((ScScale.mem_smooth_iff _).1 hx m).choose_spec

lemma ScBanach.smoothSeq_mem {x : E 0} (hx : x ∈ E.smooth) (hxU : x ∈ U) :
    E.smoothSeq hx ∈ E.lvlSetInfty U := by
  have h0 : E.smoothSeq hx 0 = x := E.toBase_smoothSeq hx 0
  exact ⟨fun m => by rw [E.toBase_smoothSeq hx m, h0], by rw [h0]; exact hxU⟩

lemma ScBanach.smoothSeq_zero {x : E 0} (hx : x ∈ E.smooth) : E.smoothSeq hx 0 = x :=
  E.toBase_smoothSeq hx 0

/-- `ScBanach.lvlSetInfty E U` represents `U_∞ = U ∩ E_∞`: its image in `E₀` is `U ∩ E_∞`, and
`v ↦ v₀` is injective on it (`E.toBase_injective`). -/
theorem ScBanach.image_lvlSetInfty :
    (fun v : ∀ m, E m => v 0) '' E.lvlSetInfty U = U ∩ (E.smooth : Set (E 0)) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv.2, (ScScale.mem_smooth_iff _).2 fun m => ⟨v m, hv.1 m⟩⟩
  · rintro ⟨hxU, hx⟩
    exact ⟨E.smoothSeq hx, E.smoothSeq_mem hx hxU, E.smoothSeq_zero hx⟩

/-- **Segments in `U_∞`**: two points of `U_∞` whose level-`0` segment lies in `U` are joined in
`U_∞` by the straight segment (continuous on every level). -/
theorem ScBanach.joinedIn_lvlSetInfty_of_segment {a b : ∀ m, E m} (ha : a ∈ E.lvlSetInfty U)
    (hb : b ∈ E.lvlSetInfty U) (hseg : segment ℝ (a 0) (b 0) ⊆ U) :
    JoinedIn (E.lvlSetInfty U) a b := by
  refine JoinedIn.ofLine (f := fun t : ℝ => AffineMap.lineMap a b t)
    AffineMap.lineMap_continuous.continuousOn (AffineMap.lineMap_apply_zero _ _)
    (AffineMap.lineMap_apply_one _ _) ?_
  rintro _ ⟨t, ht, rfl⟩
  have hcomp : ∀ m, (AffineMap.lineMap a b t : ∀ m, E m) m = AffineMap.lineMap (a m) (b m) t :=
    fun m => by simp [AffineMap.lineMap_apply_module]
  dsimp only
  refine ⟨fun m => ?_, ?_⟩
  · rw [hcomp, hcomp]
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, ha.1 m, hb.1 m]
  · rw [hcomp]
    exact hseg (by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩)

/-- **Smooth points are dense in a partial quadrant, on every level**: `C_m` is convex with
nonempty interior and `E_∞` is dense in `E_m`. -/
theorem IsPartialQuadrant.exists_smooth_near (hC : IsPartialQuadrant E C) {m : ℕ} {z : E m}
    (hz : z ∈ E.lvlSet C m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s ∈ E.smoothLvl m, s ∈ E.lvlSet C m ∧ dist s z < δ := by
  have hcl : z ∈ closure (interior (E.lvlSet C m)) := by
    rw [(hC.convex_lvlSet m).closure_interior_eq_closure_of_nonempty_interior
      (hC.interior_lvlSet_nonempty m)]
    exact subset_closure hz
  obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.1 hcl (Metric.ball z δ) Metric.isOpen_ball
    (Metric.mem_ball_self hδ)
  obtain ⟨s, ⟨hsI, hsB⟩, hss⟩ := (E.dense_smooth m).inter_open_nonempty _
    (isOpen_interior.inter Metric.isOpen_ball) ⟨q, hq2, hq1⟩
  exact ⟨s, hss, interior_subset hsI, hsB⟩

/-- A point of a relatively open `U ⊆ C` has a ball `B_ε(z)` with `B_ε(z) ∩ C ⊆ U`. -/
theorem IsRelOpenInQuadrant.exists_ball_inter_subset (hU : IsRelOpenInQuadrant E C U) {z : E 0}
    (hz : z ∈ U) : ∃ ε > 0, Metric.ball z ε ∩ C ⊆ U := by
  obtain ⟨O', hO', hUO'⟩ := hU.relOpen
  rw [hUO'] at hz ⊢
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO' z hz.1
  exact ⟨ε, hε, inter_subset_inter_left _ hball⟩

/-- **Lemma 2.2.1 (2021), `k = ∞`**: if `U ⊆ C` is relatively open and connected, then
`U_∞ = E_∞ ∩ U` is path-connected for the topology of `E_∞` (`ScBanach.lvlSetInfty`): any two
points are joined by a path which is continuous into every level `E_m`. -/
theorem lemma_2_2_1_infty (hU : IsRelOpenInQuadrant E C U) (hconn : IsConnected U) :
    IsPathConnected (E.lvlSetInfty U) := by
  have hC := hU.isPartialQuadrant
  have hUC : U ⊆ C := by
    obtain ⟨O', -, h⟩ := hU.relOpen
    rw [h]
    exact inter_subset_right
  -- smooth points of `U` near every point of `U`
  have hnear : ∀ z ∈ U, ∀ ε > 0, ∃ v ∈ E.lvlSetInfty U, dist (v 0) z < ε := by
    intro z hz ε hε
    obtain ⟨ε₁, hε₁, hball⟩ := hU.exists_ball_inter_subset hz
    obtain ⟨s, hs, hsC, hsd⟩ := hC.exists_smooth_near (m := 0) (hUC hz) (lt_min hε hε₁)
    have hsU : s ∈ U := hball ⟨lt_of_lt_of_le hsd (min_le_right _ _), hsC⟩
    have hs : s ∈ E.smooth := hs
    refine ⟨E.smoothSeq hs, E.smoothSeq_mem hs hsU, ?_⟩
    rw [E.smoothSeq_zero]
    exact lt_of_lt_of_le hsd (min_le_left _ _)
  obtain ⟨z₀, hz₀⟩ := hconn.nonempty
  obtain ⟨a, ha, -⟩ := hnear z₀ hz₀ 1 one_pos
  refine ⟨a, ha, fun {b} hb => ?_⟩
  -- `P z`: near `z`, every point of `U_∞` is joined to `a`
  let P : E 0 → Prop := fun z => ∃ ε > 0, Metric.ball z ε ∩ C ⊆ U ∧
    ∀ v ∈ E.lvlSetInfty U, v 0 ∈ Metric.ball z ε → JoinedIn (E.lvlSetInfty U) a v
  -- joining propagates inside the convex set `B_ε(z) ∩ C ⊆ U`
  have hprop : ∀ z, ∀ ε > 0, Metric.ball z ε ∩ C ⊆ U → ∀ v₀ ∈ E.lvlSetInfty U,
      v₀ 0 ∈ Metric.ball z ε → JoinedIn (E.lvlSetInfty U) a v₀ → P z := by
    intro z ε hε hball v₀ hv₀ hv₀z hj
    refine ⟨ε, hε, hball, fun v hv hvz => hj.trans
      (ScBanach.joinedIn_lvlSetInfty_of_segment hv₀ hv ?_)⟩
    exact (((convex_ball z ε).inter hC.convex).segment_subset ⟨hv₀z, hUC hv₀.2⟩
      ⟨hvz, hUC hv.2⟩).trans hball
  -- `{z ∈ U | P z}` is clopen in the connected `U`
  have hall : ∀ z ∈ U, P z := by
    have hpc : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.1 hconn.isPreconnected
    let A : Set U := {z | P z}
    have hAo : IsOpen A := by
      refine Metric.isOpen_iff.2 fun z hz => ?_
      obtain ⟨ε, hε, hball, hj⟩ := hz
      refine ⟨ε / 2, half_pos hε, fun z' hz' => ?_⟩
      have hz'z : dist (z' : E 0) z < ε / 2 := hz'
      have hsub : Metric.ball (z' : E 0) (ε / 2) ⊆ Metric.ball (z : E 0) ε :=
        Metric.ball_subset_ball' (by linarith)
      exact ⟨ε / 2, half_pos hε, (inter_subset_inter_left _ hsub).trans hball,
        fun v hv hvz => hj v hv (hsub hvz)⟩
    have hAc : IsClosed A := by
      refine isOpen_compl_iff.1 (Metric.isOpen_iff.2 fun z hz => ?_)
      obtain ⟨ε, hε, hball⟩ := hU.exists_ball_inter_subset z.2
      refine ⟨ε / 2, half_pos hε, fun z' hz' hz'A => hz ?_⟩
      have hz'z : dist (z' : E 0) z < ε / 2 := hz'
      obtain ⟨ε', hε', -, hj⟩ := hz'A
      obtain ⟨v₀, hv₀, hv₀d⟩ := hnear z' z'.2 (min ε' (ε / 2)) (lt_min hε' (half_pos hε))
      refine hprop z ε hε hball v₀ hv₀ ?_ (hj v₀ hv₀ ?_)
      · have := dist_triangle (v₀ 0) z' z
        have := min_le_right ε' (ε / 2)
        change dist (v₀ 0) z < ε
        linarith
      · exact lt_of_lt_of_le hv₀d (min_le_left _ _)
    have hAne : A.Nonempty := by
      obtain ⟨ε, hε, hball⟩ := hU.exists_ball_inter_subset ha.2
      exact ⟨⟨a 0, ha.2⟩, hprop (a 0) ε hε hball a ha (Metric.mem_ball_self hε) (JoinedIn.refl ha)⟩
    have hAu := IsClopen.eq_univ ⟨hAc, hAo⟩ hAne
    intro z hz
    have : (⟨z, hz⟩ : U) ∈ A := hAu ▸ mem_univ _
    exact this
  obtain ⟨ε, hε, -, hj⟩ := hall (b 0) hb.2
  exact hj b hb (Metric.mem_ball_self hε)

/-- **Lemma 2.2.1 (2021), `k ∈ ℕ`**: if `U ⊆ C` is relatively open and connected, then for every
`k`, `U_k = E_k ∩ U` with the topology of `E_k` is path-connected (in particular connected). -/
theorem lemma_2_2_1 (hU : IsRelOpenInQuadrant E C U) (hconn : IsConnected U) (k : ℕ) :
    IsPathConnected (E.lvlSet U k) := by
  have hC := hU.isPartialQuadrant
  obtain ⟨O', hO', hUO'⟩ := hU.relOpen
  -- the projection of the path-connected `U_∞` to `U_k`
  have hsub : (fun v : ∀ m, E m => v k) '' E.lvlSetInfty U ⊆ E.lvlSet U k := by
    rintro _ ⟨v, hv, rfl⟩
    change E.toBase k (v k) ∈ U
    rw [hv.1 k]
    exact hv.2
  obtain ⟨p, hp, hpj⟩ := (lemma_2_2_1_infty hU hconn).image (continuous_apply k)
  refine ⟨p, hsub hp, fun {x} hx => ?_⟩
  -- a smooth point `s` of `U_k` near `x`, joined to `x` by a segment in `U_k`
  have hx' : E.toBase k x ∈ O' ∩ C := hUO' ▸ hx
  have hxC : x ∈ E.lvlSet C k := hx'.2
  obtain ⟨δ, hδ, hδO'⟩ :=
    Metric.isOpen_iff.1 (hO'.preimage (E.toBase k).continuous) x hx'.1
  obtain ⟨s, hs, hsC, hsd⟩ := hC.exists_smooth_near hxC hδ
  have hballU : Metric.ball x δ ∩ E.lvlSet C k ⊆ E.lvlSet U k := fun y hy => by
    change E.toBase k y ∈ U
    rw [hUO']
    exact ⟨hδO' hy.1, hy.2⟩
  have hsB : s ∈ Metric.ball x δ := hsd
  have hseg : JoinedIn (E.lvlSet U k) s x := JoinedIn.of_segment_subset
    ((((convex_ball x δ).inter (hC.convex_lvlSet k)).segment_subset ⟨hsB, hsC⟩
      ⟨Metric.mem_ball_self hδ, hxC⟩).trans hballU)
  -- `s` is the image of the compatible sequence of the smooth point `s₀ = E_k → E_0 (s)`
  have hs0 : E.toBase k s ∈ E.smooth := hs
  have hsU : E.toBase k s ∈ U := hballU ⟨hsB, hsC⟩
  have hsk : E.smoothSeq hs0 k = s := E.toBase_injective k (E.toBase_smoothSeq hs0 k)
  have hsimg : s ∈ (fun v : ∀ m, E m => v k) '' E.lvlSetInfty U :=
    ⟨_, E.smoothSeq_mem hs0 hsU, hsk⟩
  exact ((hpj hsimg).mono hsub).trans hseg

end Levels

/-! ### Lemma 2.2.2, Definition 2.2.3, Theorem 2.2.4 -/

section LocalPathConnected

variable {E : ScBanach} {C : Set (E 0)}

/-- **Lemma 2.2.2 (2021)**: let `r : U → U` be an sc-smooth retraction onto `O`, `x ∈ O`, and
`V(x) = V' ∩ U` an open neighbourhood of `x` in `U`.  Then `W(x) = V(x) ∩ r⁻¹(V(x))` is a relatively
open neighbourhood of `x` in `C`, and (1) `W(x) ∩ O = V(x) ∩ O`, (2) `r(W(x)) ⊆ W(x)` and
`r(W(x)) = O ∩ V(x)`. -/
theorem lemma_2_2_2 (R : ScRetraction E C) {x : E 0} (hx : x ∈ R.retract) {V' : Set (E 0)}
    (hV' : IsOpen V') (hxV' : x ∈ V') :
    let V := V' ∩ R.U
    let W := V ∩ R ⁻¹' V
    IsRelOpenInQuadrant E C W ∧ x ∈ W ∧ W ∩ R.retract = V ∩ R.retract ∧ MapsTo R W W ∧
      R '' W = R.retract ∩ V := by
  intro V W
  have hxU : x ∈ R.U := R.retract_subset hx
  have hRx : R x = x := R.apply_eq_self_of_mem_retract hx
  have hfix : ∀ y ∈ V ∩ R.retract, y ∈ W := fun y hy =>
    ⟨hy.1, by rw [mem_preimage, R.apply_eq_self_of_mem_retract hy.2]; exact hy.1⟩
  refine ⟨?_, hfix x ⟨⟨hxV', hxU⟩, hx⟩, ?_, ?_, ?_⟩
  · -- `W = V' ∩ (U ∩ r⁻¹(V'))`, as `r(U) ⊆ U`
    have : W = (R.U ∩ R ⁻¹' V') ∩ V' := by
      ext z
      constructor
      · rintro ⟨⟨hzV', hzU⟩, hRz, -⟩
        exact ⟨⟨hzU, hRz⟩, hzV'⟩
      · rintro ⟨⟨hzU, hRz⟩, hzV'⟩
        exact ⟨⟨hzV', hzU⟩, hRz, R.mapsTo hzU⟩
    rw [this]
    exact (R.relOpen_inter_preimage hV').inter_isOpen hV'
  · exact Subset.antisymm (fun y hy => ⟨hy.1.1, hy.2⟩) fun y hy => ⟨hfix y hy, hy.2⟩
  · intro z hz
    refine ⟨hz.2, ?_⟩
    rw [mem_preimage, R.idem z hz.1.2]
    exact hz.2
  · refine Subset.antisymm ?_ fun y hy => ⟨y, hfix y ⟨hy.2, hy.1⟩,
      R.apply_eq_self_of_mem_retract hy.1⟩
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨R.apply_mem_retract hz.1.2, hz.2⟩

/-- **Definition 2.2.3 (2021)** is Mathlib's `LocallyPathConnectedSpace`: every point `z` has,
inside every open neighbourhood `V(z)`, a path-connected open neighbourhood `W(z)`. -/
theorem definition_2_2_3 {Z : Type*} [TopologicalSpace Z] :
    LocallyPathConnectedSpace Z ↔ ∀ z : Z, ∀ V : Set Z, IsOpen V → z ∈ V →
      ∃ W, IsOpen W ∧ z ∈ W ∧ W ⊆ V ∧ IsPathConnected W := by
  constructor
  · intro _ z V hV hz
    obtain ⟨W, ⟨hWo, hzW, hWc⟩, hWV⟩ :=
      (isOpen_isPathConnected_basis z).mem_iff.1 (hV.mem_nhds hz)
    exact ⟨W, hWo, hzW, hWV, hWc⟩
  · intro h
    refine LocallyPathConnectedSpace.of_bases
      (p := fun z (W : Set Z) => IsOpen W ∧ z ∈ W ∧ IsPathConnected W) (s := fun _ W => W)
      (fun z => ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩) (fun _ _ h => h.2.2)
    · obtain ⟨V, hVt, hVo, hzV⟩ := mem_nhds_iff.1 ht
      obtain ⟨W, hWo, hzW, hWV, hWc⟩ := h z V hVo hzV
      exact ⟨W, ⟨hWo, hzW, hWc⟩, hWV.trans hVt⟩
    · rintro ⟨W, ⟨hWo, hzW, -⟩, hWt⟩
      exact mem_of_superset (hWo.mem_nhds hzW) hWt

/-- **Theorem 2.2.4 (2021)**: an sc-smooth retract `(O, C, E)` is locally path-connected.  This is
`IsScRetract.locallyPathConnectedSpace` (`Chapter7/LocConnected.lean`). -/
theorem theorem_2_2_4 {O : Set (E 0)} (h : IsScRetract E C O) :
    LocallyPathConnectedSpace O :=
  h.locallyPathConnectedSpace

end LocalPathConnected

/-! ### Definition 2.2.5 and Proposition 2.2.6 -/

section AlmostContractible

/-- **Definition 2.2.5 (2021)**: `Z` is **almost locally contractible** if for every `z ∈ Z` and
open neighbourhood `V(z)` there are an open neighbourhood `W(z) ⊆ V(z)` and a continuous
`Φ : [0, 1] × W(z) → V(z)` with (1) `Φ(0, y) = y`, (2) `Φ(t, z) = z`, (3) `Φ(1, W(z)) = {z}`. -/
def IsAlmostLocallyContractible (Z : Type*) [TopologicalSpace Z] : Prop :=
  ∀ z : Z, ∀ V : Set Z, IsOpen V → z ∈ V → ∃ W : Set Z, IsOpen W ∧ z ∈ W ∧ W ⊆ V ∧
    ∃ Φ : I × W → Z, Continuous Φ ∧ (∀ p, Φ p ∈ V) ∧ (∀ y : W, Φ (0, y) = y) ∧
      (∀ (t : I) (hz : z ∈ W), Φ (t, ⟨z, hz⟩) = z) ∧ ∀ y : W, Φ (1, y) = z

variable {E : ScBanach} {C : Set (E 0)}

/-- **Proposition 2.2.6 (2021)**: an sc-smooth retract `(O, C, E)` is almost locally contractible,
with `Φ(t, y) = r((1 − t)y + tx)` on `W(x) = B_ε(x) ∩ O`. -/
theorem proposition_2_2_6 {O : Set (E 0)} (hO : IsScRetract E C O) :
    IsAlmostLocallyContractible O := by
  obtain ⟨R, rfl⟩ := hO
  intro z V hV hzV
  obtain ⟨Vt, hVto, rfl⟩ := isOpen_induced_iff.1 hV
  have hzU : (z : E 0) ∈ R.U := R.retract_subset z.2
  have hRz : R z = z := R.apply_eq_self_of_mem_retract z.2
  obtain ⟨O', hO'o, hUO'⟩ := R.relOpen.relOpen
  have hUC : R.U ⊆ C := by rw [hUO']; exact inter_subset_right
  have hcont : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  -- `B_ε(z) ∩ C ⊆ U` and `r(B_ε(z) ∩ C) ⊆ Vt`
  have hpre : R ⁻¹' Vt ∈ 𝓝[R.U] (z : E 0) :=
    hcont z hzU (by rw [hRz]; exact hVto.mem_nhds hzV)
  obtain ⟨ε₁, hε₁, hε₁V⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  have hzO' : (z : E 0) ∈ O' := by
    have := hzU
    rw [hUO'] at this
    exact this.1
  obtain ⟨ε₂, hε₂, hε₂O'⟩ := Metric.isOpen_iff.1 hO'o z hzO'
  set ε := min ε₁ ε₂ with hε
  have hε0 : 0 < ε := lt_min hε₁ hε₂
  have hBU : ∀ q ∈ Metric.ball (z : E 0) ε ∩ C, q ∈ R.U ∧ R q ∈ Vt := fun q hq => by
    have hqU : q ∈ R.U := by
      rw [hUO']
      exact ⟨hε₂O' (Metric.ball_subset_ball (min_le_right _ _) hq.1), hq.2⟩
    exact ⟨hqU, hε₁V ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hqU⟩⟩
  have hconv : Convex ℝ (Metric.ball (z : E 0) ε ∩ C) :=
    (convex_ball _ _).inter R.relOpen.isPartialQuadrant.convex
  have hzB : (z : E 0) ∈ Metric.ball (z : E 0) ε ∩ C := ⟨Metric.mem_ball_self hε0, hUC hzU⟩
  set W : Set R.retract := Subtype.val ⁻¹' Metric.ball (z : E 0) ε with hW
  -- the segment from `y` to `z`
  let seg : I × W → E 0 := fun p => (1 - (p.1 : ℝ)) • ((p.2 : R.retract) : E 0) + (p.1 : ℝ) • z
  have hseg : ∀ p, seg p ∈ Metric.ball (z : E 0) ε ∩ C := fun p =>
    hconv ⟨p.2.2, hUC (R.retract_subset p.2.1.2)⟩ hzB (sub_nonneg.2 p.1.2.2) p.1.2.1
      (sub_add_cancel 1 _)
  have hsegc : Continuous seg := by fun_prop
  let Φ : I × W → R.retract := fun p => ⟨R (seg p), R.apply_mem_retract (hBU _ (hseg p)).1⟩
  refine ⟨W, Metric.isOpen_ball.preimage continuous_subtype_val, Metric.mem_ball_self hε0,
    fun y hy => ?_, Φ, ?_, fun p => (hBU _ (hseg p)).2, fun y => ?_, fun t hz => ?_,
    fun y => ?_⟩
  · have := (hBU y ⟨hy, hUC (R.retract_subset y.2)⟩).2
    rwa [R.apply_eq_self_of_mem_retract y.2] at this
  · exact (hcont.comp_continuous hsegc fun p => (hBU _ (hseg p)).1).subtype_mk _
  · refine Subtype.ext ?_
    change R ((1 - ((0 : I) : ℝ)) • ((y : R.retract) : E 0) + ((0 : I) : ℝ) • (z : E 0)) = _
    simp only [Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
    exact R.apply_eq_self_of_mem_retract y.1.2
  · refine Subtype.ext ?_
    change R ((1 - (t : ℝ)) • (z : E 0) + (t : ℝ) • (z : E 0)) = _
    rw [← add_smul, sub_add_cancel, one_smul]
    exact hRz
  · refine Subtype.ext ?_
    change R ((1 - ((1 : I) : ℝ)) • ((y : R.retract) : E 0) + ((1 : I) : ℝ) • (z : E 0)) = _
    simp only [Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
    exact hRz

/-- **Non-vacuity of Definition 2.2.5**: the retract `E₀` (any sc-Banach space `E`, `r = id`) is
almost locally contractible, by Proposition 2.2.6. -/
theorem isAlmostLocallyContractible_univ (E : ScBanach) :
    IsAlmostLocallyContractible (univ : Set (E 0)) :=
  proposition_2_2_6 (C := univ)
    (⟨isPartialQuadrant_univ E, univ, isOpen_univ, (univ_inter _).symm⟩ :
      IsRelOpenInQuadrant E univ univ).isScRetract

end AlmostContractible

end Polyfold
