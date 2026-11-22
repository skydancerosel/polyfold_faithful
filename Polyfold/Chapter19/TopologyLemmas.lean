import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter8.BundleOrbitParacompact

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.3 "Topology on M(Ψ,Ψ′)" and §19.4 "Metrizability Criteria" (pp. 872–885): the point-set
topology of **Lemma 19.3.8** (p. 878), **Theorem 19.3.3** (p. 873, "regular, Hausdorff, locally
metrizable"), **Definition 19.4.1** and **Proposition 19.4.2** (pp. 879–880, the properness conditions
(v1)–(v3)), **Proposition 19.4.4** (p. 883), **Proposition 19.4.5** (p. 884), **Theorem 19.4.6** and
**Proposition 19.4.7** (p. 885), stated for arbitrary topological spaces.

# General topology for the natural topologies of Chapter 19

## The text, paraphrased

(Lemma 19.3.8) `T_{Ψ,Ψ′}` is regular: for `h ∉ A`, `A` closed, take `W(h)`, `W(o)` with
`s : W(h) → W(o)` a homeomorphism, `V(o)` with `cl_O V(o) ⊂ W(o)`; then
`A ∩ cl((s|W(h))⁻¹ V(o)) = ∅`, by a sequence argument that ends with "`W(h) ∩ A = ∅`".
(Theorem 19.3.3) Since `s` is a local homeomorphism into the metrizable `O`, `M(Ψ,Ψ′)` is locally
metrizable.
(Definition 19.4.1) (v1) sequences `h_k` in `M(Ψ,Ψ′)` with `s(h_k) ∈ U(o)` and `t(h_k)` convergent have
convergent subsequences; (v2) `cl_{|S|} |Ψ(U(o))| ⊂ |Ψ(O)|`; (v3) for `q_k ∈ U(o)`, convergence of
`|Ψ(q_k)|` implies that a subsequence of `q_k` converges in `cl_O(U(o)) ⊂ O`.
(Proposition 19.4.2) (v1) ⇔ (v2) ⇔ (v3).
(Proposition 19.4.4) Under properness `M(Ψ,Ψ′)` is paracompact (finitely many sheets `U(h_i)` over
`U(o)`, Lemma 19.4.3, and a locally finite refinement of the `V(o)` in `O`), hence metrizable by
Nagata–Smirnov.
(Proposition 19.4.5) Under properness `T` is Hausdorff and completely regular: `β : O → [0,1]`
with `β(ō) = 0`, `β = 1` off a `G`-invariant `V`, "perhaps using an averaging procedure" `G`-invariant,
descends to `|Ψ(O)|` and is extended by `1`.
(Theorem 19.4.6) Properness and second countability (Urysohn), or properness and paracompactness
(Nagata–Smirnov), imply metrizability. (Proposition 19.4.7) `T` metrizable ⇔ properness + paracompact.

## What is formalized

The item-numbered statements are stated on the uniformizer constructions; here are the
topological cores, for arbitrary spaces.

* `regularSpace_of_isLocalHomeomorph_of_t2` (serves **Lemma 19.3.8**): a Hausdorff space with a local
  homeomorphism into a regular space is regular. The step the text leaves to the reader (choose
  `W(h)` disjoint from `A`) is the choice `W = e.source ∩ interior s`; the sequence argument is
  replaced by a neighbourhood argument (no first countability is needed).
* `exists_isOpen_metrizableSpace_of_isLocalHomeomorph` (serves **Theorem 19.3.3**, "locally
  metrizable").
* `paracompactSpace_of_isLocalHomeomorph_of_finiteSheets` and
  `metrizableSpace_of_isLocalHomeomorph_of_finiteSheets` (serve **Proposition 19.4.4**): the
  conclusion of Lemma 19.4.3 (finitely many open sheets, `s` injective on each, over a
  neighbourhood) is the hypothesis; `finiteSheets_witness_snd` is a witness with two sheets.
* `IsOrbitChart G π` (`π : O → Z` continuous and open, its fibres the orbits of a group `G`; what
  Proposition 19.2.2 (3) gives for `o ↦ |Ψ(o)|`): `IsOrbitChart.homeomorph` (`range π ≃ₜ O/G`),
  `IsOrbitChart.t2Space_range`, `IsOrbitChart.metrizableSpace_range` (Proposition 19.2.2 (5)),
  `isOrbitChart_quotientMk`.
* The properness conditions in abstract form: `OrbitChartV2`, `OrbitChartV3` (Definition 19.4.1
  (2), (3)) with `IsOrbitChart.orbitChartV3_of_v2` (**Proposition 19.4.2**, (2) ⇒ (3), through
  `IsOrbitChart.tendsto_subseq_of_closure_subset`) and `IsOrbitChart.orbitChartV2_of_v3` (the
  converse, for Hausdorff first countable `Z`); `TransitionV1` (Definition 19.4.1 (1), for maps
  `s : M → O`, `t : M → O'`) with `isClosed_range_of_transitionV1` and
  `separated_of_isClosed_relation` (the Hausdorff argument of **Proposition 19.4.5**).
* `exists_invariant_urysohn` (serves **Proposition 19.4.5**, the averaging): an invariant
  `β : O → [0,1]` with `β(ō) = 0` and `β = 1` off `V`. Averaging a `β` that only vanishes at `ō`
  need not vanish at `ō` (the average at `ō` is `(1/#G) ∑ β(g ō)`); the lemma averages a `β` that
  vanishes on the whole orbit `G·ō` (Urysohn for the finite closed orbit and `O \ V`).
* `IsOrbitChart.exists_urysohn` (the descended and extended `β̄` of Proposition 19.4.5),
  `t2Space_of_forall_closure_subset_t2`, and for a family of orbit charts covering `Z` with (v2):
  `t2Space_of_orbitCharts`, `completelyRegularSpace_of_orbitCharts` (**Proposition 19.4.5**),
  `metrizableSpace_of_orbitCharts_secondCountable`, `metrizableSpace_of_orbitCharts_paracompact`
  (**Theorem 19.4.6** (1), (2)), `IsOrbitChart.orbitChartV2_of_regularSpace` and
  `paracompact_and_orbitChartV2_of_metrizableSpace` (**Proposition 19.4.7**, (1) ⇒ (2)).
  `orbitCharts_witness_reflection`: the hypotheses hold for `ℤ/2` acting on `ℝ` by `x ↦ ±x`.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

namespace Chapter19

universe u v w

/-! ### Lemma 19.3.8: regularity through a local homeomorphism -/

section LocalHomeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- **Serves Lemma 19.3.8** (p. 878): a Hausdorff space `X` with a local homeomorphism `f` into a
regular space `Y` is regular (for `M(Ψ,Ψ′)`, `f = s`). For `x` and a neighbourhood `s` of `x`: on
`W = e.source ∩ interior s` (`e` a local inverse chart at `x`; this is the text's `W(h)` with
`W(h) ∩ A = ∅`), pick a closed neighbourhood `C ⊆ f(W)` of `f(x)`; the closure of
`N = W ∩ f⁻¹(C)` stays in `W`, by Hausdorffness of `X` and injectivity of `f` on `W`. -/
theorem regularSpace_of_isLocalHomeomorph_of_t2 [T2Space X] [RegularSpace Y]
    (hf : IsLocalHomeomorph f) : RegularSpace X := by
  refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun x s hs => ?_
  have hfc := hf.continuous
  obtain ⟨e, hxe, rfl⟩ := hf x
  set W := e.source ∩ interior s with hW
  have hWo : IsOpen W := e.open_source.inter isOpen_interior
  have hWsrc : W ⊆ e.source := inter_subset_left
  have hxW : x ∈ W := ⟨hxe, mem_interior_iff_mem_nhds.2 hs⟩
  have heW : IsOpen (e '' W) := e.isOpen_image_of_subset_source hWo hWsrc
  obtain ⟨C, hC, hCc, hCW⟩ := exists_mem_nhds_isClosed_subset (heW.mem_nhds (mem_image_of_mem e hxW))
  set N := W ∩ e ⁻¹' C with hN
  have hNx : N ∈ 𝓝 x := inter_mem (hWo.mem_nhds hxW) (hfc.continuousAt.preimage_mem_nhds hC)
  have hclN : closure N ⊆ W := by
    intro y hy
    have hey : e y ∈ C := by
      have : e y ∈ closure (e '' N) := mem_closure_image hfc.continuousAt hy
      exact closure_minimal (image_subset_iff.2 fun z hz => hz.2) hCc this
    obtain ⟨w, hwW, hwy⟩ := hCW hey
    by_contra hyW
    have hyw : y ≠ w := fun h => hyW (h ▸ hwW)
    obtain ⟨P, Q, hPo, hQo, hyP, hwQ, hPQ⟩ := t2_separation hyw
    have hQ' : IsOpen (e '' (Q ∩ W)) :=
      e.isOpen_image_of_subset_source (hQo.inter hWo) (inter_subset_right.trans hWsrc)
    have hM : IsOpen (P ∩ e ⁻¹' (e '' (Q ∩ W))) := hPo.inter (hQ'.preimage hfc)
    obtain ⟨z, ⟨hzP, q, hq, hqz⟩, hzN⟩ :=
      mem_closure_iff.1 hy _ hM ⟨hyP, w, ⟨hwQ, hwW⟩, hwy⟩
    have : q = z := e.injOn (hWsrc hq.2) (hWsrc hzN.1) hqz
    exact hPQ.le_bot ⟨hzP, this ▸ hq.1⟩
  exact ⟨closure N, mem_of_superset hNx subset_closure, isClosed_closure,
    hclN.trans (inter_subset_right.trans interior_subset)⟩

/-- **Serves Theorem 19.3.3** (p. 873, "locally metrizable"; Proposition 19.3.5): a space with a
local homeomorphism into a metrizable space is locally metrizable. -/
theorem exists_isOpen_metrizableSpace_of_isLocalHomeomorph [MetrizableSpace Y]
    (hf : IsLocalHomeomorph f) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U := by
  obtain ⟨e, hxe, rfl⟩ := hf x
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  exact e.isOpenEmbedding_restrict.isEmbedding.metrizableSpace

/-- **Serves Proposition 19.4.4** (p. 883): if `f : X → Y` is a local homeomorphism into a
paracompact space and every `y` has an open neighbourhood `V` whose preimage is covered by finitely
many open sheets `U`, each with `f` injective on `U` and `y ∈ f(U)` (the conclusion of
Lemma 19.4.3, with `f = s`), then `X` is paracompact. As in the text: shrink `V` so that every sheet
lies in one member of the cover, refine the shrunken `V`'s locally finitely in `Y`, and pull back
sheet by sheet. -/
theorem paracompactSpace_of_isLocalHomeomorph_of_finiteSheets [ParacompactSpace Y]
    (hf : IsLocalHomeomorph f)
    (hsheets : ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ S : Set (Set X), S.Finite ∧
      (∀ U ∈ S, IsOpen U ∧ InjOn f U ∧ y ∈ f '' U) ∧ f ⁻¹' V ⊆ ⋃₀ S) :
    ParacompactSpace X := by
  refine ⟨fun α s hso hsc => ?_⟩
  choose V hVo hyV S hSf hS hVS using hsheets
  have hpt : ∀ (y : Y) (p : S y), ∃ a : α, ∃ x ∈ (p : Set X), f x = y ∧ x ∈ s a := by
    intro y p
    obtain ⟨x, hxU, hxy⟩ := (hS y p.1 p.2).2.2
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hsc.symm ▸ mem_univ x : x ∈ ⋃ a, s a)
    exact ⟨a, x, hxU, hxy, ha⟩
  choose a ha using hpt
  have hfin : ∀ y, Finite (S y) := fun y => (hSf y).to_subtype
  set V' : Y → Set Y := fun y => V y ∩ ⋂ p : S y, f '' ((p : Set X) ∩ s (a y p)) with hV'
  have hV'o : ∀ y, IsOpen (V' y) := fun y =>
    (hVo y).inter (isOpen_iInter_of_finite fun p => hf.isOpenMap _ ((hS y p.1 p.2).1.inter
      (hso _)))
  have hyV' : ∀ y, y ∈ V' y := fun y => ⟨hyV y, mem_iInter.2 fun p => by
    obtain ⟨x, hxU, hxy, hxs⟩ := ha y p
    exact ⟨x, ⟨hxU, hxs⟩, hxy⟩⟩
  obtain ⟨W, hWo, hWc, hWlf, hWV'⟩ := precise_refinement V' hV'o
    (eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, hyV' y⟩)
  set T : Set (Set X) := ⋃ y, (fun U => f ⁻¹' W y ∩ U) '' S y with hT
  refine ⟨T, Subtype.val, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, U, hU, rfl⟩ : ∃ y, ∃ U ∈ S y, f ⁻¹' W y ∩ U = t := by
      simpa [hT] using ht
    exact ((hWo y).preimage hf.continuous).inter (hS y U hU).1
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := mem_iUnion.1 (hWc.symm ▸ mem_univ (f x) : f x ∈ ⋃ y, W y)
    obtain ⟨U, hU, hxU⟩ := hVS y ((hWV' y hy).1 : f x ∈ V y)
    exact mem_iUnion.2 ⟨⟨f ⁻¹' W y ∩ U, mem_iUnion.2 ⟨y, U, hU, rfl⟩⟩, hy, hxU⟩
  · intro x
    obtain ⟨N, hN, hNf⟩ := hWlf (f x)
    refine ⟨f ⁻¹' N, hf.continuous.continuousAt.preimage_mem_nhds hN, ?_⟩
    have hfinT : {t : Set X | ∃ y ∈ {y | (W y ∩ N).Nonempty}, ∃ U ∈ S y,
        t = f ⁻¹' W y ∩ U}.Finite := by
      have : {t : Set X | ∃ y ∈ {y | (W y ∩ N).Nonempty}, ∃ U ∈ S y, t = f ⁻¹' W y ∩ U} =
          ⋃ y ∈ {y | (W y ∩ N).Nonempty}, (fun U => f ⁻¹' W y ∩ U) '' S y := by
        ext t
        simp only [mem_ofPred_eq, mem_iUnion, mem_image, exists_prop]
        constructor
        · rintro ⟨y, hy, U, hU, rfl⟩
          exact ⟨y, hy, U, hU, rfl⟩
        · rintro ⟨y, hy, U, hU, rfl⟩
          exact ⟨y, hy, U, hU, rfl⟩
      rw [this]
      exact hNf.biUnion fun y _ => (hSf y).image _
    refine (hfinT.preimage Subtype.val_injective.injOn).subset ?_
    rintro ⟨t, ht⟩ ⟨z, hzt, hzN⟩
    obtain ⟨y, U, hU, rfl⟩ : ∃ y, ∃ U ∈ S y, f ⁻¹' W y ∩ U = t := by
      simpa [hT] using ht
    exact ⟨y, ⟨f z, hzt.1, hzN⟩, U, hU, rfl⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, U, hU, rfl⟩ : ∃ y, ∃ U ∈ S y, f ⁻¹' W y ∩ U = t := by
      simpa [hT] using ht
    refine ⟨a y ⟨U, hU⟩, fun x hx => ?_⟩
    obtain ⟨-, hx'⟩ := hWV' y hx.1
    obtain ⟨x', ⟨hx'U, hx's⟩, hx'x⟩ := mem_iInter.1 hx' ⟨U, hU⟩
    rwa [(hS y U hU).2.1 hx.2 hx'U hx'x.symm]

/-- **Serves Proposition 19.4.4** (p. 883): under the hypotheses of
`paracompactSpace_of_isLocalHomeomorph_of_finiteSheets`, a Hausdorff `X` with a local homeomorphism
into a metrizable `Y` is metrizable (paracompact, locally metrizable, Smirnov's theorem
`Polyfold.metrizableSpace_of_locally`). -/
theorem metrizableSpace_of_isLocalHomeomorph_of_finiteSheets [T2Space X] [MetrizableSpace Y]
    (hf : IsLocalHomeomorph f)
    (hsheets : ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ S : Set (Set X), S.Finite ∧
      (∀ U ∈ S, IsOpen U ∧ InjOn f U ∧ y ∈ f '' U) ∧ f ⁻¹' V ⊆ ⋃₀ S) :
    MetrizableSpace X := by
  have := paracompactSpace_of_metrizableSpace Y
  have := paracompactSpace_of_isLocalHomeomorph_of_finiteSheets hf hsheets
  exact metrizableSpace_of_locally (exists_isOpen_metrizableSpace_of_isLocalHomeomorph hf)

end LocalHomeomorph

/-! ### Orbit charts and the properness conditions of Definition 19.4.1 -/

section OrbitChart

variable {G : Type u} [Group G] {O : Type v} [TopologicalSpace O] [MulAction G O]
  {Z : Type w} [TopologicalSpace Z]

variable (G) in
/-- **An orbit chart** `π : O → Z` for a group `G` acting on `O`: `π` is continuous and open and its
fibres are the `G`-orbits. This is what Proposition 19.2.2 (3) (p. 869) gives for
`O → |S|, o ↦ |Ψ(o)|` of a uniformizer `Ψ : G ⋉ O → S` (`|Ψ| : G\O → |S|` is an open embedding). -/
structure IsOrbitChart (π : O → Z) : Prop where
  continuous : Continuous π
  isOpenMap : IsOpenMap π
  eq_iff : ∀ x y : O, π x = π y ↔ ∃ g : G, g • x = y

namespace IsOrbitChart

variable {π : O → Z}

theorem isOpen_range (h : IsOrbitChart G π) : IsOpen (range π) := h.isOpenMap.isOpen_range

theorem apply_smul (h : IsOrbitChart G π) (g : G) (x : O) : π (g • x) = π x :=
  ((h.eq_iff x (g • x)).2 ⟨g, rfl⟩).symm

/-- `O/G → range π`, induced by `π`. -/
def quotientToRange (h : IsOrbitChart G π) : MulAction.orbitRel.Quotient G O → range π :=
  Quotient.lift (fun x => (⟨π x, x, rfl⟩ : range π)) fun x y hxy => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
    exact Subtype.ext (show π x = π y by rw [← hg, h.apply_smul])

theorem quotientToRange_mk (h : IsOrbitChart G π) (x : O) :
    h.quotientToRange (Quotient.mk _ x) = ⟨π x, x, rfl⟩ := rfl

theorem bijective_quotientToRange (h : IsOrbitChart G π) : Bijective h.quotientToRange := by
  refine ⟨fun a b hab => ?_, fun ⟨z, x, hx⟩ => ⟨Quotient.mk _ x, Subtype.ext hx⟩⟩
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  obtain ⟨g, hg⟩ := (h.eq_iff y x).1 (congrArg Subtype.val hab).symm
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g, hg⟩))

theorem continuous_quotientToRange (h : IsOrbitChart G π) : Continuous h.quotientToRange :=
  continuous_quot_lift _ (h.continuous.subtype_mk _)

theorem isOpenMap_quotientToRange (h : IsOrbitChart G π) : IsOpenMap h.quotientToRange := by
  intro S hS
  have hS' : IsOpen ((Quotient.mk (MulAction.orbitRel G O)) ⁻¹' S) := hS
  have : h.quotientToRange '' S =
      (Subtype.val : range π → Z) ⁻¹' (π '' ((Quotient.mk (MulAction.orbitRel G O)) ⁻¹' S)) := by
    ext ⟨z, x, rfl⟩
    constructor
    · rintro ⟨q, hq, hqz⟩
      induction q using Quotient.inductionOn with | h y => ?_
      exact ⟨y, hq, congrArg Subtype.val hqz⟩
    · rintro ⟨y, hy, hyz⟩
      exact ⟨Quotient.mk _ y, hy, Subtype.ext hyz⟩
  rw [this]
  exact (h.isOpenMap _ hS').preimage continuous_subtype_val

/-- **`range π ≃ₜ O/G`** for an orbit chart (Proposition 19.2.2 (3), p. 869: `|Ψ| : G\O → |Ψ(O)|` is a
homeomorphism). -/
def homeomorph (h : IsOrbitChart G π) : range π ≃ₜ MulAction.orbitRel.Quotient G O :=
  ((Equiv.ofBijective _ h.bijective_quotientToRange).toHomeomorphOfContinuousOpen
    h.continuous_quotientToRange h.isOpenMap_quotientToRange).symm

/-- **The image of an orbit chart is Hausdorff** if `O` is (serves Proposition 19.4.5, p. 884, and
Proposition 19.2.2). For `π x ≠ π y`, separate `g x` from `y` for every `g`, and intersect. -/
theorem t2Space_range [Finite G] [ContinuousConstSMul G O] [T2Space O] (h : IsOrbitChart G π) :
    T2Space (range π) := by
  refine ⟨fun a b hab => ?_⟩
  rcases a with ⟨_, x, rfl⟩
  rcases b with ⟨_, y, rfl⟩
  have hne : ∀ g : G, g • x ≠ y := fun g hg => hab (Subtype.ext ((h.eq_iff x y).2 ⟨g, hg⟩))
  choose A B hAo hBo hxA hyB hAB using fun g => t2_separation (hne g)
  set A' := ⋂ g : G, (fun z : O => g • z) ⁻¹' A g
  set B' := ⋂ g : G, B g
  have hA'o : IsOpen A' := isOpen_iInter_of_finite fun g => (hAo g).preimage (continuous_const_smul g)
  have hB'o : IsOpen B' := isOpen_iInter_of_finite hBo
  refine ⟨(Subtype.val : range π → Z) ⁻¹' (π '' A'), (Subtype.val : range π → Z) ⁻¹' (π '' B'),
    (h.isOpenMap _ hA'o).preimage continuous_subtype_val,
    (h.isOpenMap _ hB'o).preimage continuous_subtype_val,
    ⟨x, mem_iInter.2 fun g => hxA g, rfl⟩, ⟨y, mem_iInter.2 fun g => hyB g, rfl⟩, ?_⟩
  refine Set.disjoint_left.2 fun z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩ => ?_
  obtain ⟨g, hg⟩ := (h.eq_iff p q).1 (hpz.trans hqz.symm)
  have hq' : g • p ∈ B g := hg ▸ mem_iInter.1 hq g
  exact (hAB g).le_bot ⟨mem_iInter.1 hp g, hq'⟩

/-- **The image of an orbit chart is metrizable** if `O` is (serves Proposition 19.2.2 (5), p. 869),
through `homeomorph` and `metrizableSpace_orbitRel_quotient_finite`. -/
theorem metrizableSpace_range [Finite G] [ContinuousConstSMul G O] [MetrizableSpace O]
    (h : IsOrbitChart G π) : MetrizableSpace (range π) := by
  have := metrizableSpace_orbitRel_quotient_finite (G := G) (U := O) continuous_const_smul
  exact h.homeomorph.isEmbedding.metrizableSpace

end IsOrbitChart

/-- **Properness condition (v2) at `o`** (Definition 19.4.1 (2), p. 879), for a map `π : O → Z`:
an open `U ∋ o` with `cl_Z π(U) ⊆ π(O)`. -/
def OrbitChartV2 (π : O → Z) (o : O) : Prop :=
  ∃ U : Set O, IsOpen U ∧ o ∈ U ∧ closure (π '' U) ⊆ range π

/-- **Properness condition (v3) at `o`** (Definition 19.4.1 (3), p. 879), for a map `π : O → Z`: an
open `U ∋ o` such that for `q_k ∈ U` with `π(q_k)` convergent in `Z`, a subsequence of `q_k` converges
to a point of `cl_O(U)`. -/
def OrbitChartV3 (π : O → Z) (o : O) : Prop :=
  ∃ U : Set O, IsOpen U ∧ o ∈ U ∧ ∀ q : ℕ → O, (∀ k, q k ∈ U) → ∀ z : Z,
    Tendsto (π ∘ q) atTop (𝓝 z) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p ∈ closure U, Tendsto (q ∘ φ) atTop (𝓝 p)

namespace IsOrbitChart

variable {π : O → Z}

/-- **Serves Proposition 19.4.2** (p. 880), (2) ⇒ (3), for one `U`: if `cl π(U) ⊆ π(O)` and
`π(q_k) → z` with `q_k ∈ U`, then `z = π(q̄)` and, `G` being finite, for one `g` the point `q̄` is a
cluster point of `g q_k`; a subsequence of `q_k` converges to `g⁻¹ q̄ ∈ cl_O(U)`. -/
theorem tendsto_subseq_of_closure_subset [Finite G] [ContinuousConstSMul G O]
    [FirstCountableTopology O] (h : IsOrbitChart G π) {U : Set O}
    (hU : closure (π '' U) ⊆ range π) (q : ℕ → O) (hq : ∀ k, q k ∈ U) (z : Z)
    (hz : Tendsto (π ∘ q) atTop (𝓝 z)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p ∈ closure U, Tendsto (q ∘ φ) atTop (𝓝 p) := by
  obtain ⟨q₀, rfl⟩ := hU (mem_closure_of_tendsto hz
    (Eventually.of_forall fun k => mem_image_of_mem π (hq k)))
  have hclus : ∃ g : G, MapClusterPt q₀ atTop fun k => g • q k := by
    by_contra hno
    push Not at hno
    have : ∀ g : G, ∃ s ∈ 𝓝 q₀, ∀ᶠ k in atTop, g • q k ∉ s := by
      intro g
      have := hno g
      rw [mapClusterPt_iff_frequently] at this
      push Not at this
      obtain ⟨s, hs, hev⟩ := this
      exact ⟨s, hs, hev.mono fun k hk => by simpa using hk⟩
    choose s hs hev using this
    have hsm : (⋂ g, s g) ∈ 𝓝 q₀ := Filter.iInter_mem.2 hs
    have h1 : ∀ᶠ k in atTop, π (q k) ∈ π '' ⋂ g, s g := hz (h.isOpenMap.image_mem_nhds hsm)
    have h2 : ∀ᶠ k in atTop, ∀ g, g • q k ∉ s g := Filter.eventually_all.2 hev
    obtain ⟨k, ⟨y, hy, hyk⟩, hk⟩ := (h1.and h2).exists
    obtain ⟨g, hg⟩ := (h.eq_iff (q k) y).1 hyk.symm
    exact hk g (hg ▸ mem_iInter.1 hy g)
  obtain ⟨g, hg⟩ := hclus
  obtain ⟨φ, hφ, hlim⟩ := hg.tendsto_subseq
  refine ⟨φ, hφ, g⁻¹ • q₀, ?_, ?_⟩
  · have : Tendsto (q ∘ φ) atTop (𝓝 (g⁻¹ • q₀)) := by
      have := ((continuous_const_smul g⁻¹).tendsto q₀).comp hlim
      simpa [Function.comp_def, inv_smul_smul] using this
    exact mem_closure_of_tendsto this (Eventually.of_forall fun k => hq (φ k))
  · have := ((continuous_const_smul g⁻¹).tendsto q₀).comp hlim
    simpa [Function.comp_def, inv_smul_smul] using this

/-- **Proposition 19.4.2** (p. 880), (2) ⇒ (3), in abstract form: (v2) at `o` implies (v3) at `o`
(same `U`). -/
theorem orbitChartV3_of_v2 [Finite G] [ContinuousConstSMul G O] [FirstCountableTopology O]
    (h : IsOrbitChart G π) {o : O} (hv : OrbitChartV2 π o) : OrbitChartV3 π o := by
  obtain ⟨U, hUo, hoU, hU⟩ := hv
  exact ⟨U, hUo, hoU, h.tendsto_subseq_of_closure_subset hU⟩

/-- **(v3) ⇒ (v2) at `o`** (serves Proposition 19.4.2, p. 880) for a Hausdorff, Fréchet–Urysohn `Z`
(first countable, as `|S|` is by Proposition 19.2.2 (4)). The text proves (3) ⇒ (1) ⇒ (2) through
the transition sets; without them the uniqueness of limits in `Z` is used. -/
theorem orbitChartV2_of_v3 [T2Space Z] [FrechetUrysohnSpace Z] (h : IsOrbitChart G π) {o : O}
    (hv : OrbitChartV3 π o) : OrbitChartV2 π o := by
  obtain ⟨U, hUo, hoU, hU⟩ := hv
  refine ⟨U, hUo, hoU, fun z hz => ?_⟩
  obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 hz
  choose q hqU hqx using hx
  have hqz : Tendsto (π ∘ q) atTop (𝓝 z) := by
    simpa [Function.comp_def, hqx] using hxz
  obtain ⟨φ, hφ, p, -, hp⟩ := hU q hqU z hqz
  have h1 : Tendsto (π ∘ (q ∘ φ)) atTop (𝓝 (π p)) := (h.continuous.tendsto p).comp hp
  have h2 : Tendsto (π ∘ (q ∘ φ)) atTop (𝓝 z) := hqz.comp hφ.tendsto_atTop
  exact ⟨p, tendsto_nhds_unique h1 h2⟩

/-- **Proposition 19.4.7** (p. 885), (1) ⇒ (2), in abstract form: if `Z` is regular (for instance
metrizable), every orbit chart satisfies (v2) at every point (a closed neighbourhood of `π(o)`
inside the open `π(O)`). -/
theorem orbitChartV2_of_regularSpace [RegularSpace Z] (h : IsOrbitChart G π) (o : O) :
    OrbitChartV2 π o := by
  obtain ⟨C, hC, hCc, hCr⟩ :=
    exists_mem_nhds_isClosed_subset (h.isOpen_range.mem_nhds (mem_range_self o))
  refine ⟨π ⁻¹' interior C, isOpen_interior.preimage h.continuous,
    mem_interior_iff_mem_nhds.2 hC, ?_⟩
  exact (closure_mono ((image_preimage_subset _ _).trans interior_subset)).trans
    (hCc.closure_subset.trans hCr)

end IsOrbitChart

end OrbitChart

/-! ### The abstract (v1) and the Hausdorff argument of Proposition 19.4.5 -/

section TransitionV1

variable {M : Type u} {O : Type v} {O' : Type w} [TopologicalSpace M] [TopologicalSpace O]
  [TopologicalSpace O']

/-- **Properness condition (v1) at `o`** (Definition 19.4.1 (1), p. 879), for maps `s : M → O`,
`t : M → O'` (for the transition set, `M = M(Ψ,Ψ′)` and `s`, `t` its source and target maps): an
open `U ∋ o` such that every sequence `h_k` with `s(h_k) ∈ U` and `t(h_k)` convergent has a convergent
subsequence. -/
def TransitionV1 (s : M → O) (t : M → O') (o : O) : Prop :=
  ∃ U : Set O, IsOpen U ∧ o ∈ U ∧ ∀ h : ℕ → M, (∀ k, s (h k) ∈ U) → ∀ p : O',
    Tendsto (t ∘ h) atTop (𝓝 p) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : M, Tendsto (h ∘ φ) atTop (𝓝 m)

/-- **Serves Propositions 19.4.2 and 19.4.5** (pp. 880, 884): if (v1) holds at every point of `O`,
the set `{(s(h), t(h))}` is closed in `O × O'` (for continuous `s`, `t` into first countable
Hausdorff spaces). For the transition set this set is `{(o, o') | Ψ(o) ≅ Ψ′(o')}`. -/
theorem isClosed_range_of_transitionV1 [FirstCountableTopology O] [FirstCountableTopology O']
    [T2Space O] [T2Space O'] {s : M → O} {t : M → O'} (hs : Continuous s) (ht : Continuous t)
    (hv : ∀ o, TransitionV1 s t o) : IsClosed (range fun m => (s m, t m)) := by
  refine IsSeqClosed.isClosed fun u x hu hux => ?_
  choose h hh using hu
  obtain ⟨U, hUo, hoU, hU⟩ := hv x.1
  have hu' : u = fun n => (s (h n), t (h n)) := funext fun n => (hh n).symm
  rw [hu'] at hux
  have h1 : Tendsto (s ∘ h) atTop (𝓝 x.1) := (continuous_fst.tendsto x).comp hux
  have h2 : Tendsto (t ∘ h) atTop (𝓝 x.2) := (continuous_snd.tendsto x).comp hux
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1 (hUo.mem_nhds hoU))
  set h' : ℕ → M := fun k => h (k + N)
  have h1' : Tendsto (s ∘ h') atTop (𝓝 x.1) := h1.comp (tendsto_add_atTop_nat N)
  have h2' : Tendsto (t ∘ h') atTop (𝓝 x.2) := h2.comp (tendsto_add_atTop_nat N)
  obtain ⟨φ, hφ, m, hm⟩ := hU h' (fun k => hN _ (Nat.le_add_left N k)) x.2 h2'
  have e1 : s m = x.1 :=
    tendsto_nhds_unique ((hs.tendsto m).comp hm) (h1'.comp hφ.tendsto_atTop)
  have e2 : t m = x.2 :=
    tendsto_nhds_unique ((ht.tendsto m).comp hm) (h2'.comp hφ.tendsto_atTop)
  exact ⟨m, Prod.ext e1 e2⟩

/-- **Serves Proposition 19.4.5** (p. 884, Hausdorff part, the text's route): for open maps
`π : O → Z`, `π' : O' → Z` whose relation `{(x, x') | π x = π' x'}` is closed (the range of
`(s, t)` on the transition set, `isClosed_range_of_transitionV1`), points `π(o) ≠ π'(o')` have
disjoint open neighbourhoods. -/
theorem separated_of_isClosed_relation {Z : Type*} [TopologicalSpace Z] {π : O → Z} {π' : O' → Z}
    (hπ : IsOpenMap π) (hπ' : IsOpenMap π') (hR : IsClosed {q : O × O' | π q.1 = π' q.2})
    {o : O} {o' : O'} (hne : π o ≠ π' o') :
    ∃ U V : Set Z, IsOpen U ∧ IsOpen V ∧ π o ∈ U ∧ π' o' ∈ V ∧ Disjoint U V := by
  obtain ⟨A, B, hA, hB, hoA, hoB, hAB⟩ := isOpen_prod_iff.1 hR.isOpen_compl o o' hne
  refine ⟨π '' A, π' '' B, hπ _ hA, hπ' _ hB, mem_image_of_mem _ hoA, mem_image_of_mem _ hoB, ?_⟩
  refine Set.disjoint_left.2 fun z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩ => ?_
  exact hAB (mk_mem_prod ha hb) (haz.trans hbz.symm)

end TransitionV1

/-! ### Hausdorff and completely regular: Proposition 19.4.5 -/

section CompletelyRegular

variable {Z : Type w} [TopologicalSpace Z]

/-- **Serves Proposition 19.4.5** (p. 884, Hausdorff part, through (v2)): a space in which every
point `z` has an open Hausdorff neighbourhood `W` and an open neighbourhood `N` with
`cl_Z N ⊆ W` is Hausdorff. (For `z' ∉ cl N`, `N` and `Z \ cl N` separate; otherwise both points lie
in `W`.) -/
theorem t2Space_of_forall_closure_subset_t2
    (h : ∀ z : Z, ∃ W : Set Z, IsOpen W ∧ T2Space W ∧ ∃ N : Set Z, IsOpen N ∧ z ∈ N ∧
      closure N ⊆ W) : T2Space Z := by
  refine ⟨fun z₁ z₂ hne => ?_⟩
  obtain ⟨W, hWo, hWt, N, hNo, hzN, hNW⟩ := h z₂
  by_cases hz₁ : z₁ ∈ closure N
  · have h₁ : z₁ ∈ W := hNW hz₁
    have h₂ : z₂ ∈ W := hNW (subset_closure hzN)
    have hne' : (⟨z₁, h₁⟩ : W) ≠ ⟨z₂, h₂⟩ := fun e => hne (congrArg Subtype.val e)
    obtain ⟨u, v, hu, hv, hzu, hzv, huv⟩ := t2_separation hne'
    refine ⟨Subtype.val '' u, Subtype.val '' v, hWo.isOpenMap_subtype_val _ hu,
      hWo.isOpenMap_subtype_val _ hv, ⟨_, hzu, rfl⟩, ⟨_, hzv, rfl⟩, ?_⟩
    exact (disjoint_image_iff Subtype.val_injective).2 huv
  · exact ⟨(closure N)ᶜ, N, isClosed_closure.isOpen_compl, hNo, hz₁, hzN,
      disjoint_compl_left.mono_right subset_closure⟩

variable {G : Type u} [Group G] {O : Type v} [TopologicalSpace O] [MulAction G O]

/-- **Serves Proposition 19.4.5** (p. 884, the averaging step, which the text leaves open): for a
finite group acting continuously on a normal `T₁` space `O` (for instance a metrizable one), a point
`ō` and a `G`-invariant open `V ∋ ō`, there is a continuous `G`-invariant `β : O → [0,1]` with
`β(ō) = 0` and `β = 1` off `V`. Averaging a `β₀` that only vanishes at `ō` gives
`β(ō) = (1/#G) ∑_g β₀(g ō)`, which need not vanish; here `β₀` vanishes on the finite closed orbit
`G·ō` (Urysohn, `exists_continuous_zero_one_of_isClosed`), and its average keeps `β(ō) = 0`. -/
theorem exists_invariant_urysohn [Finite G] [ContinuousConstSMul G O] [NormalSpace O] [T1Space O]
    (o : O) {V : Set O} (hV : IsOpen V) (hVinv : ∀ g : G, ∀ x ∈ V, g • x ∈ V) (ho : o ∈ V) :
    ∃ β : O → ℝ, Continuous β ∧ β o = 0 ∧ (∀ x, x ∉ V → β x = 1) ∧
      (∀ x, β x ∈ Icc (0 : ℝ) 1) ∧ ∀ (g : G) (x : O), β (g • x) = β x := by
  let _ := Fintype.ofFinite G
  have hF : IsClosed (range fun g : G => g • o) := (finite_range _).isClosed
  have hd : Disjoint (range fun g : G => g • o) Vᶜ := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨g, rfl⟩ h
    exact h (hVinv g o ho)
  obtain ⟨β₀, h0, h1, h01⟩ := exists_continuous_zero_one_of_isClosed hF hV.isClosed_compl hd
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun x => (Fintype.card G : ℝ)⁻¹ * ∑ g : G, β₀ (g • x), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun g _ =>
      β₀.continuous.comp (continuous_const_smul g))
  · simp only
    rw [Finset.sum_eq_zero fun g _ => h0 ⟨g, rfl⟩, mul_zero]
  · intro x hx
    simp only
    have : ∀ g : G, β₀ (g • x) = 1 := fun g => h1 fun hgx => hx (by
      simpa using hVinv g⁻¹ _ hgx)
    rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_const, Finset.card_univ, nsmul_one,
      inv_mul_cancel₀ hcard]
  · intro x
    have hpos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
    refine ⟨mul_nonneg (inv_nonneg.2 hpos.le) (Finset.sum_nonneg fun g _ => (h01 _).1), ?_⟩
    rw [inv_mul_le_iff₀ hpos, mul_one]
    calc ∑ g : G, β₀ (g • x) ≤ ∑ _g : G, (1 : ℝ) := Finset.sum_le_sum fun g _ => (h01 _).2
      _ = Fintype.card G := by simp
  · intro g x
    simp only
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun k => by simp [mul_smul]

variable {π : O → Z}

namespace IsOrbitChart

/-- **Serves Proposition 19.4.5** (p. 884, completely regular part): for an orbit chart `π : O → Z`
(`O` normal `T₁`, `G` finite) satisfying (v2) at `ō`, and a closed `A ∌ π(ō)`, there is a continuous
`f : Z → [0,1]` with `f(π ō) = 0` and `f = 1` on `A`. The text's construction: `V` the `G`-saturation
of `U(ō) \ π⁻¹(A)`, an invariant `β` from `exists_invariant_urysohn` (the averaging), descended to
`π(O)` and extended by `1`; it is continuous on `π(O)` since `π` is open, and equal to `1` off
`cl_Z π(V) ⊆ π(O)` by (v2). -/
theorem exists_urysohn [Finite G] [ContinuousConstSMul G O] [NormalSpace O] [T1Space O]
    (h : IsOrbitChart G π) {o : O} (hv : OrbitChartV2 π o) {A : Set Z} (hA : IsClosed A)
    (hoA : π o ∉ A) : ∃ f : Z → unitInterval, Continuous f ∧ f (π o) = 0 ∧ EqOn f 1 A := by
  obtain ⟨U, hUo, hoU, hU⟩ := hv
  set U₀ := U ∩ π ⁻¹' Aᶜ with hU₀
  have hU₀o : IsOpen U₀ := hUo.inter (hA.isOpen_compl.preimage h.continuous)
  set V := ⋃ g : G, (fun x : O => g • x) ⁻¹' U₀ with hV
  have hVo : IsOpen V := isOpen_iUnion fun g => hU₀o.preimage (continuous_const_smul g)
  have hVinv : ∀ g : G, ∀ x ∈ V, g • x ∈ V := by
    intro g x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨k * g⁻¹, by simpa [mul_smul] using hk⟩
  have hoU₀ : o ∈ U₀ := ⟨hoU, hoA⟩
  have hoV : o ∈ V := mem_iUnion.2 ⟨1, by simpa using hoU₀⟩
  have himV : π '' V ⊆ π '' U₀ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg⟩ := mem_iUnion.1 hx
    exact ⟨g • x, hg, h.apply_smul g x⟩
  have hclV : closure (π '' V) ⊆ range π :=
    (closure_mono (himV.trans (image_mono inter_subset_left))).trans hU
  have hAV : ∀ x ∈ V, π x ∉ A := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := himV ⟨x, hx, rfl⟩
    rw [← hyx]
    exact hy.2
  obtain ⟨β, hβc, hβo, hβ1, hβI, hβinv⟩ := exists_invariant_urysohn (G := G) o hVo hVinv hoV
  classical
  set ψ : Z → ℝ := fun z => if hz : z ∈ range π then β hz.choose else 1 with hψ
  have hψπ : ∀ x, ψ (π x) = β x := by
    intro x
    have hz : π x ∈ range π := mem_range_self x
    simp only [hψ, dif_pos hz]
    obtain ⟨g, hg⟩ := (h.eq_iff hz.choose x).1 hz.choose_spec
    exact (hβinv g _).symm.trans (congrArg β hg)
  have hψ1 : ∀ z, z ∉ π '' V → ψ z = 1 := by
    intro z hz
    by_cases hr : z ∈ range π
    · obtain ⟨x, rfl⟩ := hr
      rw [hψπ]
      exact hβ1 x fun hx => hz ⟨x, hx, rfl⟩
    · simp only [hψ, dif_neg hr]
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ closure (π '' V)
    · obtain ⟨x, rfl⟩ := hclV hz
      have : Tendsto (ψ ∘ π) (𝓝 x) (𝓝 (ψ (π x))) := by
        rw [hψπ]
        exact (hβc.tendsto x).congr fun y => (hψπ y).symm
      exact (tendsto_map'_iff.2 this).mono_left (h.isOpenMap.nhds_le x)
    · have hev : ψ =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
        mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hz) fun z' hz' =>
          hψ1 z' fun h' => hz' (subset_closure h')
      exact continuousAt_const.congr hev.symm
  refine ⟨Set.projIcc 0 1 zero_le_one ∘ ψ, continuous_projIcc.comp hψc, ?_, ?_⟩
  · simp only [Function.comp_apply, hψπ, hβo]
    exact Set.projIcc_left _
  · intro z hz
    have : ψ z = 1 := hψ1 z fun ⟨x, hx, hxz⟩ => hAV x hx (hxz ▸ hz)
    simp only [Function.comp_apply, this, Pi.one_apply]
    exact Set.projIcc_right _

end IsOrbitChart

/-! #### A family of orbit charts covering `Z` -/

variable {ι : Type*} {G : ι → Type u} [∀ i, Group (G i)] [∀ i, Finite (G i)] {O : ι → Type v}
  [∀ i, TopologicalSpace (O i)] [∀ i, MulAction (G i) (O i)] [∀ i, ContinuousConstSMul (G i) (O i)]
  {π : ∀ i, O i → Z}

/-- **Serves Proposition 19.4.5** (p. 884), Hausdorff: if orbit charts `π_i : O_i → Z` (with
Hausdorff `O_i`; for `|S|`, the `|Ψ|` of all uniformizers) cover `Z` and satisfy (v2) everywhere,
then `Z` is Hausdorff. -/
theorem t2Space_of_orbitCharts [∀ i, T2Space (O i)] (hπ : ∀ i, IsOrbitChart (G i) (π i))
    (hcov : ∀ z : Z, ∃ i o, π i o = z) (hv : ∀ i o, OrbitChartV2 (π i) o) : T2Space Z := by
  refine t2Space_of_forall_closure_subset_t2 fun z => ?_
  obtain ⟨i, o, rfl⟩ := hcov z
  obtain ⟨U, hUo, hoU, hU⟩ := hv i o
  exact ⟨range (π i), (hπ i).isOpen_range, (hπ i).t2Space_range, π i '' U,
    (hπ i).isOpenMap _ hUo, mem_image_of_mem _ hoU, hU⟩

/-- **Proposition 19.4.5** (p. 884) in abstract form: if orbit charts `π_i : O_i → Z` with metrizable
`O_i` and finite groups cover `Z` and satisfy the properness condition (v2) everywhere, then `Z` is
Hausdorff and completely regular. -/
theorem completelyRegularSpace_of_orbitCharts [∀ i, MetrizableSpace (O i)]
    (hπ : ∀ i, IsOrbitChart (G i) (π i)) (hcov : ∀ z : Z, ∃ i o, π i o = z)
    (hv : ∀ i o, OrbitChartV2 (π i) o) : T2Space Z ∧ CompletelyRegularSpace Z := by
  refine ⟨t2Space_of_orbitCharts hπ hcov hv, ⟨fun z A hA hz => ?_⟩⟩
  obtain ⟨i, o, rfl⟩ := hcov z
  exact (hπ i).exists_urysohn (hv i o) hA hz

/-- **Theorem 19.4.6 (1)** (p. 885) in abstract form: under the hypotheses of
`completelyRegularSpace_of_orbitCharts`, a second countable `Z` is metrizable (Urysohn,
`TopologicalSpace.metrizableSpace_of_t3_secondCountable`). -/
theorem metrizableSpace_of_orbitCharts_secondCountable [∀ i, MetrizableSpace (O i)]
    [SecondCountableTopology Z] (hπ : ∀ i, IsOrbitChart (G i) (π i))
    (hcov : ∀ z : Z, ∃ i o, π i o = z) (hv : ∀ i o, OrbitChartV2 (π i) o) : MetrizableSpace Z := by
  obtain ⟨h2, h3⟩ := completelyRegularSpace_of_orbitCharts hπ hcov hv
  exact metrizableSpace_of_t3_secondCountable Z

/-- **Theorem 19.4.6 (2)** (p. 885) in abstract form: under the hypotheses of
`completelyRegularSpace_of_orbitCharts`, a paracompact `Z` is metrizable (Smirnov,
`Polyfold.metrizableSpace_of_locally`, with the metrizable open sets `π_i(O_i)`). -/
theorem metrizableSpace_of_orbitCharts_paracompact [∀ i, MetrizableSpace (O i)]
    [ParacompactSpace Z] (hπ : ∀ i, IsOrbitChart (G i) (π i))
    (hcov : ∀ z : Z, ∃ i o, π i o = z) (hv : ∀ i o, OrbitChartV2 (π i) o) : MetrizableSpace Z := by
  have := t2Space_of_orbitCharts hπ hcov hv
  refine metrizableSpace_of_locally fun z => ?_
  obtain ⟨i, o, rfl⟩ := hcov z
  exact ⟨range (π i), (hπ i).isOpen_range, mem_range_self o, (hπ i).metrizableSpace_range⟩

omit [∀ i, Finite (G i)] [∀ i, ContinuousConstSMul (G i) (O i)] in
/-- **Proposition 19.4.7** (p. 885), (1) ⇒ (2), in abstract form: a metrizable `Z` is paracompact and
every orbit chart into it satisfies (v2) everywhere. -/
theorem paracompact_and_orbitChartV2_of_metrizableSpace [MetrizableSpace Z]
    (hπ : ∀ i, IsOrbitChart (G i) (π i)) :
    ParacompactSpace Z ∧ ∀ i o, OrbitChartV2 (π i) o :=
  ⟨paracompactSpace_of_metrizableSpace Z, fun i o => (hπ i).orbitChartV2_of_regularSpace o⟩

end CompletelyRegular

/-! ### Witnesses: the hypotheses hold in a non-degenerate case -/

section Witness

/-- The quotient map `O → O/G` of a group action is an orbit chart. -/
theorem isOrbitChart_quotientMk {G : Type u} [Group G] {O : Type v} [TopologicalSpace O]
    [MulAction G O] [ContinuousConstSMul G O] :
    IsOrbitChart G (Quotient.mk (MulAction.orbitRel G O)) where
  continuous := continuous_quot_mk
  isOpenMap := MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  eq_iff x y := by
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩,
      fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩⟩

/-- **Witness for the orbit-chart hypotheses** (of `completelyRegularSpace_of_orbitCharts` and
Theorem 19.4.6 in abstract form) with a non-trivial action: `ℤ/2 = ℤˣ` acting on `ℝ` by `x ↦ ±x`,
`π : ℝ → ℝ/ℤˣ`; `π` is an orbit chart, covers, and satisfies (v2) at every point. -/
theorem orbitCharts_witness_reflection :
    IsOrbitChart ℤˣ (Quotient.mk (MulAction.orbitRel ℤˣ ℝ)) ∧
      (∀ z : MulAction.orbitRel.Quotient ℤˣ ℝ, ∃ o : ℝ, Quotient.mk _ o = z) ∧
      (∀ o : ℝ, OrbitChartV2 (Quotient.mk (MulAction.orbitRel ℤˣ ℝ)) o) ∧
      (-1 : ℤˣ) • (1 : ℝ) ≠ 1 := by
  have := metrizableSpace_orbitRel_quotient_finite (G := ℤˣ) (U := ℝ) continuous_const_smul
  refine ⟨isOrbitChart_quotientMk, Quotient.exists_rep, fun o =>
    isOrbitChart_quotientMk.orbitChartV2_of_regularSpace o, ?_⟩
  rw [Units.neg_smul, one_smul]
  norm_num

/-- **Witness for the sheet hypothesis** of `paracompactSpace_of_isLocalHomeomorph_of_finiteSheets`
with two sheets over every point: `Prod.snd : ℤˣ × ℝ → ℝ`, the sheets `{±1} × ℝ`. -/
theorem finiteSheets_witness_snd (y : ℝ) :
    ∃ V : Set ℝ, IsOpen V ∧ y ∈ V ∧ ∃ S : Set (Set (ℤˣ × ℝ)), S.Finite ∧
      (∀ U ∈ S, IsOpen U ∧ InjOn Prod.snd U ∧ y ∈ Prod.snd '' U) ∧ Prod.snd ⁻¹' V ⊆ ⋃₀ S ∧
      S.ncard = 2 := by
  refine ⟨univ, isOpen_univ, mem_univ y, range fun i : ℤˣ => {i} ×ˢ univ, finite_range _, ?_, ?_,
    ?_⟩
  · rintro _ ⟨i, rfl⟩
    refine ⟨(isOpen_discrete _).prod isOpen_univ, fun p hp q hq hpq => Prod.ext ?_ hpq,
      ⟨(i, y), ⟨rfl, mem_univ _⟩, rfl⟩⟩
    exact (hp.1 : p.1 = i).trans (hq.1 : q.1 = i).symm
  · intro p _
    exact ⟨{p.1} ×ˢ univ, ⟨p.1, rfl⟩, rfl, mem_univ _⟩
  · rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_units_int]
    intro i j hij
    have hij' : ({i} ×ˢ univ : Set (ℤˣ × ℝ)) = {j} ×ˢ univ := hij
    have : (i, (0 : ℝ)) ∈ ({j} ×ˢ univ : Set (ℤˣ × ℝ)) := hij' ▸ ⟨rfl, mem_univ _⟩
    exact this.1

end Witness

end Chapter19

end Polyfold
