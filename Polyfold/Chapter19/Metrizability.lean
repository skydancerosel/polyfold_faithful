import Polyfold.Chapter19.NaturalTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.4 "Metrizability Criteria" (pp. 879–885): **Definition 19.4.1** (the properness conditions
(v1), (v2), (v3)), **Proposition 19.4.2**, **Lemma 19.4.3**, **Proposition 19.4.4**,
**Proposition 19.4.5**, **Theorem 19.4.6**, **Proposition 19.4.7** and **Corollary 19.4.8**.
(The basic constructions showing that 19.4.2 and 19.4.3 do not hold as we read them, and the
witnesses, are in `MetrizabilityExamples`.)  Numbers and pages are the 2021 text's.

# Metrizability criteria for basic constructions

## The text, paraphrased

(19.4.1) For a basic construction `(F, 𝓕)` of `S`: (v1) for `Ψ ∈ F(α)` and `o ∈ O` there is an open
`U(o)` such that for every `Ψ' ∈ F(α')` every sequence `h_k ∈ M(Ψ, Ψ')` with `s(h_k) ∈ U` and
`t(h_k)` convergent in `O'` has a convergent subsequence; (v2) for every `Ψ` and `o` an open `U(o)`
with `cl_{|S|} |Ψ(U(o))| ⊂ |Ψ(O)|`; (v3) for every `Ψ` and `o` an open `U(o)` such that for
`q_k ∈ U(o)` the convergence of `|Ψ(q_k)|` to some `z` implies that a subsequence of `q_k` converges
to an element of `cl_O(U(o))`.  (19.4.2) The three are equivalent ("the properness condition").
(19.4.3) Under properness, for `o ∈ O` there are finitely many `h_i ∈ M(Ψ, Ψ')` and open
`U(o)`, `U(h_i)` with `s : U(h_i) → U(o)` a homeomorphism and `s(h) ∈ U(o) ⇒ h ∈ ⋃ U(h_i)`.
(19.4.4) Under properness every `T_{Ψ,Ψ'}` is metrizable (paracompact by 19.4.3, then
Nagata–Smirnov).  (19.4.5) Under properness `T` is Hausdorff and completely regular.
(19.4.6) Properness and second countability, or properness and paracompactness, imply that `T`
is metrizable.  (19.4.7) `T` is metrizable iff properness holds and `T` is paracompact.
(19.4.8) If `T` is metrizable, so are all `T_{Ψ,Ψ'}`.

## What is formalized

* `BasicConstruction.PropernessV1`, `PropernessV2 hB`, `PropernessV3 hB` (**Definition 19.4.1**,
  as printed) and `PropernessV3Lim hB` ((v3) where the limit `q` of the subsequence satisfies
  `|Ψ(q)| = z`); "the properness condition" is (v2) (equivalently (v1) or (v3Lim)).
* **Proposition 19.4.2**: `proposition_19_4_2_one_iff_two` ((v1) ⇔ (v2)),
  `proposition_19_4_2_two_three` ((v2) ⇒ (v3)), `proposition_19_4_2` ((v1) ⇔ (v2) ⇔ (v3Lim)),
  `proposition_19_4_2_three_two_hyp` ((v3) ⇒ (v2) when `T` is Hausdorff), the steps
  `propernessV3Lim_of_v1`, `propernessV2_of_v3Lim`, `propernessV3Lim_of_v2`,
  `propernessV1_of_v3Lim`; and `propernessV3_of_locallyCompactSpace` ((v3) as printed holds for
  every basic construction with locally compact domains).  `proposition_19_4_2_v3_without_limit`
  (`MetrizabilityExamples`): (v3) without the limit in the fibre ⇏ (v2).
* The sequence lemma behind 19.4.2 (3) ⇒ (1) and 19.4.3:
  `TransitionData.exists_tendsto_subseq_of_tendsto_src` (if `s(h_k) → s(a)` for some `a`, a
  subsequence of `h_k` converges), `TransitionData.exists_nbhd_eq_map`,
  `TransitionData.metrizableSpace`.
* **Lemma 19.4.3**: `lemma_19_4_3_hyp` (for `o` the source of some element of `M(Ψ, Ψ')`; no
  properness needed); `not_lemma_19_4_3` (`MetrizabilityExamples`).
* **Proposition 19.4.4** `proposition_19_4_4`, and `metrizableSpace_M` (without properness).
* **Proposition 19.4.5** `proposition_19_4_5`, **Theorem 19.4.6** `theorem_19_4_6_one`,
  `theorem_19_4_6_two`, **Proposition 19.4.7** `proposition_19_4_7`, **Corollary 19.4.8**
  `corollary_19_4_8`; `metrizableSpace_natTop_of_surjective` (a uniformizer whose `|Ψ|` is onto
  makes `T` metrizable; used for the witnesses).

## Readings

* `hB : HasClassUniformizers` (`F(α) ≠ ∅`, the standing reading of §17.1) is assumed wherever `T`
  occurs (it is what makes `T` a topology, Theorem 19.2.2 and `theorem_19_2_2_empty_family`).
  "Every uniformizer `Ψ`" in (v2), (v3) is every `Ψ ∈ F(α)`.  In (v1) the neighbourhood `U(o)`
  is chosen before `Ψ'`, as printed; (v1) does not involve `T`.
* (v3) is read with the limit `q` of the subsequence satisfying `|Ψ(q)| = z` (`PropernessV3Lim`):
  the text's step (3) ⇒ (1) considers "the morphisms with source `Ψ(q)` and target in
  `Ψ'(O')`", which needs `q` over `z`, and it is what the proof of (2) ⇒ (3) produces.  Under this
  reading the three conditions are equivalent (`proposition_19_4_2`).  Without the limit in the
  fibre (`PropernessV3`: the subsequence converges to some point of `cl_O(U(o))`), (v3) holds for
  every basic construction with locally compact `O` (`propernessV3_of_locallyCompactSpace`), also
  for the non-Hausdorff `gluedBasic` of Remark 19.2.3, where (v2) does not hold
  (`proposition_19_4_2_v3_without_limit`); it is equivalent to the others once `T` is
  Hausdorff.
* Lemma 19.4.3: when `o` is the source of an element of `M(Ψ, Ψ')` the statement holds without
  properness (`lemma_19_4_3_hyp`; the text's proof uses properness only through the sequence
  lemma, which does not need it).  When no element has source `o` but `o` is a limit of sources,
  no `U(o)` with (1), (2) exists, also under properness (`not_lemma_19_4_3`, a uniformizer
  `t ↦ eᵗ` next to the identity of `ℝ`; the proof's "fix, if it exists, `h₀`" leaves this case
  open).  "`s : U(h_i) → U(o)` is a homeomorphism" is read as: `s` restricted to `U(h_i)` is an
  open embedding with image `U(o)`.
* Proposition 19.4.4: `M(Ψ, Ψ')` is metrizable for every basic construction
  (`metrizableSpace_M`): `s` is a local homeomorphism onto the open set `s(M(Ψ, Ψ'))` of the
  metrizable `O`, with finitely many sheets over every point of it (`lemma_19_4_3_hyp`), so
  `M(Ψ, Ψ')` is paracompact, and Hausdorff and locally metrizable (Theorem 19.3.3); Smirnov's
  theorem.  `proposition_19_4_4` keeps the printed hypothesis.
* Proposition 19.4.5: Hausdorffness is derived from (v2) (the text derives it from (v1); they are
  equivalent by 19.4.2).  The averaging step "perhaps using an averaging procedure, we may assume
  that `β` is invariant" is done for a `β` vanishing on the orbit `G ō` (Chapter 19
  `TopologyLemmas.exists_invariant_urysohn`): averaging a `β` with only `β(ō) = 0` need not keep
  `β(ō) = 0`.
* Theorem 19.4.6 (2) and Proposition 19.4.7 use Smirnov's metrization theorem
  (`Polyfold.metrizableSpace_of_locally`, Chapter 2); (1) uses Urysohn's (Mathlib).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter TopologicalSpace

noncomputable section

namespace Polyfold

universe u v w

/-! ### Abstract lemmas -/

namespace Chapter19

section Abstract

variable {G : Type u} [Group G] {O : Type v} [TopologicalSpace O] [MulAction G O]
  {Z : Type w} [TopologicalSpace Z]

/-- **Properness condition (v3) with the limit in the fibre** at `o`, for a map `π : O → Z`: an
open `U ∋ o` such that for `q_k ∈ U` with `π(q_k) → z`, a subsequence of `q_k` converges to a
point `p ∈ cl_O(U)` with `π(p) = z`. -/
def OrbitChartV3Lim (π : O → Z) (o : O) : Prop :=
  ∃ U : Set O, IsOpen U ∧ o ∈ U ∧ ∀ q : ℕ → O, (∀ k, q k ∈ U) → ∀ z : Z,
    Tendsto (π ∘ q) atTop (𝓝 z) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p ∈ closure U, Tendsto (q ∘ φ) atTop (𝓝 p) ∧ π p = z

theorem OrbitChartV3Lim.orbitChartV3 {π : O → Z} {o : O} (h : OrbitChartV3Lim π o) :
    OrbitChartV3 π o := by
  obtain ⟨U, hUo, hoU, hU⟩ := h
  refine ⟨U, hUo, hoU, fun q hq z hz => ?_⟩
  obtain ⟨φ, hφ, p, hp, hpl, -⟩ := hU q hq z hz
  exact ⟨φ, hφ, p, hp, hpl⟩

namespace IsOrbitChart

variable {π : O → Z}

/-- **(v2) ⇒ (v3Lim) for one `U`** (the proof of Proposition 19.4.2, (2) ⇒ (3), p. 880): if
`cl π(U) ⊆ π(O)` and `π(q_k) → z` with `q_k ∈ U`, then `z = π(q̄)`, and for one `g` the point
`q̄` is a cluster point of `g q_k`; a subsequence of `q_k` converges to `g⁻¹ q̄`, and
`π(g⁻¹ q̄) = z`. -/
theorem tendsto_subseq_of_closure_subset_lim [Finite G] [ContinuousConstSMul G O]
    [FirstCountableTopology O] (h : IsOrbitChart G π) {U : Set O}
    (hU : closure (π '' U) ⊆ range π) (q : ℕ → O) (hq : ∀ k, q k ∈ U) (z : Z)
    (hz : Tendsto (π ∘ q) atTop (𝓝 z)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p ∈ closure U, Tendsto (q ∘ φ) atTop (𝓝 p) ∧ π p = z := by
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
  have hconv : Tendsto (q ∘ φ) atTop (𝓝 (g⁻¹ • q₀)) := by
    have := ((continuous_const_smul g⁻¹).tendsto q₀).comp hlim
    simpa [Function.comp_def, inv_smul_smul] using this
  exact ⟨φ, hφ, g⁻¹ • q₀, mem_closure_of_tendsto hconv
    (Eventually.of_forall fun k => hq (φ k)), hconv, h.apply_smul _ _⟩

/-- (v2) at `o` implies (v3Lim) at `o` (same `U`). -/
theorem orbitChartV3Lim_of_v2 [Finite G] [ContinuousConstSMul G O] [FirstCountableTopology O]
    (h : IsOrbitChart G π) {o : O} (hv : OrbitChartV2 π o) : OrbitChartV3Lim π o := by
  obtain ⟨U, hUo, hoU, hU⟩ := hv
  exact ⟨U, hUo, hoU, h.tendsto_subseq_of_closure_subset_lim hU⟩

end IsOrbitChart

/-- (v3Lim) at `o` implies (v2) at `o` (same `U`), for a Fréchet–Urysohn `Z` (for instance a first
countable one, as `|S|` is by Theorem 19.2.2 (4)). -/
theorem orbitChartV2_of_v3Lim [FrechetUrysohnSpace Z] {π : O → Z} {o : O}
    (hv : OrbitChartV3Lim π o) : OrbitChartV2 π o := by
  obtain ⟨U, hUo, hoU, hU⟩ := hv
  refine ⟨U, hUo, hoU, fun z hz => ?_⟩
  obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 hz
  choose q hqU hqx using hx
  have hqz : Tendsto (π ∘ q) atTop (𝓝 z) := by
    simpa [Function.comp_def, hqx] using hxz
  obtain ⟨φ, -, p, -, -, hp⟩ := hU q hqU z hqz
  exact ⟨p, hp⟩

/-- **(v3) as printed holds for locally compact `O`**, for every map `π`: take `U` the interior of
a compact neighbourhood of `o`; every sequence in `U` has a subsequence converging in `cl_O(U)`. -/
theorem orbitChartV3_of_locallyCompactSpace [LocallyCompactSpace O] [FirstCountableTopology O]
    (π : O → Z) (o : O) : OrbitChartV3 π o := by
  obtain ⟨K, hK, hoK⟩ := exists_compact_mem_nhds o
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.2 hoK, fun q hq _ _ => ?_⟩
  obtain ⟨p, -, φ, hφ, hp⟩ := hK.tendsto_subseq fun k => interior_subset (hq k)
  exact ⟨φ, hφ, p, mem_closure_of_tendsto hp (Eventually.of_forall fun k => hq (φ k)), hp⟩

end Abstract

/-- The corestriction of a local homeomorphism to a set containing its range is a local
homeomorphism. -/
theorem isLocalHomeomorph_codRestrict {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsLocalHomeomorph f) {s : Set Y}
    (hfs : ∀ x, f x ∈ s) : IsLocalHomeomorph (s.codRestrict f hfs) := by
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun x => ?_
  obtain ⟨U, hU, he⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.1 hf x
  refine ⟨U, hU, IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_⟩
  · exact he.continuous.codRestrict _
  · intro a b hab
    exact he.injective (congrArg Subtype.val hab)
  · intro W hW
    have h1 : IsOpen (U.domRestrict f '' W) := he.isOpenMap W hW
    have h2 : (U.domRestrict (s.codRestrict f hfs)) '' W =
        Subtype.val ⁻¹' (U.domRestrict f '' W) := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, hwy⟩
        exact ⟨w, hw, Subtype.ext hwy⟩
    rw [h2]
    exact h1.preimage continuous_subtype_val

end Chapter19

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

/-! ### The sequence lemma and the sheets over a point -/

namespace UniformizerConstruction.TransitionData

open GroupoidStr (TransitionSet)
open GroupoidStr.TransitionSet (src_comp tgt_comp)

variable {U : C.UniformizerConstruction} (F : U.TransitionData)

/-- **The sequence lemma** (the end of the proof of 2021 Proposition 19.4.2, (3) ⇒ (1), p. 880, and
the "easy exercise" in the proof of Lemma 19.4.3, p. 882): if `s(h_k) → s(a)` for some
`a ∈ M(Ψ, Ψ')`, a subsequence of `h_k` converges to an element with source `s(a)`.  For large `k`,
`h_k` and `F_a(s(h_k))` have the same source, so `h_k = m(Ψ̄'(g_k, t(F_a(s(h_k)))), F_a(s(h_k)))`;
a subsequence has `g_k = g` constant, and then `h_k = F_{m(Ψ̄'(g, t(a)), a)}(s(h_k))` by (E) and the
special form of (A).  No properness is used. -/
theorem exists_tendsto_subseq_of_tendsto_src {Ψ Ψ' : U.Unif} (h : ℕ → F.Tr Ψ Ψ')
    (a : Ψ.1.Trans Ψ'.1)
    (hs : Tendsto (fun k => (h k : Ψ.1.Trans Ψ'.1).src) atTop (𝓝 a.src)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : F.Tr Ψ Ψ', (m : Ψ.1.Trans Ψ'.1).src = a.src ∧
      Tendsto (h ∘ φ) atTop (𝓝 m) := by
  classical
  set hg : Ψ'.1.G → Ψ'.1.Trans Ψ'.1 := fun g => Ψ'.1.hat (g, a.tgt) with hhg
  have hgs : ∀ g, (hg g).src = a.tgt := fun _ => rfl
  set N : Set Ψ.1.O := ⋂ g, F.mulNbhdDom a (hg g) (hgs g) with hN
  have hNo : IsOpen N := isOpen_iInter_of_finite fun g => F.isOpen_mulNbhdDom _ _ _
  have haN : a.src ∈ N := mem_iInter.2 fun g => F.src_mem_mulNbhdDom _ _ _
  -- for `q_k ∈ N`, `h_k` is in the `G'`-orbit of `F_a(q_k)`
  have hrep : ∀ k, (h k : Ψ.1.Trans Ψ'.1).src ∈ N → ∃ g : Ψ'.1.G,
      (h k : Ψ.1.Trans Ψ'.1) = TransitionSet.comp
        (Ψ'.1.hat (g, (F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src).tgt))
        (F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src)
        (by simp [(F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src).tgt_mor]) := by
    intro k hk
    set b := F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src
    have hbs : b.src = (h k : Ψ.1.Trans Ψ'.1).src :=
      F.src_map Ψ Ψ' a _ (mem_iInter.1 hk 1).2.1
    set g := (Ψ.1.fiberEquiv b).symm ⟨(h k : Ψ.1.Trans Ψ'.1), hbs.symm⟩
    have := congrArg Subtype.val ((Ψ.1.fiberEquiv b).apply_symm_apply
      ⟨(h k : Ψ.1.Trans Ψ'.1), hbs.symm⟩)
    exact ⟨g, this.symm⟩
  have hev : ∀ᶠ k in atTop, (h k : Ψ.1.Trans Ψ'.1).src ∈ N := hs (hNo.mem_nhds haN)
  have hfreq : ∃ g : Ψ'.1.G, ∃ᶠ k in atTop, (h k : Ψ.1.Trans Ψ'.1).src ∈ N ∧
      (h k : Ψ.1.Trans Ψ'.1) = TransitionSet.comp
        (Ψ'.1.hat (g, (F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src).tgt))
        (F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src)
        (by simp [(F.map Ψ Ψ' a (h k : Ψ.1.Trans Ψ'.1).src).tgt_mor]) := by
    by_contra hno
    push Not at hno
    have hall := Filter.eventually_all.2 fun g => (hno g)
    obtain ⟨k, hk, hk'⟩ := (hev.and hall).exists
    obtain ⟨g, hg'⟩ := hrep k hk
    exact hk' g hk hg'
  obtain ⟨g, hfr⟩ := hfreq
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hfr
  -- the limit
  set m : Ψ.1.Trans Ψ'.1 := TransitionSet.comp (hg g) a
    (TransitionSet.mor_composable_of_src_eq_tgt (hgs g)) with hm
  have hms : m.src = a.src := rfl
  have hmd : a.src ∈ F.dom Ψ Ψ' m := (mem_iInter.1 haN g).1
  have heq : ∀ n, h (φ n) = F.toTr (F.map Ψ Ψ' m (h (φ n) : Ψ.1.Trans Ψ'.1).src) := by
    intro n
    obtain ⟨hk, hk'⟩ := hP n
    have hkN := mem_iInter.1 hk g
    refine hk'.trans ?_
    rw [← F.multiplication Ψ Ψ' Ψ' a (hg g) (hgs g) _ hkN.2.1 hkN.2.2 hkN.1]
    exact comp_congr (F.map_hat Ψ' (g, a.tgt) _ hkN.2.2).symm rfl _ _
  refine ⟨φ, hφ, F.toTr m, hms, ?_⟩
  have hc := (F.continuousAt_map Ψ Ψ' m hmd).tendsto.comp (hs.comp hφ.tendsto_atTop)
  have hm' : F.toTr (F.map Ψ Ψ' m a.src) = F.toTr m := by
    rw [← hms]
    exact F.map_src Ψ Ψ' m
  rw [hm'] at hc
  refine hc.congr fun n => ?_
  exact (heq n).symm

/-- **The sheets over a source point** (Lemma 19.4.3 (2), p. 881): for `a ∈ M(Ψ, Ψ')` there is an
open `N ∋ s(a)` such that every `x` with `s(x) ∈ N` is `F_b(s(x))` for an element `b` with
`s(b) = s(a)` and `s(x) ∈ V(s(b))`. -/
theorem exists_nbhd_eq_map {Ψ Ψ' : U.Unif} (a : Ψ.1.Trans Ψ'.1) :
    ∃ N : Set Ψ.1.O, IsOpen N ∧ a.src ∈ N ∧ ∀ x : Ψ.1.Trans Ψ'.1, x.src ∈ N →
      ∃ b : Ψ.1.Trans Ψ'.1, b.src = a.src ∧ x.src ∈ F.dom Ψ Ψ' b ∧ x = F.map Ψ Ψ' b x.src := by
  have := Ψ.1.P.metrizableSpace
  set W : Set (F.Tr Ψ Ψ') := ⋃ b : {b : Ψ.1.Trans Ψ'.1 // b.src = a.src},
    F.map Ψ Ψ' b.1 '' F.dom Ψ Ψ' b.1 with hW
  have hmem : ∀ x : Ψ.1.Trans Ψ'.1, F.toTr x ∈ W → ∃ b : Ψ.1.Trans Ψ'.1, b.src = a.src ∧
      x.src ∈ F.dom Ψ Ψ' b ∧ x = F.map Ψ Ψ' b x.src := by
    intro x hx
    obtain ⟨⟨b, hb⟩, q, hq, rfl⟩ := mem_iUnion.1 hx
    refine ⟨b, hb, ?_, ?_⟩
    · rw [F.src_map Ψ Ψ' b q hq]
      exact hq
    · rw [F.src_map Ψ Ψ' b q hq]
  suffices hN : ∃ N ∈ 𝓝 a.src, ∀ x : Ψ.1.Trans Ψ'.1, x.src ∈ N → F.toTr x ∈ W by
    obtain ⟨N, hN, hNW⟩ := hN
    obtain ⟨N', hN'N, hN'o, haN'⟩ := mem_nhds_iff.1 hN
    exact ⟨N', hN'o, haN', fun x hx => hmem x (hNW x (hN'N hx))⟩
  by_contra hno
  push Not at hno
  obtain ⟨V, hV⟩ := (𝓝 a.src).exists_antitone_basis
  choose x hxV hxW using fun j => hno (V j) (hV.mem j)
  obtain ⟨φ, -, m, hms, hm⟩ := F.exists_tendsto_subseq_of_tendsto_src (fun j => F.toTr (x j)) a
    (hV.tendsto hxV)
  have hWm : W ∈ 𝓝 m := by
    refine mem_of_superset ((F.isOpen_image_map Ψ Ψ' m (F.isOpen_dom _ _ _) subset_rfl).mem_nhds
      (F.mem_sheet_target Ψ Ψ' m)) ?_
    exact subset_iUnion_of_subset ⟨m, hms⟩ subset_rfl
  obtain ⟨n, hn⟩ := (hm.eventually_mem hWm).exists
  exact hxW (φ n) hn

/-- **`M(Ψ, Ψ')` with `T^F_{Ψ,Ψ'}` is metrizable**, for all transition data (serves Proposition
19.4.4): `s` is a local homeomorphism onto the open set `s(M(Ψ, Ψ'))` of the metrizable `O`, with
finitely many sheets over a neighbourhood of every point of it (`exists_nbhd_eq_map`); so
`M(Ψ, Ψ')` is paracompact; it is Hausdorff and locally metrizable; Smirnov's theorem
(`Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets`). -/
theorem metrizableSpace (Ψ Ψ' : U.Unif) : MetrizableSpace (F.Tr Ψ Ψ') := by
  have := Ψ.1.P.metrizableSpace
  have := F.t2Space Ψ Ψ'
  set s : F.Tr Ψ Ψ' → Ψ.1.O := fun a => (a : Ψ.1.Trans Ψ'.1).src with hs
  have hloc : IsLocalHomeomorph s := F.isLocalHomeomorph_src Ψ Ψ'
  have hloc' := Chapter19.isLocalHomeomorph_codRestrict hloc (s := range s) mem_range_self
  refine Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets hloc' fun y => ?_
  rcases y with ⟨_, a, rfl⟩
  obtain ⟨N, hNo, haN, hNx⟩ := F.exists_nbhd_eq_map a
  have hfin := Ψ.1.finite_fiber (Ψ' := Ψ'.1) (a : Ψ.1.Trans Ψ'.1).src
  set Uo : Set Ψ.1.O := N ∩ ⋂ b ∈ {b : Ψ.1.Trans Ψ'.1 | b.src = (a : Ψ.1.Trans Ψ'.1).src},
    F.dom Ψ Ψ' b with hUo
  have hUoo : IsOpen Uo := hNo.inter (hfin.isOpen_biInter fun b _ => F.isOpen_dom _ _ _)
  have haUo : (a : Ψ.1.Trans Ψ'.1).src ∈ Uo :=
    ⟨haN, mem_iInter₂.2 fun b hb => (hb : b.src = _) ▸ F.mem_dom Ψ Ψ' b⟩
  refine ⟨Subtype.val ⁻¹' Uo, hUoo.preimage continuous_subtype_val, haUo,
    (fun b => (F.map Ψ Ψ' b '' Uo : Set (F.Tr Ψ Ψ'))) '' {b | b.src = (a : Ψ.1.Trans Ψ'.1).src},
    hfin.image _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hUob : Uo ⊆ F.dom Ψ Ψ' b := fun q hq => mem_iInter₂.1 hq.2 b hb
    refine ⟨F.isOpen_image_map Ψ Ψ' b hUoo hUob, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ hqq
      have := congrArg Subtype.val hqq
      change (F.map Ψ Ψ' b q).src = (F.map Ψ Ψ' b q').src at this
      rw [F.src_map Ψ Ψ' b q (hUob hq), F.src_map Ψ Ψ' b q' (hUob hq')] at this
      rw [this]
    · refine ⟨F.toTr b, ⟨b.src, hb ▸ haUo, F.map_src Ψ Ψ' b⟩, ?_⟩
      exact Subtype.ext hb
  · intro x hx
    obtain ⟨b, hb, -, hxe⟩ := hNx x hx.1
    exact ⟨_, ⟨b, hb, rfl⟩, (x : Ψ.1.Trans Ψ'.1).src, hx, hxe.symm⟩

end UniformizerConstruction.TransitionData

/-- The group of a uniformizer acts by homeomorphisms. -/
theorem Uniformizer.continuousConstSMul (Ψ : C.Uniformizer) : ContinuousConstSMul Ψ.G Ψ.O :=
  ⟨EpGroupoid.Examples.action_continuous_smul Ψ.smooth_smul⟩

/-- An element `(o, φ, o')` of `M(Ψ, Ψ')` gives `|Ψ(o)| = |Ψ'(o')|`. -/
theorem π_obj_src_eq_π_obj_tgt {Ψ Ψ' : C.Uniformizer} (a : Ψ.Trans Ψ') :
    C.π (Ψ.obj a.src) = C.π (Ψ'.obj a.tgt) :=
  (C.π_eq_π_iff).2 ⟨a.mor, a.src_mor, a.tgt_mor⟩

/-! ### Definition 19.4.1 -/

namespace BasicConstruction

open GroupoidStr (TransitionSet)

variable (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers)

/-- **2021 Definition 19.4.1 (1), p. 879**: the **properness condition (v1)**: for every `Ψ` in `F`
and `o ∈ O` there is an open `U(o) ∋ o` such that for every `Ψ'` in `F` every sequence `h_k` in
`M(Ψ, Ψ')` with `s(h_k) ∈ U(o)` and `t(h_k)` convergent in `O'` has a convergent subsequence. -/
def PropernessV1 : Prop :=
  ∀ (Ψ : B.U.Unif) (o : Ψ.1.O), ∃ U : Set Ψ.1.O, IsOpen U ∧ o ∈ U ∧
    ∀ (Ψ' : B.U.Unif) (h : ℕ → B.M Ψ Ψ'), (∀ k, (h k : Ψ.1.Trans Ψ'.1).src ∈ U) →
      ∀ p : Ψ'.1.O, Tendsto (fun k => (h k : Ψ.1.Trans Ψ'.1).tgt) atTop (𝓝 p) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : B.M Ψ Ψ', Tendsto (h ∘ φ) atTop (𝓝 m)

/-- **2021 Definition 19.4.1 (2), p. 879**: the **properness condition (v2)**: for every `Ψ` in `F`
and `o ∈ O` there is an open `U(o) ∋ o` with `cl_{|S|} |Ψ(U(o))| ⊂ |Ψ(O)|` (closure in `T`). -/
def PropernessV2 : Prop :=
  ∀ (Ψ : B.U.Unif) (o : Ψ.1.O),
    @Chapter19.OrbitChartV2 Ψ.1.O _ C.OrbitSpace (B.natTop hB) (fun q => C.π (Ψ.1.obj q)) o

/-- **2021 Definition 19.4.1 (3), p. 879**: the **properness condition (v3)**, as printed: for every
`Ψ` in `F` and `o ∈ O` there is an open `U(o) ∋ o` such that for `q_k ∈ U(o)` the convergence of
`|Ψ(q_k)|` in `T` to some `z` implies that a subsequence of `q_k` converges to an element of
`cl_O(U(o))`. -/
def PropernessV3 : Prop :=
  ∀ (Ψ : B.U.Unif) (o : Ψ.1.O),
    @Chapter19.OrbitChartV3 Ψ.1.O _ C.OrbitSpace (B.natTop hB) (fun q => C.π (Ψ.1.obj q)) o

/-- **(v3) with the limit in the fibre** (Definition 19.4.1 (3) with "converges to an element `q`
of `cl_O(U(o))` with `|Ψ(q)| = z`"). -/
def PropernessV3Lim : Prop :=
  ∀ (Ψ : B.U.Unif) (o : Ψ.1.O),
    @Chapter19.OrbitChartV3Lim Ψ.1.O _ C.OrbitSpace (B.natTop hB) (fun q => C.π (Ψ.1.obj q)) o

/-- `q ↦ |Ψ(q)|` is an orbit chart for every `Ψ` in `F` (Theorem 19.2.2 (3)). -/
theorem isOrbitChart_unif (Ψ : B.U.Unif) :
    @Chapter19.IsOrbitChart Ψ.1.G _ Ψ.1.O _ _ C.OrbitSpace (B.natTop hB)
      (fun q => C.π (Ψ.1.obj q)) :=
  B.isOrbitChart hB Ψ.2.choose_spec

/-! ### Proposition 19.4.2 -/

/-- **2021 Proposition 19.4.2, (1) ⇒ (3) with the limit in the fibre** (p. 880, the argument of
(1) ⇒ (2)): for `q_k ∈ U(o)` with `|Ψ(q_k)| → z = |Ψ'(ō')|`, choose `p_k → ō'` with
`|Ψ'(p_k)| = |Ψ(q_k)|` along a subsequence, elements `h_k = (q_k, φ_k, p_k)`, and apply (v1). -/
theorem propernessV3Lim_of_v1 (hv : B.PropernessV1) : B.PropernessV3Lim hB := by
  let _inst := B.natTop hB
  intro Ψ o
  obtain ⟨U, hUo, hoU, hU⟩ := hv Ψ o
  refine ⟨U, hUo, hoU, fun q hq z hz => ?_⟩
  obtain ⟨α', hα', Ψ', hΨ'⟩ := hB z
  obtain ⟨o', ho'⟩ := B.U.isAt α' Ψ' hΨ'
  let P' : B.U.Unif := ⟨Ψ', α', hΨ'⟩
  have hπ' := B.isOrbitChart hB hΨ'
  have := Ψ'.P.metrizableSpace
  obtain ⟨V, hV⟩ := (𝓝 o').exists_antitone_basis
  have hz' : C.π (Ψ'.obj o') = z := by rw [ho', hα']
  have hev : ∀ j, ∀ᶠ k in atTop, C.π (Ψ.1.obj (q k)) ∈ (fun y => C.π (Ψ'.obj y)) '' V j := by
    intro j
    have := hπ'.isOpenMap.image_mem_nhds (hV.mem j)
    rw [hz'] at this
    exact hz.eventually_mem this
  obtain ⟨φ, hφ, hφV⟩ := Filter.extraction_forall_of_eventually hev
  choose p hpV hp using hφV
  have hmor : ∀ j, C.toGroupoidStr.Isomorphic (Ψ.1.obj (q (φ j))) (Ψ'.obj (p j)) := fun j =>
    (C.π_eq_π_iff).1 (hp j).symm
  choose μ hμs hμt using hmor
  let h : ℕ → B.M Ψ P' := fun j => (⟨q (φ j), μ j, p j, hμs j, hμt j⟩ : Ψ.1.Trans P'.1)
  have hpo : Tendsto p atTop (𝓝 o') := hV.tendsto hpV
  obtain ⟨ψ, hψ, m, hm⟩ := hU P' h (fun j => hq (φ j)) o' hpo
  have hsrc : Tendsto (q ∘ (φ ∘ ψ)) atTop (𝓝 (m : Ψ.1.Trans Ψ').src) :=
    ((B.rep.continuous_src Ψ P').tendsto m).comp hm
  have htgt : Tendsto (p ∘ ψ) atTop (𝓝 (m : Ψ.1.Trans Ψ').tgt) :=
    ((B.rep.isLocalHomeomorph_tgt Ψ P').continuous.tendsto m).comp hm
  have hmt : (m : Ψ.1.Trans Ψ').tgt = o' :=
    tendsto_nhds_unique htgt (hpo.comp hψ.tendsto_atTop)
  refine ⟨φ ∘ ψ, hφ.comp hψ, (m : Ψ.1.Trans Ψ').src,
    mem_closure_of_tendsto hsrc (Eventually.of_forall fun n => hq _), hsrc, ?_⟩
  exact (π_obj_src_eq_π_obj_tgt (m : Ψ.1.Trans P'.1)).trans
    ((congrArg (fun y => C.π (Ψ'.obj y)) hmt).trans hz')

/-- **(3) ⇒ (2) with the limit in the fibre** (Proposition 19.4.2, p. 880): `|S|` is first
countable (Theorem 19.2.2 (4)), so a point of `cl |Ψ(U)|` is a limit of `|Ψ(q_k)|`, `q_k ∈ U`. -/
theorem propernessV2_of_v3Lim (hv : B.PropernessV3Lim hB) : B.PropernessV2 hB := by
  let _inst := B.natTop hB
  have := B.theorem_19_2_2_four hB
  exact fun Ψ o => Chapter19.orbitChartV2_of_v3Lim (hv Ψ o)

/-- **2021 Proposition 19.4.2, (2) ⇒ (3), p. 880**, with the limit in the fibre: the limit is
`g⁻¹ ∗ q̄` with `|Ψ(q̄)| = z`. -/
theorem propernessV3Lim_of_v2 (hv : B.PropernessV2 hB) : B.PropernessV3Lim hB := by
  let _inst := B.natTop hB
  intro Ψ o
  have := Ψ.1.continuousConstSMul
  have := Ψ.1.P.metrizableSpace
  exact (B.isOrbitChart_unif hB Ψ).orbitChartV3Lim_of_v2 (hv Ψ o)

/-- **2021 Proposition 19.4.2, (3) ⇒ (1), p. 880**, with the limit in the fibre: for
`s(h_k) ∈ U(o)` and `t(h_k) → p`, (v3Lim) gives `s(h_k) → q` with `|Ψ(q)| = |Ψ'(p)|`, hence an
element `(q, φ, p)`, and the sequence lemma `exists_tendsto_subseq_of_tendsto_src` gives a
convergent subsequence. -/
theorem propernessV1_of_v3Lim (hv : B.PropernessV3Lim hB) : B.PropernessV1 := by
  let _inst := B.natTop hB
  intro Ψ o
  obtain ⟨U, hUo, hoU, hU⟩ := hv Ψ o
  refine ⟨U, hUo, hoU, fun Ψ' h hs p hp => ?_⟩
  have hc' := B.continuous_π_obj hB Ψ'.2.choose_spec
  have hz : Tendsto ((fun q => C.π (Ψ.1.obj q)) ∘ fun k => (h k : Ψ.1.Trans Ψ'.1).src) atTop
      (𝓝 (C.π (Ψ'.1.obj p))) := by
    have := (hc'.tendsto p).comp hp
    refine this.congr fun k => ?_
    exact (π_obj_src_eq_π_obj_tgt (h k : Ψ.1.Trans Ψ'.1)).symm
  obtain ⟨φ, hφ, q, -, hq, hqz⟩ := hU _ hs _ hz
  obtain ⟨μ, hμs, hμt⟩ := (C.π_eq_π_iff).1 hqz
  let a : Ψ.1.Trans Ψ'.1 := ⟨q, μ, p, hμs, hμt⟩
  obtain ⟨ψ, hψ, m, -, hm⟩ := B.rep.exists_tendsto_subseq_of_tendsto_src (h ∘ φ) a hq
  exact ⟨φ ∘ ψ, hφ.comp hψ, m, hm⟩

/-- **2021 Proposition 19.4.2, (1) ⇔ (2), p. 880**. -/
theorem proposition_19_4_2_one_iff_two : B.PropernessV1 ↔ B.PropernessV2 hB :=
  ⟨fun h => B.propernessV2_of_v3Lim hB (B.propernessV3Lim_of_v1 hB h),
    fun h => B.propernessV1_of_v3Lim hB (B.propernessV3Lim_of_v2 hB h)⟩

/-- **2021 Proposition 19.4.2, (2) ⇒ (3), p. 880**, for (v3) without the limit in the fibre. -/
theorem proposition_19_4_2_two_three (hv : B.PropernessV2 hB) : B.PropernessV3 hB := by
  let _inst := B.natTop hB
  exact fun Ψ o => (B.propernessV3Lim_of_v2 hB hv Ψ o).orbitChartV3

/-- **2021 Proposition 19.4.2, p. 880**, as we read it, with (v3) read with the limit `q` in the
fibre (`|Ψ(q)| = z`, which the proof of (3) ⇒ (1) uses): the three properness conditions (v1),
(v2), (v3) are equivalent. -/
theorem proposition_19_4_2 :
    (B.PropernessV1 ↔ B.PropernessV2 hB) ∧ (B.PropernessV2 hB ↔ B.PropernessV3Lim hB) :=
  ⟨B.proposition_19_4_2_one_iff_two hB, B.propernessV3Lim_of_v2 hB, B.propernessV2_of_v3Lim hB⟩

/-- **2021 Proposition 19.4.2, (3) ⇒ (2), p. 880**, when `T` is Hausdorff (then limits in `|S|` are
unique; `Chapter19.IsOrbitChart.orbitChartV2_of_v3`). -/
theorem proposition_19_4_2_three_two_hyp (hT : @T2Space _ (B.natTop hB))
    (hv : B.PropernessV3 hB) : B.PropernessV2 hB := by
  let _inst := B.natTop hB
  have := B.theorem_19_2_2_four hB
  exact fun Ψ o => (B.isOrbitChart_unif hB Ψ).orbitChartV2_of_v3 (hv Ψ o)

/-- **(v3) as printed holds whenever all domains are locally compact** (for instance
finite-dimensional), for every basic construction; so without the limit in the fibre it is not a
properness condition (`proposition_19_4_2_v3_without_limit`). -/
theorem propernessV3_of_locallyCompactSpace (hlc : ∀ Ψ : B.U.Unif, LocallyCompactSpace Ψ.1.O) :
    B.PropernessV3 hB := by
  let _inst := B.natTop hB
  intro Ψ o
  have := Ψ.1.P.metrizableSpace
  have := hlc Ψ
  exact Chapter19.orbitChartV3_of_locallyCompactSpace _ o

/-! ### Lemma 19.4.3 and Proposition 19.4.4 -/

/-- **2021 Lemma 19.4.3, p. 881**, for `o` the source of some element of `M(Ψ, Ψ')` (the `_hyp`;
then no properness is needed): there are finitely many `h_i ∈ M(Ψ, Ψ')` (the elements with source
`o`) and open `U(o) ∋ o`, `U(h_i) ∋ h_i` such that (1) `s : U(h_i) → U(o)` is a homeomorphism (an
open embedding with image `U(o)`) and (2) `s(h) ∈ U(o)` implies `h ∈ ⋃ U(h_i)`. -/
theorem lemma_19_4_3_hyp (Ψ Ψ' : B.U.Unif) {o : Ψ.1.O}
    (ho : ∃ h : B.M Ψ Ψ', (h : Ψ.1.Trans Ψ'.1).src = o) :
    ∃ (H : Set (B.M Ψ Ψ')) (Uo : Set Ψ.1.O) (Uh : B.M Ψ Ψ' → Set (B.M Ψ Ψ')),
      H.Finite ∧ IsOpen Uo ∧ o ∈ Uo ∧
      (∀ h ∈ H, IsOpen (Uh h) ∧ h ∈ Uh h ∧
        IsOpenEmbedding ((Uh h).domRestrict fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∧
        (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) '' Uh h = Uo) ∧
      ∀ h : B.M Ψ Ψ', (h : Ψ.1.Trans Ψ'.1).src ∈ Uo → ∃ h' ∈ H, h ∈ Uh h' := by
  obtain ⟨a, rfl⟩ := ho
  set F := B.rep
  obtain ⟨N, hNo, haN, hNx⟩ := F.exists_nbhd_eq_map (a : Ψ.1.Trans Ψ'.1)
  set H : Set (B.M Ψ Ψ') := {b | (b : Ψ.1.Trans Ψ'.1).src = (a : Ψ.1.Trans Ψ'.1).src} with hH
  have hfin : H.Finite := Ψ.1.finite_fiber (Ψ' := Ψ'.1) (a : Ψ.1.Trans Ψ'.1).src
  set Uo : Set Ψ.1.O := N ∩ ⋂ b ∈ H, F.dom Ψ Ψ' b with hUo
  have hUoo : IsOpen Uo := hNo.inter (hfin.isOpen_biInter fun b _ => F.isOpen_dom _ _ _)
  have haUo : (a : Ψ.1.Trans Ψ'.1).src ∈ Uo :=
    ⟨haN, mem_iInter₂.2 fun b hb => (hb : (b : Ψ.1.Trans Ψ'.1).src = _) ▸ F.mem_dom Ψ Ψ' b⟩
  have hUob : ∀ b ∈ H, Uo ⊆ F.dom Ψ Ψ' b := fun b hb q hq => mem_iInter₂.1 hq.2 b hb
  refine ⟨H, Uo, fun b => F.map Ψ Ψ' b '' Uo, hfin, hUoo, haUo, fun b hb => ?_, fun x hx => ?_⟩
  · have hop : IsOpen (F.map Ψ Ψ' b '' Uo : Set (B.M Ψ Ψ')) :=
      F.isOpen_image_map Ψ Ψ' b hUoo (hUob b hb)
    have himg : (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) '' (F.map Ψ Ψ' b '' Uo) = Uo := by
      ext q
      constructor
      · rintro ⟨_, ⟨q', hq', rfl⟩, rfl⟩
        change (F.map Ψ Ψ' b q').src ∈ Uo
        rw [F.src_map Ψ Ψ' b q' (hUob b hb hq')]
        exact hq'
      · intro hq
        exact ⟨F.map Ψ Ψ' b q, ⟨q, hq, rfl⟩, F.src_map Ψ Ψ' b q (hUob b hb hq)⟩
    refine ⟨hop, ⟨b.src, (hb : (b : Ψ.1.Trans Ψ'.1).src = _) ▸ haUo, F.map_src Ψ Ψ' b⟩, ?_, himg⟩
    refine ((F.isLocalHomeomorph_src Ψ Ψ').comp
      hop.isOpenEmbedding_subtypeVal.isLocalHomeomorph).isOpenEmbedding_of_injective ?_
    rintro ⟨_, q, hq, rfl⟩ ⟨_, q', hq', rfl⟩ hqq
    change (F.map Ψ Ψ' b q).src = (F.map Ψ Ψ' b q').src at hqq
    rw [F.src_map Ψ Ψ' b q (hUob b hb hq), F.src_map Ψ Ψ' b q' (hUob b hb hq')] at hqq
    subst hqq
    rfl
  · obtain ⟨b, hb, -, hxe⟩ := hNx x hx.1
    exact ⟨b, hb, (x : Ψ.1.Trans Ψ'.1).src, hx, hxe.symm⟩

/-- **Every `M(Ψ, Ψ')` is metrizable**, for every basic construction (no properness needed;
`TransitionData.metrizableSpace`). -/
theorem metrizableSpace_M (Ψ Ψ' : B.U.Unif) : MetrizableSpace (B.M Ψ Ψ') :=
  B.rep.metrizableSpace Ψ Ψ'

/-- **2021 Proposition 19.4.4, p. 883**: under the properness condition every `T_{Ψ,Ψ'}` is
metrizable.  (The properness condition is not used: `metrizableSpace_M`.) -/
theorem proposition_19_4_4 (_hv : B.PropernessV2 hB) (Ψ Ψ' : B.U.Unif) :
    MetrizableSpace (B.M Ψ Ψ') :=
  B.metrizableSpace_M Ψ Ψ'

/-! ### Proposition 19.4.5 – Corollary 19.4.8 -/

include hB in
/-- Every point of `|S|` is `|Ψ(o)|` for some `Ψ` in `F`. -/
theorem exists_unif_π_eq (z : C.OrbitSpace) :
    ∃ (Ψ : B.U.Unif) (o : Ψ.1.O), C.π (Ψ.1.obj o) = z := by
  obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
  obtain ⟨o, ho⟩ := B.U.isAt α Ψ hΨ
  exact ⟨⟨Ψ, α, hΨ⟩, o, by change C.π (Ψ.obj o) = z; rw [ho, hα]⟩

/-- **2021 Proposition 19.4.5, p. 884**: under the properness condition `T` is Hausdorff and
completely regular. -/
theorem proposition_19_4_5 (hv : B.PropernessV2 hB) :
    @T2Space _ (B.natTop hB) ∧ @CompletelyRegularSpace _ (B.natTop hB) := by
  let _inst := B.natTop hB
  have : ∀ Ψ : B.U.Unif, ContinuousConstSMul Ψ.1.G Ψ.1.O := fun Ψ => Ψ.1.continuousConstSMul
  have : ∀ Ψ : B.U.Unif, MetrizableSpace Ψ.1.O := fun Ψ => Ψ.1.P.metrizableSpace
  exact Chapter19.completelyRegularSpace_of_orbitCharts (G := fun Ψ : B.U.Unif => Ψ.1.G)
    (O := fun Ψ : B.U.Unif => Ψ.1.O) (π := fun Ψ q => C.π (Ψ.1.obj q))
    (B.isOrbitChart_unif hB) (B.exists_unif_π_eq hB) hv

/-- **2021 Theorem 19.4.6 (1), p. 885**: properness and second countability of `T` imply that `T`
is metrizable (Urysohn). -/
theorem theorem_19_4_6_one (hv : B.PropernessV2 hB)
    (hsc : @SecondCountableTopology _ (B.natTop hB)) : @MetrizableSpace _ (B.natTop hB) := by
  let _inst := B.natTop hB
  have : ∀ Ψ : B.U.Unif, ContinuousConstSMul Ψ.1.G Ψ.1.O := fun Ψ => Ψ.1.continuousConstSMul
  have : ∀ Ψ : B.U.Unif, MetrizableSpace Ψ.1.O := fun Ψ => Ψ.1.P.metrizableSpace
  exact Chapter19.metrizableSpace_of_orbitCharts_secondCountable (G := fun Ψ : B.U.Unif => Ψ.1.G)
    (O := fun Ψ : B.U.Unif => Ψ.1.O) (π := fun Ψ q => C.π (Ψ.1.obj q))
    (B.isOrbitChart_unif hB) (B.exists_unif_π_eq hB) hv

/-- **2021 Theorem 19.4.6 (2), p. 885**: properness and paracompactness of `T` imply that `T` is
metrizable (Smirnov). -/
theorem theorem_19_4_6_two (hv : B.PropernessV2 hB)
    (hpc : @ParacompactSpace _ (B.natTop hB)) : @MetrizableSpace _ (B.natTop hB) := by
  let _inst := B.natTop hB
  have : ∀ Ψ : B.U.Unif, ContinuousConstSMul Ψ.1.G Ψ.1.O := fun Ψ => Ψ.1.continuousConstSMul
  have : ∀ Ψ : B.U.Unif, MetrizableSpace Ψ.1.O := fun Ψ => Ψ.1.P.metrizableSpace
  exact Chapter19.metrizableSpace_of_orbitCharts_paracompact (G := fun Ψ : B.U.Unif => Ψ.1.G)
    (O := fun Ψ : B.U.Unif => Ψ.1.O) (π := fun Ψ q => C.π (Ψ.1.obj q))
    (B.isOrbitChart_unif hB) (B.exists_unif_π_eq hB) hv

/-- **2021 Proposition 19.4.7, p. 885**: `T` is metrizable iff `(F, 𝓕)` satisfies the properness
condition and `T` is paracompact. -/
theorem proposition_19_4_7 :
    @MetrizableSpace _ (B.natTop hB) ↔
      B.PropernessV2 hB ∧ @ParacompactSpace _ (B.natTop hB) := by
  let _inst := B.natTop hB
  refine ⟨fun hm => ?_, fun ⟨hv, hpc⟩ => B.theorem_19_4_6_two hB hv hpc⟩
  exact Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace
    (G := fun Ψ : B.U.Unif => Ψ.1.G) (O := fun Ψ : B.U.Unif => Ψ.1.O)
    (π := fun Ψ q => C.π (Ψ.1.obj q)) (B.isOrbitChart_unif hB) |>.symm

/-- **2021 Corollary 19.4.8, p. 885**: if `T` is metrizable, every `T_{Ψ,Ψ'}` is metrizable (by
Propositions 19.4.7 and 19.4.4). -/
theorem corollary_19_4_8 (hm : @MetrizableSpace _ (B.natTop hB)) (Ψ Ψ' : B.U.Unif) :
    MetrizableSpace (B.M Ψ Ψ') :=
  B.proposition_19_4_4 hB ((B.proposition_19_4_7 hB).1 hm).1 Ψ Ψ'

/-- **A uniformizer covering `|S|` makes `T` metrizable**: if `|Ψ|` is onto for some `Ψ ∈ F(α)`,
`|Ψ| : G\O → |S|` is a homeomorphism (Theorem 19.2.2 (3)) and `G\O` is metrizable. -/
theorem metrizableSpace_natTop_of_surjective {α : C.Obj} {Ψ : C.Uniformizer} (hΨ : Ψ ∈ B.U.F α)
    (hsurj : ∀ z : C.OrbitSpace, ∃ q : Ψ.O, C.π (Ψ.obj q) = z) :
    @MetrizableSpace _ (B.natTop hB) := by
  let _inst := B.natTop hB
  have he := (B.theorem_19_2_2_three hB hΨ).1
  have hs : Surjective Ψ.functor.orbitMap := fun z => by
    obtain ⟨q, rfl⟩ := hsurj z
    exact ⟨(GroupoidStr.translation Ψ.G Ψ.O).π q, rfl⟩
  have := metrizableSpace_translation_orbitSpace Ψ.smooth_smul
  let e := (Equiv.ofBijective _ ⟨he.injective, hs⟩).toHomeomorphOfContinuousOpen
    he.continuous he.isOpenMap
  exact e.symm.isEmbedding.metrizableSpace

end BasicConstruction

end GroupoidalCategory

end Polyfold
