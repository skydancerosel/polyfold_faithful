import Polyfold.Chapter2.Metrizable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017), Part II, Chapter 7: the properness
condition (3) of **Definition 7.3** (p. 227) and **Definition 7.17** (p. 251), in the forms used by
the proofs of Proposition 7.3 (pp. 229–230), Lemma 7.1 (p. 230), Lemmas 7.6–7.7 (pp. 245–246),
Proposition 7.11 (p. 248), Propositions 7.13–7.14 (pp. 251–252) and Lemma 7.8 (pp. 253–254).

# Proper maps and the sequential criterion

## The text, paraphrased

(Definition 7.3 (3)) Every object `x` has an open neighbourhood `V(x)` such that the map
`t : s⁻¹(cl_X(V(x))) → X` is proper.  (Definition 7.17) A subset `Q ⊂ X` is proper if
`t : s⁻¹(Q) → X` is proper.  The text does not define "proper"; its proofs use two forms.
Preimages of compact sets are compact (Proposition 7.13: "the preimage `(t|s⁻¹(Q))⁻¹(K)` of `K`
… is a compact subset of `s⁻¹(Q)`").  And, in most proofs, a sequential form: a sequence `(φ_k)`
with `s(φ_k) ∈ Q` and `t(φ_k) → y` has a convergent subsequence `φ_k → φ` (Proposition 7.3,
Lemma 7.1, Lemmas 7.6–7.8, Propositions 7.11 and 7.14).  (Proposition 7.13) A proper set is
closed: for `x_n → x` in `Q`, apply properness to the units `1_{x_n}`.  (Proposition 7.14 (1)) If
`Q` is proper, then `π(Q)` is closed in `|X|`, i.e. its saturation `π⁻¹(π(Q)) = t(s⁻¹(Q))` is
closed in `X`.  (Lemma 7.1) Properness and the local injectivity of `t` leave only finitely many
morphisms over a point.

## What is formalized

For a map `f : A → Y`:
* `exists_tendsto_subseq_of_isProperMap` (`A` first countable): if `f(a_n) → y`, a subsequence of
  `(a_n)` converges to some `x` with `f x = y`.
* `isProperMap_of_exists_tendsto_subseq` and `isProperMap_iff_exists_tendsto_subseq` (`A`
  pseudo-metrizable, `Y` Hausdorff and first countable, so in particular both metrizable):
  `IsProperMap f` holds iff `f` is continuous and every sequence whose images converge has a
  convergent subsequence.
* `finite_preimage_singleton_of_isProperMap`: a proper, locally injective map has finite fibres.

For maps `s t : M → X` and `Q ⊆ X`, with properness of `Q` read as
`IsProperMap ((s ⁻¹' Q).domRestrict t)`:
* the sequential form: `exists_tendsto_subseq_of_isProperMap_domRestrict` (also for sequences
  that lie over `Q` only eventually, `…_of_eventually`), `isProperMap_domRestrict_iff`, and, for
  a closed `Q` and a continuous `s`, `isProperMap_domRestrict_iff_of_isClosed` (the limit then lies
  over `Q` by itself, as in the text);
* **closed subsets of proper sets are proper**: `isProperMap_domRestrict_of_subset`,
  `isProperMap_domRestrict_of_subset_of_isClosed`, and `isProperMap_domRestrict_closure_mono` (an
  open `V' ⊆ V(x)` works in Definition 7.3 (3) as well as `V(x)`);
* **saturations are closed**: `isClosed_image_of_isProperMap_domRestrict` (`t(F)` is closed for a
  closed `F ⊆ s⁻¹(Q)`), `isClosed_image_preimage_of_isProperMap_domRestrict` (`t(s⁻¹(Q'))` is
  closed for a closed `Q' ⊆ Q`; for `Q' = Q` the saturation of Proposition 7.14 (1));
* `isClosed_of_isProperMap_domRestrict`: the argument of Proposition 7.13 (a proper set is
  closed), for any `u : X → M` with `s ∘ u = t ∘ u = id`;
* `finite_setOf_of_isProperMap_domRestrict`: the argument of Lemma 7.1 (finitely many `φ` with
  `s(φ) ∈ Q`, `t(φ) = y`, if `t` is locally injective).

For M-polyfolds `M` and `X` (metrizable by Theorem 2.2 [2.16], `MPolyfold.metrizableSpace`):
`MPolyfold.isProperMap_domRestrict_iff`, `MPolyfold.isProperMap_domRestrict_iff_of_isClosed`,
`MPolyfold.isProperMap_domRestrict_iff_isCompact_preimage`,
`MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict`.

## Reading

* "Proper" is Mathlib's `IsProperMap` (decision P3 of the plan): continuous, and every cluster
  point of `map f 𝓕` is the image of a cluster point of `𝓕` (Bourbaki-proper).  For a
  Hausdorff, compactly generated target this is "continuous, and preimages of compact sets are
  compact" (`isProperMap_iff_isCompact_preimage`), the form of Proposition 7.13.  Between
  metrizable spaces both are the sequential form proved here, which is how the other proofs of
  the chapter use properness.
* The restriction `t : s⁻¹(Q) → X` is `(s ⁻¹' Q).domRestrict t`, a map on the subtype; Mathlib's
  `Set.restrict` is deprecated in favour of `Set.domRestrict` (since 2026-07-19).
* In the sequential form the limit `φ` is a point of `s⁻¹(Q)` with `t(φ) = y`; the text uses
  both tacitly.  The first is automatic for closed `Q` (and a proper `Q` is closed by Proposition
  7.13), the second by continuity of `t`.
* Everything here is about maps of topological spaces; nothing depends on the ep-groupoid
  structure.  The units of Proposition 7.13 enter only through `s ∘ u = t ∘ u = id`.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

/-! ### Proper maps and sequences -/

section Sequential

variable {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y] {f : A → Y}

/-- **Proper maps, sequentially** (the form used throughout Chapter 7): if `f` is proper and
`f(a_n) → y`, then a subsequence of `(a_n)` converges to some `x` with `f x = y`.  Only the
first countability of `A` is used. -/
theorem exists_tendsto_subseq_of_isProperMap [FirstCountableTopology A] (hf : IsProperMap f)
    {a : ℕ → A} {y : Y} (ha : Tendsto (f ∘ a) atTop (𝓝 y)) :
    ∃ x, f x = y ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (a ∘ ψ) atTop (𝓝 x) := by
  have hcl : MapClusterPt y (map a atTop) f := by
    rw [MapClusterPt, Filter.map_map]
    exact ha.mapClusterPt
  obtain ⟨x, hx, hxcl⟩ := hf.clusterPt_of_mapClusterPt hcl
  exact ⟨x, hx, MapClusterPt.tendsto_subseq hxcl⟩

/-- **The sequential criterion implies properness**: a continuous map from a pseudo-metrizable
space to a Hausdorff first countable space is proper if every sequence whose images converge has
a convergent subsequence. -/
theorem isProperMap_of_exists_tendsto_subseq [PseudoMetrizableSpace A] [T2Space Y]
    [FirstCountableTopology Y] (hc : Continuous f)
    (h : ∀ ⦃a : ℕ → A⦄ ⦃y : Y⦄, Tendsto (f ∘ a) atTop (𝓝 y) →
      ∃ x, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (a ∘ ψ) atTop (𝓝 x)) :
    IsProperMap f := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨hc, fun K hK => IsSeqCompact.isCompact ?_⟩
  intro a ha
  obtain ⟨y, hyK, ψ, hψ, hy⟩ := hK.tendsto_subseq (x := f ∘ a) ha
  obtain ⟨x, ψ', hψ', hx⟩ := h (a := a ∘ ψ) hy
  have hfx : f x = y :=
    tendsto_nhds_unique ((hc.tendsto x).comp hx) (hy.comp hψ'.tendsto_atTop)
  exact ⟨x, by rw [mem_preimage, hfx]; exact hyK, ψ ∘ ψ', hψ.comp hψ', hx⟩

/-- **Proper maps between metrizable spaces, sequentially**: `f` is proper iff it is continuous
and every sequence `(a_n)` with `f(a_n)` convergent has a convergent subsequence.  (The
hypotheses: `A` pseudo-metrizable, `Y` Hausdorff and first countable; metrizable spaces have
both.) -/
theorem isProperMap_iff_exists_tendsto_subseq [PseudoMetrizableSpace A] [T2Space Y]
    [FirstCountableTopology Y] :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃a : ℕ → A⦄ ⦃y : Y⦄, Tendsto (f ∘ a) atTop (𝓝 y) →
      ∃ x, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (a ∘ ψ) atTop (𝓝 x) := by
  refine ⟨fun hf => ⟨hf.continuous, fun a y ha => ?_⟩,
    fun h => isProperMap_of_exists_tendsto_subseq h.1 h.2⟩
  obtain ⟨x, -, hx⟩ := exists_tendsto_subseq_of_isProperMap hf ha
  exact ⟨x, hx⟩

/-- **A proper, locally injective map has finite fibres** (the argument of Lemma 7.1): the fibre
is compact, and discrete because `f` is injective near each of its points. -/
theorem finite_preimage_singleton_of_isProperMap (hf : IsProperMap f)
    (hinj : IsLocallyInjective f) (y : Y) : (f ⁻¹' {y}).Finite := by
  refine (hf.isCompact_preimage isCompact_singleton).finite
    (isDiscrete_iff_forall_mem_exists_isOpen.2 fun a ha => ?_)
  have ha' : f a = y := ha
  obtain ⟨U, hUo, haU, hinjU⟩ := hinj a
  refine ⟨U, hUo, Set.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · have hb' : f b = y := hb.2
    exact hinjU hb.1 haU (hb'.trans ha'.symm)
  · rw [mem_singleton_iff] at hb
    subst hb
    exact ⟨haU, ha⟩

end Sequential

/-! ### Proper subsets: `t : s⁻¹(Q) → X` -/

section Restrict

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X] {s t : M → X} {Q Q' : Set X}

/-- **The sequential form of properness of `Q`** (Proposition 7.3, Lemma 7.1, Lemmas 7.6–7.8,
Proposition 7.14): if `t : s⁻¹(Q) → X` is proper, `s(φ_n) ∈ Q` and `t(φ_n) → y`, then a
subsequence of `(φ_n)` converges to some `φ₀` with `s(φ₀) ∈ Q` and `t(φ₀) = y`. -/
theorem exists_tendsto_subseq_of_isProperMap_domRestrict [FirstCountableTopology M]
    (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t)) {φ : ℕ → M} (hφ : ∀ n, s (φ n) ∈ Q) {y : X}
    (hy : Tendsto (t ∘ φ) atTop (𝓝 y)) :
    ∃ φ₀, s φ₀ ∈ Q ∧ t φ₀ = y ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  obtain ⟨x, hx, ψ, hψ, hlim⟩ :=
    exists_tendsto_subseq_of_isProperMap hQ (a := fun n => ⟨φ n, hφ n⟩) hy
  exact ⟨x, x.2, hx, ψ, hψ, (continuous_subtype_val.tendsto x).comp hlim⟩

/-- The sequential form of properness for sequences which lie over `Q` only eventually (as in
Lemma 7.8, where `s(h_k) → x₀ ∈ V(x₀)`). -/
theorem exists_tendsto_subseq_of_isProperMap_domRestrict_of_eventually
    [FirstCountableTopology M] (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t)) {φ : ℕ → M}
    (hφ : ∀ᶠ n in atTop, s (φ n) ∈ Q) {y : X} (hy : Tendsto (t ∘ φ) atTop (𝓝 y)) :
    ∃ φ₀, s φ₀ ∈ Q ∧ t φ₀ = y ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hφ
  obtain ⟨φ₀, h₁, h₂, ψ, hψ, hlim⟩ := exists_tendsto_subseq_of_isProperMap_domRestrict hQ
    (φ := fun n => φ (n + N)) (fun n => hN _ (Nat.le_add_left N n))
    ((tendsto_add_atTop_iff_nat N).2 hy)
  exact ⟨φ₀, h₁, h₂, fun n => ψ n + N, fun a b hab => Nat.add_lt_add_right (hψ hab) N, hlim⟩

/-- **The sequential criterion for `t : s⁻¹(Q) → X`**: if every sequence `(φ_n)` over `Q` with
`t(φ_n)` convergent has a subsequence converging to a point over `Q`, the map is proper. -/
theorem isProperMap_domRestrict_of_exists_tendsto_subseq [PseudoMetrizableSpace M] [T2Space X]
    [FirstCountableTopology X] (ht : Continuous t)
    (h : ∀ ⦃φ : ℕ → M⦄ ⦃y : X⦄, (∀ n, s (φ n) ∈ Q) → Tendsto (t ∘ φ) atTop (𝓝 y) →
      ∃ φ₀, s φ₀ ∈ Q ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀)) :
    IsProperMap ((s ⁻¹' Q).domRestrict t) := by
  refine isProperMap_of_exists_tendsto_subseq (ht.comp continuous_subtype_val) fun a y ha => ?_
  obtain ⟨φ₀, hφ₀, ψ, hψ, hlim⟩ := h (φ := fun n => (a n : M)) (fun n => (a n).2) ha
  exact ⟨⟨φ₀, hφ₀⟩, ψ, hψ, tendsto_subtype_rng.2 hlim⟩

/-- **Properness of `Q`, sequentially** (`M` pseudo-metrizable, `X` Hausdorff and first
countable): `t : s⁻¹(Q) → X` is proper iff every sequence `(φ_n)` with `s(φ_n) ∈ Q` and
`t(φ_n)` convergent has a subsequence converging to some `φ₀` with `s(φ₀) ∈ Q`. -/
theorem isProperMap_domRestrict_iff [PseudoMetrizableSpace M] [T2Space X]
    [FirstCountableTopology X] (ht : Continuous t) :
    IsProperMap ((s ⁻¹' Q).domRestrict t) ↔ ∀ ⦃φ : ℕ → M⦄ ⦃y : X⦄, (∀ n, s (φ n) ∈ Q) →
      Tendsto (t ∘ φ) atTop (𝓝 y) →
        ∃ φ₀, s φ₀ ∈ Q ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  refine ⟨fun hQ φ y hφ hy => ?_, isProperMap_domRestrict_of_exists_tendsto_subseq ht⟩
  obtain ⟨φ₀, h₁, -, h₃⟩ := exists_tendsto_subseq_of_isProperMap_domRestrict hQ hφ hy
  exact ⟨φ₀, h₁, h₃⟩

/-- **Properness of a closed `Q`, sequentially**, in the words of the text: `t : s⁻¹(Q) → X` is
proper iff every sequence `(φ_n)` with `s(φ_n) ∈ Q` and `t(φ_n)` convergent has a convergent
subsequence (its limit lies over `Q` since `Q` is closed and `s` continuous). -/
theorem isProperMap_domRestrict_iff_of_isClosed [PseudoMetrizableSpace M] [T2Space X]
    [FirstCountableTopology X] (hs : Continuous s) (ht : Continuous t) (hQ : IsClosed Q) :
    IsProperMap ((s ⁻¹' Q).domRestrict t) ↔ ∀ ⦃φ : ℕ → M⦄ ⦃y : X⦄, (∀ n, s (φ n) ∈ Q) →
      Tendsto (t ∘ φ) atTop (𝓝 y) →
        ∃ φ₀, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  rw [isProperMap_domRestrict_iff ht]
  refine forall₂_congr fun φ y => imp_congr_right fun hφ => imp_congr_right fun _ =>
    ⟨fun ⟨φ₀, _, h⟩ => ⟨φ₀, h⟩, fun ⟨φ₀, ψ, hψ, hlim⟩ => ⟨φ₀, ?_, ψ, hψ, hlim⟩⟩
  exact (hQ.preimage hs).mem_of_tendsto hlim (Eventually.of_forall fun n => hφ (ψ n))

/-- **Subsets of proper sets with closed preimage are proper**: if `t : s⁻¹(Q) → X` is proper,
`Q' ⊆ Q` and `s⁻¹(Q')` is closed, then `t : s⁻¹(Q') → X` is proper (`s⁻¹(Q') → s⁻¹(Q)` is a
closed embedding). -/
theorem isProperMap_domRestrict_of_subset (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t))
    (hQ' : Q' ⊆ Q) (hcl : IsClosed (s ⁻¹' Q')) : IsProperMap ((s ⁻¹' Q').domRestrict t) := by
  have hsub : s ⁻¹' Q' ⊆ s ⁻¹' Q := preimage_mono hQ'
  have hemb : IsClosedEmbedding (inclusion hsub) :=
    ⟨IsEmbedding.inclusion hsub, by
      rw [range_inclusion]
      exact hcl.preimage continuous_subtype_val⟩
  exact hQ.comp hemb.isProperMap

/-- **Closed subsets of proper sets are proper** (`s` continuous). -/
theorem isProperMap_domRestrict_of_subset_of_isClosed (hs : Continuous s)
    (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t)) (hQ' : Q' ⊆ Q) (hcl : IsClosed Q') :
    IsProperMap ((s ⁻¹' Q').domRestrict t) :=
  isProperMap_domRestrict_of_subset hQ hQ' (hcl.preimage hs)

/-- **Shrinking the neighbourhood in Definition 7.3 (3)**: if `t : s⁻¹(cl V) → X` is proper and
`V' ⊆ V`, then `t : s⁻¹(cl V') → X` is proper (`s` continuous). -/
theorem isProperMap_domRestrict_closure_mono (hs : Continuous s) {V V' : Set X}
    (hV : IsProperMap ((s ⁻¹' closure V).domRestrict t)) (hV' : V' ⊆ V) :
    IsProperMap ((s ⁻¹' closure V').domRestrict t) :=
  isProperMap_domRestrict_of_subset_of_isClosed hs hV (closure_mono hV') isClosed_closure

/-- **Images of closed sets under a proper `t : s⁻¹(Q) → X` are closed**: `t(F)` is closed for
every closed `F ⊆ s⁻¹(Q)`. -/
theorem isClosed_image_of_isProperMap_domRestrict (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t))
    {F : Set M} (hF : F ⊆ s ⁻¹' Q) (hFc : IsClosed F) : IsClosed (t '' F) := by
  have h := hQ.isClosedMap _ (hFc.preimage continuous_subtype_val)
  rwa [image_domRestrict, inter_eq_left.2 hF] at h

/-- **Saturations are closed** (Proposition 7.14 (1), at the level of objects): if `Q` is
proper and `Q' ⊆ Q` has closed preimage `s⁻¹(Q')`, then `t(s⁻¹(Q'))` is closed.  For `Q' = Q`
this is the closedness of the saturation `π⁻¹(π(Q)) = t(s⁻¹(Q))`. -/
theorem isClosed_image_preimage_of_isProperMap_domRestrict
    (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t)) (hQ' : Q' ⊆ Q) (hcl : IsClosed (s ⁻¹' Q')) :
    IsClosed (t '' (s ⁻¹' Q')) :=
  isClosed_image_of_isProperMap_domRestrict hQ (preimage_mono hQ') hcl

/-- **A proper set is closed** (the argument of Proposition 7.13): if `t : s⁻¹(Q) → X` is proper
and `u : X → M` satisfies `s ∘ u = t ∘ u = id` (the units), then `Q` is closed.  For `x_n → x` in
`Q` a subsequence of `u(x_n)` converges to some `φ₀` over `Q`, and `x = s(φ₀)`. -/
theorem isClosed_of_isProperMap_domRestrict [FirstCountableTopology M] [T2Space X]
    [FrechetUrysohnSpace X] (hs : Continuous s) (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t))
    {u : X → M} (hsu : ∀ x, s (u x) = x) (htu : ∀ x, t (u x) = x) : IsClosed Q := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨a, haQ, hax⟩ := mem_closure_iff_seq_limit.1 hx
  have htua : t ∘ u ∘ a = a := funext fun n => htu (a n)
  obtain ⟨φ₀, hφ₀, -, ψ, hψ, hlim⟩ := exists_tendsto_subseq_of_isProperMap_domRestrict hQ
    (φ := u ∘ a) (fun n => by simp only [comp_apply, hsu]; exact haQ n)
    (by rw [htua]; exact hax)
  have hsua : s ∘ (u ∘ a) ∘ ψ = a ∘ ψ := funext fun n => hsu (a (ψ n))
  have h₁ : Tendsto (a ∘ ψ) atTop (𝓝 (s φ₀)) := hsua ▸ (hs.tendsto φ₀).comp hlim
  rw [tendsto_nhds_unique (hax.comp hψ.tendsto_atTop) h₁]
  exact hφ₀

/-- **Finitely many morphisms over a point** (the argument of Lemma 7.1): if `t : s⁻¹(Q) → X`
is proper and `t` is locally injective, then for every `y` there are only finitely many `φ`
with `s(φ) ∈ Q` and `t(φ) = y`. -/
theorem finite_setOf_of_isProperMap_domRestrict (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t))
    (ht : IsLocallyInjective t) (y : X) : {φ | s φ ∈ Q ∧ t φ = y}.Finite := by
  have hinj : IsLocallyInjective ((s ⁻¹' Q).domRestrict t) :=
    ht.comp_right continuous_subtype_val Subtype.val_injective
  have hfin := (finite_preimage_singleton_of_isProperMap hQ hinj y).image Subtype.val
  refine hfin.subset fun φ hφ => ⟨⟨φ, hφ.1⟩, hφ.2, rfl⟩

end Restrict

/-! ### M-polyfolds -/

namespace MPolyfold

variable {M X : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M]
  [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {s t : M → X} {Q : Set X}

/-- **Properness of `Q` for M-polyfolds, sequentially** (both spaces are metrizable, Theorem 2.2
[2.16]): `t : s⁻¹(Q) → X` is proper iff every sequence `(φ_n)` with `s(φ_n) ∈ Q` and `t(φ_n)`
convergent has a subsequence converging to some `φ₀` with `s(φ₀) ∈ Q`. -/
theorem isProperMap_domRestrict_iff (PM : MPolyfold M) (PX : MPolyfold X) (ht : Continuous t) :
    IsProperMap ((s ⁻¹' Q).domRestrict t) ↔ ∀ ⦃φ : ℕ → M⦄ ⦃y : X⦄, (∀ n, s (φ n) ∈ Q) →
      Tendsto (t ∘ φ) atTop (𝓝 y) →
        ∃ φ₀, s φ₀ ∈ Q ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  have := PM.metrizableSpace
  have := PX.metrizableSpace
  exact Polyfold.isProperMap_domRestrict_iff ht

/-- **Properness of a closed `Q` for M-polyfolds, sequentially**, in the words of the text: every
sequence `(φ_n)` with `s(φ_n) ∈ Q` and `t(φ_n)` convergent has a convergent subsequence. -/
theorem isProperMap_domRestrict_iff_of_isClosed (PM : MPolyfold M) (PX : MPolyfold X)
    (hs : Continuous s) (ht : Continuous t) (hQ : IsClosed Q) :
    IsProperMap ((s ⁻¹' Q).domRestrict t) ↔ ∀ ⦃φ : ℕ → M⦄ ⦃y : X⦄, (∀ n, s (φ n) ∈ Q) →
      Tendsto (t ∘ φ) atTop (𝓝 y) →
        ∃ φ₀, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  have := PM.metrizableSpace
  have := PX.metrizableSpace
  exact Polyfold.isProperMap_domRestrict_iff_of_isClosed hs ht hQ

omit [T2Space M] [ParacompactSpace M] in
/-- **Properness of `Q` for M-polyfolds, by compact sets** (the form of Proposition 7.13):
`t : s⁻¹(Q) → X` is proper iff it is continuous and preimages of compact sets are compact. -/
theorem isProperMap_domRestrict_iff_isCompact_preimage (PX : MPolyfold X) :
    IsProperMap ((s ⁻¹' Q).domRestrict t) ↔ Continuous ((s ⁻¹' Q).domRestrict t) ∧
      ∀ ⦃K : Set X⦄, IsCompact K → IsCompact ((s ⁻¹' Q).domRestrict t ⁻¹' K) := by
  have := PX.metrizableSpace
  exact isProperMap_iff_isCompact_preimage

omit [T2Space X] [ParacompactSpace X] in
/-- **The sequential form of properness for M-polyfolds**: if `t : s⁻¹(Q) → X` is proper,
`s(φ_n) ∈ Q` and `t(φ_n) → y`, a subsequence of `(φ_n)` converges to some `φ₀` with
`s(φ₀) ∈ Q` and `t(φ₀) = y`. -/
theorem exists_tendsto_subseq_of_isProperMap_domRestrict (PM : MPolyfold M)
    (hQ : IsProperMap ((s ⁻¹' Q).domRestrict t)) {φ : ℕ → M} (hφ : ∀ n, s (φ n) ∈ Q) {y : X}
    (hy : Tendsto (t ∘ φ) atTop (𝓝 y)) :
    ∃ φ₀, s φ₀ ∈ Q ∧ t φ₀ = y ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) := by
  have := PM.metrizableSpace
  exact Polyfold.exists_tendsto_subseq_of_isProperMap_domRestrict hQ hφ hy

end MPolyfold

end Polyfold
