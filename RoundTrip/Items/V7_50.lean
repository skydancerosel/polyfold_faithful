import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_50

/-!
Round trip for V7_50 (Part I, Lemma 2.7 (Michael) and Proposition 2.17, p. 51).

`A` is the conjunction of the types of the ten listed theorems of `Polyfold/Chapter7/Michael.lean`,
all universes at `0` (the space `X : Type`, the index types `ι : Type`; the cover indices of
`lemma_2_56`, `michael_tfae`, `paracompactSpace_of_closed_refinement` live in the universe of `X`,
hence in `Type`, as in `B`).

* `A → B`: `B`'s Lemma 2.7 is `lemma_2_56` (its extra `[T2Space T]` is not used), `B`'s
  Proposition 2.17 is `proposition_2_57`; both are taken from the hypothesis.
* `B → A` is not proved.  `A` is strictly more general than `B`:
  - every listed theorem drops the text's Hausdorff assumption (only `RegularSpace`);
  - `paracompactSpace_of_closed_refinement` ((d) ⇒ (a) of Michael's lemma) has **no separation
    axiom at all**; `B` says nothing about non-regular spaces, so this conjunct cannot be
    obtained from `B` (a space with locally finite closed refinements of all open covers need not
    be regular, e.g. the Sierpiński space), and would have to be re-proved (Michael's argument);
  - `michael_tfae` adds Michael's conditions (b) σ-locally finite open refinements and (c)
    locally finite refinements by arbitrary sets, which `B` does not mention (they follow from
    (a) ⇔ (d) with the unbanned `refinement_of_sigma_refinement`, `closed_refinement_of_refinement`);
  - `exists_closed_precise_refinement` is the precise (same index, `v i ⊆ u i`) form, and
    `paracompactSpace_iUnion`, `…_of_finite`, `…_biUnion_of_finite`, `paracompactSpace_union`,
    `paracompactSpace_of_isClosed_subset` are subspace forms (unions of closed paracompact
    *subsets* of an ambient regular space, and closed subsets of a paracompact subspace).
  Dropping Hausdorff could be bridged from `B` through the Kolmogorov quotient (open and closed
  sets of any space are saturated for inseparability, so the four conditions and the subspace
  statements transfer; a regular `T₀` space is `T₂`), at a cost of substantial glue; dropping
  regularity in `paracompactSpace_of_closed_refinement` cannot be bridged.
-/

namespace RoundTrip.V7_50
open Polyfold Set

/-- The ten listed theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.lemma_2_56.{0} ∧
  type_of% @Polyfold.michael_tfae.{0} ∧
  type_of% @Polyfold.proposition_2_57.{0, 0} ∧
  type_of% @Polyfold.paracompactSpace_of_closed_refinement.{0} ∧
  type_of% @Polyfold.exists_closed_precise_refinement.{0, 0} ∧
  type_of% @Polyfold.paracompactSpace_iUnion.{0, 0} ∧
  type_of% @Polyfold.paracompactSpace_iUnion_of_finite.{0, 0} ∧
  type_of% @Polyfold.paracompactSpace_biUnion_of_finite.{0, 0} ∧
  type_of% @Polyfold.paracompactSpace_union.{0} ∧
  type_of% @Polyfold.paracompactSpace_of_isClosed_subset.{0}

theorem A_holds : A :=
  ⟨@Polyfold.lemma_2_56.{0}, @Polyfold.michael_tfae.{0}, @Polyfold.proposition_2_57.{0, 0},
    @Polyfold.paracompactSpace_of_closed_refinement.{0},
    @Polyfold.exists_closed_precise_refinement.{0, 0}, @Polyfold.paracompactSpace_iUnion.{0, 0},
    @Polyfold.paracompactSpace_iUnion_of_finite.{0, 0},
    @Polyfold.paracompactSpace_biUnion_of_finite.{0, 0}, @Polyfold.paracompactSpace_union.{0},
    @Polyfold.paracompactSpace_of_isClosed_subset.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h256, -, h257, -⟩
  refine ⟨fun T _ _ _ => h256, fun T _ _ _ ι Y hYc hYf hYu hYp => ?_⟩
  exact @h257 T _ _ ι Y hYc hYf hYu hYp

#rt_check RoundTrip.V7_50.A_to_B [Polyfold.lemma_2_56, Polyfold.michael_tfae,
  Polyfold.proposition_2_57, Polyfold.paracompactSpace_of_closed_refinement,
  Polyfold.exists_closed_precise_refinement, Polyfold.paracompactSpace_iUnion,
  Polyfold.paracompactSpace_iUnion_of_finite, Polyfold.paracompactSpace_biUnion_of_finite,
  Polyfold.paracompactSpace_union, Polyfold.paracompactSpace_of_isClosed_subset]
#rt_overlap RoundTrip.V7_50.A_to_B [Polyfold.lemma_2_56, Polyfold.michael_tfae,
  Polyfold.proposition_2_57, Polyfold.paracompactSpace_of_closed_refinement,
  Polyfold.exists_closed_precise_refinement, Polyfold.paracompactSpace_iUnion,
  Polyfold.paracompactSpace_iUnion_of_finite, Polyfold.paracompactSpace_biUnion_of_finite,
  Polyfold.paracompactSpace_union, Polyfold.paracompactSpace_of_isClosed_subset]

end RoundTrip.V7_50
