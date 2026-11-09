import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_33

/-! Round trip for V10_33 (2021 Definition 10.3.1, p. 484; 2017: Definition 10.4, p. 348:
diagrams, refinements and the two examples).

The listed `Diagram`, `Diagram.IsRefinement` and `Diagram.precomp` are definitions (vocabulary);
`A` is the conjunction of the types of the three listed theorems, universe at `0` (`B` lives in
`EP.{0}`): `IsRefinement.refl`, `isRefinement_precomp` (first example: `X ←F∘H A' →Φ∘H Y`
refines `d`) and `isRefinement_of_naturallyEquivalent` (second example: `X ←G A →Ψ Y` with
`G ≃ F`, `Ψ ≃ Φ` refines `d`, via `H = 1_A`).

* `A_to_B`: B (a) is the field `isEquivalence_F` of `Diagram`, and B (b) holds by `Iff.rfl`
  (`NaturallyEquivalent F G` is `Nonempty (EpNatTrans F G)` by definition, so the project's
  `IsRefinement` *is* B's `IsRefinementB`); neither uses `A`.  B (c) is `isRefinement_precomp`
  (B's diagram `mk A' (F ∘ H) hFH (Φ ∘ H)` is `d.precomp H hH` up to proof irrelevance); B (d) is
  `isRefinement_of_naturallyEquivalent` with the two natural equivalences reversed
  (`NaturallyEquivalent.symm`: B takes `F → F'`, the project `G → F`).
* `B_to_A`: `IsRefinement.refl` is B (d) with `F' = F`, `Φ' = Φ` (`NaturallyEquivalent.refl`;
  `mk d.A d.F _ d.Φ` is `d` by structure eta), transported by B (b); the two examples are B (c)
  (with `hFH` the proof field of `d.precomp H hH`) and B (d) (with `symm`), transported by
  B (b). -/

namespace RoundTrip.V10_33
open Polyfold EPLocalization

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.refl.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_precomp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_of_naturallyEquivalent.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.Diagram.IsRefinement.refl.{0},
    @Polyfold.EPLocalization.Diagram.isRefinement_precomp.{0},
    @Polyfold.EPLocalization.Diagram.isRefinement_of_naturallyEquivalent.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, h2, h3⟩
  intro X Y
  refine ⟨fun d => d.isEquivalence_F, fun d' d => Iff.rfl, ?_, ?_⟩
  · intro d A' H hFH hH
    exact h2 d H hH
  · intro d F' hF' Φ' hF hΦ
    exact h3 d F' hF' Φ' (EpFunctor.NaturallyEquivalent.symm hF)
      (EpFunctor.NaturallyEquivalent.symm hΦ)

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro X Y d
    exact ((hB X Y).2.1 d d).2 ((hB X Y).2.2.2 d d.F d.isEquivalence_F d.Φ
      (EpFunctor.NaturallyEquivalent.refl d.F) (EpFunctor.NaturallyEquivalent.refl d.Φ))
  · intro X Y d A' H hH
    exact ((hB X Y).2.1 _ d).2 ((hB X Y).2.2.1 d A' H (d.precomp H hH).isEquivalence_F hH)
  · intro X Y d G hG Ψ hGF hΨΦ
    exact ((hB X Y).2.1 _ d).2 ((hB X Y).2.2.2 d G hG Ψ (EpFunctor.NaturallyEquivalent.symm hGF)
      (EpFunctor.NaturallyEquivalent.symm hΨΦ))

#rt_check RoundTrip.V10_33.A_to_B [Polyfold.EPLocalization.Diagram.IsRefinement.refl,
  Polyfold.EPLocalization.Diagram.isRefinement_precomp,
  Polyfold.EPLocalization.Diagram.isRefinement_of_naturallyEquivalent]
#rt_check RoundTrip.V10_33.B_to_A [Polyfold.EPLocalization.Diagram.IsRefinement.refl,
  Polyfold.EPLocalization.Diagram.isRefinement_precomp,
  Polyfold.EPLocalization.Diagram.isRefinement_of_naturallyEquivalent]
#rt_overlap RoundTrip.V10_33.B_to_A [Polyfold.EPLocalization.Diagram.IsRefinement.refl,
  Polyfold.EPLocalization.Diagram.isRefinement_precomp,
  Polyfold.EPLocalization.Diagram.isRefinement_of_naturallyEquivalent]

end RoundTrip.V10_33
