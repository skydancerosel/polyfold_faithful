import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_21

/-! Round trip for V3_21 (Proposition 3.22: `N ∩ C` is a partial quadrant in `N`).

`A` is the conjunction of the types of `proposition_3_22`, `exists_quadrantNormalForm` (universe
of `V` instantiated at `0`), `mem_quadCone_of_vanIdx` and `sigmaCoord_surjective` (both also
universe-polymorphic in `V`, instantiated at `0`).  `QuadrantNormalForm` is a definition
(vocabulary).

* `A → B` is proved: `B`'s good position (`IsInGoodPositionB`: an sc-complement when `N` is smooth,
  a closed complement otherwise) gives the project's `IsInGoodPosition` (an algebraic complement
  with the same `ε`-property; the level-`0` part of an sc-splitting is an algebraic complement),
  and `proposition_3_22` concludes.  `B`'s extra hypothesis `E.IsScSubspace N` is not needed.
* `B → A` is not proved, and is a genuine generality gap: `A`'s `proposition_3_22` allows any
  finite-dimensional `N` (not necessarily smooth) with a merely ALGEBRAIC good complement, which
  `B` (smooth `N`, sc-complement) does not cover; turning an algebraic good complement into an
  sc-complement with the `ε`-property is possible but is itself the normal-form argument
  (Lemma 3.65).  `A`'s other three conjuncts are the coordinate core of the proof (functionals
  `ℓ_i` on an arbitrary normed space `V`), which `B` does not state.
-/

namespace RoundTrip.V3_21
open Polyfold

/-- The project's statement (universe of `V` at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_3_22) ∧
    (type_of% @Polyfold.exists_quadrantNormalForm.{0}) ∧
    (type_of% @Polyfold.mem_quadCone_of_vanIdx.{0}) ∧
    (type_of% @Polyfold.sigmaCoord_surjective.{0})

theorem A_holds : A :=
  ⟨@Polyfold.proposition_3_22, @Polyfold.exists_quadrantNormalForm.{0},
    @Polyfold.mem_quadCone_of_vanIdx.{0}, @Polyfold.sigmaCoord_surjective.{0}⟩

/-- `B`'s good complement (sc-complement / closed complement with the `ε`-property) is a good
complement in the project's (algebraic) sense. -/
theorem isGoodComplement_of_B {E : ScBanach} {C : Set (E 0)} {N P : Submodule ℝ (E 0)}
    (h : IsGoodComplementB E C N P) : IsGoodComplement E C N P := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h3⟩
  by_cases hN : N ≤ E.smooth
  · have := (h1 hN).2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  · exact (h2 hN).1

theorem isInGoodPosition_of_B {E : ScBanach} {C : Set (E 0)} {N : Submodule ℝ (E 0)}
    (h : IsInGoodPositionB E C N) : IsInGoodPosition E C N :=
  ⟨h.1, let ⟨P, hP⟩ := h.2; ⟨P, isGoodComplement_of_B hP⟩⟩

theorem A_to_B : A → B := by
  rintro ⟨h322, -⟩ E C N _ hC _ hN
  exact h322 hC (isInGoodPosition_of_B hN)

#rt_check RoundTrip.V3_21.A_to_B [Polyfold.proposition_3_22, Polyfold.exists_quadrantNormalForm,
  Polyfold.mem_quadCone_of_vanIdx, Polyfold.sigmaCoord_surjective]
#rt_overlap RoundTrip.V3_21.A_to_B [Polyfold.proposition_3_22, Polyfold.exists_quadrantNormalForm,
  Polyfold.mem_quadCone_of_vanIdx, Polyfold.sigmaCoord_surjective]

end RoundTrip.V3_21
