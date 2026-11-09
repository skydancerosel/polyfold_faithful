import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_64

/-!
Round trip for V10_64 (2021 Proposition 10.3.16, p. 492: (LR) under generalized isomorphisms).

The item lists two theorems; `A` is the conjunction of their types, universes at `0`:
`EPLoc.proposition_10_3_16` (for `f : of X ⟶ of Y` a generalized isomorphism, `X.X.IsLR ↔
Y.X.IsLR`) and the general reduction `EPLoc.iff_of_isGeneralizedIso` (a property of `EP`
invariant under equivalences is invariant under generalized isomorphisms).

`B` says: for `X, Y : EPLoc.{0}` and a generalized isomorphism `f : X ⟶ Y`,
`X.toEP.X.IsLR ↔ Y.toEP.X.IsLR`.

* `A_to_B`: `proposition_10_3_16` at `X.toEP`, `Y.toEP` (`of X.toEP` is `X` by structure eta).
* `B_to_A`: `proposition_10_3_16` is `B` at `of X`, `of Y`.  The general reduction
  `iff_of_isGeneralizedIso` is not a consequence of `B` (it is about an arbitrary property `P`);
  it is re-proved outright below from the non-item lemma `exists_diagram_of_isGeneralizedIso`
  (a representative `X ←F A →Φ Y` with both legs equivalences, Theorem 10.3.10).
-/

namespace RoundTrip.V10_64
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EPLocalization.EPLoc.proposition_10_3_16.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso.{0}

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.proposition_10_3_16.{0},
    @Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩ X Y f hf
  exact h (X := X.toEP) (Y := Y.toEP) hf

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X Y f} hf => hB (EPLoc.of X) (EPLoc.of Y) f hf, ?_⟩
  -- the general reduction, re-proved outright (not a consequence of `B`)
  intro X Y P hP f hf
  obtain ⟨d, -, hΦ⟩ := EPLoc.exists_diagram_of_isGeneralizedIso hf
  exact (hP d.F d.isEquivalence_F).symm.trans (hP d.Φ hΦ)

#rt_check RoundTrip.V10_64.A_to_B [Polyfold.EPLocalization.EPLoc.proposition_10_3_16,
  Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso]
#rt_check RoundTrip.V10_64.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_10_3_16,
  Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso]
#rt_overlap RoundTrip.V10_64.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_10_3_16,
  Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso]

end RoundTrip.V10_64
