import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_39

/-! Round trip for V10_39 (2021 Definition 10.3.7, p. 488; 2017: Definition 10.7, p. 351: the
map `|[d]|` of a class of diagrams).

The item lists the definition `Diagram.orbitMapQ` (vocabulary: `Quotient.lift` of
`Diagram.orbitMap` along the project's setoid) and two theorems.  `A` is the conjunction of
their types, universes at `0`: `orbitMapQ_mk` (`|⟦d⟧| = |d|`, i.e. `|Φ| ∘ |F|⁻¹` for any
representative) and `isHomeomorph_orbitMap` (`|d|` is a homeomorphism when `Φ` is an
equivalence).

`B` (at universe `0`): `orbitMapQ ⟦d⟧ = orbB d` for every representative `d`, and
`orbitMapQ ⟦d⟧` is a homeomorphism when `d.Φ` is an equivalence; the blind `orbB d` is
definitionally the project's `d.orbitMap` (the same term).

* `A ⇒ B`: the first conjunct is `orbitMapQ_mk`; the second is `isHomeomorph_orbitMap`
  transported along `orbitMapQ_mk`.
* `B ⇒ A`: `orbitMapQ_mk` is `B`'s first conjunct; `isHomeomorph_orbitMap` is `B`'s second
  conjunct transported back along the first.
-/

namespace RoundTrip.V10_39
open Polyfold Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.orbitMapQ_mk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isHomeomorph_orbitMap.{0})

theorem A_holds : A := ⟨@Diagram.orbitMapQ_mk.{0}, @Diagram.isHomeomorph_orbitMap.{0}⟩

/-- Glue: `orbB` is the project's `Diagram.orbitMap` (definitional). -/
theorem orbB_eq {X Y : EP.{0}} (d : Diagram X Y) : orbB d = d.orbitMap := rfl

theorem A_to_B : A → B.{0} := by
  rintro ⟨h1, h2⟩ X Y d
  have e : Diagram.orbitMapQ (Quotient.mk (Diagram.setoid X Y) d) = d.orbitMap := h1 d
  refine ⟨e.trans (orbB_eq d).symm, fun hΦ => ?_⟩
  rw [e]
  exact h2 d hΦ

theorem B_to_A : B.{0} → A := by
  intro hB
  refine ⟨fun {X Y} d => ((hB X Y d).1.trans (orbB_eq d)), fun {X Y} d hΦ => ?_⟩
  have e : Diagram.orbitMapQ (Quotient.mk (Diagram.setoid X Y) d) = d.orbitMap :=
    (hB X Y d).1.trans (orbB_eq d)
  rw [← e]
  exact (hB X Y d).2 hΦ

#rt_check RoundTrip.V10_39.A_to_B [Polyfold.EPLocalization.Diagram.orbitMapQ_mk,
  Polyfold.EPLocalization.Diagram.isHomeomorph_orbitMap]
#rt_check RoundTrip.V10_39.B_to_A [Polyfold.EPLocalization.Diagram.orbitMapQ_mk,
  Polyfold.EPLocalization.Diagram.isHomeomorph_orbitMap]
#rt_overlap RoundTrip.V10_39.B_to_A [Polyfold.EPLocalization.Diagram.orbitMapQ_mk,
  Polyfold.EPLocalization.Diagram.isHomeomorph_orbitMap]

end RoundTrip.V10_39
