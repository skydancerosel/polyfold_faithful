import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_43

/-! Round trip for V10_43 (2021 Proposition 10.3.11, p. 490; 2017: Proposition 10.6, p. 353):
`|g ∘ f| = |g| ∘ |f|`.

The item lists the definition `EPLoc.orbitMap` (vocabulary) and five theorems; `A` is the
conjunction of their types, universes at `0` (`B` lives in `Type`): `EPLoc.orbitMap_homMk`
(`|[d]| = |d|`, `rfl`), `EPLoc.continuous_orbitMap`, `EPLoc.orbitMap_id` (`|1_X| = id`),
`Diagram.orbitMap_comp` (`|d.comp e| = |e| ∘ |d|` on representatives) and
`EPLoc.proposition_10_3_11` (`|f ≫ g| = |g| ∘ |f|` on classes).

`B` says, on representatives `d : X → Y`, `e : Y → Z`, `orbB (d.comp e) = orbB e ∘ orbB d`,
with `orbB d = |Φ| ∘ |F|⁻¹`, which is `Diagram.orbitMap d` by `rfl`.

* `A_to_B`: `B` is `Diagram.orbitMap_comp` (fourth conjunct of `A`) verbatim.
* `B_to_A`: `Diagram.orbitMap_comp` is `B`; `proposition_10_3_11` follows from `B` by induction
  on the two classes; `orbitMap_homMk` is `rfl`.  Continuity and `|1_X| = id` are not
  consequences of `B` (which only speaks of composites); they are re-proved outright, from the
  non-item lemma `Diagram.continuous_orbitMap` and from `|1| ∘ |1|⁻¹ = id`. -/

namespace RoundTrip.V10_43
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.orbitMap_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.continuous_orbitMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.orbitMap_id.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.orbitMap_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.proposition_10_3_11.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.orbitMap_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.continuous_orbitMap.{0},
    @Polyfold.EPLocalization.EPLoc.orbitMap_id.{0},
    @Polyfold.EPLocalization.Diagram.orbitMap_comp.{0},
    @Polyfold.EPLocalization.EPLoc.proposition_10_3_11.{0}⟩

theorem A_to_B : A → B.{0} := by
  rintro ⟨-, -, -, hcomp, -⟩
  intro X Y Z d e
  exact hcomp d e

theorem B_to_A : B.{0} → A := by
  intro hB
  refine ⟨fun d => rfl, fun {X Y} f => ?_, fun X => ?_, fun d e => hB _ _ _ d e,
    fun {X Y Z} f g => ?_⟩
  · -- continuity, outright: `|[d]| = |Φ| ∘ |F|⁻¹` is continuous
    induction f using Quotient.inductionOn with
    | h d => exact Diagram.continuous_orbitMap d
  · -- `|1_X| = id`, outright: `|1| ∘ |1|⁻¹ = id`
    funext q
    -- `|1_X|(q) = |1|(|1|⁻¹ q) = q`
    exact (IsHomeomorph.homeomorph _
      (Diagram.id X.toEP).isEquivalence_F.isHomeomorph_orbitMap).apply_symm_apply q
  · -- Proposition 10.3.11 on classes, from `B` on representatives
    induction f using Quotient.inductionOn with
    | h d =>
      induction g using Quotient.inductionOn with
      | h e => exact hB _ _ _ d e

#rt_check RoundTrip.V10_43.A_to_B [Polyfold.EPLocalization.EPLoc.orbitMap_homMk,
  Polyfold.EPLocalization.EPLoc.continuous_orbitMap, Polyfold.EPLocalization.EPLoc.orbitMap_id,
  Polyfold.EPLocalization.Diagram.orbitMap_comp,
  Polyfold.EPLocalization.EPLoc.proposition_10_3_11]
#rt_check RoundTrip.V10_43.B_to_A [Polyfold.EPLocalization.EPLoc.orbitMap_homMk,
  Polyfold.EPLocalization.EPLoc.continuous_orbitMap, Polyfold.EPLocalization.EPLoc.orbitMap_id,
  Polyfold.EPLocalization.Diagram.orbitMap_comp,
  Polyfold.EPLocalization.EPLoc.proposition_10_3_11]
#rt_overlap RoundTrip.V10_43.B_to_A [Polyfold.EPLocalization.EPLoc.orbitMap_homMk,
  Polyfold.EPLocalization.EPLoc.continuous_orbitMap, Polyfold.EPLocalization.EPLoc.orbitMap_id,
  Polyfold.EPLocalization.Diagram.orbitMap_comp,
  Polyfold.EPLocalization.EPLoc.proposition_10_3_11]

end RoundTrip.V10_43
