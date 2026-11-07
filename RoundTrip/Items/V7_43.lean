import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_43

/-!
Round trip for V7_43 (Lemma 7.4: local metrizability of `|X|`).

`A` is the conjunction of the types of the three listed theorems, universes at `0`
(`Obj Mor : Type`):
* `metrizableSpace_orbitRel_quotient_naturalRep`: for a natural representation `R` at `x`, the
  orbit space `G_x\U(x)` (`MulAction.orbitRel.Quotient (X.Isotropy x) R.U`) is metrizable;
* `lemma_7_4_naturalRep`: `|U(x)| = π(U(x))` is metrizable;
* `lemma_7_4`: every `z ∈ |X|` has an open metrizable neighbourhood.

`B`: every `z` has an open metrizable neighbourhood, and for every natural representation `R` at
any `x`, `π(R.U)` is open, contains `π x` and is metrizable.

`A ⇒ B`: openness of `π(U)` is `proposition_7_1` (`π` is open) with `R.isOpen_U`, and `x ∈ U` is
`R.mem_U`.  `B ⇒ A`: the quotient `G_x\U(x)` is homeomorphic to `π(U(x))` (Proposition 7.6,
`proposition_7_6`, a project definition not among the item's declarations), so its metrizability
follows from B's metrizability of `π(U(x))`.
-/

namespace RoundTrip.V7_43
open Polyfold Set

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.metrizableSpace_orbitRel_quotient_naturalRep.{0} ∧
  type_of% @Polyfold.EpGroupoid.lemma_7_4_naturalRep.{0} ∧
  type_of% @Polyfold.EpGroupoid.lemma_7_4.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.metrizableSpace_orbitRel_quotient_naturalRep, @EpGroupoid.lemma_7_4_naturalRep,
    @EpGroupoid.lemma_7_4⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  exact ⟨hA.2.2 X, fun x R =>
    ⟨X.proposition_7_1 _ R.isOpen_U, mem_image_of_mem _ R.mem_U, hA.2.1 R⟩⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x R
    have := ((hB Obj Mor X).2 x R).2.2
    exact (EpGroupoid.proposition_7_6 R).isEmbedding.metrizableSpace
  · intro Obj Mor _ _ _ _ _ _ X x R
    exact ((hB Obj Mor X).2 x R).2.2
  · intro Obj Mor _ _ _ _ _ _ X
    exact (hB Obj Mor X).1

#rt_check RoundTrip.V7_43.A_to_B [Polyfold.EpGroupoid.metrizableSpace_orbitRel_quotient_naturalRep,
  Polyfold.EpGroupoid.lemma_7_4_naturalRep, Polyfold.EpGroupoid.lemma_7_4]
#rt_check RoundTrip.V7_43.B_to_A [Polyfold.EpGroupoid.metrizableSpace_orbitRel_quotient_naturalRep,
  Polyfold.EpGroupoid.lemma_7_4_naturalRep, Polyfold.EpGroupoid.lemma_7_4]
#rt_overlap RoundTrip.V7_43.B_to_A [Polyfold.EpGroupoid.metrizableSpace_orbitRel_quotient_naturalRep,
  Polyfold.EpGroupoid.lemma_7_4_naturalRep, Polyfold.EpGroupoid.lemma_7_4]

end RoundTrip.V7_43
