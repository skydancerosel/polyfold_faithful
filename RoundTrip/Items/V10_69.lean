import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_69

/-! Round trip for V10_69 (2021 Lemma 10.3.4 in the strong bundle case, §10.5 p. 504:
"having a common refinement" is transitive, so the generalized strong bundle maps are its
classes).

`A` is the conjunction of the types of the four listed theorems, universes at `0`:
`SDiagram.lemma_10_3_4` and its alias `SDiagram.Equiv.trans` (transitivity),
`SDiagram.equivalence_equiv` (an equivalence relation) and `SDiagram.cls_eq_cls_iff`
(`[D] = [D'] ↔ D ≈ D'`).  `B`: for all `A A' : SEP.{0}`, `Equivalence SDiagram.Equiv` and
`D.cls = D'.cls ↔ D.Equiv D'`.

* `A_to_B`: `equivalence_equiv` and `cls_eq_cls_iff` of `A`.
* `B_to_A`: transitivity is `(B A A').1.trans` (twice), the equivalence is `(B A A').1`, the
  iff `(B A A').2`. -/

namespace RoundTrip.V10_69
open Polyfold Polyfold.SBLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.SDiagram.lemma_10_3_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.Equiv.trans.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.equivalence_equiv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SDiagram.lemma_10_3_4.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.trans.{0},
    @Polyfold.SBLocalization.SDiagram.equivalence_equiv.{0},
    @Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, hequiv, hiff⟩
  intro A A'
  exact ⟨hequiv, fun D D' => hiff⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A A' D D' D'' h h'
    exact (hB A A').1.trans h h'
  · intro A A' D D' D'' h h'
    exact (hB A A').1.trans h h'
  · intro A A'
    exact (hB A A').1
  · intro A A' D D'
    exact (hB A A').2 D D'

#rt_check RoundTrip.V10_69.A_to_B [Polyfold.SBLocalization.SDiagram.lemma_10_3_4,
  Polyfold.SBLocalization.SDiagram.Equiv.trans,
  Polyfold.SBLocalization.SDiagram.equivalence_equiv,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff]
#rt_check RoundTrip.V10_69.B_to_A [Polyfold.SBLocalization.SDiagram.lemma_10_3_4,
  Polyfold.SBLocalization.SDiagram.Equiv.trans,
  Polyfold.SBLocalization.SDiagram.equivalence_equiv,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff]
#rt_overlap RoundTrip.V10_69.B_to_A [Polyfold.SBLocalization.SDiagram.lemma_10_3_4,
  Polyfold.SBLocalization.SDiagram.Equiv.trans,
  Polyfold.SBLocalization.SDiagram.equivalence_equiv,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff]

end RoundTrip.V10_69
