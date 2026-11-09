import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_61

set_option maxSynthPendingDepth 3

/-!
Round trip for V10_61 (2021 Proposition 10.5.6, p. 508: (LR) of strong bundles under generalized
strong bundle isomorphisms, reduced to Proposition 10.4.6).

The item lists one theorem; `A` is its type, universe at `0`:
`SBLocalization.GenSBMap.iff_of_isGeneralizedIso` — for **any** property `Pr : SEP → Prop` that
is invariant under strong bundle equivalences (`SEP.equivalences`), and a generalized strong
bundle isomorphism `f : GenSBMap A A'`, `Pr A ↔ Pr A'`.  This is only the reduction step of the
text's proof; Proposition 10.4.6 ((LR) of Definition 8.4.2 is invariant under strong bundle
equivalences) is not formalized in the project, so no project theorem mentions (LR) here.

`B`: for every generalized strong bundle isomorphism `f : GenSBMap A A'`,
`IsLRB A.E ↔ IsLRB A'.E`, with B's own (LR) `IsLRB` (Definition 8.4.2, testing strong bundle
isomorphisms of `W|U(x)`).

* `A ⇒ B` is not proved: `A` turns invariance under strong bundle equivalences into invariance
  under generalized isomorphisms, but `B` does not provide the former, and `A` does not either.
  The missing input is exactly Proposition 10.4.6 for `IsLRB`; with it as a hypothesis,
  `A ⇒ B` is immediate (`A_to_B_of_hyp`).  Proving it would be the strong bundle analogue of the
  transport argument of Proposition 10.1.9 (a natural representation transported along a strong
  bundle equivalence, and the lifted actions intertwined), i.e. new mathematics, not glue.
* `B ⇒ A` holds, but only because `A` is provable outright (`B_to_A` does not use `B`): from a
  representative `W ←Φ W'' →Ψ W'` with `Φ` (by definition) and `Ψ` (by `IsGeneralizedIso`)
  strong bundle equivalences, `Pr A ↔ Pr W'' ↔ Pr A'`.
-/

namespace RoundTrip.V10_61
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- The project's statement (universe at `0`). -/
def A : Prop := type_of% @Polyfold.SBLocalization.GenSBMap.iff_of_isGeneralizedIso.{0}

theorem A_holds : A := @Polyfold.SBLocalization.GenSBMap.iff_of_isGeneralizedIso.{0}

/-- `A ⇒ B` given Proposition 10.4.6 for B's (LR): invariance of `IsLRB` under strong bundle
equivalences.  This hypothesis is what neither side provides. -/
theorem A_to_B_of_hyp (hA : A)
    (h1046 : ∀ {C C' : SEP.{0}} (F : C ⟶ C'), SEP.equivalences F → (IsLRB C.E ↔ IsLRB C'.E)) :
    B := fun _ _ _ hf => hA (fun C => IsLRB C.E) h1046 hf

/-- `B ⇒ A`, proving `A` outright (the hypothesis is not used). -/
theorem B_to_A : B → A := by
  intro _ X X' Pr hPr f hf
  obtain ⟨D, -, hΨ⟩ := hf
  exact (hPr D.Φ D.isEquivalence_Φ).symm.trans (hPr D.Ψ hΨ)

#rt_check RoundTrip.V10_61.A_to_B_of_hyp [Polyfold.SBLocalization.GenSBMap.iff_of_isGeneralizedIso]
#rt_check RoundTrip.V10_61.B_to_A [Polyfold.SBLocalization.GenSBMap.iff_of_isGeneralizedIso]
#rt_overlap RoundTrip.V10_61.B_to_A [Polyfold.SBLocalization.GenSBMap.iff_of_isGeneralizedIso]

end RoundTrip.V10_61
