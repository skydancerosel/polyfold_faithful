import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_20

/-! Round trip for V1_20 (Theorem 1.21, the chain rule).

`A` is the conjunction of the types of `Polyfold.IsSc1With.hasFDerivWithinAt_comp`,
`Polyfold.IsSc1With.comp`, `Polyfold.theorem_1_21'`, `Polyfold.theorem_1_21`,
`Polyfold.IsSck.comp`, `Polyfold.IsSck.comp_of_isRelOpenInQuadrant` and `Polyfold.IsScSmooth.comp`.
None has universe parameters (`ScBanach` lives in `Type`).

`A → B` is `theorem_1_21` (plus the trivial `(g ∘ f)(U) ⊆ W`).

`B → A` fails: `A` also contains the chain rule on arbitrary `IsScDomain`s (`theorem_1_21'`,
`IsSck.comp`, `IsScSmooth.comp`) and for an explicit derivative family on any `U` with `V₁`
open ∩ convex (`IsSc1With.comp`, `hasFDerivWithinAt_comp`), and the iterated sc^k chain rule.
What `B` does give is `theorem_1_21` itself (`B_to_theorem_1_21`, taking `W = Q = G₀`). -/

namespace RoundTrip.V1_20
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSc1With.hasFDerivWithinAt_comp) ∧ (type_of% @Polyfold.IsSc1With.comp) ∧
    (type_of% @Polyfold.theorem_1_21') ∧ (type_of% @Polyfold.theorem_1_21) ∧
    (type_of% @Polyfold.IsSck.comp) ∧ (type_of% @Polyfold.IsSck.comp_of_isRelOpenInQuadrant) ∧
    (type_of% @Polyfold.IsScSmooth.comp)

theorem A_holds : A :=
  ⟨@Polyfold.IsSc1With.hasFDerivWithinAt_comp, @Polyfold.IsSc1With.comp, @Polyfold.theorem_1_21',
    @Polyfold.theorem_1_21, @Polyfold.IsSck.comp, @Polyfold.IsSck.comp_of_isRelOpenInQuadrant,
    @Polyfold.IsScSmooth.comp⟩

theorem A_to_B : A → B := by
  intro hA E F G C U D V Q W f g hU hV _ hfV hgW hf hg
  exact ⟨hgW.comp hfV, hA.2.2.2.1 hU hV hf hg hfV⟩

/-- What `B` does give: the conjunct `theorem_1_21` of `A` (relatively open subsets of partial
quadrants, sc¹). -/
theorem B_to_theorem_1_21 (hB : B) : type_of% @Polyfold.theorem_1_21 := by
  intro E F G U V f g C D hU hV hf hg hfV
  have hW : IsRelOpenInQuadrant G Set.univ Set.univ :=
    ⟨isPartialQuadrant_univ G, Set.univ, isOpen_univ, (Set.univ_inter _).symm⟩
  exact (hB E F G C U D V Set.univ Set.univ f g hU hV hW hfV (Set.mapsTo_univ _ _) hf hg).2

#rt_check RoundTrip.V1_20.A_to_B [Polyfold.IsSc1With.hasFDerivWithinAt_comp,
  Polyfold.IsSc1With.comp, Polyfold.theorem_1_21', Polyfold.theorem_1_21, Polyfold.IsSck.comp,
  Polyfold.IsSck.comp_of_isRelOpenInQuadrant, Polyfold.IsScSmooth.comp]
#rt_check RoundTrip.V1_20.B_to_theorem_1_21 [Polyfold.IsSc1With.hasFDerivWithinAt_comp,
  Polyfold.IsSc1With.comp, Polyfold.theorem_1_21', Polyfold.theorem_1_21, Polyfold.IsSck.comp,
  Polyfold.IsSck.comp_of_isRelOpenInQuadrant, Polyfold.IsScSmooth.comp]

end RoundTrip.V1_20
