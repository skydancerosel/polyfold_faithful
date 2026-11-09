import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_40

set_option maxSynthPendingDepth 3

/-!
Round trip for V11_40 (the category `𝒫𝒞`, its class `E_𝒫𝒞`, diagrams and Definition 11.6.7;
2021 p. 561).

This is a definition item: `PC`, `PC.equivalences`, `PC.fibred`, `fibredFst`, `fibredSnd`,
`PC.Diagram`, `Diagram.CommonRefinement`, `HasCommonRefinement` and the witnesses `pair`,
`point`, `diagram`, `fibredPair`, `diagram'` are vocabulary.  `A` (universe `0`) is the conjunction
of the three listed theorems: `ProperCoveringHom.comp_assoc` (composition of functors between
proper coverings is associative, used for the category), and the witnesses
`equivalences_pairToPoint` (`pairToPointCovering ∈ E_𝒫𝒞`) and `isEquivalence_fibredFst`
(`π₁ : pair ×_point pair → pair` is an equivalence).  None of them is part of the definitions.

`B` says the project's `PC`, its morphisms, identities, composition, `E_𝒫𝒞`, diagrams and common
refinements are the text's.  The content is `B` itself, proved outright (`B_holds`): the objects
of `PC` are exactly the proper coverings, `A ⟶ B` is `ProperCoveringHom A.F B.F`, the identity is
`(1_Y, 1_X)` and the composition componentwise (all `rfl`), `PC.equivalences f` is the structure
`IsEquivalence f` (= `B`'s conjunction `IsEquivB`), a `Diagram` is exactly a triple `(A, Γ, ε)` with
`Γ` an equivalence (structure eta), and `HasCommonRefinement` is `B`'s
`HasCommonRefinementB` (`NaturallyEquivalent` is `Nonempty` of the project's `NatTrans`, the
pair `(τ_Y, τ_X)` with (11.20); `(Γ.comp H).Ψ = Γ.Ψ.comp H.Ψ` by `rfl`).

Both implications are therefore vacuous: `A_to_B := fun _ => B_holds`, and `B_to_A` re-proves the
three side theorems without `B` (which says nothing about associativity of `ProperCoveringHom.comp`
for arbitrary functors, nor about the examples): `comp_assoc` by `ext rfl rfl`, the two witnesses
by the project's one-step proofs (`isEquivalence_pairToPointCovering`, Theorem 11.6.6's last
claim `theorem_11_6_6`, which is not banned here).
-/

namespace RoundTrip.V11_40
open Polyfold CategoryTheory

/-- The project's statements, universe `0`. -/
def A : Prop :=
  type_of% @Polyfold.ProperCoveringHom.comp_assoc.{0} ∧
  type_of% @Polyfold.PC.Examples.equivalences_pairToPoint ∧
  type_of% @Polyfold.PC.Examples.isEquivalence_fibredFst

theorem A_holds : A :=
  ⟨@ProperCoveringHom.comp_assoc, PC.Examples.equivalences_pairToPoint,
    PC.Examples.isEquivalence_fibredFst⟩

/-- **The project's definitions are the text's** (`B`, proved outright). -/
theorem B_holds : B := by
  refine ⟨fun c => c.isProperCovering, fun Y X F hF => ⟨⟨Y, X, F, hF⟩, rfl, rfl, HEq.rfl⟩,
    fun A B => rfl, fun A => ⟨rfl, rfl, rfl, rfl⟩, fun A B C f g => ⟨rfl, rfl, rfl, rfl⟩,
    fun A B f => ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩, fun F F' => ⟨?_, ?_⟩, ?_⟩
  · -- a diagram is determined by `(A, Γ, ε)`
    rintro ⟨A, Γ, hΓ, ε⟩ ⟨A', Γ', hΓ', ε'⟩ h
    simp only [diagDataB, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · -- and every `(A, Γ, ε)` with `Γ ∈ E_𝒫𝒞` is a diagram
    ext p
    refine ⟨?_, fun h => ⟨⟨p.1, p.2.1, ⟨h.1, h.2.1, h.2.2⟩, p.2.2⟩, rfl⟩⟩
    rintro ⟨d, rfl⟩
    exact ⟨d.isEquivalence_Γ.1, d.isEquivalence_Γ.2, d.isEquivalence_Γ.3⟩
  · -- common refinements
    intro F F' d d'
    constructor
    · rintro ⟨⟨A'', H, H', hH, hH', ⟨τ⟩, ⟨σ⟩⟩⟩
      exact ⟨A'', H, H', ⟨hH.1, hH.2, hH.3⟩, ⟨hH'.1, hH'.2, hH'.3⟩, ⟨τ.τY, τ.τX, τ.comm⟩,
        ⟨σ.τY, σ.τX, σ.comm⟩⟩
    · rintro ⟨A'', H, H', hH, hH', ⟨τY, τX, hτ⟩, ⟨σY, σX, hσ⟩⟩
      exact ⟨⟨A'', H, H', ⟨hH.1, hH.2.1, hH.2.2⟩, ⟨hH'.1, hH'.2.1, hH'.2.2⟩, ⟨⟨τY, τX, hτ⟩⟩,
        ⟨⟨σY, σX, hσ⟩⟩⟩⟩

/-- Vacuous: `B` holds outright. -/
theorem A_to_B (_hA : A) : B := B_holds

/-- Vacuous: `A`'s three side theorems re-proved without `B`. -/
theorem B_to_A (_hB : B) : A := by
  open CoveringEquivalence.Examples PC.Examples in
  refine ⟨fun Γ₃ Γ₂ Γ₁ => ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl),
    isEquivalence_pairToPointCovering, ?_⟩
  open CoveringEquivalence.Examples PC.Examples in
  exact (ProperCoveringHom.theorem_11_6_6 _ _ pair.isProperCovering point.isProperCovering
    pair.isProperCovering isEquivalence_pairToPointCovering).2.2.2.2 isEquivalence_pairToPointCovering

#rt_check RoundTrip.V11_40.B_holds [Polyfold.ProperCoveringHom.comp_assoc,
  Polyfold.PC.Examples.equivalences_pairToPoint, Polyfold.PC.Examples.isEquivalence_fibredFst]
#rt_check RoundTrip.V11_40.A_to_B [Polyfold.ProperCoveringHom.comp_assoc,
  Polyfold.PC.Examples.equivalences_pairToPoint, Polyfold.PC.Examples.isEquivalence_fibredFst]
#rt_check RoundTrip.V11_40.B_to_A [Polyfold.ProperCoveringHom.comp_assoc,
  Polyfold.PC.Examples.equivalences_pairToPoint, Polyfold.PC.Examples.isEquivalence_fibredFst]
#rt_overlap RoundTrip.V11_40.B_to_A [Polyfold.ProperCoveringHom.comp_assoc,
  Polyfold.PC.Examples.equivalences_pairToPoint, Polyfold.PC.Examples.isEquivalence_fibredFst]

end RoundTrip.V11_40
