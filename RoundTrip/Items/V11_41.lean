import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_41

set_option maxSynthPendingDepth 3

/-!
Round trip for V11_41 (Proposition 11.6.8: having a common refinement is transitive; 2021 p. 562).

`A` (universe `0`) is the conjunction of the four listed theorems: `PC.proposition_11_6_8`
(transitivity of `HasCommonRefinement`), `Diagram.hasCommonRefinement_equivalence` (with
reflexivity and symmetry, an equivalence relation), and the witnesses
`hasCommonRefinement_diagram` (`diagram ≈ diagram'`) and `hasCommonRefinement_diagram_diagram`
(`diagram ≈ diagram`, obtained from Proposition 11.6.8).

`B`: for `F, F' : PC.{0}` and diagrams `d, d', d''`, `HasCommonRefinementB d d'` and
`HasCommonRefinementB d' d''` give `HasCommonRefinementB d d''`, with `B`'s own reading of
Definition 11.6.7 (equivalences `H`, `H'` as the conjunction `IsEquivB`, natural equivalences as
pairs of `EpNatTrans` with (11.20), composition componentwise).

The glue is `hasCommonRefinementB_iff`: `B`'s `HasCommonRefinementB` is the project's
`HasCommonRefinement` (the same check as in V11_40: `IsEquivalence` is the structure of `IsEquivB`'s
three conjuncts, `NaturallyEquivalent` is `Nonempty` of the project's `NatTrans`, and
`(Γ.comp H).Ψ = Γ.Ψ.comp H.Ψ` by `rfl`).

* `A ⇒ B` (`A_to_B`): `proposition_11_6_8` through the iff.
* `B ⇒ A` (`B_to_A`): `proposition_11_6_8` from `B` through the iff; the equivalence relation
  with transitivity from `B` and reflexivity (`A'' = A`, `H = H' = 1`) and symmetry (swap `H`, `H'`)
  proved here; `hasCommonRefinement_diagram` re-proved outright (a witness, not a consequence of
  transitivity: the project's term, with Theorem 11.6.6 (3), not banned here);
  `hasCommonRefinement_diagram_diagram` from `B` applied to it and its symmetric.
-/

namespace RoundTrip.V11_41
open Polyfold

/-- The project's statements, universe `0`. -/
def A : Prop :=
  type_of% @Polyfold.PC.proposition_11_6_8.{0} ∧
  type_of% @Polyfold.PC.Diagram.hasCommonRefinement_equivalence.{0} ∧
  type_of% @Polyfold.PC.Examples.hasCommonRefinement_diagram ∧
  type_of% @Polyfold.PC.Examples.hasCommonRefinement_diagram_diagram

theorem A_holds : A :=
  ⟨@PC.proposition_11_6_8, @PC.Diagram.hasCommonRefinement_equivalence,
    PC.Examples.hasCommonRefinement_diagram, PC.Examples.hasCommonRefinement_diagram_diagram⟩

/-- `B`'s reading of Definition 11.6.7 is the project's. -/
theorem hasCommonRefinementB_iff {F F' : PC.{0}} (d d' : F.Diagram F') :
    HasCommonRefinementB d d' ↔ d.HasCommonRefinement d' := by
  constructor
  · rintro ⟨A'', H, H', hH, hH', ⟨τY, τX, hτ⟩, ⟨σY, σX, hσ⟩⟩
    exact ⟨⟨A'', H, H', ⟨hH.1, hH.2.1, hH.2.2⟩, ⟨hH'.1, hH'.2.1, hH'.2.2⟩, ⟨⟨τY, τX, hτ⟩⟩,
      ⟨⟨σY, σX, hσ⟩⟩⟩⟩
  · rintro ⟨⟨A'', H, H', hH, hH', ⟨τ⟩, ⟨σ⟩⟩⟩
    exact ⟨A'', H, H', ⟨hH.1, hH.2, hH.3⟩, ⟨hH'.1, hH'.2, hH'.3⟩, ⟨τ.τY, τ.τX, τ.comm⟩,
      ⟨σ.τY, σ.τX, σ.comm⟩⟩

theorem A_to_B (hA : A) : B := by
  intro F F' d d' d'' h h'
  rw [hasCommonRefinementB_iff] at h h' ⊢
  exact hA.1 h h'

theorem B_to_A (hB : B) : A := by
  have trans : ∀ {F F' : PC.{0}} {d d' d'' : F.Diagram F'}, d.HasCommonRefinement d' →
      d'.HasCommonRefinement d'' → d.HasCommonRefinement d'' := fun {F F' d d' d''} h h' =>
    (hasCommonRefinementB_iff d d'').1 (hB F F' d d' d''
      ((hasCommonRefinementB_iff d d').2 h) ((hasCommonRefinementB_iff d' d'').2 h'))
  have symm : ∀ {F F' : PC.{0}} {d d' : F.Diagram F'}, d.HasCommonRefinement d' →
      d'.HasCommonRefinement d := fun ⟨c⟩ =>
    ⟨⟨c.A'', c.H', c.H, c.isEquivalence_H', c.isEquivalence_H,
      ProperCoveringHom.naturallyEquivalent_equivalence.symm c.natEquiv_Γ,
      ProperCoveringHom.naturallyEquivalent_equivalence.symm c.natEquiv_ε⟩⟩
  -- the witness `diagram ≈ diagram'` (not a consequence of transitivity; the project's term)
  have hdiag : PC.Examples.diagram.HasCommonRefinement PC.Examples.diagram' := by
    open CoveringEquivalence.Examples PC.Examples ProperCoveringHom in
    exact ⟨⟨fibredPair,
      PC.fibredFst pairToPointCovering isEquivalence_pairToPointCovering pairToPointCovering,
      ProperCoveringHom.id _, isEquivalence_fibredFst, IsEquivalence.id,
      naturallyEquivalent_equivalence.refl _,
      (theorem_11_6_6 _ _ pair.isProperCovering point.isProperCovering pair.isProperCovering
        isEquivalence_pairToPointCovering).2.2.1⟩⟩
  refine ⟨fun h h' => trans h h', ?_, hdiag, trans hdiag (symm hdiag)⟩
  exact
    { refl := fun d => ⟨⟨d.A, ProperCoveringHom.id _, ProperCoveringHom.id _,
        ProperCoveringHom.IsEquivalence.id, ProperCoveringHom.IsEquivalence.id,
        ProperCoveringHom.naturallyEquivalent_equivalence.refl _,
        ProperCoveringHom.naturallyEquivalent_equivalence.refl _⟩⟩
      symm := symm
      trans := trans }

#rt_check RoundTrip.V11_41.A_to_B [Polyfold.PC.proposition_11_6_8,
  Polyfold.PC.Diagram.hasCommonRefinement_equivalence,
  Polyfold.PC.Examples.hasCommonRefinement_diagram,
  Polyfold.PC.Examples.hasCommonRefinement_diagram_diagram]
#rt_check RoundTrip.V11_41.B_to_A [Polyfold.PC.proposition_11_6_8,
  Polyfold.PC.Diagram.hasCommonRefinement_equivalence,
  Polyfold.PC.Examples.hasCommonRefinement_diagram,
  Polyfold.PC.Examples.hasCommonRefinement_diagram_diagram]
#rt_overlap RoundTrip.V11_41.B_to_A [Polyfold.PC.proposition_11_6_8,
  Polyfold.PC.Diagram.hasCommonRefinement_equivalence,
  Polyfold.PC.Examples.hasCommonRefinement_diagram,
  Polyfold.PC.Examples.hasCommonRefinement_diagram_diagram]

end RoundTrip.V11_41
