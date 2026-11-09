import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_38

/-! Round trip for V10_38 (2021 Lemma 10.3.6, p. 488; 2017: Lemma 10.5, p. 351: the orbit map
`|d| = |Φ| ∘ |F|⁻¹` of a diagram is invariant under refinement).

The item lists the definition `Diagram.orbitMap` (vocabulary) and six theorems.  `A` is the
conjunction of their types, universes at `0`: `Diagram.continuous_orbitMap`,
`Diagram.orbitMap_orbitMap_F` (`|d| ∘ |F| = |Φ|`), `Diagram.lemma_10_3_6` (the lemma),
`Diagram.Equiv.orbitMap_eq` (equivalent diagrams have the same orbit map), and two general
lemmas on ep-functors: `EpFunctor.NaturallyEquivalent.orbitMap_eq` (`F ≃ G ⇒ |F| = |G|`) and
`EpFunctor.orbitMap_comp` (`|G ∘ F| = |G| ∘ |F|`).

`B` (at universe `0`): if `d'` refines `d` (the blind author's `IsRefinementB`, definitionally
the project's `Diagram.IsRefinement`), then `orbB d = orbB d'`, where `orbB` is definitionally
the project's `Diagram.orbitMap` (the same term `|Φ| ∘ (IsHomeomorph.homeomorph |F| _).symm`).

* `A ⇒ B`: `lemma_10_3_6` from `A`.
* `B ⇒ A`: `lemma_10_3_6` is `B`; `Equiv.orbitMap_eq` is `B` applied to both legs of a common
  refinement; `NaturallyEquivalent.orbitMap_eq` also follows from `B`: for `F ≃ G : X → Y`, the
  diagram `X ←1 X →G Y` refines `X ←1 X →F Y` (by `1_X`), so `|F| ∘ |1|⁻¹ = |G| ∘ |1|⁻¹`.
  `continuous_orbitMap`, `orbitMap_orbitMap_F` and `EpFunctor.orbitMap_comp` are not about
  refinements and are re-proved outright (the project's short proofs, with non-item lemmas).
-/

namespace RoundTrip.V10_38
open Polyfold Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.continuous_orbitMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.orbitMap_orbitMap_F.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.lemma_10_3_6.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.orbitMap_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.orbitMap_comp.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Diagram.continuous_orbitMap.{0}, @Diagram.orbitMap_orbitMap_F.{0}, @Diagram.lemma_10_3_6.{0},
    @Diagram.Equiv.orbitMap_eq.{0}, @EpFunctor.NaturallyEquivalent.orbitMap_eq.{0, 0},
    @EpFunctor.orbitMap_comp.{0, 0, 0}⟩

/-- Glue: `orbB` is the project's `Diagram.orbitMap` (definitional). -/
theorem orbB_eq {X Y : EP.{0}} (d : Diagram X Y) : orbB d = d.orbitMap := rfl

theorem A_to_B : A → B.{0} := by
  rintro ⟨-, -, h3, -⟩ X Y d d' h
  rw [orbB_eq, orbB_eq]
  exact h3 h

theorem B_to_A : B.{0} → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- re-proved outright
    intro X Y d
    exact d.Φ.continuous_orbitMap.comp (Homeomorph.continuous _)
  · -- re-proved outright
    intro X Y d q
    change d.Φ.orbitMap ((IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).symm
      ((IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap) q)) = _
    rw [Homeomorph.symm_apply_apply]
  · -- `B`
    intro X Y d d' h
    exact hB X Y d d' h
  · -- `B`, twice
    rintro X Y d d' ⟨d'', h₁, h₂⟩
    exact (hB X Y d d'' h₁).trans (hB X Y d' d'' h₂).symm
  · -- `B`, for `X ←1 X →F Y` and its refinement `X ←1 X →G Y`
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G h
    let X' : EP.{0} := EP.mk Obj Mor X
    let Y' : EP.{0} := EP.mk Obj' Mor' Y
    let d : Diagram X' X' := ⟨X', EpFunctor.id X, EpFunctor.IsEquivalence.id X, EpFunctor.id X⟩
    let dF : Diagram X' Y' := ⟨X', EpFunctor.id X, EpFunctor.IsEquivalence.id X, F⟩
    let dG : Diagram X' Y' := ⟨X', EpFunctor.id X, EpFunctor.IsEquivalence.id X, G⟩
    have hr : IsRefinementB dG dF :=
      ⟨EpFunctor.id X, EpFunctor.IsEquivalence.id X, EpFunctor.NaturallyEquivalent.refl _, h⟩
    have he := hB X' Y' dF dG hr
    funext q
    have hq := congrFun he ((EpFunctor.id X).orbitMap q)
    change F.orbitMap ((IsHomeomorph.homeomorph _ dF.isEquivalence_F.isHomeomorph_orbitMap).symm
        ((IsHomeomorph.homeomorph _ dF.isEquivalence_F.isHomeomorph_orbitMap) q)) =
      G.orbitMap ((IsHomeomorph.homeomorph _ dG.isEquivalence_F.isHomeomorph_orbitMap).symm
        ((IsHomeomorph.homeomorph _ dG.isEquivalence_F.isHomeomorph_orbitMap) q)) at hq
    -- one rewrite handles both sides (the two homeomorphisms coincide)
    rw [Homeomorph.symm_apply_apply] at hq
    exact hq
  · -- re-proved outright
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ X Y Z G F
    funext q
    induction q using Quotient.inductionOn with | h x => rfl

#rt_check RoundTrip.V10_38.A_to_B [Polyfold.EPLocalization.Diagram.continuous_orbitMap,
  Polyfold.EPLocalization.Diagram.orbitMap_orbitMap_F, Polyfold.EPLocalization.Diagram.lemma_10_3_6,
  Polyfold.EPLocalization.Diagram.Equiv.orbitMap_eq,
  Polyfold.EpFunctor.NaturallyEquivalent.orbitMap_eq, Polyfold.EpFunctor.orbitMap_comp]
#rt_check RoundTrip.V10_38.B_to_A [Polyfold.EPLocalization.Diagram.continuous_orbitMap,
  Polyfold.EPLocalization.Diagram.orbitMap_orbitMap_F, Polyfold.EPLocalization.Diagram.lemma_10_3_6,
  Polyfold.EPLocalization.Diagram.Equiv.orbitMap_eq,
  Polyfold.EpFunctor.NaturallyEquivalent.orbitMap_eq, Polyfold.EpFunctor.orbitMap_comp]
#rt_overlap RoundTrip.V10_38.B_to_A [Polyfold.EPLocalization.Diagram.continuous_orbitMap,
  Polyfold.EPLocalization.Diagram.orbitMap_orbitMap_F, Polyfold.EPLocalization.Diagram.lemma_10_3_6,
  Polyfold.EPLocalization.Diagram.Equiv.orbitMap_eq,
  Polyfold.EpFunctor.NaturallyEquivalent.orbitMap_eq, Polyfold.EpFunctor.orbitMap_comp]

end RoundTrip.V10_38
