import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_32

/-! Round trip for V10_32 (2021 §10.3, the properties (E1)–(E3) of the class `E`, p. 483;
2017 p. 347).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EPLocalization.isEquivalence_of_isIso` ((E1): an isomorphism of the
category `EP`, Mathlib's `IsIso`, is an equivalence), `EpFunctor.IsEquivalence.comp` ((E2)) and
`EpFunctor.proposition_10_1_5` ((E3) in the form "if `F ≃ G`, then `F` is an equivalence iff `G`
is one").

* `A_to_B`: (E1) bundles `X`, `Y` as objects of `EP` and turns B's componentwise inverse `G`
  into an `IsIso` instance (`EpFunctor.ext`); (E2) is `IsEquivalence.comp`; (E3) is either half
  of `proposition_10_1_5`, applied to `F ≃ G` or to `G ≃ F` (`NaturallyEquivalent` is
  `Nonempty (EpNatTrans _ _)` by definition).
* `B_to_A`: (E1) reads the inverse off `IsIso.out` and its two equations componentwise (as the
  project's proof does), then applies B's (E1); (E2) is B's (E2); (E3) both halves of the iff
  are B's (E3), once with `Or.inl`, once with `Or.inr`. -/

namespace RoundTrip.V10_32
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.isEquivalence_of_isIso.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.proposition_10_1_5.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.isEquivalence_of_isIso.{0},
    @Polyfold.EpFunctor.IsEquivalence.comp.{0, 0, 0},
    @Polyfold.EpFunctor.proposition_10_1_5.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, h2, h3⟩
  intro Obj Mor Obj' Mor' Obj'' Mor'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z
  refine ⟨fun F hF => ?_, fun F G hF hG => h2 hG hF, fun F G hF hFG => ?_⟩
  · obtain ⟨G, hGF₀, hGF₁, hFG₀, hFG₁⟩ := hF
    let X' : EP.{0} := EP.mk Obj Mor X
    let Y' : EP.{0} := EP.mk Obj' Mor' Y
    let F' : X' ⟶ Y' := F
    let G' : Y' ⟶ X' := G
    have : IsIso F' :=
      ⟨⟨G', EpFunctor.ext (funext fun x => hGF₀ x) (funext fun φ => hGF₁ φ),
        EpFunctor.ext (funext fun y => hFG₀ y) (funext fun ψ => hFG₁ ψ)⟩⟩
    exact h1 F'
  · rcases hFG with hFG | hFG
    · exact (h3 hFG).1 hF
    · exact (h3 hFG).2 hF

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro X Y F hF
    obtain ⟨G, hFG, hGF⟩ := hF.out
    have hGFo : ∀ x, G.obj (F.obj x) = x := fun x => congrArg (fun H : X ⟶ X => H.obj x) hFG
    have hFGo : ∀ y, F.obj (G.obj y) = y := fun y => congrArg (fun H : Y ⟶ Y => H.obj y) hGF
    have hGFm : ∀ φ, G.mor (F.mor φ) = φ := fun φ => congrArg (fun H : X ⟶ X => H.mor φ) hFG
    have hFGm : ∀ ψ, F.mor (G.mor ψ) = ψ := fun ψ => congrArg (fun H : Y ⟶ Y => H.mor ψ) hGF
    exact (hB X.Obj X.Mor Y.Obj Y.Mor X.Obj X.Mor X.X Y.X X.X).1 F ⟨G, hGFo, hGFm, hFGo, hFGm⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ X Y Z G F hG hF
    exact (hB Obj Mor Obj' Mor' Obj'' Mor'' X Y Z).2.1 F G hF hG
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G h
    exact ⟨fun hF => (hB Obj Mor Obj' Mor' Obj Mor X Y X).2.2 F G hF (Or.inl h),
      fun hG => (hB Obj Mor Obj' Mor' Obj Mor X Y X).2.2 G F hG (Or.inr h)⟩

#rt_check RoundTrip.V10_32.A_to_B [Polyfold.EPLocalization.isEquivalence_of_isIso,
  Polyfold.EpFunctor.IsEquivalence.comp, Polyfold.EpFunctor.proposition_10_1_5]
#rt_check RoundTrip.V10_32.B_to_A [Polyfold.EPLocalization.isEquivalence_of_isIso,
  Polyfold.EpFunctor.IsEquivalence.comp, Polyfold.EpFunctor.proposition_10_1_5]
#rt_overlap RoundTrip.V10_32.B_to_A [Polyfold.EPLocalization.isEquivalence_of_isIso,
  Polyfold.EpFunctor.IsEquivalence.comp, Polyfold.EpFunctor.proposition_10_1_5]

end RoundTrip.V10_32
