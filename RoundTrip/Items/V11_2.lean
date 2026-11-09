import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_2

/-! Round trip for V11_2 (2021 Proposition 11.1.2, p. 522; 2017: Proposition 11.1, p. 376: a
generalized isomorphism preserves the degeneracy index).

The item lists the definition `EpGroupoid.degIndexOrbit` (vocabulary, `d_{|X|}`, a
`Quotient.lift` of `d_X`) and four theorems; `A` is the conjunction of their types, all universes
at `0` (`B` lives in `EP.{0}`): `EPLoc.proposition_11_1_2` (the proposition, plus
`d_{|X|}(|x|) = d_{|Y|}(|y|)`), `EPLoc.degIndexOrbit_orbitMap` (`d_{|Y|} ∘ |f| = d_{|X|}` for a
generalized isomorphism), `Diagram.degIndexOrbit_orbitMap` (the same for a diagram with both legs
equivalences) and `EpFunctor.IsEquivalence.degIndexOrbit_orbitMap` (the same for `|Φ|`, `Φ` an
equivalence between unbundled ep-groupoids).

* `A_to_B`: `IsIso f` is `IsGeneralizedIso f` (`isGeneralizedIso_iff_isIso`), then the first half
  of `proposition_11_1_2` with `x = x₀`, `y = y₀`.
* `B_to_A`: every conjunct from `B`.  `d_{|X|}(π x) = d_X(x)` is `rfl`; for the orbit-map
  conjuncts pick representatives (`surjective_π`).  A diagram with `Φ` an equivalence gives an
  isomorphism `[d]` (`theorem_10_3_10`); an equivalence `Φ : X → Y` gives the isomorphism
  `i(Φ) = [X ←1 X →Φ Y]` between the bundled `EP.mk _ _ X`, `EP.mk _ _ Y`, with
  `|i(Φ)|(|x|) = |Φ(x)|` (`Diagram.orbitMap_orbitMap_F`). -/

namespace RoundTrip.V11_2
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.proposition_11_1_2.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.degIndexOrbit_orbitMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.degIndexOrbit_orbitMap.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.proposition_11_1_2.{0},
    @Polyfold.EPLocalization.EPLoc.degIndexOrbit_orbitMap.{0},
    @Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap.{0},
    @Polyfold.EpFunctor.IsEquivalence.degIndexOrbit_orbitMap.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hP, -, -, -⟩ X Y f hf x₀ y₀ h
  exact (hP ((EPLoc.isGeneralizedIso_iff_isIso f).2 hf) h).1 x₀ y₀ rfl rfl

theorem B_to_A : B → A := by
  intro hB
  -- the orbit-map form for generalized isomorphisms
  have h2 : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      ∀ q, Y.X.degIndexOrbit (EPLoc.orbitMap f q) = X.X.degIndexOrbit q := by
    intro X Y f hf q
    obtain ⟨x, rfl⟩ := X.X.surjective_π q
    obtain ⟨y, hy⟩ := Y.X.surjective_π (EPLoc.orbitMap f (X.X.π x))
    rw [← hy]
    exact (hB X Y f ((EPLoc.isGeneralizedIso_iff_isIso f).1 hf) x y hy.symm).symm
  refine ⟨?_, h2, ?_, ?_⟩
  · intro X Y f hf x y h
    have hI := (EPLoc.isGeneralizedIso_iff_isIso f).1 hf
    refine ⟨fun x₀ y₀ hx hy => hB X Y f hI x₀ y₀ ?_, hB X Y f hI x y h⟩
    change EPLoc.orbitMap f (X.X.π x₀) = Y.X.π y₀
    rw [hx, hy, h]
  · intro X Y d hΦ q
    exact h2 ((EPLoc.theorem_10_3_10 d).1.2 hΦ) q
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF q
    obtain ⟨x, rfl⟩ := X.surjective_π q
    let X' : EP.{0} := EP.mk Obj Mor X
    let Y' : EP.{0} := EP.mk Obj' Mor' Y
    let F' : X' ⟶ Y' := F
    have hI : IsIso (EPLoc.localizationFunctor.map F') :=
      (EPLoc.isIso_homMk_iff (Diagram.ofFunctor F')).2 hF
    have hπ : EPLoc.orbitMap (EPLoc.localizationFunctor.map F') (X.π x) = Y.π (F.obj x) :=
      (Diagram.ofFunctor F').orbitMap_orbitMap_F (X.π x)
    exact (hB X' Y' _ hI x (F.obj x) hπ).symm

#rt_check RoundTrip.V11_2.A_to_B [Polyfold.EPLocalization.EPLoc.proposition_11_1_2,
  Polyfold.EPLocalization.EPLoc.degIndexOrbit_orbitMap,
  Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap,
  Polyfold.EpFunctor.IsEquivalence.degIndexOrbit_orbitMap]
#rt_check RoundTrip.V11_2.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_11_1_2,
  Polyfold.EPLocalization.EPLoc.degIndexOrbit_orbitMap,
  Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap,
  Polyfold.EpFunctor.IsEquivalence.degIndexOrbit_orbitMap]
#rt_overlap RoundTrip.V11_2.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_11_1_2,
  Polyfold.EPLocalization.EPLoc.degIndexOrbit_orbitMap,
  Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap,
  Polyfold.EpFunctor.IsEquivalence.degIndexOrbit_orbitMap]

end RoundTrip.V11_2
