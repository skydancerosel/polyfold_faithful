import Polyfold
/-! Blind formalization of V10_38 (the Springer 2021 book, Part II, §10.3, Lemma 10.3.6, p. 488;
2017: Lemma 10.5, p. 351): the orbit map of a diagram is invariant under refinement.

Text: if `H : d' → d` is a refinement, then `|d| = |d'|`, for `|d| = |Φ| ∘ |F|⁻¹`.

Choices:
- Setting: the project's bundled ep-groupoids `EP.{u}` (any universe `u`) and diagrams
  `d : X ←F A →Φ Y`, the project's `EPLocalization.Diagram X Y` (`#print`ed: `A`, `F`, a proof
  `isEquivalence_F` that `F` is an equivalence, `Φ`), as in `RoundTrip/Blind/V10_37.lean`.
- Refinement (2021 Definition 10.3.1): my `IsRefinementB d' d`, an equivalence `H : A' → A`
  (`EpFunctor.IsEquivalence`) with (sc-smooth) natural transformations `F ∘ H ⇒ F'`,
  `Φ ∘ H ⇒ Φ'` (`EpNatTrans`), copied from `RoundTrip/Blind/V10_37.lean`; the project's
  `Diagram.IsRefinement` is not used.  The refining map `H` is existentially quantified (the
  lemma does not depend on it).
- `|d| = |Φ| ∘ |F|⁻¹` (my `orbB`): `|F|`, `|Φ|` are the induced maps of orbit spaces
  (`GroupoidFunctor.orbitMap` through `EpFunctor.toGroupoidFunctor`; `|X|` is the project's
  `OrbitSpace`, a quotient), and `|F|⁻¹` is the inverse of the homeomorphism `|F|` given by
  Definition 10.1.1 (2) (the field `isHomeomorph_orbitMap` of `isEquivalence_F`), so no junk
  value occurs.  The project's `Diagram.orbitMap` is not used.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_38
open Polyfold Polyfold.EPLocalization

universe u

/-- `d'` is a refinement of `d`: an equivalence `H : A' → A` with natural transformations
`F ∘ H ⇒ F'` and `Φ ∘ H ⇒ Φ'`. -/
def IsRefinementB {X Y : EP.{u}} (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- `|d| = |Φ| ∘ |F|⁻¹ : |X| → |Y|`, `|F|` being a homeomorphism as `F` is an equivalence. -/
noncomputable def orbB {X Y : EP.{u}} (d : Diagram X Y) : X.X.OrbitSpace → Y.X.OrbitSpace :=
  d.Φ.orbitMap ∘
    (IsHomeomorph.homeomorph d.F.orbitMap d.isEquivalence_F.isHomeomorph_orbitMap).symm

/-- A refinement `d' → d` has the same orbit map: `|d| = |d'|`. -/
def B : Prop :=
  ∀ (X Y : EP.{u}) (d d' : Diagram X Y), IsRefinementB d' d → orbB d = orbB d'

end RoundTrip.V10_38
