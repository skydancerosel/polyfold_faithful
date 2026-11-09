import Polyfold
/-! Blind formalization of V10_43 (the Springer 2021 book, Part II, §10.3, Proposition 10.3.11,
p. 490; 2017: Proposition 10.6, p. 353): `|g ∘ f| = |g| ∘ |f|`.

Text: for generalized maps `f : X → Y`, `g : Y → Z`, `|g ∘ f| = |g| ∘ |f|`.

Choices:
- Setting: `EP.{u}`, any universe `u`, and the project's `Diagram` (`RoundTrip/Blind/V10_37.lean`).
- A generalized map is a class `f = [d]` (Definition 10.3.9); B quantifies over representatives
  `d : X → Y`, `e : Y → Z` (every generalized map has one).  `g ∘ f = [e] ∘ [d]` is the class of
  the composite diagram `X ← A ×_Y B → Z` of Theorem 10.3.8, the project's `Diagram.comp d e`
  (see `RoundTrip/Blind/V10_40.lean`).  `|[d]| = |Φ| ∘ |F|⁻¹` for any representative
  (Definition 10.3.7): my `orbB d`, with `|F|⁻¹` the inverse of the homeomorphism `|F|` of
  Definition 10.1.1 (2) (`RoundTrip/Blind/V10_38.lean`); the project's orbit maps of diagrams
  and of `EPLoc` morphisms are not used.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_43
open Polyfold Polyfold.EPLocalization

universe u

/-- `|d| = |Φ| ∘ |F|⁻¹ : |X| → |Y|`, `|F|` being a homeomorphism as `F` is an equivalence. -/
noncomputable def orbB {X Y : EP.{u}} (d : Diagram X Y) : X.X.OrbitSpace → Y.X.OrbitSpace :=
  d.Φ.orbitMap ∘
    (IsHomeomorph.homeomorph d.F.orbitMap d.isEquivalence_F.isHomeomorph_orbitMap).symm

/-- `|[e] ∘ [d]| = |[e]| ∘ |[d]|`. -/
def B : Prop :=
  ∀ (X Y Z : EP.{u}) (d : Diagram X Y) (e : Diagram Y Z), orbB (d.comp e) = orbB e ∘ orbB d

end RoundTrip.V10_43
