import Polyfold
/-! Blind formalization of V10_46 (the Springer 2021 book, Part II, §10.3, Theorem 10.3.15,
p. 492; 2017: Theorem 10.6, p. 355): the orbit space functor.

Text: a functor `|·| : EP(E⁻¹) → TOP`, `X ↦ |X|`, `[d] ↦ |Φ| ∘ |F|⁻¹`.

Choices:
- `EP(E⁻¹)` is the project's category `EPLoc` (compared with Definition 10.3.12 in
  `RoundTrip/Blind/V10_44.lean`); `EP.{u}`, any universe `u`.  `TOP` is the category of
  topological spaces and continuous maps; `|X|` is the project's orbit space `OrbitSpace` (a
  quotient) with Mathlib's quotient topology.
- The map on morphisms: the project's `EPLoc.orbitMap f` (docstring: `|f|` of Definition 10.3.7);
  B pins it down by (1) `|[d]| = |Φ| ∘ |F|⁻¹` (my `orbB d`, with `|F|⁻¹` the inverse of the
  homeomorphism `|F|` of Definition 10.1.1 (2), as in `RoundTrip/Blind/V10_38.lean`).
- "A functor `EP(E⁻¹) → TOP` with these values" is stated elementarily (to avoid casts along
  `G.obj X = TopCat.of |X|`): (2) each `|f|` is continuous (a morphism of `TOP`), (3)
  `|1_X| = id`, (4) `|f ≫ g| = |g| ∘ |f|` for the composition of `EPLoc` (Mathlib order:
  `f ≫ g` is the text's `g ∘ f`).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_46
open Polyfold Polyfold.EPLocalization CategoryTheory

universe u

/-- `|d| = |Φ| ∘ |F|⁻¹ : |X| → |Y|`, `|F|` being a homeomorphism as `F` is an equivalence. -/
noncomputable def orbB {X Y : EP.{u}} (d : Diagram X Y) : X.X.OrbitSpace → Y.X.OrbitSpace :=
  d.Φ.orbitMap ∘
    (IsHomeomorph.homeomorph d.F.orbitMap d.isEquivalence_F.isHomeomorph_orbitMap).symm

/-- `X ↦ |X|`, `[d] ↦ |Φ| ∘ |F|⁻¹` is a functor from `EP(E⁻¹)` to topological spaces. -/
def B : Prop :=
  (∀ (X Y : EP.{u}) (d : Diagram X Y), EPLoc.orbitMap (EPLoc.homMk d) = orbB d) ∧
  (∀ (X Y : EP.{u}) (f : EPLoc.of X ⟶ EPLoc.of Y), Continuous (EPLoc.orbitMap f)) ∧
  (∀ X : EP.{u}, EPLoc.orbitMap (𝟙 (EPLoc.of X)) = id) ∧
  (∀ (X Y Z : EP.{u}) (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of Z),
      EPLoc.orbitMap (f ≫ g) = EPLoc.orbitMap g ∘ EPLoc.orbitMap f)

end RoundTrip.V10_46
