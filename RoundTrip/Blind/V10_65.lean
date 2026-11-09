import Polyfold
/-! Blind formalization of V10_65 (the Springer 2021 book, Part II, §10.3, Theorem 10.3.19,
pp. 493–494; 2017: Theorem 10.7, p. 355), stated literally.

Text: if one of `X`, `Y` has the local regularity property and `f, f' : X → Y` are generalized
isomorphisms with `|f| = |f'|`, then `f = f'`.  (2017: without the (LR) hypothesis.)

Choices:
- Setting: universe 0 (all spaces in `Type`), `X`, `Y` objects of the project's category
  `EPLoc.{0}` (`EP(E⁻¹)`, 2021 Definition 10.3.12; see `RoundTrip/Blind/V10_64.lean`), `f, f'`
  morphisms `X ⟶ Y` there (generalized maps, classes of diagrams); `f = f'` is equality of
  morphisms of `EP(E⁻¹)`, i.e. of classes.
- "generalized isomorphism": the project's `EPLoc.IsGeneralizedIso` (Definition 10.3.9, read with
  `#print`: a two-sided inverse in `EP(E⁻¹)`).
- "(LR)": the project's `EpGroupoid.IsLR` (2021 Definition 7.4.19, read with `#print`) of the
  underlying ep-groupoid; "one of `X`, `Y`": the disjunction.
- `|f| : |X| → |Y|`: the project's `EPLoc.orbitMap` (2021 Definition 10.3.7: `|Φ| ∘ |F|⁻¹` for any
  representative `X ←F A →Φ Y`); `|f| = |f'|` is equality of the functions
  `X.OrbitSpace → Y.OrbitSpace`.
- DOUBT (formalized literally anyway): as I read it the claim fails without effectiveness.  For
  `X = Y = ℤ/3 × ℝ ⇉ ℝ` (trivial action) (LR) holds (every `β` with `|β(y)| = |y|` is the identity,
  which is `ĝ` for every `g`), and `f = 1_X`, `f' = [X ←1 X →Inv X]` (`Inv(g, x) = (g⁻¹, x)`) are
  generalized isomorphisms with `|f| = |f'| = id`, but `Inv` is not naturally equivalent to the
  identity (a natural transformation `1 ⇒ Inv` would give `h g h⁻¹ = g⁻¹` in the abelian `ℤ/3`), so
  I expect `f ≠ f'`.  V10_66 adds an effective target.
-/
namespace RoundTrip.V10_65
open Polyfold Polyfold.EPLocalization

/-- **Theorem 10.3.19** (literal): with (LR) on one side, generalized isomorphisms with the same
orbit map are equal. -/
def B : Prop :=
  ∀ (X Y : EPLoc.{0}), (X.toEP.X.IsLR ∨ Y.toEP.X.IsLR) →
    ∀ f f' : X ⟶ Y, EPLoc.IsGeneralizedIso f → EPLoc.IsGeneralizedIso f' →
      EPLoc.orbitMap f = EPLoc.orbitMap f' → f = f'

end RoundTrip.V10_65
