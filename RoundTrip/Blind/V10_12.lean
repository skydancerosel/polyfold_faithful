import Polyfold
/-! Blind formalization of V10_12 (the text's Part II, §10.1, Example 10.1.15, p. 474 of the
Springer 2021 book; 2017: Example 10.1, p. 341).

Text: for `ℤ/4` acting on `ℝ` and on `ℝ²` and the functor to the origin, `Φ` does not induce a
map `𝐗^R → 𝐘^R`.

Choices:
- Setting: the translation ep-groupoids `X = ℤ/4 ⋉ ℝ` and `Y = ℤ/4 ⋉ ℝ²` are the project's
  `example1015X` (objects `Fin 1 → ℝ`, morphisms `Multiplicative (ZMod 4) × (Fin 1 → ℝ)`) and
  `example1015Y` (objects `Fin 2 → ℝ`), and `Φ` the project's `example1015Functor`.  I cannot
  build ep-groupoids in B, so B pins them down: a morphism `(i, x)` goes from `x` to `i • x`; on
  `ℝ`, `i` acts by `x ↦ (-1)^i x` (`1`, `3` by `x ↦ -x`, `0`, `2` trivially), on `ℝ²` by the
  `i`-th power of the quarter turn `(a, b) ↦ (-b, a)` (rotation by `i · 90°`, my `rotB`); units
  `1_x = (1, x)`; the object M-polyfolds are `ℝ`, `ℝ²` with their standard structures (the
  project's `rnPolyfold`); `Φ(x) = 0`, `Φ(i, x) = (i, 0)` ("the functor to the origin").  The
  morphism M-polyfolds (the project's `actionMorPolyfold`, four copies of the object space) are
  not restated.  That the text's action of `ℤ/4` on `ℝ` is through the sign `(-1)^i` is my
  reading of "`ℤ/4` acting on `ℝ`" (the only non-trivial action by linear maps).
- `𝐗^R`, `𝐘^R`: the project's `ReducedMor` (`Quot ReducedRel`, see
  `RoundTrip/Blind/V7_38.lean`), with projections `reducedπ`.
- "`Φ` does not induce a map `𝐗^R → 𝐘^R`": there is no map `f : 𝐗^R → 𝐘^R` with
  `f [φ] = [Φ φ]` for all `φ` (no continuity asked: the non-existence of any map is the claim).
- Nothing looks false to me (`2 ∈ T_x` acts trivially on `ℝ`, so `[(0, x)] = [(2, x)]` in `𝐗^R`,
  while `T_0 = 1` in `Y`, so `[(0, 0)] ≠ [(2, 0)]` in `𝐘^R`).
-/
namespace RoundTrip.V10_12
open Polyfold
open Polyfold.EpGroupoid.Examples

/-- The quarter turn `(a, b) ↦ (-b, a)` of `ℝ²`. -/
def rotB (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-y 1, y 0]

/-- Example 10.1.15: for `X = ℤ/4 ⋉ ℝ`, `Y = ℤ/4 ⋉ ℝ²` and `Φ` the functor to the origin, there is
no map `𝐗^R → 𝐘^R`, `[φ] ↦ [Φ φ]`. -/
def B : Prop :=
  -- `X = ℤ/4 ⋉ ℝ`, `i` acting by `(-1)^i`
  (∀ (i : Multiplicative (ZMod 4)) (x : Fin 1 → ℝ),
    example1015X.src (i, x) = x ∧
    example1015X.tgt (i, x) = if (Multiplicative.toAdd i).val % 2 = 0 then x else -x) ∧
  (∀ x : Fin 1 → ℝ, example1015X.unit x = (1, x)) ∧
  example1015X.PObj = rnPolyfold 1 ∧
  -- `Y = ℤ/4 ⋉ ℝ²`, `i` acting by the rotation by `i · 90°`
  (∀ (i : Multiplicative (ZMod 4)) (y : Fin 2 → ℝ),
    example1015Y.src (i, y) = y ∧
    example1015Y.tgt (i, y) = rotB^[(Multiplicative.toAdd i).val] y) ∧
  (∀ y : Fin 2 → ℝ, example1015Y.unit y = (1, y)) ∧
  example1015Y.PObj = rnPolyfold 2 ∧
  -- `Φ`, the functor to the origin
  (∀ x : Fin 1 → ℝ, example1015Functor.obj x = 0) ∧
  (∀ (i : Multiplicative (ZMod 4)) (x : Fin 1 → ℝ), example1015Functor.mor (i, x) = (i, 0)) ∧
  -- the example: `Φ` induces no map `𝐗^R → 𝐘^R`
  ¬ ∃ f : example1015X.ReducedMor → example1015Y.ReducedMor,
      ∀ φ : Multiplicative (ZMod 4) × (Fin 1 → ℝ),
        f (example1015X.reducedπ φ) = example1015Y.reducedπ (example1015Functor.mor φ)

end RoundTrip.V10_12
