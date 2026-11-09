import Polyfold
/-! Blind formalization of V10_8 (the text's Part II, §10.1, Remark 10.1.11, p. 470 of the
Springer 2021 book; 2017: Remark 10.1, p. 340).

Text: on `ℤ/2 ⋉ ℝ²` with `F = id` and `G = -id`, the morphisms `α_z : z → -z` cannot be chosen in
an sc-smooth local family with `α_0 = 1_0`.

Choices:
- Setting: the translation ep-groupoid `ℤ/2 ⋉ ℝ²` is the project's `pointReflectionEpGroupoid`
  (objects `Fin 2 → ℝ`, morphisms `ℤˣ × (Fin 2 → ℝ)`, `ℤ/2 = ℤˣ`), and `G = -id` the project's
  `negFunctor`; `F = id` is the project's `EpFunctor.id`.  I cannot build an ep-groupoid in B, so
  B pins these down: `s(k, z) = z`, `t(k, z) = k • z` (`±z`), `1_z = (1, z)`; `G(z) = -z`,
  `G(k, z) = (k, -z)`; the object M-polyfold is `ℝ²` with its standard structure (the project's
  `rnPolyfold 2`); `id` is the identity on objects and morphisms.  The morphism M-polyfold (the
  project's `actionMorPolyfold`, two copies of `ℝ²`) is not restated.
- "the morphisms `α_z : z → -z`", i.e. `α_z : F(z) → G(z)`; "an sc-smooth local family": an open
  neighbourhood `U` of `0` and a map `α : ℝ² → 𝐗` which is sc-smooth on `U` (the project's
  `MPolyfold.IsScSmoothOn` from the object to the morphism M-polyfold, which includes continuity
  on the open `U`) with `s(α z) = F z`, `t(α z) = G z` for `z ∈ U`.  "with `α_0 = 1_0`":
  `α 0 = 1_0`.  B: no such `U`, `α` exist.  I do not require naturality of the family (the
  summary does not mention it); without it the non-existence claim is the stronger one.
- Nothing looks false to me (for `z ≠ 0` the only morphism `z → -z` is `(-1, z)`, which tends to
  `(-1, 0) ≠ (1, 0) = 1_0`).
-/
namespace RoundTrip.V10_8
open Polyfold
open Polyfold.EpGroupoid.Examples

/-- Remark 10.1.11: on `ℤ/2 ⋉ ℝ²`, with `F = id` and `G = -id`, there is no sc-smooth family
`α_z : F(z) → G(z)` near `0` with `α_0 = 1_0`. -/
def B : Prop :=
  -- the ep-groupoid `ℤ/2 ⋉ ℝ²`
  (∀ (k : ℤˣ) (z : Fin 2 → ℝ),
    pointReflectionEpGroupoid.src (k, z) = z ∧ pointReflectionEpGroupoid.tgt (k, z) = k • z) ∧
  (∀ z : Fin 2 → ℝ, pointReflectionEpGroupoid.unit z = (1, z)) ∧
  pointReflectionEpGroupoid.PObj = rnPolyfold 2 ∧
  -- the functors `F = id` and `G = -id`
  (∀ z : Fin 2 → ℝ, (EpFunctor.id pointReflectionEpGroupoid).obj z = z) ∧
  (∀ φ : ℤˣ × (Fin 2 → ℝ), (EpFunctor.id pointReflectionEpGroupoid).mor φ = φ) ∧
  (∀ z : Fin 2 → ℝ, negFunctor.obj z = -z) ∧
  (∀ (k : ℤˣ) (z : Fin 2 → ℝ), negFunctor.mor (k, z) = (k, -z)) ∧
  -- the remark
  ¬ ∃ (U : Set (Fin 2 → ℝ)) (α : (Fin 2 → ℝ) → ℤˣ × (Fin 2 → ℝ)),
      IsOpen U ∧ (0 : Fin 2 → ℝ) ∈ U ∧
      pointReflectionEpGroupoid.PObj.IsScSmoothOn pointReflectionEpGroupoid.PMor α U ∧
      (∀ z ∈ U,
        pointReflectionEpGroupoid.src (α z) = (EpFunctor.id pointReflectionEpGroupoid).obj z ∧
          pointReflectionEpGroupoid.tgt (α z) = negFunctor.obj z) ∧
      α 0 = pointReflectionEpGroupoid.unit 0

end RoundTrip.V10_8
