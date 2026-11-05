import Polyfold
/-! Blind formalization of V1_34 (the text's §1.1, after Definition 1.14, p. 11).

Text: the map `U_1 → L(E_0, F_0)`, `x ↦ Df(x)`, will in general not be continuous for the
operator norm, but it is continuous for the compact-open topology.

Choices:
- Setting: the setting of Definition 1.14: sc-Banach spaces `E F : ScBanach` (the project's,
  levels in `Type`; checked with `#print` to be Definition 1.1), a partial quadrant `C ⊆ E` and a
  relatively open `U ⊆ C` (the project's `IsRelOpenInQuadrant E C U`, checked with `#print`:
  `IsPartialQuadrant E C` — `C = T⁻¹([0,∞)ⁿ ⊕ W)` for an sc-isomorphism `T : E → ℝⁿ ⊕ W`,
  Definition 1.11 — and `U = O ∩ C` with `O` open in `E₀`), and `f : U → F` given as a map
  `E₀ → F₀` (values off `U` irrelevant).
- "`f` is sc¹ with derivative `Df`" is the project's `IsSc1With U f D`, checked with `#print`
  against Definition 1.14: `f` is sc⁰ (`IsSc0`: `f(U_m) ⊆ F_m` with continuous induced maps);
  for `x ∈ U₁`, `f ∘ ι : U₁ → F₀` has derivative `D x ∘ ι` within `U₁` in the `E₁`-topology
  (condition (1): `|f(x+h) − f(x) − Df(x)h|₀ / |h|₁ → 0`, `x + h ∈ U₁`); and the tangent map
  `Tf(x, h) = (f(x), Df(x)h)` is sc⁰ on `TU = U¹ ⊕ E` (condition (2)).  `D` is indexed by all of
  `E₁` (junk off `U₁`).  `Df(x)` is unique on `U₁` (it is determined on the dense `E₁` because
  `U₁` is relatively open in a partial quadrant), so "the map `x ↦ Df(x)`" is any such `D`
  restricted to `U₁`; the positive claim is stated for every witness `D`.
- `U₁ = E.lvlSet U 1 ⊆ E₁` carries the `E₁` topology.  "Continuous for the compact-open
  topology": `x ↦ Df(x)`, viewed in `C(E₀, F₀)` with Mathlib's compact-open topology (the
  compact-open topology of `L(E₀, F₀)` is the subspace topology), is continuous on `U₁`.
- "will in general not be continuous for the operator norm": there exist `E, F, C, U, f, Df` as
  above with `f` sc¹ and `x ↦ Df(x) ∈ L(E₀, F₀)` not continuous on `U₁` for the operator norm
  (the norm topology is Mathlib's topology on `E₀ →L[ℝ] F₀`).
- Nothing looks false.
-/
namespace RoundTrip.V1_34
open Polyfold

/-- The derivative of an sc¹ map is continuous `U₁ → L(E₀, F₀)` for the compact-open topology,
but in general not for the operator norm. -/
def B : Prop :=
  (∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
      (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0),
      IsRelOpenInQuadrant E C U → IsSc1With U f D →
      ContinuousOn (fun x : E.lvl 1 => ((D x : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0)))
        (E.lvlSet U 1)) ∧
  (∃ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
      (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0),
      IsRelOpenInQuadrant E C U ∧ IsSc1With U f D ∧ ¬ ContinuousOn D (E.lvlSet U 1))

end RoundTrip.V1_34
