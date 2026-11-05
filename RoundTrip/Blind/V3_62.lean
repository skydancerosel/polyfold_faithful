import Polyfold
/-! Blind formalization of V3_62 (the text's §3.8.4, Lemma 3.77, p. 140). Choices:
- Setting (§3.8.4): "`C ⊆ ℝⁿ` a partial quadrant".  I take `ℝⁿ` to be an arbitrary
  finite-dimensional real normed space `Rn : Type` (every such space is `ℝⁿ` with some norm, and
  every norm on `ℝⁿ` arises).  The text writes `|·|` on `ℝⁿ` without fixing a norm; I read it as an
  arbitrary norm (this covers the Euclidean norm and Mathlib's sup norm on `Fin n → ℝ`).
  `Rn : Type` (universe `0`, as `ScBanach.const` requires; nothing depends on the universe).
  `C` is a partial quadrant (Definition 1.11) of `Rn` with its constant sc-structure: the
  project's `IsPartialQuadrant (ScBanach.const Rn) C`.  `d_C` is the project's
  `degIndex (ScBanach.const Rn) C` (Definition 1.23, computed with any presentation; its junk
  value `0` for non-quadrants does not arise).
- "relatively open in `C`": `U = O ∩ C` with `O ⊆ Rn` open (`IsRelOpen`, defined here).
- Naming: the space is `Rn` in Lean; the text's `V = f(U)` is `f '' U`.
- "smooth": Mathlib's `ContDiffOn ℝ ∞` on the (relatively open) set, derivatives within the set;
  `Df(x)` is `fderivWithin ℝ f U x` (unique: `U` is locally a convex set with nonempty interior,
  as `C` is).
- Hypotheses exactly as quoted (no convexity, no `0 ∈ U`, no degeneracy condition): `U` relatively
  open in `C`; `f : U → C` smooth (`f : Rn → Rn`, values off `U` junk, `f(U) ⊆ C`); `V = f(U)`
  relatively open in `C`; `f : U → V` a homeomorphism (a homeomorphism `h : U ≃ₜ V` of the
  subspaces with `h(x) = f(x)`); `Df(x)` invertible for every `x ∈ U` (it is a continuous linear
  equivalence `Rn ≃L Rn`).
- Conclusion for `g = f⁻¹ : V → U` (any `g` with `g(y) ∈ U`, `f(g(y)) = y` on `V`; its values on `V`
  are determined): `g` is `C¹` on `V` (`ContDiffOn ℝ 1`), and at every `y ∈ V`, `g` has derivative
  `[Df(g(y))]⁻¹` within `V` (`HasFDerivWithinAt`), the inverse being that of the equivalence
  `Df(g(y))`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_62
open Polyfold
open scoped ContDiff

/-- `U` is relatively open in `C`: `U = O ∩ C` for an open `O`. -/
def IsRelOpen {Rn : Type} [TopologicalSpace Rn] (C U : Set Rn) : Prop :=
  ∃ O : Set Rn, IsOpen O ∧ U = O ∩ C

/-- Lemma 3.77: if `f : U → C` is smooth on a relatively open `U ⊆ C`, `V = f(U)` is relatively
open, `f : U → V` is a homeomorphism and every `Df(x)` is invertible, then `g = f⁻¹` is `C¹` on `V`
with `Dg(y) = [Df(g(y))]⁻¹`. -/
def B : Prop :=
  ∀ (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn),
    IsPartialQuadrant (ScBanach.const Rn) C →
    IsRelOpen C U →
    ContDiffOn ℝ ∞ f U → Set.MapsTo f U C →
    IsRelOpen C (f '' U) →
    (∃ h : U ≃ₜ (f '' U), ∀ x : U, (h x : Rn) = f x) →
    (∀ x ∈ U, ∃ e : Rn ≃L[ℝ] Rn, (e : Rn →L[ℝ] Rn) = fderivWithin ℝ f U x) →
    ∀ g : Rn → Rn, (∀ y ∈ f '' U, g y ∈ U ∧ f (g y) = y) →
      ContDiffOn ℝ 1 g (f '' U) ∧
      ∀ y ∈ f '' U, ∀ e : Rn ≃L[ℝ] Rn, (e : Rn →L[ℝ] Rn) = fderivWithin ℝ f U (g y) →
        HasFDerivWithinAt g (e.symm : Rn →L[ℝ] Rn) (f '' U) y

end RoundTrip.V3_62
