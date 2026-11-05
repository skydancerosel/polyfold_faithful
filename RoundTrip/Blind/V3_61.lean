import Polyfold
/-! Blind formalization of V3_61 (the text's §3.8.4, Corollary 3.75, p. 139). Choices:
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
- Hypotheses of Proposition 3.73 (`Hyp373`): `C` a partial quadrant, `U ⊆ C` relatively open,
  convex, `0 ∈ U`; `f : U → C` (`f : Rn → Rn` with `f(U) ⊆ C`; values off `U` are junk and unused)
  smooth; (1) `f(0) = 0`; (2) `‖Df(x) − 1‖ ≤ 1/2` for all `x ∈ U`, operator norm for the chosen norm
  of `Rn`; (3) `d_C(x) = d_C(f(x))` for all `x ∈ U`.
- Conclusion "`f : U → V` is a homeomorphism between relatively open subsets of `C`": `V = f(U)`
  is relatively open in `C` (`U` is, by hypothesis), and there is a homeomorphism `h : U ≃ₜ V` of
  the subspaces with `h(x) = f(x)`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_61
open Polyfold
open scoped ContDiff

/-- `U` is relatively open in `C`: `U = O ∩ C` for an open `O`. -/
def IsRelOpen {Rn : Type} [TopologicalSpace Rn] (C U : Set Rn) : Prop :=
  ∃ O : Set Rn, IsOpen O ∧ U = O ∩ C

/-- The hypotheses of Proposition 3.73: `C` a partial quadrant, `U ⊆ C` relatively open and convex
with `0 ∈ U`, `f : U → C` smooth with (1) `f(0) = 0`, (2) `|Df(x) − 1| ≤ 1/2` and
(3) `d_C(x) = d_C(f(x))` for `x ∈ U`. -/
def Hyp373 (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn) : Prop :=
  IsPartialQuadrant (ScBanach.const Rn) C ∧ IsRelOpen C U ∧ Convex ℝ U ∧ (0 : Rn) ∈ U ∧
    ContDiffOn ℝ ∞ f U ∧ Set.MapsTo f U C ∧
    f 0 = 0 ∧
    (∀ x ∈ U, ‖fderivWithin ℝ f U x - ContinuousLinearMap.id ℝ Rn‖ ≤ 1 / 2) ∧
    (∀ x ∈ U, degIndex (ScBanach.const Rn) C x = degIndex (ScBanach.const Rn) C (f x))

/-- Corollary 3.75: under the hypotheses of Proposition 3.73, `f : U → V = f(U)` is a
homeomorphism between relatively open subsets of `C`. -/
def B : Prop :=
  ∀ (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn),
    Hyp373 Rn C U f →
      IsRelOpen C (f '' U) ∧ ∃ h : U ≃ₜ (f '' U), ∀ x : U, (h x : Rn) = f x

end RoundTrip.V3_61
