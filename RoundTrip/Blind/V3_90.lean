import Polyfold
/-! Blind formalization of V3_90 (the text's §3.8.4, Proposition 3.73 and Lemma 3.77, pp. 137,
140).  `B` is the conjunction of the claims.  Choices:
- Setting (§3.8.4, as in my earlier blind files V3_59/V3_62): "`C ⊆ ℝⁿ` a partial quadrant".  I
  take `ℝⁿ` to be an arbitrary finite-dimensional real normed space `Rn : Type` (every such space
  is `ℝⁿ` with some norm, and every norm on `ℝⁿ` arises); the text writes `|·|` without fixing a
  norm, and `‖Df − 1‖` is the operator norm for the chosen norm.  `Rn : Type` (universe `0`, as
  `ScBanach.const` requires; nothing depends on the universe).  `C` is a partial quadrant
  (Definition 1.11) of `Rn` with its constant sc-structure (`IsPartialQuadrant`); `d_C` is the
  project's `degIndex (ScBanach.const Rn) C` (Definition 1.23).
- "relatively open in `C`": `U = O ∩ C` with `O ⊆ Rn` open (`IsRelOpen`, defined here); "convex":
  `Convex ℝ U`.
- "`f : U → C` smooth": `f : Rn → Rn` (values off `U` are junk and unused), `f(U) ⊆ C`,
  `ContDiffOn ℝ ∞ f U` (derivatives within `U`); `Df(x)` is `fderivWithin ℝ f U x` (unique: `U` is
  locally a convex set with nonempty interior, as `C` is).
- Hypotheses exactly as quoted (`Hyp373`): `‖Df(x) − 1‖ ≤ 1/2` for `x ∈ U`, `f(0) = 0` (this
  presupposes `0 ∈ U`, which I add), and `d_C(x) = d_C(f(x))` for `x ∈ U`.
- Conclusions: `f(U)` is relatively open in `C`; `f : U → f(U)` is a smooth diffeomorphism: `f` is
  injective on `U` (it maps `U` onto `f(U)` by definition and is smooth by hypothesis) and there
  is an inverse `g : f(U) → U` (`g(y) ∈ U`, `f(g(y)) = y`) which is smooth on `f(U)`; and (Lemma
  3.77) `g` is differentiable with `Dg(y) = [Df(g(y))]⁻¹`: at every `y ∈ f(U)`, `Df(g(y))` is
  invertible (a continuous linear equivalence `e`) and `g` has derivative `e⁻¹` within `f(U)` at
  `y` (`HasFDerivWithinAt`).
- The item's title says "with the hypotheses their proofs use"; the quoted hypotheses are exactly
  those of Proposition 3.73, which is what `B` assumes.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_90
open Polyfold
open scoped ContDiff

/-- `U` is relatively open in `C`: `U = O ∩ C` for an open `O`. -/
def IsRelOpen {Rn : Type} [TopologicalSpace Rn] (C U : Set Rn) : Prop :=
  ∃ O : Set Rn, IsOpen O ∧ U = O ∩ C

/-- The hypotheses: `C` a partial quadrant, `U ⊆ C` relatively open and convex with `0 ∈ U`,
`f : U → C` smooth with `f(0) = 0`, `|Df(x) − 1| ≤ 1/2` and `d_C(x) = d_C(f(x))` for `x ∈ U`. -/
def Hyp373 (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn) : Prop :=
  IsPartialQuadrant (ScBanach.const Rn) C ∧ IsRelOpen C U ∧ Convex ℝ U ∧ (0 : Rn) ∈ U ∧
    ContDiffOn ℝ ∞ f U ∧ Set.MapsTo f U C ∧
    f 0 = 0 ∧
    (∀ x ∈ U, ‖fderivWithin ℝ f U x - ContinuousLinearMap.id ℝ Rn‖ ≤ 1 / 2) ∧
    (∀ x ∈ U, degIndex (ScBanach.const Rn) C x = degIndex (ScBanach.const Rn) C (f x))

/-- Proposition 3.73 with Lemma 3.77: under the hypotheses, `f(U)` is relatively open in `C`,
`f : U → f(U)` is a smooth diffeomorphism, and its inverse `g` has `Dg(y) = [Df(g(y))]⁻¹`. -/
def B : Prop :=
  ∀ (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn),
    Hyp373 Rn C U f →
      IsRelOpen C (f '' U) ∧ Set.InjOn f U ∧
      ∃ g : Rn → Rn, (∀ y ∈ f '' U, g y ∈ U ∧ f (g y) = y) ∧ ContDiffOn ℝ ∞ g (f '' U) ∧
        ∀ y ∈ f '' U, ∃ e : Rn ≃L[ℝ] Rn,
          (e : Rn →L[ℝ] Rn) = fderivWithin ℝ f U (g y) ∧
          HasFDerivWithinAt g (e.symm : Rn →L[ℝ] Rn) (f '' U) y

end RoundTrip.V3_90
