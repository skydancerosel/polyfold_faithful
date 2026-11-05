import Polyfold
/-! Blind formalization of V3_58 (the text's §3.8.4, Theorem 3.72, p. 136). Choices:
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
- "smooth": Mathlib's `ContDiffOn ℝ ∞` on the (relatively open) set, derivatives within the set;
  `Df(x)` is `fderivWithin ℝ f U x` (unique: `U` is locally a convex set with nonempty interior,
  as `C` is).
- `U ⊆ C` a relatively open neighbourhood of `0`; `f : U → ℝⁿ` is `f : Rn → Rn` (values off `U` are
  junk and unused), smooth on `U`, with `f(U) ⊆ C`.
- (1) `f(0) = 0` and `Df(0)C = C`: the image of `C` under the linear map `Df(0)` is `C`.
  (2) `d_C(x) = d_C(f(x))` for all `x ∈ U` (the quantifier range is all of `U`).
- Conclusion "`f` is a diffeomorphism between relatively open neighbourhoods `U'`, `V'` of `0` in
  `C`": there are `U' ⊆ U` and `V' ⊆ C`, both relatively open in `C` and containing `0`, such that
  `f` maps `U'` bijectively onto `V'`, `f` is smooth on `U'` and the inverse `g : V' → U'` is
  smooth on `V'` (`ContDiffOn ℝ ∞`).  (`U' ⊆ U` is presupposed: `f` is only defined on `U`.)
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_58
open Polyfold
open scoped ContDiff

/-- `U` is relatively open in `C`: `U = O ∩ C` for an open `O`. -/
def IsRelOpen {Rn : Type} [TopologicalSpace Rn] (C U : Set Rn) : Prop :=
  ∃ O : Set Rn, IsOpen O ∧ U = O ∩ C

/-- Theorem 3.72 (quadrant inverse function theorem): a smooth `f : U → ℝⁿ` on a relatively open
neighbourhood `U` of `0` in a partial quadrant `C`, with `f(U) ⊆ C`, `f(0) = 0`, `Df(0)C = C` and
`d_C(f(x)) = d_C(x)`, restricts to a diffeomorphism between relatively open neighbourhoods
`U'`, `V'` of `0` in `C`. -/
def B : Prop :=
  ∀ (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn),
    IsPartialQuadrant (ScBanach.const Rn) C →
    IsRelOpen C U → (0 : Rn) ∈ U →
    ContDiffOn ℝ ∞ f U → Set.MapsTo f U C →
    f 0 = 0 → (fderivWithin ℝ f U 0) '' C = C →
    (∀ x ∈ U, degIndex (ScBanach.const Rn) C x = degIndex (ScBanach.const Rn) C (f x)) →
    ∃ (U' V' : Set Rn) (g : Rn → Rn),
      IsRelOpen C U' ∧ U' ⊆ U ∧ (0 : Rn) ∈ U' ∧
      IsRelOpen C V' ∧ (0 : Rn) ∈ V' ∧
      Set.BijOn f U' V' ∧ (∀ y ∈ V', g y ∈ U' ∧ f (g y) = y) ∧
      ContDiffOn ℝ ∞ f U' ∧ ContDiffOn ℝ ∞ g V'

end RoundTrip.V3_58
