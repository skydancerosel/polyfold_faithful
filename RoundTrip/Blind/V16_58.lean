import Polyfold
/-! Blind formalization of V16_58 (the text's Part II, §16.3, Theorem 16.3.17 (2), p. 728 of the
Springer 2021 book; 2017: Theorem 16.4 (2)).

Text: if `n` is reflexive, the extension can be taken reflexive.

Choices:
- Setting: `Y Z : Type` (universe `0`), a strong polyfold bundle `c : StrongPolyfoldBundle p`,
  with the standing hypotheses of Theorem 16.3.17 as in V16_57: `(Z, c)` tame
  (`c.polyfold.IsTame`), `n : Y → ℝ` an auxiliary norm of `Y_{0,1}|∂Z`
  (`IsAuxNormBoundary`, `#print`ed: in every structure an auxiliary norm over `∂X`).
- Reflexivity presupposes reflexive `1`-fibres (Definition 12.2.10 is made for such bundles), so
  I add `c.HasReflexiveFibers` (Definition 16.3.12) as a hypothesis.
- "`n` is reflexive" (over `∂Z`): there is no project notion of a reflexive auxiliary norm of
  `Y_{0,1}|∂Z`, so I define `IsReflexiveAuxNormBoundary` myself, in the form of Definition
  16.3.13 (an auxiliary norm represented in SOME structure by a reflexive one): `n` is an
  auxiliary norm of `Y_{0,1}|∂Z` and in some structure `S ∈ c̄`, `e ↦ n(Γ(|e|))` is a reflexive
  auxiliary norm over `∂X` (the project's ep-level `EpStrongBundle.IsReflexiveAuxNormOn`,
  Definition 12.2.10 over a subset, with `A = ∂X`).
- "the extension can be taken reflexive": there is `n'` with `IsReflexiveAuxNorm n'`
  (Definition 16.3.13, which contains `IsAuxNorm n'`) and `n' = n` on `Y_{0,1}|∂Z`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_58
open Polyfold

/-- `n` is a reflexive auxiliary norm of `Y_{0,1}|∂Z` (Definition 16.3.13 read over `∂Z`). -/
def IsReflexiveAuxNormBoundary {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    {p : Y → Z} (c : StrongPolyfoldBundle p) (n : Y → ℝ) : Prop :=
  c.IsAuxNormBoundary n ∧
    ∃ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c ∧
      S.A.E.IsReflexiveAuxNormOn S.A.X.PObj.boundary (S.normOf n)

/-- Theorem 16.3.17 (2): a reflexive auxiliary norm of `Y_{0,1}|∂Z` over a tame polyfold extends
to a reflexive auxiliary norm of `p`. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p), c.polyfold.IsTame → c.HasReflexiveFibers →
    ∀ n : Y → ℝ, IsReflexiveAuxNormBoundary c n →
      ∃ n' : Y → ℝ, c.IsReflexiveAuxNorm n' ∧
        ∀ y ∈ c.Y01, p y ∈ c.polyfold.boundary → n' y = n y

end RoundTrip.V16_58
