import Polyfold
/-! Blind formalization of V10_66 (the Springer 2021 book, Part II, §10.3, Theorem 10.3.19,
pp. 493–494; 2017: Theorem 10.7, p. 355), with an effective target.

Text: if one of `X`, `Y` has the local regularity property and `f, f' : X → Y` are generalized
isomorphisms with `|f| = |f'|`, then `f = f'`; the item's title adds that the target `Y` is
effective.

Choices:
- Setting and notions as in `RoundTrip/Blind/V10_65.lean`: universe 0, `X`, `Y : EPLoc.{0}`
  (`EP(E⁻¹)`), the project's `EPLoc.IsGeneralizedIso` (Definition 10.3.9), `EpGroupoid.IsLR`
  (Definition 7.4.19) on one of `X`, `Y` (a disjunction), `EPLoc.orbitMap` for `|f|`
  (Definition 10.3.7).
- "an effective target": the extra hypothesis that `Y` is effective, the project's
  `EpGroupoid.IsEffective` (read with `#print`: for every `x` and `g ∈ G_x` with `g ≠ 1`, every
  open neighbourhood of `g` in the morphism space contains a `ψ` with `s(ψ) ≠ t(ψ)`; the text's
  effectiveness, as used in `RoundTrip/Blind/V8_48.lean`).  Only `Y`, as the title says; the
  (LR) hypothesis is kept as stated.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_66
open Polyfold Polyfold.EPLocalization

/-- **Theorem 10.3.19 for an effective target**: with `Y` effective and (LR) on one side,
generalized isomorphisms `X → Y` with the same orbit map are equal. -/
def B : Prop :=
  ∀ (X Y : EPLoc.{0}), Y.toEP.X.IsEffective → (X.toEP.X.IsLR ∨ Y.toEP.X.IsLR) →
    ∀ f f' : X ⟶ Y, EPLoc.IsGeneralizedIso f → EPLoc.IsGeneralizedIso f' →
      EPLoc.orbitMap f = EPLoc.orbitMap f' → f = f'

end RoundTrip.V10_66
