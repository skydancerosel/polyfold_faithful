import Polyfold
/-! Blind formalization of V5_10 (the text's §5.2, Theorem 5.5, p. 172).

Text: over a tame `X`, an sc-Fredholm section with compact solution set is proper; for
sc-Fredholm sections proper, weakly proper and "compact solution set" are equivalent.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P` (Definition
  2.51), as in `RoundTrip/Blind/V5_12.lean` (Theorem 5.7, same section, same "over a tame `X`").
- "Over a tame `X`": `PX.IsTame` (Definition 2.37, checked with `#print`: an atlas EQUIVALENT to
  the given one all of whose charts are modelled on tame retracts — a property of the given
  structure, not "every chart is tame").  The bundle itself is not assumed tame (the text only says
  `X` is tame).  The tameness hypothesis is put on both conjuncts (the second sentence is read in
  the same setting).
- `f` sc-Fredholm: the project's `Bd.IsScFredholmSection f` (Definition 3.14, checked with
  `#print`: sc-smooth section, regularizing, an sc-Fredholm germ at every smooth point).  I did not
  use the tame-chart variant `IsScFredholmSectionTame`, since only `X` is said to be tame.
- "compact solution set": `{x | f(x) = 0_x}` (`IsZeroAt`) compact in `X = X_0`.
- "proper", "weakly proper": the project's `Bd.IsProper`, `Bd.IsWeaklyProper` (Definition 5.4,
  checked with `#print` against the text's Definition 5.4: both include compactness of
  `f⁻¹(0)`; weakly proper: for every auxiliary norm `N` an open `U ⊇ f⁻¹(0)` such that `{f = s}`
  is compact for every sc⁺-section `s` with `cl{s ≠ 0} ⊆ U` and `N(s(y)) ≤ 1` for all `y`; proper:
  for every auxiliary `N` an open `U ⊇ f⁻¹(0)` with `cl_{X_0}{x ∈ U | N(f(x)) ≤ 1}` compact, with
  `N(f(x)) = ∞` off `Y_{0,1}` (`AuxLe`)).
- "proper, weakly proper and compact solution set are equivalent": stated as
  `(proper ↔ weakly proper) ∧ (weakly proper ↔ compact solution set)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_10
open Polyfold

/-- Theorem 5.5: over a tame M-polyfold, an sc-Fredholm section with compact solution set is
proper, and for sc-Fredholm sections "proper", "weakly proper" and "compact solution set" are
equivalent. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P),
    PX.IsTame →
      (∀ f : X → Y, Bd.IsScFredholmSection f → IsCompact {x | IsZeroAt P f x} →
          Bd.IsProper f) ∧
      (∀ f : X → Y, Bd.IsScFredholmSection f →
          (Bd.IsProper f ↔ Bd.IsWeaklyProper f) ∧
          (Bd.IsWeaklyProper f ↔ IsCompact {x | IsZeroAt P f x}))

end RoundTrip.V5_10
