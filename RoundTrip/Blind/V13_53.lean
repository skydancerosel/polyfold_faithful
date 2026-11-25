import Polyfold
/-! Blind formalization of V13_53 (the Springer 2021 book, Part II, §13.4, Theorem 13.4.4,
pp. 626–628; 2017: Theorem 13.5).

Text: for a proper strong bundle covering `Φ : E → W` over the proper covering functor
`F : Y → X` and structurable `Λ`, `Φ^*Λ` is structurable.

Choices:
- Setting: universe 0; strong bundles over ep-groupoids `SEP.{0}`: `C` for `E → Y`, `A` for
  `W → X`.  `F : Y → X` an ep-functor (`EpFunctor C.X A.X`), `Φ : E → W` a map of the total
  spaces (`C.W → A.W`).
- "proper strong bundle covering over the proper covering functor `F`": the project's
  `EpStrongBundle.IsProperStrongBundleCovering2021 C.E A.E F Φ` (2021 Definition 8.5.9; its
  docstring: `Φ` a fibrewise linear strong bundle map covering `F`, compatible with the actions,
  surjective local strong bundle isomorphism covering the sc-smooth proper covering functor `F`,
  with the even covering and the strong bundle isomorphism of condition (3)).  The properness
  and covering property of `F` are part of this predicate.
- `Φ^*Λ = Λ ∘ Φ`, written out.
- "structurable": the project's `IsStructurable` (`#print`ed: an sc⁺-multisection functor with
  a system of symmetric structures carrying correspondences, Definition 13.3.6).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V13_53
open Polyfold Polyfold.SBLocalization

/-- Theorem 13.4.4: pull-backs along proper strong bundle coverings are structurable. -/
def B : Prop :=
  ∀ (C A : SEP.{0}) (F : EpFunctor C.X A.X) (Φ : C.W → A.W),
    C.E.IsProperStrongBundleCovering2021 A.E F Φ →
    ∀ Λ : A.W → ℚ≥0, IsStructurable A Λ → IsStructurable C (fun w => Λ (Φ w))

end RoundTrip.V13_53
