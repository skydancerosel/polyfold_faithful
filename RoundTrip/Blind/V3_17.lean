import Polyfold
/-! Blind formalization of V3_17 (the text's §3.1, Theorem 3.15, p. 71). Choices:
- Setting: `X Y : Type` (universe 0 for both spaces, as asked; nothing in the claim depends on
  the universe).  `PX : MPolyfold X` is the M-polyfold structure of `X`; `P : Y → X` with the
  fibrewise linear structure given as instances on the fibres `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` the strong bundle structure (Definition 2.51).
- Hypotheses exactly as quoted: the base is a tame M-polyfold (`PX.IsTame`, Definition 2.37);
  the bundle itself is *not* assumed tame (the statement says "a strong bundle over a tame
  M-polyfold").
- `f ∈ Fred(P)`: `StrongBundle.IsScFredholmSection` (Definition 3.14: sc-smooth section,
  regularizing, an sc-Fredholm germ at every smooth point, the germ data in *some* strong bundle
  chart compatible with the bundle structure).  I did not use the "tame chart" variant
  `IsScFredholmSectionTame` (Definitions 3.50/3.51 of §3.6), since the statement does not ask for
  a tame strong bundle; the same notion is used in the hypothesis and in the conclusion.
- `s ∈ Γ⁺(P)`: `StrongBundle.IsScPlusSection` (Definition 2.52).
- `f + s`: the fibrewise sum `sectionAdd P f s` (its junk branch is never used, since `f` and `s`
  are sections).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_17
open Polyfold

/-- Theorem 3.15: over a tame M-polyfold, an sc-Fredholm section perturbed by an sc⁺-section is
again sc-Fredholm. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f s : X → Y),
    PX.IsTame → Bd.IsScFredholmSection f → Bd.IsScPlusSection s →
      Bd.IsScFredholmSection (sectionAdd P f s)

end RoundTrip.V3_17
