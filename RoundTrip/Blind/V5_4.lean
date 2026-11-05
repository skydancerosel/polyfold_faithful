import Polyfold
/-! Blind formalization of V5_4 (the text's §5.1, Lemma 5.2, p. 169).

Text: for a continuous `N` which fibrewise is a complete norm: `N` is auxiliary iff every `x` has a
strong bundle isomorphism `Φ : Y|V → K` and `0 < c < C` with `cN(w) ≤ |h|₁ ≤ CN(w)` for all
`w ∈ P⁻¹(V)`, `Φ(w) = (p, h)`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P` (Definition
  2.51), as in `RoundTrip/Blind/V5_10.lean`.  No tameness.
- `N : Y_{0,1} → ℝ` on the project's `Bd.One` (= `Y_{0,1}`, checked).  "Continuous": for the
  topology the project puts on `Bd.One` (the one of `IsAuxNorm`; it must be the topology of the
  M-polyfold `Y[1]`, since the project builds `Y[1]` on it; audited separately in
  `RoundTrip/Blind/V5_3.lean`).  "Fibrewise a complete norm": `Bd.IsCompleteFiberNorm N x` for
  every `x` (Definition 5.1 (1), checked with `#print`: norm axioms on `(Y_{0,1})_x` and
  completeness).  "Auxiliary": the project's `Bd.IsAuxNorm N` (Definition 5.1, checked with
  `#print`; compared with the text in V5_3).
- "a strong bundle isomorphism `Φ : Y|V → K`" (around `x`): a strong bundle chart compatible with
  the strong bundle structure, `c : StrongBundleChart PX P` with `Bd.IsChart c` (checked: `c` is
  compatible with every chart of the atlas, i.e. lies in the maximal atlas), with `x ∈ V`
  (`c.φ.source`, open).  Not restricted to the charts of the given atlas (the text quantifies over
  strong bundle isomorphisms, V5_1).
- `w ∈ P⁻¹(V)`: `w ∈ Y_{0,1}` (where `N` is defined) with `P(w) ∈ V`.  `Φ(w) = (p, h)`, `h ∈ F₀`
  in the range of `F₁ → F₀`; `|h|₁` is the `F₁`-norm of its lift (`fiberNormOne`; the lift is
  `Function.invFun` of the injective inclusion, exact on the range).
- "`0 < c < C`": literally `0 < c ∧ c < C`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_4
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- `|h|₁` for `Φ(y) = (p, h)`: the `F₁`-norm of the fibre component of `Φ(y)`. -/
noncomputable def fiberNormOne (c : StrongBundleChart PX P) (y : Y) : ℝ :=
  ‖Function.invFun (c.F.toBase 1) (c.toPartialEquiv y).2‖

end

/-- Lemma 5.2: a continuous fibrewise complete norm on `Y_{0,1}` is auxiliary iff near every point
it is uniformly equivalent to the `F₁`-norm read in some strong bundle chart. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ),
    Continuous N → (∀ x : X, Bd.IsCompleteFiberNorm N x) →
      (Bd.IsAuxNorm N ↔
        ∀ x : X, ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧ x ∈ c.φ.source ∧
          ∃ a A : ℝ, 0 < a ∧ a < A ∧
            ∀ w : Bd.One, P (Bd.oneVal w) ∈ c.φ.source →
              a * N w ≤ fiberNormOne c (Bd.oneVal w) ∧ fiberNormOne c (Bd.oneVal w) ≤ A * N w)

end RoundTrip.V5_4
