import Polyfold
/-! Blind formalization of V5_23 (the text's §5.3, Definition 5.15, p. 175).

Text: `g` is transversal to the zero section if at every `x` with `g(x) = 0` the linearization
`g'(x) : T_xX → Y_x` is surjective.

Choices:
- This item is a definition.  B says that, for every sc-smooth section `g`, the project's
  `Bd.IsTransversal g` (Definition 5.15) is the text's notion `IsTransversalB Bd g` written below.
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_10.lean`.  No tameness (the definition has none).
- Range of `g`: the linearization `g'(x)` only makes sense for an sc-smooth (at least sc¹) section,
  so B quantifies over sc-smooth sections, the project's `Bd.IsScSmoothSection g` (Definition
  2.52, "sc-smooth as a map into `Y[0]`").  (The text uses the notion for sc-Fredholm sections
  `f + s`, which are sc-smooth.)
- `g(x) = 0`: `g x = 0_x`, the zero of the fibre `P⁻¹(x)` (`IsZeroAt`, checked:
  `f x = fiberZero P x`).
- The linearization at a zero, in a strong bundle chart `Φ` of `P` around `x` (`Bd.IsChart c`:
  compatible with the atlas, Definition 2.50) with base chart `φ`, base retraction
  `r = StrongRetr.r R` (`r(u) = (R(u, 0))₁`) and principal part `ĝ : O → F`
  (`StrongBundleChart.principal`, `Φ ∘ g ∘ φ⁻¹(p) = (p, ĝ(p))`): `x` must lie in `X_1`, i.e.
  `φ(x)` lifts to a point `z ∈ E_1`; then `T_xX ≅ T_zO = Dr(z)E` (`TO`, Definition 2.17), `Y_x ≅`
  the fibre `K_{φ(x)} = {k | (φ(x), k) ∈ K}` of the local strong bundle, and
  `g'(x) ≅ D(ĝ ∘ r)(z)|_{T_zO}` (`Dg`; the project's `scDeriv` is the derivative of an sc¹ map,
  "junk if not sc¹" — irrelevant for sc-smooth `g`).  "Surjective": every `k ∈ K_{φ(x)}` is
  `D(ĝ ∘ r)(z)v` for some `v ∈ T_zO` (the image is always inside `K_{φ(x)}` at a zero).
- The text's `g'(x)` is intrinsic (independent of the chart); I require surjectivity in EVERY
  strong bundle chart of `P` around `x` (equivalently, by the chart independence of the
  linearization at a zero, in one chart).  This is my choice; it is not weaker than "in some
  chart".
- Nothing looks false to me.
-/
namespace RoundTrip.V5_23
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The tangent space `T_zO = Dr(z)E` of the retract `O = r(U)` at `z ∈ O_1`, `r` the base
retraction of the chart. -/
noncomputable def TO (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range (scDeriv c.U (StrongRetr.r c.R) z).toLinearMap

/-- `D(ĝ ∘ r)(z) : E → F` for the principal part `ĝ` of a section `g` in the chart; restricted to
`T_zO` it is the linearization `g'(x)` at a zero. -/
noncomputable def Dg (c : StrongBundleChart PX P) (g : X → Y) (z : c.φ.model.E.lvl 1) :
    c.φ.model.E.lvl 0 →L[ℝ] c.F.lvl 0 :=
  scDeriv c.U (c.principal g ∘ StrongRetr.r c.R) z

/-- **Definition 5.15**: `g` is transversal to the zero section: at every zero `x`, in every strong
bundle chart around `x`, the linearization `T_zO → K_{φ(x)}` is onto (`z ∈ E_1` the lift of
`φ(x)`). -/
def IsTransversalB (Bd : StrongBundle PX P) (g : X → Y) : Prop :=
  ∀ x : X, IsZeroAt P g x →
    ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
      ∃ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x ∧
        ∀ k : c.F.lvl 0, (c.φ.toPartialEquiv x, k) ∈ c.K →
          ∃ v ∈ TO c z, Dg c g z v = k

end

/-- Definition 5.15: for sc-smooth sections, the project's transversality is the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (g : X → Y),
    Bd.IsScSmoothSection g → (Bd.IsTransversal g ↔ IsTransversalB Bd g)

end RoundTrip.V5_23
