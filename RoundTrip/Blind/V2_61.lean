import Polyfold
/-! Blind formalization of V2_61 (the text's §2.5, Proposition 2.54, p. 53).

Text: (for a strong bundle `P : Y → X` and an sc-smooth `f : Z → X`, Definition 2.53)
`P_f : f*Y → Z` carries a natural structure of a strong bundle over `Z` ("the easy proof is left
to the reader").

Choices:
- Setting: `X Y Z : Type` (universe 0, as asked), each a Hausdorff paracompact space; `PX`, `PZ`
  the M-polyfold structures of `X`, `Z`; `P : Y → X` with its fibrewise linear structure as
  instances on the fibres `P ⁻¹' {x}`; `Bd : StrongBundle PX P` (Definition 2.51, checked with
  `#print`: continuous surjection, Banachable fibres, a strong bundle atlas); `f : Z → X` sc-smooth
  (`PZ.IsScSmoothMap PX f`, Definition 2.14).
- `f*Y`, `P_f`, `P'`: the project's `pullbackSpace P f` (checked: `{(z, y) | P y = f z}` as a set
  of `Z × Y`, with the subspace topology of the product), `pullbackProj P f` (`(z, y) ↦ z`) and
  `pullbackProj' P f` (`(z, y) ↦ y`).  The linear structure on the fibres `P_f⁻¹(z)` is the one
  found by instance search (a project instance); B pins it down by asserting that the fibre
  identification `pullbackFiberEquiv P f z : P_f⁻¹(z) ≃ P⁻¹(f z)` (checked: `(z, y) ↦ y`) is
  additive and `ℝ`-homogeneous, i.e. that the fibres of `f*Y` carry the linear structure of the
  fibres of `Y`.
- "a strong bundle over `Z`": a structure `StrongBundle PZ (pullbackProj P f)`.  It needs `f*Y`
  paracompact (Definition 2.51 asks the total space to be paracompact Hausdorff); B asserts this
  (`T2Space` is automatic for the subspace of a product of Hausdorff spaces).
- "natural": I read it as "compatible with the two projections of Definition 2.53": (a) the fibres
  of `P_f` carry the linear structure of the fibres of `P` (above); (b) `P' : f*Y → Y` is a strong
  bundle map covering `f`, i.e. sc-smooth `Y_f[0] → Y[0]` and `Y_f[1] → Y[1]` (the M-polyfolds
  `toMPolyfold0` and `toMPolyfold1` after Definition 2.51; on `Y_f[1] = (f*Y)_{0,1}` it is stated
  as: some map `g : Bf.One → Bd.One` with `g w = P' w` on the underlying points is sc-smooth).  I
  did not use the project's `StrongBundle.pullback` / `pullbackAtlas` (built from the chart
  formulas of the proof).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_61
open Polyfold

/-- Proposition 2.54: the pull-back `P_f : f*Y → Z` of a strong bundle along an sc-smooth map
carries a strong bundle structure over `Z`, natural in that the fibres of `f*Y` are those of `Y`
(linearly) and `P' : f*Y → Y` is sc-smooth on the levels `[0]` and `[1]`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (PZ : MPolyfold Z)
    (Bd : StrongBundle PX P) (f : Z → X),
    PZ.IsScSmoothMap PX f →
      -- the fibres of `f*Y` carry the linear structure of the fibres of `Y`
      (∀ (z : Z) (a b : pullbackProj P f ⁻¹' {z}) (c : ℝ),
        pullbackFiberEquiv P f z (a + b) = pullbackFiberEquiv P f z a + pullbackFiberEquiv P f z b ∧
        pullbackFiberEquiv P f z (c • a) = c • pullbackFiberEquiv P f z a) ∧
      -- `f*Y` is paracompact and carries a strong bundle structure over `Z`
      ∃ (_ : ParacompactSpace (pullbackSpace P f)) (Bf : StrongBundle PZ (pullbackProj P f)),
        -- natural: `P' : f*Y → Y` is sc-smooth on `[0]` and on `[1]`
        Bf.toMPolyfold0.IsScSmoothMap Bd.toMPolyfold0 (pullbackProj' P f) ∧
        ∃ g : Bf.One → Bd.One,
          (∀ w : Bf.One, Bd.oneVal (g w) = pullbackProj' P f (Bf.oneVal w)) ∧
          Bf.toMPolyfold1.IsScSmoothMap Bd.toMPolyfold1 g

end RoundTrip.V2_61
