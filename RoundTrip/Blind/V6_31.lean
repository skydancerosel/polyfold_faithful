import Polyfold
/-! Blind formalization of V6_31 (the text's §6.5, Definition 6.27, pp. 219–220).

Text: an orientation of `(f, x)`, `x` smooth, is a choice of one of the two orientations of
`DET(f, x)`.  The objects of a category are the sets `Or^f_x = {o_x, −o_x}`; for smooth `x`, `y`
in the same path component the morphisms are the two bijections `±o_x ↦ ±o_y` and
`±o_x ↦ ∓o_y`.

Choices:
- This item is a definition.  B states its content: (1) the orientations of `(f, x)` form a set
  `Or^f_x = {o_x, −o_x}` with two elements, `−o_x` the opposite orientation of `o_x`; (2) for
  smooth `x`, `y` in the same path component the bijections `Or^f_x → Or^f_y` are exactly the two
  bijections `±o_x ↦ ±o_y` and `±o_x ↦ ∓o_y` (both exist, and every bijection is one of them).
  The category itself (with no morphisms between different path components) is not built.
- Setting: as in `RoundTrip/Blind/V6_30.lean` (Proposition 6.26): `X Y : Type`, a strong bundle
  `Bd : StrongBundle PX P`, `f` sc-Fredholm, `x`, `y` smooth points.  `DET(f, x)` is read in a
  chart point `p : ChartPoint Bd x` (a chart of the atlas around `x` with the lift of `φ(x)`); B
  quantifies over all chart points.
- `Or^f_x`: the orientations of the line bundle `DET(f, x)` (the project's
  `ChartPoint.detLin f p hf`, the restriction of `DET(T_xX, Y_x)` to `Lin(f, x)`), i.e. the
  project's `LineOrientation (ChartPoint.detLin f p hf)` (which is what the project's
  `ChartPoint.Or f p hf` unfolds to, checked with `#print`).
- `−o`: the orientation `L ↦ −o(L)` (opposite ray in every fibre); B states it through the
  predicate `IsOpp o o'` (`o' L = −o(L)` for all `L`), so no proof that `−o` is an orientation is
  needed in the statement: "`Or^f_x = {o, −o}`" is: for every orientation `o` there is an
  orientation `o'` with `IsOpp o o'`, `o' ≠ o`, and every orientation is `o` or `o'`.
- "the same path component": `Joined x y` (a continuous path in `X`; the text's path components
  of the topological space `X`).  The claim (2) does not depend on it, but it is the text's
  hypothesis.
- Nothing looks false to me (if `Lin(f, x)` were empty, (1) would fail: see V6_30).
-/
namespace RoundTrip.V6_31
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- `Or^f_x`: the orientations of `DET(f, x)`, read in the chart point `p`. -/
abbrev OrB (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f) {x : X}
    (p : ChartPoint Bd x) : Type :=
  LineOrientation (ChartPoint.detLin f p hf)

/-- `o'` is the opposite orientation `−o`. -/
def IsOpp {Bd : StrongBundle PX P} {f : X → Y} {hf : Bd.IsScFredholmSection f} {x : X}
    {p : ChartPoint Bd x} (o o' : OrB Bd f hf p) : Prop :=
  ∀ L : ↥(p.linSet f),
    let r : Module.Ray ℝ (fredholmDet (L : ↥p.T →L[ℝ] ↥p.K)) := o.1 L
    let r' : Module.Ray ℝ (fredholmDet (L : ↥p.T →L[ℝ] ↥p.K)) := o'.1 L
    r' = -r

end

/-- Definition 6.27: `Or^f_x = {o_x, −o_x}`, and the bijections `Or^f_x → Or^f_y` are the two maps
`±o_x ↦ ±o_y` and `±o_x ↦ ∓o_y`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    -- (1) `Or^f_x = {o_x, −o_x}`
    (∀ x ∈ PX.smoothSet, ∀ (p : ChartPoint Bd x) (o : OrB Bd f hf p),
      ∃ o' : OrB Bd f hf p, IsOpp o o' ∧ o' ≠ o ∧ ∀ o'' : OrB Bd f hf p, o'' = o ∨ o'' = o') ∧
    -- (2) the morphisms between `Or^f_x` and `Or^f_y`
    (∀ x ∈ PX.smoothSet, ∀ y ∈ PX.smoothSet, Joined x y →
      ∀ (p : ChartPoint Bd x) (q : ChartPoint Bd y) (ox ox' : OrB Bd f hf p)
        (oy oy' : OrB Bd f hf q), IsOpp ox ox' → IsOpp oy oy' →
        (∃ e : OrB Bd f hf p ≃ OrB Bd f hf q, e ox = oy ∧ e ox' = oy') ∧
        (∃ e : OrB Bd f hf p ≃ OrB Bd f hf q, e ox = oy' ∧ e ox' = oy) ∧
        ∀ e : OrB Bd f hf p ≃ OrB Bd f hf q,
          (e ox = oy ∧ e ox' = oy') ∨ (e ox = oy' ∧ e ox' = oy))

end RoundTrip.V6_31
