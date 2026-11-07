import Polyfold
/-! Blind formalization of V6_55 (the text's §6.5, Definition 6.27, p. 220, and the objects of
Theorem 6.37, p. 228).

Text: `Or^f_x`, the set of the two orientations of `DET(f, x)`, is the object that `Γ_f` assigns
to the smooth point `x`.

Choices:
- The claim made is that `Or^f_x` (the orientations of `DET(f, x)`) has exactly two elements, at
  every smooth point `x`; B states that.  "Is the object that `Γ_f` assigns to `x`" is the
  definition of the object map of `Γ_f` (Theorem 6.37), not a separate claim; it is built into my
  formalization of Theorem 6.37 (`RoundTrip/Blind/V6_57.lean`, objects `Or^f_x`).
- Setting: as in `RoundTrip/Blind/V6_48.lean` (`X Y : Type`, `Bd : StrongBundle PX P`,
  `f` sc-Fredholm, `Bd.IsScFredholmSection f`), with `PX.IsTame`: the quote ties `Or^f_x` to the
  objects of Theorem 6.37, whose setting is a tame `X`.  (Without tameness B would be stronger.)
- `DET(f, x)` and `Or^f_x` (Definition 6.27): the project's `ChartPoint.detLin f p hf` and
  `ChartPoint.Or f p hf`, read in a chart point `p` at `x` (a strong bundle chart around `x` and
  the level-`1` lift of `φ(x)`).  Checked with `#print`: `Lin(f, x)` (`linSet`) is the set of
  operators `(f + s)'(x) + a : T_zO → K_z` for a (global) sc⁺-section `s` with `(f + s)(x) = 0`
  and an sc⁺-operator `a`; `DET(f, x)` is the determinant line bundle `DET(T_xX, Y_x)` pulled back
  to `Lin(f, x)`; `Or` is the type of its orientations (rays chosen continuously: locally the ray
  of a continuous non-vanishing section).  I quantify over EVERY chart point `p` at `x` (so the
  chosen chart of the project's `Orx` is included); the text's `Or^f_x` is chart independent up to
  the canonical identification, which preserves the number of elements.
- "The set of the two orientations": `Nat.card (Or^f_x) = 2` (which also says it is finite).
- DOUBT (not a misprint): `Or^f_x` has two elements only if `Lin(f, x) ≠ ∅`, i.e. if there is an
  sc⁺-section `s` with `s(x) = −f(x)`; otherwise the line bundle over the empty set has exactly
  one (empty) orientation.  The quote states no hypothesis giving such sections (usually they come
  from sc-smooth bump functions, Chapter 5), so B, stated with the text's hypotheses only, may be
  false in general.
-/
namespace RoundTrip.V6_55
open Polyfold

/-- At every smooth point `x` of a tame `X`, `Or^f_x` (read in any chart point at `x`) consists of
exactly two orientations. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame → ∀ x ∈ PX.smoothSet, ∀ p : ChartPoint Bd x,
      Nat.card (ChartPoint.Or f p hf) = 2

end RoundTrip.V6_55
