import Polyfold
/-! Blind formalization of V2_60 (the text's §2.5, Definition 2.53, p. 53).

Text: for a strong bundle `P : Y → X` and an sc-smooth map `f : Z → X`, the pull-back is
`f*Y = {(z, y) ∈ Z × Y | P(y) = f(z)}` with `P_f(z, y) = z` and `P'(z, y) = y`, and
`P ∘ P' = f ∘ P_f`.

Choices:
- This item is a definition plus one property (`P ∘ P' = f ∘ P_f`).  B says the project's
  `pullbackSpace`, `pullbackProj` (`P_f`), `pullbackProj'` (`P'`) are my definitions of the text's
  notions, that `f*Y` carries the subspace topology of `Z × Y` (implicit in the text: `f*Y` is a
  subset of `Z × Y`; the instance found on `↥(pullbackSpace P f)` is Mathlib's
  `instTopologicalSpaceSubtype`, checked with `#synth`), and the identity `P ∘ P' = f ∘ P_f`.
- Setting (as in my `RoundTrip/Blind/V2_58.lean` and `V2_61.lean`): `X Y Z : Type` (universe 0;
  the project's definitions are universe-polymorphic), `X`, `Z` M-polyfolds (`PX`, `PZ`), `Y`
  Hausdorff paracompact with fibre linear structures as instances, `Bd : StrongBundle PX P`
  (Definition 2.51), `f` sc-smooth (`PZ.IsScSmoothMap PX f`, Definition 2.14).  These are the
  text's hypotheses; the definitions and the identity do not use them.
- `f*Y` as a set: `{p : Z × Y | P p.2 = f p.1}` (my `pullbackB`); the projections as functions on
  the subtype.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_60
open Polyfold

/-- **Definition 2.53**: the pull-back `f*Y = {(z, y) ∈ Z × Y | P(y) = f(z)}`. -/
def pullbackB {X Y Z : Type} (P : Y → X) (f : Z → X) : Set (Z × Y) :=
  {p | P p.2 = f p.1}

/-- **Definition 2.53**: `P_f : f*Y → Z`, `P_f(z, y) = z`. -/
def projB {X Y Z : Type} (P : Y → X) (f : Z → X) : pullbackB P f → Z :=
  fun p => p.1.1

/-- **Definition 2.53**: `P' : f*Y → Y`, `P'(z, y) = y`. -/
def projB' {X Y Z : Type} (P : Y → X) (f : Z → X) : pullbackB P f → Y :=
  fun p => p.1.2

/-- Definition 2.53: the project's pull-back `f*Y ⊆ Z × Y` (with the subspace topology) and its
projections `P_f`, `P'` are the text's, and `P ∘ P' = f ∘ P_f`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] [T2Space Y] [ParacompactSpace Y]
    {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (PZ : MPolyfold Z)
    (_Bd : StrongBundle PX P) (f : Z → X),
    PZ.IsScSmoothMap PX f →
      -- the set `f*Y`, with the topology of a subspace of `Z × Y`
      pullbackSpace P f = pullbackB P f ∧
      (inferInstance : TopologicalSpace (pullbackSpace P f)) =
        TopologicalSpace.induced (Subtype.val : pullbackSpace P f → Z × Y) inferInstance ∧
      -- the projections `P_f(z, y) = z`, `P'(z, y) = y`
      (∀ (w : pullbackSpace P f) (w' : pullbackB P f), w.1 = w'.1 →
        pullbackProj P f w = projB P f w' ∧ pullbackProj' P f w = projB' P f w') ∧
      -- `P ∘ P' = f ∘ P_f`
      P ∘ pullbackProj' P f = f ∘ pullbackProj P f

end RoundTrip.V2_60
