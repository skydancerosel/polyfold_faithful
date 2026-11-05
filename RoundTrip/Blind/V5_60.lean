import Polyfold
/-! Blind formalization of V5_60 (the text's §5.4.2, Definition 5.41, p. 198).

Text: `E` is weakly compactly generated if there is a weakly compact `K` with
`E = cl_E(span K)`.

Choices:
- This item is a definition.  B says that the project's `IsWCG V` is the text's notion `IsWCGB V`
  written below, for every real Banach space `V : Type` (universe 0, as asked; the text's `E` is a
  Banach space).
- "weakly compact": compact for the weak topology `σ(V, V*)`, which I define myself (`weakTopB`:
  the coarsest topology making every continuous linear functional `V → ℝ` continuous), not via
  Mathlib's `WeakSpace` (which the project uses).
- "`E = cl_E(span K)`": the norm closure of the linear span of `K` is all of `V`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_60
open Polyfold

/-- The weak topology `σ(V, V*)` of a normed space. -/
@[instance_reducible]
def weakTopB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : TopologicalSpace V :=
  ⨅ ℓ : V →L[ℝ] ℝ, TopologicalSpace.induced ℓ inferInstance

/-- **Definition 5.41**: `V` is weakly compactly generated: some weakly compact `K ⊆ V` has dense
linear span. -/
def IsWCGB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∃ K : Set V, @IsCompact V (weakTopB V) K ∧
    closure (Submodule.span ℝ K : Set V) = Set.univ

/-- Definition 5.41: the project's WCG spaces are the text's. -/
def B : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V], IsWCG V ↔ IsWCGB V

end RoundTrip.V5_60
