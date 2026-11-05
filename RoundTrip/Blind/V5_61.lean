import Polyfold
/-! Blind formalization of V5_61 (the text's §5.4.2, Proposition 5.42, p. 198).

Text: (i) a reflexive `E` is WCG; (ii) a separable `E` is WCG.

Choices:
- Setting: every real Banach space `V : Type` (universe 0, as asked; the text's `E` is a Banach
  space).  B is the conjunction of (i) and (ii).
- "reflexive": the project's `IsReflexive V` (checked with `#print`: the canonical map
  `V → V''`, Mathlib's `NormedSpace.inclusionInDoubleDual`, is onto) — the standard definition.
- "WCG": the project's `IsWCG V` (Definition 5.41, checked with `#print`: some `K` compact in the
  weak topology, `toWeakSpace ℝ V '' K` compact in Mathlib's `WeakSpace ℝ V`, with
  `cl_V(span K) = V`); see `RoundTrip/Blind/V5_60.lean`.
- "separable": Mathlib's `TopologicalSpace.SeparableSpace V` (norm topology).
- Nothing looks false to me.
-/
namespace RoundTrip.V5_61
open Polyfold

/-- Proposition 5.42: reflexive Banach spaces and separable Banach spaces are WCG. -/
def B : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V],
    (IsReflexive V → IsWCG V) ∧ (TopologicalSpace.SeparableSpace V → IsWCG V)

end RoundTrip.V5_61
