import Polyfold
/-! Blind formalization of V2_62 (the text's §2.6.2, Theorem 2.55, p. 56; Smirnov's metrization
theorem, quoted by the text).

Text: a paracompact Hausdorff space in which every point has a metrizable open neighbourhood is
metrizable.

Choices:
- Setting: a topological space `X : Type` (universe 0, as asked) with `[T2Space X]` and
  `[ParacompactSpace X]` (Mathlib's paracompactness: every open cover has a locally finite open
  refinement).  Pure point-set topology; no project definitions are used.
- "every point has a metrizable open neighbourhood": for every `x` there is an open `U ∋ x` such
  that `U` with the subspace topology is metrizable (`TopologicalSpace.MetrizableSpace ↥U`).
- "metrizable": `TopologicalSpace.MetrizableSpace X` (some metric induces the topology).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_62
open Polyfold

/-- Smirnov: a paracompact Hausdorff space which is locally metrizable (every point has a
metrizable open neighbourhood) is metrizable. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X],
    (∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ TopologicalSpace.MetrizableSpace U) →
      TopologicalSpace.MetrizableSpace X

end RoundTrip.V2_62
