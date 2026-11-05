import Polyfold
/-! Blind formalization of V5_57 (the text's §5.4.2, Theorem 5.37, p. 195).

Text: (i) `X` admits sc-smooth partitions of unity subordinate to any open cover iff (ii) `X`
admits an atlas consisting of local models having the sc-smooth approximation property.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, with an M-polyfold structure
  `PX : MPolyfold X` (Definition 2.13).  B is the equivalence for every such `(X, PX)`.
- (i): the project's `PX.AdmitsScPartitionsOfUnity` (Definition 5.28, checked with `#print`: for
  every index type `ι : Type` and every open cover `(U_i)` of `X` there is a Mathlib
  `PartitionOfUnity ι X` (locally finite, nonnegative, summing to `1`) subordinate to it
  (`tsupport ρ_i ⊆ U_i`) all of whose functions are sc-smooth `X → ℝ`, `ℝ` with its one-chart
  M-polyfold structure).
- "sc-smooth approximation property" of a local model `(O, C, E)`: the project's
  `LocalModel.HasApproxProperty` (Definition 5.36, checked with `#print` against the text's
  Definition 5.36: for every `V = O ∩ W`, `W` open in `E_0`, with `cl(V) ⊆ O` (closure in `E_0`,
  equal to the closure in the closed `C`), every `f : O → [0, 1]` continuous on `O` with
  `supp_O(f) ⊆ V` and every `ε > 0`, an sc-smooth `g : O → [0, 1]` with `supp_O(g) ⊆ V` and
  `|f − g| ≤ ε` on `O`).
- (ii) "admits an atlas consisting of local models having the property": an atlas `A` of the
  given M-polyfold structure, i.e. equivalent to `PX.atlas` (`MAtlas.Equiv`, Definition 2.12: the
  union is an atlas), all of whose charts have a local model with the approximation property.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_57
open Polyfold

/-- Theorem 5.37: an M-polyfold admits sc-smooth partitions of unity subordinate to every open
cover iff it has an (equivalent) atlas whose local models have the sc-smooth approximation
property. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsScPartitionsOfUnity ↔
      ∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, φ.model.HasApproxProperty

end RoundTrip.V5_57
