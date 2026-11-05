import Polyfold
/-! Blind formalization of V5_47 (the text's §5.4.2, Definition 5.28, p. 192).

Text: `X` admits sc-smooth partitions of unity if for every open covering there is a subordinate
sc-smooth partition of unity.

Choices:
- This item is a definition.  B says that the project's `PX.AdmitsScPartitionsOfUnity` is the
  text's notion `AdmitsScPOUB PX`, written below without Mathlib's `PartitionOfUnity`.
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, with an M-polyfold structure
  `PX : MPolyfold X` (Definition 2.13), as in `RoundTrip/Blind/V5_57.lean`.
- "open covering": a family `(U_λ)_{λ ∈ Λ}` of open subsets of `X` with union `X`, for EVERY index
  type `Λ : Type` (same universe as `X`; a cover indexed by a larger type can be re-indexed by the
  set of its members, so nothing is lost).
- "sc-smooth partition of unity" (`IsScPOUB`): a family `(β_λ)` of sc-smooth functions `X → ℝ`
  (the project's `PX.IsScSmoothMap realPolyfold`, Definition 2.14 with `ℝ` the one-chart
  M-polyfold, checked with `#print`; it includes continuity) with `β_λ ≥ 0`, the family of supports
  `supp(β_λ) = cl{β_λ ≠ 0}` locally finite, and `Σ_λ β_λ = 1` at every point (a finite sum there,
  `finsum`).  "Subordinate": `supp(β_λ) ⊆ U_λ` for every `λ`, same index set.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_47
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- An sc-smooth partition of unity `(β_λ)_{λ ∈ Λ}` on `X`: sc-smooth, non-negative, locally
finite supports, summing to `1`. -/
def IsScPOUB (PX : MPolyfold X) {Λ : Type} (β : Λ → X → ℝ) : Prop :=
  (∀ l, PX.IsScSmoothMap realPolyfold (β l)) ∧ (∀ l x, 0 ≤ β l x) ∧
  LocallyFinite (fun l => tsupport (β l)) ∧ ∀ x, ∑ᶠ l, β l x = 1

/-- **Definition 5.28**: every open covering `(U_λ)` of `X` has a subordinate sc-smooth partition
of unity `(β_λ)`, `supp(β_λ) ⊆ U_λ`. -/
def AdmitsScPOUB (PX : MPolyfold X) : Prop :=
  ∀ (Λ : Type) (U : Λ → Set X), (∀ l, IsOpen (U l)) → (⋃ l, U l) = Set.univ →
    ∃ β : Λ → X → ℝ, IsScPOUB PX β ∧ ∀ l, tsupport (β l) ⊆ U l

end

/-- Definition 5.28: the project's "admits sc-smooth partitions of unity" is the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsScPartitionsOfUnity ↔ AdmitsScPOUB PX

end RoundTrip.V5_47
