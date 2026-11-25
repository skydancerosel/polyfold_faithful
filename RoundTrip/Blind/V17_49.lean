import Polyfold
/-! Blind formalization of V17_49 (the text's §17.2, Proposition 17.2.12, p. 776 of the Springer
2021 book; new in the 2021 edition).

Text: there is a unique topology on `M(TΨ₁, TΨ₂)` making the maps (17.42) homeomorphisms onto
open sets.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and `hU : S.HasUniformizers` (`F(α) ≠ ∅` for every `α`).  The
  last hypothesis is needed only because the project's tangent uniformizers `TΨ` on objects
  (`S.tangentUnifObj hU Ψ`), hence the set `M(TΨ₁, TΨ₂)`, are built with it; the text
  presupposes that the reference uniformizers `Ψ_α ∈ F(α)` exist (pp. 769–771).
- `Ψ₁, Ψ₂` range over all uniformizers of `F` (`S.Unif`).
- `M(TΨ₁, TΨ₂)` = the project's `S.TTr hU Ψ₁ Ψ₂` (`#print`ed: the transition set
  (Definition 17.1.5) in `TC` of the tangent uniformizers on objects `TΨ₁, TΨ₂`).
- "the maps (17.42)": the project's `S.tangentTrChart hU T : TU(o) → M(TΨ₁, TΨ₂)`,
  `k ↦ (k, Φ_k, Tσ(k))`, for EVERY `o ∈ M(Ψ₁, Ψ₂)` and EVERY admissible triple `T` at `o`
  (`S.AdmissibleTriple o`, (17.6)), with `TU(o) = p⁻¹(U(o)) ⊆ TO₁` carrying the subspace topology
  of the tangent bundle `TO₁` (Part I).  These maps are the text's construction, taken from the
  vocabulary.
- "homeomorphism onto an open set" = Mathlib's `IsOpenEmbedding`.
- The project's `tangentTrTopology` (Definition 17.2.13) is not used.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_49
open Polyfold

/-- Proposition 17.2.12: exactly one topology on `M(TΨ₁, TΨ₂)` makes every map (17.42) an open
embedding. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif),
    ∃! τ : TopologicalSpace (S.TTr hU Ψ₁ Ψ₂),
      ∀ (o : S.Tr Ψ₁ Ψ₂) (T : S.AdmissibleTriple o),
        @Topology.IsOpenEmbedding _ _ _ τ (S.tangentTrChart hU T)

end RoundTrip.V17_49
