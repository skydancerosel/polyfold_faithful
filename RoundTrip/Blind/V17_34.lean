import Polyfold
/-! Blind formalization of V17_34 (the text's §17.1, pp. 765–766 of the Springer 2021 book;
2017: §17.1).

Text: `|C_i|` has a natural metrizable topology from `|X^i|`, and `C^{i+1} := (C^i)^1`.

Choices:
- Setting: universe `0`: `X : GCT.UniformizedPolyfold.{0}` (a GCT `C = X.cat` with a polyfold
  structure `S = X.str` in which every object has a uniformizer, `F(α) ≠ ∅`; the project's setting
  for iterating `C ↦ C¹`, and the text presupposes it when it forms `C^i` for all `i`).
- `C_i` = the full subcategory of the objects of regularity `i` (p. 766) = the project's
  `S.regSub i`; `X^i` = the `i`-fold index raise of the model `X_Ψ` of a covering set `Ψ`
  (`(S.modelEP c.Ψ).lift i`), and `Γ_Ψ^i : X_Ψ^i → C_i` = the project's `S.modelFunctorLevel c.Ψ i`
  (`Γ_Ψ` on the level-`i` points).  These are the text's constructions, from the vocabulary.
- "natural topology from `|X^i|`": I read it as a topology `T` on `|C_i|` for which `|Γ_Ψ^i|` is a
  homeomorphism `|X_Ψ^i| → |C_i|` for EVERY covering set `Ψ` (so `T` is transported from `|X^i|`
  and does not depend on `Ψ`); "metrizable" for `T`.  I do not use the project's
  `levelTopology`.
- "`C^{i+1} := (C^i)^1`" is a definition (the project's `UniformizedPolyfold.level`); the claim
  I attach to it is that the GCT `C^i` so defined has orbit space `|C^i|` homeomorphic to
  `(|C_i|, T)` through its identification with `C_i` (`X.levelEquivSub i`, the inclusion
  `C^i → C` corestricted to `C_i`).  This last conjunct is my reading of how the two halves of
  the sentence fit together; drop it if the text means the recursion only as a definition.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_34
open Polyfold

/-- The levels `|C_i|` carry a natural metrizable topology, transported from `|X_Ψ^i|`, and it is
the topology of the GCT `C^i`. -/
def B : Prop :=
  ∀ (X : GCT.UniformizedPolyfold.{0}) (i : ℕ),
    ∃ T : TopologicalSpace (X.str.regSub i).OrbitSpace,
      letI := T
      TopologicalSpace.MetrizableSpace (X.str.regSub i).OrbitSpace ∧
      (∀ c : X.str.CoveringFamily, IsHomeomorph (X.str.modelFunctorLevel c.Ψ i).orbitMap) ∧
      IsHomeomorph (X.levelEquivSub i).orbitMap

end RoundTrip.V17_34
