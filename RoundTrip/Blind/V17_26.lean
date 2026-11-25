import Polyfold
/-! Blind formalization of V17_26 (the text's §17.1, Proposition 17.1.23, p. 758 of the
Springer 2021 book; new in the 2021 edition).

Text: if `C` satisfies (ZHOU), it has (LUC), (SLUC), (LR) and (SLR) (Theorems 7.4.13, 7.4.24).

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction` (`C = (C, F, M)`).
- "`C` has property P" (Definition 17.1.22): I read it as "the model `X_Ψ` of some covering set
  `Ψ` has P", which is what the project's `S.IsZhou`, `S.IsLUC`, `S.IsSLUC`, `S.IsLR`, `S.IsSLR`
  say (`#print`ed: `∃ c : S.CoveringFamily, P (S.modelEP c.Ψ)`, with P = (ZHOU) Definition
  7.4.5, (LUC) Definition 7.2.18, (SLUC) = (LUC) for every `Xⁱ` Definition 7.4.12, (LR)
  Definition 7.4.19, (SLR) = (LR) for every `Xⁱ` Definition 7.4.23).  I use these definitions.
- B is the conjunction of the four implications.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_26
open Polyfold

/-- Proposition 17.1.23: (ZHOU) for `C` implies (LUC), (SLUC), (LR), (SLR) for `C`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction), S.IsZhou →
    S.IsLUC ∧ S.IsSLUC ∧ S.IsLR ∧ S.IsSLR

end RoundTrip.V17_26
