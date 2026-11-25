import Polyfold
/-! Blind formalization of V17_35 (the text's §17.1, Corollary 17.1.29, p. 766 of the Springer
2021 book; new in the 2021 edition).

Text: if `C` satisfies (ZHOU), (SLUC) or (SLR), so does `C¹`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and `hc : S.HasCoveringUniformizers` (the footprints of the
  uniformizers of `F` cover `|C|`; the text presupposes this, since `C¹` and its topology are
  built from a covering set, p. 766).
- `C¹` with its polyfold structure `(F¹, M_{F¹})` of Theorem 17.1.28 = the project's
  `S.levelOneGCT hc` and `S.levelOneConstruction hc` (the text's construction, taken from the
  vocabulary).
- "`C` satisfies P" (Definition 17.1.22) = the project's `IsZhou`, `IsSLUC`, `IsSLR` (some
  covering set's model has P).
- "or": B is the conjunction of the three implications P(C) ⇒ P(C¹).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_35
open Polyfold

/-- Corollary 17.1.29: (ZHOU), (SLUC), (SLR) pass from `C` to `C¹`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers),
    (S.IsZhou → (S.levelOneConstruction hc).IsZhou) ∧
    (S.IsSLUC → (S.levelOneConstruction hc).IsSLUC) ∧
    (S.IsSLR → (S.levelOneConstruction hc).IsSLR)

end RoundTrip.V17_35
