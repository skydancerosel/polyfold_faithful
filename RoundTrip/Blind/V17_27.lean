import Polyfold
/-! Blind formalization of V17_27 (the text's §17.1, Proposition 17.1.24, p. 758 of the
Springer 2021 book; new in the 2021 edition).

Text: if `C` has one of (LR), (SLR), (LUC), (SLUC), (ZHOU), then `X_Ψ` has it for every
covering set `Ψ`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`; "covering set" = `S.CoveringFamily`; `X_Ψ` = the project's
  model `S.modelEP c.Ψ` (Theorem 17.1.14).
- "`C` has P" (Definition 17.1.22) = the project's `S.IsLR` etc. (`#print`ed: some covering set's
  model has P).  "`X_Ψ` has P": `(S.modelEP c.Ψ).X.IsLR`, `EP.IsSLR`, `.X.IsLUC`, `EP.IsSLUC`,
  `.X.IsZhou` (the Chapter 7 definitions 7.4.19, 7.4.23, 7.2.18, 7.4.12, 7.4.5).
- "one of": B is the conjunction, over the five properties, of "C has it ⇒ every model has it".
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_27
open Polyfold

/-- Proposition 17.1.24: a model property of `C` holds for every model `X_Ψ`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction),
    (S.IsLR → ∀ c : S.CoveringFamily, (S.modelEP c.Ψ).X.IsLR) ∧
    (S.IsSLR → ∀ c : S.CoveringFamily, (S.modelEP c.Ψ).IsSLR) ∧
    (S.IsLUC → ∀ c : S.CoveringFamily, (S.modelEP c.Ψ).X.IsLUC) ∧
    (S.IsSLUC → ∀ c : S.CoveringFamily, (S.modelEP c.Ψ).IsSLUC) ∧
    (S.IsZhou → ∀ c : S.CoveringFamily, (S.modelEP c.Ψ).X.IsZhou)

end RoundTrip.V17_27
