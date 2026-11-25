import Polyfold
/-! Blind formalization of V17_29 (the text's §17.1, Theorem 17.1.26, p. 759 of the Springer
2021 book; new in the 2021 edition).

Text: if `C` satisfies (ZHOU), the metrizable space `|C|` carries a natural equivalence class
`c_C` of polyfold structures (Definition 16.1.1), giving `(C, F, M) ↦ (|C|, c_C)`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` (metrizable `|C|`) with a polyfold structure
  `S : C.PolyfoldConstruction`; hypothesis `S.IsZhou` (Definition 17.1.22: some covering set's
  model satisfies (ZHOU)).
- "natural equivalence class": I read it as: there is a class `c` of polyfold structures on
  `|C|` (the project's `PolyfoldClass`, a quotient of `PolyfoldStructure` by the equivalence of
  Definition 16.1.2) such that, for EVERY covering set `Ψ`, the pair `(X_Ψ, |Γ_Ψ|)` is a polyfold
  structure on `|C|` (paracompact orbit space, (ZHOU), `|Γ_Ψ|` a homeomorphism) and lies in `c`.
  This makes `c` independent of the choice of `Ψ`, which is what "natural" means to me; it also
  determines `c` uniquely when a covering set exists.
- `X_Ψ` = `S.modelEP c.Ψ`, `Γ_Ψ` = `S.modelFunctor c.Ψ` (the text's constructions, from the
  vocabulary).  The proofs of the Definition 16.1.1 conditions are existentially quantified, so
  B asserts them.
- I did not use the project's `polyfoldClass` (it is the construction under audit).
- The assignment `(C, F, M) ↦ (|C|, c_C)` is not a separate claim beyond the existence of `c`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_29
open Polyfold

/-- Theorem 17.1.26: under (ZHOU), `|C|` carries a natural class `c_C` of polyfold structures,
containing `(X_Ψ, |Γ_Ψ|)` for every covering set `Ψ`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction), S.IsZhou →
    ∃ cl : PolyfoldClass C.toGroupoidStr.OrbitSpace,
      ∀ c : S.CoveringFamily,
        ∃ (hp : (S.modelEP c.Ψ).X.HasParacompactOrbitSpace) (hz : (S.modelEP c.Ψ).X.IsZhou)
          (hh : IsHomeomorph (S.modelFunctor c.Ψ).orbitMap),
          (⟦PolyfoldStructure.mk (S.modelEP c.Ψ) hp hz (hh.homeomorph _)⟧ :
              PolyfoldClass C.toGroupoidStr.OrbitSpace) = cl

end RoundTrip.V17_29
