import Polyfold
/-! Blind formalization of V17_102 (the text's Part II, §17.5, Proposition 17.5.7 and (17.86),
p. 816 of the Springer 2021 book; 2017: Proposition 17.10).

Text: `TΘ` defines a section functor `C_∞ → Gr(C)`, given on a model by (17.86); the proof is
left to the reader.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, with `hU : S.HasUniformizers` (`F(α) ≠ ∅` for every `α`; the
  project's tangent category `TC`, the functor `ν` and `Gr(C)` need it, and the text's tangent
  spaces `T_αC` (§17.2) are built from some `Ψ ∈ F(α)`, so I read it as presupposed), and a
  branched ep⁺-subcategory `Θ` (`S.IsBranchedSubcategory Θ`, Definition 17.5.1).
- `C_∞` = the project's full subcategory `S.regSubInf` (objects of regularity `∞`), as a Mathlib
  category `S.regSubInf.Ob`.  `Gr(C)` = the category of elements of the functor
  `ν : C_∞ → SET`, `ν(α) = Gr(α)`, `ν(φ)(∑ σ_L L) = ∑ σ_L Tφ(L)` (p. 815) = the project's
  `S.grFunctorC hU` (the text's construction, from the vocabulary); `Gr(C) → C_∞` is Mathlib's
  `CategoryOfElements.π`.
- "section functor": a functor `F : C_∞ → Gr(C)` with `π ∘ F = 1` (equality of functors).  The
  existence of such `F` with prescribed values on objects encodes the functoriality
  `ν(φ)(TΘ(α)) = TΘ(α')` for `φ : α → α'`.
- "given on a model by (17.86)": the value `TΘ(α) ∈ Gr(α)` is `(TΓ_Ψ)_*(T(Γ_Ψ^*Θ))(α)`, i.e.
  `Tφ(TΓ(TΘ∘Γ(x)))` for an `x` of `X_Ψ` and `φ : Γ(x) → α` = the project's
  `S.tangentSectionVia hU c.Ψ Θ α`.  I require this for EVERY covering family `Ψ` (which also
  says the value does not depend on `Ψ`, as Definition 17.5.6 presupposes).  I do not use the
  project's `tangentSectionFunctorC` or `branchedTangentSection` (the constructions under audit).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_102
open Polyfold CategoryTheory

/-- Proposition 17.5.7: `TΘ` is a section functor `C_∞ → Gr(C)`, with value (17.86) computed on
the model of any covering family. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hU : S.HasUniformizers) (Θ : C.Obj → ℚ),
    S.IsBranchedSubcategory Θ →
    ∃ F : S.regSubInf.Ob ⥤ (S.grFunctorC hU).Elements,
      F ⋙ CategoryOfElements.π (S.grFunctorC hU) = 𝟭 _ ∧
      ∀ (α : S.regSubInf.Ob) (c : S.CoveringFamily),
        Subtype.val
          ((F.obj α).2 : ↥(S.GrC (GCT.PolyfoldConstruction.smoothObjVal (F.obj α).1))) =
          S.tangentSectionVia hU c.Ψ Θ (GCT.PolyfoldConstruction.smoothObjVal (F.obj α).1)

end RoundTrip.V17_102
