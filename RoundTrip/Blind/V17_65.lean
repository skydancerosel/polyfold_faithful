import Polyfold
/-! Blind formalization of V17_65 (the text's §17.3, Proposition 17.3.8, p. 787 of the Springer
2021 book; 2017: Proposition 17.7).

Text: if the tame `C` is face-structured, every face is a subpolyfold.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, tame (`S.IsTame`, Definition 17.1.8: all uniformizers of `F` are
  tame).
- The degeneracy index `d_{|C|}`, the faces and "face-structured" (Definition 17.3.7) are read
  through the sc-smooth model `X_c` of a covering family `c`: the project's `S.degIndexVia c`
  (`#print`ed: `d_{|X_c|}` at `|Γ_c|⁻¹(z)`), `S.IsFaceVia c θ` (`#print`ed: `θ ⊆ |C|` is the
  closure of a connected component of `{z | d(z) = 1}`) and `S.IsFaceStructuredVia c`
  (`#print`ed: tame and every `z` lies in exactly `d(z)` faces).  The text's notions do not
  depend on the model; B quantifies over EVERY covering family `c` and uses the same `c` in
  hypothesis and conclusion.
- The face `C_θ` is the full subcategory on `π⁻¹(θ) = {α | |α| ∈ θ}` (the project's `faceSub`
  is the same full subcategory; I use the set `π⁻¹(θ)`).
- "subpolyfold" = Definition 17.3.1, written out here (`Def1`): `π⁻¹(θ)` is saturated and for
  every `α` in it and every `Ψ ∈ F(α)`, `Ψ⁻¹(π⁻¹(θ))` is a sub-M-polyfold of `O`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_65
open Polyfold

/-- Definition 17.3.1: `A` is a subpolyfold. -/
def Def1 {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj) : Prop :=
  C.toGroupoidStr.IsSaturated A ∧
    ∀ α ∈ A, ∀ Ψ ∈ S.F α, Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)

/-- Proposition 17.3.8: in a tame face-structured `C` every face `C_θ` is a subpolyfold. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (c : S.CoveringFamily),
    S.IsTame → S.IsFaceStructuredVia c →
      ∀ θ : Set C.toGroupoidStr.OrbitSpace, S.IsFaceVia c θ →
        Def1 S (C.toGroupoidStr.π ⁻¹' θ)

end RoundTrip.V17_65
