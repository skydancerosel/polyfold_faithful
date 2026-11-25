import Polyfold
/-! Blind formalization of V17_60 (the text's §17.3, Proposition 17.3.4, p. 784 of the Springer
2021 book; new in the 2021 edition).

Text: Definitions 17.3.1 and 17.3.2 are equivalent.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and `hc : S.HasCoveringUniformizers` (the footprints of `F` cover
  `|C|`).  The last hypothesis is presupposed by Definition 17.3.2, which speaks of an sc-smooth
  model `X_Ψ` of `C` (a covering set, p. 752); without it no model exists and the two
  definitions trivially differ (on `A = ∅`).
- A full subcategory is given by its set `A ⊆ obj(C)` of objects ("saturated" =
  `GroupoidStr.IsSaturated`, `π⁻¹(π(A)) = A`).
- Definition 17.3.1 (written out here; the project's `IsSubpolyfold` is not used, though its
  `#print`ed body is the same): `A` is saturated and for every `α ∈ A` and every `Ψ ∈ F(α)`,
  `A_Ψ = Ψ⁻¹(A)` is a sub-M-polyfold of `O` (`MPolyfold.IsSubMPolyfold`, Definition 2.3.18).
- Definition 17.3.2 (written out here; the project's `IsSubpolyfoldModel` is not used): `A` is
  saturated and, for a suitable sc-smooth model, i.e. for SOME covering family `c`,
  `Γ_Ψ⁻¹(A)` is an ep-subgroupoid of `X_Ψ` (`EpGroupoid.IsEpSubgroupoid`, Definition 7.1.21),
  where `X_Ψ` = the project's `S.modelEP c.Ψ` and `Γ_Ψ` = `S.modelFunctor c.Ψ` ((17.10)), the
  text's constructions.  "Suitable" is read as "some"; the reading "every" would give a
  different (stronger) Definition 17.3.2.
- B: for every `A`, Definition 17.3.1 ↔ Definition 17.3.2.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_60
open Polyfold

/-- Definition 17.3.1: `A` is a subpolyfold. -/
def Def1 {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj) : Prop :=
  C.toGroupoidStr.IsSaturated A ∧
    ∀ α ∈ A, ∀ Ψ ∈ S.F α, Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)

/-- Definition 17.3.2: `A` is a subpolyfold, through an sc-smooth model. -/
def Def2 {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj) : Prop :=
  C.toGroupoidStr.IsSaturated A ∧
    ∃ c : S.CoveringFamily,
      (S.modelEP c.Ψ).X.IsEpSubgroupoid ((S.modelFunctor c.Ψ).obj ⁻¹' A)

/-- Proposition 17.3.4: Definitions 17.3.1 and 17.3.2 are equivalent. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction), S.HasCoveringUniformizers →
    ∀ A : Set C.Obj, Def1 S A ↔ Def2 S A

end RoundTrip.V17_60
