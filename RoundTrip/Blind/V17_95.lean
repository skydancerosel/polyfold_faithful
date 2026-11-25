import Polyfold
/-! Blind formalization of V17_95 (the text's Part II, §17.5, Proposition 17.5.2, p. 813 of the
Springer 2021 book; 2017: Proposition 17.8).

Text: (1) if `Θ` is a branched ep⁺-subgroupoid of `X_Ψ`, then `(Γ_Ψ)_*Θ` is a branched
ep⁺-subcategory; (2) if `Θ` is a branched ep⁺-subcategory, then `Γ_Ψ^*Θ` is a branched
ep⁺-subgroupoid.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction` (`C = (C, F, M)`), and a covering family `Ψ` (`S.CoveringFamily`,
  p. 752): `X_Ψ` and `Γ_Ψ : X_Ψ → C` are defined in §17.1 for covering families, so I read `Ψ`
  as a covering family (not an arbitrary family of uniformizers).
- `X_Ψ` = the project's ep-groupoid `S.modelEpGroupoid c.Ψ` (Theorem 17.1.14, the text's
  construction from the vocabulary).  "branched ep⁺-subgroupoid" = the project's
  `EpGroupoid.IsBranchedEpSubgroupoid` (Definition 9.1.2).  "branched ep⁺-subcategory" = the
  project's `S.IsBranchedSubcategory` (Definition 17.5.1: a functor `Θ : C → ℚ⁺` with `Θ ∘ Ψ` a
  branched ep⁺-subgroupoid of `G ⋉ O` for every `α` and `Ψ ∈ F(α)`).
- `(Γ_Ψ)_*Θ` = the project's `S.modelPush c.Ψ Θ` (p. 812: `(Γ_*Θ)(α) = Θ(x)` for an `x` with a
  morphism `Γ(x) → α`; for a covering family such an `x` exists for every `α`, so no junk value
  is reached).  `Γ_Ψ^*Θ = Θ ∘ Γ_Ψ` = the project's `S.modelPull c.Ψ Θ`.
- B is the conjunction of (1) and (2), for every covering family.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_95
open Polyfold

/-- Proposition 17.5.2: push-forward along `Γ_Ψ` of a branched ep⁺-subgroupoid of `X_Ψ` is a
branched ep⁺-subcategory, and pull-back of a branched ep⁺-subcategory is a branched
ep⁺-subgroupoid of `X_Ψ`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (c : S.CoveringFamily),
    (∀ Θ : S.ModelObj c.Ψ → ℚ, (S.modelEpGroupoid c.Ψ).IsBranchedEpSubgroupoid Θ →
      S.IsBranchedSubcategory (S.modelPush c.Ψ Θ)) ∧
    (∀ Θ : C.Obj → ℚ, S.IsBranchedSubcategory Θ →
      (S.modelEpGroupoid c.Ψ).IsBranchedEpSubgroupoid (S.modelPull c.Ψ Θ))

end RoundTrip.V17_95
