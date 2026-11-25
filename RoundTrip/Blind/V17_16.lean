import Polyfold
/-! Blind formalization of V17_16 (the text's Part II, §17.1, Theorem 17.1.14, p. 753 of the
Springer 2021 book; 2017: Theorem 17.1).

Text: for a covering family `Ψ`, `X_Ψ` is an ep-groupoid, tame if `(F, M)` is tame.

Choices:
- Setting: a GCT `C : GCT` (Definition 17.1.1; universe `0`) with a polyfold structure
  `S = (F, M) : C.PolyfoldConstruction` (Definition 17.1.8), a covering family
  `Ψ = (Ψ_λ)_{λ ∈ Λ}` of uniformizers of `F` whose footprints cover `|C|` (the project's
  `S.CoveringFamily`, p. 752).
- `X_Ψ` (p. 753): objects `X = ⊔_λ O_λ` with the disjoint-union M-polyfold structure, morphisms
  `𝐗 = ⊔_{(λ, λ')} M(Ψ_λ, Ψ_λ')` with the M-polyfold structures `M`, and the small category of
  p. 753.  I use the project's DATA for these: `S.ModelObj`, `S.ModelMor` (`#print`ed: the sigma
  types), `S.modelObjPolyfold`, `S.modelMorPolyfold` and the category `S.modelGroupoid`.  I pin
  the source and target of `S.modelGroupoid` to the text's `s(q_λ, φ, q_λ') = q_λ`,
  `t(q_λ, φ, q_λ') = q_λ'` (the units, inverses and composition are not pinned).
- I do NOT use the project's `S.modelEpGroupoid` (which is already of type `EpGroupoid`, so its
  existence would make the claim trivial).  "`X_Ψ` is an ep-groupoid" is stated as: there is an
  `EpGroupoid` (Definition 7.1.3) whose groupoid is `S.modelGroupoid`, whose object M-polyfold is
  `S.modelObjPolyfold` and whose morphism M-polyfold is `S.modelMorPolyfold`.
- "`(F, M)` tame": the project's `PolyfoldConstruction.IsTame` (Definition 17.1.8, `#print`ed:
  every uniformizer in every `F(α)` is tame, i.e. its `O` is tame).  "`X_Ψ` tame" (Definition
  7.1.6): the object M-polyfold `⊔_λ O_λ` is tame.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_16
open Polyfold

/-- Theorem 17.1.14: `X_Ψ` is an ep-groupoid (with the text's source and target maps), tame if
`(F, M)` is tame. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (c : S.CoveringFamily),
    -- the source and target maps of the category `X_Ψ`
    (∀ (pr : c.ι × c.ι) (a : S.Tr (c.Ψ pr.1) (c.Ψ pr.2)),
      (S.modelGroupoid c.Ψ).src ⟨pr, a⟩ =
          ⟨pr.1, GroupoidStr.TransitionSet.src (a : (c.Ψ pr.1).1.Trans (c.Ψ pr.2).1)⟩ ∧
      (S.modelGroupoid c.Ψ).tgt ⟨pr, a⟩ =
          ⟨pr.2, GroupoidStr.TransitionSet.tgt (a : (c.Ψ pr.1).1.Trans (c.Ψ pr.2).1)⟩) ∧
    -- `X_Ψ` is an ep-groupoid
    (∃ X : EpGroupoid (S.ModelObj c.Ψ) (S.ModelMor c.Ψ),
      X.toGroupoidStr = S.modelGroupoid c.Ψ ∧ X.PObj = S.modelObjPolyfold c.Ψ ∧
        X.PMor = S.modelMorPolyfold c.Ψ) ∧
    -- tame if `(F, M)` is tame
    (S.IsTame → (S.modelObjPolyfold c.Ψ).IsTame)

end RoundTrip.V17_16
