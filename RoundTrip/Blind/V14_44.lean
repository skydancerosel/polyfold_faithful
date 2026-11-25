import Polyfold
/-! Blind formalization of V14_44 (the Springer 2021 book, Part II, §14.1, Proposition 14.1.8,
p. 645; 2017: Proposition 14.1).

Text: for a generalized strong bundle isomorphism `𝔣 : W → W'` between strong bundles over tame
ep-groupoids with paracompact orbit spaces, and `Λ`, `Λ'` structurable over the boundary,
`𝔣̄_*Λ` and `𝔣̄^*Λ'` are structurable over the boundary.

Choices:
- Setting: universe 0; strong bundles over ep-groupoids `SEP.{0}`; generalized strong bundle maps
  `GenSBMap A A'` and generalized strong bundle isomorphisms `GenSBMap.IsGeneralizedIso`
  (Definition 10.5.2, the class of a diagram `W ←Φ W'' →Ψ W'` with both legs strong bundle
  equivalences), as in `V11_30.lean`, `V11_32.lean`.
- "tame ep-groupoid with paracompact orbit space": the project's `EpGroupoid.IsTame` and
  `EpGroupoid.HasParacompactOrbitSpace` (`#print`ed: `X.PObj.IsTame`, `ParacompactSpace |X|`), for
  both `X` and `X'`.
- `Λ : W|∂X → ℚ⁺` is represented by a functor `W → ℚ⁺` whose values off `W|∂X` are ignored;
  "structurable over the boundary" is the project's `IsBoundaryStructurable` (Definition 14.1.7:
  an sc⁺-multisection over `∂X` with a good system for `∂X`, symmetric structures and
  correspondences `τ`; `#print`ed, it only looks at `W|∂X`).
- `𝔣̄_*Λ` and `𝔣̄^*Λ'`: the project's `GenSBMap.pushMult hf Λ` (`Ψ_*Φ^*Λ` on a chosen
  representative, p. 548) and `GenSBMap.pullMult hf Λ'` (`Φ_*Ψ^*Λ'`), the operations of
  Proposition 11.5.3 used in `V11_32.lean`, applied to functors on `W|∂X` (equivalences preserve
  the degeneracy index, so the values over `∂X'` only involve values over `∂X`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V14_44
open Polyfold Polyfold.SBLocalization

/-- Proposition 14.1.8. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A'.X.IsTame → A'.X.HasParacompactOrbitSpace →
      (∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ →
        IsBoundaryStructurable A' (GenSBMap.pushMult hf Λ)) ∧
      (∀ Λ' : A'.W → ℚ≥0, IsBoundaryStructurable A' Λ' →
        IsBoundaryStructurable A (GenSBMap.pullMult hf Λ'))

end RoundTrip.V14_44
