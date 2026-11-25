import Polyfold
/-! Blind formalization of V14_8 (the Springer 2021 book, Part II, §14.1, Theorem 14.1.9,
p. 646, the ∂-extension theorem; 2017: Theorem 14.2).

Text: assume `X` is tame, with `|X|` paracompact and sc-smooth partitions of unity; `Λ` on
`W|∂X` is structurable; `N` is an auxiliary norm; `Ũ` is a saturated open set containing
`dom-supp(Λ)`; `f ≥ 0` is a continuous functor supported in `Ũ` with `N(Λ) < f` on
`dom-supp(Λ)`.  Then there is a structurable `Λ' : W → ℚ⁺` with (1) `N(Λ') ≤ f`;
(2) `dom-supp(Λ') ⊆ Ũ`; (3) `Λ'|W|∂X = Λ`.

Choices:
- Setting: universe 0; the strong bundle `P : W → X` over the ep-groupoid is `A : SEP.{0}`.
- "`X` tame": `A.X.IsTame` (Definition 7.1.6: the object M-polyfold is tame); "`|X|`
  paracompact": `A.X.HasParacompactOrbitSpace`; "sc-smooth partitions of unity": the
  ep-groupoid notion `A.X.HasScPartitionsOfUnity` (Definition 7.5.5; the alternative reading is
  the object M-polyfold's `MPolyfold.AdmitsScPartitionsOfUnity`).
- `Λ : W|∂X → ℚ⁺` is a function `A.W → ℚ≥0` of which only the values over `∂X`
  (`A.X.PObj.boundary`) matter; "structurable": the project's `IsBoundaryStructurable`
  (`#print`ed: `IsBoundaryScPlusMultisection A Λ ∧ ∃ D : BoundaryDecoration A Λ, Nonempty D.Tau`,
  Definitions 14.1.3, 14.1.5, 14.1.7).
- `N`: an auxiliary norm `N : W_{0,1} → ℝ` with `A.E.IsAuxNorm N` (Definition 8.3.5);
  `N(Λ)(x)`: `pointwiseNorm N Λ x` (Definition 13.2.3, a supremum over the support at `x`).
- `dom-supp(Λ)` of `Λ` on `W|∂X`: the project's `boundaryDomSupp` (`#print`ed: the closure of
  the `x ∈ ∂X` over which `Λ` charges a nonzero point); `dom-supp(Λ')`: `domSupp` (the same over
  all of `X`).
- `Ũ` "saturated open": open with `GroupoidStr.IsSaturated` (`#print`ed: `π⁻¹(π(Ũ)) = Ũ`).
- `f`: `f : X → ℝ`, continuous, `f ≥ 0`, a functor (`f(s(φ)) = f(t(φ))` for every morphism),
  "supported in `Ũ`": `tsupport f ⊆ Ũ` (the closed support).  `N(Λ)(x) < f(x)` for
  `x ∈ dom-supp(Λ)`.
- Conclusion: `Λ'` structurable (the project's `IsStructurable`, Definition 13.3.6, which includes
  being an sc⁺-multisection functor); (1) `N(Λ')(x) ≤ f(x)` for all `x`; (2)
  `dom-supp(Λ') ⊆ Ũ`; (3) `Λ'(w) = Λ(w)` for all `w` over `∂X`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V14_8
open Polyfold Polyfold.SBLocalization

/-- Theorem 14.1.9 (∂-extension theorem). -/
def B : Prop :=
  ∀ A : SEP.{0}, A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.HasScPartitionsOfUnity →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ →
  ∀ N : A.B.One → ℝ, A.E.IsAuxNorm N →
  ∀ Ut : Set A.Obj, IsOpen Ut → A.X.IsSaturated Ut → boundaryDomSupp Λ ⊆ Ut →
  ∀ f : A.Obj → ℝ, Continuous f → (∀ x, 0 ≤ f x) →
    (∀ φ : A.Mor, f (A.X.src φ) = f (A.X.tgt φ)) → tsupport f ⊆ Ut →
    (∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < f x) →
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧
      (∀ x : A.Obj, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ut ∧
      ∀ w : A.W, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w

end RoundTrip.V14_8
