import Polyfold
/-! Blind formalization of V15_33 (the Springer 2021 book, Part II, §15.3, Corollary 15.3.10 (1),
p. 699; 2017: Corollary 15.1 (1)): regular perturbations exist.

Text: `d_X ≡ 0`, `|X|` paracompact, `f` sc-Fredholm with `|S_f|` compact, `(N, U)` controlling
compactness: there is a structurable `Λ` with dom-supp in `U`, `N(Λ) < 1` and `T(f,Λ)` onto on
the support; `Θ = Λ ∘ f` is a tame branched ep⁺-subgroupoid with compact `|supp Θ|`
("structurable regular perturbation").

Choices:
- Setting: universe 0, `A : SEP.{0}`.  `d_X ≡ 0`: the degeneracy index of the object M-polyfold
  vanishes at every object (`A.X.PObj.degIndex x = 0`).  "`|X|` paracompact":
  `A.X.HasParacompactOrbitSpace` (Definition 7.5.1).
- `f`: `IsScFredholmSectionFunctor`; `|S_f|` compact: `HasCompactSolutionSetEp`; `(N, U)`:
  `ControlsCompactness` (Definition 15.3.1, `#print`ed), as in my `V15_29.lean`.
- Conclusion: `Λ` structurable (`IsStructurable`, Definition 13.3.6), `domSupp Λ ⊆ U`,
  `N(Λ)(x) < 1` at every object (`pointwiseNorm`), `T(f,Λ)` onto on `supp(Λ ∘ f)`
  (`IsTransversal`, Definition 15.2.1); and `Θ = z ↦ Λ(f(z))` a branched ep⁺-subgroupoid
  (`IsBranchedEpSubgroupoid`, Definition 9.1.2), tame (`IsTameBranched`, Definition 9.3.6) with
  `|supp Θ|` compact (`IsCompactBranched`).  I state the conditions explicitly rather than with
  the project's `IsRegularPerturbation` (which, `#print`ed, is the same list together with
  `ControlsCompactness`).
- Literal hypotheses only.  Doubt: the existence rests on Theorem 15.3.7, which assumes sc-smooth
  bump functions (and a tame `X`, automatic for `d_X ≡ 0`); my statement file quotes no
  bump-function (or partition-of-unity) hypothesis for the corollary, so none is added.  If the
  text has such a standing hypothesis, B is stronger than the text (and possibly not holding without
  it: with no nonzero sc⁺-sections a non-transversal `f` admits no transversal `Λ`).
-/
namespace RoundTrip.V15_33
open Polyfold Polyfold.SBLocalization

/-- Corollary 15.3.10 (1): a structurable regular perturbation exists. -/
def B : Prop :=
  ∀ (A : SEP.{0}), (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∃ Λ : A.W → ℚ≥0, IsStructurable A Λ ∧ domSupp Λ ⊆ U ∧
        (∀ x, pointwiseNorm N Λ x < 1) ∧ IsTransversal f Λ ∧
        A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsTameBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsCompactBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ))

end RoundTrip.V15_33
