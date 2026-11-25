import Polyfold
/-! Blind formalization of V15_30 (the Springer 2021 book, Part II, §15.3, Theorem 15.3.7, last
sentence, p. 694; 2017: Theorem 15.4): "in particular `Λ ∘ f` is compact and branched".

Text: for `Λ` as in the theorem, `Λ ∘ f` is a compact tame branched ep⁺-subgroupoid.

Choices:
- Setting and hypotheses of Theorem 15.3.7 exactly as in my `V15_29.lean`: universe 0,
  `A : SEP.{0}`, `A.X.IsTame`, `A.X.AdmitsBumpFunctions` (Definition 12.3.1), `f` an
  sc-Fredholm section functor with `|S_f|` compact (`HasCompactSolutionSetEp`), `(N, U)` with
  `ControlsCompactness` (Definition 15.3.1), `h : X → (0, 1]` a continuous functor.
- "`Λ` as in the theorem": an sc⁺-multisection functor (`IsScPlusMultisection`) with
  (1) `N(Λ)(x) < h(x)` for all `x` (`pointwiseNorm`), (2) `domSupp Λ ⊆ U`, (3) `IsTransversal f Λ`
  (`T(f,Λ)` onto on `supp(Λ ∘ f)`), (4) `IsInGeneralPosition A f Λ` (Definition 15.3.5).
  Structurability is not assumed: the "in particular" follows from (1)–(4); if the text means
  the structurable `Λ` only, B is stronger than the text.
- `Λ ∘ f` as a functor `X → ℚ⁺`: `z ↦ Λ(f(z))` cast to `ℚ`.  "branched ep⁺-subgroupoid": the
  project's `IsBranchedEpSubgroupoid` (Definition 9.1.2); "compact": `IsCompactBranched`
  (Definition 9.1.6 (2), `#print`ed: `|supp Θ|` compact in `|X|`); "tame": `IsTameBranched`
  (Definition 9.3.6, `#print`ed: a tame local branching structure at every point of `supp Θ`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_30
open Polyfold Polyfold.SBLocalization

/-- `h : X → (0, 1]` is a continuous functor. -/
def IsUnitFunctor (A : SEP.{0}) (h : A.Obj → ℝ) : Prop :=
  Continuous h ∧ (∀ x, 0 < h x ∧ h x ≤ 1) ∧ ∀ φ : A.Mor, h (A.X.src φ) = h (A.X.tgt φ)

/-- Theorem 15.3.7, last sentence: for `Λ` with (1)–(4), `Λ ∘ f` is a compact tame branched
ep⁺-subgroupoid. -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.AdmitsBumpFunctions →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ (h : A.Obj → ℝ), IsUnitFunctor A h →
    ∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ →
      (∀ x, pointwiseNorm N Λ x < h x) → domSupp Λ ⊆ U → IsTransversal f Λ →
      IsInGeneralPosition A f Λ →
        A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsCompactBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsTameBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ))

end RoundTrip.V15_30
