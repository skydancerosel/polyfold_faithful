import Polyfold
/-! Blind formalization of V15_3 (the Springer 2021 book, Part II, §15.1, Remark 15.1.2, p. 684;
2017: Remark 15.1).

Text: `(f − sᵢ)'(y)` is not defined unless `f(y) = sᵢ(y)`, but then it is not counted; with the
empty sum `0`, (1) follows from (2) (of Theorem 15.1.1).

Choices:
- Setting as in my `V15_2.lean`: universe 0, `SEP.{0}`, `f` an sc-Fredholm section functor, `Λ` an
  sc⁺-multisection functor; local sc⁺-section structures `IsLocalRepOn A Λ O s σ` on open `O`;
  the formal sum `∑_{f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)` in `GrF(y)` read in a chart `c` of the bundle
  atlas with domain in `O` (the project's `linSumIntr c`, which only sums over `i` with
  `f(y) = sᵢ(y)`, so "not counted" is built into it).
- The remark has two claims, conjoined: (a) at `y ∉ supp(Λ ∘ f)` (`Λ(f(y)) = 0`) the sum is the
  empty sum `0` (since `Λ(f(y)) = ∑_{f(y) = sᵢ(y)} σᵢ` with `σᵢ > 0`, no `i` has
  `f(y) = sᵢ(y)`); (b) hence every choice `T(y) ∈ GrF(y)` satisfying (2) at all level-`1` points
  (for every local structure and every chart) satisfies (1) there.  I state both on all of `X₁`
  (the points where `GrF` is defined), not only on `X_∞`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_3
open Polyfold Polyfold.SBLocalization

/-- Property (2) of Theorem 15.1.1 at every level-`1` point. -/
def FormulaB {A : SEP.{0}} (f : A.Obj → A.W) (Λ : A.W → ℚ≥0)
    (T : (x : A.X.PObj.Level 1) → GrF x) : Prop :=
  ∀ (O : Set A.Obj), IsOpen O → ∀ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
    IsLocalRepOn A Λ O s σ →
    ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
    ∀ (y : A.X.PObj.Level 1) (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source),
      T y = linSumIntr c hy f s σ

/-- Remark 15.1.2. -/
def B : Prop :=
  ∀ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0),
    A.E.IsScFredholmSectionFunctor f → IsScPlusMultisection A Λ →
      -- (a) off `supp(Λ ∘ f)` the formula of (2) is the empty sum `0`
      (∀ (O : Set A.Obj), IsOpen O → ∀ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
        IsLocalRepOn A Λ O s σ →
        ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
        ∀ (y : A.X.PObj.Level 1) (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source),
          Λ (f (A.X.PObj.levelVal 1 y)) = 0 → linSumIntr c hy f s σ = 0) ∧
      -- (b) (1) follows from (2)
      (∀ T : (x : A.X.PObj.Level 1) → GrF x, FormulaB f Λ T →
        ∀ y : A.X.PObj.Level 1, Λ (f (A.X.PObj.levelVal 1 y)) = 0 → T y = 0)

end RoundTrip.V15_3
