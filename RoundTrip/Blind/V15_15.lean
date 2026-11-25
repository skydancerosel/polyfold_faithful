import Polyfold
/-! Blind formalization of V15_15 (the Springer 2021 book, Part II, §15.2, Theorem 15.2.5, p. 690;
2017: Theorem 15.3).

Text: if `(f, Λ)` is in good position at `x ∈ ∂X`, there are `U(x)` with the natural `G_x`-action,
tame submanifolds `Mᵢ` and weights `σᵢ > 0` with (1) the `Mᵢ` properly embedded; (2) `T(f,Λ)` onto,
with kernels in good position, on `M_{U(x)}`; (3) `Λ(f(y)) = ∑_{y ∈ Mᵢ} σᵢ`.  `Λ ∘ f` is then a
tame branched ep⁺-subgroupoid.  The same holds under the general position requirement instead
of (2).

Choices:
- Setting: universe 0, `SEP.{0}` over a TAME ep-groupoid (`EpGroupoid.IsTame`, Chapter 15's
  setting for boundary points), `f` an sc-Fredholm section functor, `Λ` an sc⁺-multisection
  functor.  `∂X` is the project's `X.PObj.boundary` (`d_X ≥ 1`).
- "good position at `y`": the project's `IsGoodPositionAt` (Definition 15.2.4, `#print`ed:
  `Λ(f(y)) > 0`, `T(f,Λ)(y)` onto, and for a local sc⁺-section structure near `y` every branch
  `f − sᵢ` through `y` is in good position in Part I's sense, i.e. onto with kernel in good
  position to the partial quadrant in a tame chart).  So (2) "`T(f,Λ)` onto, with kernels in good
  position, on `M_{U(x)}`" is: `IsGoodPositionAt f Λ y` for every `y ∈ U(x)` with `Λ(f(y)) > 0`.
  "general position at `y`": the project's `IsInGeneralPositionAt` (Definition 15.3.5 at a point:
  `y ∈ X₁` and the reduced linearization is onto); it does not contain `Λ(f(y)) > 0`, so for
  the general position variant I add `x ∈ supp(Λ ∘ f)`.
- `U(x)`: the domain of a natural representation `R : NaturalRep x`.  Tame submanifolds:
  `Mᵢ ⊆ U(x)`, `Mᵢ ⊆ X_∞`, smooth submanifolds (`MPolyfold.IsSmoothSubmanifold`) with tame induced
  structure (`MPolyfold.HasTameInducedStructure`); finitely many, indexed by `Fin k`; weights
  `σᵢ ∈ ℚ`, `σᵢ > 0`; (1) the inclusions `Mᵢ → U(x)` are proper maps; (3) for `y ∈ U(x)`.
  The `Mᵢ` are not tied to the sections of `Λ` (the statement file does not say so).
- "`Λ ∘ f` is then a tame branched ep⁺-subgroupoid": read globally, under good position at every
  point of `supp(Λ ∘ f)` (interior points included, where good position is transversality):
  `Θ = Λ ∘ f : X → ℚ⁺` is a branched ep⁺-subgroupoid (the project's `IsBranchedEpSubgroupoid`,
  Definition 9.1.2) whose local branching structures can be taken tame
  (`EpGroupoid.IsTameBranched`: a `TameBranchingStructure` at every point of `supp Θ`).
- "The same holds under the general position requirement instead of (2)": both the local
  statement (with (2) replaced by general position at every `y ∈ M_{U(x)}`) and the global one
  (general position at every point of `supp(Λ ∘ f)`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_15
open Polyfold Polyfold.SBLocalization

open Classical in
/-- The local conclusion at `x`: `U(x)`, tame submanifolds `Mᵢ`, weights `σᵢ > 0` with (1), (3)
and the pointwise requirement `Good` on `M_{U(x)}` (for (2)). -/
def LocalB (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj)
    (Good : A.Obj → Prop) : Prop :=
  ∃ R : A.X.NaturalRep x, ∃ (k : ℕ) (M : Fin k → Set A.Obj) (σ : Fin k → ℚ),
    (∀ i, M i ⊆ R.U) ∧ (∀ i, M i ⊆ A.X.PObj.smoothSet) ∧
    (∀ i, A.X.PObj.IsSmoothSubmanifold (M i)) ∧ (∀ i, A.X.PObj.HasTameInducedStructure (M i)) ∧
    (∀ i, 0 < σ i) ∧
    -- (1) properly embedded
    (∀ i, ∃ h : M i ⊆ R.U, IsProperMap (Set.inclusion h)) ∧
    -- (2) on `M_{U(x)}`
    (∀ y ∈ R.U, 0 < Λ (f y) → Good y) ∧
    -- (3) `Λ(f(y)) = ∑_{y ∈ Mᵢ} σᵢ`
    (∀ y ∈ R.U, ((Λ (f y) : ℚ≥0) : ℚ) = ∑ i with y ∈ M i, σ i)

/-- `Λ ∘ f` is a tame branched ep⁺-subgroupoid. -/
def TameBranchedB (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) : Prop :=
  A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
    A.X.IsTameBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ))

/-- Theorem 15.2.5. -/
def B : Prop :=
  ∀ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0), A.X.IsTame →
    A.E.IsScFredholmSectionFunctor f → IsScPlusMultisection A Λ →
      -- good position
      (∀ x ∈ A.X.PObj.boundary, IsGoodPositionAt f Λ x →
        LocalB A f Λ x (IsGoodPositionAt f Λ)) ∧
      ((∀ x, 0 < Λ (f x) → IsGoodPositionAt f Λ x) → TameBranchedB A f Λ) ∧
      -- general position instead of (2)
      (∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsInGeneralPositionAt f Λ x →
        LocalB A f Λ x (IsInGeneralPositionAt f Λ)) ∧
      ((∀ x, 0 < Λ (f x) → IsInGeneralPositionAt f Λ x) → TameBranchedB A f Λ)

end RoundTrip.V15_15
