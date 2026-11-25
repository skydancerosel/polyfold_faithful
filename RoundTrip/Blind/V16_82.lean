import Polyfold
/-! Blind formalization of V16_82 (the text's Part II, §16.6, Theorem 16.6.6 for Fredholm
index `0`, p. 739 of the Springer 2021 book; 2017: Theorem 16.8).

Text: the invariant for a closed form of degree `k` equal to the index, including `k = 0`: for
`λ` controlled by `(n, U)` in general position, the weighted counts of the `0`-dimensional
`λ ∘ f` with the inherited orientation do not depend on `λ`.  (Standing hypotheses of Theorem
16.6.6: `∂Z = ∅`, `f` oriented with compact solution set, `(n, U)` controls compactness.)

Choices:
- Setting, `∂Z = ∅`, the oriented sc-Fredholm section `(f, o)`, compact solution set, the
  auxiliary norm `n`, the open neighbourhood `U` of `S(f)`, "`(n, U)` controls compactness",
  "`λ` controlled by `(n, U)`", "`(f, λ)` in general position": exactly as in V16_78 (all spaces
  in `Type`; `c.polyfold.boundary = ∅`; `f : c.FredholmSection`, `o : OrientationRep f` an
  orientation of a representative, B stated for every such `o`; `HasCompactSolutionSet`;
  `IsAuxNorm`; `ControlsCompactness` (`#print`ed: aux norm, `U` open, `S(f) ⊆ U`,
  `cl{z ∈ U | n(f(z)) ≤ 1}` compact); `IsControlledBy` (`n(λ) ≤ 1`, `dom-supp λ ⊆ U`);
  `IsInGeneralPositionWith` (some model representatives of `f` and `λ` in general position)).
  No structurability of `λ` is assumed.
- Index `0`: read in the model of `o`, `IsIndexAt o.a.F x 0` at every smooth object `x`.
- "the `0`-dimensional `λ ∘ f` with the inherited orientation": a `PointOrientedPerturbation f`
  `Q` (`#print`ed: a compact oriented branched suborbifold of `Z`, tame of dimension `0`, whose
  function is `λ ∘ f` with `λ = Q.t`) with `IsCanonicalPointSolutionSet o Q` (`#print`ed: `Q` is
  the class of a point solution set `(Λ ∘ F, T̂)` in the model of `o` with `T̂` the canonical
  orientation of Definition 15.4.2 from `o`; `Λ` need not be a regular perturbation).
- "weighted counts": the dimension-`0` branched integral `∫_{θ̂} τ` (2021 p. 732, Definition
  9.5.6 (1) for `n = 0`: the weighted signed count `Σ ± w·τ(z)`), the project's
  `PointSuborbifold.count τ`, for every closed `0`-form `τ` (`dτ = 0`; the invariant on
  `H⁰_dR(Z)`, which contains the plain weighted count `τ = 1`).  The integral `∫`, not the
  effective `∮`.  In degree `0` there are no exact forms, so "depends only on `[τ]`" is empty.
- B is the conjunction of (1) every admissible `λ` gives a `0`-dimensional `λ ∘ f` with the
  inherited orientation (the presupposition that makes the count defined for all admissible `λ`)
  and (2) for any two admissible `λ, λ'` (any such realisations `Q, Q'`) and every closed
  `0`-form `τ`, the two weighted counts agree.  Existence of an admissible `λ` is not part of B.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_82
open Polyfold

/-- `λ` is admissible for `(f, n, U)`: controlled by `(n, U)` and `(f, λ)` in general position. -/
def Admissible {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    {c : StrongPolyfoldBundle p} (f : c.FredholmSection) (n : Y → ℝ) (U : Set Z)
    (lam : c.ScPlusMultisection) : Prop :=
  lam.IsControlledBy n U ∧ (f : c.ScSection).IsInGeneralPositionWith lam

/-- Theorem 16.6.6 for index `0`: the weighted signed counts of a closed `0`-form over the
`0`-dimensional `λ ∘ f` with the inherited orientation exist for every admissible `λ` and do not
depend on `λ`. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p),
    c.polyfold.boundary = ∅ →
    ∀ (f : c.FredholmSection) (o : StrongPolyfoldBundle.OrientationRep f),
    (∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x 0) →
    (f : c.ScSection).HasCompactSolutionSet →
    ∀ (n : Y → ℝ) (U : Set Z),
    c.IsAuxNorm n → IsOpen U → (f : c.ScSection).solutionSet ⊆ U →
    (f : c.ScSection).ControlsCompactness n U →
      -- (1) every admissible `λ` gives a `0`-dimensional `λ ∘ f` with the inherited orientation
      (∀ lam : c.ScPlusMultisection, Admissible f n U lam →
        ∃ Q : StrongPolyfoldBundle.PointOrientedPerturbation (f : c.ScSection),
          Q.t = lam ∧ StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q) ∧
      -- (2) the weighted counts do not depend on `λ`
      (∀ Q Q' : StrongPolyfoldBundle.PointOrientedPerturbation (f : c.ScSection),
        Admissible f n U Q.t → StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q →
        Admissible f n U Q'.t → StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q' →
        ∀ (τ : c.polyfold.ScForm 0), PolyfoldClass.ScForm.d τ = 0 →
          Q.toPointSuborbifold.count τ = Q'.toPointSuborbifold.count τ)

end RoundTrip.V16_82
