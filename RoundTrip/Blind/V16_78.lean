import Polyfold
/-! Blind formalization of V16_78 (the text's Part II, §16.6, Theorem 16.6.6, p. 739 of the
Springer 2021 book; 2017: Theorem 16.8).

Text: `∂Z = ∅`, `f` oriented, compact solution set, `(n, U)` controls compactness, `λ` controlled
by `(n, U)`, `(f, λ)` in general position: the branched integrals over `λ ∘ f` define a map on
cohomology, `Φ_{(f,o)}([ω]) = ∫_{λ∘f} ω`, independent of `λ`.

Choices:
- Setting: all spaces in `Type` (universe `0`); a strong polyfold bundle `(p : Y → Z, c̄)` is the
  project's `StrongPolyfoldBundle p` (Definition 16.3.4), its polyfold `(Z, c)` is `c.polyfold`.
- `∂Z = ∅`: `c.polyfold.boundary = ∅` (Definition 16.1.17, `∂Z = {d_Z ≥ 1}`).
- "`f` oriented": an sc-Fredholm section `f : c.FredholmSection` (Definition 16.6.1) together with
  an orientation `o : OrientationRep f` (Definition 16.6.5: an orientation of a representative
  `(W, F)`).  The orientation of the text is the class of `o`; I quantify over every
  representative `o`, so B is stated for each.
- The Fredholm index.  The text speaks of "the" index of `f` (the degree of the closed forms that
  are integrated equals it), so I presuppose a constant index `k = m + 1 ≥ 1` and read it in the
  model of `o`: `IsIndexAt o.a.F x (m+1)` at every smooth object `x` of that model (Definition
  6.2.1 read in the model).  The index-`0` case (weighted counts) is the separate item V16_82, so
  here `k ≥ 1`; for forms of a degree different from the index `Φ` is `0` by the text's
  convention and nothing is claimed.
- "compact solution set": `HasCompactSolutionSet` (Definition 16.6.2: `S(f)` compact).
- `n` an auxiliary norm (`IsAuxNorm`, Definition 16.3.9), `U ⊆ Z` an open neighbourhood of
  `S(f)`, `(n, U)` controls compactness: the project's `ControlsCompactness` (`#print`ed: it
  is `IsAuxNorm n ∧ IsOpen U ∧ S(f) ⊆ U ∧ cl{z ∈ U | n(f(z)) ≤ 1}` compact, Definition 16.6.3
  with `C = 1`).  I also list `IsAuxNorm n`, `IsOpen U`, `S(f) ⊆ U` explicitly (redundant).
- `λ` an sc⁺-multisection (`ScPlusMultisection`, Definition 16.5.1); "controlled by `(n, U)`" is
  `IsControlledBy n U` (`#print`ed: `n(λ) ≤ 1` pointwise and `dom-supp(λ) ⊆ U`); "`(f, λ)` in
  general position" is `IsInGeneralPositionWith` (`#print`ed: in some model, a representative
  `F` of `f` and a functor `Λ` representing `λ` are in general position, Definition 15.3.4).
  No structurability of `λ` is assumed (the text does not ask it in this theorem).
- "`λ ∘ f` with the inherited orientation": an `OrientedPerturbation f m` `Q` (`#print`ed: a
  compact oriented branched suborbifold `θ̂` of `Z`, tame of dimension `m + 1`, whose function is
  `λ ∘ f` with `λ = Q.t`) such that `IsCanonicalSolutionSet o Q` (`#print`ed: `Q` is the class of
  a compact oriented solution set `(Λ ∘ F, T̂)` in the model of `o` whose `T̂` is the canonical
  orientation of Definition 15.4.2 induced by `o`, Theorem 15.4.1).  I use this, not
  `IsInheritedFrom`, since the latter asks `Λ` to be a (structurable) regular perturbation, which
  the text does not.
- The branched integral `∫_{θ̂} ω` (2021 p. 732) is `CompactOrientedSuborbifold.integral`; I use
  the integral `∫`, not the effective `∮`.
- Reading of "define a map on cohomology, independent of `λ`" as the conjunction of
  (1) for every admissible `λ`, `λ ∘ f` carries the inherited orientation as a compact tame
      oriented branched suborbifold of dimension `m + 1` (the presupposition that makes
      `∫_{λ∘f} ω` meaningful for every admissible `λ`; I include it so that "all perturbations"
      is not vacuous);
  (2) the integral over such a `λ ∘ f` of a closed `(m+1)`-form depends only on its class:
      `∫ (ω + dτ) = ∫ ω` for closed `ω` and every `m`-form `τ`;
  (3) for any two admissible `λ, λ'` (with any inherited-orientation realisations `Q, Q'`) and
      every closed `ω`, `∫_{Q} ω = ∫_{Q'} ω`.
  Linearity of `Φ` and the existence of an admissible `λ` are not part of B.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_78
open Polyfold

/-- `λ` is admissible for `(f, n, U)`: controlled by `(n, U)` and `(f, λ)` in general position. -/
def Admissible {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    {c : StrongPolyfoldBundle p} (f : c.FredholmSection) (n : Y → ℝ) (U : Set Z)
    (lam : c.ScPlusMultisection) : Prop :=
  lam.IsControlledBy n U ∧ (f : c.ScSection).IsInGeneralPositionWith lam

/-- Theorem 16.6.6 (index `m + 1 ≥ 1`): `Φ_{(f,o)}([ω]) = ∫_{λ∘f} ω` is defined for every
admissible `λ`, depends only on `[ω]`, and does not depend on `λ`. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p),
    c.polyfold.boundary = ∅ →
    ∀ (f : c.FredholmSection) (o : StrongPolyfoldBundle.OrientationRep f) (m : ℕ),
    (∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((m + 1 : ℕ) : ℤ)) →
    (f : c.ScSection).HasCompactSolutionSet →
    ∀ (n : Y → ℝ) (U : Set Z),
    c.IsAuxNorm n → IsOpen U → (f : c.ScSection).solutionSet ⊆ U →
    (f : c.ScSection).ControlsCompactness n U →
      -- (1) every admissible `λ` gives `λ ∘ f` with the inherited orientation
      (∀ lam : c.ScPlusMultisection, Admissible f n U lam →
        ∃ Q : StrongPolyfoldBundle.OrientedPerturbation (f : c.ScSection) m,
          Q.t = lam ∧ StrongPolyfoldBundle.IsCanonicalSolutionSet o Q) ∧
      -- (2) the integral of a closed form depends only on its cohomology class
      (∀ Q : StrongPolyfoldBundle.OrientedPerturbation (f : c.ScSection) m,
        Admissible f n U Q.t → StrongPolyfoldBundle.IsCanonicalSolutionSet o Q →
        ∀ (ω : c.polyfold.ScForm (m + 1)), PolyfoldClass.ScForm.d ω = 0 →
        ∀ (τ : c.polyfold.ScForm m),
          Q.toCompactOrientedSuborbifold.integral (ω + PolyfoldClass.ScForm.d τ) =
            Q.toCompactOrientedSuborbifold.integral ω) ∧
      -- (3) independence of `λ`
      (∀ Q Q' : StrongPolyfoldBundle.OrientedPerturbation (f : c.ScSection) m,
        Admissible f n U Q.t → StrongPolyfoldBundle.IsCanonicalSolutionSet o Q →
        Admissible f n U Q'.t → StrongPolyfoldBundle.IsCanonicalSolutionSet o Q' →
        ∀ (ω : c.polyfold.ScForm (m + 1)), PolyfoldClass.ScForm.d ω = 0 →
          Q.toCompactOrientedSuborbifold.integral ω =
            Q'.toCompactOrientedSuborbifold.integral ω)

end RoundTrip.V16_78
