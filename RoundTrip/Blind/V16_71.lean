import Polyfold
/-! Blind formalization of V16_71 (the text's Part II, §16.5, Theorem 16.5.7, p. 735 of the
Springer 2021 book; 2017: Theorem 16.6).

Text: tame `Z` with sc-smooth partitions of unity, `λ` structurable over `∂Z`, `Ũ ⊇ dom-supp(λ)`
open, `f ≥ 0` continuous with support in `Ũ`, `n(λ) < f` on `dom-supp(λ)`: there is a structurable
`λ'` with `n(λ') ≤ f`, `dom-supp(λ') ⊆ Ũ`, `λ' = λ` over `∂Z`.

Choices:
- Setting: `Y Z : Type` (universe `0`), a strong polyfold bundle `c : StrongPolyfoldBundle p`,
  its polyfold `(Z, c) = c.polyfold`, `∂Z = c.polyfold.boundary`.
- "tame `Z`": `c.polyfold.IsTame` (Definition 16.1.20); "with sc-smooth partitions of unity":
  `c.polyfold.AdmitsScPartitionsOfUnity` (Definition 16.1.5 (2)).
- `λ` an sc⁺-multisection of `Y|∂Z`: `c.BoundaryMultisection` (Definition 16.5.5), its function
  `λ.toFun : Y → ℚ⁺` (read `0` off `p⁻¹(∂Z)`); "structurable": `IsStructurable` (Definition 16.5.6:
  a representative with structurable `Λ` over `∂X`).  I do NOT use the project's
  `IsStructurableNe` (non-empty index sets), which is not the text's wording.
- `n`: the statement uses `n(λ)` without introducing `n`; I read it as an auxiliary norm of
  `(p, c̄)` (`IsAuxNorm`, Definition 16.3.9), quantified universally.
- `n(λ)`: the project's `StrongPolyfoldBundle.normLam n λ` ((16.8): `n(λ)(z)` is the supremum of
  `n(y)` over `y ∈ p⁻¹(z)` with `λ(y) ≠ 0`, `n` read as `0` off `Y_{0,1}`); for the boundary `λ` it
  is applied to `λ.toFun`.
- `dom-supp`: the project's `BoundaryMultisection.domSupp` (Definition 16.5.2 read over `∂Z`) and
  `ScPlusMultisection.domSupp` (Definition 16.5.2 read with `y ≠ 0_z` as in Definition 13.2.2; the
  printed Definition 16.5.2 allows `y = 0_z`, which would make `dom-supp` of every multisection
  the whole base, so I take the `y ≠ 0` reading; the project also has `domSuppText`, unused).
- `Ũ ⊆ Z` open with `dom-supp(λ) ⊆ Ũ`.  `f : Z → ℝ` continuous, `f ≥ 0`, "support in `Ũ`" read
  as `supp f = cl{f ≠ 0} ⊆ Ũ` (Mathlib `tsupport`).  "`n(λ) < f` on `dom-supp(λ)`": pointwise
  strict inequality at every `z ∈ dom-supp(λ)`.
- Conclusion: an sc⁺-multisection `λ'` of `(p, c̄)` (`ScPlusMultisection`, Definition 16.5.1),
  structurable (Definition 16.5.4), with `n(λ')(z) ≤ f(z)` for EVERY `z ∈ Z`,
  `dom-supp(λ') ⊆ Ũ`, and `λ'(y) = λ(y)` for every `y` with `p(y) ∈ ∂Z`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_71
open Polyfold

/-- Theorem 16.5.7: a structurable sc⁺-multisection over `∂Z` extends to a structurable
sc⁺-multisection with `n(λ') ≤ f` and domain support in `Ũ`. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p),
    c.polyfold.IsTame → c.polyfold.AdmitsScPartitionsOfUnity →
    ∀ (lam : c.BoundaryMultisection), lam.IsStructurable →
    ∀ (n : Y → ℝ), c.IsAuxNorm n →
    ∀ (U : Set Z), IsOpen U → lam.domSupp ⊆ U →
    ∀ (f : Z → ℝ), Continuous f → (∀ z, 0 ≤ f z) → tsupport f ⊆ U →
      (∀ z ∈ lam.domSupp, c.normLam n lam.toFun z < f z) →
      ∃ lam' : c.ScPlusMultisection, lam'.IsStructurable ∧
        (∀ z, c.normLam n lam'.toFun z ≤ f z) ∧
        lam'.domSupp ⊆ U ∧
        ∀ y, p y ∈ c.polyfold.boundary → lam'.toFun y = lam.toFun y

end RoundTrip.V16_71
