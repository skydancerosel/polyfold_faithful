import Polyfold
/-! Blind formalization of V13_52 (the Springer 2021 book, Part II, §13.4, Theorem 13.4.3,
pp. 625–626; 2017: Theorem 13.4).

Text: for `Φ` over the equivalence `F` and structurable `Λ`, `Φ_*Λ` is structurable.

Choices:
- Setting: universe 0; strong bundles over ep-groupoids `SEP.{0}` (`C` for `W → X`, `A` for
  `W' → X'`); `Φ` a strong bundle equivalence, i.e. a morphism `F : C ⟶ A` of `SEP` in
  `SEP.equivalences` (Definition 10.4.1), covering the equivalence `F.ϕ : X → X'`.  `Φ` on
  objects is `F.Φ.obj`.
- `Φ_*Λ` (2021 p. 547): `Φ_*Λ(w') = Λ(w)` for any `w` with a morphism `Φ(w) → w'` in the total
  ep-groupoid `(W', 𝐖')` (the project's `Isomorphic` of `A.E.toEpGroupoid`).  I do not use the
  project's `pushMult`: I state the claim for every `Λ' : W' → ℚ⁺` satisfying this defining
  property (for a functor `Λ` and an equivalence `Φ` there is exactly one).
- "structurable": the project's `IsStructurable` (`#print`ed: an sc⁺-multisection functor with
  a system of symmetric structures carrying correspondences, Definition 13.3.6).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V13_52
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- Theorem 13.4.3: push-forwards along strong bundle equivalences are structurable. -/
def B : Prop :=
  ∀ (C A : SEP.{0}) (F : C ⟶ A), SEP.equivalences F →
    ∀ Λ : C.W → ℚ≥0, IsStructurable C Λ →
      ∀ Λ' : A.W → ℚ≥0,
        (∀ (w : C.W) (w' : A.W), A.E.toEpGroupoid.Isomorphic (F.Φ.obj w) w' → Λ' w' = Λ w) →
        IsStructurable A Λ'

end RoundTrip.V13_52
