import Polyfold
/-! Blind formalization of V11_31 (the Springer 2021 book, Part II, §11.5, Lemma 11.5.2, p. 548,
with the sc⁺-multisection functors of pp. 547–548).

Text: for a strong bundle equivalence `Φ` and an sc⁺-multisection `Λ`, `Φ_*Λ(w') = Λ(w)` for
`Φ(w) ≅ w'` is a well-defined sc⁺-multisection.

Choices:
- Setting: universe 0; strong bundles over ep-groupoids the project's `SEP.{0}` (`P : W → X` with
  `μ`; `W` is itself an ep-groupoid, the project's `E.toEpGroupoid`, with morphisms
  `(φ, w) : w → μ(φ, w)`); a strong bundle equivalence `Φ : A → A'` is a morphism of `SEP` in the
  project's class `SEP.equivalences` (`#print`ed: `IsStrongBundleEquivalence` of the pair
  `(ϕ, Φ)`, 2021 Definition 10.4.1), as in `V10_58.lean`.  `Φ(w)` is `Φ.Φ.obj w`.
- sc⁺-multisection (pp. 547–548; the project has no such notion, so `IsScPlusMultisectionB` is
  mine): a functor `Λ : W → ℚ⁺` (values `≥ 0` and `Λ(μ(φ, w)) = Λ(w)`, the project's
  `SBLocalization.IsWFunctor`, `#print`ed) such that every `x ∈ X` has an open neighbourhood
  `U(x)`, finitely many local sc⁺-sections `s₁, …, s_k` on `U(x)` and rational weights `σᵢ > 0`
  with `∑ σᵢ = 1` and `Λ(w) = ∑_{i : sᵢ(P(w)) = w} σᵢ` for `w ∈ W|U(x)`.  A local sc⁺-section on
  `U` (`IsLocalScPlusSectionB`): `P(s(x)) = x` on `U`, `s(U) ⊆ W_{0,1}`, and `s : U → W[1]` is
  sc-smooth (Part I's `IsScSmoothOn` into the project's M-polyfold `W[1]`,
  `StrongBundle.toMPolyfold1`; Definition 2.52 on an open set).  Values of `s` off `U` are junk.
- `Φ_*Λ`: the project's `SBLocalization.pushMult` (`#print`ed: `Λ` at a chosen `w`).
  "Well-defined": every `w'` has some `w` with `Φ(w) ≅ w'` (a morphism `Φ(w) → w'` in `W'`), and
  `(Φ_*Λ)(w') = Λ(w)` for EVERY such `w`; and `Φ_*Λ` is an sc⁺-multisection.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_31
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- `s` is an sc⁺-section of `P : W → X` over the open set `U`. -/
def IsLocalScPlusSectionB (A : SEP.{0}) (U : Set A.Obj) (s : A.Obj → A.W) : Prop :=
  (∀ x ∈ U, A.P (s x) = x) ∧
  ∃ s₁ : A.Obj → StrongBundle.One A.B,
    (∀ x ∈ U, StrongBundle.oneVal A.B (s₁ x) = s x) ∧
    A.X.PObj.IsScSmoothOn (StrongBundle.toMPolyfold1 A.B) s₁ U

open Classical in
/-- `Λ : W → ℚ⁺` is an sc⁺-multisection functor. -/
def IsScPlusMultisectionB (A : SEP.{0}) (Λ : A.W → ℚ) : Prop :=
  (∀ w, 0 ≤ Λ w) ∧ IsWFunctor A Λ ∧
  ∀ x : A.Obj, ∃ U : Set A.Obj, IsOpen U ∧ x ∈ U ∧
    ∃ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ),
      (∀ i, IsLocalScPlusSectionB A U (s i)) ∧ (∀ i, 0 < σ i) ∧ ∑ i, σ i = 1 ∧
      ∀ w : A.W, A.P w ∈ U → Λ w = ∑ i with s i (A.P w) = w, σ i

/-- Lemma 11.5.2: `Φ_*Λ(w') = Λ(w)` for `Φ(w) ≅ w'` is a well-defined sc⁺-multisection. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (Φ : A ⟶ A') (hΦ : SEP.equivalences Φ) (Λ : A.W → ℚ),
    IsScPlusMultisectionB A Λ →
      (∀ w' : A'.W, ∃ w : A.W, A'.E.toEpGroupoid.Isomorphic (Φ.Φ.obj w) w') ∧
      (∀ (w : A.W) (w' : A'.W), A'.E.toEpGroupoid.Isomorphic (Φ.Φ.obj w) w' →
        pushMult Φ hΦ Λ w' = Λ w) ∧
      IsScPlusMultisectionB A' (pushMult Φ hΦ Λ)

end RoundTrip.V11_31
