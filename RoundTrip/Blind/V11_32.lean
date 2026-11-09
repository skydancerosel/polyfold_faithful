import Polyfold
/-! Blind formalization of V11_32 (the Springer 2021 book, Part II, §11.5, Proposition 11.5.3,
p. 548).

Text: for a generalized strong bundle isomorphism `[D]`, `[D]_*` and `[D]^*` of sc⁺-multisections
are well defined and mutually inverse; for generalized strong bundle maps with `|[D]| = |[D']|`
they agree.

Choices:
- Setting: universe 0; the project's `SEP.{0}`, diagrams `D = W ←Φ W'' →Ψ W'` (`SDiagram`, `Φ` a
  strong bundle equivalence in every diagram), classes `SDiagram.cls`, `GenSBMap`, generalized
  strong bundle isomorphisms `GenSBMap.IsGeneralizedIso` (`#print`ed), as in my `V11_30.lean`.
- sc⁺-multisections: my `IsScPlusMultisectionB` (copied from my `V11_31.lean`: a functor
  `Λ : W → ℚ⁺` locally `∑_{i : sᵢ(P(w)) = w} σᵢ` for local sc⁺-sections `sᵢ` and weights
  `σᵢ > 0`, `∑ σᵢ = 1`; the project has no such notion).
- For a strong bundle equivalence `Φ`, `Φ_*Λ` is the project's `SBLocalization.pushMult`
  (Lemma 11.5.2, see `V11_31.lean`), and `Ψ^*Λ' = Λ' ∘ Ψ` the project's `SBLocalization.pullMult`
  (`#print`ed: exactly `Λ' ∘ Ψ.Φ.obj`).  `[D]_* = Ψ_*Φ^*`, `[D]^* = Φ_*Ψ^*` (the text's
  definitions on a representative): the project's `GenSBMap.pushMult`, `GenSBMap.pullMult`
  (`#print`ed: these composites on a chosen representative).
- "well defined": `[D]_*Λ` and `[D]^*Λ'` are sc⁺-multisections, and they equal `Ψ_*Φ^*Λ`,
  `Φ_*Ψ^*Λ'` computed on EVERY representative `D` of `[D]` whose `Ψ` is a strong bundle
  equivalence.  "mutually inverse": `[D]^*[D]_*Λ = Λ`, `[D]_*[D]^*Λ' = Λ'` on sc⁺-multisections.
  "for generalized strong bundle maps with `|[D]| = |[D']|` they agree": for generalized strong
  bundle isomorphisms `f₁, f₂` (for which `f_*`, `f^*` are defined) with the same orbit map
  `|f₁| = |f₂| : |W| → |W'|` (the project's `GenSBMap.orbitMap`), `f₁_* = f₂_*` and
  `f₁^* = f₂^*` on sc⁺-multisections.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_32
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

/-- Proposition 11.5.3. -/
def B : Prop :=
  -- well defined: sc⁺-multisections go to sc⁺-multisections, and every representative computes
  -- `[D]_*`, `[D]^*`
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
      IsScPlusMultisectionB A' (GenSBMap.pushMult hf Λ)) ∧
    (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
      IsScPlusMultisectionB A (GenSBMap.pullMult hf Λ')) ∧
    ∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
        GenSBMap.pushMult hf Λ = pushMult D.Ψ hΨ (pullMult D.Φ Λ)) ∧
      (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
        GenSBMap.pullMult hf Λ' = pushMult D.Φ D.isEquivalence_Φ (pullMult D.Ψ Λ'))) ∧
  -- mutually inverse
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
      GenSBMap.pullMult hf (GenSBMap.pushMult hf Λ) = Λ) ∧
    (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
      GenSBMap.pushMult hf (GenSBMap.pullMult hf Λ') = Λ')) ∧
  -- maps with the same `|[D]|` agree
  (∀ (A A' : SEP.{0}) (f₁ f₂ : GenSBMap A A') (h₁ : f₁.IsGeneralizedIso)
    (h₂ : f₂.IsGeneralizedIso), f₁.orbitMap = f₂.orbitMap →
    (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
      GenSBMap.pushMult h₁ Λ = GenSBMap.pushMult h₂ Λ) ∧
    (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
      GenSBMap.pullMult h₁ Λ' = GenSBMap.pullMult h₂ Λ'))

end RoundTrip.V11_32
