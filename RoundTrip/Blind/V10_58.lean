import Polyfold
/-! Blind formalization of V10_58 (the text's Part II, §10.5, the push-forward
`[D]_* f = Ψ_* Φ^* f`, p. 507 of the Springer 2021 book; 2017 p. 367).

Text: for a representative with both legs strong bundle equivalences, `[D]_* f = Ψ_* Φ^* f` and
`[D]^* g = Φ_* Ψ^* g`; for a refinement by `H`,
`Ψ_* Φ^* f = Ψ_* H_* H^* Φ^* f = (Ψ ∘ H)_* (Φ ∘ H)^* f = Ψ'_* Φ'^* f` (Propositions 10.4.2–10.4.4),
so `[D]_*` is well defined.

Choices:
- Setting: universe 0; the project's `SEP.{0}`, `SDiagram`, `GenSBMap` (V10_51) and generalized
  strong bundle isomorphisms `GenSBMap.IsGeneralizedIso` (V10_56).  `Γ(P, μ)` is the project's
  `EpStrongBundle.sectionFunctors` (the sc-smooth section functors, 2017 Definition 8.7 (1)).
  For a strong bundle equivalence `Φ : W'' → W` (a morphism of `SEP` in the project's
  class `SEP.equivalences`, 2021 Definition 10.4.1), `Φ^*` and `Φ_*` are the project's
  `IsStrongBundleEquivalence.pullback` and `.pushforward` (2021 §10.4, pp. 496–498: `Φ^*(f)(x) =
  Φ_x⁻¹(f(ϕ(x)))`, `(Φ_* f)(x') = μ'(σ, Φ(f(x)))`; junk values off sections, which do not occur
  below); my abbreviations `pullB`, `pushB`.  Composites `Φ ∘ H` are composites in `SEP`
  (`H ≫ Φ`); that they are strong bundle equivalences is a hypothesis (the proofs are
  quantified), as is the equivalence of `Ψ'`.
- (a), (b): the project's `[D]_*`, `[D]^*` (`GenSBMap.pushforward`, `.pullback`, defined with a
  chosen representative) are `Ψ_* Φ^* f`, `Φ_* Ψ^* g` for every representative `D` of `[D]` with
  both legs strong bundle equivalences, for `f ∈ Γ(P, μ)`, `g ∈ Γ(P', μ')` (this is the
  well-definedness of `[D]_*`, and of `[D]^*`, which the text writes the same way).
- (c): the chain of equalities, for a refinement `D'` of `D` by a strong bundle equivalence `H`
  (`Φ ∘ H ≃ Φ'`, `Ψ ∘ H ≃ Ψ'`, the project's `SEP.NatEquiv`, 2021 Definition 10.4.8), on
  `f ∈ Γ(P, μ)`, each equality a conjunct.  (d): hence for diagrams with a common refinement
  (`SDiagram.Equiv`), `Ψ_* Φ^* f = Ψ'_* Φ'^* f`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_58
open Polyfold CategoryTheory

/-- `Φ^*` for a strong bundle equivalence `Φ : C → A`. -/
noncomputable def pullB {C A : SEP.{0}} (Φ : C ⟶ A) (h : SEP.equivalences Φ) :
    (A.Obj → A.W) → C.Obj → C.W :=
  EpStrongBundle.IsStrongBundleEquivalence.pullback h

/-- `Φ_*` for a strong bundle equivalence `Φ : C → A`. -/
noncomputable def pushB {C A : SEP.{0}} (Φ : C ⟶ A) (h : SEP.equivalences Φ) :
    (C.Obj → C.W) → A.Obj → A.W :=
  EpStrongBundle.IsStrongBundleEquivalence.pushforward h

/-- The push-forward `[D]_* = Ψ_* Φ^*` and pull-back `[D]^* = Φ_* Ψ^*` along a generalized strong
bundle isomorphism do not depend on the representative. -/
def B : Prop :=
  ∀ A A' : SEP.{0},
    -- (a) `[D]_* f = Ψ_* Φ^* f`
    (∀ (f : SBLocalization.GenSBMap A A') (hf : f.IsGeneralizedIso)
      (D : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      ∀ s ∈ A.E.sectionFunctors,
        SBLocalization.GenSBMap.pushforward hf s = pushB D.Ψ hΨ (pullB D.Φ D.isEquivalence_Φ s)) ∧
    -- (b) `[D]^* g = Φ_* Ψ^* g`
    (∀ (f : SBLocalization.GenSBMap A A') (hf : f.IsGeneralizedIso)
      (D : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      ∀ t ∈ A'.E.sectionFunctors,
        SBLocalization.GenSBMap.pullback hf t = pushB D.Φ D.isEquivalence_Φ (pullB D.Ψ hΨ t)) ∧
    -- (c) the chain of equalities for a refinement `D'` of `D` by `H`
    (∀ (D D' : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
      (hΨ' : SEP.equivalences D'.Ψ) (H : D'.B ⟶ D.B) (hH : SEP.equivalences H),
      SEP.NatEquiv (H ≫ D.Φ) D'.Φ → SEP.NatEquiv (H ≫ D.Ψ) D'.Ψ →
      ∀ (hΦH : SEP.equivalences (H ≫ D.Φ)) (hΨH : SEP.equivalences (H ≫ D.Ψ)),
      ∀ s ∈ A.E.sectionFunctors,
        pushB D.Ψ hΨ (pullB D.Φ D.isEquivalence_Φ s) =
          pushB D.Ψ hΨ (pushB H hH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s))) ∧
        pushB D.Ψ hΨ (pushB H hH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s))) =
          pushB (H ≫ D.Ψ) hΨH (pullB (H ≫ D.Φ) hΦH s) ∧
        pushB (H ≫ D.Ψ) hΨH (pullB (H ≫ D.Φ) hΦH s) =
          pushB D'.Ψ hΨ' (pullB D'.Φ D'.isEquivalence_Φ s)) ∧
    -- (d) equivalent diagrams give the same push-forward
    (∀ (D D' : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
      (hΨ' : SEP.equivalences D'.Ψ), D.Equiv D' →
      ∀ s ∈ A.E.sectionFunctors,
        pushB D.Ψ hΨ (pullB D.Φ D.isEquivalence_Φ s) =
          pushB D'.Ψ hΨ' (pullB D'.Φ D'.isEquivalence_Φ s))

end RoundTrip.V10_58
