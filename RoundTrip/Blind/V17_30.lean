import Polyfold
/-! Blind formalization of V17_30 (the text's §17.1, Theorem 17.1.27, pp. 759–761, (17.17)–(17.19)
of the Springer 2021 book; 2017: Remark 17.2).

Text: on the weak fibred product `X ×_{X''} X'` for `Ψ'' = Ψ ⊔ Ψ'`,
`τ(q_λ, (q_λ, φ'', q_μ'), q_μ') = φ''` is a natural transformation between the equivalences
`Γ ∘ π₁` and `Γ' ∘ π₂`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and two covering families `c, c'` (the text's `Ψ, Ψ'`; the
  setting of (17.14) is two covering sets).
- `X = X_Ψ`, `X' = X_Ψ'`, `X'' = X_{Ψ ⊔ Ψ'}` and the weak fibred product
  `X ×_{X''} X'` of the inclusions `A : X → X''`, `A' : X' → X''` = the project's
  `S.modelFibredProduct c.Ψ c'.Ψ _` with projections `S.modelProjLeft`, `S.modelProjRight`
  (`π₁`, `π₂`); `Γ = S.modelFunctor c.Ψ`, `Γ' = S.modelFunctor c'.Ψ`,
  `Γ'' = S.modelFunctor (Sum.elim c.Ψ c'.Ψ)` (the functors (17.10)).  All are the text's
  constructions, taken from the vocabulary.  I compose `Γ ∘ π₁` and `Γ' ∘ π₂` myself
  (`GroupoidFunctor.comp`), not with the project's `modelFunctorLeft/Right`, and I do not use the
  project's `canonicalNatTrans`.
- An object of the weak fibred product is a triple `(q_λ, φ'', q_μ')`; its middle entry is
  `WeakFibredProduct.Obj.φ o`, a morphism of `X''`, i.e. `(q_λ, φ'', q_μ') ∈ M(Ψ''_a, Ψ''_b)`.
  The text's "`= φ''`" means the morphism `φ''` of `C`, which is `Γ''` applied to that middle
  entry (`Γ''(q, φ, q') = φ`, (17.10)).
- "equivalences": the presupposition that `Γ ∘ π₁` and `Γ' ∘ π₂` are equivalences of categories
  is included as conjuncts (Mathlib's `Functor.IsEquivalence` on the categories underlying the
  groupoids).  "natural transformation" = a Mathlib `NatTrans` between the underlying functors,
  with component at `o` given by `φ''` (`GroupoidStr.homMk`, the proofs of source/target
  existentially quantified).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_30
open Polyfold CategoryTheory

/-- Theorem 17.1.27: `τ(q_λ, (q_λ, φ'', q_μ'), q_μ') = φ''` is a natural transformation
`Γ ∘ π₁ → Γ' ∘ π₂` between equivalences. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (c c' : S.CoveringFamily),
    let F₁ := (S.modelFunctor c.Ψ).comp (S.modelProjLeft c.Ψ c'.Ψ c'.cover).toGroupoidFunctor
    let F₂ := (S.modelFunctor c'.Ψ).comp (S.modelProjRight c.Ψ c'.Ψ c'.cover).toGroupoidFunctor
    F₁.toFunctor.IsEquivalence ∧ F₂.toFunctor.IsEquivalence ∧
    ∃ τ : F₁.toFunctor ⟶ F₂.toFunctor,
      ∀ o : (S.modelFibredProduct c.Ψ c'.Ψ c'.cover).X.toGroupoidStr.Ob,
        ∃ h₁ h₂, τ.app o = C.toGroupoidStr.homMk
          ((S.modelFunctor (Sum.elim c.Ψ c'.Ψ)).mor (WeakFibredProduct.Obj.φ o)) h₁ h₂

end RoundTrip.V17_30
