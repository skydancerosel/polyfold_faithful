import Polyfold
/-! Blind formalization of V18_36 (the text's Part II, §18.3, Theorem 18.3.5, p. 853 of the
Springer 2021 book; 2017: Theorem 18.5).

Text: `Λ₁ ⊕ Λ₂` and `β ⊙ Λ₁` are structurable if `Λ₁`, `Λ₂` are (from §13.3).

Choices:
- Setting: universe `0`; `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT `V`
  (`P : E → C`) with a strong polyfold bundle construction `Q`.  Multisection functors are
  `Λ : E → ℚ⁺` (`V.EObj → ℚ≥0`).
- "structurable" (Definition 18.3.3): the project's `Q.IsStructurableFunctor` (`#print`ed: `Λ`
  constant along the morphisms of `E` and, for some covering family, the pull-back `Γ̄^*Λ` to the
  model is structurable in the sense of Definition 13.3.7).  Taken from the vocabulary.
- `Λ₁ ⊕ Λ₂` = the project's `multisectionFunctorAdd` (docstring:
  `(Λ₁ ⊕ Λ₂)(α, e) = ∑_{e' + e'' = e} Λ₁(α, e') Λ₂(α, e'')`, p. 852); `β ⊙ Λ` = the project's
  `multisectionFunctorSmul` (docstring, p. 853: `Λ(α, β(α)⁻¹ e)` if `β(α) ≠ 0`; the indicator of
  `0` if `β(α) = 0`).  Taken from the vocabulary (the text's definitions).
- `β`: an sc-smooth functor `β : C → ℝ` (the project's `S.IsScSmoothFunctionFunctor`,
  `#print`ed: constant along morphisms and `β ∘ Ψ` sc-smooth for every uniformizer).  I read the
  text's `β` as such (the hypothesis of the ep-groupoid version in §13.3).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_36
open Polyfold

/-- Theorem 18.3.5: sums of structurable sc⁺-multisection functors and products with sc-smooth
functions are structurable. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S),
    (∀ Λ₁ Λ₂ : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ₁ → Q.IsStructurableFunctor Λ₂ →
      Q.IsStructurableFunctor (GCT.VectorBundle.multisectionFunctorAdd Λ₁ Λ₂)) ∧
    (∀ (β : C.Obj → ℝ) (Λ₁ : V.EObj → ℚ≥0), S.IsScSmoothFunctionFunctor β →
      Q.IsStructurableFunctor Λ₁ →
      Q.IsStructurableFunctor (GCT.VectorBundle.multisectionFunctorSmul β Λ₁))

end RoundTrip.V18_36
