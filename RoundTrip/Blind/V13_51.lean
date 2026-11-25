import Polyfold
/-! Blind formalization of V13_51 (the Springer 2021 book, Part II, §13.4, Theorem 13.4.1,
pp. 621–622; 2017: Theorem 13.3).

Text: for a strong bundle equivalence `Φ : W → W'` covering `F : X → X'` and structurable `Λ'`,
`Φ^*Λ' = Λ' ∘ Φ` is structurable; a structured `Λ'` gives a canonical structure on `Φ^*Λ'`.

Choices:
- Setting: universe 0; strong bundles over ep-groupoids `SEP.{0}` (`C` for `W → X`, `A` for
  `W' → X'`).  A strong bundle equivalence is a morphism `F : C ⟶ A` of `SEP` (the pair of the
  base functor `F.ϕ : X → X'` and the functor `F.Φ` of the total ep-groupoids) in the class
  `SEP.equivalences` (Definition 10.4.1 / 10.4.11).  `Φ` on objects is `F.Φ.obj : W → W'`.
- `Φ^*Λ'` is written out as `fun w => Λ' (F.Φ.obj w)` (the text's `Λ' ∘ Φ`), not through a
  project definition.
- "structurable": the project's `IsStructurable` (`#print`ed: `IsScPlusMultisection A Λ ∧
  ∃ D : Decoration A Λ, Nonempty D.Tau`: an sc⁺-multisection functor with a system of symmetric
  structures carrying correspondences, Definitions 13.2.7, 13.3.4, 13.3.6).
- "a structured `Λ'` gives a canonical structure on `Φ^*Λ'`": the canonical construction is the
  project's `PullMap.pullTuple` along `PullMap.ofEquivalence hF` (its docstrings: a good system
  `𝒰` on `X` adapted to `𝒰'` (`PullData`), `I_x = I'_{F(x)}` with `g(i) = F(g)(i)`,
  `Φ(sᵢ(z)) = s'ᵢ(F(z))`, `τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))`, the construction of the text's
  proof).  I state what "canonical" means: (b) the pulled tuple structures `Λ' ∘ Φ`, and (c) its
  class depends only on the class `[Λ', 𝒰', S', τ']`: equivalent structured tuples (the project's
  `StructuredTuple.Equiv`, Definition 13.3.8) and any choices of the adapted good systems give
  equivalent pulled tuples.  This uses project constructions I could not avoid; their docstrings
  match the text's construction.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V13_51
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- Theorem 13.4.1: pull-backs along strong bundle equivalences are structurable, with a
canonical structure. -/
def B : Prop :=
  ∀ (C A : SEP.{0}) (F : C ⟶ A) (hF : SEP.equivalences F),
    -- (a) `Φ^*Λ'` is structurable
    (∀ Λ' : A.W → ℚ≥0, IsStructurable A Λ' → IsStructurable C (fun w => Λ' (F.Φ.obj w))) ∧
    -- (b) the canonical structure is a structure of `Φ^*Λ'`
    (∀ (T' : StructuredTuple A) (P : (PullMap.ofEquivalence hF).PullData T'.dec.𝒰),
      (PullMap.pullTuple T' P).Λ = fun w => T'.Λ (F.Φ.obj w)) ∧
    -- (c) it is well defined on structured sc⁺-multisections
    (∀ T₁ T₂ : StructuredTuple A, T₁.Equiv T₂ →
      ∀ (P₁ : (PullMap.ofEquivalence hF).PullData T₁.dec.𝒰)
        (P₂ : (PullMap.ofEquivalence hF).PullData T₂.dec.𝒰),
        (PullMap.pullTuple T₁ P₁).Equiv (PullMap.pullTuple T₂ P₂))

end RoundTrip.V13_51
