import Polyfold
/-! Blind formalization of V18_37 (the text's Part II, §18.3, Theorem 18.3.6, p. 853 of the
Springer 2021 book; 2017: Theorem 18.6).

Text: for an sc-smooth strong bundle proper covering functor `P̃` over `C̃ → C` and structurable
`Λ`, `P̃^*Λ` is structurable (from Theorem 13.4.4).

Choices:
- Setting: universe `0`; two GCTs `C̃ = C'`, `C` with polyfold structures `S'`, `S`, vector
  bundle GCTs `V'`, `V` with strong polyfold bundle constructions `Q'`, `Q`.
- "sc-smooth strong bundle proper covering functor `P̃ : Ẽ → E`": the project's
  `Q'.StrongBundleProperCovering Q` (`#print`ed: a functor `P̃` of the total categories over a
  functor `P : C' → C` of the bases, covering families `c'`, `c` of strong bundle uniformizers,
  an ep-functor `F : X' → X` of the models and a map `A : W' → W` which is a proper strong bundle
  covering of Definition 8.5.9 (`IsProperStrongBundleCovering2021`), with `Γ̄(A w) ≅ P̃(Γ̄'(w))`).
  This is the text's reading through models (p. 842); I did not find a way to state the notion
  without models and took it from the vocabulary.
- `P̃^*Λ = Λ ∘ P̃` on objects, written out.  "structurable": `IsStructurableFunctor`
  (Definition 18.3.3, `#print`ed: constant along morphisms and structurable in some model).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_37
open Polyfold

/-- Theorem 18.3.6: the pull-back of a structurable sc⁺-multisection functor along an sc-smooth
strong bundle proper covering functor is structurable. -/
def B : Prop :=
  ∀ (C C' : GCT.{0}) (S : C.PolyfoldConstruction) (S' : C'.PolyfoldConstruction)
    (V : C.VectorBundle) (V' : C'.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (Q' : V'.StrongPolyfoldBundleConstruction S')
    (Pt : Q'.StrongBundleProperCovering Q) (Λ : V.EObj → ℚ≥0),
    Q.IsStructurableFunctor Λ → Q'.IsStructurableFunctor (fun e => Λ (Pt.functor.obj e))

end RoundTrip.V18_37
