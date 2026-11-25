import Polyfold
/-! Blind formalization of V18_49 (the text's §18.5, Proposition 18.5.6, p. 859 of the Springer
2021 book; 2017: Proposition 18.2), orientations through models.

Text: (1) `f` is orientable iff `f_Ψ̄` is, for a model; (2) an orientation of `f` gives
orientations of the models; (3) model orientations `o`, `o'` come from one orientation of `f` iff
they correspond under the comparison.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT
  `V`, a strong polyfold bundle construction `Q` (vocabulary), an sc-Fredholm section functor `f`
  (`Q.IsScFredholmSectionFunctor`, Definition 18.1.1).  The vocabulary's notions of orientation
  (`OrSection`, `IsOrientation`, `IsOrientable`, `ModelOr`, `IsModelOrientation`) take as
  arguments `S.AdmitsModelBumpFunctions`, `S.IsTame`, `Q.IsScFredholmSectionFunctorTame f` and
  `Q.HasStrongBundleUniformizers`; I add these as hypotheses for that reason (the quoted
  statement names none of them; bump functions and tameness are what the text needs to speak of
  `DET(f, α)` and model orientations, as I understand it).
- "a model": a covering model `W_Ψ̄ → X_Ψ` of a bundle covering family `c`
  (`Q.BundleCoveringFamily`), with the model section `f^Ψ̄_Ψ`; "`f_Ψ̄` orientable" = it has an
  orientation (`∃ m : Q.ModelOr hf c, Q.IsModelOrientation … c m`, Definition 12.5.4 in the
  model).  "for a model" in (1) is read as "for every covering model" (each model is equivalent).
- (2) "an orientation of `f` gives orientations of the models": for every orientation `o` of `f`
  and every covering family `c`, the pulled-back section `Γ̄^* o` (the vocabulary's `pullCat`)
  is an orientation of the model section.
- (3) "the comparison": the transport of sections between two covering models along the natural
  generalized strong bundle isomorphism (the vocabulary's `modelTransport c c'`).  For model
  orientations `m` (on `c`) and `m'` (on `c'`): there is an orientation `o` of `f` with
  `Γ̄_c^* o = m` and `Γ̄_{c'}^* o = m'` iff `modelTransport c c' m = m'`.
- The proof is left to the reader in the text; not part of the claim.  Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_49
open Polyfold

/-- Proposition 18.5.6: orientations of `f` and of its covering models. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S)
    (hF : Q.HasStrongBundleUniformizers) (ht : S.IsTame) (hb : S.AdmitsModelBumpFunctions)
    (f : V.SectionFunctor) (hf : Q.IsScFredholmSectionFunctor f)
    (hfT : Q.IsScFredholmSectionFunctorTame f),
    -- (1)
    (∀ c : Q.BundleCoveringFamily,
      Q.IsOrientable hf hb ht hfT hF ↔
        ∃ m : Q.ModelOr hf c, Q.IsModelOrientation hf hb ht hfT c m) ∧
    -- (2)
    (∀ o : Q.OrSection hf hF, Q.IsOrientation hf hb ht hfT hF o →
      ∀ c : Q.BundleCoveringFamily,
        Q.IsModelOrientation hf hb ht hfT c (Q.pullCat hf hb hF c o)) ∧
    -- (3)
    (∀ (c c' : Q.BundleCoveringFamily) (m : Q.ModelOr hf c) (m' : Q.ModelOr hf c'),
      Q.IsModelOrientation hf hb ht hfT c m → Q.IsModelOrientation hf hb ht hfT c' m' →
      ((∃ o : Q.OrSection hf hF, Q.IsOrientation hf hb ht hfT hF o ∧
          Q.pullCat hf hb hF c o = m ∧ Q.pullCat hf hb hF c' o = m') ↔
        Q.modelTransport hf hb c c' m = m'))

end RoundTrip.V18_49
