import Polyfold
/-! Blind formalization of V18_28 (the text's Part II, §18.2, Theorem 18.2.6, p. 851 of the
Springer 2021 book; 2017: Theorem 18.4).

Text: with a reflexive auxiliary norm and reflexive local compactness, an open `U_b` of `|∂C|`
controlling compactness of `∂f` extends to `U` with `U ∩ |∂C| = U_b` controlling compactness
(from Theorem 12.4.6).

Choices:
- Setting: universe `0`; `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT `V`
  with a strong polyfold bundle construction `Q`, a section functor `f`.  Standing hypotheses
  of §18.2 (named in the docstring of the project's Definition 18.2.4): `f` sc-Fredholm
  (`Q.IsScFredholmSectionFunctor f`) and reflexive `(0, 1)`-fibres (`Q.HasReflexiveFibers`).
  I did not add tameness of `C` (not named in the quoted statement); if Theorem 12.4.6 assumes a
  tame ep-groupoid, `S.IsTame` should be added.
- "reflexive auxiliary norm": `Q.IsReflexiveAuxNormFunctor N` (Definition 18.1.11 read in the
  models, as in my V18_21).  "reflexive local compactness": `Q.HasReflexiveLocalCompactness f`
  (Definition 18.2.4, `#print`ed: for every reflexive auxiliary norm and every `z ∈ |C|` an open
  `U(z) ∋ z` with `cl{y ∈ U(z) | |N| ∘ |f|(y) ≤ 1}` compact).
- `|∂C| = π(∂C)`, `∂C` the objects with `d ≥ 1` (`S.boundarySet`, Definition 17.1.30).  `∂f` is
  `f` restricted to `∂C`, so `|S_{∂f}| = π(S_f ∩ ∂C)`.
- "`U_b` open in `|∂C|` controlling compactness of `∂f`" (Definition 18.2.3 for `∂f` and the
  restriction of `N`): `U_b = W ∩ |∂C|` for an open `W ⊆ |C|`, `|S_{∂f}| ⊆ U_b`, and
  `cl{z ∈ U_b | |N| ∘ |f|(z) ≤ 1}` compact, the closure taken in `|C|` (`f.sublevel N 1`).  The
  closure in `|∂C|` would be the same set when `|∂C|` is closed in `|C|`.
- Conclusion: an open `U ⊆ |C|` with `(N, U)` controlling compactness for `f` (the project's
  `f.ControlsCompactness N U`, `#print`ed: `U` open, `|S_f| ⊆ U`, `cl(U ∩ {|N| ∘ |f| ≤ 1})`
  compact) and `U ∩ |∂C| = U_b`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_28
open Polyfold

/-- Theorem 18.2.6: a relatively open `U_b ⊆ |∂C|` controlling compactness of `∂f` for a
reflexive auxiliary norm extends to an open `U` controlling compactness of `f` with
`U ∩ |∂C| = U_b`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
    Q.IsScFredholmSectionFunctor f → Q.HasReflexiveFibers → Q.HasReflexiveLocalCompactness f →
    ∀ N : V.EObj → ENNReal, Q.IsReflexiveAuxNormFunctor N →
    ∀ Ub : Set C.toGroupoidStr.OrbitSpace,
      (∃ W : Set C.toGroupoidStr.OrbitSpace, IsOpen W ∧
        Ub = W ∩ C.toGroupoidStr.π '' S.boundarySet) →
      C.toGroupoidStr.π '' (f.zeroSet ∩ S.boundarySet) ⊆ Ub →
      IsCompact (closure (Ub ∩ f.sublevel N 1)) →
      ∃ U : Set C.toGroupoidStr.OrbitSpace, f.ControlsCompactness N U ∧
        U ∩ C.toGroupoidStr.π '' S.boundarySet = Ub

end RoundTrip.V18_28
