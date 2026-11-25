import Polyfold
/-! Blind formalization of V17_140 (the text's Part II, §17.8, Proposition 17.8.15, pp. 837–838
of the Springer 2021 book; 2017: Proposition 17.12).

Text: for a proper polyfold covering functor the bijection (17.103) is an sc-diffeomorphism.

Choices:
- Setting: universe `0`; `A B : GCT.{0}` and `Pc : ProperPolyfoldCoveringFunctor A B`
  (Definition 17.8.13, `#print`ed: the functor `P`, its proper covering property, and the proper
  polyfold covering structure `Pc.S`: the construction `F = Pc.S.toC`, the polyfold structure
  `Pc.S.SB` of `B` on the uniformizers of `F`, and the M-polyfold structures `Pc.S.MH U U'` on
  the transition sets `M(Ψ̂, Ψ̂')`).  B ranges over all pairs `U = (Ψ̂, Ψ)`, `U' = (Ψ̂', Ψ')` of
  uniformizers of `F`.
- (17.103): `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`, `(e, φ, e') ↦ (p(e, φ, e'), e)` = the project's
  `fibredTransMap` (`#print`ed: `a ↦ (transMap a, src a)` into the subtype
  `TransFibred = {(a, e) | s(a) = τ̂(e)}`), with `p` = `transMap` (docstring:
  `p(e, φ, e') = (τ̂(e), P(φ), τ̂'(e'))`).
- Structures: `M(Ψ̂, Ψ̂')` carries `Pc.S.MH U U'`; `M(Ψ, Ψ')` carries `Pc.S.SB.transPolyfold`;
  `E` its object M-polyfold `U.unif.E.PObj`; `O_β` the M-polyfold `U.unif.Ψ.P`.  The fibred
  product carries the sub-M-polyfold structure of `M(Ψ, Ψ') × E` (Proposition 2.5.20, `s` being a
  local sc-diffeomorphism).
- "sc-diffeomorphism" onto the fibred product, written out: (a) the map into the product is
  sc-smooth (its two components `p` and `s` are sc-smooth); (b) it is a bijection onto the
  fibred product; (c) its inverse is sc-smooth on the sub-M-polyfold fibred product, the
  project's `MPolyfold.IsScSmoothOnFibredProduct`, whose arguments (`s : M(Ψ, Ψ') → O` a local
  sc-diffeomorphism, `τ̂` sc-smooth) are asserted with `∃` (true facts of the setting).  The
  inverse is any left inverse of the bijection (I do not use the project's `fibredTransInv`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_140
open Polyfold

/-- Proposition 17.8.15: the bijection (17.103) `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` is an
sc-diffeomorphism onto the sub-M-polyfold fibred product. -/
def B : Prop :=
  ∀ (A B : GCT.{0}) (Pc : ProperPolyfoldCoveringFunctor A B) (U U' : Pc.S.toC.Unif),
    -- the components `p` and `s` of (17.103) are sc-smooth
    (Pc.S.MH U U').IsScSmoothMap
        (Pc.S.SB.transPolyfold (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U)
          (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U'))
        (fun a => U.unif.transMap U'.unif a) ∧
    (Pc.S.MH U U').IsScSmoothMap U.unif.E.PObj (fun a => GroupoidStr.TransitionSet.src a) ∧
    Function.Bijective (U.unif.fibredTransMap U'.unif) ∧
    ∃ (hs : (Pc.S.SB.transPolyfold (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U)
          (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U')).IsLocalScDiffeo U.unif.Ψ.P
          (fun a => GroupoidStr.TransitionSet.src a))
      (hτ : U.unif.E.PObj.IsScSmoothMap U.unif.Ψ.P U.unif.τ.obj),
      ∀ g : U.unif.TransFibred U'.unif → U.unif.HatTrans U'.unif,
        Function.LeftInverse g (U.unif.fibredTransMap U'.unif) →
        MPolyfold.IsScSmoothOnFibredProduct
          (Pc.S.SB.transPolyfold (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U)
            (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U'))
          U.unif.E.PObj (Pc.S.MH U U') hs hτ g

end RoundTrip.V17_140
