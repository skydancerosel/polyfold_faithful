import Polyfold
/-! Blind formalization of V18_13 (the text's Part II, §18.1, Theorem 18.1.5, p. 846 of the
Springer 2021 book; 2017: Theorem 18.1).

Text: `C` tame, `f` sc-Fredholm, `f(α) = 0`, `f'(α)` onto with kernel in good position: there is
an open `U ∋ |α|` such that (1) `Θ : C_U → {0, 1}`, `1` exactly on zeros, is a tame orbifold-type
ep⁺-subcategory, and (2) at zeros `β` in `C_U` `f'(β)` is onto with kernel in good position; the
support of `Θ` is a smooth submanifold (Note).

Choices:
- Setting: universe `0`; a GCT `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT
  `V` over `C` (Definition 17.7.1) with a strong polyfold bundle construction
  `Q : V.StrongPolyfoldBundleConstruction S` (Definition 17.7.4), and a section functor
  `f : V.SectionFunctor`.  "`C` tame": `S.IsTame` (Definition 17.1.8).  "`f` sc-Fredholm":
  `Q.IsScFredholmSectionFunctor f` (Definition 18.1.1, `#print`ed: every representative
  `f_Ψ̄` is sc-Fredholm).  The linearization needs `Q.IsScSmoothSectionFunctor f` (true for
  sc-Fredholm `f`), which B takes as a further hypothesis `hs`.
- `f(α) = 0`: `f.toFun α = V.objMk α 0`.  `f'(α)` = the project's `Q.linearization f hs α h0 hne`
  (Definition 18.1.3), which needs `Fact (S.TangentObj α)` (`α ∈ C¹` and `F(α) ≠ ∅`) and
  `F̄(α) ≠ ∅`; B takes both as hypotheses at `α` (the text presupposes them for `f'(α)`), and in
  (2) quantifies over them at `β`.  "onto": `Function.Surjective`.  "kernel in good position":
  `Q.IsKernelInGoodPosition` (`#print`ed: `ker f'(α)` in good position to the partial cone
  `C_αC`).
- `C_U` and its polyfold structure: `C.openSub U` with `S.openSubConstruction hU` (2021 p. 845).
  `Θ` = the project's `f.zeroIndicator` (`#print`ed: `1` if `f(β) = 0`, else `0`) restricted to
  `C_U` (`GCT.restrictTheta U`).
- "tame orbifold-type ep⁺-subcategory": branched ep⁺-subcategory (`IsBranchedSubcategory`,
  Definition 17.5.1), orbifold-type (`IsOrbifoldTypeBranched`, Definition 17.5.4 (2)) and tame in
  the sense of Definition 17.5.4 (3) (`IsTameSubcategory`, `#print`ed: `Θ ∘ Ψ` tame for
  `Θ(α) > 0`, `Ψ ∈ F(α)`), all for the structure of `C_U`.  (Definition 17.5.3 (2) is the other
  notion of tame in the text.)
- (2): for every object `β` with `|β| ∈ U` and `f(β) = 0`.
- The Note "the support of `Θ` is a smooth submanifold": read on the models, as in my V17_99: for
  every covering family `Ψ` of `C_U`, `supp(Γ_Ψ^*Θ)` is a smooth finite-dimensional submanifold
  of the object M-polyfold of `X_Ψ` (`MPolyfold.IsSmoothSubmanifold`).  Drop this conjunct if the
  Note is a remark rather than part of the claim.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_13
open Polyfold

/-- Theorem 18.1.5 (implicit function theorem): near a zero `α` of an sc-Fredholm section
functor over a tame polyfold with `f'(α)` onto and kernel in good position, the zero indicator is
a tame orbifold-type branched ep⁺-subcategory of `C_U`, all zeros in `C_U` are of the same kind,
and the support is a smooth submanifold in the models. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
    S.IsTame → Q.IsScFredholmSectionFunctor f → ∀ (hs : Q.IsScSmoothSectionFunctor f)
    (α : C.Obj) [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0)
    (hne : (Q.F α).Nonempty),
    Function.Surjective (Q.linearization f hs α h0 hne) →
    Q.IsKernelInGoodPosition f hs α h0 hne →
    ∃ (U : Set C.toGroupoidStr.OrbitSpace) (hU : IsOpen U), C.toGroupoidStr.π α ∈ U ∧
      -- (1)
      (S.openSubConstruction hU).IsBranchedSubcategory (GCT.restrictTheta U f.zeroIndicator) ∧
      (S.openSubConstruction hU).IsTameSubcategory (GCT.restrictTheta U f.zeroIndicator) ∧
      (C.openSub U).IsOrbifoldTypeBranched (GCT.restrictTheta U f.zeroIndicator) ∧
      -- (2)
      (∀ (β : C.Obj), C.toGroupoidStr.π β ∈ U → ∀ (h0' : f.toFun β = V.objMk β 0)
        [Fact (S.TangentObj β)] (hne' : (Q.F β).Nonempty),
        Function.Surjective (Q.linearization f hs β h0' hne') ∧
          Q.IsKernelInGoodPosition f hs β h0' hne') ∧
      -- the Note: the support is a smooth submanifold (in every model of `C_U`)
      (∀ c : (S.openSubConstruction hU).CoveringFamily,
        ((S.openSubConstruction hU).modelEP c.Ψ).X.PObj.IsSmoothSubmanifold
          (EpGroupoid.supp
            ((S.openSubConstruction hU).modelPull c.Ψ (GCT.restrictTheta U f.zeroIndicator))))

end RoundTrip.V18_13
