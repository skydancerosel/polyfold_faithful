import Polyfold.Chapter12.OrientationGeneralizedIsoTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 595, **Theorem 12.5.7 (2)** (2017: Theorem 12.12 (2)): the push-forward orientation of a
generalized strong bundle isomorphism `f̄ : W → W'` does not depend on the diagram representing
`f̄`.

## The text, paraphrased

An orientation `o` of `f` has a push-forward orientation `o' = f̄_* o` of `f'`.

## What is formalized

For a diagram `W ←Φ– V –Ψ→ W'` the orientation `o'` corresponds to `o` over `V` if
`Ψ^* o' = Φ^* o` in `Or^{f''}_v` for every smooth `v ∈ V` (`f'' = Φ^* f = Ψ^* f'`).

* `SDiagram.orbitOrMap_mk`: `|D|_*` on the class of `(Φ(v), ω)` is the class of
  `(Ψ(v), (Ψ^*)⁻¹ Φ^* ω)`.
* `GenSBMap.theorem_12_5_7_two_corr_indep`: if `o` and `o'` are invariant under the morphisms and
  correspond over one representative of `f̄`, they correspond over every representative.
* `GenSBMap.theorem_12_5_7_two_cls_unique`: an orientation `o` of `f` (Definition 12.5.4) has
  exactly one orientation `o'` of `f'` corresponding to `o` over **all** representatives of `f̄`;
  so `o' = f̄_* o` is defined by the class.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' : SEP.{u}}

namespace SDiagram

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

/-- **`|D|_*` on a class over `Φ(v)`**: `|D|_* |(Φ(v), ω)| = |(Ψ(v), (Ψ^*)⁻¹ Φ^* ω)|`. -/
theorem orbitOrMap_mk (v : D.B.Obj) (hv : v ∈ D.B.X.PObj.smoothSet)
    (ω : Orx f hF.2 (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :
    D.orbitOrMap hΨ hF hF' hff' hsec hsec'
        (Quot.mk _ ⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj hv), ω⟩) =
      Quot.mk _ ⟨A'.X.PObj.smoothMk _ ((sbe hΨ).smooth_obj hv),
        ((sbe hΨ).orEqv (D.isScFredholm_pullback hF) hF' hff' (D.hasScPlusSectionsThrough_B hsec)
          hsec' v hv).symm (D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl
            (D.hasScPlusSectionsThrough_B hsec) hsec v hv ω)⟩ := by
  have h1 : D.hΦ.orbitOrMap (D.isScFredholm_pullback hF) hF rfl
      (D.hasScPlusSectionsThrough_B hsec) hsec
      (Quot.mk _ ⟨D.B.X.PObj.smoothMk v hv, D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl
        (D.hasScPlusSectionsThrough_B hsec) hsec v hv ω⟩) =
      Quot.mk _ ⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj hv), ω⟩ :=
    congrArg (fun t => Quot.mk (A.E.OrRel hF hsec)
      (⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj hv), t⟩ : OrSpace f hF.2))
      (Equiv.symm_apply_apply (D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl
        (D.hasScPlusSectionsThrough_B hsec) hsec v hv) ω)
  rw [← h1]
  unfold SDiagram.orbitOrMap
  exact (congrArg (Equiv.ofBijective _ ((sbe hΨ).orbitOrMap_bijective
    (D.isScFredholm_pullback hF) hF' hff' (D.hasScPlusSectionsThrough_B hsec) hsec'))
    (Equiv.ofBijective_symm_apply_apply _ (D.hΦ.orbitOrMap_bijective
      (D.isScFredholm_pullback hF) hF rfl (D.hasScPlusSectionsThrough_B hsec) hsec) _)).trans rfl

end SDiagram

namespace GenSBMap

variable {F : GenSBMap A A'} (hFi : F.IsGeneralizedIso) {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
  (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hf' : f' = pushforward hFi f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

/-- **Theorem 12.5.7 (2), independence of the representative**, p. 595: let `o`, `o'` be
sections of `σ`, `σ'` invariant under the morphisms.  If `o'` corresponds to `o` over the middle
of one diagram `D` representing `f̄`, then it corresponds to `o` over the middle of every diagram
`D'` representing `f̄`. -/
theorem theorem_12_5_7_two_corr_indep {D D' : SDiagram A A'} (hD : D.cls = F) (hD' : D'.cls = F)
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), Orx f hF.2 a hs}
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs}
    (ho : ∀ (φ : A.Mor) {x x' : A.Obj} (hx : A.X.src φ = x) (hx' : A.X.tgt φ = x')
      (hs : x ∈ A.X.PObj.smoothSet) (hs' : x' ∈ A.X.PObj.smoothSet),
      A.E.orMor hF hsec φ hx hx' hs hs' (o x hs) = o x' hs')
    (ho' : ∀ (φ : A'.Mor) {x x' : A'.Obj} (hx : A'.X.src φ = x) (hx' : A'.X.tgt φ = x')
      (hs : x ∈ A'.X.PObj.smoothSet) (hs' : x' ∈ A'.X.PObj.smoothSet),
      A'.E.orMor hF' hsec' φ hx hx' hs hs' (o' x hs) = o' x' hs')
    (hcorr : ∀ v (hv : v ∈ D.B.X.PObj.smoothSet),
      (sbe (equivalences_Ψ_of_cls hFi hD)).orEqv (D.isScFredholm_pullback hF) hF'
          (pullback_eq_of_cls' hFi hD hF.1 hf') (D.hasScPlusSectionsThrough_B hsec) hsec' v hv
          (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD)).smooth_obj hv)) =
        D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl (D.hasScPlusSectionsThrough_B hsec)
          hsec v hv (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)))
    (v : D'.B.Obj) (hv : v ∈ D'.B.X.PObj.smoothSet) :
    (sbe (equivalences_Ψ_of_cls hFi hD')).orEqv (D'.isScFredholm_pullback hF) hF'
        (pullback_eq_of_cls' hFi hD' hF.1 hf') (D'.hasScPlusSectionsThrough_B hsec) hsec' v hv
        (o' (D'.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD')).smooth_obj hv)) =
      D'.hΦ.orEqv (D'.isScFredholm_pullback hF) hF rfl (D'.hasScPlusSectionsThrough_B hsec)
        hsec v hv (o (D'.Φ.ϕ.obj v) (D'.hΦ.smooth_obj hv)) := by
  have hs := D'.hΦ.smooth_obj hv
  obtain ⟨a, ha, ψ, h1, h2⟩ := D.hΦ.exists_smooth_iso hs
  -- the classes of `(Φ(a), o)` and `(Φ'(v), o)` agree
  have hcls : (Quot.mk (A.E.OrRel hF hsec)
      ⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj ha), o _ (D.hΦ.smooth_obj ha)⟩) =
      Quot.mk _ ⟨A.X.PObj.smoothMk _ hs, o _ hs⟩ :=
    Quot.sound ⟨ψ, h1, h2, ho ψ h1 h2 _ _⟩
  have e₁ := D.orbitOrMap_mk (equivalences_Ψ_of_cls hFi hD) hF hF'
    (pullback_eq_of_cls' hFi hD hF.1 hf') hsec hsec' a ha (o _ (D.hΦ.smooth_obj ha))
  have e₂ := D'.orbitOrMap_mk (equivalences_Ψ_of_cls hFi hD') hF hF'
    (pullback_eq_of_cls' hFi hD' hF.1 hf') hsec hsec' v hv (o _ hs)
  have k₁ := orbitOrMap_eq hFi hF hF' hf' hsec hsec' hD
  have k₂ := orbitOrMap_eq hFi hF hF' hf' hsec hsec' hD'
  have e₃ := e₁.symm.trans ((congrFun k₁ _).symm.trans
    ((congrArg _ hcls).trans ((congrFun k₂ _).trans e₂)))
  obtain ⟨β, hb, hb', hβ⟩ := A'.E.orRel_of_quot_eq hF' hsec' e₃
  have h5 := (Equiv.symm_apply_eq _).2 (hcorr a ha).symm
  have h3 := ho' β hb hb' (A'.X.PObj.smoothVal_mem _) (A'.X.PObj.smoothVal_mem _)
  exact (Equiv.eq_symm_apply _).1 (h3.symm.trans ((congrArg _ h5.symm).trans hβ))

variable (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hfT : A.B.IsScFredholmSectionTame f) (hX' : A'.X.PObj.IsTame)
  (hbump' : A'.X.PObj.AdmitsBumpFunctions) (hfT' : A'.B.IsScFredholmSectionTame f')

/-- **Theorem 12.5.7 (2) for the class**, p. 595 (2017: Theorem 12.12 (2)), with Part I's
hypotheses on `W` and `W'`: an orientation `o` of `f` (Definition 12.5.4) has exactly one
orientation `o'` of `f'` which corresponds to `o` over the middle of every diagram representing
`f̄`. -/
theorem theorem_12_5_7_two_cls_unique
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), Orx f hF.2 a hs} :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    haveI := paracompactSpace_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_pullback A'.B
    haveI := paracompactSpace_rn_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A'.B
    A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o →
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs,
      A'.E.definition_12_5_4 hF' hsec' (orTopology (orLocalTransport hX' hbump' hfT' hsec')) o' ∧
        ∀ (D : SDiagram A A') (hD : D.cls = F) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (equivalences_Ψ_of_cls hFi hD)).orEqv (D.isScFredholm_pullback hF) hF'
              (pullback_eq_of_cls' hFi hD hF.1 hf') (D.hasScPlusSectionsThrough_B hsec) hsec' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl (D.hasScPlusSectionsThrough_B hsec)
              hsec v hv (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  intro ho
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := theorem_12_5_7_two_cls hFi hF hF' hf' hsec hsec' hX hbump hfT
    hX' hbump' hfT' (cls_rep hFi) ho
  refine ⟨o', ⟨ho', fun D hD v hv => ?_⟩, fun o'' ⟨ho'', hc''⟩ =>
    huniq o'' ⟨ho'', hc'' (rep hFi) (cls_rep hFi)⟩⟩
  exact theorem_12_5_7_two_corr_indep hFi hF hF' hf' hsec hsec' (cls_rep hFi) hD ho.2 ho'.2 hc
    v hv

end GenSBMap

end SBLocalization

end Polyfold
