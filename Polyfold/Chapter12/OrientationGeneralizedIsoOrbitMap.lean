import Polyfold.Chapter12.OrientationEqualOrbitMaps
import Polyfold.Chapter12.OrientationGeneralizedIsoUnique

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 595, **Theorem 12.5.7 (2)** (2017: Theorem 12.12 (2)), with **Theorem 10.5.7** (p. 508) and
**Definition 8.4.2** (p. 382): the push-forward orientation of a generalized strong bundle
isomorphism `f̄ : W → W'` depends only on the map `|f̄| : |W| → |W'|` of orbit spaces.

## The text, paraphrased

(Theorem 10.5.7) For strong bundles with the local regularity property, generalized strong
bundle isomorphisms with the same map of orbit spaces are equal.  (Theorem 12.5.7 (2)) An
orientation `o` of `f` has a push-forward orientation `o' = f̄_* o` of `f' = f̄_* f`.

For a base which is not effective two generalized strong bundle isomorphisms with the same map
of orbit spaces can differ (`LocalizationLRBundleBaseExamples.not_theorem_10_5_7_of_isLRLocal`),
so `f̄` is not determined by `|f̄|`.  The push-forward of orientations still is.

## What is formalized

With the local regularity property of the target `W'` (Definition 8.4.2, read as
`EpStrongBundle.IsLRLocal`) and no effectiveness:

* `SDiagram.orbitOrMap_eq_of_orbitMap_eq`: diagrams `D, D' : W → W'` with both legs strong
  bundle equivalences and `|D| = |D'|` induce the same map `|O_f| → |O_{f'}|`.  Proof: on the
  weak fibred product `V ×_W V'` of the left legs (Theorem 10.2.2) the left legs are naturally
  equivalent and the right legs have the same map of orbit spaces; the latter induce the same map
  of orientations by Proposition 10.4.7 (`orbitOrMap_eq_of_orbitMap_eq` for equivalences).
* `GenSBMap.orbitOrMap_eq_of_orbitMap_eq`: `|f̄|_* = |ḡ|_*` on `|O_f|` for generalized strong
  bundle isomorphisms `f̄, ḡ` with `|f̄| = |ḡ|` and `f̄_* f = ḡ_* f = f'`.
* **`GenSBMap.theorem_12_5_7_two_corr_indep_of_orbitMap_eq`**: if morphism-invariant families
  `o`, `o'` correspond over one representative of `f̄`, they correspond over every representative
  of every `ḡ` with `|ḡ| = |f̄|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' : SEP.{u}}

namespace SDiagram

variable {D D' : SDiagram A A'} (hΨ : SEP.equivalences D.Ψ) (hΨ' : SEP.equivalences D'.Ψ)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hff'' : D'.hΦ.pullback f = (sbe hΨ').pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

include hff'' in
/-- **Theorem 12.5.7 for diagrams with the same map of orbit spaces**, p. 595 (2017:
Theorem 12.12): if `W'` has the local regularity property (Definition 8.4.2 as `IsLRLocal`),
diagrams `D, D'` with both legs strong bundle equivalences and `|D| = |D'| : |W| → |W'|` induce
the same map `|O_f| → |O_{f'}|`.  The diagrams need not be equivalent. -/
theorem orbitOrMap_eq_of_orbitMap_eq (h : D.orbitMap = D'.orbitMap) (hA' : A'.E.IsLRLocal) :
    D.orbitOrMap hΨ hF hF' hff' hsec hsec' = D'.orbitOrMap hΨ' hF hF' hff'' hsec hsec' := by
  -- the weak fibred product `V ×_W V'` of the left legs
  obtain ⟨hZ, hnat, -, -⟩ := SBWeakFibredProduct.theorem_10_2_2 D.isEquivalence_Φ D'.Φ
  have hX := SBWeakFibredProduct.theorem_10_2_2_right D.isEquivalence_Φ D'.Φ D'.isEquivalence_Φ
  set pX := SBWeakFibredProduct.projX D.isEquivalence_Φ D'.Φ
  set pZ := SBWeakFibredProduct.projZ D.isEquivalence_Φ D'.Φ
  have horb : (Hom.Φ (pX ≫ D.Ψ)).orbitMap = (Hom.Φ (pZ ≫ D'.Ψ)).orbitMap := by
    funext q
    induction q using Quotient.inductionOn with | h w => ?_
    have h₁ := congrFun hnat.orbitMap_eq ((SBWeakFibredProduct.wfpSEP D.isEquivalence_Φ
      D'.Φ).E.toEpGroupoid.π w)
    change (Hom.Φ D.Ψ).orbitMap ((Hom.Φ pX).orbitMap (GroupoidStr.π _ w)) =
      (Hom.Φ D'.Ψ).orbitMap ((Hom.Φ pZ).orbitMap (GroupoidStr.π _ w))
    change (Hom.Φ D.Φ).orbitMap ((Hom.Φ pX).orbitMap (GroupoidStr.π _ w)) =
      (Hom.Φ D'.Φ).orbitMap ((Hom.Φ pZ).orbitMap (GroupoidStr.π _ w)) at h₁
    rw [← D.orbitMap_orbitMap_Φ, ← D'.orbitMap_orbitMap_Φ, h₁, h]
  obtain ⟨ζ₁⟩ := hnat.symm
  have k₁ := D.hΦ.comp (sbe hX)
  have hs : IsSection A.P f := hF.2.isScSmooth.1
  have hF₃ : (SBWeakFibredProduct.wfpSEP D.isEquivalence_Φ D'.Φ).E.IsScFredholmSectionFunctor
      (k₁.pullback f) := (theorem_10_4_5_fred k₁).2.1 hF
  have hpbH₁ : k₁.pullback f = (sbe hX).pullback (D.hΦ.pullback f) :=
    (proposition_10_4_4 (sbe hX) D.hΦ).1 f hs
  have hpbH₂ : k₁.pullback f = (sbe hZ).pullback (D'.hΦ.pullback f) := by
    rw [← (proposition_10_4_4 (sbe hZ) D'.hΦ).1 f hs]
    exact proposition_10_4_2 k₁ (D'.hΦ.comp (sbe hZ)) hnat.orbitMap_eq hF.1
  funext x
  exact theorem_12_5_7_rep_indep_of_orbitMap_eq D.hΦ (sbe hΨ) D'.hΦ (sbe hΨ') (sbe hX) (sbe hZ)
    ζ₁ hF hF' (D.isScFredholm_pullback hF) (D'.isScFredholm_pullback hF) hF₃ rfl hff' rfl hff''
    hpbH₁ hpbH₂ hsec hsec' (D.hasScPlusSectionsThrough_B hsec)
    (D'.hasScPlusSectionsThrough_B hsec) (k₁.hasScPlusSectionsThrough hsec) horb hA' x

end SDiagram

namespace GenSBMap

variable {F G : GenSBMap A A'} (hFi : F.IsGeneralizedIso) (hGi : G.IsGeneralizedIso)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
  (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hf' : f' = pushforward hFi f) (hg' : f' = pushforward hGi f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

/-- **`|f̄|_*` depends only on `|f̄|`**: for generalized strong bundle isomorphisms
`f̄, ḡ : W → W'` with `|f̄| = |ḡ|` and `f̄_* f = ḡ_* f = f'`, and a target with the local
regularity property (Definition 8.4.2 as `IsLRLocal`), the maps `|O_f| → |O_{f'}|` agree. -/
theorem orbitOrMap_eq_of_orbitMap_eq (horb : F.orbitMap = G.orbitMap) (hA' : A'.E.IsLRLocal) :
    orbitOrMap hFi hF hF' hf' hsec hsec' = orbitOrMap hGi hF hF' hg' hsec hsec' := by
  rw [orbitOrMap_eq hFi hF hF' hf' hsec hsec' (cls_rep hFi),
    orbitOrMap_eq hGi hF hF' hg' hsec hsec' (cls_rep hGi)]
  refine SDiagram.orbitOrMap_eq_of_orbitMap_eq _ _ hF hF' _ _ hsec hsec' ?_ hA'
  have e₁ : (rep hFi).orbitMap = F.orbitMap := congrArg GenSBMap.orbitMap (cls_rep hFi)
  have e₂ : (rep hGi).orbitMap = G.orbitMap := congrArg GenSBMap.orbitMap (cls_rep hGi)
  exact e₁.trans (horb.trans e₂.symm)

/-- **Theorem 12.5.7 (2), independence of the generalized isomorphism**, p. 595: let `o`, `o'`
be families of orientations invariant under the morphisms, `f̄, ḡ : W → W'` generalized strong
bundle isomorphisms with `|f̄| = |ḡ|` and `f̄_* f = ḡ_* f = f'`, and let `W'` have the local
regularity property (Definition 8.4.2 as `IsLRLocal`).  If `o'` corresponds to `o` over the
middle of one diagram `D` representing `f̄`, it corresponds to `o` over the middle of every
diagram `D'` representing `ḡ`. -/
theorem theorem_12_5_7_two_corr_indep_of_orbitMap_eq (horb : F.orbitMap = G.orbitMap)
    (hA' : A'.E.IsLRLocal) {D D' : SDiagram A A'} (hD : D.cls = F) (hD' : D'.cls = G)
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
    (sbe (equivalences_Ψ_of_cls hGi hD')).orEqv (D'.isScFredholm_pullback hF) hF'
        (pullback_eq_of_cls' hGi hD' hF.1 hg') (D'.hasScPlusSectionsThrough_B hsec) hsec' v hv
        (o' (D'.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hGi hD')).smooth_obj hv)) =
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
  have e₂ := D'.orbitOrMap_mk (equivalences_Ψ_of_cls hGi hD') hF hF'
    (pullback_eq_of_cls' hGi hD' hF.1 hg') hsec hsec' v hv (o _ hs)
  have k₁ := orbitOrMap_eq hFi hF hF' hf' hsec hsec' hD
  have k₂ := orbitOrMap_eq hGi hF hF' hg' hsec hsec' hD'
  have k₀ := orbitOrMap_eq_of_orbitMap_eq hFi hGi hF hF' hf' hg' hsec hsec' horb hA'
  have e₃ := e₁.symm.trans ((congrFun k₁ _).symm.trans ((congrFun k₀ _).trans
    ((congrArg _ hcls).trans ((congrFun k₂ _).trans e₂))))
  obtain ⟨β, hb, hb', hβ⟩ := A'.E.orRel_of_quot_eq hF' hsec' e₃
  have h5 := (Equiv.symm_apply_eq _).2 (hcorr a ha).symm
  have h3 := ho' β hb hb' (A'.X.PObj.smoothVal_mem _) (A'.X.PObj.smoothVal_mem _)
  exact (Equiv.eq_symm_apply _).1 (h3.symm.trans ((congrArg _ h5.symm).trans hβ))

end GenSBMap

end SBLocalization

end Polyfold
