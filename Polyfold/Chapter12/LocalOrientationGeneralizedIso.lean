import Polyfold.Chapter12.LocalOrientationRepresentativeIndep
import Polyfold.Chapter12.OrientationGeneralizedIsoUnique

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** for Chapter 10's objects, for the linearizations made with
local sc⁺-sections: the map `|f̄|_* : |O_f| → |O_{f'}|` of a generalized strong bundle
isomorphism `f̄ : W → W'` (Definition 10.5.2, a class `GenSBMap A A'` of diagrams
`SDiagram A A'`), `f'` the push-forward of `f` (Theorem 10.5.4), with the topology, and the
push-forward of orientations.

## The text, paraphrased

(Theorem 12.5.7) For strong bundles over tame ep-groupoids, sc-Fredholm section functors `f`,
`f'` and a generalized strong bundle isomorphism `f̄ : W → W'` with `f̄_* f = f'`: (1) `f̄` induces
a homeomorphism `|O_f| → |O_{f'}|` covering the homeomorphism `|X_∞| → |X'_∞|`; (2) an
orientation `o` of `f` has a unique push-forward orientation `o'` of `f'`.  A representative
`W ←Φ– V –Φ'→ W'` of `f̄` consists of strong bundle equivalences; the pull-back `f''` of `f` to
`V` is the pull-back of `f'`, and `|f̄|_*` is the composite of the bijections
`|O_f| ← |O_{f''}| → |O_{f'}|`.  Different representatives give the same map.

## What is formalized

The orientation sets are the local ones (`OrxLoc`) and the hypotheses are those of the text:
the object M-polyfolds of `W`, `W'` are tame and `f` has tame germ data (the middle of a
diagram inherits both; `f' = f̄_* f` inherits the tame germ data,
`GenSBMap.isScFredholmSectionTame_of_eq_pushforward`).  No sc-smooth bump functions and no
sc⁺-sections over the whole object space are assumed.

* `SDiagram.orbitOrMapLoc` (`|Ψ|_* ∘ |Φ|_*⁻¹`), bijective, fibre preserving
  (`orbitProjLoc_orbitOrMapLoc`), `orbitOrMapLoc_mk`.
* **Independence of the representative**: `SDiagram.orbitOrMapLoc_eq_of_equiv`.
* **Functoriality**: `SDiagram.orbitOrMapLoc_comp`, `SDiagram.orbitOrMapLoc_id`.
* On classes: `GenSBMap.orbitOrMapLoc` for `f' = f̄_* f`, equal to the map of every
  representative (`orbitOrMapLoc_eq`), `GenSBMap.theorem_12_5_7_cls_loc`,
  `GenSBMap.theorem_12_5_7_functorial_loc`, `GenSBMap.theorem_12_5_7_id_loc`.
* `GenSBMap.isScFredholmSectionTame_of_eq_pushforward`: tame germ data of `f` give those of
  `f' = f̄_* f` (Theorem 10.4.5 for both legs of a representative).
* `GenSBMap.theorem_12_5_7_one_loc_cls`: **(1)** for the class: homeomorphisms
  `|O_f| ≃ₜ |O_{f'}|`, `|X_∞| ≃ₜ |X'_∞|` commuting with `|σ|`, `|σ'|`, whose underlying maps
  are `GenSBMap.orbitOrMapLoc` and `GenSBMap.smoothOrbitMap`.
* `GenSBMap.theorem_12_5_7_two_loc_cls`: **(2)** for every representative `D` of the class: an
  orientation `o` of `f` (Definition 12.5.4) has exactly one orientation `o'` of `f'`
  corresponding to `o` over the middle of `D`.
* `GenSBMap.theorem_12_5_7_two_corr_indep_loc`, `GenSBMap.theorem_12_5_7_two_loc_cls_unique`:
  the correspondence does not depend on the representative, so an orientation `o` of `f` has
  exactly one orientation `o'` of `f'` corresponding to `o` over all representatives of `f̄`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

open StrongRetr

universe u

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' A'' : SEP.{u}}

namespace SDiagram

/-! ### The maps of one diagram -/

section Maps

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f')

/-- **`|D|_* = |Ψ|_* ∘ |Φ|_*⁻¹ : |O_f| → |O_{f'}|`** (proof of Theorem 12.5.7), for a diagram
with both legs strong bundle equivalences and `Φ^* f = Ψ^* f'`. -/
def orbitOrMapLoc (x : Quot (A.E.OrRelLoc hX hF hfT)) : Quot (A'.E.OrRelLoc hX' hF' hfT') :=
  (Equiv.ofBijective _ ((sbe hΨ).orbitOrMapLoc_bijective (D.isScFredholm_pullback hF) hF' hff'
    (D.isTame_B hX) hX' (D.isScFredholmSectionTame_pullback hfT) hfT'))
    ((Equiv.ofBijective _ (D.hΦ.orbitOrMapLoc_bijective (D.isScFredholm_pullback hF) hF rfl
      (D.isTame_B hX) hX (D.isScFredholmSectionTame_pullback hfT) hfT)).symm x)

/-- `|D|_*` computed through any section functor `f₀` on the middle with `f₀ = Φ^* f = Ψ^* f'`. -/
theorem orbitOrMapLoc_eq_mid {f₀ : D.B.Obj → D.B.W} (hF₀ : D.B.E.IsScFredholmSectionFunctor f₀)
    (h₀ : f₀ = D.hΦ.pullback f) (h₀' : f₀ = (sbe hΨ).pullback f')
    (hX₀ : D.B.X.PObj.IsTame) (hfT₀ : D.B.B.IsScFredholmSectionTame f₀)
    (x : Quot (A.E.OrRelLoc hX hF hfT)) :
    D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT' x =
      (Equiv.ofBijective _ ((sbe hΨ).orbitOrMapLoc_bijective hF₀ hF' h₀' hX₀ hX' hfT₀ hfT'))
        ((Equiv.ofBijective _ (D.hΦ.orbitOrMapLoc_bijective hF₀ hF h₀ hX₀ hX hfT₀ hfT)).symm x) :=
            by
  subst h₀
  rfl

theorem orbitOrMapLoc_bijective : Bijective (D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT') :=
  (Equiv.ofBijective _ _).bijective.comp (Equiv.ofBijective _ _).symm.bijective

/-- **`|D|_*` is fibre preserving**: `|σ'| ∘ |D|_* = |d| ∘ |σ|`. -/
theorem orbitProjLoc_orbitOrMapLoc (x : Quot (A.E.OrRelLoc hX hF hfT)) :
    A'.E.orbitProjLoc hX' hF' hfT' (D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT' x) =
      D.smoothOrbitMap hΨ (A.E.orbitProjLoc hX hF hfT x) := by
  set e₁ := Equiv.ofBijective _ (D.hΦ.orbitOrMapLoc_bijective (D.isScFredholm_pullback hF) hF rfl
    (D.isTame_B hX) hX (D.isScFredholmSectionTame_pullback hfT) hfT)
  obtain ⟨c, rfl⟩ := e₁.surjective x
  have h1 : D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT' (e₁ c) =
      (sbe hΨ).orbitOrMapLoc (D.isScFredholm_pullback hF) hF' hff'
        (D.isTame_B hX) hX' (D.isScFredholmSectionTame_pullback hfT) hfT' c := by
    change (Equiv.ofBijective _ _) (e₁.symm (e₁ c)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [h1, EpStrongBundle.IsStrongBundleEquivalence.orbitProjLoc_orbitOrMapLoc]
  change _ = (Equiv.ofBijective _ (sbe hΨ).smoothOrbitMap_bijective)
    ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective).symm
      (A.E.orbitProjLoc hX hF hfT (D.hΦ.orbitOrMapLoc _ hF rfl _ hX _ hfT c)))
  rw [EpStrongBundle.IsStrongBundleEquivalence.orbitProjLoc_orbitOrMapLoc]
  change _ = (Equiv.ofBijective _ (sbe hΨ).smoothOrbitMap_bijective)
    ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective).symm
      ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective) (D.B.E.orbitProjLoc _ _ _ c)))
  rw [Equiv.symm_apply_apply]
  rfl

end Maps

/-! ### Independence of the representative -/

section Indep

variable {D D' : SDiagram A A'} (hΨ : SEP.equivalences D.Ψ) (hΨ' : SEP.equivalences D'.Ψ)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hff'' : D'.hΦ.pullback f = (sbe hΨ').pullback f')
  (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f')

include hff'' in
/-- **Theorem 12.5.7, independence of the representative**, p. 595 (2017: Theorem 12.12), for
Chapter 10's diagrams: equivalent diagrams (`SDiagram.Equiv`, a common refinement) with both
legs strong bundle equivalences induce the same map `|O_f| → |O_{f'}|`. -/
theorem orbitOrMapLoc_eq_of_equiv (h : Equiv D D') :
    D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT' = D'.orbitOrMapLoc hΨ' hF hF' hff'' hX hX' hfT
        hfT' := by
  obtain ⟨C, ⟨H₁, hH₁, hΦ₁, hΨ₁⟩, ⟨H₂, hH₂, hΦ₂, hΨ₂⟩⟩ := h
  obtain ⟨ζ₁⟩ := hΦ₂.trans hΦ₁.symm
  obtain ⟨ζ₂⟩ := hΨ₂.trans hΨ₁.symm
  have k₁ := D.hΦ.comp (sbe hH₁)
  have k₂ := (sbe hΨ).comp (sbe hH₁)
  have hs : IsSection A.P f := hF.2.isScSmooth.1
  have hs' : IsSection A'.P f' := hF'.2.isScSmooth.1
  -- the middle `C` carries `f₃ = (Φ ∘ H₁)^* f`
  have hF₃ : C.B.E.IsScFredholmSectionFunctor (k₁.pullback f) := (theorem_10_4_5_fred k₁).2.1 hF
  have hpbH₁ : k₁.pullback f = (sbe hH₁).pullback (D.hΦ.pullback f) :=
    (proposition_10_4_4 (sbe hH₁) D.hΦ).1 f hs
  have hk₂ : k₁.pullback f = k₂.pullback f' := by
    rw [hpbH₁, (proposition_10_4_4 (sbe hH₁) (sbe hΨ)).1 f' hs', hff']
  have hpbH₂ : k₁.pullback f = (sbe hH₂).pullback (D'.hΦ.pullback f) := by
    rw [← (proposition_10_4_4 (sbe hH₂) D'.hΦ).1 f hs]
    exact proposition_10_4_2 k₁ (D'.hΦ.comp (sbe hH₂)) (hΦ₂.trans hΦ₁.symm).orbitMap_eq.symm hF.1
  funext x
  exact theorem_12_5_7_rep_indep_loc D.hΦ (sbe hΨ) D'.hΦ (sbe hΨ') k₁ k₂ (sbe hH₁) (sbe hH₂)
    (StrongBundleNatTrans.refl (Hom.isStrongBundleFunctor (H₁ ≫ D.Φ)))
    (StrongBundleNatTrans.refl (Hom.isStrongBundleFunctor (H₁ ≫ D.Ψ))) ζ₁ ζ₂ hF hF'
    (D.isScFredholm_pullback hF) (D'.isScFredholm_pullback hF) hF₃ rfl hff' rfl hff''
    hpbH₁ hpbH₂ rfl hk₂ hX hX' (D.isTame_B hX) (D'.isTame_B hX)
        (k₁.isEquivalence_base.isLocalScDiffeo_obj.isTame hX) hfT hfT'
            (D.isScFredholmSectionTame_pullback hfT) (D'.isScFredholmSectionTame_pullback hfT)
                (k₁.isScFredholmSectionTame_pullback hfT) x

end Indep

/-! ### Functoriality -/

section Comp

open WeakFibredProduct

variable (D : SDiagram A A') (E : SDiagram A' A'')

variable {D E} (hΨ : SEP.equivalences D.Ψ) (hΨE : SEP.equivalences E.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} {f'' : A''.Obj → A''.W}
  (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hf'f'' : E.hΦ.pullback f' = (sbe hΨE).pullback f'')

variable (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hF'' : A''.E.IsScFredholmSectionFunctor f'') (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame)
  (hX'' : A''.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f') (hfT'' : A''.B.IsScFredholmSectionTame f'')

/-- **Theorem 12.5.7, functoriality**, p. 595 (2017: Theorem 12.12), for Chapter 10's composite
diagram `D ∘ E` (the weak fibred product `W'' ×_{W'} V''`): `|D ∘ E|_* = |E|_* ∘ |D|_*`. -/
theorem orbitOrMapLoc_comp (x : Quot (A.E.OrRelLoc hX hF hfT)) :
    (D.comp E).orbitOrMapLoc (equivalences_comp_Ψ hΨ hΨE) hF hF''
        (comp_pullback_eq hΨ hΨE hff' hf'f'' hF.1 hF'.1 hF''.2.isScSmooth.1) hX hX'' hfT hfT'' x =
      E.orbitOrMapLoc hΨE hF' hF'' hf'f'' hX' hX'' hfT' hfT'' (D.orbitOrMapLoc hΨ hF hF' hff' hX
          hX' hfT hfT' x) := by
  have p₁ := sbe (equivalences_compLeft D E)
  have p₂ := sbe (equivalences_compRight D E hΨ)
  have hF₁ := D.isScFredholm_pullback hF
  have hF₂ := E.isScFredholm_pullback hF'
  have hF₃ : (compMid D E).E.IsScFredholmSectionFunctor (p₁.pullback (D.hΦ.pullback f)) :=
    (theorem_10_4_5_fred p₁).2.1 hF₁
  have hp₂ : p₁.pullback (D.hΦ.pullback f) = p₂.pullback (E.hΦ.pullback f') :=
    compLeft_pullback_eq hΨ hff' hF'.1
  have hX₁ := D.isTame_B hX
  have hfT₁ := D.isScFredholmSectionTame_pullback hfT
  have hX₂ := E.isTame_B hX'
  have hfT₂ := E.isScFredholmSectionTame_pullback hfT'
  have hX₃ := p₁.isEquivalence_base.isLocalScDiffeo_obj.isTame hX₁
  have hfT₃ := p₁.isScFredholmSectionTame_pullback hfT₁
  obtain ⟨θ⟩ := natEquiv_compLeft_compRight D E
  rw [(D.comp E).orbitOrMapLoc_eq_mid _ hF hF'' _ hX hX'' hfT hfT'' hF₃
    (pullback_comp_of p₁ D.hΦ hF rfl rfl) (pullback_comp_of p₂ (sbe hΨE) hF'' hp₂ hf'f'') hX₃ hfT₃
        x]
  exact theorem_12_5_7_functorial_loc D.hΦ (sbe hΨ) E.hΦ (sbe hΨE) p₁ p₂ θ hF hF' hF'' hF₁ hF₂ hF₃
    rfl hff' rfl hf'f'' rfl hp₂ hX hX' hX'' hX₁ hX₂ hX₃ hfT hfT' hfT'' hfT₁ hfT₂ hfT₃ x

end Comp

/-- **The identity diagram induces the identity** on `|O_f|`. -/
theorem orbitOrMapLoc_id {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)
    (hX : A.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f)
    (x : Quot (A.E.OrRelLoc hX hF hfT)) :
    (SDiagram.id A).orbitOrMapLoc (SEP.equivalences.id_mem A) hF hF rfl hX hX hfT hfT x = x :=
  Equiv.apply_symm_apply _ x

section Mk

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f')

/-- **`|D|_*` on a class over `Φ(v)`**: `|D|_* |(Φ(v), ω)| = |(Ψ(v), (Ψ^*)⁻¹ Φ^* ω)|`. -/
theorem orbitOrMapLoc_mk (v : D.B.Obj) (hv : v ∈ D.B.X.PObj.smoothSet)
    (ω : OrxLoc hfT (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :
    D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT'
        (Quot.mk _ ⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj hv), ω⟩) =
      Quot.mk _ ⟨A'.X.PObj.smoothMk _ ((sbe hΨ).smooth_obj hv),
        ((sbe hΨ).orEqvLoc hff' (D.isScFredholmSectionTame_pullback hfT) hfT' v hv).symm
            (D.hΦ.orEqvLoc rfl (D.isScFredholmSectionTame_pullback hfT) hfT v hv ω)⟩ := by
  have h1 : D.hΦ.orbitOrMapLoc (D.isScFredholm_pullback hF) hF rfl
      (D.isTame_B hX) hX (D.isScFredholmSectionTame_pullback hfT) hfT
      (Quot.mk _ ⟨D.B.X.PObj.smoothMk v hv, D.hΦ.orEqvLoc rfl (D.isScFredholmSectionTame_pullback
          hfT) hfT v hv ω⟩) =
      Quot.mk _ ⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj hv), ω⟩ :=
    congrArg (fun t => Quot.mk (A.E.OrRelLoc hX hF hfT)
      (⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj hv), t⟩ : OrSpaceLoc hX hfT))
      (Equiv.symm_apply_apply (D.hΦ.orEqvLoc rfl (D.isScFredholmSectionTame_pullback hfT) hfT v hv)
          ω)
  rw [← h1]
  unfold SDiagram.orbitOrMapLoc
  exact (congrArg (Equiv.ofBijective _ ((sbe hΨ).orbitOrMapLoc_bijective
    (D.isScFredholm_pullback hF) hF' hff' (D.isTame_B hX) hX' (D.isScFredholmSectionTame_pullback
        hfT) hfT'))
    (Equiv.ofBijective_symm_apply_apply _ (D.hΦ.orbitOrMapLoc_bijective
      (D.isScFredholm_pullback hF) hF rfl (D.isTame_B hX) hX (D.isScFredholmSectionTame_pullback
          hfT) hfT) _)).trans rfl

end Mk

end SDiagram

/-! ### Generalized strong bundle isomorphisms -/

namespace GenSBMap

variable {F : GenSBMap A A'} (hFi : F.IsGeneralizedIso)

variable {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hf' : f' = pushforward hFi f)
  (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f')

/-- **`|f̄|_* : |O_f| → |O_{f'}|`** for a generalized strong bundle isomorphism `f̄` and the
push-forward `f' = f̄_* f` (Theorem 12.5.7), computed with a chosen representative; it is the map
of every representative (`orbitOrMapLoc_eq`). -/
def orbitOrMapLoc (x : Quot (A.E.OrRelLoc hX hF hfT)) : Quot (A'.E.OrRelLoc hX' hF' hfT') :=
  (rep hFi).orbitOrMapLoc (isEquivalence_rep_Ψ hFi) hF hF'
    (pullback_eq_of_cls' hFi (cls_rep hFi) hF.1 hf') hX hX' hfT hfT' x

/-- **Independence of the representative**: `|f̄|_*` is the map `|Ψ|_* ∘ |Φ|_*⁻¹` of every
representative `W ←Φ– V –Ψ→ W'` of `f̄`. -/
theorem orbitOrMapLoc_eq {D : SDiagram A A'} (hD : D.cls = F) :
    orbitOrMapLoc hFi hF hF' hf' hX hX' hfT hfT' =
      D.orbitOrMapLoc (equivalences_Ψ_of_cls hFi hD) hF hF' (pullback_eq_of_cls' hFi hD hF.1 hf')
        hX hX' hfT hfT' :=
  SDiagram.orbitOrMapLoc_eq_of_equiv (isEquivalence_rep_Ψ hFi) (equivalences_Ψ_of_cls hFi hD) hF hF'
    _ _ hX hX' hfT hfT' (SDiagram.cls_eq_cls_iff.1 ((cls_rep hFi).trans hD.symm))

/-- **Theorem 12.5.7 (1) for classes, without the topology**, p. 595 (2017: Theorem 12.12):
`|f̄|_*` and `|f|` are bijections, `|σ'| ∘ |f̄|_* = |f| ∘ |σ|`, and both are the maps of every
representative of `f̄`. -/
theorem theorem_12_5_7_cls_loc :
    Bijective (orbitOrMapLoc hFi hF hF' hf' hX hX' hfT hfT') ∧ Bijective (smoothOrbitMap hFi) ∧
      (∀ x, A'.E.orbitProjLoc hX' hF' hfT' (orbitOrMapLoc hFi hF hF' hf' hX hX' hfT hfT' x) =
        smoothOrbitMap hFi (A.E.orbitProjLoc hX hF hfT x)) ∧
      ∀ (D : SDiagram A A') (hD : D.cls = F),
        orbitOrMapLoc hFi hF hF' hf' hX hX' hfT hfT' =
          D.orbitOrMapLoc (equivalences_Ψ_of_cls hFi hD) hF hF'
            (pullback_eq_of_cls' hFi hD hF.1 hf') hX hX' hfT hfT' ∧
        smoothOrbitMap hFi = D.smoothOrbitMap (equivalences_Ψ_of_cls hFi hD) :=
  ⟨SDiagram.orbitOrMapLoc_bijective (rep hFi) (isEquivalence_rep_Ψ hFi) hF hF' _ hX hX' hfT hfT',
    SDiagram.smoothOrbitMap_bijective (rep hFi) (isEquivalence_rep_Ψ hFi),
    SDiagram.orbitProjLoc_orbitOrMapLoc (rep hFi) (isEquivalence_rep_Ψ hFi) hF hF' _ hX hX' hfT
        hfT',
    fun _ hD =>
      ⟨orbitOrMapLoc_eq hFi hF hF' hf' hX hX' hfT hfT' hD, smoothOrbitMap_eq hFi hD⟩⟩

/-! #### Composition -/

variable {G : GenSBMap A' A''} (hGi : G.IsGeneralizedIso)

/-- **Theorem 12.5.7, functoriality, for classes**, p. 595 (2017: Theorem 12.12):
`|ḡ ∘ f̄|_* = |ḡ|_* ∘ |f̄|_*` for generalized strong bundle isomorphisms `f̄ : W → W'`,
`ḡ : W' → W''` (the composition of `SEP(F⁻¹)`), with `f' = f̄_* f`, `f'' = ḡ_* f'`. -/
theorem theorem_12_5_7_functorial_loc (hFG : (F.comp G).IsGeneralizedIso) {f'' : A''.Obj → A''.W}
    (hF'' : A''.E.IsScFredholmSectionFunctor f'') (hf'' : f'' = pushforward hGi f')
    (hX'' : A''.X.PObj.IsTame) (hfT'' : A''.B.IsScFredholmSectionTame f'') (x : Quot (A.E.OrRelLoc
    hX hF hfT)) :
    orbitOrMapLoc hFG hF hF'' (eq_pushforward_comp hFi hf' hGi hFG hF.1 hf'') hX hX'' hfT hfT'' x =
      orbitOrMapLoc hGi hF' hF'' hf'' hX' hX'' hfT' hfT'' (orbitOrMapLoc hFi hF hF' hf' hX hX' hfT
          hfT' x) := by
  rw [orbitOrMapLoc_eq hFG _ _ _ hX hX'' hfT hfT'' (cls_comp_rep hFi hGi)]
  exact SDiagram.orbitOrMapLoc_comp (isEquivalence_rep_Ψ hFi) (isEquivalence_rep_Ψ hGi)
    (pullback_eq_of_cls' hFi (cls_rep hFi) hF.1 hf')
    (pullback_eq_of_cls' hGi (cls_rep hGi) hF'.1 hf'') hF hF' hF'' hX hX' hX'' hfT hfT' hfT'' x

/-! #### The identity -/

/-- **Theorem 12.5.7, functoriality, the identity**: `|[1_W]|_* = 1` on `|O_f|`. -/
theorem theorem_12_5_7_id_loc (hid : (SDiagram.id A).cls.IsGeneralizedIso) {f : A.Obj → A.W}
    (hF : A.E.IsScFredholmSectionFunctor f) (hX : A.X.PObj.IsTame) (hfT :
    A.B.IsScFredholmSectionTame f)
    (x : Quot (A.E.OrRelLoc hX hF hfT)) :
    orbitOrMapLoc hid hF hF (pushforward_id hid hF.1).symm hX hX hfT hfT x = x := by
  rw [orbitOrMapLoc_eq hid hF hF _ hX hX hfT hfT rfl]
  exact SDiagram.orbitOrMapLoc_id hF hX hfT x


section Corr


include hX hX' in
/-- **Theorem 12.5.7 (2), independence of the representative**, p. 595: let `o`, `o'` be
sections of `σ`, `σ'` invariant under the morphisms.  If `o'` corresponds to `o` over the middle
of one diagram `D` representing `f̄`, then it corresponds to `o` over the middle of every diagram
`D'` representing `f̄`. -/
theorem theorem_12_5_7_two_corr_indep_loc {D D' : SDiagram A A'} (hD : D.cls = F) (hD' : D'.cls = F)
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), OrxLoc hfT a hs}
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), OrxLoc hfT' x hs}
    (ho : ∀ (φ : A.Mor) {x x' : A.Obj} (hx : A.X.src φ = x) (hx' : A.X.tgt φ = x')
      (hs : x ∈ A.X.PObj.smoothSet) (hs' : x' ∈ A.X.PObj.smoothSet),
      A.E.orMorLoc hF hfT φ hx hx' hs hs' (o x hs) = o x' hs')
    (ho' : ∀ (φ : A'.Mor) {x x' : A'.Obj} (hx : A'.X.src φ = x) (hx' : A'.X.tgt φ = x')
      (hs : x ∈ A'.X.PObj.smoothSet) (hs' : x' ∈ A'.X.PObj.smoothSet),
      A'.E.orMorLoc hF' hfT' φ hx hx' hs hs' (o' x hs) = o' x' hs')
    (hcorr : ∀ v (hv : v ∈ D.B.X.PObj.smoothSet),
      (sbe (equivalences_Ψ_of_cls hFi hD)).orEqvLoc (pullback_eq_of_cls' hFi hD hF.1 hf')
          (D.isScFredholmSectionTame_pullback hfT) hfT' v hv
          (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD)).smooth_obj hv)) =
        D.hΦ.orEqvLoc rfl (D.isScFredholmSectionTame_pullback hfT) hfT v hv (o (D.Φ.ϕ.obj v)
            (D.hΦ.smooth_obj hv)))
    (v : D'.B.Obj) (hv : v ∈ D'.B.X.PObj.smoothSet) :
    (sbe (equivalences_Ψ_of_cls hFi hD')).orEqvLoc (pullback_eq_of_cls' hFi hD' hF.1 hf')
        (D'.isScFredholmSectionTame_pullback hfT) hfT' v hv
        (o' (D'.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD')).smooth_obj hv)) =
      D'.hΦ.orEqvLoc rfl (D'.isScFredholmSectionTame_pullback hfT) hfT v hv (o (D'.Φ.ϕ.obj v)
          (D'.hΦ.smooth_obj hv)) := by
  have hs := D'.hΦ.smooth_obj hv
  obtain ⟨a, ha, ψ, h1, h2⟩ := D.hΦ.exists_smooth_iso hs
  -- the classes of `(Φ(a), o)` and `(Φ'(v), o)` agree
  have hcls : (Quot.mk (A.E.OrRelLoc hX hF hfT)
      ⟨A.X.PObj.smoothMk _ (D.hΦ.smooth_obj ha), o _ (D.hΦ.smooth_obj ha)⟩) =
      Quot.mk _ ⟨A.X.PObj.smoothMk _ hs, o _ hs⟩ :=
    Quot.sound ⟨ψ, h1, h2, ho ψ h1 h2 _ _⟩
  have e₁ := D.orbitOrMapLoc_mk (equivalences_Ψ_of_cls hFi hD) hF hF'
    (pullback_eq_of_cls' hFi hD hF.1 hf') hX hX' hfT hfT' a ha (o _ (D.hΦ.smooth_obj ha))
  have e₂ := D'.orbitOrMapLoc_mk (equivalences_Ψ_of_cls hFi hD') hF hF'
    (pullback_eq_of_cls' hFi hD' hF.1 hf') hX hX' hfT hfT' v hv (o _ hs)
  have k₁ := orbitOrMapLoc_eq hFi hF hF' hf' hX hX' hfT hfT' hD
  have k₂ := orbitOrMapLoc_eq hFi hF hF' hf' hX hX' hfT hfT' hD'
  have e₃ := e₁.symm.trans ((congrFun k₁ _).symm.trans
    ((congrArg _ hcls).trans ((congrFun k₂ _).trans e₂)))
  obtain ⟨β, hb, hb', hβ⟩ := A'.E.orRelLoc_of_quot_eq hX' hF' hfT' e₃
  have h5 := (Equiv.symm_apply_eq _).2 (hcorr a ha).symm
  have h3 := ho' β hb hb' (A'.X.PObj.smoothVal_mem _) (A'.X.PObj.smoothVal_mem _)
  exact (Equiv.eq_symm_apply _).1 (h3.symm.trans ((congrArg _ h5.symm).trans hβ))

end Corr

/-! #### Theorem 12.5.7 with the topology, for classes -/

section TameGerm

include hF hf' hfT in
/-- **Tame germ data pass to `f' = f̄_* f`** (Definition 3.6.4): `f̄_* f = Ψ_* Φ^* f` for the
chosen representative, and `Φ^*`, `Ψ_*` keep tame germ data (Theorem 10.4.5). -/
theorem isScFredholmSectionTame_of_eq_pushforward : A'.B.IsScFredholmSectionTame f' := by
  have hF'' : (rep hFi).B.E.IsScFredholmSectionFunctor ((rep hFi).hΦ.pullback f) :=
    (EpStrongBundle.theorem_10_4_5_fred (rep hFi).hΦ).2.1 hF
  exact hf' ▸ (sbe (isEquivalence_rep_Ψ hFi)).isScFredholmSectionTame_pushforward hF''.1
    ((rep hFi).hΦ.isScFredholmSectionTame_pullback hfT)

end TameGerm

section Topology

variable {F : GenSBMap A A'} (hFi : F.IsGeneralizedIso) {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
  (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hf' : f' = pushforward hFi f) (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame)
  (hfT : A.B.IsScFredholmSectionTame f) (hfT' : A'.B.IsScFredholmSectionTame f')

/-- **Theorem 12.5.7 (1) for a generalized strong bundle isomorphism**, p. 595, with the
topology, for the local orientation sets: for tame object M-polyfolds of `W`, `W'` and tame
germ data of `f`, `f' = f̄_* f`, there are homeomorphisms `|O_f| ≃ₜ |O_{f'}|` and
`|X_∞| ≃ₜ |X'_∞|` with `|σ'| ∘ F = G ∘ |σ|`, and they are `|f̄|_*` and `|f|`
(`GenSBMap.orbitOrMapLoc`, `GenSBMap.smoothOrbitMap`, the maps of every representative).  The
tame germ data of `f'` are those inherited from `f`
(`isScFredholmSectionTame_of_eq_pushforward`). -/
theorem theorem_12_5_7_one_loc_cls :
    letI : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
    letI : TopologicalSpace (OrSpaceLoc hX'
        (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT)) :=
      orTopologyLoc hX' (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT)
    ∃ (Fh : Quot (A.E.OrRelLoc hX hF hfT) ≃ₜ Quot (A'.E.OrRelLoc hX' hF'
        (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT)))
      (G : Quot A.X.SmoothRel ≃ₜ Quot A'.X.SmoothRel),
      (∀ c, A'.E.orbitProjLoc hX' hF'
          (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT) (Fh c) =
        G (A.E.orbitProjLoc hX hF hfT c)) ∧
      ⇑Fh = orbitOrMapLoc hFi hF hF' hf' hX hX' hfT
        (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT) ∧
      ⇑G = smoothOrbitMap hFi := by
  have hfT' := isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT
  have hΨ := isEquivalence_rep_Ψ hFi
  have hff' := pullback_eq_of_cls' hFi (cls_rep hFi) hF.1 hf'
  obtain ⟨Fh, G, h1, h2, h3⟩ := theorem_12_5_7_one_loc (rep hFi).hΦ (sbe hΨ) hF hF'
    ((rep hFi).isScFredholm_pullback hF) rfl hff' hX hX' ((rep hFi).isTame_B hX) hfT hfT'
    ((rep hFi).isScFredholmSectionTame_pullback hfT)
  refine ⟨Fh, G, h1, funext fun x => ?_, funext fun v => ?_⟩
  · have hb := (rep hFi).hΦ.orbitOrMapLoc_bijective ((rep hFi).isScFredholm_pullback hF) hF rfl
      ((rep hFi).isTame_B hX) hX ((rep hFi).isScFredholmSectionTame_pullback hfT) hfT
    conv_lhs => rw [← (Equiv.ofBijective _ hb).apply_symm_apply x]
    rw [Equiv.ofBijective_apply, h2]
    rfl
  · have hb := (rep hFi).hΦ.smoothOrbitMap_bijective
    conv_lhs => rw [← (Equiv.ofBijective _ hb).apply_symm_apply v]
    rw [Equiv.ofBijective_apply, h3]
    rfl

/-- **Theorem 12.5.7 (2) for a generalized strong bundle isomorphism**, p. 595, for the local
orientation sets and any representative `W ←Φ– V –Ψ→ W'` of `f̄`: for tame object M-polyfolds
of `W`, `W'` and tame germ data of `f`, `f' = f̄_* f`, an orientation `o` of `f` in the sense
of Definition 12.5.4 has exactly one orientation `o'` of `f'` (Definition 12.5.4)
corresponding to `o` over `V`. -/
theorem theorem_12_5_7_two_loc_cls {D : SDiagram A A'} (hD : D.cls = F)
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : A.E.definition_12_5_4_loc hX hF hfT o) :
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), OrxLoc hfT' x hs,
      A'.E.definition_12_5_4_loc hX' hF' hfT' o' ∧
        ∀ v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (equivalences_Ψ_of_cls hFi hD)).orEqvLoc (pullback_eq_of_cls' hFi hD hF.1 hf')
              (D.isScFredholmSectionTame_pullback hfT) hfT' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD)).smooth_obj hv)) =
            D.hΦ.orEqvLoc rfl (D.isScFredholmSectionTame_pullback hfT) hfT v hv
              (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  theorem_12_5_7_two_loc D.hΦ (sbe (equivalences_Ψ_of_cls hFi hD)) hF hF'
    (D.isScFredholm_pullback hF) rfl (pullback_eq_of_cls' hFi hD hF.1 hf') hX hX'
    (D.isTame_B hX) hfT hfT' (D.isScFredholmSectionTame_pullback hfT) ho

/-- **Theorem 12.5.7 (2) for the class**, p. 595, for the local orientation sets: for tame
object M-polyfolds of `W`, `W'` and tame germ data of `f`, `f' = f̄_* f`, an orientation `o` of
`f` (Definition 12.5.4) has exactly one orientation `o'` of `f'` which corresponds to `o` over
the middle of every diagram representing `f̄`.  The tame germ data of `f'` are those inherited
from `f` (`isScFredholmSectionTame_of_eq_pushforward`). -/
theorem theorem_12_5_7_two_loc_cls_unique
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : A.E.definition_12_5_4_loc hX hF hfT o) :
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet),
        OrxLoc (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT) x hs,
      A'.E.definition_12_5_4_loc hX' hF'
          (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT) o' ∧
        ∀ (D : SDiagram A A') (hD : D.cls = F) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (equivalences_Ψ_of_cls hFi hD)).orEqvLoc (pullback_eq_of_cls' hFi hD hF.1 hf')
              (D.isScFredholmSectionTame_pullback hfT)
              (isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT) v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD)).smooth_obj hv)) =
            D.hΦ.orEqvLoc rfl (D.isScFredholmSectionTame_pullback hfT) hfT v hv
              (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  have hfT' := isScFredholmSectionTame_of_eq_pushforward hFi hF hf' hfT
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := theorem_12_5_7_two_loc_cls hFi hF hF' hf' hX hX' hfT hfT'
    (cls_rep hFi) ho
  refine ⟨o', ⟨ho', fun D hD v hv => ?_⟩, fun o'' ⟨ho'', hc''⟩ =>
    huniq o'' ⟨ho'', hc'' (rep hFi) (cls_rep hFi)⟩⟩
  exact theorem_12_5_7_two_corr_indep_loc hFi hF hF' hf' hX hX' hfT hfT' (cls_rep hFi) hD ho.2
    ho'.2 hc v hv

end Topology

end GenSBMap

end SBLocalization

end Polyfold
