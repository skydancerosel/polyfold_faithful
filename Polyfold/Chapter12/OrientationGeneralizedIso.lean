import Polyfold.Chapter12.OrientationRepresentativeIndep
import Polyfold.Chapter10.StrongBundleLocalizationCategory
import Polyfold.Chapter10.StrongBundleIsoConverse
import Polyfold.Chapter10.FredholmEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12) for Chapter 10's objects: the map
`|f̄|_* : |O_f| → |O_{f'}|` of a generalized strong bundle isomorphism `f̄ : W → W'`
(Definition 10.5.2, a class `GenSBMap A A'` of diagrams `SDiagram A A'`), `f'` the push-forward
of `f` (Theorem 10.5.4).

## The text, paraphrased

A representative `W ←Φ– V –Φ'→ W'` of `f̄` consists of strong bundle equivalences; the pull-back
`f''` of `f` to `V` is the pull-back of `f'`, and `|f̄|_*` is the composite of the bijections
`|O_f| ← |O_{f''}| → |O_{f'}|`.  Different representatives give the same map, and the
construction is functorial.

## What is formalized

* `IsStrongBundleEquivalence.hasScPlusSectionsThrough`: sc⁺-sections through the smooth fibre
  points pass from `W'` to `W` along a strong bundle equivalence `W → W'` (pull-back,
  `isScPlusSection_pullback`).  So the standing hypothesis `hsec` of §12.5 is needed only on the
  two ends of a diagram, not on its middle.
* For a diagram `D` with both legs strong bundle equivalences and section functors with
  `Φ^* f = Ψ^* f'`: `SDiagram.orbitOrMap` (`|Ψ|_* ∘ |Φ|_*⁻¹`), `SDiagram.smoothOrbitMap`
  (`|ψ| ∘ |φ|⁻¹` on `|X_∞|`), bijective, with `|σ'| ∘ |D|_* = |d| ∘ |σ|`
  (`orbitProj_orbitOrMap`).
* **Independence of the representative**: `SDiagram.orbitOrMap_eq_of_equiv`,
  `smoothOrbitMap_eq_of_equiv` (Chapter 10's `SDiagram.Equiv`, through the common refinement
  `W ←Φ∘H– V'' –Ψ∘H→ W'`, both legs equivalences, and `theorem_12_5_7_rep_indep`).
* **Functoriality**: `SDiagram.equivalences_compRight` (the leg `compRight` of Chapter 10's
  composite is a strong bundle equivalence when `D.Ψ` is one),
  `SDiagram.compLeft_pullback_eq` (the two pull-backs to the middle of the composite agree),
  `SDiagram.orbitOrMap_comp`, `smoothOrbitMap_comp` (through `theorem_12_5_7_functorial`), and
  `SDiagram.orbitOrMap_id`.
* On classes: `GenSBMap.orbitOrMap`, `GenSBMap.smoothOrbitMap` for `f' = f̄_* f`, equal to the
  map of every representative (`orbitOrMap_eq`, `smoothOrbitMap_eq`), bijective and fibre
  preserving; `GenSBMap.isGeneralizedIso_comp`, `pushforward_comp` (`(ḡ ∘ f̄)_* = ḡ_* ∘ f̄_*` on
  `Fred`), and **`GenSBMap.theorem_12_5_7_functorial`**: `|ḡ ∘ f̄|_* = |ḡ|_* ∘ |f̄|_*`;
  `GenSBMap.theorem_12_5_7_cls` collects the statements.

The homeomorphism of (1) and the continuity in (2) for classes, with Part I's hypotheses on the
two ends only, are in `OrientationGeneralizedIsoTopology` (`GenSBMap.theorem_12_5_7_one_homeo_cls`,
`GenSBMap.theorem_12_5_7_two_cls`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

open StrongRetr

universe u

/-! ### Sc⁺-sections through smooth points along a strong bundle equivalence -/

section Transfer

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

include h in
/-- **Sc⁺-sections through smooth fibre points pass to the source of a strong bundle
equivalence** `Φ : W → W'`: for smooth `x` and smooth `e ∈ W_x`, an sc⁺-section `t` of `W'` with
`t(ϕ(x)) = Φ(e)` pulls back to an sc⁺-section `Φ^* t` with `(Φ^* t)(x) = e`. -/
theorem hasScPlusSectionsThrough (hsec' : B'.HasScPlusSectionsThrough) :
    B.HasScPlusSectionsThrough := by
  intro x hx e he hex
  obtain ⟨t, ht, htx⟩ := hsec' (ϕ.obj x) (h.smooth_obj hx) (Φ.obj e)
    ((h.isLocalScDiffeo_obj.mem_smoothSet_iff e).2 he) (by rw [h.covers, hex])
  exact ⟨h.pullback t, h.isScPlusSection_pullback ht, h.pullback_eq ht.1 hex htx.symm⟩

end EpStrongBundle.IsStrongBundleEquivalence

end Transfer

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' A'' : SEP.{u}}

namespace SDiagram

/-! ### The maps of one diagram -/

/-- The middle of a diagram has sc⁺-sections through its smooth fibre points if the source has. -/
theorem hasScPlusSectionsThrough_B (D : SDiagram A A') (hsec : A.B.HasScPlusSectionsThrough) :
    D.B.B.HasScPlusSectionsThrough :=
  D.hΦ.hasScPlusSectionsThrough hsec

/-- The pull-back `f'' = Φ^* f` of an sc-Fredholm section functor to the middle (Theorem 10.4.5). -/
theorem isScFredholm_pullback (D : SDiagram A A') {f : A.Obj → A.W}
    (hF : A.E.IsScFredholmSectionFunctor f) :
    D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback f) :=
  (theorem_10_4_5_fred D.hΦ).2.1 hF

/-- `f'' = Φ^* f = Ψ^* f'` when `f' = [D]_* f = Ψ_* Φ^* f` (the text's choice of `f'`). -/
theorem pullback_eq_pullback_pushforward (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {f : A.Obj → A.W} (hf : f ∈ A.E.sectionFunctors) :
    D.hΦ.pullback f = (sbe hΨ).pullback (D.pushforward hΨ f) := by
  obtain ⟨hs, hfun⟩ := (theorem_10_4_5 D.hΦ).1.2.1 hf
  exact ((sbe hΨ).pullback_pushforward hs.1 hfun).symm

section Maps

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

/-- **`|D|_* = |Ψ|_* ∘ |Φ|_*⁻¹ : |O_f| → |O_{f'}|`** (proof of Theorem 12.5.7), for a diagram
with both legs strong bundle equivalences and `Φ^* f = Ψ^* f'`. -/
def orbitOrMap (x : Quot (A.E.OrRel hF hsec)) : Quot (A'.E.OrRel hF' hsec') :=
  (Equiv.ofBijective _ ((sbe hΨ).orbitOrMap_bijective (D.isScFredholm_pullback hF) hF' hff'
    (D.hasScPlusSectionsThrough_B hsec) hsec'))
    ((Equiv.ofBijective _ (D.hΦ.orbitOrMap_bijective (D.isScFredholm_pullback hF) hF rfl
      (D.hasScPlusSectionsThrough_B hsec) hsec)).symm x)

/-- **`|d| = |ψ| ∘ |φ|⁻¹ : |X_∞| → |X'_∞|`**. -/
def smoothOrbitMap (x : Quot A.X.SmoothRel) : Quot A'.X.SmoothRel :=
  (Equiv.ofBijective _ (sbe hΨ).smoothOrbitMap_bijective)
    ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective).symm x)

/-- `|D|_*` computed through any section functor `f₀` on the middle with `f₀ = Φ^* f = Ψ^* f'`. -/
theorem orbitOrMap_eq_mid {f₀ : D.B.Obj → D.B.W} (hF₀ : D.B.E.IsScFredholmSectionFunctor f₀)
    (h₀ : f₀ = D.hΦ.pullback f) (h₀' : f₀ = (sbe hΨ).pullback f')
    (hsec₀ : D.B.B.HasScPlusSectionsThrough) (x : Quot (A.E.OrRel hF hsec)) :
    D.orbitOrMap hΨ hF hF' hff' hsec hsec' x =
      (Equiv.ofBijective _ ((sbe hΨ).orbitOrMap_bijective hF₀ hF' h₀' hsec₀ hsec'))
        ((Equiv.ofBijective _ (D.hΦ.orbitOrMap_bijective hF₀ hF h₀ hsec₀ hsec)).symm x) := by
  subst h₀
  rfl

theorem orbitOrMap_bijective : Bijective (D.orbitOrMap hΨ hF hF' hff' hsec hsec') :=
  (Equiv.ofBijective _ _).bijective.comp (Equiv.ofBijective _ _).symm.bijective

theorem smoothOrbitMap_bijective : Bijective (D.smoothOrbitMap hΨ) :=
  (Equiv.ofBijective _ _).bijective.comp (Equiv.ofBijective _ _).symm.bijective

/-- **`|D|_*` is fibre preserving**: `|σ'| ∘ |D|_* = |d| ∘ |σ|`. -/
theorem orbitProj_orbitOrMap (x : Quot (A.E.OrRel hF hsec)) :
    A'.E.orbitProj hF' hsec' (D.orbitOrMap hΨ hF hF' hff' hsec hsec' x) =
      D.smoothOrbitMap hΨ (A.E.orbitProj hF hsec x) := by
  set e₁ := Equiv.ofBijective _ (D.hΦ.orbitOrMap_bijective (D.isScFredholm_pullback hF) hF rfl
    (D.hasScPlusSectionsThrough_B hsec) hsec)
  obtain ⟨c, rfl⟩ := e₁.surjective x
  have h1 : D.orbitOrMap hΨ hF hF' hff' hsec hsec' (e₁ c) =
      (sbe hΨ).orbitOrMap (D.isScFredholm_pullback hF) hF' hff'
        (D.hasScPlusSectionsThrough_B hsec) hsec' c := by
    change (Equiv.ofBijective _ _) (e₁.symm (e₁ c)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [h1, EpStrongBundle.IsStrongBundleEquivalence.orbitProj_orbitOrMap]
  change _ = (Equiv.ofBijective _ (sbe hΨ).smoothOrbitMap_bijective)
    ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective).symm
      (A.E.orbitProj hF hsec (D.hΦ.orbitOrMap _ hF rfl _ hsec c)))
  rw [EpStrongBundle.IsStrongBundleEquivalence.orbitProj_orbitOrMap]
  change _ = (Equiv.ofBijective _ (sbe hΨ).smoothOrbitMap_bijective)
    ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective).symm
      ((Equiv.ofBijective _ D.hΦ.smoothOrbitMap_bijective) (D.B.E.orbitProj _ _ c)))
  rw [Equiv.symm_apply_apply]
  rfl

end Maps

/-! ### Independence of the representative -/

section Indep

variable {D D' : SDiagram A A'} (hΨ : SEP.equivalences D.Ψ) (hΨ' : SEP.equivalences D'.Ψ)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hff'' : D'.hΦ.pullback f = (sbe hΨ').pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

include hff'' in
/-- **Theorem 12.5.7, independence of the representative**, p. 595 (2017: Theorem 12.12), for
Chapter 10's diagrams: equivalent diagrams (`SDiagram.Equiv`, a common refinement) with both
legs strong bundle equivalences induce the same map `|O_f| → |O_{f'}|`. -/
theorem orbitOrMap_eq_of_equiv (h : Equiv D D') :
    D.orbitOrMap hΨ hF hF' hff' hsec hsec' = D'.orbitOrMap hΨ' hF hF' hff'' hsec hsec' := by
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
  exact theorem_12_5_7_rep_indep D.hΦ (sbe hΨ) D'.hΦ (sbe hΨ') k₁ k₂ (sbe hH₁) (sbe hH₂)
    (StrongBundleNatTrans.refl (Hom.isStrongBundleFunctor (H₁ ≫ D.Φ)))
    (StrongBundleNatTrans.refl (Hom.isStrongBundleFunctor (H₁ ≫ D.Ψ))) ζ₁ ζ₂ hF hF'
    (D.isScFredholm_pullback hF) (D'.isScFredholm_pullback hF) hF₃ rfl hff' rfl hff''
    hpbH₁ hpbH₂ rfl hk₂ hsec hsec' (D.hasScPlusSectionsThrough_B hsec)
    (D'.hasScPlusSectionsThrough_B hsec) (k₁.hasScPlusSectionsThrough hsec) x

/-- The base form of `orbitOrMap_eq_of_equiv`: equivalent diagrams induce the same map
`|X_∞| → |X'_∞|`. -/
theorem smoothOrbitMap_eq_of_equiv (h : Equiv D D') :
    D.smoothOrbitMap hΨ = D'.smoothOrbitMap hΨ' := by
  obtain ⟨C, ⟨H₁, hH₁, hΦ₁, hΨ₁⟩, ⟨H₂, hH₂, hΦ₂, hΨ₂⟩⟩ := h
  obtain ⟨ζ₁⟩ := hΦ₂.trans hΦ₁.symm
  obtain ⟨ζ₂⟩ := hΨ₂.trans hΨ₁.symm
  funext x
  exact theorem_12_5_7_rep_indep_base D.hΦ (sbe hΨ) D'.hΦ (sbe hΨ') (D.hΦ.comp (sbe hH₁))
    ((sbe hΨ).comp (sbe hH₁)) (sbe hH₁) (sbe hH₂)
    (StrongBundleNatTrans.refl (Hom.isStrongBundleFunctor (H₁ ≫ D.Φ)))
    (StrongBundleNatTrans.refl (Hom.isStrongBundleFunctor (H₁ ≫ D.Ψ))) ζ₁ ζ₂ x

end Indep

/-! ### Functoriality -/

section Comp

open WeakFibredProduct

variable (D : SDiagram A A') (E : SDiagram A' A'')

/-- The square of Chapter 10's composite: `D.Ψ ∘ compLeft ≃ E.Φ ∘ compRight` (Definition 10.4.8). -/
theorem natEquiv_compLeft_compRight :
    SEP.NatEquiv (compLeft D E ≫ D.Ψ) (compRight D E ≫ E.Φ) :=
  natEquiv_cone E.hΦ D.Ψ (Y := compBase D E) _ _ _

/-- **The leg `W'' ×_{W'} V'' → V''` of Chapter 10's composite is a strong bundle equivalence when
`D.Ψ` is one**: `E.Φ ∘ compRight ≃ D.Ψ ∘ compLeft` is injective on the fibres and covers an
equivalence, hence is a strong bundle equivalence (`equivalences_of_natEquiv_comp`), and two out
of three. -/
theorem equivalences_compRight (hΨ : SEP.equivalences D.Ψ) : SEP.equivalences (compRight D E) := by
  have hK : SEP.equivalences (compLeft D E ≫ D.Ψ) :=
    SEP.equivalences.comp_mem _ _ (equivalences_compLeft D E) hΨ
  have hnat := natEquiv_compLeft_compRight D E
  have hψ : (Hom.ϕ (compRight D E ≫ E.Φ)).IsEquivalence :=
    E.hΦ.isEquivalence_base.comp (isEquivalence_projRight (sbe hΨ).isEquivalence_base
      (D.admissible E))
  have hinj : FibInj (compRight D E ≫ E.Φ) := FibInj.of_natEquiv hnat (fibInj_of_equivalences hK)
  have h := SEP.equivalences_of_natEquiv_comp (compRight D E ≫ E.Φ) hψ hinj (𝟙 _) _ hK
    (by rw [Category.id_comp]; exact hnat)
  exact SEP.equivalences.of_comp_left E.isEquivalence_Φ h

/-- The composite of two diagrams with both legs strong bundle equivalences has both legs
strong bundle equivalences. -/
theorem equivalences_comp_Ψ {D : SDiagram A A'} {E : SDiagram A' A''} (hΨ : SEP.equivalences D.Ψ)
    (hΨE : SEP.equivalences E.Ψ) : SEP.equivalences (D.comp E).Ψ :=
  SEP.equivalences.comp_mem _ _ (equivalences_compRight D E hΨ) hΨE

variable {D E} (hΨ : SEP.equivalences D.Ψ) (hΨE : SEP.equivalences E.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} {f'' : A''.Obj → A''.W}
  (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hf'f'' : E.hΦ.pullback f' = (sbe hΨE).pullback f'')

include hff' in
/-- **The two pull-backs to the middle of the composite agree**:
`compLeft^* (Φ^* f) = compRight^* (Φ'^* f')` (Propositions 10.4.2 and 10.4.4). -/
theorem compLeft_pullback_eq (hf' : f' ∈ A'.E.sectionFunctors) :
    (sbe (equivalences_compLeft D E)).pullback (D.hΦ.pullback f) =
      (sbe (equivalences_compRight D E hΨ)).pullback (E.hΦ.pullback f') := by
  have hs' : IsSection A'.P f' := hf'.1.1
  rw [hff', ← (proposition_10_4_4 (sbe (equivalences_compLeft D E)) (sbe hΨ)).1 f' hs',
    ← (proposition_10_4_4 (sbe (equivalences_compRight D E hΨ)) E.hΦ).1 f' hs']
  exact proposition_10_4_2 _ _ (natEquiv_compLeft_compRight D E).orbitMap_eq hf'

include hff' hf'f'' in
/-- `Φ_c^* f = Ψ_c^* f''` for the composite `D ∘ E`. -/
theorem comp_pullback_eq (hf : f ∈ A.E.sectionFunctors) (hf' : f' ∈ A'.E.sectionFunctors)
    (hs'' : IsSection A''.P f'') :
    (D.comp E).hΦ.pullback f = (sbe (equivalences_comp_Ψ hΨ hΨE)).pullback f'' := by
  have e₁ : (D.comp E).hΦ.pullback f =
      (sbe (equivalences_compLeft D E)).pullback (D.hΦ.pullback f) :=
    (proposition_10_4_4 (sbe (equivalences_compLeft D E)) D.hΦ).1 f hf.1.1
  rw [e₁, compLeft_pullback_eq hΨ hff' hf', hf'f'']
  exact ((proposition_10_4_4 (sbe (equivalences_compRight D E hΨ)) (sbe hΨE)).1 f'' hs'').symm

variable (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hF'' : A''.E.IsScFredholmSectionFunctor f'') (hsec : A.B.HasScPlusSectionsThrough)
  (hsec' : A'.B.HasScPlusSectionsThrough) (hsec'' : A''.B.HasScPlusSectionsThrough)

/-- **Theorem 12.5.7, functoriality**, p. 595 (2017: Theorem 12.12), for Chapter 10's composite
diagram `D ∘ E` (the weak fibred product `W'' ×_{W'} V''`): `|D ∘ E|_* = |E|_* ∘ |D|_*`. -/
theorem orbitOrMap_comp (x : Quot (A.E.OrRel hF hsec)) :
    (D.comp E).orbitOrMap (equivalences_comp_Ψ hΨ hΨE) hF hF''
        (comp_pullback_eq hΨ hΨE hff' hf'f'' hF.1 hF'.1 hF''.2.isScSmooth.1) hsec hsec'' x =
      E.orbitOrMap hΨE hF' hF'' hf'f'' hsec' hsec'' (D.orbitOrMap hΨ hF hF' hff' hsec hsec' x) := by
  have p₁ := sbe (equivalences_compLeft D E)
  have p₂ := sbe (equivalences_compRight D E hΨ)
  have hF₁ := D.isScFredholm_pullback hF
  have hF₂ := E.isScFredholm_pullback hF'
  have hF₃ : (compMid D E).E.IsScFredholmSectionFunctor (p₁.pullback (D.hΦ.pullback f)) :=
    (theorem_10_4_5_fred p₁).2.1 hF₁
  have hp₂ : p₁.pullback (D.hΦ.pullback f) = p₂.pullback (E.hΦ.pullback f') :=
    compLeft_pullback_eq hΨ hff' hF'.1
  have hsec₁ := D.hasScPlusSectionsThrough_B hsec
  have hsec₂ := E.hasScPlusSectionsThrough_B hsec'
  have hsec₃ := p₁.hasScPlusSectionsThrough hsec₁
  obtain ⟨θ⟩ := natEquiv_compLeft_compRight D E
  rw [(D.comp E).orbitOrMap_eq_mid _ hF hF'' _ hsec hsec'' hF₃
    (pullback_comp_of p₁ D.hΦ hF rfl rfl) (pullback_comp_of p₂ (sbe hΨE) hF'' hp₂ hf'f'') hsec₃ x]
  exact theorem_12_5_7_functorial D.hΦ (sbe hΨ) E.hΦ (sbe hΨE) p₁ p₂ θ hF hF' hF'' hF₁ hF₂ hF₃
    rfl hff' rfl hf'f'' rfl hp₂ hsec hsec' hsec'' hsec₁ hsec₂ hsec₃ x

omit hΨ hΨE in
/-- The base form of `orbitOrMap_comp` on `|X_∞|`. -/
theorem smoothOrbitMap_comp (hΨ : SEP.equivalences D.Ψ) (hΨE : SEP.equivalences E.Ψ)
    (x : Quot A.X.SmoothRel) :
    (D.comp E).smoothOrbitMap (equivalences_comp_Ψ hΨ hΨE) x =
      E.smoothOrbitMap hΨE (D.smoothOrbitMap hΨ x) := by
  obtain ⟨θ⟩ := natEquiv_compLeft_compRight D E
  exact theorem_12_5_7_functorial_base D.hΦ (sbe hΨ) E.hΦ (sbe hΨE)
    (sbe (equivalences_compLeft D E)) (sbe (equivalences_compRight D E hΨ)) θ x

end Comp

/-- **The identity diagram induces the identity** on `|O_f|`. -/
theorem orbitOrMap_id {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)
    (hsec : A.B.HasScPlusSectionsThrough) (x : Quot (A.E.OrRel hF hsec)) :
    (SDiagram.id A).orbitOrMap (SEP.equivalences.id_mem A) hF hF rfl hsec hsec x = x :=
  Equiv.apply_symm_apply _ x

theorem smoothOrbitMap_id (x : Quot A.X.SmoothRel) :
    (SDiagram.id A).smoothOrbitMap (SEP.equivalences.id_mem A) x = x :=
  Equiv.apply_symm_apply _ x

end SDiagram

/-! ### Generalized strong bundle isomorphisms -/

namespace GenSBMap

variable {F : GenSBMap A A'} (hFi : F.IsGeneralizedIso)

include hFi in
/-- Every representative of a generalized strong bundle isomorphism has both legs strong bundle
equivalences (`SEPLoc.isIso_iff_isGeneralizedIso`). -/
theorem equivalences_Ψ_of_cls {D : SDiagram A A'} (hD : D.cls = F) : SEP.equivalences D.Ψ := by
  have h := SEPLoc.isIso_of_isGeneralizedIso hFi
  rw [← hD] at h
  exact SEPLoc.equivalences_Ψ_of_isIso D h

/-- For `f' = f̄_* f`, the pull-backs of `f` and `f'` to the middle of any representative agree. -/
theorem pullback_eq_of_cls {D : SDiagram A A'} (hD : D.cls = F) (hΨ : SEP.equivalences D.Ψ)
    {f : A.Obj → A.W} (hf : f ∈ A.E.sectionFunctors) :
    D.hΦ.pullback f = (sbe hΨ).pullback (pushforward hFi f) := by
  rw [pushforward_eq hFi hD hΨ hf]
  exact D.pullback_eq_pullback_pushforward hΨ hf

/-- The same with `f' = f̄_* f` given as an equation. -/
theorem pullback_eq_of_cls' {D : SDiagram A A'} (hD : D.cls = F) {f : A.Obj → A.W}
    {f' : A'.Obj → A'.W} (hf : f ∈ A.E.sectionFunctors) (hf' : f' = pushforward hFi f) :
    D.hΦ.pullback f = (sbe (equivalences_Ψ_of_cls hFi hD)).pullback f' := by
  subst hf'
  exact pullback_eq_of_cls hFi hD (equivalences_Ψ_of_cls hFi hD) hf

variable {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hf' : f' = pushforward hFi f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

/-- **`|f̄|_* : |O_f| → |O_{f'}|`** for a generalized strong bundle isomorphism `f̄` and the
push-forward `f' = f̄_* f` (Theorem 12.5.7), computed with a chosen representative; it is the map
of every representative (`orbitOrMap_eq`). -/
def orbitOrMap (x : Quot (A.E.OrRel hF hsec)) : Quot (A'.E.OrRel hF' hsec') :=
  (rep hFi).orbitOrMap (isEquivalence_rep_Ψ hFi) hF hF'
    (pullback_eq_of_cls' hFi (cls_rep hFi) hF.1 hf') hsec hsec' x

/-- **`|f| : |X_∞| → |X'_∞|`** of the covered generalized isomorphism. -/
def smoothOrbitMap (x : Quot A.X.SmoothRel) : Quot A'.X.SmoothRel :=
  (rep hFi).smoothOrbitMap (isEquivalence_rep_Ψ hFi) x

/-- **Independence of the representative**: `|f̄|_*` is the map `|Ψ|_* ∘ |Φ|_*⁻¹` of every
representative `W ←Φ– V –Ψ→ W'` of `f̄`. -/
theorem orbitOrMap_eq {D : SDiagram A A'} (hD : D.cls = F) :
    orbitOrMap hFi hF hF' hf' hsec hsec' =
      D.orbitOrMap (equivalences_Ψ_of_cls hFi hD) hF hF' (pullback_eq_of_cls' hFi hD hF.1 hf')
        hsec hsec' :=
  SDiagram.orbitOrMap_eq_of_equiv (isEquivalence_rep_Ψ hFi) (equivalences_Ψ_of_cls hFi hD) hF hF'
    _ _ hsec hsec' (SDiagram.cls_eq_cls_iff.1 ((cls_rep hFi).trans hD.symm))

theorem smoothOrbitMap_eq {D : SDiagram A A'} (hD : D.cls = F) :
    smoothOrbitMap hFi = D.smoothOrbitMap (equivalences_Ψ_of_cls hFi hD) :=
  SDiagram.smoothOrbitMap_eq_of_equiv (isEquivalence_rep_Ψ hFi) (equivalences_Ψ_of_cls hFi hD)
    (SDiagram.cls_eq_cls_iff.1 ((cls_rep hFi).trans hD.symm))

/-- **Theorem 12.5.7 (1) for classes, without the topology**, p. 595 (2017: Theorem 12.12):
`|f̄|_*` and `|f|` are bijections, `|σ'| ∘ |f̄|_* = |f| ∘ |σ|`, and both are the maps of every
representative of `f̄`. -/
theorem theorem_12_5_7_cls :
    Bijective (orbitOrMap hFi hF hF' hf' hsec hsec') ∧ Bijective (smoothOrbitMap hFi) ∧
      (∀ x, A'.E.orbitProj hF' hsec' (orbitOrMap hFi hF hF' hf' hsec hsec' x) =
        smoothOrbitMap hFi (A.E.orbitProj hF hsec x)) ∧
      ∀ (D : SDiagram A A') (hD : D.cls = F),
        orbitOrMap hFi hF hF' hf' hsec hsec' =
          D.orbitOrMap (equivalences_Ψ_of_cls hFi hD) hF hF'
            (pullback_eq_of_cls' hFi hD hF.1 hf') hsec hsec' ∧
        smoothOrbitMap hFi = D.smoothOrbitMap (equivalences_Ψ_of_cls hFi hD) :=
  ⟨SDiagram.orbitOrMap_bijective (rep hFi) (isEquivalence_rep_Ψ hFi) hF hF' _ hsec hsec',
    SDiagram.smoothOrbitMap_bijective (rep hFi) (isEquivalence_rep_Ψ hFi),
    SDiagram.orbitProj_orbitOrMap (rep hFi) (isEquivalence_rep_Ψ hFi) hF hF' _ hsec hsec',
    fun _ hD =>
      ⟨orbitOrMap_eq hFi hF hF' hf' hsec hsec' hD, smoothOrbitMap_eq hFi hD⟩⟩

/-! #### Composition -/

variable {G : GenSBMap A' A''} (hGi : G.IsGeneralizedIso)

include hFi hGi in
/-- The composite of generalized strong bundle isomorphisms is one. -/
theorem isGeneralizedIso_comp : (F.comp G).IsGeneralizedIso := by
  refine ⟨(rep hFi).comp (rep hGi), ?_,
    SDiagram.equivalences_comp_Ψ (isEquivalence_rep_Ψ hFi) (isEquivalence_rep_Ψ hGi)⟩
  rw [← cls_comp_cls, cls_rep, cls_rep]

theorem cls_comp_rep : ((rep hFi).comp (rep hGi)).cls = F.comp G := by
  rw [← cls_comp_cls, cls_rep, cls_rep]

/-- **`(ḡ ∘ f̄)_* = ḡ_* ∘ f̄_*`** on section functors. -/
theorem pushforward_comp (hFG : (F.comp G).IsGeneralizedIso) {f : A.Obj → A.W}
    (hf : f ∈ A.E.sectionFunctors) :
    pushforward hFG f = pushforward hGi (pushforward hFi f) := by
  set D := rep hFi
  set E := rep hGi
  have hf' := (theorem_10_5_4 hFi).2.1.1 hf
  have hf'' := (theorem_10_5_4 hGi).2.1.1 hf'
  have hΨc := SDiagram.equivalences_comp_Ψ (isEquivalence_rep_Ψ hFi) (isEquivalence_rep_Ψ hGi)
  have hc := SDiagram.comp_pullback_eq (isEquivalence_rep_Ψ hFi) (isEquivalence_rep_Ψ hGi)
    (pullback_eq_of_cls hFi (cls_rep hFi) (isEquivalence_rep_Ψ hFi) hf)
    (pullback_eq_of_cls hGi (cls_rep hGi) (isEquivalence_rep_Ψ hGi) hf')
    hf hf' hf''.1.1
  rw [pushforward_eq hFG (cls_comp_rep hFi hGi) hΨc hf]
  change (sbe hΨc).pushforward ((D.comp E).hΦ.pullback f) = _
  rw [hc]
  exact (sbe hΨc).pushforward_pullback hf''.1.1 hf''.2

include hFi hf' in
/-- `f'' = (ḡ ∘ f̄)_* f` when `f' = f̄_* f` and `f'' = ḡ_* f'`. -/
theorem eq_pushforward_comp (hFG : (F.comp G).IsGeneralizedIso) {f'' : A''.Obj → A''.W}
    (hf : f ∈ A.E.sectionFunctors) (hf'' : f'' = pushforward hGi f') : f'' = pushforward hFG f := by
  rw [hf'', hf', pushforward_comp hFi hGi hFG hf]

/-- **Theorem 12.5.7, functoriality, for classes**, p. 595 (2017: Theorem 12.12):
`|ḡ ∘ f̄|_* = |ḡ|_* ∘ |f̄|_*` for generalized strong bundle isomorphisms `f̄ : W → W'`,
`ḡ : W' → W''` (the composition of `SEP(F⁻¹)`), with `f' = f̄_* f`, `f'' = ḡ_* f'`. -/
theorem theorem_12_5_7_functorial (hFG : (F.comp G).IsGeneralizedIso) {f'' : A''.Obj → A''.W}
    (hF'' : A''.E.IsScFredholmSectionFunctor f'') (hf'' : f'' = pushforward hGi f')
    (hsec'' : A''.B.HasScPlusSectionsThrough) (x : Quot (A.E.OrRel hF hsec)) :
    orbitOrMap hFG hF hF'' (eq_pushforward_comp hFi hf' hGi hFG hF.1 hf'') hsec hsec'' x =
      orbitOrMap hGi hF' hF'' hf'' hsec' hsec'' (orbitOrMap hFi hF hF' hf' hsec hsec' x) := by
  rw [orbitOrMap_eq hFG _ _ _ hsec hsec'' (cls_comp_rep hFi hGi)]
  exact SDiagram.orbitOrMap_comp (isEquivalence_rep_Ψ hFi) (isEquivalence_rep_Ψ hGi)
    (pullback_eq_of_cls' hFi (cls_rep hFi) hF.1 hf')
    (pullback_eq_of_cls' hGi (cls_rep hGi) hF'.1 hf'') hF hF' hF'' hsec hsec' hsec'' x

/-- The base form of `theorem_12_5_7_functorial`: `|g ∘ f| = |g| ∘ |f|` on `|X_∞|`. -/
theorem theorem_12_5_7_functorial_base (hFG : (F.comp G).IsGeneralizedIso)
    (x : Quot A.X.SmoothRel) :
    smoothOrbitMap hFG x = smoothOrbitMap hGi (smoothOrbitMap hFi x) := by
  rw [smoothOrbitMap_eq hFG (cls_comp_rep hFi hGi)]
  exact SDiagram.smoothOrbitMap_comp (isEquivalence_rep_Ψ hFi) (isEquivalence_rep_Ψ hGi) x

/-! #### The identity -/

/-- `[1_W]_* f = f` on section functors. -/
theorem pushforward_id (hid : (SDiagram.id A).cls.IsGeneralizedIso) {f : A.Obj → A.W}
    (hf : f ∈ A.E.sectionFunctors) : pushforward hid f = f := by
  rw [pushforward_eq hid rfl (SEP.equivalences.id_mem A) hf]
  exact (sbe (SEP.equivalences.id_mem A)).pushforward_pullback hf.1.1 hf.2

/-- **Theorem 12.5.7, functoriality, the identity**: `|[1_W]|_* = 1` on `|O_f|`. -/
theorem theorem_12_5_7_id (hid : (SDiagram.id A).cls.IsGeneralizedIso) {f : A.Obj → A.W}
    (hF : A.E.IsScFredholmSectionFunctor f) (hsec : A.B.HasScPlusSectionsThrough)
    (x : Quot (A.E.OrRel hF hsec)) :
    orbitOrMap hid hF hF (pushforward_id hid hF.1).symm hsec hsec x = x := by
  rw [orbitOrMap_eq hid hF hF _ hsec hsec rfl]
  exact SDiagram.orbitOrMap_id hF hsec x

end GenSBMap

end SBLocalization

end Polyfold
