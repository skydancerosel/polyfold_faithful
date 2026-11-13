import Polyfold.Chapter12.P3W7W3_OrEqvNat

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12): **independence of the representative**
(left to the reader in the text).  A generalized strong bundle isomorphism is represented by a
diagram `W ←Φ₁– V –Φ₂→ W'` of strong bundle equivalences (Chapter 10, `SBLocalization.SDiagram`);
two diagrams represent the same morphism iff they have a common refinement
(`SDiagram.IsRefinement`: `H : V'' → V` an equivalence with `Φᵢ ∘ H ≃ Φ'ᵢ`, Definition 10.4.8).
The map `|O_f| → |O_{f'}|` of a diagram is `|Φ₂|_* ∘ |Φ₁|_*⁻¹` (both bijective, Theorem 12.5.7
(1)); the same for `|X_∞| → |X'_∞|`.

* `orbitOrMap_refine`, `smoothOrbitMap_refine`: `|K|_* = |Φ|_* ∘ |H|_*` when `Φ ∘ H ≃ K`
  (`orbitOrMap_comp` and `orbitOrMap_nat`).
* `theorem_12_5_7_refinement`, `theorem_12_5_7_refinement_base`: a refinement induces the same
  maps.
* `theorem_12_5_7_rep_indep`, `theorem_12_5_7_rep_indep_base`: two diagrams with a common
  refinement induce the same maps (the equivalence relation `SDiagram.Equiv`).
* `theorem_12_5_7_functorial`, `theorem_12_5_7_functorial_base`: the map of a composite diagram
  (middle `V₃` with equivalences to the two middles and `Φ₂ ∘ Π₁ ≃ Γ₁ ∘ Π₂`, as for the weak
  fibred product of Chapter 10) is the composite of the maps.

The section functors on the middle bundles are taken with `f'' = Φ₁^* f = Φ₂^* f'` as in
`theorem_12_5_7_one_homeo_hyp`; no hypothesis beyond those of Theorem 12.5.7 is added.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Rep

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle X.PObj P} [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {B' : StrongBundle X'.PObj P'} [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {Obj₁ Mor₁ : Type u} [TopologicalSpace Obj₁] [T2Space Obj₁] [ParacompactSpace Obj₁]
  [TopologicalSpace Mor₁] [T2Space Mor₁] [ParacompactSpace Mor₁] {X₁ : EpGroupoid Obj₁ Mor₁}
  {V₁ : Type u} [TopologicalSpace V₁] [T2Space V₁] [ParacompactSpace V₁] {P₁ : V₁ → Obj₁}
  [∀ x, AddCommGroup (P₁ ⁻¹' {x})] [∀ x, Module ℝ (P₁ ⁻¹' {x})]
  {B₁ : StrongBundle X₁.PObj P₁} [ParacompactSpace (pullbackSpace P₁ X₁.src)]
  {Obj₂ Mor₂ : Type u} [TopologicalSpace Obj₂] [T2Space Obj₂] [ParacompactSpace Obj₂]
  [TopologicalSpace Mor₂] [T2Space Mor₂] [ParacompactSpace Mor₂] {X₂ : EpGroupoid Obj₂ Mor₂}
  {V₂ : Type u} [TopologicalSpace V₂] [T2Space V₂] [ParacompactSpace V₂] {P₂ : V₂ → Obj₂}
  [∀ x, AddCommGroup (P₂ ⁻¹' {x})] [∀ x, Module ℝ (P₂ ⁻¹' {x})]
  {B₂ : StrongBundle X₂.PObj P₂} [ParacompactSpace (pullbackSpace P₂ X₂.src)]
  {Obj₃ Mor₃ : Type u} [TopologicalSpace Obj₃] [T2Space Obj₃] [ParacompactSpace Obj₃]
  [TopologicalSpace Mor₃] [T2Space Mor₃] [ParacompactSpace Mor₃] {X₃ : EpGroupoid Obj₃ Mor₃}
  {V₃ : Type u} [TopologicalSpace V₃] [T2Space V₃] [ParacompactSpace V₃] {P₃ : V₃ → Obj₃}
  [∀ x, AddCommGroup (P₃ ⁻¹' {x})] [∀ x, Module ℝ (P₃ ⁻¹' {x})]
  {B₃ : StrongBundle X₃.PObj P₃} [ParacompactSpace (pullbackSpace P₃ X₃.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E₁ : EpStrongBundle X₁ B₁}
  {E₂ : EpStrongBundle X₂ B₂} {E₃ : EpStrongBundle X₃ B₃} {E'' : EpStrongBundle X'' B''}

namespace EpStrongBundle.IsStrongBundleEquivalence

section Refine

variable {ϕ₁ : EpFunctor X₁ X} {Φ₁ : EpFunctor E₁.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X₁ X'} {Φ₂ : EpFunctor E₁.toEpGroupoid E'.toEpGroupoid}
  {κ₁ : EpFunctor X₃ X} {K₁ : EpFunctor E₃.toEpGroupoid E.toEpGroupoid}
  {κ₂ : EpFunctor X₃ X'} {K₂ : EpFunctor E₃.toEpGroupoid E'.toEpGroupoid}
  {η : EpFunctor X₃ X₁} {H : EpFunctor E₃.toEpGroupoid E₁.toEpGroupoid}
  (h₁ : E₁.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E₁.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  (k₁ : E₃.IsStrongBundleEquivalence E κ₁ K₁) (k₂ : E₃.IsStrongBundleEquivalence E' κ₂ K₂)
  (hH : E₃.IsStrongBundleEquivalence E₁ η H)
  (θ₁ : E₃.StrongBundleNatTrans E (ϕ₁.comp η) κ₁ (Φ₁.comp H) K₁)
  (θ₂ : E₃.StrongBundleNatTrans E' (ϕ₂.comp η) κ₂ (Φ₂.comp H) K₂)
  {f : Obj → W} {f' : Obj' → W'} {f₁ : Obj₁ → V₁} {f₃ : Obj₃ → V₃}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF₁ : E₁.IsScFredholmSectionFunctor f₁) (hF₃ : E₃.IsScFredholmSectionFunctor f₃)
  (hpb₁ : f₁ = h₁.pullback f) (hpb₂ : f₁ = h₂.pullback f') (hpbH : f₃ = hH.pullback f₁)
  (hk₁ : f₃ = k₁.pullback f) (hk₂ : f₃ = k₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec₁ : B₁.HasScPlusSectionsThrough) (hsec₃ : B₃.HasScPlusSectionsThrough)

include θ₁ in
/-- **`|K|_* = |Φ|_* ∘ |H|_*` when `Φ ∘ H ≃ K`** (Definition 10.4.8). -/
theorem orbitOrMap_refine (c : Quot (E₃.OrRel hF₃ hsec₃)) :
    k₁.orbitOrMap hF₃ hF hk₁ hsec₃ hsec c =
      h₁.orbitOrMap hF₁ hF hpb₁ hsec₁ hsec (hH.orbitOrMap hF₃ hF₁ hpbH hsec₃ hsec₁ c) :=
  (orbitOrMap_nat (h₁.comp hH) k₁ θ₁ hF₃ hF (pullback_comp_of hH h₁ hF hpbH hpb₁) hk₁ hsec₃
    hsec c).symm.trans (orbitOrMap_comp hH h₁ hF₃ hF₁ hF hpbH hpb₁ hsec₃ hsec₁ hsec c)

include θ₁ in
/-- **`|κ| = |ϕ| ∘ |η|` on `|X_∞|` when `ϕ ∘ η ≃ κ`.** -/
theorem smoothOrbitMap_refine (c : Quot X₃.SmoothRel) :
    k₁.smoothOrbitMap c = h₁.smoothOrbitMap (hH.smoothOrbitMap c) :=
  (smoothOrbitMap_nat (h₁.comp hH) k₁ θ₁ c).symm.trans (smoothOrbitMap_comp hH h₁ c)

include θ₁ θ₂ hH hF₃ hpbH hk₁ hk₂ hsec₃ in
/-- **Theorem 12.5.7, independence under refinement**, p. 595 (2017: Theorem 12.12): if
`W ←K₁– V'' –K₂→ W'` refines `W ←Φ₁– V –Φ₂→ W'` through the equivalence `H : V'' → V`
(`Φᵢ ∘ H ≃ Kᵢ`), the maps `|O_f| → |O_{f'}|` agree: `|Φ₂|_* ∘ |Φ₁|_*⁻¹ = |K₂|_* ∘ |K₁|_*⁻¹`. -/
theorem theorem_12_5_7_refinement (x : Quot (E.OrRel hF hsec)) :
    (Equiv.ofBijective _ (h₂.orbitOrMap_bijective hF₁ hF' hpb₂ hsec₁ hsec'))
      ((Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF₁ hF hpb₁ hsec₁ hsec)).symm x) =
    (Equiv.ofBijective _ (k₂.orbitOrMap_bijective hF₃ hF' hk₂ hsec₃ hsec'))
      ((Equiv.ofBijective _ (k₁.orbitOrMap_bijective hF₃ hF hk₁ hsec₃ hsec)).symm x) := by
  set e₁ := Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF₁ hF hpb₁ hsec₁ hsec)
  set d₁ := Equiv.ofBijective _ (k₁.orbitOrMap_bijective hF₃ hF hk₁ hsec₃ hsec)
  obtain ⟨c, rfl⟩ := d₁.surjective x
  rw [Equiv.symm_apply_apply]
  have h1 : e₁.symm (d₁ c) = hH.orbitOrMap hF₃ hF₁ hpbH hsec₃ hsec₁ c := by
    rw [Equiv.symm_apply_eq]
    exact orbitOrMap_refine h₁ k₁ hH θ₁ hF hF₁ hF₃ hpb₁ hpbH hk₁ hsec hsec₁ hsec₃ c
  rw [h1]
  exact (orbitOrMap_refine h₂ k₂ hH θ₂ hF' hF₁ hF₃ hpb₂ hpbH hk₂ hsec' hsec₁ hsec₃ c).symm

include θ₁ θ₂ hH in
/-- The base form of `theorem_12_5_7_refinement`: `|ϕ₂| ∘ |ϕ₁|⁻¹ = |κ₂| ∘ |κ₁|⁻¹` on
`|X_∞|`. -/
theorem theorem_12_5_7_refinement_base (x : Quot X.SmoothRel) :
    (Equiv.ofBijective _ h₂.smoothOrbitMap_bijective)
      ((Equiv.ofBijective _ h₁.smoothOrbitMap_bijective).symm x) =
    (Equiv.ofBijective _ k₂.smoothOrbitMap_bijective)
      ((Equiv.ofBijective _ k₁.smoothOrbitMap_bijective).symm x) := by
  set e₁ := Equiv.ofBijective _ h₁.smoothOrbitMap_bijective
  set d₁ := Equiv.ofBijective _ k₁.smoothOrbitMap_bijective
  obtain ⟨c, rfl⟩ := d₁.surjective x
  rw [Equiv.symm_apply_apply]
  have h1 : e₁.symm (d₁ c) = hH.smoothOrbitMap c := by
    rw [Equiv.symm_apply_eq]
    exact smoothOrbitMap_refine h₁ k₁ hH θ₁ c
  rw [h1]
  exact (smoothOrbitMap_refine h₂ k₂ hH θ₂ c).symm

end Refine

section Common

variable {ϕ₁ : EpFunctor X₁ X} {Φ₁ : EpFunctor E₁.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X₁ X'} {Φ₂ : EpFunctor E₁.toEpGroupoid E'.toEpGroupoid}
  {γ₁ : EpFunctor X₂ X} {Γ₁ : EpFunctor E₂.toEpGroupoid E.toEpGroupoid}
  {γ₂ : EpFunctor X₂ X'} {Γ₂ : EpFunctor E₂.toEpGroupoid E'.toEpGroupoid}
  {κ₁ : EpFunctor X₃ X} {K₁ : EpFunctor E₃.toEpGroupoid E.toEpGroupoid}
  {κ₂ : EpFunctor X₃ X'} {K₂ : EpFunctor E₃.toEpGroupoid E'.toEpGroupoid}
  {η₁ : EpFunctor X₃ X₁} {H₁ : EpFunctor E₃.toEpGroupoid E₁.toEpGroupoid}
  {η₂ : EpFunctor X₃ X₂} {H₂ : EpFunctor E₃.toEpGroupoid E₂.toEpGroupoid}
  (h₁ : E₁.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E₁.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  (g₁ : E₂.IsStrongBundleEquivalence E γ₁ Γ₁) (g₂ : E₂.IsStrongBundleEquivalence E' γ₂ Γ₂)
  (k₁ : E₃.IsStrongBundleEquivalence E κ₁ K₁) (k₂ : E₃.IsStrongBundleEquivalence E' κ₂ K₂)
  (hH₁ : E₃.IsStrongBundleEquivalence E₁ η₁ H₁) (hH₂ : E₃.IsStrongBundleEquivalence E₂ η₂ H₂)
  (θ₁ : E₃.StrongBundleNatTrans E (ϕ₁.comp η₁) κ₁ (Φ₁.comp H₁) K₁)
  (θ₂ : E₃.StrongBundleNatTrans E' (ϕ₂.comp η₁) κ₂ (Φ₂.comp H₁) K₂)
  (ζ₁ : E₃.StrongBundleNatTrans E (γ₁.comp η₂) κ₁ (Γ₁.comp H₂) K₁)
  (ζ₂ : E₃.StrongBundleNatTrans E' (γ₂.comp η₂) κ₂ (Γ₂.comp H₂) K₂)
  {f : Obj → W} {f' : Obj' → W'} {f₁ : Obj₁ → V₁} {f₂ : Obj₂ → V₂} {f₃ : Obj₃ → V₃}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF₁ : E₁.IsScFredholmSectionFunctor f₁) (hF₂ : E₂.IsScFredholmSectionFunctor f₂)
  (hF₃ : E₃.IsScFredholmSectionFunctor f₃)
  (hpb₁ : f₁ = h₁.pullback f) (hpb₂ : f₁ = h₂.pullback f')
  (hqb₁ : f₂ = g₁.pullback f) (hqb₂ : f₂ = g₂.pullback f')
  (hpbH₁ : f₃ = hH₁.pullback f₁) (hpbH₂ : f₃ = hH₂.pullback f₂)
  (hk₁ : f₃ = k₁.pullback f) (hk₂ : f₃ = k₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec₁ : B₁.HasScPlusSectionsThrough) (hsec₂ : B₂.HasScPlusSectionsThrough)
  (hsec₃ : B₃.HasScPlusSectionsThrough)

include θ₁ θ₂ ζ₁ ζ₂ k₁ k₂ hH₁ hH₂ hF₃ hpbH₁ hpbH₂ hk₁ hk₂ hsec₃ in
/-- **Theorem 12.5.7, independence of the representative**, p. 595 (2017: Theorem 12.12): two
diagrams `W ←Φ₁– V₁ –Φ₂→ W'` and `W ←Γ₁– V₂ –Γ₂→ W'` with a common refinement
`W ←K₁– V₃ –K₂→ W'` (through equivalences `H₁ : V₃ → V₁`, `H₂ : V₃ → V₂`, `Φᵢ ∘ H₁ ≃ Kᵢ`,
`Γᵢ ∘ H₂ ≃ Kᵢ`; Chapter 10's `SDiagram.Equiv`) induce the same map `|O_f| → |O_{f'}|`. -/
theorem theorem_12_5_7_rep_indep (x : Quot (E.OrRel hF hsec)) :
    (Equiv.ofBijective _ (h₂.orbitOrMap_bijective hF₁ hF' hpb₂ hsec₁ hsec'))
      ((Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF₁ hF hpb₁ hsec₁ hsec)).symm x) =
    (Equiv.ofBijective _ (g₂.orbitOrMap_bijective hF₂ hF' hqb₂ hsec₂ hsec'))
      ((Equiv.ofBijective _ (g₁.orbitOrMap_bijective hF₂ hF hqb₁ hsec₂ hsec)).symm x) :=
  (theorem_12_5_7_refinement h₁ h₂ k₁ k₂ hH₁ θ₁ θ₂ hF hF' hF₁ hF₃ hpb₁ hpb₂ hpbH₁ hk₁ hk₂
    hsec hsec' hsec₁ hsec₃ x).trans
    (theorem_12_5_7_refinement g₁ g₂ k₁ k₂ hH₂ ζ₁ ζ₂ hF hF' hF₂ hF₃ hqb₁ hqb₂ hpbH₂ hk₁ hk₂
      hsec hsec' hsec₂ hsec₃ x).symm

include θ₁ θ₂ ζ₁ ζ₂ k₁ k₂ hH₁ hH₂ in
/-- The base form of `theorem_12_5_7_rep_indep`: the same map `|X_∞| → |X'_∞|`. -/
theorem theorem_12_5_7_rep_indep_base (x : Quot X.SmoothRel) :
    (Equiv.ofBijective _ h₂.smoothOrbitMap_bijective)
      ((Equiv.ofBijective _ h₁.smoothOrbitMap_bijective).symm x) =
    (Equiv.ofBijective _ g₂.smoothOrbitMap_bijective)
      ((Equiv.ofBijective _ g₁.smoothOrbitMap_bijective).symm x) :=
  (theorem_12_5_7_refinement_base h₁ h₂ k₁ k₂ hH₁ θ₁ θ₂ x).trans
    (theorem_12_5_7_refinement_base g₁ g₂ k₁ k₂ hH₂ ζ₁ ζ₂ x).symm

end Common

section Functorial

variable {ϕ₁ : EpFunctor X₁ X} {Φ₁ : EpFunctor E₁.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X₁ X'} {Φ₂ : EpFunctor E₁.toEpGroupoid E'.toEpGroupoid}
  {γ₁ : EpFunctor X₂ X'} {Γ₁ : EpFunctor E₂.toEpGroupoid E'.toEpGroupoid}
  {γ₂ : EpFunctor X₂ X''} {Γ₂ : EpFunctor E₂.toEpGroupoid E''.toEpGroupoid}
  {π₁ : EpFunctor X₃ X₁} {Q₁ : EpFunctor E₃.toEpGroupoid E₁.toEpGroupoid}
  {π₂ : EpFunctor X₃ X₂} {Q₂ : EpFunctor E₃.toEpGroupoid E₂.toEpGroupoid}
  (h₁ : E₁.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E₁.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  (g₁ : E₂.IsStrongBundleEquivalence E' γ₁ Γ₁) (g₂ : E₂.IsStrongBundleEquivalence E'' γ₂ Γ₂)
  (p₁ : E₃.IsStrongBundleEquivalence E₁ π₁ Q₁) (p₂ : E₃.IsStrongBundleEquivalence E₂ π₂ Q₂)
  (θ : E₃.StrongBundleNatTrans E' (ϕ₂.comp π₁) (γ₁.comp π₂) (Φ₂.comp Q₁) (Γ₁.comp Q₂))
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} {f₁ : Obj₁ → V₁} {f₂ : Obj₂ → V₂}
  {f₃ : Obj₃ → V₃}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hF₁ : E₁.IsScFredholmSectionFunctor f₁) (hF₂ : E₂.IsScFredholmSectionFunctor f₂)
  (hF₃ : E₃.IsScFredholmSectionFunctor f₃)
  (hpb₁ : f₁ = h₁.pullback f) (hpb₂ : f₁ = h₂.pullback f')
  (hqb₁ : f₂ = g₁.pullback f') (hqb₂ : f₂ = g₂.pullback f'')
  (hp₁ : f₃ = p₁.pullback f₁) (hp₂ : f₃ = p₂.pullback f₂)
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec'' : B''.HasScPlusSectionsThrough)
  (hsec₁ : B₁.HasScPlusSectionsThrough) (hsec₂ : B₂.HasScPlusSectionsThrough)
  (hsec₃ : B₃.HasScPlusSectionsThrough)

include θ in
/-- **Theorem 12.5.7, functoriality**, p. 595 (2017: Theorem 12.12): for diagrams
`W ←Φ₁– V₁ –Φ₂→ W'` and `W' ←Γ₁– V₂ –Γ₂→ W''` and a composite diagram
`W ←Φ₁Q₁– V₃ –Γ₂Q₂→ W''` (equivalences `Q₁ : V₃ → V₁`, `Q₂ : V₃ → V₂` with
`Φ₂ ∘ Q₁ ≃ Γ₁ ∘ Q₂`, as for the weak fibred product of Chapter 10), the map
`|O_f| → |O_{f''}|` of the composite is the composite of the maps. -/
theorem theorem_12_5_7_functorial (x : Quot (E.OrRel hF hsec)) :
    (Equiv.ofBijective _ ((g₂.comp p₂).orbitOrMap_bijective hF₃ hF''
      (pullback_comp_of p₂ g₂ hF'' hp₂ hqb₂) hsec₃ hsec''))
      ((Equiv.ofBijective _ ((h₁.comp p₁).orbitOrMap_bijective hF₃ hF
        (pullback_comp_of p₁ h₁ hF hp₁ hpb₁) hsec₃ hsec)).symm x) =
    (Equiv.ofBijective _ (g₂.orbitOrMap_bijective hF₂ hF'' hqb₂ hsec₂ hsec''))
      ((Equiv.ofBijective _ (g₁.orbitOrMap_bijective hF₂ hF' hqb₁ hsec₂ hsec')).symm
        ((Equiv.ofBijective _ (h₂.orbitOrMap_bijective hF₁ hF' hpb₂ hsec₁ hsec'))
          ((Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF₁ hF hpb₁ hsec₁ hsec)).symm x))) := by
  set d := Equiv.ofBijective _ ((h₁.comp p₁).orbitOrMap_bijective hF₃ hF
    (pullback_comp_of p₁ h₁ hF hp₁ hpb₁) hsec₃ hsec)
  obtain ⟨c, rfl⟩ := d.surjective x
  rw [Equiv.symm_apply_apply]
  have e1 : (Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF₁ hF hpb₁ hsec₁ hsec)).symm (d c) =
      p₁.orbitOrMap hF₃ hF₁ hp₁ hsec₃ hsec₁ c := by
    rw [Equiv.symm_apply_eq]
    exact orbitOrMap_comp p₁ h₁ hF₃ hF₁ hF hp₁ hpb₁ hsec₃ hsec₁ hsec c
  have e2 : h₂.orbitOrMap hF₁ hF' hpb₂ hsec₁ hsec' (p₁.orbitOrMap hF₃ hF₁ hp₁ hsec₃ hsec₁ c) =
      g₁.orbitOrMap hF₂ hF' hqb₁ hsec₂ hsec' (p₂.orbitOrMap hF₃ hF₂ hp₂ hsec₃ hsec₂ c) :=
    (orbitOrMap_comp p₁ h₂ hF₃ hF₁ hF' hp₁ hpb₂ hsec₃ hsec₁ hsec' c).symm.trans
      ((orbitOrMap_nat (h₂.comp p₁) (g₁.comp p₂) θ hF₃ hF'
        (pullback_comp_of p₁ h₂ hF' hp₁ hpb₂) (pullback_comp_of p₂ g₁ hF' hp₂ hqb₁) hsec₃
        hsec' c).trans (orbitOrMap_comp p₂ g₁ hF₃ hF₂ hF' hp₂ hqb₁ hsec₃ hsec₂ hsec' c))
  rw [e1]
  change _ = g₂.orbitOrMap hF₂ hF'' hqb₂ hsec₂ hsec'' ((Equiv.ofBijective _
    (g₁.orbitOrMap_bijective hF₂ hF' hqb₁ hsec₂ hsec')).symm
      (h₂.orbitOrMap hF₁ hF' hpb₂ hsec₁ hsec' (p₁.orbitOrMap hF₃ hF₁ hp₁ hsec₃ hsec₁ c)))
  rw [e2]
  change _ = g₂.orbitOrMap hF₂ hF'' hqb₂ hsec₂ hsec'' ((Equiv.ofBijective _
    (g₁.orbitOrMap_bijective hF₂ hF' hqb₁ hsec₂ hsec')).symm ((Equiv.ofBijective _
      (g₁.orbitOrMap_bijective hF₂ hF' hqb₁ hsec₂ hsec'))
        (p₂.orbitOrMap hF₃ hF₂ hp₂ hsec₃ hsec₂ c)))
  rw [Equiv.symm_apply_apply]
  exact orbitOrMap_comp p₂ g₂ hF₃ hF₂ hF'' hp₂ hqb₂ hsec₃ hsec₂ hsec'' c

include θ in
/-- The base form of `theorem_12_5_7_functorial` on `|X_∞|`. -/
theorem theorem_12_5_7_functorial_base (x : Quot X.SmoothRel) :
    (Equiv.ofBijective _ (g₂.comp p₂).smoothOrbitMap_bijective)
      ((Equiv.ofBijective _ (h₁.comp p₁).smoothOrbitMap_bijective).symm x) =
    (Equiv.ofBijective _ g₂.smoothOrbitMap_bijective)
      ((Equiv.ofBijective _ g₁.smoothOrbitMap_bijective).symm
        ((Equiv.ofBijective _ h₂.smoothOrbitMap_bijective)
          ((Equiv.ofBijective _ h₁.smoothOrbitMap_bijective).symm x))) := by
  set d := Equiv.ofBijective _ (h₁.comp p₁).smoothOrbitMap_bijective
  obtain ⟨c, rfl⟩ := d.surjective x
  rw [Equiv.symm_apply_apply]
  have e1 : (Equiv.ofBijective _ h₁.smoothOrbitMap_bijective).symm (d c) =
      p₁.smoothOrbitMap c := by
    rw [Equiv.symm_apply_eq]; exact smoothOrbitMap_comp p₁ h₁ c
  have e2 : h₂.smoothOrbitMap (p₁.smoothOrbitMap c) = g₁.smoothOrbitMap (p₂.smoothOrbitMap c) :=
    (smoothOrbitMap_comp p₁ h₂ c).symm.trans
      ((smoothOrbitMap_nat (h₂.comp p₁) (g₁.comp p₂) θ c).trans (smoothOrbitMap_comp p₂ g₁ c))
  rw [e1]
  change _ = g₂.smoothOrbitMap ((Equiv.ofBijective _ g₁.smoothOrbitMap_bijective).symm
    (h₂.smoothOrbitMap (p₁.smoothOrbitMap c)))
  rw [e2]
  change _ = g₂.smoothOrbitMap ((Equiv.ofBijective _ g₁.smoothOrbitMap_bijective).symm
    ((Equiv.ofBijective _ g₁.smoothOrbitMap_bijective) (p₂.smoothOrbitMap c)))
  rw [Equiv.symm_apply_apply]
  exact smoothOrbitMap_comp p₂ g₂ c

end Functorial

end EpStrongBundle.IsStrongBundleEquivalence

end Rep

end Polyfold
