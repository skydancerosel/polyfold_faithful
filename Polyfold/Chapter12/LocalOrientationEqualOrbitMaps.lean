import Polyfold.Chapter12.LocalOrientationGeneralizedIso
import Polyfold.Chapter12.OrientationEqualOrbitMapsGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 595, **Theorem 12.5.7**, with **Proposition 10.4.7** (pp. 501–502), **Theorem 10.5.7**
(p. 508) and **Definition 8.4.2** (p. 382): strong bundle equivalences and generalized strong
bundle isomorphisms with the same map of orbit spaces induce the same maps of orientations,
for the linearizations made with local sc⁺-sections.

## The text, paraphrased

(Proposition 10.4.7) For strong bundle equivalences `Φ, Ψ : W → W'` with `|Φ| = |Ψ|` between
strong bundles with the local regularity property, every `x` has a neighbourhood `U(x)` and an
sc-smooth `z ↦ α_z : ϕ(z) → ψ(z)` on it with `μ'(α_z, Φ(v)) = Ψ(v)` for `P(v) = z`.
(Theorem 12.5.7 (2)) An orientation `o` of `f` has a push-forward orientation `o' = f̄_* o` of
`f' = f̄_* f`.

## What is formalized

The orientation sets are the local ones (`OrxLoc`); the hypotheses are tame object M-polyfolds
and tame germ data, and the local regularity property of the target on germs
(`EpStrongBundle.IsLRGerm`).

* `orEqvLoc_of_germ`: for a morphism `σ : ϕ(a) → ψ(a)` with `Φ̂'_σ ∘ Ψ = Φ` near `a`, the
  identification `Or^{f'}_{ψ(a)} ≃ Or^f_a` of `Ψ` after `σ_*` is that of `Φ`.
* `orRelLoc_orSpaceMapLoc_of_isLRGerm`, **`orbitOrMapLoc_eq_of_isLRGerm`**: `|Φ| = |Ψ|` gives
  `|Φ|_* = |Ψ|_*` on `|O_f|`.
* **`theorem_12_5_7_rep_indep_loc_of_isLRGerm`**: two diagrams refined by one middle bundle.
* `SBLocalization.SDiagram.orbitOrMapLoc_eq_of_isLRGerm`,
  `SBLocalization.GenSBMap.orbitOrMapLoc_eq_of_isLRGerm`,
  **`SBLocalization.GenSBMap.theorem_12_5_7_two_corr_indep_loc_of_isLRGerm`**: Theorem 12.5.7
  (2) does not depend on the generalized strong bundle isomorphism with a given map of orbit
  spaces.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

open StrongRetr StrongBundle.LocalIso

universe u

section Germ

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

variable {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ) (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ)

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpbΦ : f = hΦ.pullback f')
  (hpbΨ : f = hΨ.pullback f') (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame) (hfT :
  B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')

variable {a : Obj} (σ : Mor') (hσs : X'.src σ = ϕ.obj a) (hσt : X'.tgt σ = ψ.obj a)

variable (hG : ∃ N : Set Obj, IsOpen N ∧ a ∈ N ∧
    (∀ y ∈ N, (E'.morIso σ).ϕ ((hΨ.locIso a).ϕ y) = (hΦ.locIso a).ϕ y) ∧
    ∀ w, P w ∈ N → (E'.morIso σ).Φ ((hΨ.locIso a).Φ w) = (hΦ.locIso a).Φ w)

include hG in
/-- **The identifications of orientations of `Φ` and `Ψ` at `a` differ by `σ_*`**, for
`σ : ϕ(a) → ψ(a)` with `Φ̂'_σ ∘ Ψ = Φ` near `a`, on the local orientation sets. -/
theorem orEqvLoc_of_germ (hs : a ∈ X.PObj.smoothSet)
    (o : OrxLoc hfT' (ϕ.obj a) (hΦ.smooth_obj hs)) :
    hΨ.orEqvLoc hpbΨ hfT hfT' a hs (E'.orMorLoc hF' hfT' σ hσs hσt (hΦ.smooth_obj hs)
      (hΨ.smooth_obj hs) o) = hΦ.orEqvLoc hpbΦ hfT hfT' a hs o :=
  DFunLike.congr_fun (orLoc_triangle (L := E'.morIso σ) (L₂ := hΨ.locIso a)
    (N := hΦ.locIso a) hfT hfT' hfT' (E'.eqOn_morIso_of_functor hF' σ)
    (hΨ.eqOn_loc hpbΨ hfT'.isScSmooth.1 a) (hΦ.eqOn_loc hpbΦ hfT'.isScSmooth.1 a)
    (hΨ.mem_locSet a) (hΦ.mem_locSet a) rfl (mem_tgtSet hσt) (E'.morIso_ϕ_eq hσs hσt) rfl hs
    (hΨ.smooth_obj hs) (hΦ.smooth_obj hs) hG) o

/-- **`Φ_*` and `Ψ_*` agree on `|O_f|` when `|Φ| = |Ψ|`**, for a target with the local
regularity property (Definition 8.4.2 on germs, `IsLRGerm`): the point `(a, o)` goes to
`(ϕ(a), …)` and `(ψ(a), …)`, related by the morphism `α_a` of Proposition 10.4.7. -/
theorem orRelLoc_orSpaceMapLoc_of_isLRGerm (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (hE' : E'.IsLRGerm)
    (p : OrSpaceLoc hX hfT) :
    E'.OrRelLoc hX' hF' hfT' (hΦ.orSpaceMapLoc hpbΦ hX hX' hfT hfT' p)
      (hΨ.orSpaceMapLoc hpbΨ hX hX' hfT hfT' p) := by
  set a := X.PObj.smoothVal p.1 with ha
  have hs : a ∈ X.PObj.smoothSet := X.PObj.smoothVal_mem p.1
  obtain ⟨R, -, α, hα, hfam⟩ :=
    EpStrongBundle.proposition_10_4_7_of_isLRGerm hΦ hΨ hΦΨ hE' a isOpen_univ (mem_univ a)
  have hG := germ_of_family hΦ hΨ R.isOpen_U hα.continuousOn hfam R.mem_U
  obtain ⟨hσs, hσt, -⟩ := hfam a R.mem_U
  refine ⟨α a, hσs, hσt, ?_⟩
  change E'.orMorLoc hF' hfT' (α a) hσs hσt (hΦ.smooth_obj hs) (hΨ.smooth_obj hs)
      ((hΦ.orEqvLoc hpbΦ hfT hfT' _ hs).symm p.2) =
    (hΨ.orEqvLoc hpbΨ hfT hfT' _ hs).symm p.2
  rw [Equiv.eq_symm_apply, orEqvLoc_of_germ hΦ hΨ hF' hpbΦ hpbΨ hfT hfT' (α a) hσs hσt hG,
    Equiv.apply_symm_apply]

/-- **Theorem 12.5.7 for strong bundle equivalences with the same orbit map**: if
`|Φ| = |Ψ| : |W| → |W'|` and `W'` has the local regularity property (Definition 8.4.2 on germs,
`IsLRGerm`), then `|Φ|_* = |Ψ|_*` on `|O_f|`, for `f = Φ^* f' = Ψ^* f'`. -/
theorem orbitOrMapLoc_eq_of_isLRGerm (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (hE' : E'.IsLRGerm)
    (c : Quot (E.OrRelLoc hX hF hfT)) :
    hΦ.orbitOrMapLoc hF hF' hpbΦ hX hX' hfT hfT' c = hΨ.orbitOrMapLoc hF hF' hpbΨ hX hX' hfT hfT' c
        := by
  induction c using Quot.ind with
  | mk p =>
    exact Quot.sound
      (orRelLoc_orSpaceMapLoc_of_isLRGerm hΦ hΨ hF' hpbΦ hpbΨ hX hX' hfT hfT' hΦΨ hE' p)

end EpStrongBundle.IsStrongBundleEquivalence

end Germ

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
  {E₂ : EpStrongBundle X₂ B₂} {E₃ : EpStrongBundle X₃ B₃}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ₁ : EpFunctor X₁ X} {Φ₁ : EpFunctor E₁.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X₁ X'} {Φ₂ : EpFunctor E₁.toEpGroupoid E'.toEpGroupoid}
  {γ₁ : EpFunctor X₂ X} {Γ₁ : EpFunctor E₂.toEpGroupoid E.toEpGroupoid}
  {γ₂ : EpFunctor X₂ X'} {Γ₂ : EpFunctor E₂.toEpGroupoid E'.toEpGroupoid}
  {η₁ : EpFunctor X₃ X₁} {H₁ : EpFunctor E₃.toEpGroupoid E₁.toEpGroupoid}
  {η₂ : EpFunctor X₃ X₂} {H₂ : EpFunctor E₃.toEpGroupoid E₂.toEpGroupoid}
  (h₁ : E₁.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E₁.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  (g₁ : E₂.IsStrongBundleEquivalence E γ₁ Γ₁) (g₂ : E₂.IsStrongBundleEquivalence E' γ₂ Γ₂)
  (hH₁ : E₃.IsStrongBundleEquivalence E₁ η₁ H₁) (hH₂ : E₃.IsStrongBundleEquivalence E₂ η₂ H₂)
  (ζ₁ : E₃.StrongBundleNatTrans E (γ₁.comp η₂) (ϕ₁.comp η₁) (Γ₁.comp H₂) (Φ₁.comp H₁))
  {f : Obj → W} {f' : Obj' → W'} {f₁ : Obj₁ → V₁} {f₂ : Obj₂ → V₂} {f₃ : Obj₃ → V₃}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF₁ : E₁.IsScFredholmSectionFunctor f₁) (hF₂ : E₂.IsScFredholmSectionFunctor f₂)
  (hF₃ : E₃.IsScFredholmSectionFunctor f₃)
  (hpb₁ : f₁ = h₁.pullback f) (hpb₂ : f₁ = h₂.pullback f')
  (hqb₁ : f₂ = g₁.pullback f) (hqb₂ : f₂ = g₂.pullback f')
  (hpbH₁ : f₃ = hH₁.pullback f₁) (hpbH₂ : f₃ = hH₂.pullback f₂)
  (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame) (hX₁ : X₁.PObj.IsTame) (hX₂ : X₂.PObj.IsTame) (hX₃ :
  X₃.PObj.IsTame) (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f') (hfT₁
      : B₁.IsScFredholmSectionTame f₁) (hfT₂ : B₂.IsScFredholmSectionTame f₂) (hfT₃ :
          B₃.IsScFredholmSectionTame f₃)

include ζ₁ hH₁ hH₂ hF₃ hpbH₁ hpbH₂ hX₃ hfT₃ in
/-- **Theorem 12.5.7, two diagrams with the same map of orbit spaces**, p. 595 (2017:
Theorem 12.12): let `W ←Φ₁– V₁ –Φ₂→ W'` and `W ←Γ₁– V₂ –Γ₂→ W'` be diagrams of strong bundle
equivalences with `Φ₁^* f = Φ₂^* f'`, `Γ₁^* f = Γ₂^* f'`, and `H₁ : V₃ → V₁`, `H₂ : V₃ → V₂`
strong bundle equivalences with `Γ₁ ∘ H₂ ≃ Φ₁ ∘ H₁` (Definition 10.4.8) and
`|Φ₂ ∘ H₁| = |Γ₂ ∘ H₂|` on `|V₃|`.  If `W'` has the local regularity property (Definition 8.4.2
on germs, `IsLRGerm`), the two diagrams induce the same map `|O_f| → |O_{f'}|`. -/
theorem theorem_12_5_7_rep_indep_loc_of_isLRGerm
    (horb : (Φ₂.comp H₁).orbitMap = (Γ₂.comp H₂).orbitMap) (hE' : E'.IsLRGerm)
    (x : Quot (E.OrRelLoc hX hF hfT)) :
    (Equiv.ofBijective _ (h₂.orbitOrMapLoc_bijective hF₁ hF' hpb₂ hX₁ hX' hfT₁ hfT'))
      ((Equiv.ofBijective _ (h₁.orbitOrMapLoc_bijective hF₁ hF hpb₁ hX₁ hX hfT₁ hfT)).symm x) =
    (Equiv.ofBijective _ (g₂.orbitOrMapLoc_bijective hF₂ hF' hqb₂ hX₂ hX' hfT₂ hfT'))
      ((Equiv.ofBijective _ (g₁.orbitOrMapLoc_bijective hF₂ hF hqb₁ hX₂ hX hfT₂ hfT)).symm x) := by
  have k₁ := h₁.comp hH₁
  have k₂ := h₂.comp hH₁
  have l₁ := g₁.comp hH₂
  have l₂ := g₂.comp hH₂
  have hk₁ : f₃ = k₁.pullback f := pullback_comp_of hH₁ h₁ hF hpbH₁ hpb₁
  have hk₂ : f₃ = k₂.pullback f' := pullback_comp_of hH₁ h₂ hF' hpbH₁ hpb₂
  have hl₁ : f₃ = l₁.pullback f := pullback_comp_of hH₂ g₁ hF hpbH₂ hqb₁
  have hl₂ : f₃ = l₂.pullback f' := pullback_comp_of hH₂ g₂ hF' hpbH₂ hqb₂
  -- both sides through the middle `V₃`
  have e₁ := theorem_12_5_7_refinement_loc h₁ h₂ k₁ k₂ hH₁
    (StrongBundleNatTrans.refl k₁.isStrongBundleFunctor)
    (StrongBundleNatTrans.refl k₂.isStrongBundleFunctor) hF hF' hF₁ hF₃ hpb₁ hpb₂ hpbH₁ hk₁ hk₂
    hX hX' hX₁ hX₃ hfT hfT' hfT₁ hfT₃ x
  have e₂ := theorem_12_5_7_refinement_loc g₁ g₂ l₁ l₂ hH₂
    (StrongBundleNatTrans.refl l₁.isStrongBundleFunctor)
    (StrongBundleNatTrans.refl l₂.isStrongBundleFunctor) hF hF' hF₂ hF₃ hqb₁ hqb₂ hpbH₂ hl₁ hl₂
    hX hX' hX₂ hX₃ hfT hfT' hfT₂ hfT₃ x
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  set d₁ := Equiv.ofBijective _ (k₁.orbitOrMapLoc_bijective hF₃ hF hk₁ hX₃ hX hfT₃ hfT)
  set d₂ := Equiv.ofBijective _ (l₁.orbitOrMapLoc_bijective hF₃ hF hl₁ hX₃ hX hfT₃ hfT)
  obtain ⟨c, rfl⟩ := d₂.surjective x
  have hc : d₁ c = d₂ c :=
    (orbitOrMapLoc_nat l₁ k₁ ζ₁ hF₃ hF hl₁ hk₁ hX₃ hX hfT₃ hfT c).symm
  rw [← hc, Equiv.symm_apply_apply, hc, Equiv.symm_apply_apply]
  exact orbitOrMapLoc_eq_of_isLRGerm k₂ l₂ hF₃ hF' hk₂ hl₂ hX₃ hX' hfT₃ hfT' horb hE' c

end EpStrongBundle.IsStrongBundleEquivalence

end Rep

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' : SEP.{u}}

namespace SDiagram

variable {D D' : SDiagram A A'} (hΨ : SEP.equivalences D.Ψ) (hΨ' : SEP.equivalences D'.Ψ)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hff'' : D'.hΦ.pullback f = (sbe hΨ').pullback f')
  (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f')

include hff'' in
/-- **Theorem 12.5.7 for diagrams with the same map of orbit spaces**, p. 595 (2017:
Theorem 12.12): if `W'` has the local regularity property (Definition 8.4.2 on germs, `IsLRGerm`),
diagrams `D, D'` with both legs strong bundle equivalences and `|D| = |D'| : |W| → |W'|` induce
the same map `|O_f| → |O_{f'}|`.  The diagrams need not be equivalent. -/
theorem orbitOrMapLoc_eq_of_isLRGerm (h : D.orbitMap = D'.orbitMap) (hA' : A'.E.IsLRGerm) :
    D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT' = D'.orbitOrMapLoc hΨ' hF hF' hff'' hX hX' hfT
        hfT' := by
  -- the weak fibred product `V ×_W V'` of the left legs
  obtain ⟨hZ, hnat, -, -⟩ := SBWeakFibredProduct.theorem_10_2_2 D.isEquivalence_Φ D'.Φ
  have hXr := SBWeakFibredProduct.theorem_10_2_2_right D.isEquivalence_Φ D'.Φ D'.isEquivalence_Φ
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
  have k₁ := D.hΦ.comp (sbe hXr)
  have hs : IsSection A.P f := hF.2.isScSmooth.1
  have hF₃ : (SBWeakFibredProduct.wfpSEP D.isEquivalence_Φ D'.Φ).E.IsScFredholmSectionFunctor
      (k₁.pullback f) := (theorem_10_4_5_fred k₁).2.1 hF
  have hpbH₁ : k₁.pullback f = (sbe hXr).pullback (D.hΦ.pullback f) :=
    (proposition_10_4_4 (sbe hXr) D.hΦ).1 f hs
  have hpbH₂ : k₁.pullback f = (sbe hZ).pullback (D'.hΦ.pullback f) := by
    rw [← (proposition_10_4_4 (sbe hZ) D'.hΦ).1 f hs]
    exact proposition_10_4_2 k₁ (D'.hΦ.comp (sbe hZ)) hnat.orbitMap_eq hF.1
  funext x
  exact theorem_12_5_7_rep_indep_loc_of_isLRGerm D.hΦ (sbe hΨ) D'.hΦ (sbe hΨ') (sbe hXr) (sbe hZ)
    ζ₁ hF hF' (D.isScFredholm_pullback hF) (D'.isScFredholm_pullback hF) hF₃ rfl hff' rfl hff''
    hpbH₁ hpbH₂ hX hX' (D.isTame_B hX) (D'.isTame_B hX)
        (k₁.isEquivalence_base.isLocalScDiffeo_obj.isTame hX) hfT hfT'
            (D.isScFredholmSectionTame_pullback hfT) (D'.isScFredholmSectionTame_pullback hfT)
                (k₁.isScFredholmSectionTame_pullback hfT) horb hA' x

end SDiagram

namespace GenSBMap

variable {F G : GenSBMap A A'} (hFi : F.IsGeneralizedIso) (hGi : G.IsGeneralizedIso)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
  (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hf' : f' = pushforward hFi f) (hg' : f' = pushforward hGi f)
  (hX : A.X.PObj.IsTame) (hX' : A'.X.PObj.IsTame) (hfT : A.B.IsScFredholmSectionTame f) (hfT' :
  A'.B.IsScFredholmSectionTame f')

/-- **`|f̄|_*` depends only on `|f̄|`**: for generalized strong bundle isomorphisms
`f̄, ḡ : W → W'` with `|f̄| = |ḡ|` and `f̄_* f = ḡ_* f = f'`, and a target with the local
regularity property (Definition 8.4.2 on germs, `IsLRGerm`), the maps `|O_f| → |O_{f'}|` agree. -/
theorem orbitOrMapLoc_eq_of_isLRGerm (horb : F.orbitMap = G.orbitMap) (hA' : A'.E.IsLRGerm) :
    orbitOrMapLoc hFi hF hF' hf' hX hX' hfT hfT' = orbitOrMapLoc hGi hF hF' hg' hX hX' hfT hfT' :=
        by
  rw [orbitOrMapLoc_eq hFi hF hF' hf' hX hX' hfT hfT' (cls_rep hFi),
    orbitOrMapLoc_eq hGi hF hF' hg' hX hX' hfT hfT' (cls_rep hGi)]
  refine SDiagram.orbitOrMapLoc_eq_of_isLRGerm _ _ hF hF' _ _ hX hX' hfT hfT' ?_ hA'
  have e₁ : (rep hFi).orbitMap = F.orbitMap := congrArg GenSBMap.orbitMap (cls_rep hFi)
  have e₂ : (rep hGi).orbitMap = G.orbitMap := congrArg GenSBMap.orbitMap (cls_rep hGi)
  exact e₁.trans (horb.trans e₂.symm)

include hX hX' in
/-- **Theorem 12.5.7 (2), independence of the generalized isomorphism**, p. 595: let `o`, `o'`
be families of orientations invariant under the morphisms, `f̄, ḡ : W → W'` generalized strong
bundle isomorphisms with `|f̄| = |ḡ|` and `f̄_* f = ḡ_* f = f'`, and let `W'` have the local
regularity property (Definition 8.4.2 on germs, `IsLRGerm`).  If `o'` corresponds to `o` over the
middle of one diagram `D` representing `f̄`, it corresponds to `o` over the middle of every
diagram `D'` representing `ḡ`. -/
theorem theorem_12_5_7_two_corr_indep_loc_of_isLRGerm (horb : F.orbitMap = G.orbitMap)
    (hA' : A'.E.IsLRGerm) {D D' : SDiagram A A'} (hD : D.cls = F) (hD' : D'.cls = G)
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
    (sbe (equivalences_Ψ_of_cls hGi hD')).orEqvLoc (pullback_eq_of_cls' hGi hD' hF.1 hg')
        (D'.isScFredholmSectionTame_pullback hfT) hfT' v hv
        (o' (D'.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hGi hD')).smooth_obj hv)) =
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
  have e₂ := D'.orbitOrMapLoc_mk (equivalences_Ψ_of_cls hGi hD') hF hF'
    (pullback_eq_of_cls' hGi hD' hF.1 hg') hX hX' hfT hfT' v hv (o _ hs)
  have k₁ := orbitOrMapLoc_eq hFi hF hF' hf' hX hX' hfT hfT' hD
  have k₂ := orbitOrMapLoc_eq hGi hF hF' hg' hX hX' hfT hfT' hD'
  have k₀ := orbitOrMapLoc_eq_of_isLRGerm hFi hGi hF hF' hf' hg' hX hX' hfT hfT' horb hA'
  have e₃ := e₁.symm.trans ((congrFun k₁ _).symm.trans ((congrFun k₀ _).trans
    ((congrArg _ hcls).trans ((congrFun k₂ _).trans e₂))))
  obtain ⟨β, hb, hb', hβ⟩ := A'.E.orRelLoc_of_quot_eq hX' hF' hfT' e₃
  have h5 := (Equiv.symm_apply_eq _).2 (hcorr a ha).symm
  have h3 := ho' β hb hb' (A'.X.PObj.smoothVal_mem _) (A'.X.PObj.smoothVal_mem _)
  exact (Equiv.eq_symm_apply _).1 (h3.symm.trans ((congrArg _ h5.symm).trans hβ))

end GenSBMap

end SBLocalization

end Polyfold
