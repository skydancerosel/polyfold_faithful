import Polyfold.Chapter12.LocalOrientationGeneralizedIso
import Polyfold.Chapter12.LocalOrientationEquivalenceComparison
import Polyfold.Chapter12.OrientationGeneralizedIsoTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, Theorem 12.5.7 for Chapter 10's diagrams, in the two descriptions of `|O_f|`.

# The map `|D|_*` of a diagram: local and global sc⁺-sections

## The text, paraphrased

A diagram `W ←Φ– V –Ψ→ W'` of strong bundle equivalences with `Φ^* f = Ψ^* f'` gives
`|D|_* = |Ψ|_* ∘ |Φ|_*⁻¹ : |O_f| → |O_{f'}|` (proof of Theorem 12.5.7).

## What is formalized

* `IsStrongBundleEquivalence.orxLocEquiv_pushOr`: the push-forward of a family of orientations
  along a strong bundle equivalence (`pushOr`) and the push-forward for the local orientation
  sets (`pushOrLoc`) correspond under `orxLocEquiv`.
* `SDiagram.orbitOrMapLoc_orbitLocHomeomorph`: when the source admits sc-smooth bump functions
  (then so does the middle, `SDiagram.admitsBumpFunctions_B`) and the target does, the map
  `|D|_*` made with sc⁺-sections over the whole object spaces (`SDiagram.orbitOrMap`) and the
  one made with the local orientation sets (`SDiagram.orbitOrMapLoc`) correspond under the
  homeomorphisms `orbitLocHomeomorph` of the orbit spaces.  The proof applies the same statement
  for one strong bundle equivalence
  (`IsStrongBundleEquivalence.orbitOrMapLoc_orbitLocHomeomorph`) to the two legs.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Equiv

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
  {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

/-- **Push-forwards of families of orientations correspond**: the image under `orxLocEquiv` of
the push-forward `pushOr o` along a strong bundle equivalence is the push-forward `pushOrLoc`
of the image of `o`. -/
theorem orxLocEquiv_pushOr (o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs) (x : Obj')
    (hs : x ∈ X'.PObj.smoothSet) :
    orxLocEquiv hfT' hsec' x hs (h.pushOr hF hF' hpb hsec hsec' o x hs) =
      h.pushOrLoc hF' hpb hfT hfT' (fun a ha => orxLocEquiv hfT hsec a ha (o a ha)) x hs := by
  change orxLocEquiv hfT' hsec' x hs (E'.orMor hF' hsec' _ _ _ _ hs _) = E'.orMorLoc hF' hfT' _
    _ _ _ hs _
  rw [E'.orxLocEquiv_orMor_apply hF' hfT' hsec']
  congr 1
  rw [Equiv.eq_symm_apply, ← h.orxLocEquiv_orEqv_apply hF hF' hpb hfT hfT' hsec hsec',
    Equiv.apply_symm_apply]

end EpStrongBundle.IsStrongBundleEquivalence

end Equiv

namespace SBLocalization

open SEP EpStrongBundle

variable {A A' : SEP.{u}}

namespace SDiagram

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) {f : A.Obj → A.W}
  {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hff' : D.hΦ.pullback f = (sbe hΨ).pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
  (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hfT : A.B.IsScFredholmSectionTame f) (hX' : A'.X.PObj.IsTame)
  (hbump' : A'.X.PObj.AdmitsBumpFunctions) (hfT' : A'.B.IsScFredholmSectionTame f')

/-- **`|D|_*` in the two descriptions**: the map of a diagram on the orbit spaces made with
sc⁺-sections over the whole object spaces and the map made with the local orientation sets
correspond under the homeomorphisms `orbitLocHomeomorph`, when source and target admit
sc-smooth bump functions. -/
theorem orbitOrMapLoc_orbitLocHomeomorph (c : Quot (A.E.OrRel hF hsec)) :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    haveI := paracompactSpace_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_pullback A'.B
    haveI := paracompactSpace_rn_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A'.B
    D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT'
        (A.E.orbitLocHomeomorph hF hfT hsec hX hbump c) =
      A'.E.orbitLocHomeomorph hF' hfT' hsec' hX' hbump'
        (D.orbitOrMap hΨ hF hF' hff' hsec hsec' c) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  have := paracompactSpace_rn_prod A'.X.PObj
  have := paracompactSpace_rn_pullback A'.B
  have := paracompactSpace_rn_rn_prod A'.X.PObj
  have := paracompactSpace_rn_rn_pullback A'.B
  have := paracompactSpace_rn_prod D.B.X.PObj
  have := paracompactSpace_rn_pullback D.B.B
  have := paracompactSpace_rn_rn_prod D.B.X.PObj
  have := paracompactSpace_rn_rn_pullback D.B.B
  have hF₀ := D.isScFredholm_pullback hF
  have hsec₀ := D.hasScPlusSectionsThrough_B hsec
  have hX₀ := D.isTame_B hX
  have hbump₀ := D.admitsBumpFunctions_B hbump
  have hfT₀ := D.isScFredholmSectionTame_pullback hfT
  set e₁ := Equiv.ofBijective _ (D.hΦ.orbitOrMap_bijective hF₀ hF rfl hsec₀ hsec)
  set e₁' := Equiv.ofBijective _ (D.hΦ.orbitOrMapLoc_bijective hF₀ hF rfl hX₀ hX hfT₀ hfT)
  obtain ⟨d, rfl⟩ := e₁.surjective c
  have hl := D.hΦ.orbitOrMapLoc_orbitLocHomeomorph hF₀ hF rfl hfT₀ hfT hsec₀ hsec hX₀ hbump₀
    hX hbump d
  have hr := (sbe hΨ).orbitOrMapLoc_orbitLocHomeomorph hF₀ hF' hff' hfT₀ hfT' hsec₀ hsec' hX₀
    hbump₀ hX' hbump' d
  have h₁ : D.orbitOrMap hΨ hF hF' hff' hsec hsec' (e₁ d) =
      (sbe hΨ).orbitOrMap hF₀ hF' hff' hsec₀ hsec' d := by
    change (Equiv.ofBijective _ _) (e₁.symm (e₁ d)) = _
    rw [e₁.symm_apply_apply]
    rfl
  have h₂ : ∀ x, D.orbitOrMapLoc hΨ hF hF' hff' hX hX' hfT hfT' (e₁' x) =
      (sbe hΨ).orbitOrMapLoc hF₀ hF' hff' hX₀ hX' hfT₀ hfT' x := fun x => by
    change (Equiv.ofBijective _ _) (e₁'.symm (e₁' x)) = _
    rw [e₁'.symm_apply_apply]
    rfl
  have h₃ : A.E.orbitLocHomeomorph hF hfT hsec hX hbump (e₁ d) =
      e₁' (D.B.E.orbitLocHomeomorph hF₀ hfT₀ hsec₀ hX₀ hbump₀ d) := hl.symm
  rw [h₃, h₂, h₁, hr]

end SDiagram

end SBLocalization

end Polyfold
