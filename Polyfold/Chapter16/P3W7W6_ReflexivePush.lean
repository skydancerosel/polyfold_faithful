import Polyfold.Chapter16.P3W5PC_ReflexivePull
import Polyfold.Chapter16.P3W3V_PolyfoldAuxNorm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 16.3.12,
p. 727 (2017: Definition 16.24), the parenthetical "equivalent structures then also have", with
Definition 5.1.4, p. 207, and Definition 10.4.1, p. 496: **the push direction**, completing part
(i) of gap G.166.  Numbers and pages are the 2021 text's.

# Reflexive `(0, 1)`-fibres are invariant under equivalence

## What is formalized

* `EpStrongBundle.IsStrongBundleEquivalence.hasReflexiveFibers_push`: for a strong bundle
  equivalence `Φ : W → W'` covering `ϕ`, reflexive `(0, 1)`-fibres of `W` give those of `W'`.
  For `x' ∈ X'` pick `x` and `σ : ϕ(x) → x'` (`|ϕ|` is onto); a reflexive chart of `W` at `x`
  is pushed to `ϕ(x)` by the inverse of the local strong bundle isomorphism of Definition
  10.4.1 (2) (`LocalIso.symm`), and moved from `ϕ(x)` to `x'` by the action of `σ`, a local
  strong bundle isomorphism of `W'` (`EpStrongBundle.exists_localIso_mor`).
* `IsStrongBundleEquivalence.hasReflexiveFibers_iff` (both directions).
* `SBLocalization.SDiagram.hasReflexiveFibers_of`, `GenSBMap.hasReflexiveFibers_iff`: along a
  generalized strong bundle isomorphism `[W ← W'' → W']`.
* `StrongPolyfoldBundleStructure.hasReflexiveFibers_of_equiv` and
  **`StrongPolyfoldBundle.hasReflexiveFibers_iff_forall`**: the parenthetical of Definition
  16.3.12, "if one structure of `c̄` has reflexive `1`-fibres, all have".
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpStrongBundle

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

/-- **Reflexive `(0, 1)`-fibres push forward along a strong bundle equivalence** (the push
direction of the parenthetical of Definition 16.3.12, p. 727). -/
theorem IsStrongBundleEquivalence.hasReflexiveFibers_push {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hB : B.HasReflexiveFibers) : B'.HasReflexiveFibers := by
  intro x'
  obtain ⟨ξ, hξ⟩ := h.isEquivalence_base.isHomeomorph_orbitMap.surjective (X'.π x')
  induction ξ using Quotient.inductionOn with | h x => ?_
  have h1 : X'.π (ϕ.obj x) = X'.π x' := hξ
  obtain ⟨σ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
  -- a reflexive chart of `W'` at `ϕ(x)`
  obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
  obtain ⟨c, hc, hxc, hr⟩ := hB x
  set L₀ := hi.toLocalIso
  have hϕx : ϕ.obj x ∈ U' := L₀.base.mapsTo hxU
  have hgx : L₀.symm.ϕ (ϕ.obj x) = x := L₀.base.left_inv x hxU
  obtain ⟨c₁, hc₁, hx₁, hr₁⟩ :=
    L₀.symm.exists_reflexive_chart hϕx hc (by rw [hgx]; exact hxc) hr
  -- move it along `σ : ϕ(x) → x'`
  obtain ⟨V, V', L, hx'V, hLϕ, -⟩ := E'.exists_localIso_mor σ
  rw [ht] at hx'V hLϕ
  exact L.exists_reflexive_chart hx'V hc₁ (by rw [hLϕ, hs]; exact hx₁) hr₁

/-- **Reflexive `(0, 1)`-fibres are invariant under strong bundle equivalences.** -/
theorem IsStrongBundleEquivalence.hasReflexiveFibers_iff {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleEquivalence E' ϕ Φ) :
    B.HasReflexiveFibers ↔ B'.HasReflexiveFibers :=
  ⟨h.hasReflexiveFibers_push, h.hasReflexiveFibers_of⟩

end EpStrongBundle

namespace SBLocalization

open EPLocalization

variable {A A' : SEP.{u}}

/-- **Along a diagram `W ←Φ W'' →Ψ W'` of strong bundle equivalences**, reflexive
`(0, 1)`-fibres of `W` give those of `W'` (pull along `Φ`, push along `Ψ`). -/
theorem SDiagram.hasReflexiveFibers_of (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    (hA : A.B.HasReflexiveFibers) : A'.B.HasReflexiveFibers :=
  (sbe hΨ).hasReflexiveFibers_push (D.hΦ.hasReflexiveFibers_of hA)

/-- **Reflexive `(0, 1)`-fibres are invariant under generalized strong bundle isomorphisms.** -/
theorem GenSBMap.hasReflexiveFibers_iff {F : GenSBMap A A'} (hF : F.IsGeneralizedIso) :
    A.B.HasReflexiveFibers ↔ A'.B.HasReflexiveFibers := by
  set D := GenSBMap.rep hF
  have hΨ := GenSBMap.isEquivalence_rep_Ψ hF
  refine ⟨D.hasReflexiveFibers_of hΨ, fun hA' => ?_⟩
  exact (sbe D.isEquivalence_Φ).hasReflexiveFibers_push ((sbe hΨ).hasReflexiveFibers_of hA')

end SBLocalization

namespace StrongPolyfoldBundleStructure

open SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **Equivalent structures have reflexive `1`-fibres together** (Definition 16.3.3). -/
theorem hasReflexiveFibers_of_equiv {S S' : StrongPolyfoldBundleStructure p} (h : Equiv S S')
    (hS : S.A.E.HasReflexiveFibers) : S'.A.E.HasReflexiveFibers := by
  obtain ⟨F, hF, -, -⟩ := h
  exact (GenSBMap.hasReflexiveFibers_iff hF).1 hS

end StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **2021 Definition 16.3.12, p. 727, the parenthetical** ("equivalent structures then also
have reflexive `1`-fibres"): `(p, c̄)` has reflexive `1`-fibres iff every structure of `c̄` has. -/
theorem hasReflexiveFibers_iff_forall :
    c.HasReflexiveFibers ↔
      ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.E.HasReflexiveFibers := by
  refine ⟨fun ⟨S₀, hS₀, h₀⟩ S hS => ?_, fun h => ?_⟩
  · exact hasReflexiveFibers_of_equiv (Quotient.exact (hS₀.trans hS.symm)) h₀
  · obtain ⟨S, hS⟩ := Quotient.exists_rep c
    exact ⟨S, hS, h S hS⟩

theorem HasReflexiveFibers.of_mem (hc : c.HasReflexiveFibers)
    {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) : S.A.E.HasReflexiveFibers :=
  hasReflexiveFibers_iff_forall.1 hc S hS

end StrongPolyfoldBundle

end Polyfold
