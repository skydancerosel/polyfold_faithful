import Polyfold.Chapter10.FredholmEquivalence
import Polyfold.Chapter10.StrongBundleEquivalence
import Polyfold.Chapter2.StrongBundleRestrict
import Polyfold.Chapter5.P3R_Reflexive2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 16.3.12,
p. 727 (2017: Definition 16.24), the parenthetical "equivalent structures then also have", with
Definition 5.1.4, p. 207, and Definition 10.4.1, p. 496.  Numbers and pages are the 2021 text's.

# Reflexive `(0, 1)`-fibres pull back along local strong bundle isomorphisms

## What is formalized

* `StrongBundle.LocalIso.exists_reflexive_chart`: for a local strong bundle isomorphism
  `Φ : Y|U → Y'|U'` covering `ϕ`, a compatible chart of `Y'` at `ϕ(x)` with `F₁` reflexive gives
  one of `Y` at `x` (`x ∈ U`): restrict the chart to `U'` (`StrongBundleChart.restrict`) and
  transport it by `Φ` (`LocalIso.transportChart`); the fibre model `F` is unchanged.
* `StrongBundle.hasReflexiveFibers_of_isStrongBundleIsoOn`: if every point of `X` lies in the
  domain of such an isomorphism, `Y' → X'` with reflexive `(0, 1)`-fibres gives `Y → X` with
  reflexive `(0, 1)`-fibres.
* `EpStrongBundle.IsStrongBundleEquivalence.hasReflexiveFibers_of`: **the pull direction of the
  parenthetical of Definition 16.3.12** at the level of Definition 10.4.1: for a strong bundle
  equivalence `Φ : W → W'` covering `ϕ`, reflexive `(0, 1)`-fibres of `W'` give those of `W`
  ((2) of Definition 10.4.1 for objects).

The push direction (from `W` to `W'`) uses in addition the essential surjectivity of `ϕ` and the
transport of charts along the action `μ` over a sheet of morphisms; it is not done here.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace StrongBundle

section Pull

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {U : Set X} {U' : Set X'}

/-- **A reflexive chart pulls back along a local strong bundle isomorphism**: a compatible
strong bundle chart of `Y'` at `ϕ(x)` with `F₁` reflexive gives one of `Y` at `x ∈ U`, with the
same fibre model. -/
theorem LocalIso.exists_reflexive_chart (L : LocalIso B B' U U') {x : X} (hx : x ∈ U)
    {c' : StrongBundleChart PX' P'} (hc' : B'.IsChart c') (hxc' : L.ϕ x ∈ c'.φ.source)
    (hr : IsReflexive (c'.F 1)) :
    ∃ c : StrongBundleChart PX P, B.IsChart c ∧ x ∈ c.φ.source ∧ IsReflexive (c.F 1) := by
  have hs : c'.φ.source ∩ U' ⊆ c'.φ.source := inter_subset_left
  have hso : IsOpen (c'.φ.source ∩ U') := c'.φ.isOpen_source.inter L.isOpen_U'
  set c'' := c'.restrict hs hso
  have hc'' : B'.IsChart c'' := fun d hd => (hc' d hd).restrict_left hs hso
  have hsub : c''.φ.source ⊆ U' := inter_subset_right
  refine ⟨L.transportChart c'' hsub, L.isChart_transportChart c'' hsub hc'', ?_, hr⟩
  rw [L.transportChart_φ_source]
  exact ⟨hx, hxc', L.base.mapsTo hx⟩

/-- **Reflexive `(0, 1)`-fibres pull back along local strong bundle isomorphisms**: if every
point of `X` lies in the domain `U` of a strong bundle isomorphism `Y|U → Y'|U'` covering `f`,
and `Y' → X'` has reflexive `(0, 1)`-fibres (Definition 5.1.4), so has `Y → X`. -/
theorem hasReflexiveFibers_of_isStrongBundleIsoOn {f : X → X'} {Φ : Y → Y'}
    {h : B.IsStrongBundleMap B' f Φ}
    (hloc : ∀ x : X, ∃ (U : Set X) (U' : Set X'), x ∈ U ∧ B.IsStrongBundleIsoOn B' h U U')
    (hB' : B'.HasReflexiveFibers) : B.HasReflexiveFibers := fun x => by
  obtain ⟨U, U', hx, hi⟩ := hloc x
  obtain ⟨c', hc', hxc', hr⟩ := hB' (f x)
  exact hi.toLocalIso.exists_reflexive_chart hx hc' hxc' hr

end Pull

end StrongBundle

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

/-- **Reflexive `(0, 1)`-fibres pull back along a strong bundle equivalence** (Definition 10.4.1,
used for the parenthetical of Definition 16.3.12, p. 727): if `Φ : W → W'` is a strong bundle
equivalence and `W' → X'` has reflexive `(0, 1)`-fibres, so has `W → X`. -/
theorem IsStrongBundleEquivalence.hasReflexiveFibers_of {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hB' : B'.HasReflexiveFibers) : B.HasReflexiveFibers :=
  StrongBundle.hasReflexiveFibers_of_isStrongBundleIsoOn h.isLocalStrongBundleIso_obj hB'

end EpStrongBundle

end Polyfold
