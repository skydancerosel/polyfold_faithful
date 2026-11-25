import Polyfold
/-! Blind formalization of V19_62 (the text's §19.6, Theorem 19.6.13, the multiplication map,
p. 900 of the Springer 2021 book; 2017: Theorem 19.8).

Text: the multiplication map is a strong bundle map.

Choices:
- This is the last clause of Theorem 19.6.13 (blind V19_61), stated on its own; the setting and
  the readings are those of V19_61: universe `0`, a groupoidal category `C`, `μ : S → Ban`, a
  basic strong bundle construction `Bs` with `Bs.base.U.HasClassUniformizers` and `T` (the
  vocabulary's `Bs.base.natTop hB`) metrizable (the theorem's hypothesis), any representative
  `F̄` of `𝓕̄`; base `M(Ψ, Ψ')` = `Fbar.toTD.transPolyfold` (Theorem 19.5.1), total space
  `M(Ψ̄, Ψ̄')` = the vocabulary's `MB`, projection `p` = `projBar`.
- "the multiplication map" is a strong bundle map for THE natural strong bundle structure of the
  theorem.  I express "natural" as in V19_61 by its characterizing property: `s̄` and `t̄` are
  local strong bundle isomorphisms onto the bundles `p : K → O` of the uniformizers
  (`IsLocalSBIso`, my definition: a strong bundle map which over small open sets of the base is a
  strong bundle isomorphism `StrongBundle.IsStrongBundleIsoOn`).  The claim: there is a family of
  strong bundle structures on `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` with this property for which `m̄` is a
  strong bundle map.
- `m̄` = the vocabulary's `mBar` (p. 904: `((h', h), h̄) ↦ h̄' ∘ h̄`, `h̄'` the element over `h'`
  with source `t(h̄)`), defined on the pull-back `pr₂*M(Ψ̄, Ψ̄')` over the fibred product
  `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` (M-polyfold structure = the vocabulary's `BFPpoly`), covering
  `m` (`mulBase`); the pull-back bundle is `StrongBundle.pullback` along `pr₂` (the sc-smoothness
  proof of `pr₂` is quantified over).  This identification of `M(Ψ̄', Ψ̄'') ₛ×ₜ M(Ψ̄, Ψ̄')` with
  `pr₂*M(Ψ̄, Ψ̄')` is the text's (p. 904).
- The fibre linear structures are those supplied by the project's instances.  I did not use the
  project's `bundleBar`, `mulBundle` or `Theorem_19_6_13_Statement`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_62
open Polyfold
open GroupoidalCategory.StrongBundleUniformizerConstruction

/-- A strong bundle map `Φ : Y → Y'` covering `f` which is locally (over open sets of the base) a
strong bundle isomorphism. -/
def IsLocalSBIso {X Y X' Y' : Type}
    [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
    [∀ x : X, AddCommGroup (P ⁻¹' {x})] [∀ x : X, Module ℝ (P ⁻¹' {x})]
    [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
    [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
    [∀ x : X', AddCommGroup (P' ⁻¹' {x})] [∀ x : X', Module ℝ (P' ⁻¹' {x})]
    (B₁ : StrongBundle PX P) (B₂ : StrongBundle PX' P') (f : X → X') (Φ : Y → Y') : Prop :=
  ∃ hΦ : B₁.IsStrongBundleMap B₂ f Φ, ∀ x : X, ∃ U : Set X, ∃ U' : Set X',
    IsOpen U ∧ x ∈ U ∧ IsOpen U' ∧ B₁.IsStrongBundleIsoOn B₂ hΦ U U'

/-- Theorem 19.6.13, last clause: the multiplication `m̄` is a strong bundle map. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (μ : C.BanFunctor) (Bs : C.BasicStrongBundleConstruction μ)
    (hB : Bs.base.U.HasClassUniformizers)
    (_hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (Bs.base.natTop hB))
    (Fbar : Bs.U.BundleTransitionData),
    Quotient.mk (BundleTransitionData.setoid Bs.U) Fbar = Bs.𝓕 →
    ∃ Kb : ∀ Ψ Ψ' : Bs.U.Unif,
        StrongBundle (Fbar.toTD.transPolyfold (Bs.U.baseUnif Ψ) (Bs.U.baseUnif Ψ'))
          (projBar Fbar Ψ Ψ'),
      -- the structure is the natural one: `s` and `t` are local strong bundle isomorphisms
      (∀ Ψ Ψ' : Bs.U.Unif,
        IsLocalSBIso (Kb Ψ Ψ') (Bs.U.strU Ψ).B
          (fun k : MS Fbar Ψ Ψ' => k.src) (fun h : MB Fbar Ψ Ψ' => h.src) ∧
        IsLocalSBIso (Kb Ψ Ψ') (Bs.U.strU Ψ').B
          (fun k : MS Fbar Ψ Ψ' => k.tgt) (fun h : MB Fbar Ψ Ψ' => h.tgt)) ∧
      -- `m` is a strong bundle map (on the pull-back `pr₂*M(Ψ̄, Ψ̄')`)
      (∀ (Ψ Ψ' Ψ'' : Bs.U.Unif)
        (hpr : (BFPpoly Fbar Ψ Ψ' Ψ'').IsScSmoothMap
          (Fbar.toTD.transPolyfold (Bs.U.baseUnif Ψ) (Bs.U.baseUnif Ψ')) (pr₂BFP Fbar Ψ Ψ' Ψ'')),
        ((Kb Ψ Ψ').pullback hpr).IsStrongBundleMap (Kb Ψ Ψ'')
          (mulBase Fbar Ψ Ψ' Ψ'') (mBar Fbar Ψ Ψ' Ψ''))

end RoundTrip.V19_62
