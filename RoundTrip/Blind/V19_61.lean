import Polyfold
/-! Blind formalization of V19_61 (the text's §19.6, Theorem 19.6.13, p. 900 of the Springer 2021
book; 2017: Theorem 19.8).

Text: if `T` is metrizable, `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` has a natural strong bundle structure for which
`s`, `t` are local strong bundle isomorphisms and `u`, `ι`, `m` are strong bundle maps.

Choices:
- Setting: universe `0`: a groupoidal category `C`, a functor `μ : S → Ban` (`C.BanFunctor`), a
  basic strong bundle construction `Bs = (F̄, 𝓕̄)` (`C.BasicStrongBundleConstruction μ`, Definition
  19.6.6) with `Bs.base.U.HasClassUniformizers` (needed for `T` to be a topology, as in the blind
  V19_12) and `T` (the vocabulary's `Bs.base.natTop hB`, Definition 19.2.1) metrizable; `F̄` is
  any representative of `𝓕̄` (`⟦Fbar⟧ = Bs.𝓕`), `F = Fbar.toTD` its underlying transition data.
  `Ψ̄, Ψ̄', Ψ̄''` range over the members of `F̄` (`Bs.U.Unif`), `Ψ = baseUnif Ψ̄` etc.
- Spaces: the base `M(Ψ, Ψ')` is the M-polyfold of Theorem 19.5.1 (the vocabulary's
  `Fbar.toTD.transPolyfold`, on `T^F_{Ψ,Ψ'}`); the total space `M(Ψ̄, Ψ̄')` carries its natural
  topology (the vocabulary's `MB Fbar Ψ̄ Ψ̄'`, the topology `T^{F̄}` of the lifts `F̄` viewed as
  transition data of `E_μ`); `p` = the vocabulary's `projBar` ((19.13), `(a, φ, a') ↦
  (p(a), φ, p'(a'))`).  The strong bundles `p : K → O` of the uniformizers are `(strU Ψ̄).B`.
- "has a natural strong bundle structure for which ...": there is a family `Kb Ψ̄ Ψ̄'` of strong
  bundle structures (`Polyfold.StrongBundle`) on `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` with the listed
  properties.  I do not pin "natural" further: a structure for which `s̄` is a local strong bundle
  isomorphism onto `K` covering `s` is determined (up to equivalent atlases) by that property, and
  it is the structure of the text (transported along `H` from `s*K`).  I did not use the
  project's `bundleBar`, `altH…` or `Theorem_19_6_13_Statement`.
- "local strong bundle isomorphism" (`IsLocalSBIso`, my definition): a strong bundle map
  (`StrongBundle.IsStrongBundleMap`, covering the base map) such that every point of the base has
  an open neighbourhood `U` and an open `U'` with the map a strong bundle isomorphism
  `Y|U → Y'|U'` (`StrongBundle.IsStrongBundleIsoOn`).
- Maps: `s̄(a, φ, a') = a` covering `s(o, φ, o') = o`; `t̄(a, φ, a') = a'` covering `t`;
  `ū(a) = (a, 1, a)` from `K` covering `u(o) = (o, 1, o)`; `ῑ(a, φ, a') = (a', φ⁻¹, a)` covering
  `ι`; `m̄` = the vocabulary's `mBar` (p. 904: `((h', h), h̄) ↦ h̄' ∘ h̄` with `h̄'` the
  element over `h'` with source `t(h̄)`) on the pull-back `pr₂*M(Ψ̄, Ψ̄')` over the fibred product
  `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` (its M-polyfold structure = the vocabulary's `BFPpoly`), covering the
  multiplication `m` (`mulBase`).  The pull-back bundle is `StrongBundle.pullback` along `pr₂`;
  it needs a proof that `pr₂` is sc-smooth, which I quantify over (proof-irrelevant).
- The linear structures on the fibres `p⁻¹(h)` (and on those of the pull-back) are the ones the
  project's instances supply (found by instance search; I did not inspect them); the text's is
  the one making `H : K_{s(h)} → p⁻¹(h)` linear.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_61
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

/-- Theorem 19.6.13: the natural strong bundle `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (μ : C.BanFunctor) (Bs : C.BasicStrongBundleConstruction μ)
    (hB : Bs.base.U.HasClassUniformizers)
    (_hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (Bs.base.natTop hB))
    (Fbar : Bs.U.BundleTransitionData),
    Quotient.mk (BundleTransitionData.setoid Bs.U) Fbar = Bs.𝓕 →
    ∃ Kb : ∀ Ψ Ψ' : Bs.U.Unif,
        StrongBundle (Fbar.toTD.transPolyfold (Bs.U.baseUnif Ψ) (Bs.U.baseUnif Ψ'))
          (projBar Fbar Ψ Ψ'),
      -- `s` and `t` are local strong bundle isomorphisms
      (∀ Ψ Ψ' : Bs.U.Unif,
        IsLocalSBIso (Kb Ψ Ψ') (Bs.U.strU Ψ).B
          (fun k : MS Fbar Ψ Ψ' => k.src) (fun h : MB Fbar Ψ Ψ' => h.src) ∧
        IsLocalSBIso (Kb Ψ Ψ') (Bs.U.strU Ψ').B
          (fun k : MS Fbar Ψ Ψ' => k.tgt) (fun h : MB Fbar Ψ Ψ' => h.tgt)) ∧
      -- `u` is a strong bundle map
      (∀ Ψ : Bs.U.Unif,
        (Bs.U.strU Ψ).B.IsStrongBundleMap (Kb Ψ Ψ)
          (fun o => (GroupoidStr.TransitionSet.unit o : MS Fbar Ψ Ψ))
          (fun a => (GroupoidStr.TransitionSet.unit a : MB Fbar Ψ Ψ))) ∧
      -- `ι` is a strong bundle map
      (∀ Ψ Ψ' : Bs.U.Unif,
        (Kb Ψ Ψ').IsStrongBundleMap (Kb Ψ' Ψ)
          (fun k : MS Fbar Ψ Ψ' => (GroupoidStr.TransitionSet.inv k : MS Fbar Ψ' Ψ))
          (fun h : MB Fbar Ψ Ψ' => (GroupoidStr.TransitionSet.inv h : MB Fbar Ψ' Ψ))) ∧
      -- `m` is a strong bundle map (on the pull-back `pr₂*M(Ψ̄, Ψ̄')`)
      (∀ (Ψ Ψ' Ψ'' : Bs.U.Unif)
        (hpr : (BFPpoly Fbar Ψ Ψ' Ψ'').IsScSmoothMap
          (Fbar.toTD.transPolyfold (Bs.U.baseUnif Ψ) (Bs.U.baseUnif Ψ')) (pr₂BFP Fbar Ψ Ψ' Ψ'')),
        ((Kb Ψ Ψ').pullback hpr).IsStrongBundleMap (Kb Ψ Ψ'')
          (mulBase Fbar Ψ Ψ' Ψ'') (mBar Fbar Ψ Ψ' Ψ''))

end RoundTrip.V19_61
