import Polyfold
/-! Blind formalization of V8_24 (the text's Part II, §8.3, Definition 8.3.3 = 2017 Definition
8.6, p. 378 / 2017 p. 274).

Text: a strong bundle functor `Φ : P → P'` between the strong bundles `P : W → X`, `P' : W' → X'`
over the ep-groupoids `X`, `X'` is a functor `Φ : (W, 𝐖) → (W', 𝐖')` between ep-groupoids, linear
on the fibres, covering an sc-smooth functor `(φ, 𝛗) : (X, 𝐗) → (X', 𝐗')`; moreover `Φ` induces
strong bundle maps `Φ : W → W'` and `𝚽 : 𝐖 → 𝐖'` with `P' ∘ Φ = φ ∘ P`.

Choices:
- This item is a definition.  Setting as in my `RoundTrip/Blind/V8_23.lean` (all spaces in
  `Type`; the project's `IsStrongBundleFunctor` puts all of them in one universe), with
  `E : EpStrongBundle X B`, `E' : EpStrongBundle X' B'` (V8_20) and `(φ, 𝛗)` a project
  `EpFunctor X X'` (V7_9).  The ep-groupoids `(W, 𝐖)`, `(W', 𝐖')` are the project's
  `E.toEpGroupoid`, `E'.toEpGroupoid` (characterized in my `RoundTrip/Blind/V8_22.lean`); they need
  paracompactness of `𝐖`, `𝐖'` (instance hypotheses, true), and the pull-back strong bundles
  `𝐖 → 𝐗`, `𝐖' → 𝐗'` need the sc-smoothness `hs`, `hs'` of `s`, `s'` (true), as in V8_20.
- "functor between ep-groupoids": a functor of the underlying groupoids (`GroupoidFunctor`,
  V7_9's `IsFunctorB`), not assumed sc-smooth (the text says "sc-smooth" only of `(φ, 𝛗)`).  My
  `IsSBFunctorB`: the object map is a strong bundle map `W → W'` covering `φ` (for `P`, `P'`), the
  morphism map a strong bundle map `𝐖 → 𝐖'` covering `𝛗` (for the pull-back bundles
  `(ψ, w) ↦ ψ`), with "strong bundle map" the project's `IsStrongBundleMap` (covers, linear on the
  fibres, sc-smooth on `[0]` and `[1]`; trusted as in V8_20); I also write out the covering
  squares `P' ∘ Φ = φ ∘ P` and `𝐏' ∘ 𝚽 = 𝛗 ∘ 𝐏` (implied, but stated in the text).
- B: (a) for an `EpFunctor` `Φ`, the project's `IsStrongBundleFunctor E E' φ Φ` iff its
  underlying functor satisfies `IsSBFunctorB`; (b) every functor satisfying `IsSBFunctorB` is
  sc-smooth, i.e. underlies an `EpFunctor` (so the project's restriction to `EpFunctor`s loses
  nothing).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_24
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]

/-- **Definition 8.3.3**: the functor `Φ : (W, 𝐖) → (W', 𝐖')` is a strong bundle functor
covering `φ`. -/
def IsSBFunctorB (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (φ : EpFunctor X X')
    (hs : X.PMor.IsScSmoothMap X.PObj X.src) (hs' : X'.PMor.IsScSmoothMap X'.PObj X'.src)
    (Φ : GroupoidFunctor E.toEpGroupoid.toGroupoidStr E'.toEpGroupoid.toGroupoidStr) : Prop :=
  -- `Φ : W → W'` is a strong bundle map covering `φ`
  B.IsStrongBundleMap B' φ.obj Φ.obj ∧
  -- `𝚽 : 𝐖 → 𝐖'` is a strong bundle map covering `𝛗`
  (B.pullback hs).IsStrongBundleMap (B'.pullback hs') φ.mor Φ.mor ∧
  -- the covering squares `P' ∘ Φ = φ ∘ P` and `𝐏' ∘ 𝚽 = 𝛗 ∘ 𝐏`
  (∀ w : W, P' (Φ.obj w) = φ.obj (P w)) ∧
  (∀ p : pullbackSpace P X.src, (Φ.mor p).1.1 = φ.mor p.1.1)

end

/-- Definition 8.3.3: the project's strong bundle functors are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)]
    (Obj' Mor' : Type) [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] (X' : EpGroupoid Obj' Mor')
    (W' : Type) [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] (P' : W' → Obj')
    [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] (B' : StrongBundle X'.PObj P')
    [ParacompactSpace (pullbackSpace P' X'.src)]
    (hs : X.PMor.IsScSmoothMap X.PObj X.src) (hs' : X'.PMor.IsScSmoothMap X'.PObj X'.src)
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (φ : EpFunctor X X'),
    -- (a) the project's notion is the text's
    (∀ Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid,
      E.IsStrongBundleFunctor E' φ Φ ↔ IsSBFunctorB E E' φ hs hs' Φ.toGroupoidFunctor) ∧
    -- (b) such functors are sc-smooth
    (∀ Φ : GroupoidFunctor E.toEpGroupoid.toGroupoidStr E'.toEpGroupoid.toGroupoidStr,
      IsSBFunctorB E E' φ hs hs' Φ →
        ∃ Φ' : EpFunctor E.toEpGroupoid E'.toEpGroupoid, Φ'.toGroupoidFunctor = Φ)

end RoundTrip.V8_24
