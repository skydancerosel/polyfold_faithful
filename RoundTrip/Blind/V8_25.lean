import Polyfold
/-! Blind formalization of V8_25 (the text's Part II, §8.3, between Definitions 8.3.2 and 8.3.3
= 2017 Definitions 8.5 and 8.6, pp. 377–379 / 2017 pp. 273–274).

Text: for `Φ` as in Definition 8.3.2, `𝚽(γ, w) = (φ(γ), Φ(w))` is a strong bundle map `𝐖 → 𝐖'`
covering `𝛗` with `μ' ∘ 𝚽 = Φ ∘ μ` and `s_{𝐖'} ∘ 𝚽 = Φ ∘ s_𝐖`, so `Φ` lifts to a functor
`(W, 𝐖) → (W', 𝐖')`.  Conversely such a functor covering `φ` and linear on the fibres gives a
strong bundle map `Φ : W → W'` with the properties of Definition 8.3.2, from which the functor is
recovered completely; "in any case these are identical notions".

Choices:
- Setting as in my `RoundTrip/Blind/V8_24.lean`: strong bundles `E`, `E'` over the ep-groupoids
  `X`, `X'` (V8_20), an sc-smooth functor `φ : X → X'`, the ep-groupoids `(W, 𝐖)`, `(W', 𝐖')` of
  V8_22 (`E.toEpGroupoid`, needing paracompactness of `𝐖`, `𝐖'` as instance hypotheses), the
  pull-back strong bundles `𝐖 → 𝐗` (needing `hs`, `hs'`); all hypotheses true and satisfiable.
- Definition 8.3.2 is the project's `EpStrongBundle.IsMap` (V8_23 says it is the text's notion),
  Definition 8.3.3 the project's `IsStrongBundleFunctor` on `EpFunctor`s (V8_24).  Points of
  `𝐖'` are compared through their underlying pairs.
- (a) for `Φ` as in 8.3.2 there is an sc-smooth functor `(W, 𝐖) → (W', 𝐖')` with object map `Φ`
  and morphism map `𝚽(γ, w) = (φ(γ), Φ(w))`; `𝚽` is a strong bundle map covering `𝛗`, `μ' ∘ 𝚽 =
  Φ ∘ μ`, `s_{𝐖'} ∘ 𝚽 = Φ ∘ s_𝐖`, and the functor is a strong bundle functor (8.3.3).
- (b) "Conversely, such a functor covering `φ` and linear on the fibres": I read "such a functor"
  as a strong bundle functor of Definition 8.3.3 (the item says the two definitions are
  equivalent; a functor that is only sc-smooth, covering and fibrewise linear need not be
  sc-smooth on the `[1]`-levels, which a strong bundle map requires).  Its object map satisfies
  8.3.2, and its morphism map is `(γ, w) ↦ (φ(γ), Φ(w))`.
- (c) "recovered completely": two strong bundle functors covering `φ` with the same object map are
  equal.  (d) "identical notions": a bijection between the maps of 8.3.2 and the functors of 8.3.3
  covering `φ`, given by taking the object map.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_25
open Polyfold

/-- Definitions 8.3.2 and 8.3.3 are equivalent. -/
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
    -- (a) Definition 8.3.2 ⇒ the lift `(Φ, 𝚽)` is a functor, a strong bundle functor
    (∀ Φ : W → W', E.IsMap E' φ Φ →
      ∃ F : EpFunctor E.toEpGroupoid E'.toEpGroupoid,
        F.obj = Φ ∧
        (∀ p : pullbackSpace P X.src, (F.mor p).1 = (φ.mor p.1.1, Φ p.1.2)) ∧
        (B.pullback hs).IsStrongBundleMap (B'.pullback hs') φ.mor F.mor ∧
        (∀ p : pullbackSpace P X.src, E'.μ (F.mor p) = Φ (E.μ p)) ∧
        (∀ p : pullbackSpace P X.src, E'.toEpGroupoid.src (F.mor p) = Φ (E.toEpGroupoid.src p)) ∧
        E.IsStrongBundleFunctor E' φ F) ∧
    -- (b) Definition 8.3.3 ⇒ the object map satisfies Definition 8.3.2, and determines `𝚽`
    (∀ F : EpFunctor E.toEpGroupoid E'.toEpGroupoid, E.IsStrongBundleFunctor E' φ F →
      E.IsMap E' φ F.obj ∧
        ∀ p : pullbackSpace P X.src, (F.mor p).1 = (φ.mor p.1.1, F.obj p.1.2)) ∧
    -- (c) the functor is recovered completely from its object map
    (∀ F₁ F₂ : EpFunctor E.toEpGroupoid E'.toEpGroupoid,
      E.IsStrongBundleFunctor E' φ F₁ → E.IsStrongBundleFunctor E' φ F₂ →
        F₁.obj = F₂.obj → F₁ = F₂) ∧
    -- (d) identical notions
    (∃ e : {Φ : W → W' // E.IsMap E' φ Φ} ≃
        {F : EpFunctor E.toEpGroupoid E'.toEpGroupoid // E.IsStrongBundleFunctor E' φ F},
      ∀ Φ, (e Φ).1.obj = Φ.1)

end RoundTrip.V8_25
