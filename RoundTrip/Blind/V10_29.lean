import Polyfold
/-! Blind formalization of V10_29 (the text's Part II, §10.4, Remark 10.4.9 and (10.23),
pp. 502–503 of the Springer 2021 book; 2017: Remark 10.4, p. 363).

Text: for a natural transformation `(T, τ)` between strong bundle functors `Φ, Ψ` covering `ϕ, ψ`
(Definition 10.4.8), `T(w) = (τ(P(w)), Φ(w))` and (10.23) `Ψ(w) = μ'(τ(P(w)), Φ(w))`; so `T` and
`Ψ` are determined by `Φ` and `τ`; and `T` is a strong bundle map.

Choices:
- Setting and `IsSBNatTransB` (Definition 10.4.8) as in my `RoundTrip/Blind/V10_28.lean` (copied
  here); `Φ`, `Ψ` are strong bundle functors covering `ϕ`, `ψ` (the project's
  `IsStrongBundleFunctor`, V8_24), `τ : ϕ → ψ` a project `EpNatTrans`.
- (i) `T(w) = (τ(P(w)), Φ(w))` as elements of `Mor' × W'` (the underlying pair of `T w ∈ 𝐗' ₛ×_{P'}
  W'`).  (ii) (10.23): the pair `(τ(P(w)), Φ(w))` lies in `𝐗' ₛ×_{P'} W'` and
  `Ψ(w) = μ'(τ(P(w)), Φ(w))`.
- (iii) "`T` and `Ψ` are determined by `Φ` and `τ`": if `(T₂, τ)` is also a natural
  transformation from `Φ` to a strong bundle functor `Ψ₂` covering `ψ`, then `T₂ = T` and
  `Ψ₂ = Ψ` on objects and on morphisms (I read "`Ψ` is determined" as the whole functor; on
  morphisms this uses naturality).
- (iv) "`T` is a strong bundle map": `T : W → 𝐗' ₛ×_{P'} W'` is a strong bundle map covering
  `τ : X → 𝐗'` from `P` to the pull-back strong bundle `𝐗' ₛ×_{P'} W' → 𝐗'`, `(σ, w') ↦ σ` (the
  project's `StrongBundle.IsStrongBundleMap` and `StrongBundle.pullback`, trusted as in V8_20,
  V8_24); the pull-back needs the sc-smoothness `hs'` of `s : 𝐗' → X'`, a hypothesis of B (true).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_29
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

/-- **Definition 10.4.8**: `T` is a natural transformation `Φ → Ψ` over `τ : ϕ → ψ`. -/
def IsSBNatTransB (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') {ϕ ψ : EpFunctor X X'}
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (τ : EpNatTrans ϕ ψ)
    (T : W → pullbackSpace P' X'.src) : Prop :=
  -- `T(w) : Φ(w) → Ψ(w)` in `(W', 𝐖')`
  (∀ w : W, E'.toEpGroupoid.src (T w) = Φ.obj w ∧ E'.toEpGroupoid.tgt (T w) = Ψ.obj w) ∧
  -- naturality: `T(w') ∘ Φ(h) = Ψ(h) ∘ T(w)` for `h : w → w'` in `𝐖`
  (∀ h : pullbackSpace P X.src,
    E'.toEpGroupoid.comp (T (E.toEpGroupoid.tgt h)) (Φ.mor h) =
      E'.toEpGroupoid.comp (Ψ.mor h) (T (E.toEpGroupoid.src h))) ∧
  -- `T(w)` lies over `τ(P(w))`
  (∀ w : W, (T w).1.1 = τ.app (P w))

end

/-- **Remark 10.4.9**: `T(w) = (τ(P(w)), Φ(w))`, `Ψ(w) = μ'(τ(P(w)), Φ(w))`, so `T`, `Ψ` are
determined by `Φ`, `τ`; and `T` is a strong bundle map covering `τ`. -/
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
    (hs' : X'.PMor.IsScSmoothMap X'.PObj X'.src)
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (ϕ ψ : EpFunctor X X')
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (τ : EpNatTrans ϕ ψ)
    (T : W → pullbackSpace P' X'.src),
    E.IsStrongBundleFunctor E' ϕ Φ → E.IsStrongBundleFunctor E' ψ Ψ →
    IsSBNatTransB E E' Φ Ψ τ T →
    -- (i) `T(w) = (τ(P(w)), Φ(w))`
    (∀ w : W, (T w).1 = (τ.app (P w), Φ.obj w)) ∧
    -- (ii) (10.23): `Ψ(w) = μ'(τ(P(w)), Φ(w))`
    (∀ w : W, ∃ h : P' (Φ.obj w) = X'.src (τ.app (P w)),
      Ψ.obj w = E'.μ ⟨(τ.app (P w), Φ.obj w), h⟩) ∧
    -- (iii) `T` and `Ψ` are determined by `Φ` and `τ`
    (∀ (Ψ₂ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (T₂ : W → pullbackSpace P' X'.src),
      E.IsStrongBundleFunctor E' ψ Ψ₂ → IsSBNatTransB E E' Φ Ψ₂ τ T₂ →
        T₂ = T ∧ Ψ₂.obj = Ψ.obj ∧ Ψ₂.mor = Ψ.mor) ∧
    -- (iv) `T : W → 𝐗' ₛ×_{P'} W'` is a strong bundle map covering `τ`
    B.IsStrongBundleMap (B'.pullback hs') τ.app T

end RoundTrip.V10_29
