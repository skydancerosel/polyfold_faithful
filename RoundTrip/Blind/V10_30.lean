import Polyfold
/-! Blind formalization of V10_30 (the text's Part II, §10.4, Definition 10.4.10 and its
equivalence with Definition 10.4.8, p. 503 of the Springer 2021 book; 2017: Definition 10.12,
p. 363).

Text: for strong bundle functors `Φ, Ψ` covering `ϕ, ψ : X → X'`, a natural transformation
`Φ → Ψ` is a strong bundle map `T : W → 𝐗' ₛ×_{P'} W'` covering a natural transformation
`τ : ϕ → ψ`, satisfying (10.23); the two definitions (10.4.8 and 10.4.10) are equivalent.

Choices:
- Setting, and Definition 10.4.8 (`IsSBNatTransB`), as in my `RoundTrip/Blind/V10_28.lean`
  (copied here); `Φ`, `Ψ` strong bundle functors covering `ϕ`, `ψ` (the project's
  `IsStrongBundleFunctor`, V8_24), `τ` a project `EpNatTrans ϕ ψ` (Definition 10.1.4, V10_4).
- Definition 10.4.10 (`IsSBNatTransMapB`): `T` is a strong bundle map from `P : W → X` to the
  pull-back strong bundle `𝐗' ₛ×_{P'} W' → 𝐗'`, `(σ, w') ↦ σ`, covering `τ : X → 𝐗'` (the
  project's `StrongBundle.IsStrongBundleMap`, `StrongBundle.pullback`, trusted as in V8_20; the
  pull-back needs the sc-smoothness `hs'` of `s : 𝐗' → X'`, a hypothesis of B, true), with (10.23)
  read, as in Remark 10.4.9 (my V10_29), as the two identities `T(w) = (τ(P(w)), Φ(w))` and
  `Ψ(w) = μ'(τ(P(w)), Φ(w))` (the latter with the membership `(τ(P(w)), Φ(w)) ∈ 𝐗' ₛ×_{P'} W'`).
- B (a): the project's `IsStrongBundleNatTransMap E E' Φ Ψ τ T` is `IsSBNatTransMapB`;
  (b) "the two definitions are equivalent": for every pair `(T, τ)`, Definition 10.4.8 holds iff
  Definition 10.4.10 holds.  Both under the text's standing hypothesis that `Φ`, `Ψ` are strong
  bundle functors covering `ϕ`, `ψ`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_30
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

/-- **Definition 10.4.10**: `T : W → 𝐗' ₛ×_{P'} W'` is a strong bundle map covering `τ` with
`T(w) = (τ(P(w)), Φ(w))` and (10.23) `Ψ(w) = μ'(τ(P(w)), Φ(w))`. -/
def IsSBNatTransMapB (hs' : X'.PMor.IsScSmoothMap X'.PObj X'.src) (E : EpStrongBundle X B)
    (E' : EpStrongBundle X' B') {ϕ ψ : EpFunctor X X'}
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (τ : EpNatTrans ϕ ψ)
    (T : W → pullbackSpace P' X'.src) : Prop :=
  B.IsStrongBundleMap (B'.pullback hs') τ.app T ∧
  (∀ w : W, (T w).1 = (τ.app (P w), Φ.obj w)) ∧
  (∀ w : W, ∃ h : P' (Φ.obj w) = X'.src (τ.app (P w)),
    Ψ.obj w = E'.μ ⟨(τ.app (P w), Φ.obj w), h⟩)

end

/-- Definition 10.4.10: the project's notion is the text's, and it is equivalent to Definition
10.4.8. -/
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
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid),
    E.IsStrongBundleFunctor E' ϕ Φ → E.IsStrongBundleFunctor E' ψ Ψ →
    ∀ (τ : EpNatTrans ϕ ψ) (T : W → pullbackSpace P' X'.src),
      -- (a) the project's Definition 10.4.10 is the text's
      (E.IsStrongBundleNatTransMap E' Φ Ψ τ T ↔ IsSBNatTransMapB hs' E E' Φ Ψ τ T) ∧
      -- (b) Definitions 10.4.8 and 10.4.10 are equivalent
      (IsSBNatTransB E E' Φ Ψ τ T ↔ IsSBNatTransMapB hs' E E' Φ Ψ τ T)

end RoundTrip.V10_30
