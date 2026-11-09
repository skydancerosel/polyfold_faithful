import Polyfold
/-! Blind formalization of V10_28 (the text's Part II, §10.4, Definition 10.4.8, p. 502 of the
Springer 2021 book; 2017: Definition 10.11, p. 362).

Text: for strong bundle functors `Φ, Ψ : (W, 𝐖) → (W', 𝐖')` covering `ϕ, ψ : X → X'`, a natural
transformation `Φ → Ψ` consists of morphisms `T(w) : Φ(w) → Ψ(w)` of `(W', 𝐖')`, natural in `w`,
lying over a natural transformation `τ : ϕ → ψ`.

Choices:
- This item is a definition.  Setting as in `RoundTrip/Blind/V8_24.lean` and my
  `RoundTrip/Blind/V10_25.lean`: strong bundles `E : EpStrongBundle X B`, `E' : EpStrongBundle X'
  B'` over ep-groupoids, all spaces in `Type`, paracompactness of `𝐗 ₛ×_P W`, `𝐗' ₛ×_{P'} W'` as
  instance hypotheses; `(W, 𝐖)`, `(W', 𝐖')` the project's ep-groupoids `E.toEpGroupoid`,
  `E'.toEpGroupoid` (characterized in `RoundTrip/Blind/V8_22.lean`: morphisms `(σ, w') ∈ 𝐗' ₛ×_{P'}
  W'` from `w'` to `μ'(σ, w')`); "strong bundle functor covering `ϕ`" the project's
  `IsStrongBundleFunctor E E' ϕ Φ` (V8_24), assumed for `Φ` and `Ψ`.
- `T : W → 𝐖'` (my `IsSBNatTransB`): `T(w)` has source `Φ(w)` and target `Ψ(w)` in `(W', 𝐖')`;
  naturality `T(w') ∘ Φ(h) = Ψ(h) ∘ T(w)` for every morphism `h : w → w'` of `𝐖` (composition
  of `(W', 𝐖')`); "over `τ`": the projection `(σ, w') ↦ σ` of `T(w)` is `τ(P(w))`.  No smoothness
  of `T` is required (the text does not ask for it; Remark 10.4.9 derives it).
- `τ : ϕ → ψ` is a natural transformation of sc-smooth functors (Definition 10.1.4), the project's
  `EpNatTrans ϕ ψ` (characterized in `RoundTrip/Blind/V10_4.lean`).
- B: (a) the data `(T, τ)` of every project `StrongBundleNatTrans E E' ϕ ψ Φ Ψ` satisfy
  `IsSBNatTransB`; (b) every pair `(T, τ)` satisfying it is the data of one.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_28
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

/-- Definition 10.4.8: the project's natural transformations of strong bundle functors are the
text's. -/
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
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (ϕ ψ : EpFunctor X X')
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid),
    E.IsStrongBundleFunctor E' ϕ Φ → E.IsStrongBundleFunctor E' ψ Ψ →
    -- (a) the project's natural transformations are natural transformations in the text's sense
    (∀ N : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ, IsSBNatTransB E E' Φ Ψ N.τ N.T) ∧
    -- (b) every natural transformation in the text's sense is one of the project's
    (∀ (τ : EpNatTrans ϕ ψ) (T : W → pullbackSpace P' X'.src), IsSBNatTransB E E' Φ Ψ τ T →
      ∃ N : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ, N.τ = τ ∧ N.T = T)

end RoundTrip.V10_28
