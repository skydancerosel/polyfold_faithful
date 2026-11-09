import Polyfold
/-! Blind formalization of V8_17 (the text's Part II, §8.1, Proposition 8.1.14 = 2017
Proposition 8.1, pp. 367–372 / 2017 pp. 267–268).

Text: if `τ : Φ → Ψ` is a natural transformation between sc-smooth functors
`Φ, Ψ : X → Y` of ep-groupoids, then the tangent `Tτ : TX → T𝐘` is a natural transformation
`Tτ : TΦ → TΨ` between the tangent functors `TΦ, TΨ : (TX, T𝐗) → (TY, T𝐘)`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_15.lean`: ep-groupoids `X`, `Y` with spaces in `Type`
  (universe 0), sc-smooth functors = the project's `EpFunctor`; natural transformations are my
  reading `IsNatTransB` of Definition 8.1.13 (copied from V8_15); the hypothesis is
  `hτ : IsNatTransB Φ Ψ τ`.
- Tangents: `Tτ`, `TΦ = (TΦ, T𝚽)` are Part I's tangent maps `MPolyfold.tangentMap` of the
  sc-smooth maps `τ : X → 𝐘`, `Φ.obj : X → Y`, `Φ.mor : 𝐗 → 𝐘` (they take the sc-smoothness proof
  as argument; by proof irrelevance the choice does not matter).  The tangent ep-groupoids
  `T(X, 𝐗)`, `T(Y, 𝐘)` are the project's `EpGroupoid.tangentEpGroupoid` (the 2017 book's
  Theorem 8.1, not this item; its docstring: object M-polyfold `TX`, morphism M-polyfold
  `T𝐗`, structure maps (8.3)–(8.9)); I trust it as the text's tangent ep-groupoid.  The
  tangent spaces live in `Type 1`, so `IsNatTransDataB` is stated universe-polymorphically.
- "the two tangent functors `TΦ, TΨ`" presupposes that the tangent maps form sc-smooth functors
  `T(X, 𝐗) → T(Y, 𝐘)`; B asserts this (∃ `EpFunctor`s with these object and morphism maps) and
  that `Tτ` is a natural transformation between them in the sense of Definition 8.1.13: `Tτ` is
  sc-smooth `TX → T𝐘`, `Tτ(a) : TΦ(a) → TΨ(a)` in `T(Y, 𝐘)`, and the naturality square in
  `T(Y, 𝐘)` for every morphism `h : a → a'` of `T(X, 𝐗)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_17
open Polyfold

universe u v

/-- `τ : X → 𝐘` is a natural transformation from `(F₀, F₁)` to `(G₀, G₁)`: sc-smooth,
`τ(x) : F₀(x) → G₀(x)`, and `τ(x') ∘ F₁(h) = G₁(h) ∘ τ(x)` for `h : x → x'`. -/
def IsNatTransDataB {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor')
    (F₀ G₀ : Obj → Obj') (F₁ G₁ : Mor → Mor') (τ : Obj → Mor') : Prop :=
  X.PObj.IsScSmoothMap Y.PMor τ ∧
  (∀ x : Obj, Y.src (τ x) = F₀ x ∧ Y.tgt (τ x) = G₀ x) ∧
  (∀ (h : Mor) (x x' : Obj), X.src h = x → X.tgt h = x' →
    Y.comp (τ x') (F₁ h) = Y.comp (G₁ h) (τ x))

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- **Definition 8.1.13**: `τ` is a natural transformation `F → G`. -/
def IsNatTransB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y)
    (τ : Obj → Mor') : Prop :=
  IsNatTransDataB X Y F.obj G.obj F.mor G.mor τ

end

/-- Proposition 8.1.14: the tangent `Tτ` of a natural transformation `τ : Φ → Ψ` is a natural
transformation between the tangent functors `TΦ, TΨ : T(X, 𝐗) → T(Y, 𝐘)`. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (Φ Ψ : EpFunctor X Y)
    (τ : Obj → Mor') (hτ : IsNatTransB Φ Ψ τ),
    ∃ TΦ TΨ : EpFunctor X.tangentEpGroupoid Y.tangentEpGroupoid,
      TΦ.obj = MPolyfold.tangentMap Φ.isScSmoothMap_obj ∧
      TΦ.mor = MPolyfold.tangentMap Φ.isScSmoothMap_mor ∧
      TΨ.obj = MPolyfold.tangentMap Ψ.isScSmoothMap_obj ∧
      TΨ.mor = MPolyfold.tangentMap Ψ.isScSmoothMap_mor ∧
      IsNatTransDataB X.tangentEpGroupoid Y.tangentEpGroupoid TΦ.obj TΨ.obj TΦ.mor TΨ.mor
        (MPolyfold.tangentMap hτ.1)

end RoundTrip.V8_17
