import Polyfold
/-! Blind formalization of V8_15 (the text's Part II, §8.1, Definition 8.1.13 = 2017 Definition
8.1, p. 367 / 2017 p. 266).

Text: for sc-smooth functors `F, G : X → Y` between ep-groupoids, `F ≃ G` if there is an sc-smooth
map `τ : X → 𝐘` with `τ(x) : F(x) → G(x)` and `τ(x') ∘ F(h) = G(h) ∘ τ(x)` for every morphism
`h : x → x'` in `𝐗`; such a `τ` is a natural transformation `τ : F → G`.

Choices:
- This item is a definition (two notions).  Setting: ep-groupoids `X : EpGroupoid Obj Mor`,
  `Y : EpGroupoid Obj' Mor'` with all four spaces in `Type` (universe 0; the project's notions
  allow `X` and `Y` in two universes, this is the instance `u = v = 0`), Hausdorff and paracompact
  as the project's `EpGroupoid` requires (`RoundTrip/Blind/V7_3.lean`).  "sc-smooth functor" is the
  project's `EpFunctor` (characterized as the text's notion in `RoundTrip/Blind/V7_9.lean`).
- My notion `IsNatTransB` (with `IsNatTransDataB` taking the object and morphism maps of `F`, `G`
  separately, for reuse): `τ : Obj → Mor'` is sc-smooth from the object M-polyfold of `X` to the
  morphism M-polyfold of `Y` (`MPolyfold.IsScSmoothMap`, Definition 2.14); `τ(x) : F(x) → G(x)`
  means `s(τ x) = F x` and `t(τ x) = G x`; naturality for every `h` with `s h = x`, `t h = x'`:
  `comp (τ x') (F h) = comp (G h) (τ x)` (the project's `comp φ ψ = φ ∘ ψ`, first `ψ`; both pairs
  are composable by the typing).
- B: (a)/(b) the project's `EpNatTrans F G` (fields read with `#print`) is exactly such a `τ`
  (its `app`); (c) the project's `EpFunctor.NaturallyEquivalent F G` holds iff such a `τ` exists.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_15
open Polyfold

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- `τ : X → 𝐘` is a natural transformation from `(F₀, F₁)` to `(G₀, G₁)`: sc-smooth,
`τ(x) : F₀(x) → G₀(x)`, and `τ(x') ∘ F₁(h) = G₁(h) ∘ τ(x)` for `h : x → x'`. -/
def IsNatTransDataB (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor')
    (F₀ G₀ : Obj → Obj') (F₁ G₁ : Mor → Mor') (τ : Obj → Mor') : Prop :=
  X.PObj.IsScSmoothMap Y.PMor τ ∧
  (∀ x : Obj, Y.src (τ x) = F₀ x ∧ Y.tgt (τ x) = G₀ x) ∧
  (∀ (h : Mor) (x x' : Obj), X.src h = x → X.tgt h = x' →
    Y.comp (τ x') (F₁ h) = Y.comp (G₁ h) (τ x))

/-- **Definition 8.1.13**: `τ` is a natural transformation `F → G`. -/
def IsNatTransB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y)
    (τ : Obj → Mor') : Prop :=
  IsNatTransDataB X Y F.obj G.obj F.mor G.mor τ

end

/-- Definition 8.1.13: the project's natural transformations are the text's, and the project's
natural equivalence `F ≃ G` is the existence of a natural transformation `F → G`. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F G : EpFunctor X Y),
    -- (a) every project natural transformation is one in the text's sense
    (∀ τ : EpNatTrans F G, IsNatTransB F G τ.app) ∧
    -- (b) every natural transformation in the text's sense is a project one
    (∀ τ : Obj → Mor', IsNatTransB F G τ → ∃ T : EpNatTrans F G, T.app = τ) ∧
    -- (c) `F ≃ G` iff there is a natural transformation `F → G`
    (F.NaturallyEquivalent G ↔ ∃ τ : Obj → Mor', IsNatTransB F G τ)

end RoundTrip.V8_15
