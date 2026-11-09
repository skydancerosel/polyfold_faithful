import Polyfold
/-! Blind formalization of V11_37 (the text's Part II, §11.6, Definition 11.6.5, p. 554 of the
Springer 2021 book, and the diagram on p. 555; 2017: Definition 11.7, p. 405).

Text: a natural transformation `(ζ, ξ) → (ζ', ξ')` is a pair `τ_Y`, `τ_X` with
`τ_X ∘ F = F' ∘ τ_Y` ((11.20)).

Choices:
- This item is a definition.  Setting as in my `RoundTrip/Blind/V11_36.lean`: proper covering
  functors `F : Y → X`, `F' : Y' → X'` (the project's `EpFunctor.IsProperCovering`), all spaces in
  `Type`; `(ζ, ξ)`, `(ζ', ξ') : F → F'` elements `Γ`, `Γ'` of the project's
  `ProperCoveringHom F F'` (characterized in V11_36 as the pairs of sc-smooth functors with
  `ξ ∘ F = F' ∘ ζ`), with `ζ = Γ.Ψ`, `ξ = Γ.Φ`.
- "a pair `τ_Y`, `τ_X`": natural transformations `τ_Y : ζ → ζ'`, `τ_X : ξ → ξ'` of sc-smooth
  functors between ep-groupoids, the project's `EpNatTrans` (Definition 8.1 / 10.1.4: an
  sc-smooth map `τ : Y → 𝐘'` with `τ(y) : ζ(y) → ζ'(y)` and the naturality squares), as in
  `RoundTrip/Blind/V10_35.lean`.
- (11.20) "`τ_X ∘ F = F' ∘ τ_Y`": equality of the maps `Y → 𝐗'`, `y ↦ τ_X(F(y))` and
  `y ↦ F'(τ_Y(y))`.
- B says that the project's type `Γ.NatTrans Γ'` is exactly the set of such pairs: every
  element has components satisfying (11.20), every such pair occurs, and an element is
  determined by its components.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_37
open Polyfold

/-- Definition 11.6.5: the project's natural transformations of functors between proper
coverings are the text's. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (ObjY' MorY' : Type) [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
    [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
    (ObjX' MorX' : Type) [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
    [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX)
    (Y' : EpGroupoid ObjY' MorY') (X' : EpGroupoid ObjX' MorX')
    (F : EpFunctor Y X) (F' : EpFunctor Y' X'),
    F.IsProperCovering → F'.IsProperCovering →
    ∀ Γ Γ' : ProperCoveringHom F F',
      -- every natural transformation `(τ_Y, τ_X)` satisfies (11.20),
      (∀ τ : Γ.NatTrans Γ', ∀ y : ObjY, τ.τX.app (F.obj y) = F'.mor (τ.τY.app y)) ∧
      -- every pair of natural transformations satisfying (11.20) occurs,
      (∀ (τY : EpNatTrans Γ.Ψ Γ'.Ψ) (τX : EpNatTrans Γ.Φ Γ'.Φ),
        (∀ y : ObjY, τX.app (F.obj y) = F'.mor (τY.app y)) →
        ∃ τ : Γ.NatTrans Γ', τ.τY = τY ∧ τ.τX = τX) ∧
      -- and a natural transformation is determined by `(τ_Y, τ_X)`
      (∀ τ τ' : Γ.NatTrans Γ', τ.τY = τ'.τY → τ.τX = τ'.τX → τ = τ')

end RoundTrip.V11_37
