import Polyfold
/-! Blind formalization of V11_36 (the text's Part II, §11.6, Definition 11.6.4, p. 553 of the
Springer 2021 book; 2017: Definition 11.6, p. 404).

Text: (1) a functor `(Ψ, Φ) : F → F'` with `Φ ∘ F = F' ∘ Ψ`; (2) an equivalence if `Ψ`, `Φ` are
equivalences and `Ψ` maps each fibre `Y_x` bijectively onto `Y'_{Φ(x)}`.

Choices:
- This item is a definition.  Setting: proper covering functors `F : Y → X`, `F' : Y' → X'`
  between ep-groupoids (the project's `EpFunctor.IsProperCovering`, Definition 8.5.1, checked in
  `RoundTrip/Blind/V8_27.lean`), all eight spaces in `Type` (universe 0).
- (1) "functor `(Ψ, Φ) : F → F'`": a pair of sc-smooth functors (the project's `EpFunctor`,
  `RoundTrip/Blind/V7_9.lean`) `Ψ : Y → Y'`, `Φ : X → X'`; "`Φ ∘ F = F' ∘ Ψ`": equality on
  objects and on morphisms.  B says that the project's type `ProperCoveringHom F F'` is exactly
  the set of such pairs: every element has components `Ψ`, `Φ` satisfying the equation, every
  such pair occurs, and an element is determined by its components.
- (2) "equivalence" of ep-groupoids: the project's `EpFunctor.IsEquivalence` (2021
  Definition 10.1.1, checked in `RoundTrip/Blind/V10_1.lean`).  "`Ψ` maps each fibre `Y_x`
  bijectively onto `Y'_{Φ(x)}`": `Set.BijOn Ψ.obj (F⁻¹(x)) (F'⁻¹(Φ(x)))` for every object `x`
  of `X`.  B says the project's `ProperCoveringHom.IsEquivalence` is this condition.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_36
open Polyfold

/-- Definition 11.6.4: the project's functors and equivalences between proper coverings are the
text's. -/
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
    -- (1) an element `(Ψ, Φ)` of `ProperCoveringHom F F'` satisfies `Φ ∘ F = F' ∘ Ψ`,
    (∀ Γ : ProperCoveringHom F F',
      (∀ y : ObjY, Γ.Φ.obj (F.obj y) = F'.obj (Γ.Ψ.obj y)) ∧
      (∀ ψ : MorY, Γ.Φ.mor (F.mor ψ) = F'.mor (Γ.Ψ.mor ψ))) ∧
    -- every pair of sc-smooth functors with `Φ ∘ F = F' ∘ Ψ` occurs,
    (∀ (Ψ : EpFunctor Y Y') (Φ : EpFunctor X X'),
      (∀ y : ObjY, Φ.obj (F.obj y) = F'.obj (Ψ.obj y)) →
      (∀ ψ : MorY, Φ.mor (F.mor ψ) = F'.mor (Ψ.mor ψ)) →
      ∃ Γ : ProperCoveringHom F F', Γ.Ψ = Ψ ∧ Γ.Φ = Φ) ∧
    -- and an element is determined by `(Ψ, Φ)`
    (∀ Γ Γ' : ProperCoveringHom F F', Γ.Ψ = Γ'.Ψ → Γ.Φ = Γ'.Φ → Γ = Γ') ∧
    -- (2) equivalences
    (∀ Γ : ProperCoveringHom F F',
      Γ.IsEquivalence ↔
        Γ.Ψ.IsEquivalence ∧ Γ.Φ.IsEquivalence ∧
          ∀ x : ObjX, Set.BijOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x}))

end RoundTrip.V11_36
