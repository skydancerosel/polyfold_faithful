import Polyfold
/-! Blind formalization of V11_14 (the text's Part II, §11.3, Definition 11.3.1, p. 535 of the
Springer 2021 book; 2017: Definition 11.4, p. 389).

Text: for an equivalence `F : X → Y` and functors `Θ : X → ℚ⁺`, `Θ' : Y → ℚ⁺`:
`F^*Θ' = Θ' ∘ F` and `(F_*Θ)(y) = Θ(x)` for `x` with a morphism `F(x) → y`.

Choices:
- This item is a definition.  B says that the project's `EpFunctor.pullbackTheta` and
  `EpFunctor.pushforwardTheta` are the text's `F^*`, `F_*` on the text's domain.
- Setting: `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in `Type`
  (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); `F` an sc-smooth functor
  (`EpFunctor`) which is an equivalence (the project's `EpFunctor.IsEquivalence`,
  Definition 10.1.1, `RoundTrip/Blind/V10_1.lean`).
- "functor `Θ : X → ℚ⁺`" (`IsQFunctorB`, as in `RoundTrip/Blind/V9_1.lean`): `Θ : Obj → ℚ` with
  `0 ≤ Θ`, constant along morphisms (`ℚ⁺` a category with identity morphisms only).
- B is asserted only for such functors and only for equivalences `F` (the text's domain); off it
  the project's values (e.g. its `0` where no `x` exists) are junk and not constrained.
- Push-forward: for every `y`, every `x` and every morphism `ψ : F(x) → y`, `(F_*Θ)(y) = Θ(x)`
  (this also expresses that the value does not depend on the choice of `x`).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_14
open Polyfold

/-- `Θ : X → ℚ⁺` is a functor: nonnegative and constant along morphisms. -/
def IsQFunctorB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  (∀ x, 0 ≤ Θ x) ∧ ∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)

/-- Definition 11.3.1: the project's pull-back and push-forward of functors `Θ` along an
equivalence are `F^*Θ' = Θ' ∘ F` and `(F_*Θ)(y) = Θ(x)` for `ψ : F(x) → y`. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y), F.IsEquivalence →
    (∀ Θ' : Obj' → ℚ, IsQFunctorB Y Θ' → F.pullbackTheta Θ' = fun x => Θ' (F.obj x)) ∧
    (∀ Θ : Obj → ℚ, IsQFunctorB X Θ →
      ∀ (y : Obj') (x : Obj) (ψ : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = y →
        F.pushforwardTheta Θ y = Θ x)

end RoundTrip.V11_14
