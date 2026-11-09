import Polyfold
/-! Blind formalization of V11_15 (the text's Part II, §11.3, Lemma 11.3.2, p. 536 of the
Springer 2021 book; 2017: Lemma 11.5, p. 389).

Text: for an equivalence `F`: `F_*Θ` is well defined and a functor, `F^*F_*Θ = Θ`;
`F_*F^*Θ' = Θ'`; naturally equivalent equivalences have the same push-forwards and pull-backs.

Choices:
- Setting: `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all spaces in `Type`
  (universe 0), Hausdorff and paracompact; `F` an equivalence (the project's
  `EpFunctor.IsEquivalence`, `RoundTrip/Blind/V10_1.lean`).
- `Θ`, `Θ'`: arbitrary functors `X → ℚ⁺`, `Y → ℚ⁺` (`IsQFunctorB`: `0 ≤ Θ`, constant along
  morphisms; the setting of Definition 11.3.1).  The item's title says "with weaker hypotheses";
  I take the weakest hypotheses the quoted statement supports (no branching structure on `Θ`).
- `F^*`, `F_*`: the project's `pullbackTheta`, `pushforwardTheta` (Definition 11.3.1, compared
  with the text in my `RoundTrip/Blind/V11_14.lean`).
- "`F_*Θ` is well defined": every `y` has some `x` with a morphism `F(x) → y`, and `Θ(x)` does
  not depend on the choice of `x` (stated directly, without the project's definition); "a
  functor": `IsQFunctorB Y (F_*Θ)`.
- "naturally equivalent": a natural transformation `F → G` exists (the project's `EpNatTrans`,
  Definition 10.1.4, `RoundTrip/Blind/V10_4.lean`; in a groupoid it is a natural equivalence);
  both `F` and `G` equivalences; the equalities are asserted on functors `Θ`, `Θ'`.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_15
open Polyfold

/-- `Θ : X → ℚ⁺` is a functor: nonnegative and constant along morphisms. -/
def IsQFunctorB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  (∀ x, 0 ≤ Θ x) ∧ ∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)

/-- Lemma 11.3.2: push-forward along an equivalence is well defined, functorial, inverse to the
pull-back, and invariant under natural equivalence (as is the pull-back). -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y), F.IsEquivalence →
    (∀ Θ : Obj → ℚ, IsQFunctorB X Θ →
      -- `F_*Θ` is well defined
      (∀ y : Obj', ∃ (x : Obj) (ψ : Mor'), Y.src ψ = F.obj x ∧ Y.tgt ψ = y) ∧
      (∀ (y : Obj') (x x' : Obj) (ψ ψ' : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = y →
        Y.src ψ' = F.obj x' → Y.tgt ψ' = y → Θ x = Θ x') ∧
      -- `F_*Θ` is a functor, and `F^*F_*Θ = Θ`
      IsQFunctorB Y (F.pushforwardTheta Θ) ∧
      F.pullbackTheta (F.pushforwardTheta Θ) = Θ) ∧
    -- `F_*F^*Θ' = Θ'`
    (∀ Θ' : Obj' → ℚ, IsQFunctorB Y Θ' → F.pushforwardTheta (F.pullbackTheta Θ') = Θ') ∧
    -- naturally equivalent equivalences
    (∀ G : EpFunctor X Y, G.IsEquivalence → Nonempty (EpNatTrans F G) →
      (∀ Θ : Obj → ℚ, IsQFunctorB X Θ → F.pushforwardTheta Θ = G.pushforwardTheta Θ) ∧
      (∀ Θ' : Obj' → ℚ, IsQFunctorB Y Θ' → F.pullbackTheta Θ' = G.pullbackTheta Θ'))

end RoundTrip.V11_15
