import Polyfold
/-! Blind formalization of V9_8 (the Springer 2021 book, Part II, §9.1, Definition 9.1.8, p. 405;
2017: Definition 9.3, p. 294): manifold-type and orbifold-type `Θ`.

Text: `Θ` is of manifold type if it takes only the values `0` and `1` and between two objects of
`supp(Θ)` there is at most one morphism; of orbifold type if it takes only the values `0` and `1`.

Choices:
- This item is a definition.  B says that the project's `X.IsManifoldType Θ` and
  `EpGroupoid.IsOrbifoldType Θ` are these notions, for every ep-groupoid and every
  `Θ : Obj → ℚ` (defined in the text for branched ep⁺-subgroupoids; both sides make sense for any
  function).
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.
- "takes only the values `0` and `1`": `Θ x = 0 ∨ Θ x = 1` for every object `x` (not that both
  values are attained).
- "between two objects of `supp(Θ)` there is at most one morphism": for `x, y ∈ supp Θ`
  (`x = y` allowed, so the isotropy groups of points of the support are trivial), any two
  morphisms `φ, ψ` with `s φ = s ψ = x`, `t φ = t ψ = y` are equal.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_8
open Polyfold

/-- `supp(Θ) = {x | Θ(x) > 0}`. -/
def suppB {Obj : Type} (Θ : Obj → ℚ) : Set Obj := {x | 0 < Θ x}

/-- `Θ` takes only the values `0` and `1`. -/
def IsZeroOneB {Obj : Type} (Θ : Obj → ℚ) : Prop := ∀ x, Θ x = 0 ∨ Θ x = 1

/-- Definition 9.1.8: manifold type and orbifold type. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ),
    (X.IsManifoldType Θ ↔
      IsZeroOneB Θ ∧
        ∀ x ∈ suppB Θ, ∀ y ∈ suppB Θ, ∀ φ ψ : Mor,
          X.src φ = x → X.tgt φ = y → X.src ψ = x → X.tgt ψ = y → φ = ψ) ∧
    (EpGroupoid.IsOrbifoldType Θ ↔ IsZeroOneB Θ)

end RoundTrip.V9_8
