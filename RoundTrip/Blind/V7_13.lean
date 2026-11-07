import Polyfold
/-! Blind formalization of V7_13 (the 2017 book, Part II, §7.1, Proposition 7.3, pp. 229–230:
the local closure relation `π(cl_X(A)) = cl_{|X|}(π(A))`). Choices:
- Setting as in `V7_11`: `Obj Mor : Type` (universe 0) with their topologies (`T2`, paracompact)
  as instances, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read with
  `#print`); `|X|` and `π` are the project's `X.OrbitSpace` and `X.π` (`Quotient` by
  `x ∼ y :↔ ∃ φ, s φ = x ∧ t φ = y`, `π x = ⟦x⟧`).
- `|X|` carries the quotient topology (the standing convention of §7.1, Propositions 7.1–7.2);
  it is defined here (`orbitTop X`, coinduced by `π`), not taken from an instance.
  `cl_{|X|}` is `closure[orbitTop X]`, `cl_X` the closure in the topology of `Obj`.
- "For every `z ∈ |X|` and every representative `x` of `z`": `∀ z x, π x = z → …` (kept
  literally although `z` is determined by `x`). "Open neighbourhood `U` of `x`": `IsOpen U`,
  `x ∈ U`. "For every subset `A ⊂ U`": `∀ A, A ⊆ U → …`.
-/
namespace RoundTrip.V7_13
open Polyfold Topology

/-- The quotient topology on the orbit space `|X|`: the finest topology making `π` continuous. -/
abbrev orbitTop {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    TopologicalSpace X.OrbitSpace :=
  TopologicalSpace.coinduced X.π inferInstance

/-- Proposition 7.3: every representative `x` of a point of `|X|` has an open neighbourhood `U`
such that `π(cl_X A) = cl_{|X|}(π A)` for all `A ⊆ U`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (z : X.OrbitSpace) (x : Obj), X.π x = z →
    ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧
      ∀ A : Set Obj, A ⊆ U → X.π '' closure A = closure[orbitTop X] (X.π '' A)

end RoundTrip.V7_13
