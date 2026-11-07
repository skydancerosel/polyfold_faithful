import Polyfold
/-! Blind formalization of V7_11 (the 2017 book, Part II, §7.1, the paragraph before
Proposition 7.1 and Proposition 7.1, p. 229: the quotient topology on `|X|`, and `π` is open).
Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with the topologies, `T2`
  and paracompactness as instances, and `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3; I read its fields with `#print`: a groupoid structure, M-polyfold structures
  `PObj`, `PMor`, `s`, `t` local sc-diffeomorphisms, `u`, `ι` sc-smooth, the properness
  condition, `m` sc-smooth on the fibred product). The text's objects `X` are `Obj`, its
  morphisms `𝐗` are `Mor`.
- The orbit space `|X|` and `π` are the project's `X.OrbitSpace` (`Quotient X.orbitSetoid`, the
  relation `x ∼ y :↔ ∃ φ, s φ = x ∧ t φ = y`) and `X.π x = ⟦x⟧` (both read with `#print`; they
  are the text's `|X|` and `x ↦ |x|`).
- The quotient topology is defined here, not taken from an instance: `orbitTop X` is the
  coinduced topology `TopologicalSpace.coinduced X.π`, i.e. `V` is open iff `π⁻¹(V)` is open in
  `X`. This is the definition of the paragraph before the proposition (not a claim; it is not a
  conjunct of `B`). Mathlib's quotient instance on `Quotient _` is definitionally this topology.
- `B`: for every ep-groupoid, `π : X → |X|` is an open map for `orbitTop X`.
-/
namespace RoundTrip.V7_11
open Polyfold Topology

/-- The quotient topology on the orbit space `|X|`: the finest topology making `π` continuous. -/
abbrev orbitTop {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    TopologicalSpace X.OrbitSpace :=
  TopologicalSpace.coinduced X.π inferInstance

/-- Proposition 7.1: for an ep-groupoid with `|X|` carrying the quotient topology, the
projection `π : X → |X|` is open. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    @IsOpenMap Obj X.OrbitSpace _ (orbitTop X) X.π

end RoundTrip.V7_11
