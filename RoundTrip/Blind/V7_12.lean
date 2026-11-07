import Polyfold
/-! Blind formalization of V7_12 (the 2017 book, Part II, §7.1, Proposition 7.2, p. 229:
countable monotone neighbourhood bases of `|X|`). Choices:
- Setting as in `V7_11`: `Obj Mor : Type` (universe 0) with their topologies (`T2`, paracompact)
  as instances, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read with
  `#print`); `|X|` and `π` are the project's `X.OrbitSpace` and `X.π` (`Quotient` by
  `x ∼ y :↔ ∃ φ, s φ = x ∧ t φ = y`, `π x = ⟦x⟧`).
- "The quotient topology `𝒯`" is defined here (`orbitTop X`, the topology coinduced by `π`),
  not taken from an instance.
- "A countable basis of open neighbourhoods `(V_k)`, monotone": a sequence `V : ℕ → Set |X|`
  (index `k ∈ ℕ`; the text's `k ≥ 1` is a shift), each `V k` open and containing `z`, with
  `V (k+1) ⊆ V k`, such that every open set containing `z` (equivalently: every neighbourhood of
  `z`) contains some `V k`.
-/
namespace RoundTrip.V7_12
open Polyfold Topology

/-- The quotient topology on the orbit space `|X|`: the finest topology making `π` continuous. -/
abbrev orbitTop {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    TopologicalSpace X.OrbitSpace :=
  TopologicalSpace.coinduced X.π inferInstance

/-- Proposition 7.2: every point of `|X|` (quotient topology) has a countable, monotone basis of
open neighbourhoods. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (z : X.OrbitSpace),
    ∃ V : ℕ → Set X.OrbitSpace,
      (∀ k, IsOpen[orbitTop X] (V k) ∧ z ∈ V k) ∧
      (∀ k, V (k + 1) ⊆ V k) ∧
      ∀ N : Set X.OrbitSpace, IsOpen[orbitTop X] N → z ∈ N → ∃ k, V k ⊆ N

end RoundTrip.V7_12
