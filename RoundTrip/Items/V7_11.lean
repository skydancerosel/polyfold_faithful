import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_11

/-! Round trip for V7_11 (p. 229: the quotient topology of `|X|`, and Proposition 7.1: `π` is
open).

`A` is the conjunction of the types of the four listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.continuous_π`, `EpGroupoid.proposition_7_1`
(`IsOpenMap X.π`), `EpGroupoid.proposition_7_1_isOpenQuotientMap` and
`EpGroupoid.proposition_7_1_map_nhds` (`map π (𝓝 x) = 𝓝 (π x)`).  The project's topology on
`X.OrbitSpace = Quotient X.orbitSetoid` is Mathlib's quotient instance, which is definitionally
`B`'s `orbitTop X = coinduced X.π` (the proofs below use this by `exact`).

* `A → B`: `B` is `proposition_7_1`.
* `B → A`: `proposition_7_1` is `B`; `isOpenQuotientMap` is surjectivity, continuity and `B`;
  `map_nhds` follows from `IsOpenQuotientMap.map_nhds_eq`; `continuous_π` is re-proved outright
  (`continuous_quot_mk`: it is the defining property of the quotient topology, not part of
  `B`'s claim). -/

namespace RoundTrip.V7_11
open Polyfold Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.continuous_π.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_1.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_1_isOpenQuotientMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_1_map_nhds.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.continuous_π.{0}, @Polyfold.EpGroupoid.proposition_7_1.{0},
    @Polyfold.EpGroupoid.proposition_7_1_isOpenQuotientMap.{0},
    @Polyfold.EpGroupoid.proposition_7_1_map_nhds.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  exact hA.2.1 X

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  have hO : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      IsOpenQuotientMap X.π := fun Obj Mor _ _ _ _ _ _ X =>
    ⟨Quotient.mk''_surjective, continuous_quot_mk, hB Obj Mor X⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X
    exact continuous_quot_mk
  · intro Obj Mor _ _ _ _ _ _ X
    exact hB Obj Mor X
  · intro Obj Mor _ _ _ _ _ _ X
    exact hO Obj Mor X
  · intro Obj Mor _ _ _ _ _ _ X x
    exact (hO Obj Mor X).map_nhds_eq x

#rt_check RoundTrip.V7_11.A_to_B [Polyfold.EpGroupoid.continuous_π,
  Polyfold.EpGroupoid.proposition_7_1, Polyfold.EpGroupoid.proposition_7_1_isOpenQuotientMap,
  Polyfold.EpGroupoid.proposition_7_1_map_nhds]
#rt_check RoundTrip.V7_11.B_to_A [Polyfold.EpGroupoid.continuous_π,
  Polyfold.EpGroupoid.proposition_7_1, Polyfold.EpGroupoid.proposition_7_1_isOpenQuotientMap,
  Polyfold.EpGroupoid.proposition_7_1_map_nhds]
#rt_overlap RoundTrip.V7_11.B_to_A [Polyfold.EpGroupoid.continuous_π,
  Polyfold.EpGroupoid.proposition_7_1, Polyfold.EpGroupoid.proposition_7_1_isOpenQuotientMap,
  Polyfold.EpGroupoid.proposition_7_1_map_nhds]

end RoundTrip.V7_11
